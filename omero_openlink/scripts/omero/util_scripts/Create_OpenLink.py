#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""
This script can be used with python 3.6

This script creates a download slot with links to the given image objects.
Directory structure is orientated on the omero project-dataset-image structure.
@author Susanne Kunis
<a href="mailto:sinukesus@gmail.com">sinukesus@gmail.com"</a>
"""

import os
import sys
import random
import string
import omero
from omero.rtypes import rstring, rlong
import time
import omero.scripts as scripts
from omero.gateway import BlitzGateway
import datetime
import re
import subprocess
from pathlib import Path

import smtplib
from email.mime.multipart import MIMEMultipart
from email.mime.text import MIMEText
from email.utils import formatdate
import json
import glob


# -------------------------------------------------
# ------------ Configuration ----------------------
# -------------------------------------------------

# Directory for links that the nginx server also has access to
OPENLINK_DIR = "/path/to/open_link_dir"

# name of nginx website
SERVER_NAME = "omero-data.myfacility.com"

# type of hypertext transfer protocol (http or https)
TYPE_HTTP = "https"


# email originator
ADMIN_EMAIL = "myemail@yourfacilitydomain"

# length of hash string used in the openlink url
LENGTH_HASH = 12
# --------------------------------------------------


# OMERO.script GUI elements
PARAM_DATATYPE = "Data_Type"
PARAM_ID = "IDs"
PARAM_SLOTS = "Choose_existing_OpenLink"
PARAM_ADD_TO_SLOT = "Add_to_existing_OpenLink"
PARAM_SLOT_NAME = "OpenLink_Name"
PARAM_ATTACH = "Add_attachments"

# email server IP adress
SMTP_IP = "127.0.0.1"

NGINX_LOCATION = ""  # '/openlink'

URL = "%s://%s%s" % (TYPE_HTTP, SERVER_NAME, NGINX_LOCATION)

OPENLINK_PATTERN = "rn_*_"
GET_SLOTNAME_PATTERN = r"^rn_[A-Z,0-9]+_\d+_(.+)"
CURL_FILE = "batch_download.curl"
CONTENT_FILE = "content.json"
CURL_PATTERN = 'create-dirs\noutput="%s%s%s"\ncontinue-at -\nurl="%s/%s/%s"\n'

CMD = "curl -s %s/%s/%s | curl -K-"

MAX_PATHLENGTH = 200  # max pathlength in windows:256


NON_VALID_CHAR = r"[@ `!#$%^&+=*()<>?/\\|}{~:ÃƒÆ’Ã…Â¸,]"


# define valid characters that should be used instead of a certain non valid
# character. If nothing is specified, the character will be replaced by '_'
REPLACE_CHAR = {"&": "AND", "%": "Perc", "#": "Num", "+": "AND", "^": "OR"}

# flag for non valid characters in filenames
WARNINGS = False
ERRORS = False
# dict of {'<userID>':{'images':<list_of_imageIds>,'email':<mail>}} for mail
# notification
NOTIFICATION_LIST = {}


# -------------------------------------------------------------------


def setWarning():
    global WARNINGS
    WARNINGS = True


def setError():
    global ERRORS
    ERRORS = True


def get_realpath(path):
    """return target of symlink"""
    return Path(path).resolve().as_posix()


def get_omero_paths(client):
    """
    Args:
        client: calling omero client object
    Returns:
        managed_repo_dir: path to MANAGED_REPOSITORY of this omero instance (see config: omero.managed.dir)  # noqa
        orig_repo_dir: path to data of this omero instance (see config: omero.data.dir)  # noqa
    """
    resources = client.sf.sharedResources()
    repos = resources.repositories()
    managed_repo_dir = None
    orig_repo_dir = None

    # Identify repository paths
    for desc in repos.descriptions:
        if "ManagedRepository".lower() in desc.name.val.lower():
            managed_repo_dir = desc.path.val + desc.name.val
        if "OMERO".lower() in desc.name.val.lower():
            orig_repo_dir = desc.path.val + desc.name.val

    # if the repo paths could not be identify, check custom configurations
    # from config of omero
    svc = client.sf.getConfigService()
    if not managed_repo_dir:
        managed_repo_dir = svc.getConfigValue("omero.managed.dir")
    if not orig_repo_dir:
        orig_repo_dir = svc.getConfigValue("omero.data.dir")

    # catching empty paths
    if not managed_repo_dir:
        print(
            "ERROR: no specification was found for managed repository path. "
            "Please check path of type Managed under \n >>omero fs repos \n "
            "or the value of omero.managed.dir under\n >>omero config get"
        )
        setError()
        return None, None

    if not orig_repo_dir:
        print(
            "ERROR: no specification was found for omero repository path. "
            "Please check path of type Public under \n >>omero fs repos \n "
            "or the value of omero.data.dir under\n >>omero config get"
        )
        setError()
        return None, None

    # Ensure paths end with a slash
    if managed_repo_dir and not managed_repo_dir.endswith("/"):
        managed_repo_dir = managed_repo_dir + "/"
    if orig_repo_dir:
        orig_repo_dir = orig_repo_dir + "/Files/"

    # Resolve to absolute paths
    managed_repo_dir = get_realpath(managed_repo_dir)
    orig_repo_dir = get_realpath(orig_repo_dir)

    #  Validate paths exist
    if not os.path.exists(managed_repo_dir):
        managed_repo_dir = None
    if not os.path.exists(orig_repo_dir):
        orig_repo_dir = None

    return managed_repo_dir, orig_repo_dir


# returning file paths in qiven directory and all subdirs
def get_file_paths(directory, file_paths):
    """Append absolute paths of file in qiven directory and in all subdirs
    Args:
        directory:
        file_paths: list of absolute paths of files
    Returns:
        file_paths: list of absolute paths of files
    """
    for f in glob.iglob(os.path.join(directory, "*"), recursive=True):
        if os.path.isdir(f):
            # Collect paths from subdirectories
            file_paths = get_file_paths(f, file_paths)
        else:
            file_paths.append(f)

    return file_paths


def addToCurlFile(base, hash_name):
    """
    Args:
        base: absolute path to openlink area
        hash_name: name of openlink area dir
    """

    curl_file = os.path.join(base, CURL_FILE)
    content_file = os.path.join(base, CONTENT_FILE)
    file_list = get_file_paths(base, [])
    access_area_name = parseAreaNames(hash_name)
    try:
        t_file = open(curl_file, "w")
        for file in file_list:
            if os.path.basename(file) == os.path.basename(content_file):
                continue
            if not os.path.basename(file) == os.path.basename(curl_file):
                relpath = os.path.relpath(file, base)
                relpath = relpath.replace("\\", "/")
                if len(relpath) > MAX_PATHLENGTH:
                    print(
                        "WARNING: pathlength is in the critical range! This "
                        "could generate download issues for %s" % relpath
                    )
                    setWarning()

                # replace whitespaces
                entry = CURL_PATTERN % (
                    access_area_name,
                    os.sep,
                    replace_special_char_in_tokens(relpath),
                    URL,
                    hash_name.replace(" ", "%20"),
                    relpath.replace(" ", "%20"),
                )
                t_file.write(entry)
                t_file.write("\n")
        t_file.flush()
    finally:
        t_file.close()


# get location of sources in managed rep
# TODO: filenames with special characters makes problems
def getOriginalFile(image_obj):
    """Get location of sources in managed rep.
    Args:
        image_obj: image object
    Returns:
        path: path to file
        name: name of the file
    """
    fileset = image_obj.getFileset()

    for orig_file in fileset.listFiles():
        name = orig_file.getName()
        path = orig_file.getPath()

    return path, name


def writeDictContent(path):
    global CONTENT_DICT
    with open(path, 'w') as f:
        json.dump(CONTENT_DICT, f)


def loadDictContent(path):
    global CONTENT_DICT
    if os.path.exists(path):
        with open(path, 'r') as f:
            CONTENT_DICT = json.load(f)
    else:
        print("INFO: create new content dict")
        CONTENT_DICT = {}


def existsInDictContent(path, id):
    global CONTENT_DICT
    if not CONTENT_DICT:
        return False

    if CONTENT_DICT.get(path) is not None and CONTENT_DICT.get(path) == id:
        return True
    return False


def getContentFromDictById(id):
    global CONTENT_DICT
    if not CONTENT_DICT:
        return False
    paths = [k for k, v in CONTENT_DICT.items() if v == id]

    return paths


def addToDictContent(path, id):
    global CONTENT_DICT
    CONTENT_DICT.update({path: id})


def createObjectDir(ppath, object, name):
    """
    Create new directory of <name> in <ppath> and add this path and the
    object id to global dict CONTENT_DICT .
    Normally <name> is the name of the given object.
    If the directory still exists, but was created from a different object,
    append object id to the name of the dir.

    Args:
        ppath: path to directory where the new directory should be created
        object: omero object
        name: name of the new directory
    RETURN:
        absolute path of created dir

    """
    if name is None:
        return None

    # replace non valid characters
    name, message = replace_special_char(name)
    if message:
        print(message)
    path = os.path.join(ppath, name)
    if not os.path.exists(path):
        try:
            os.mkdir(path)
            addToDictContent(path, object.getId())
            return path
        except Exception:
            print(
                "ERROR: Cannot create directory for ID:%s: %s in %s (possible problems:length of name, or name contains special char)"  # noqa
                % (object.getId(), name, ppath)
            )
            setError()
            return None
    else:
        # check if existing object is the same
        if not existsInDictContent(path, object.getId()):
            # check if there is another name for this object
            existing_paths = getContentFromDictById(object.getId())
            if len(existing_paths) == 0:
                # create alternativ name (append id)
                alter_dir_name = "%s_%s" % (object.getName(), object.getId())
                return createObjectDir(ppath, object, alter_dir_name)
            else:
                return existing_paths[0]
    return path


def getPath(image, slot):
    """
    Generate directory structure like in omero (project/dataset/) for given
    <image> in directory <slot> if it not exist.
    RETURN: absolute path to dataset
    """
    dataset_obj = image.getParent()
    project_obj = dataset_obj.getParent()

    link_dir = slot

    if project_obj is not None:
        link_dir = createObjectDir(link_dir, project_obj,
                                   project_obj.getName())

    if link_dir is not None:
        link_dir = createObjectDir(link_dir, dataset_obj,
                                   dataset_obj.getName())

    if link_dir is None:
        print("ERROR: can't create Project directory for ", image.getName())
        setError()

    return link_dir


def userIsOwner(conn, user_name, id):
    """
    Check if owner of the image == calling user.
    Args:
        conn: BlitzGateway object
        userName: name of the user
        id: image Id
    Returns:
        True if user is onwer, else false
    """
    image = conn.getObject("Image", id)
    return image.getOwnerOmeName() == user_name


def userIsFullAdmin(conn):
    # Check if you are an full administrator

    if not conn.isFullAdmin():
        return False
    else:
        return True


def groupAllowedToShareData(conn, user_id):
    """
    Return true if the current group is read-annotate or (if the user is owner
    of the group and the group is not private)
    Args:
        conn: BlitzGateway connection
        userID: user ID

    """
    group = conn.getGroupFromContext()
    print("# INFO:  Current group: %s" % group.getName())
    # if current group is a private group -> return false
    group_perms = group.getDetails().getPermissions()
    perm_string = str(group_perms)
    permission_names = {
        "rw----": "PRIVATE",
        "rwr---": "READ-ONLY",
        "rwra--": "READ-ANNOTATE",
        "rwrw--": "READ-WRITE",
    }
    print(
        "# INFO: Group Permission: %s (%s)"
        % (permission_names[perm_string], perm_string)
    )

    # private group?
    if permission_names[perm_string] == permission_names["rw----"]:
        return False
    # read-write group?
    if permission_names[perm_string] == permission_names["rwrw--"]:
        return True

    # user is owner of this group?
    owners, members = group.groupSummary()
    for own in owners:
        if user_id == own.getId():
            return True

    return False


def replace_special_char(name):
    if name is None:
        return name
    replaced_name = re.sub(NON_VALID_CHAR, "_", name)
    message = None
    if replaced_name != name:
        message = "# WARNING: replaced char : [%s] -> [%s]" % (name, replaced_name)  # noqa
        setWarning()
    return replaced_name, message


def replace_special_char_in_tokens(name):
    # split by string by "/" to separate tokens
    tokens = name.split("/")
    replaced_name = ""
    for i in tokens:
        token = re.sub(NON_VALID_CHAR, "_", i)
        # if token!=i:
        #    print("replaced char!!!!, ",token)

        # merge tokens
        replaced_name = replaced_name + "/" + token
    print("WARNING: replaced_tokens:\n [%s] -> [%s]" % (name, replaced_name))

    return replaced_name


def getFilesetPath(conn, id):
    """
    Return path to the fileset of given image

    Args:
        conn: BlitzGateway connection
        id: image id

    """
    image = conn.getObject("Image", id)
    # this will include pre-FS data IF images were archived on import
    # specifically count Fileset files
    file_count = image.countFilesetFiles()
    # list files
    file_paths = []
    f_name = ""
    if file_count > 0:
        if file_count > 1:
            for orig_file in image.getImportedImageFiles():
                path = orig_file.getPath()
                file_paths.append(path)
        else:
            path, f_name = getOriginalFile(image)
            file_paths.append(path)

    fileset_path = os.path.commonprefix(file_paths)

    return fileset_path, f_name


def checkLinks(target, dir, name, link_names, link_targets, id):
    """
     Decide if symlink and target will be added to the lists of names and
     targets, or change symlink name if necessary
     Args:
         target: path that should be linked
         dir: dir where the link should be created
         name: name of link
         link_names: list of symlinks
         link_targets: list of link targets
         id: id of object that should be linked
    Return:
        link_names: list of symlinks
        link_target: list of link targets
    """
    name, message = replace_special_char(name)
    symlink = os.path.join(dir, name)
    if target not in link_targets:
        if symlink not in link_names:
            # ("accept : %s"%name)
            link_names.append(symlink)
            link_targets.append(target)
            if message:
                print(message)
        else:  # link of same name still exists -> rename
            f_name, extension = os.path.splitext(name)
            name = "%s_%s%s" % (f_name, id, extension)
            print("# INFO: rename : %s [new: %s]" % (f_name, name))
            link_names, link_target = checkLinks(
                target, dir, name, link_names, link_targets, id
            )
    else:  # link to target still exists
        if symlink not in link_names:  # ignore
            # print("# INFO: ignore %s (src exists, dest not)"%name)
            pass
        else:  # ignore
            # print("# INFO: ignore %s (src exists, dest exists)"%name)
            pass

    return link_names, link_targets


def createSymlinks(link_names, link_target):
    """
    Create symlink on the system if not exists.
    Args:
        link_names: name of symlink
        link_target: target where the link points to
    """
    if link_names is not None and len(link_names) > 0:
        for src, dest in zip(link_target, link_names):
            # print("# create link: %s ->\n\t%s"%(dest,src))
            try:
                # if src path is a symlink (for inplace imported data)
                if os.path.islink(src):
                    # use string representing the path
                    # to which the symbolic link points
                    src = os.readlink(src)

                os.symlink(src, dest)
            except FileExistsError:
                print("# INFO: skip:: Link still exists: ", src)


def addAttachment(obj, tdir):
    """
    Args:
        obj: object with attachments
        tdir: path where links to the attachments should be created
    Returns:
    """
    global ORIGINAL_REP
    if tdir is not None:
        for ann in obj.listAnnotations():
            if isinstance(ann, omero.gateway.FileAnnotationWrapper):
                print(
                    "# INFO: Annotation File ID:",
                    ann.getFile().getId(),
                    ann.getFile().getName(),
                )
                # TODO: link - if file still exists - skip
                file = ann.getFile()
                carg = "find %s -name %s" % (ORIGINAL_REP, file.getId())
                paths = [
                    line[0:]
                    for line in subprocess.check_output(carg, shell=True).splitlines()  # noqa
                ]
                if len(paths) > 1:
                    print(
                        "# WARNING: file annotation target is not unique: %s --> use first match"   # noqa
                        % ("\n".join(paths))
                    )
                    setWarning()
                link_names = []
                link_names.append(os.path.join(tdir, file.getName()))
                link_target = []
                link_target.append(str(paths[0].decode("utf-8")))
                createSymlinks(link_names, link_target)


def addToNotifyList(user, image_id):
    """
    Validate user mail and add image id as well email to
    list of user that get a notification mail.
    Args:
        user: user object
        image_id: image id
    """
    # Initialises also the proxy object for simpleMarshal
    user_id = user.getId()
    dic = user.simpleMarshal()
    if "email" in dic and dic["email"]:
        user_email = dic["email"]
    else:
        print("No mail is given for user %s" % user.getName())
        return

    # TO BE MOVED
    url = "http://omero.cellnanos.uni-osnabrueck.de/webclient/?show=image-"
    image_url = url + str(image_id)

    # Validate with a regular expression. Not perfect but it will do
    pattern = "^[a-zA-Z0-9._%-]+@[a-zA-Z0-9._%-]+.[a-zA-Z]{2,6}$"
    match = re.match(pattern, user_email)
    if match:
        global NOTIFICATION_LIST
        if len(NOTIFICATION_LIST) == 0:
            NOTIFICATION_LIST = {user_id: {"images": [image_url],
                                           "email": user_email}}
        else:
            # user available?
            if user_id in NOTIFICATION_LIST and NOTIFICATION_LIST[user_id]:
                if NOTIFICATION_LIST[user_id]["images"]:
                    NOTIFICATION_LIST[user_id]["images"].append(image_url)
                else:
                    NOTIFICATION_LIST[user_id] = {
                        "images": [image_url],
                        "email": user_email,
                    }
            else:
                NOTIFICATION_LIST.update(
                    {user_id: {"images": [image_url], "email": user_email}}
                )


def get_owner_of_data(image):
    return image.getDetails().getOwner()


def addImages(conn, slot, images, user, add_attachments,
              allowed_to_share, target_dir=None):
    """
    Check if parent dir (dataset) exists (and create one if not)
    and afterwards calls createObjectDir for given image objects
    Args:
        conn: BlitzGateway connection
        slot: path to access area
        images: List of OMERO dataset objects
        user: user object
        add_attachments (bool):
        allowed_to_share (bool):
        target_dir: parent dataset dir if exists
    """
    link_names = []
    link_target = []
    user_name = user.getName()
    global MANAGED_REP

    # proof images
    for image in images:
        user_is_owner = userIsOwner(conn, user_name, image.id)
        user_is_fulladmin = userIsFullAdmin(conn)
        # share data
        share = allowed_to_share or user_is_owner
        if user_is_fulladmin:
            share = True
        if share:
            if not target_dir:
                target_dir = getPath(image, slot)
                # failed path
                if not target_dir:
                    continue

            src_fileset_path, src_fname = getFilesetPath(conn, image.id)

            # add tp linkNames and linkTarget list
            if src_fileset_path:
                if image.countFilesetFiles() > 1:
                    name, extension = os.path.splitext(image.getName())
                    src = os.path.join(MANAGED_REP, src_fileset_path)

                    link_names, link_target = checkLinks(
                        src, target_dir, name, link_names,
                        link_target, image.id
                    )

                else:
                    src = os.path.join(
                        os.path.join(MANAGED_REP, src_fileset_path), src_fname
                    )

                    link_names, link_target = checkLinks(
                        src, target_dir, src_fname, link_names, link_target,
                        image.id
                    )

                # if data owned by others - owner of this data should be notify
                if not user_is_owner and allowed_to_share:
                    addToNotifyList(get_owner_of_data(image), image.id)
            else:
                print("# WARNING: No raw file or fileset available")
                setWarning()

            # add available attachments if required
            if add_attachments:
                addAttachment(image, target_dir)
        else:
            print(
                f"# WARNING: You are not allowed to share image: {image.getId()}. (ownership: {user_is_owner}, group permission: {allowed_to_share})"  # noqa
            )
            setWarning()

    # create links from proof images
    createSymlinks(link_names, link_target)


def addDatasets(
    conn, slot, datasets, user, add_attachments,
    allowed_to_share, target_dir=None
):
    """
    TODO: doubled with addPath?
    Check if parent project dir exists (and create one if not) and
    afterwards calls createObjectDir for given dataset objects
    and add images
    Args:
      conn: BlitzGateway connection
      slot: path to access area
      projects: List of OMERO dataset objects
      user: user object
      add_attachments (bool):
      allowed_to_share (bool):
      target_dir: parent project dir if exists
    """
    for dataset in datasets:
        # check if parent project dir still exists
        if not target_dir:
            project_obj = dataset.getParent()
            if project_obj is not None:
                link_dir = createObjectDir(slot, project_obj,
                                           project_obj.getName())
            else:
                link_dir = slot
        else:
            link_dir = target_dir

        if link_dir is not None:
            link_dir = createObjectDir(link_dir, dataset, dataset.getName())

            if add_attachments:
                addAttachment(dataset, link_dir)

            addImages(
                conn,
                slot,
                dataset.listChildren(),
                user,
                add_attachments,
                allowed_to_share,
                link_dir,
            )


def addProjects(conn, slot, projects, user, add_attachments, allowed_to_share):
    """
    TODO: doubled with addPath?
    Calls createObjectDir for given project objects and add child datasets
    Args:
        conn: BlitzGateway connection
        slot: path to access area
        projects: List of OMERO project objects
        user: user object
        add_attachments (bool):
        allowed_to_share (bool):
    """
    for project in projects:
        link_dir = createObjectDir(slot, project, project.getName())
        if link_dir is not None:
            if add_attachments:
                addAttachment(project, link_dir)

            addDatasets(
                conn,
                slot,
                project.listChildren(),
                user,
                add_attachments,
                allowed_to_share,
                link_dir,
            )


def addPlates(conn, slot, plates, user, add_attachments,
              allowed_to_share, target_dir=None):
    """
    TODO: doubled with addPath?
    Check if parent screen dir exists (and create one if not)
    and afterwards calls createObjectDir for given plates objects
    and add images
    Args:
      conn: BlitzGateway connection
      slot: path to access area
      plates: List of OMERO plates objects
      user: user object
      add_attachments (bool):
      allowed_to_share (bool):
      target_dir: parent project dir if exists
    """
    for plate in plates:
        # check if parent screen dir still exists
        if not target_dir:
            screen_obj = plate.getParent()
            if screen_obj is not None:
                link_dir = createObjectDir(slot, screen_obj,
                                           screen_obj.getName())
            else:
                link_dir = slot
        else:
            link_dir = target_dir

        if link_dir is not None:
            link_dir = createObjectDir(link_dir, plate, plate.getName())

            if add_attachments:
                addAttachment(plate, link_dir)
            image_list = []
            for well in plate.listChildren():
                index = well.countWellSample()

                for index in range(0, index):
                    image_list.append(well.getImage(index))
            addImages(
                conn, slot, image_list, user, add_attachments,
                allowed_to_share, link_dir
            )


def addScreens(conn, slot, screens, user, add_attachments, allowed_to_share):
    """
    Calls createObjectDir for given screen objects and add child plates
     Args:
        conn: BlitzGateway connection
        slot: path to access area
        screens: List of OMERO screen objects
        user: user object
        add_attachments (bool):
        allowed_to_share (bool):
    """
    for screen in screens:
        link_dir = createObjectDir(slot, screen, screen.getName())
        if link_dir is not None:
            if add_attachments:
                addAttachment(screen, link_dir)

            addPlates(
                conn,
                slot,
                screen.listChildren(),
                user,
                add_attachments,
                allowed_to_share,
                link_dir,
            )


def getRandomString(n):
    """generating random strings
    Args:
        n: length of random number
    """
    return "".join(random.choices(string.ascii_uppercase + string.digits, k=n))


def generateHashName(user, n, access_area_name):
    """
    Generate name for access area like
    "rn_<randomNumber>_<userID>_<userSpecificAreaName>"
    Args:
        user: user object
        n: lenght of random number
        accessAreaName: access area name specified by user
    Returns:
        hashname: string like "rn_<randomNumber>_<userID>_<userSpecificAreaName>"  # noqa
    """

    return "%s_%s_%s_%s" % ("rn", getRandomString(n), user.getId(), access_area_name)  # noqa


def createDefaultAreaName():
    """
    Return default name for an area.
    Returns:
        timeStr: current date and time as string in the format: %Y-%m-%d_%H-%M-%S  # noqa
    """
    date = datetime.datetime.now()
    return date.strftime("%Y-%m-%d_%H-%M-%S")


def generateNewArea(user, name):
    """
    Args:
        user: user object
        name: access area name specified by user
    Returns:
        path_to_area: path to area
        hash_name: whole name of area directory
    """

    hash_name = generateHashName(user, LENGTH_HASH, name)

    while os.path.exists(os.path.join(OPENLINK_DIR, hash_name)):
        hash_name = generateHashName(user, LENGTH_HASH, name)

    path_to_area = os.path.join(OPENLINK_DIR, hash_name)
    os.mkdir(path_to_area)

    return path_to_area, hash_name


def email_results(conn, image_ids, email, smtp_obj):
    """
    E-mail the result to the user.

    Args:
        conn:    The BlitzGateway connection
        image_ids: ID's of data that was shared
        email: email address of receiver
        smtp_obj:
    """
    shared_name = conn.getUser().getFullName()
    msg = MIMEMultipart()
    msg["From"] = ADMIN_EMAIL
    msg["To"] = email
    msg["Date"] = formatdate(localtime=True)
    msg["Subject"] = "[OMERO Share] your data was shared"
    msg.attach(
        MIMEText(
            """Your data was shared by %s.

    List of shared data:

    %s

    """
            % (shared_name, "\n".join(str(v) for v in image_ids))
        )
    )
    smtp_obj.sendmail(ADMIN_EMAIL, [email], msg.as_string())
    return


def notifyMembers(conn):
    """
    Notify owner of the data via mail if they was shared by group owner
    """
    global NOTIFICATION_LIST

    if len(NOTIFICATION_LIST) == 0:
        return
    else:
        start = time.time()
        smtp_obj = smtplib.SMTP(SMTP_IP)

        for key, value in NOTIFICATION_LIST.items():
            print("# INFO: Send Notification to %s" % value["email"])
            email_results(conn, value["images"], value["email"], smtp_obj)
        smtp_obj.quit()
        print("# INFO: Notification via mail took %.2f seconds" % (time.time() - start))  # noqa


def addObjToArea(conn, params, existing_areas_names=None, paths=None):
    """
    add selected object and its content to a slot on OPENLINK_DIR
    as link to sources on ManagedRepository

    Args:
        conn: current user connection
        params: user input
        existing_areas_names: list of available slots for current user
        paths: list of paths to the available slots of the surrent user
    Returns:
        message:
    """

    # init Notifationlist
    global NOTIFICATION_LIST
    NOTIFICATION_LIST = {}

    # check group permissions for sharing
    allowed_to_share = groupAllowedToShareData(conn, conn.getUser().getId())

    # prepare openLink area
    access_area_path, hash_name = prepareOpenLinkArea(
        existing_areas_names, conn, params, paths
    )

    add_attachments = False
    if params.get(PARAM_ATTACH):
        add_attachments = True

    dest_objs = None
    if params.get(PARAM_ID) is not None:
        dest_objs = conn.getObjects(params.get(PARAM_DATATYPE),
                                    params.get(PARAM_ID))
        dest_type = params.get(PARAM_DATATYPE)

    # parse json with object ids available in this area to dict
    content_file_name = "%s/%s" % (access_area_path, CONTENT_FILE)
    loadDictContent(content_file_name)

    if dest_objs is None:
        setError()
        return None, "ERROR: Given objects not available"
    if dest_type is None:
        setError()
        return (
            None,
            "ERROR: Can't identify selected object. Please select Projects, Datasets or Images",  # noqa
        )
    elif dest_type == "Project":
        addProjects(
            conn,
            access_area_path,
            dest_objs,
            conn.getUser(),
            add_attachments,
            allowed_to_share,
        )
    elif dest_type == "Dataset":
        addDatasets(
            conn,
            access_area_path,
            dest_objs,
            conn.getUser(),
            add_attachments,
            allowed_to_share,
        )
    elif dest_type == "Screen":
        addScreens(
            conn,
            access_area_path,
            dest_objs,
            conn.getUser(),
            add_attachments,
            allowed_to_share,
        )
    elif dest_type == "Plate":
        addPlates(
            conn,
            access_area_path,
            dest_objs,
            conn.getUser(),
            add_attachments,
            allowed_to_share,
        )
    elif dest_type == "Image":
        addImages(
            conn,
            access_area_path,
            dest_objs,
            conn.getUser(),
            add_attachments,
            allowed_to_share,
        )

    addToCurlFile(access_area_path, hash_name)
    writeDictContent(content_file_name)
    url = "%s/%s/" % (URL, hash_name)
    cmd = CMD % (URL, hash_name.replace(" ", "%20"), CURL_FILE)

    print("\n-----------------------------------------------------\n")
    print("URL: \n%s\n" % url)
    print(
        "Batch download: copy the following line between the hashes into your cmd:\n### "  # noqa
    )
    print(cmd)
    print("###\n")

    notifyMembers(conn)
    return url


def prepareOpenLinkArea(existing_areas_names, conn, params, paths):
    """
    Return path to openlink area and hashName
    """
    # get available openlink
    if params.get(PARAM_ADD_TO_SLOT) and paths and len(paths) > 0:
        index = existing_areas_names.index(params.get(PARAM_SLOTS))
        access_area_path = paths[index]
        hash_name = os.path.basename(access_area_path)
    else:
        # create new openlink
        area_name = params.get(PARAM_SLOT_NAME)
        if not area_name:
            area_name = createDefaultAreaName()
        access_area_path, hash_name = generateNewArea(conn.getUser(),
                                                      area_name)

    return access_area_path, hash_name


def parseAreaNames(p):
    """
    Return name of openLink area specified by user
    """
    try:
        name = re.search(GET_SLOTNAME_PATTERN, p).group(1)
    except AttributeError:
        name = None  # apply your error handling
        print("## ERROR ## at parse OpenLink names")
        setError()
    return name


def getAreasOfUser(id):
    """
    Args:
        id: user id
    Returns:
        values: list of paths that contains ID in the folder name
    """
    values = []
    p = "%s/%s%s_*" % (OPENLINK_DIR, OPENLINK_PATTERN, id)
    values = glob.glob(p)

    return values


def getExistingAreas(conn):
    """
    get all slots for current user
    (OPENLINK_DIR/rn_<RN>_<userid>_<accessAreaName>/;
    Args:
        conn: connection of calling user
    Returns:
        values: list of description of slots; one slot is described
                like "<areaName> [created <date>]"; if no slot
                available it returns ['No OpenLinks available for <userName>]
        paths: list of path to slots
    """
    values = None
    try:
        user = conn.getUser()
        user_name = user.getName()
        list_of_directories_for_user = None
        if os.path.exists(OPENLINK_DIR):
            list_of_directories_for_user = getAreasOfUser(str(user.getId()))

        if not list_of_directories_for_user or len(list_of_directories_for_user) == 0:  # noqa
            return ["No OpenLinks available for %s" % user_name], []

        # get names
        values = []
        paths = []
        for p in list_of_directories_for_user:
            area_name = parseAreaNames(os.path.basename(p))

            if area_name:
                timestamp = os.path.getctime(p)
                dt = datetime.datetime.fromtimestamp(timestamp)
                this_date = dt.strftime("%d %b %Y (%I:%M:%S %p)")
                values.append("%s [created %s]" % (area_name, this_date))
                paths.append(p)
    except Exception as e:
        values = ["Error parsing OpenLink for %s" % user_name]

        exc_type, exc_obj, exc_tb = sys.exc_info()
        print(
            "## ERROR ##: while reading OpenLink : %s\n %s %s"
            % (str(e), exc_type, exc_tb.tb_lineno)
        )
        setError()

    if len(values) == 0:
        values = ["No OpenLink found for %s" % user_name]

    return values, paths


def run_script():
    """
    The main entry point of the script, as called by the client via the
    scripting service, passing the required parameters.
    """

    client = omero.client()
    client.createSession()
    conn = omero.gateway.BlitzGateway(client_obj=client)
    conn.SERVICE_OPTS.setOmeroGroup(-1)
    existing_area_names, paths = getExistingAreas(conn)
    client.closeSession()

    data_types = [
        rstring("Screen"),
        rstring("Plate"),
        rstring("Project"),
        rstring("Dataset"),
        rstring("Image"),
    ]

    client = scripts.client(
        "Create_OpenLink.py",
        """
        Add selected objects and all subordinate objects
        to a new or existing OpenLink area.
        After the creation of the OpenLink section is
        completed, you will find a link under
        the right tab OpenLink
        after a REFRESH of your omero.web content.

        *** NOTE: ***
        You can only add data that belongs to you to
        your OpenLink area OR as group owner of a NON-PRIVATE
        group you can also use data from other members
        (the owner of the data will be notify by mail).
        """,
        scripts.String(
            PARAM_DATATYPE,
            optional=False,
            grouping="1",
            description="Choose source of objects",
            values=data_types,
        ),
        scripts.List(
            PARAM_ID,
            optional=False,
            grouping="2",
            description="List of Image IDs to process",
        ).ofType(rlong(0)),
        scripts.String(
            PARAM_SLOT_NAME,
            optional=True,
            grouping="3",
            description="Create new OpenLink area with given name. If nothing is specified, the current date is used.",  # noqa
        ),
        scripts.Bool(
            PARAM_ADD_TO_SLOT,
            grouping="4",
            description="Add data to an existing OpenLink area",
            default=False,
        ),
        scripts.String(
            PARAM_SLOTS,
            optional=True,
            grouping="4.1",
            description="Choose available OpenLink area",
            values=existing_area_names,
        ),
        scripts.Bool(
            PARAM_ATTACH,
            grouping="5",
            description="Link all file attachments of selected and subordinate objects",  # noqa
            default=True,
        ),
        namespaces=[omero.constants.namespaces.NSDYNAMIC],
        version="2.1.2",
        authors=["Susanne Kunis", "CellNanOs"],
        institutions=["University of Osnabrueck"],
        contact="sinukesus@gmail.com",
    )  # noqa

    try:
        params = client.getInputs(unwrap=True)
        if os.path.exists(OPENLINK_DIR):
            conn = BlitzGateway(client_obj=client)
            mrep, orep = get_omero_paths(client)

            global MANAGED_REP
            global ORIGINAL_REP

            if mrep:
                MANAGED_REP = mrep
            if orep:
                ORIGINAL_REP = orep
            # call main script, return the dest project
            message = addObjToArea(conn, params, existing_area_names, paths)
            message = "After reload you can find URL and batch download command listed under OpenLink in the right hand pane"  # noqa

            hints = []
            if WARNINGS:
                hints.append("WARNINGS")
            if ERRORS:
                hints.append("ERRORS")

            if hints:
                message = "*** Please note there are %s, see (i) *** \n%s" % (
                    " & ".join(hints),
                    message,
                )

            client.setOutput("Message", rstring(message))
        else:
            client.setOutput(
                "ERROR",
                rstring("No such OpenLink directory: %s" % OPENLINK_DIR)
            )
    finally:
        client.closeSession()


if __name__ == "__main__":
    run_script()
