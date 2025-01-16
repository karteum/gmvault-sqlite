#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
@author: Adrien Demarez
License: GPLv3 https://www.gnu.org/licenses/gpl-3.0.en.html

This program
- walks through a folder from a GMvault backup (assuming .eml are not gzipped. In my case I archived the whole dir in squashfs-lzma so it was better to leave the eml uncompressed) and parses the .meta and .eml files, the latter can be MIME with various encoding, attachments, etc.
- or walks through an mbox file (only tested with mbox from Google Takeout, noting that Google performs some encoding conversions that permanently break all non-ascii characters (they are all replaced by 0xEFBFBD, therefore encoding display issues are not a bug in this script but in the prior encoding bugs on Google Takeout side))
- stores the emails (header, txt, html, signatures) in an SQLite database. For HTML, the attached images are extracted and inserted as base64 embedded images within the html in order to avoid keeping a separate file
- extracts the other attached files to a dedicated folder (so all the attached files can be accessed directly through the filesystem). If the same file (same name, same md5) has already been extracted, it will not be stored twice. If a file with similar name but different md5 has already been extracted, it will be stored with a different name
- adds a small GUI to walk through the emails and add additional "where" conditions to the SQL query (for the moment it works with plain sqlite including "like" clauses. In the future I will test SQLite's full-text search features)

TODO: (among other things)
- refactor code. Put functions within the dedicated DB class
- solve encoding issues for HTML
- DB schema is simple but not optimal  (3NF, etc)
- implement full-text search with sqlite
- look deeper in winmail.dat (rtf attachments ?) and oledata.mso
...
"""

import sqlite3
import json
import sys
import re

#import mailparser # I realized afterwards that https://pypi.org/project/mail-parser/ might have done the job instead of writing custom decodemail() / decodepart() routines, but I didn't really test so for the moment I'll keep my own code :)
#from email.iterators import _structure
import email,quopri
#import email.contentmanager # FIXME: not used ?
from werkzeug.utils import secure_filename

import hashlib
#import xxhash # might replace md5 in the future since I don't need a cryptographically secure hash

import os,sys
#import io # FIXME: unused ?
import time
from datetime import datetime
from dateutil.parser import parse as dateparse

from PySide6.QtWidgets import *
#from PySide2.QtWebEngineWidgets import *
from PySide6.QtCore import *
from PySide6.QtSql import *
from PySide6.QtGui import *
import gzip
import argparse

def gui(dbfile):
    #cwd = '' if os.path.dirname(dbfile).startswith('/') else os.getcwd()+'/'
    def loadmsg(item):
        myquery = QSqlQuery()
        myquery.exec_("select body_text,body_html,attachments,gmail_labels from messages where id=%d" % (item.siblingAtColumn(0).data()))
        myquery.next()
        data=myquery.value(1) # value(1) is html, value(0) is plain text
        if data==None or data=="":
            data = "<html><head><title>foobar</title></head><body><pre>" + myquery.value(0) + "</pre></body></html>" # displays body_text when there is no html
        else:
            data = re.sub(r'<(meta|META) .*charset=.*>', '', data) # we already converted to utf-8 when storing html in SQLite so we filter lines such as <meta http-equiv="Content-Type" content="text/html; charset=iso-8859-1">

        local_textBrowser.setHtml(data)
        # I used to do local_webEngineView.setHtml(data), but setHtml has a 2MB size limit => need to switch to setUrl on tmp file for large contents
        # tmpfile = '/tmp/gmvault_sqlite_tmp.html' # FIXME: random tmp name. FIXME: delete the tmp file when it's no longer needed
        # with open(tmpfile, 'wb') as fp:
        #     fp.write(data.encode())
        # local_webEngineView.setUrl(QUrl('file://' + tmpfile))
        attachlist.clear()
        for att in myquery.value(2).split('¤'):
            item = QListWidgetItem(att)
            item.setData(1, os.path.dirname(os.path.abspath(dbfile))+'/'+myquery.value(3)+'/'+att)
            #item.setData(1, cwd+os.path.dirname(dbfile)+'/'+myquery.value(3)+'/'+att)
            attachlist.addItem(item)

    def model_update(item=None):
        if(item != None):
            #tmp = "labels='%s'" % (item.data(),)
            tmp = "labels='%s'" % (item.siblingAtColumn(1).data(),)
        else:
            tmp=lineedit.text()
        if tmp!=None and tmp!="":
            tmp=" where " + tmp
        model.clear()
        model.setQuery(db.exec_("select id, gmail_threadid thread, gm_id eml, gmail_labels labels, datetime(messages.datetime, 'unixepoch') as dt, msgfrom, msgto, msgcc, subject, flags, signature, attachments,size,sizeatt,numatt from messages" + tmp))
        #model.setQuery(db.exec_("select id, gmail_threadid thread, gm_id eml, gmail_labels labels, datetime(messages.datetime, 'unixepoch') as dt, msgfrom, msgto, msgcc, subject, flags, signature, attachments from messages" + tmp))
        while model.canFetchMore():
            model.fetchMore()
        #model.select()

    def createtreeitem(name): # recursive creation of parents items
        if name in itemlist:
            return itemlist[name]
        elif '/' in name:
            idx = name.rfind('/')
            parentitem = createtreeitem(name[:idx])
            item = QTreeWidgetItem(None, [name[idx+1:], name] )
            itemlist[name] = item
            parentitem.addChild(item)
            return item
        else:
            item = QTreeWidgetItem(None, [name, name] )
            itemlist[name] = item
            foldertree.insertTopLevelItem(0,item)
            return item

    app = QApplication(sys.argv)

    tabview = QTableView()
    tabview.clicked.connect(loadmsg)
    tabview.setVerticalScrollMode(QAbstractItemView.ScrollPerPixel)
    tabview.setHorizontalScrollMode(QAbstractItemView.ScrollPerPixel)
    # folderlist = QListWidget()
    # folderlist.clicked.connect(model_update)
    foldertree = QTreeWidget()
    foldertree.setColumnCount(2)
    foldertree.hideColumn(1)
    foldertree.clicked.connect(model_update)

    # local_webEngineView = QWebEngineView()
    local_textBrowser = QTextBrowser() # Actually QTextBrowser is enough to display basic HTML (including images) without js and without security issues that might arise with QWebEngineView parsing potentially hostile HTML...
    #local_textBrowser.setStyleSheet("background-color: black;")
    attachlist = QListWidget()
    attachlist.doubleClicked.connect(lambda item: QDesktopServices.openUrl(QUrl.fromLocalFile(item.data(1))))
    #attachlist.doubleClicked.connect(lambda item: print(item.data(1)))

    splitter_left = QSplitter(Qt.Vertical)
    splitter_left.addWidget(tabview)
    #splitter_left.addWidget(local_webEngineView)
    splitter_left.addWidget(local_textBrowser)
    splitter_left.setSizes([800,800])
    splitter_right = QSplitter(Qt.Vertical)
    #splitter_right.addWidget(folderlist)
    splitter_right.addWidget(foldertree)
    splitter_right.addWidget(attachlist)
    splitter_right.setSizes([800,200])
    splitter = QSplitter(Qt.Horizontal)
    splitter.addWidget(splitter_left)
    splitter.addWidget(splitter_right)
    splitter.setSizes([800,200])
    #splitter.setStretchFactor(0,8)

    vbox = QVBoxLayout()
    vbox.addWidget(splitter)

    mainWin = QWidget()
    mainWin.setLayout(vbox)

    lineedit=QLineEdit()
    lineedit.returnPressed.connect(model_update)

    toolbar = QToolBar()
    toolbar.addWidget(lineedit)

    mainwin2 = QMainWindow()
    mainwin2.setCentralWidget(mainWin)
    mainwin2.addToolBar(toolbar)

    availableGeometry = app.primaryScreen().geometry() #app.desktop().availableGeometry(mainWin)
    mainwin2.resize(availableGeometry.width() * 2 / 3, availableGeometry.height() * 2 / 3)

    db = QSqlDatabase.addDatabase("QSQLITE")
    db.setDatabaseName(dbfile)
    if not db.open():
        print("cannot open DB")
        return

    myquery2 = db.exec_("select gmail_labels labels from messages group by labels order by labels")
    itemlist = {}
    while myquery2.next():
        # folderlist.addItem(myquery2.value(0))
        createtreeitem(myquery2.value(0))

    model=QSqlTableModel()
    model_update()
    tabview.setModel(model)

    mainwin2.show()
    app.exec_()

# for winmail.dat
from tnefparse.tnef import TNEF, TNEFAttachment, TNEFObject
from tnefparse.mapi import TNEFMAPI_Attribute
def my_tnef_parse(filepath="winmail.dat"):
    t = TNEF(open(filepath).read(), do_checksum=True)
    for a in t.attachments:
        with open(a.name, "wb") as afp:
            afp.write(a.data)
    sys.exit("Successfully wrote %i files" % len(t.attachments))

def md5sum(filename, blocksize=65536):
    hash = hashlib.md5()
    with open(filename, "rb") as f:
        for block in iter(lambda: f.read(blocksize), b''):
            hash.update(block)
    return hash.hexdigest()

def dateparse_normalized(datestr):
    datestr=datestr.replace('+0000 GMT','GMT') # "+0000 GMT" raises an error in the date parser
    for tmp in datestr.split(','): # Remove everything before and after (potential) comma, since they are error prone (e.g. if the string starts with "Wen, ..." instead of "Wed, ..." the parser would fail without this. Same with regards to the end of the string)
        if re.search(r'..:..:..', tmp):
            #tmp = re.sub(r'(.*..:..:..) .*', '\\1', tmp)
            tmp = re.sub(r'(.*..:..:[^\(a-zA-Z]*).*', '\\1', tmp) # FIXME: keep year e.g. in case of 'Wed Feb 29 07:02:03 +0000 2012'
            break
    return int(datetime.timestamp(dateparse(tmp)))
    # FIXME "UnknownTimezoneWarning: tzname EDT identified but not understood.  Pass `tzinfos` argument in order to correctly return a timezone-aware datetime.  In a future version, this will raise an exception."

def cset_sanitize(cset):
    if cset==None or cset=="utf-8//translit" or cset=='utf8':
        cset="utf-8"
    elif cset=='iso-2022-cn': # this codec is not supported in Python, and they don't care (bug report https://bugs.python.org/issue2066 is closed with status WONTFIX)
        cset='iso-2022-jp-2' # FIXME: not sure at all and I know nothing about those iso-2022 encodings, but looking at https://docs.python.org/2/library/codecs.html#standard-encodings I wonder whether it might be an alternative ? Anyway I have to choose something...
    elif cset=='IBM-eucKR':
        cset='euc_kr'
    elif cset.startswith('windows-1252'): # There was a bug with charset="windows-1252http-equivContent-Type"
        cset='windows-1252'
    elif cset=='windows-874':
        cset='iso-8859-11' # FIXME: also not sure...
    elif cset.startswith('charset'):
        cset=cset[cset.find('"')+1:cset.rfind('"')]
    try: # got weird charset names such as "charset=y" or "charset=x-binaryenc". Default is to use utf-8 in case of an unknown charset
        'a'.encode(cset)
    except LookupError:
        print("\nUnsupported charset : " + cset)
        cset='utf-8'
    return cset

def qdecode(qstr):
    # parse the "Q-encoding" (not exhaustive, but it works for my cases)
    #if myfield_qp_list[2] in ["Q", "B", 'q', 'b']:
        #cset = cset_sanitize(myfield_qp_list[1])
        #myfield_val = myfield_qp_list[3].replace('_', ' ')
    #else:
        #myfield_val = msg[myfield][2:-2].replace('_', ' ')
    if qstr.startswith('=?'):
        qlist = qstr.split('?')
        if qlist[2] in ["Q", "B", 'q', 'b']:
            cset = cset_sanitize(qlist[1]) # FIXME: what if multiline q-entry has different encoding between lines ? (can it happen ?)
            ret_tmp = ""
            nlines = int((len(qlist) - 1) / 4)
            for k in range(nlines):
                ret_tmp += qlist[3+4*k]
            try:
                ret = quopri.decodestring(ret_tmp).decode(cset)
            except UnicodeDecodeError:
                ret = quopri.decodestring(ret_tmp).decode('iso8859-1') # Handle case where utf-8 is announced but the real encoding is different (I only got this bug once and the real encoding was iso8859-1). FIXME: handle more cases i.e. guess the real encoding
            except ValueError:
                ret_tmp = quopri.encodestring(ret_tmp.encode())
                ret = quopri.decodestring(ret_tmp).decode(cset)
            return ret
    return qstr

def mbox_messages(mboxfile):
    # Generator sending messages one-by-one from mbox. I wrote this after observing that mailbox.mbox(mboxfile) took several minutes before returning the first message (it seems it needs to load/parse the whole mbox before starting, which can take long in the case of large mbox files...)
    lprev=''
    text=''
    with open(mboxfile,'r',encoding='utf8') as f:
        for line in f:
            if line.startswith('From ') and lprev=='\n' and "@xxx" in line: # FIXME: more reliable trigger ?
                #msg = email.message_from_bytes(text.encode())
                msg = email.message_from_string(text)
                msg.set_unixfrom(line) # FIXME: takes the "from" of next message instead of current
                text=''
                yield msg
            lprev=line
            text+=line

import mmap
def mbox_messages2(mboxfile):
    # Alternative approach. May be deleted later since it does not fix encoding issues (which are introduced by Google Takeout...). Need to check which version is faster
    text=b''
    mlen = os.path.getsize(mboxfile)
    with open(mboxfile,'r+b') as f:
        mm = mmap.mmap(f.fileno(), 0)
        i1=0
        while i1 < mlen:
            i2 = mm.find(b'\r\n\r\nFrom ', i1) # FIXME: more reliable trigger ?
            if i2==-1: # FIXME: needed ?
                print('ret')
                return
            text = mm[i1:i2]
            i3=text.find(b'\r\nX-GM-THRID:')
            msg = email.message_from_bytes(text)
            msg.set_unixfrom(text[:i3].decode())
            i1=i2+4 # +4 is to account for '\r\n\r\n'
            yield msg

#import mailbox
def scan_mbox(mboxfile, outdir):
    if not os.path.exists(outdir):
        os.makedirs(outdir)
    if os.path.exists(outdir+'/mails.db'):
        db=MDB(outdir+'/mails.db') # don't "drop table if exists"
    else:
        db=MDB(outdir+'/mails.db')
        db.createdb()
    mbox_size = os.path.getsize(mboxfile)
    #mbox = mailbox.mbox(mboxfile) # FIXME: slow
    k=0
    ltot=0
    for message in mbox_messages(mboxfile): #mbox.items():
    #for key,message in mbox.items():
        mfrom=message.get_unixfrom().replace('\n','') # in the case of gmail mbox, includes gmail_id followed by date
        flags = []
        labels = []
        if 'X-Gmail-Labels' in message:
            entries= qdecode(message['X-Gmail-Labels']).replace('_', ' ').split(',')
            for l in entries:
                if l.startswith('[') or l.startswith('IMAP '):
                    continue
                elif l in ('Ouvert','Non lus','Important','Favoris','Non lus'):
                    flags.append(l)
                else:
                    labels.append(l)
            labelstr = '_'.join(labels) if labels!= [] else None

        #print(mfrom)
        #mfrom=message.get_from() # in the case of gmail mbox, includes gmail_id followed by date
        msgdec=decodemail(message, outdir, labelstr)
        if msgdec == None:
            continue
        msgdec["msg_id"] = None
        msgdec["thread_id"] = int(msgdec["X-GM-THRID"])
        msgdec["gm_id"] = mfrom.split('@xxx')[0] #int(msgjson['gm_id'])
        msgdec['flags'] = '_'.join(flags) if flags!= [] else None
        #msgdec['gmail_timestamp']=datetime.fromtimestamp(msgjson['internal_date'])
        db.addmail(msgdec)
        db.conn.commit()
        k+=1
        ltot+=len(message.as_string())
        sys.stderr.write(f"\r\033[KProcessing message {k} ({ltot>>20}/{mbox_size>>20} MB) : {msgdec['Date']}")

def scan_maildir(rootdir, outdir, includelist=[]):
    pass

def scandir_gmvault(rootdir, outdir, includelist=[]): # '2009-01'
    if not os.path.exists(outdir):
        os.makedirs(outdir)
    if os.path.exists(outdir+'/mails.db'):
        db=MDB(outdir+'/mails.db') # don't "drop table if exists"
    else:
        db=MDB(outdir+'/mails.db')
        db.createdb()
    for dirname,_,files in os.walk(rootdir):
        included=False
        for k in includelist:
            if k in dirname:
                included=True
                break
        if included==False and len(includelist)>0:
            continue
        for entry in files:
            if entry.endswith(".meta"):
                continue
            id = entry[:entry.rfind('.eml')]
            if db.checkmail(id):
                sys.stderr.write("\r\033[KSkipping: " + id)
                continue
            msgjson=decodejson(dirname+'/'+id+".meta")

            # Process labels
            # Labels are concatenated into a single string (so it can correspond to a folder on the filesystem).
            labels = [l.replace('\\','') for l in msgjson['labels'] if not l.startswith('\\') or l in ('\\Sent', '\\Inbox')]
            flags = [f.replace('\\','') for f in msgjson['flags']]
            flags.extend([l.replace('\\','') for l in msgjson['labels'] if l.startswith('\\') and not l in ('\\Sent', '\\Inbox')])
            if len(labels)>1: # some labels are included in others and repeated multiple times => keep the longest (most complete) one
                for l1 in labels:
                    for l2 in labels:
                        if l1!=l2 and l2.startswith(l1):
                            labels.remove(l1)
            if "Inbox" in labels and "Sent" in labels:
                labels.remove('Inbox')
            if labels==[]:
                labels=['Inbox']
            labelstr='__'.join(labels).replace('\\', '').replace("[",'_').replace(']','_')
            if 'portant' in labelstr or "imap" in labelstr or "tarred" in labelstr: # Important|imap|Starred
                print("Processing: " + dirname+'/'+entry)
                print(labels)

            if not os.path.exists(outdir + '/' + labelstr):
                os.makedirs(outdir + '/' + labelstr)

            fp = gzip.open(dirname+'/'+entry, "rt") if entry.endswith(".eml.gz") else open(dirname+'/'+entry)
            #msg = email.parser.Parser().parse(fp)
            msg=email.message_from_file(fp)
            fp.close()
            msgdec = decodemail(msg, outdir, labelstr)
            if msgdec == None:
                continue
            msgdec["msg_id"]=msgjson["msg_id"]
            msgdec["thread_id"] = int(msgjson["thread_ids"])
            msgdec["gm_id"] = int(msgjson['gm_id'])
            msgdec['flags'] = '_'.join(flags)
            msgdec['gmail_timestamp']=datetime.fromtimestamp(msgjson['internal_date'])
            db.addmail(msgdec)
            sys.stderr.write("\r\033[KProcessing: " + entry + ', date : ' + msgdec['Date'])
        db.conn.commit()

def decodemail(msg, outdir1, labelstr='Default'):
    #_structure(msg)
    csets=msg.get_charsets()
    cset='utf-8'
    for c in csets:
        if c==None:
            continue
        if c.startswith('charset'):
            c=c[c.find('"')+1:c.rfind('"')]
        cset=cset_sanitize(c)
        break

    msgdec={}
    for myfield in ('From', 'To', 'Cc', 'Bcc', 'Date', 'Subject', 'X-GM-THRID'): # "Received"
        if myfield in msg:
            msgdec[myfield]=qdecode(msg[myfield]).replace('_', ' ')
        else:
            msgdec[myfield] = None
    if msgdec['Date']==None:
        mfrom=msg.get_unixfrom() # in the case of gmail mbox, includes gmail_id followed by date
        #mfrom=msg.get_from() # in the case of gmail mbox, includes gmail_id followed by date
        msgdec['Date'] = mfrom.replace('\n','').split('@xxx ')[1]

    #labelstr = msgdec['X-Gmail-Labels'] if 'X-Gmail-Labels' in msgdec and msgdec['X-Gmail-Labels']!=None else labelstr
    outdir= outdir1 + '/' + labelstr
    msgdec['Attachments'] = []
    msgdec['EmbeddedImg'] = {}
    msgdec['Size'] = 0
    msgdec['SizeAtt'] = 0
    msgdec['NumAtt'] = 0
    msgdec['Outdir'] = outdir
    msgdec['labelstr'] = labelstr
    msgdec['Date_parsed'] = dateparse_normalized(msgdec['Date'])

    #body2=msg.get_body(preferencelist=('plain', 'html'))
    decodepart(msg, msgdec) # recursive part
    if not 'Body' in msgdec and not 'BodyHTML' in msgdec:
        return None

    if not "BodyHTML" in msgdec and msgdec['Body'].find('[cid:') and len(msgdec['EmbeddedImg'].keys())>0:
        # When there is only plain text together with embedded images, generate the corresponding HTML with references to images
        msgdec["BodyHTML"] = "<html><head><title></title></head><body><pre>" + re.sub(r'\[(cid:.*)\]', '<img src="\\1">', msgdec['Body']) + "</pre></body></html>"
    if 'BodyHTML' in msgdec and msgdec['BodyHTML'].find('<img src="cid:'):
        # Embed images referenced in the HTML directly as base64 within the HTML document instead of separate files (so that the HTML is self-sufficient and only other attachments need to be extracted on the filesystem)
        for cid in msgdec['EmbeddedImg'].keys():
            msgdec["BodyHTML"]=msgdec["BodyHTML"].replace("cid:"+cid, msgdec['EmbeddedImg'][cid])

    if not 'Body' in msgdec:
        msgdec['Body'] = None
    else:
        msgdec["Size"] += len(msgdec['Body'].encode())
    if not 'BodyHTML' in msgdec:
        msgdec['BodyHTML'] = None
    else:
        msgdec["Size"] += len(msgdec['BodyHTML'].encode()) # by doing it here, we ensure that it also catches the size of attached images (that we embedded in base64 within the html previously)
    if not 'signature' in msgdec:
        msgdec['signature'] = None
    else:
        msgdec["Size"] += len(msgdec['signature'].encode())

    return msgdec

# A MIME message is made of different parts, which themselves can also embed a MIME contents with subparts, in a recursive structure
# Most of the time (always ?), the 'multipart/alternative' contains the two versions of the body (in plaintext and HTML, with embedded images for HTML in a subpart 'multipart/related')
# The attached files can then be extracted, but some special cases are pgp signatures (want to keep in the sqlite db rather than extract as a file) and winmail.dat (which themselves embed other parts)
def decodepart(part, msgdec, level=0):
    def extract_file(dir, filename, filecontents):
        if filecontents==None:
            return
        if not os.path.exists(dir):
            os.makedirs(dir)
        if filename==None or filename=="":
            filename="__noname__"
        hash = hashlib.md5() ; hash.update(filecontents)
        filemd5 = hash.hexdigest()
        while os.path.exists(dir+'/'+filename):
            filemd5_orig = md5sum(dir+'/'+filename)
            if(filemd5==filemd5_orig):
                return filename # no need to write the file again because content is identical
            # if we arrive here, this means another file with same filename already exist _and_ has a different content => rename new files with __2, __3, etc.
            ki=filename.rfind('.')
            if ki>0:
                k_base=filename[:ki]
                k_ext=filename[ki:]
            else:
                k_base=filename
                k_ext=""
            rx = re.search(r'([^_\.]+)__([0-9]+)',k_base)
            filename = rx.group(1) + '__' + str(int(rx.group(2))+1) + k_ext if rx else k_base + '__2' + k_ext

        with open(dir+'/'+filename, 'wb') as fp:
            fp.write(filecontents)
        os.utime(dir+'/'+filename, (msgdec["Date_parsed"],msgdec["Date_parsed"]))
        msgdec['Attachments'].append(filename)
        msgdec['SizeAtt'] += len(filecontents)
        msgdec['NumAtt'] += 1
        return filename

    while isinstance(part.get_payload(),email.message.Message):
        part=part.get_payload()
    if part.is_multipart():
        for subpart in part.get_payload():
            decodepart(subpart, msgdec, level+1) # recursive call (theoretically there could be any structure and any levels of nested messages)
        #if ctype=="multipart/alternative":
        #    pass
        #elif ctype=="multipart/related":
        #    pass

    else:
        ctype = part.get_content_type()
        cset=cset_sanitize(part.get_content_charset())
        dir=msgdec['Outdir']
        #print('  '*level + 'L' + str(level) + ' -> content-type : ' + ctype + ', cset=' + cset)
        if(ctype=="text/plain" and not "Body" in msgdec): # FIXME: we didn't check whether we are really in a "multipart/alternative" section
            try:
                body = part.get_payload(decode=True).decode(cset)
            except UnicodeDecodeError:
                body = part.get_payload(decode=False)
            msgdec['Body'] = body # FIXME: change meta charset to utf-8
        elif(ctype=="text/html" and not "BodyHTML" in msgdec): # FIXME: we didn't check whether we are really in a "multipart/alternative" section
            try:
                body = part.get_payload(decode=True).decode(cset)
            except UnicodeDecodeError:
                body = part.get_payload(decode=False)
            msgdec['BodyHTML'] = body
        elif "Content-ID" in part and ctype.startswith("image"): # FIXME: we didn't check whether we are really in a "multipart/related" section
            cid=part["Content-ID"][1:-1]
            body=cid
            msgdec['EmbeddedImg'][cid]="data:"+ctype+";base64,"+part.get_payload(decode=False).replace('\n','')
        elif part.get_filename(): # FIXME: we didn't check whether we are really in a "multipart/mixed" section
            #if ctype.startswith("application") or ctype.startswith("multipart"):
            #filename2=email.utils.collapse_rfc2231_value(filename2).strip()
            #filename2=part.get_param('filename', None, 'content-disposition')
            filename=part.get_filename()
            filename = qdecode(filename)
            filecontents = part.get_payload(decode=True)
            if (filename=="signature.asc" or filename=='PGP.sig') and not 'signature' in msgdec:
                msgdec['signature'] = filecontents.decode()
            #elif filename=="smime.p7s": # FIXME: check contents beyond file name
            #    msgdec['signature'] = part.get_payload(decode=False)
            # elif filename=='oledata.mso':
            #     pass # FIXME: handle this
            elif filename=='winmail.dat':
                k=extract_file(dir, 'winmail.dat', filecontents) # FIXME: not needed anymore after we extract the other stuffs (embedded RTF, etc)
                t = TNEF(filecontents, do_checksum=True)
                #print(t.codepage)
                #t.dump(force_strings=True)
                if hasattr(t,'body'):
                    data=getattr(t, 'body')
                    if isinstance(data,str):
                        data=data.encode()
                    extract_file(dir,secure_filename(k)+'.txt', data)
                if hasattr(t,'htmlbody'):
                    data=getattr(t, 'htmlbody')
                    if isinstance(data,str):
                        data=data.encode()
                    extract_file(dir,secure_filename(k)+'.html', data)
                if hasattr(t,'rtfbody'):
                    data=getattr(t, 'rtfbody')
                    if isinstance(data,str):
                        data=data.encode()
                    extract_file(dir,secure_filename(k)+'.rtf', data)

                for a in t.attachments:
                    winname = 'winmail_'+secure_filename(a.long_filename())
                    # if isinstance(a._name, bytes):
                    #     winname=a._name.decode('cp1252').strip('\x00')
                    # else:
                    #     winname=a._name.strip('\x00')
                    if isinstance((a.data), bytes):
                        dat=a.data
                    elif isinstance((a.data), list):
                        dat=a.data[0]
                    extract_file(dir, winname, dat)
            else:
                filename = secure_filename(filename)
                if filename==None or filename=="":
                    filename="__noname__" + ctype.replace('/','_')
                extract_file(dir, filename, filecontents)
        else:
            body="__None__" #+ str(part.get_payload(decode=True))

def decodejson(filename):
    with open(filename) as fp:
        my_json = json.loads(fp.read())
    return my_json

class MDB():
    def __init__(self, dbname, domagic=False):
        self.conn = sqlite3.connect(dbname)
        #self.init_path=init_path.rstrip('/')

    def createdb(self):
        cur = self.conn.cursor() # FIXME: "contacts" and "attachment" tables are still unused
        cur.executescript('''
            drop table if exists messages;
            create table messages(
                id integer primary key,
                gmail_msgid text,
                gmail_threadid integer,
                gmail_labels text,
                gm_id integer,
                datetime integer,
                msgfrom integer,
                msgto text,
                msgcc text,
                subject text,
                body_text text,
                body_html text,
                attachments text,
                flags text,
                signature text,
                size integer,
                sizeatt integer,
                numatt integer
            );
            create index messages_gm_id_idx on messages(gm_id);

            PRAGMA main.page_size=4096;
            PRAGMA main.cache_size=10000;
            PRAGMA main.locking_mode=EXCLUSIVE;
            PRAGMA main.synchronous=NORMAL;
        ''') # PRAGMA main.journal_mode=WAL;

    def checkmail(self, gm_id):
        cur = self.conn.cursor()
        rs=cur.execute('select id from messages where gm_id=?', (gm_id,)).fetchall()
        if len(rs)>0:
            return True
        return False

    def addmail(self, m):
        cur = self.conn.cursor()
        cur.execute("insert into messages values (null, ?,?,?,?, ?,?,?,?, ?,?,?,?, ?, ?,?,?,?)", (
            m["msg_id"], m["thread_id"], m['labelstr'], m['gm_id'],
            int(m['Date_parsed']), m['From'], m['To'], m['Cc'],
            m["Subject"], m['Body'], m['BodyHTML'], '¤'.join(m["Attachments"]), m['flags'], m["signature"],
            m["Size"],m["SizeAtt"],m["NumAtt"]
        ))

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="subcommand", required=True)

    parser_createdb = subparsers.add_parser('gmvault', help="Scan directory")
    parser_createdb.add_argument("gmvault_dir", help="GMVault dir or mountpoint")
    parser_createdb.add_argument("outdir", help="Output dir")

    parser_mbox = subparsers.add_parser('mbox', help="Scan MBox from Google Takeout")
    parser_mbox.add_argument("mboxfile", help="MBox file")
    parser_mbox.add_argument("outdir", help="Output dir")

    parser_gui = subparsers.add_parser('gui', help="Launch GUI")
    parser_gui.add_argument("dbfile", help="DB file")

    args = parser.parse_args()

    if args.subcommand=="gmvault":
        scandir_gmvault(args.gmvault_dir + "/db", args.outdir)
    elif args.subcommand=="mbox":
        scan_mbox(args.mboxfile,args.outdir)
    elif args.subcommand=="gui":
        gui(args.dbfile)
