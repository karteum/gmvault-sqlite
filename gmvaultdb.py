#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
@author: Adrien Demarez
License: GPLv3 https://www.gnu.org/licenses/gpl-3.0.en.html

This program
- walks through a folder from a GMvault backup (assuming .eml are not gzipped. In my case I archived the whole dir in squashfs-lzma so it was better to leave the eml uncompressed).
- parses the .meta and .eml files, the latter can be MIME with various encoding, attachments, etc.
- stores the emails (header, txt, html, signatures) in an SQLite database. For HTML, the attached images are extracted and inserted as base64 embedded images within the html in order to avoid keeping a separate file
- extracts the other attached files to a dedicated folder (so all the attached files can be accessed directly through the filesystem). If the same file (same name, same md5) has already been extracted, it will not be stored twice. If a file with similar name but different md5 has already been extracted, it will be stored with a different name
- adds a small GUI to walk through the emails and add additional "where" conditions to the SQL query (for the moment it works with plain sqlite including "like" clauses. In the future I will test SQLite's full-text search features)

TODO: (among other things)
- refactor code. Put functions within the dedicated DB class
- solve encoding issues for HTML
- DB schema is simple but not optimal  (3NF, etc)
- implement full-text search with sqlite
- populate contacts and attachments tables
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

from PySide2.QtWidgets import *
#from PySide2.QtWebEngineWidgets import *
from PySide2.QtCore import *
from PySide2.QtSql import *
from PySide2.QtGui import *

def gui(dbfile):
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
            item.setData(1, os.path.dirname(dbfile)+'/'+myquery.value(3)+'/'+att)
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
#        model.setQuery(db.exec_("select id, gmail_threadid thread, gm_id eml, gmail_labels labels, datetime(messages.datetime, 'unixepoch') as dt, msgfrom, msgto, msgcc, subject, flags, signature, attachments,size,sizeatt,numatt from messages" + tmp))
        model.setQuery(db.exec_("select id, gmail_threadid thread, gm_id eml, gmail_labels labels, datetime(messages.datetime, 'unixepoch') as dt, msgfrom, msgto, msgcc, subject, flags, signature, attachments from messages" + tmp))
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

    availableGeometry = app.desktop().availableGeometry(mainWin)
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
        for block in iter(lambda: f.read(blocksize), b""):
            hash.update(block)
    return hash.hexdigest()

def scandir(rootdir, outdir, includelist=['2009-01']):
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

            msgdec=decodemail(dirname+'/'+entry, outdir, labelstr)
            if not 'Body' in msgdec and not 'BodyHTML' in msgdec:
                continue
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
            msgdec['flags'] = '_'.join(flags)
            msgdec['gmail_timestamp']=datetime.fromtimestamp(msgjson['internal_date'])
            db.addmail(msgdec, msgjson)
        db.conn.commit()

def dateparse_normalized(datestr):
    for tmp in datestr.split(','): # Remove everything before and after (potential) comma, since they are error prone (e.g. if the string starts with "Wen, ..." instead of "Wed, ..." the parser would fail without this. Same with regards to the end of the string)
        if re.search(r'..:..:..', tmp):
            tmp = re.sub(r'(.*..:..:..) .*', '\\1', tmp)
            break
    return int(datetime.timestamp(dateparse(tmp)))

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

def decodemail(filename, outdir1, labelstr='Default'):
    outdir= outdir1 + '/' + labelstr
    #body = bytes(body,'utf-8').decode('unicode-escape')!
    with open(filename) as fp:
        #msg = email.parser.Parser().parse(fp)
        msg=email.message_from_file(fp)
        #print(filename)
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
        for myfield in ('From', 'To', 'Cc', 'Bcc', 'Date', 'Subject'): # "Received"
            if myfield in msg:
                if msg[myfield].startswith('=?'):
                    myfield_qp_list = msg[myfield].split('?')
                    if myfield_qp_list[2] in ["Q", "B", 'q', 'b']:
                        cset = cset_sanitize(myfield_qp_list[1])
                        myfield_val = myfield_qp_list[3].replace('_', ' ')
                    else:
                        myfield_val = msg[myfield][2:-2].replace('_', ' ')
                    try:
                        msgdec[myfield] = quopri.decodestring(myfield_val).decode(cset) # iso8859-1,utf-8,'windows-1252'
                    except ValueError:
                        myfield_val2 = quopri.encodestring(myfield_val.encode())
                        msgdec[myfield] = quopri.decodestring(myfield_val2).decode(cset)
                else:
                    msgdec[myfield] = msg[myfield]
            else:
                msgdec[myfield] = None

        msgdec['Attachments'] = []
        msgdec['EmbeddedImg'] = {}
        msgdec['Size'] = 0
        msgdec['SizeAtt'] = 0
        msgdec['NumAtt'] = 0
        msgdec['Outdir'] = outdir
        msgdec['labelstr'] = labelstr
        msgdec['Date_parsed'] = dateparse_normalized(msgdec['Date'])
        sys.stderr.write("\r\033[KProcessing: " + filename + ', date : ' + msgdec['Date'])

    #body2=msg.get_body(preferencelist=('plain', 'html'))
    decodepart(msg, msgdec)

    if not "BodyHTML" in msgdec and "Body" in msgdec and msgdec['Body'].find('[cid:') and len(msgdec['EmbeddedImg'].keys())>0:
        # When there is only plain text together with embedded images, generate the corresponding HTML with references to images
        msgdec["BodyHTML"] = "<html><head><title></title></head><body><pre>" + re.sub(r'\[(cid:.*)\]', '<img src="\\1">', msgdec['Body']) + "</pre></body></html>"
    if 'BodyHTML' in msgdec and msgdec['BodyHTML'].find('<img src="cid:'):
        # Embed images referenced in the HTML directly as base64 within the HTML document instead of separate files (so that the HTML is self-sufficient and only other attachments need to be extracted on the filesystem)
        for cid in msgdec['EmbeddedImg'].keys():
            msgdec["BodyHTML"]=msgdec["BodyHTML"].replace("cid:"+cid, msgdec['EmbeddedImg'][cid])

    return msgdec

# A MIME message is made of different parts, which themselves can also embed a MIME contents with subparts, in a recursive structure
# Most of the time (always ?), the 'multipart/alternative' contains the two versions of the body (in plaintext and HTML, with embedded images for HTML in a subpart 'multipart/related')
# The attached files can then be extracted, but some special cases are pgp signatures (want to keep in the sqlite db rather than extract as a file) and winmail.dat (which themselves embed other parts)
def decodepart(part, msgdec, level=0):
    def extract_file(dir, filename, filecontents):
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
            if rx:
                filename = rx.group(1) + '__' + str(int(rx.group(2))+1) + k_ext
            else:
                filename = k_base + '__2' + k_ext

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
            if filename.startswith('=?'): # parse the "Q-encoding"
                filename_qp_list = filename.split('?')
                if filename_qp_list[2] in ["Q", "B", 'q', 'b']:
                    cset_filename = cset_sanitize(filename_qp_list[1]) # FIXME: what if multiline filename has different encoding between lines ? (can it happen ?)
                    filename_tmp = ""
                    nlines = int((len(filename_qp_list) - 1) / 4)
                    for k in range(nlines):
                        filename_tmp += filename_qp_list[3+4*k]
                    try:
                        filename = quopri.decodestring(filename_tmp).decode(cset_filename) # filename_qp_list[3]
                    except UnicodeDecodeError:
                        filename = quopri.decodestring(filename_tmp).decode('iso8859-1') # Handle case where utf-8 is announced but the real encoding is different (I only got this bug once and the real encoding was iso8859-1). FIXME: handle more cases i.e. guess the real encoding

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
                    extract_file(dir,secure_filename(k)+'.txt', getattr(t, 'body'))
                if hasattr(t,'htmlbody'):
                    extract_file(dir,secure_filename(k)+'.html', getattr(t, 'htmlbody'))
                if hasattr(t,'rtfbody'):
                    extract_file(dir,secure_filename(k)+'.rtf', getattr(t, 'rtfbody'))

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
            drop table if exists contacts;
            create table contacts(
                id integer primary key autoincrement,
                name text,
                email text
            );
            drop table if exists messages;
            create table messages(
                id integer primary key autoincrement,
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

            drop table if exists attachments;
            create table attachments(
                id integer primary key autoincrement,
                messageid integer,
                name text,
                size integer,
                hash text
            );

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

    def addmail(self, m, j):
        cur = self.conn.cursor()
        cur.execute("insert into messages values (null, ?,?,?,?, ?,?,?,?, ?,?,?,?, ?, ?,?,?,?)", (
            j["msg_id"], int(j["thread_ids"]), m['labelstr'], int(j['gm_id']),
            int(m['Date_parsed']), m['From'], m['To'], m['Cc'],
            m["Subject"], m['Body'], m['BodyHTML'], '¤'.join(m["Attachments"]), m['flags'], m["signature"],
            m["Size"],m["SizeAtt"],m["NumAtt"]
        ))


def usage():
    print("""Usage :
    gmvault_sql createdb gmvault_dir out_dir : create out_dir with mails.db file and subdirs with attachments
    gmvault_sql gui db_file
    """)

if __name__ == "__main__":
    if len(sys.argv) < 3:
        usage()
        exit()
    opmode=sys.argv[1] # FIXME: handle errors !
    if opmode=="createdb":
        gmvault_dir=sys.argv[2]
        outdir=sys.argv[3]
        scandir(gmvault_dir + "/db", outdir) # FIXME: better name than "scandir". Place it within MDB class...
    elif opmode=="gui":
        dbfile=sys.argv[2]
        gui(dbfile)
