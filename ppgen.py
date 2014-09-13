#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import argparse
from time import gmtime, strftime
import re, sys, string, os, platform
import textwrap
import codecs
import unicodedata
from collections import defaultdict
import shlex
import random, inspect
from math import sqrt

VERSION="3.24N" # allow .nr pnc to set page number color

NOW = strftime("%Y-%m-%d %H:%M:%S", gmtime()) + " GMT"

"""
  ppgen.py

  Copyright 2014, Asylum Computer Services LLC
  Licensed under the MIT license:
  http://www.opensource.org/licenses/mit-license.php

  Roger Frank (rfrank@rfrank.net)

  Permission is hereby granted, free of charge, to any person obtaining
  a copy of this software and associated documentation files (the
  "Software"), to deal in the Software without restriction, including
  without limitation the rights to use, copy, modify, merge, publish,
  distribute, sublicense, and/or sell copies of the Software, and to
  permit persons to whom the Software is furnished to do so, subject to
  the following conditions:

  The above copyright notice and this permission notice shall be
  included in all copies or substantial portions of the Software.

  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
  EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
  MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
  IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
  CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
  TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
  SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

"""

empty = re.compile("^$")

# - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    
# displays the line that called us and the message    
def xp(msg):
  frame,filename,line_number,function_name,lines,index = inspect.stack()[1]
  print("{:5}: {}".format(line_number,msg))

# ====== Book, parent of text and ppnh classes ==========================================

class Book(object):
  wb = [] # working buffer
  eb = [] # emit buffer
  regLL = 72 # line length
  regIN = 0 # indent
  regTI = 0 # temporary indent
  regAD = 1 # 1 if justified, 0 if ragged right
  latin1only = False

  instack = [] # last indent level
  llstack = [] # last line length
  psstack = [] # last para spacing
  nfstack = [] # block stack
  warnings = [] # warnings displayed
  cl = 0 # current line number
  tcnt = 0 # table counter
  pindent = False
  pnshow = False # set to True if page numbering found in source file
  pnlink = False # create links but do not show page number
  csslc = 900 # CSS line counter
  dtitle = "" # display title for HTML
  cimage = "cover.jpg" # default cover image

  nregs = {} # named registers
  macro = {} # user macro storage
  
  mau = [] # UTF-8
  mal = [] # user-defined Latin-1  
  
  linelimitwarning = 75

  def __init__(self, args, renc):
    del self.wb[:]
    del self.eb[:]
    self.renc = renc # requested output encoding (t, u, or h)
    self.debug = args.debug
    self.srcfile = args.infile
    self.anonymous = args.anonymous
    self.log = args.log
    self.wrapper = textwrap.TextWrapper()
    self.wrapper.break_long_words = False
    self.wrapper.break_on_hyphens = False
    self.nregs["psi"] = "0" # default above/below paragraph spacing for indented text
    self.nregs["psb"] = "1.0em" # default above/below paragraph spacing for block text
    self.nregs["pnc"] = "silver" # use to define page number color in HTML
    self.encoding = "" # input file encoding
    self.pageno = "" # page number stored as string

  # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  # get the value of the requested parameter from attr string
  # remove parameter from string, return string and parameter
  def get_id(self, tgt, attr, np=2):
    
    done = False
    m = re.search(r"{}='(.*?)'".format(tgt), attr)  # single quotes
    if m:
      the_id = m.group(1)
      attr = re.sub(m.group(0), "", attr)
      done = True
      
    if not done:
      m = re.search(r"{}=\"(.*?)\"".format(tgt), attr)  # double quotes
      if m:
        the_id = m.group(1)
        attr = re.sub(m.group(0), "", attr)
        done = True

    if not done:
      m = re.search(r"{}=(.*?)($|[ >])".format(tgt), attr)  # no quotes
      if m:
        the_id = m.group(1)
        attr = re.sub(m.group(0), "", attr)
        done = True

    # if the user was looking for an "id-", then check it.
    if tgt == "id":
      self.checkId(the_id)  

    if done:
      if np == 1:
        return (attr)
      if np == 2:
        return (attr, the_id)
      if np == 3:
        return (attr, the_id, m.group(0))
    else:
      # should never get here
      self.fatal("could not process {} in {}".format(tgt, attr)) 

  # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  # load file from specified source file
  def loadFile(self, fn):
    self.wb = []
    self.encoding = ""

    if not os.path.isfile(fn):
      self.fatal("specified file {} not found".format(fn))

    if self.encoding == "":
      try:
        wbuf = open(fn, "r", encoding='ascii').read()
        self.encoding = "ASCII" # we consider ASCII as a subset of Latin-1 for DP purposes
        self.wb = wbuf.split("\n")
      except Exception as e:
        pass

    if self.encoding == "":
      try:
        wbuf = open(fn, "rU", encoding='UTF-8').read()
        self.encoding = "utf_8"
        self.wb = wbuf.split("\n")
        # remove BOM on first line if present
        t = ":".join("{0:x}".format(ord(c)) for c in self.wb[0])
        if t[0:4] == 'feff':
          self.wb[0] = self.wb[0][1:]
      except:
        pass

    if self.encoding == "":
      try:
        wbuf = open(fn, "r", encoding='latin_1').read()
        self.encoding = "latin_1"
        self.wb = wbuf.split("\n")
        self.latin1only = True  # only generate Latin-1 output
      except Exception as e:
        pass

    if self.encoding == "":
      self.fatal("cannot determine input file decoding")
    else:
      # self.info("input file is: {}".format(self.encoding))
      if self.encoding == "ASCII":
        self.encoding = "latin_1" # handle ASCII as Latin-1 for DP purposes
    while self.wb[-1] == "": # no trailing blank lines
      self.wb.pop()

    for i in range(len(self.wb)):
      self.wb[i] = self.wb[i].rstrip()
    
  # log print
  def lprint(self, msg):
    if self.log:
      print(msg)

  def rp(self, flag, msg):
    print("=> {} {}".format(flag,msg))    

  # display error message and exit
  def fatal(self, message):
    sys.stderr.write("FATAL: " + message + "\n")
    exit(1)

  # display warning
  def warn(self, message):
    if message not in self.warnings: # don't give exact same warning more than once.
      self.warnings.append(message)
      sys.stderr.write("**warning: " + message + "\n")

  # display informational message
  def info(self, message):
    sys.stderr.write("  info: " + message + "\n")

  # all dot commands are switched here
  def doDot(self):
    dotcmd = self.wb[self.cl][0:3]
    if ".h1" == dotcmd:
      self.doH1()
    elif ".h2" == dotcmd:
      self.doH2()
    elif ".h3" == dotcmd:
      self.doH3()
    elif ".sp" == dotcmd:
      self.doSpace()
    elif ".fs" == dotcmd:
      self.doFontSize()
    elif ".il" == dotcmd:
      self.doIllo()
    elif ".in" == dotcmd:
      self.doIn()
    elif ".ll" == dotcmd:
      self.doLl()
    elif ".ti" == dotcmd:
      self.doTi()
    elif ".li" == dotcmd:
      self.doLit()
    elif ".de" == dotcmd:
      self.doDef()
    elif ".pb" == dotcmd:
      self.doPb()
    elif ".hr" == dotcmd:
      self.doHr()
    elif ".tb" == dotcmd:
      self.doTbreak()
    elif ".fn" == dotcmd:
      self.doFnote()
    elif ".fm" == dotcmd:
      self.doFmark()
    elif ".pi" == dotcmd: # paragraph indenting
      self.doPi()
    elif ".ni" == dotcmd: # no (paragraph) indenting
      self.doNi()
    elif ".ta" == dotcmd: # tables
      self.doTable() 
    elif ".di" == dotcmd: # dropcap images
      self.doDropimage()
    elif ".dc" == dotcmd: # dropcap alpha
      self.doDropcap()
    elif ".na" == dotcmd: # no adjust (ragged right)
      self.doNa()
    elif ".ad" == dotcmd: # adjust (justify l/r margins)
      self.doAd()
    elif ".rj" == dotcmd: # 03-Apr-2014 right justify lines
      self.doRj()
    elif ".nf" == dotcmd:
      self.doNf()
    elif ".nr" == dotcmd: # named register
      self.doNr()
    else:
      self.fatal("unhandled dot command: {}".format(self.wb[self.cl]))

  def crash_w_context(self, msg, i, r=5):
    print("{}\ncontext:".format(msg))
    startline = max(0,i-r)
    endline = min(len(self.wb),i+r)
    for j in range(startline,endline):
      if j == i:
        print(">> {}".format(self.wb[j]))
      else:
        print("   {}".format(self.wb[j]))
    self.fatal("exiting")

  def preProcessCommon(self):

    def pushk(s, i):
      self.nfstack.append( (s,i) )

    def popk():
      t = self.nfstack.pop() # pops a tuple
      return t
    
    # if source file is UTF-8 and requested encoding is Latin-1, down-convert
    if self.encoding == "utf_8" and self.renc == "l":
      for j,ch in enumerate(self.mau):
        for i in range(len(self.wb)): # O=n^2
          self.wb[i] = re.sub(ch, self.mal[j], self.wb[i])
      # user-defined character mapping complete, now do default mapping to Latin-1
      self.utoLat()
          
    # .if conditionals (moved to preProcessCommon 28-Aug-2014)
    text = []
    keep = True
    for line in self.wb:

      m = re.match(r"\.if (\w)", line)  # start of conditional
      if m:
        keep = False
        if m.group(1) == 't' and self.renc in "lut":
          keep = True
        if m.group(1) == 'h' and self.renc == "h":
          keep = True
        continue

      if line == ".if-":
        keep = True
        continue

      if keep:
        text.append(line)
    self.wb = text    
    
    # suspense: mark for deletion Feb 2015
    say_bye = False
    for i,line in enumerate(self.wb):
      if ".." == line:
        self.warn("'..' tag line {}".format(i))
        say_bye = True
    if say_bye:
        self.fatal("'..' tags must be replaced with explicit forms.")

    for i,line in enumerate(self.wb):
      if re.match(".nf [clrb]-", line):
        self.warn("misformatted closing tag {} line {}".format(line, i))
        say_bye = True
    if say_bye:
        self.fatal("misformatted closing tags")
    
    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    # process character mappings
    # character mappings are from the UTF-8 representation to Latin-1
    i = 0
    del self.mau[:]
    del self.mal[:]
    self.mau.append("—")   # maps a dash in UTF-8 to "--" in Latin-1 
    self.mal.append("--")
    while i < len(self.wb):
      m = re.match(r"\.ma ", self.wb[i])
      if m:
        clex = shlex.split(self.wb[i])
        self.mau.append(clex[1])
        self.mal.append(clex[2])
        del self.wb[i]
        i -= 1
      i += 1

    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    # long caption lines may end with a single backslash (25-Jun-2014)
    i = 0
    while i < len(self.wb):
      if self.wb[i].startswith(".ca"): # captions only. allow .de multi-line CSS passthrough
        if re.search(r"\\$", self.wb[i]):
          self.wb[i] = re.sub(r"\\$", " ", self.wb[i]) + self.wb[i+1]
          del self.wb[i+1]
          i -= 1
      i += 1

    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    # courtesy remaps
    #
    i = 0
    while i < len(self.wb):
      if not self.wb[i].startswith("."):
        i += 1
        continue
      # courtesy maps
      if ".nf" == self.wb[i]:
        self.wb[i] = ".nf l"
      if ".sp" == self.wb[i]:
        self.wb[i] = ".sp 1"
      if ".hr" == self.wb[i]:
        self.wb[i] = ".hr 100%"
      if ".ti" == self.wb[i]:
        self.wb[i] = ".ti 2"
      if ".ce" == self.wb[i]:
        self.wb[i] = ".ce 1"
      if ".rj" == self.wb[i]:
        self.wb[i] = ".rj 1"
      i += 1

    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    # other comments
    i = 0
    while i < len(self.wb):
      if  re.match(r"\/\/", self.wb[i]): # entire line is a comment
        del self.wb[i]
        continue
      if re.search(r"\/\/.*$", self.wb[i]):
        self.wb[i] = re.sub(r"\/\/.*$", "", self.wb[i])
        self.wb[i] = self.wb[i].rstrip()
      i += 1

    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    # remaps of protected characters and escapes
    for i, line in enumerate(self.wb):
      # dots not part of dot directive
      self.wb[i] = self.wb[i].replace("....", "ⓓⓓⓓⓓ") # four dot ellipsis
      self.wb[i] = self.wb[i].replace("...", "ⓓⓓⓓ") # 3 dot ellipsis
      self.wb[i] = self.wb[i].replace(". . .", "ⓓⓢⓓⓢⓓ") # 3 dot ellipsis, spaced
      self.wb[i] = self.wb[i].replace("\. \. \.", "ⓓⓢⓓⓢⓓ") # 3 dot ellipsis, spaced
      # escaped characters
      self.wb[i] = self.wb[i].replace(r"\{", "①")
      self.wb[i] = self.wb[i].replace(r"\}", "②")
      self.wb[i] = self.wb[i].replace(r"\[", "③")
      self.wb[i] = self.wb[i].replace(r"\]", "④")
      self.wb[i] = self.wb[i].replace(r"\<", "⑤")
      self.wb[i] = self.wb[i].replace(r"\:", "⑥")
      self.wb[i] = self.wb[i].replace(r"\-", "⑨")
      # spacing
      self.wb[i] = self.wb[i].replace(r'\ ', "ⓢ") # non-breaking space
      self.wb[i] = self.wb[i].replace(r'\_', "ⓢ") # alternate non-breaking space
      self.wb[i] = self.wb[i].replace(r"\&", "ⓣ") # zero space
      self.wb[i] = self.wb[i].replace(r"\^", "ⓤ") # thin space (after italics)
      self.wb[i] = self.wb[i].replace(r"\|", "ⓥ") # thick space (between ellipsis dots)
      # special characters
      # leave alone if in literal block (correct way, not yet implemented)
      # map &nbsp; to non-breaking space
      # 10-Sep-2014: I don't fully understand why I did this mapping
      if not self.wb[i].startswith(".dt"):
        self.wb[i] = self.wb[i].replace("&nbsp;", "ⓢ") # ampersand
        self.wb[i] = self.wb[i].replace("&", "Ⓩ") # ampersand
      
    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    # define macro
    # .dm name
    # .dm name $1 $2
    # macro line 1
    # macro line 2
    # .dm-
    i = 0
    while i < len(self.wb):
      if self.wb[i].startswith(".dm"):
        tlex = shlex.split(self.wb[i])
        macroid = tlex[1] # string
        del self.wb[i]
        t = []
        while self.wb[i] != ".dm-":
          t.append(self.wb[i])
          del self.wb[i]
        del self.wb[i] # the closing .dm-
        # macro is stored in t[]
        self.macro[macroid] = t
        i -= 1
      i += 1

    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    # play macro
    # .pm name
    i = 0
    while i < len(self.wb):
      if self.wb[i].startswith(".pm"):
        tlex = shlex.split(self.wb[i])  # ".pm" "tnote" "a" "<li>"
        macroid = tlex[1]  # "tnote"
        # t = self.macro[macroid].copy() # after 3.3 only
        # t = self.macro[macroid][:] # another way
        if not macroid in self.macro:
          self.fatal("undefined macro: {}".format(macroid))
        t = list(self.macro[macroid]) # all the lines in this macro as previously defined
        for j,line in enumerate(t): # for each line
          m = re.search(r'\$(\d)', t[j]) # is there a substitution?
          while m:
            t[j] = re.sub(r'\$\d', tlex[int(m.group(1))+1], t[j], 1)
            m = re.search(r'\$(\d)', t[j]) # another substitution on same line
        self.wb[i:i+1] = t
        i -= 1
      i += 1

    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    # map .ce into equivalent .nf c (02-Aug-2014 3.13)
    # do not map if inside a no-fill block (31-Aug-2014 3.23D)
    # needs to happen after conditionals and macro expansion
    i = 0
    inNF = False
    while i < len(self.wb):
      if ".ce" == self.wb[i]:
        self.wb[i] = ".ce 1"
      if self.wb[i].startswith(".nf-"):
        inNF = False
        i += 1
        continue
      if self.wb[i].startswith(".nf"):
        inNF = True
        i += 1
        continue
      if not inNF and self.wb[i].startswith(".ce"):
        m = re.match(r".ce (\d+)", self.wb[i])
        if m:
          nlines = int(m.group(1))
          self.wb[i] = ".nf c"
          self.wb.insert(i+nlines+1, ".nf-")
        else:
          self.fatal("malformed .ce directive: {}".format(self.wb[i]))
      i += 1
      
    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    # 05-Jun-2014 allow .sp inside a .nf block
    i = 0
    inNF = False
    while i < len(self.wb):
      if re.match(r"\.nf .", self.wb[i]):
        inNF = True
      if re.match(r"\.nf-", self.wb[i]):
        inNF = False
      if inNF and self.wb[i].startswith(".sp"):
        m = re.match(r"\.sp (\d+)", self.wb[i])
        if m:
          nBlankLines = int(m.group(1))
          # remove any contingent blank lines first
          del self.wb[i]
          while empty.match(self.wb[i-1]):
            del self.wb[i-1]
            i -= 1
          while empty.match(self.wb[i]):
            del self.wb[i]
          # then populate with user-specified count of blank lines
          while nBlankLines > 0:
            self.wb.insert(i, "")
            nBlankLines -= 1
      i += 1

    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    # ignored text removed in preprocessor
    i = 0
    while i < len(self.wb):
      # one line
      if re.match(r"\.ig ",self.wb[i]): # single line
        del self.wb[i]
      if ".ig" == self.wb[i]: # multi-line
        while i < len(self.wb) and self.wb[i] != ".ig-":
          del self.wb[i]
        if i < len(self.wb):
          del self.wb[i] # the ".ig-"
        else:
          self.fatal("unterminated .ig command")
      i += 1

    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    # search for display title directive, record and remove
    i = 0
    while i < len(self.wb):
      # option with a value
      m = re.match(r"\.dt (.*)", self.wb[i])
      if m:
        self.dtitle = m.group(1)
        del self.wb[i]
        i -= 1
      i += 1

    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    # search for cover image directive, record and remove
    i = 0
    while i < len(self.wb):
      # option with a value
      m = re.match(r"\.ci (\S*)", self.wb[i])
      if m:
        self.cimage = m.group(1)
        del self.wb[i]
        i -= 1
      i += 1

    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    # .mt has been eliminated 22-May-2014
    i = 0
    while i < len(self.wb):
      if self.wb[i].startswith(".mt"):
        self.warn("{} <- user metadata no longer supported.".format(self.wb[i]))
        del(self.wb[i])
        i -= 1
      i += 1

    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    # superscripts, subscripts
    for i in range(len(self.wb)):

      pat = re.compile("\^([^\{])")
      m = re.search(pat, self.wb[i]) # single character superscript
      while m:
        suptext = m.group(1)
        self.wb[i] = re.sub(pat, "◸{}◹".format(suptext), self.wb[i], 1) 
        m = re.search(pat, self.wb[i])     

      pat = re.compile("\^\{(.*?)\}")
      m = re.search(pat, self.wb[i])
      while m:
        suptext = m.group(1)
        self.wb[i] = re.sub(pat, "◸{}◹".format(suptext), self.wb[i], 1)
        m = re.search(pat, self.wb[i])

      pat = re.compile("_\{(.*?)\}")
      m = re.search(pat, self.wb[i])
      while m:
        subtext = m.group(1)
        self.wb[i] = re.sub(pat, "◺{}◿".format(subtext), self.wb[i], 1)
        m = re.search(pat, self.wb[i])

    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    # map small caps to <sc> or <SC>
    # affects text format only
    # if <sc>, default handling: display as ALL CAPS in text
    # if <SC>, alternate handling: do not display as all caps. retain case in text.
    sctoUpper = True # default is to ALL CAPS in text
    i = 0
    while i < len(self.wb):
      if self.wb[i].startswith(".sc off" ):
        sctoUpper = False
        del(self.wb[i])
        self.warn(".sc option is deprecated") # 04-Jul-2014
      if self.wb[i].startswith(".sc on" ):
        sctoUpper = True
        del(self.wb[i])
        self.warn(".sc option is deprecated")
      if not sctoUpper:
        self.wb[i] = self.wb[i].replace("<sc","<SC")
        self.wb[i] = self.wb[i].replace("</sc","</SC")
      i += 1

    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    # map italics to <i> or <I>
    # affects text format only
    # if <i>, default handling: mark with underscore in text
    # if <I>, alternate handling: will not mark with underscore in text
    itMark = True # default is to mark italics in text
    i = 0
    while i < len(self.wb):
      if self.wb[i].startswith(".it off" ):
        itMark = False
        del(self.wb[i])
        self.warn(".it option is deprecated") # 04-Jul-2014
      if self.wb[i].startswith(".it on" ):
        itMark = True
        del(self.wb[i])
        self.warn(".it option is deprecated")
      if not itMark:
        self.wb[i] = self.wb[i].replace("<i","<I")
        self.wb[i] = self.wb[i].replace("</i","</I")
      i += 1

    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    # map bold to <b> or <B>
    # affects text format only
    # if <b>, default handling: mark with = in text
    # if <B>, alternate handling: will not mark with = in text
    bdMark = True # default is to mark bold in text
    i = 0
    while i < len(self.wb):
      if self.wb[i].startswith(".bd off" ):
        bdMark = False
        del(self.wb[i])
        self.warn(".bd option is deprecated") # 04-Jul-2014
      if self.wb[i].startswith(".bd on" ):
        bdMark = True
        del(self.wb[i])
        self.warn(".bd option is deprecated")
      if not bdMark:
        self.wb[i] = self.wb[i].replace("<b","<B")
        self.wb[i] = self.wb[i].replace("</b","</B")
      i += 1

    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    # set pnshow, pnlink variables
    # if any .pn numeric is seen, pnshow <- True
    # override with .pn off
    override = False
    self.pnshow = False # generate links and show
    self.pnlink = False # generate links but do not display
    for i,t in enumerate(self.wb):
      if self.wb[i].startswith(".pn link"):
        self.pnlink = True
        self.wb[i] = ""
      if self.wb[i].startswith(".pn off"):
        override = True
        self.wb[i] = ""
      # if re.match(".pn \d", self.wb[i]): # any numeric explicit page number
      if re.match(".pn (.+)", self.wb[i]): # any explicit page number
        self.pnshow = True
    if override:
      self.pnshow = False # disable visible page numbers

# ====== ppt ============================================================================

# this class is used to generate UTF-8 or Latin-1 (ANSI) text
# it must be re-run for cases where these differ by user conditionals,
# for example, where in UTF-8 Greek characters are used and in Latin-1
# a transliteration is provided by the post-processor

class Ppt(Book):
  eb = [] # emit buffer for generated text
  wb = [] # working buffer

  long_table_line_count = 0

  def __init__(self, args, renc):
    Book.__init__(self, args, renc)
    self.renc = renc # requested encoding: "l" Latin-1, "u" UTF-8
    if self.renc == "u":
      self.outfile = re.sub("-src", "", self.srcfile.split('.')[0]) + "-utf8.txt"
    if self.renc == "l":
      self.outfile = re.sub("-src", "", self.srcfile.split('.')[0]) + "-lat1.txt"

  # -------------------------------------------------------------------------------------
  # utility methods

  # print if debug includes 'd'
  def dprint(self, msg):
    if 'd' in self.debug:
      print("{}: {}".format(self.__class__.__name__, msg))

  # bailout after saving working buffer in bailout.txt
  def bailout(self, buffer):
    f1 = open("bailout.txt", "w", encoding='utf-8')
    for index,t in enumerate(buffer):
      f1.write( "{:s}\r\n".format(t.rstrip()) )
    f1.close()
    exit(1)

  def meanstdv(self, x):
    """ Calculate mean and standard deviation of data x[] """  
    n, mean, std = len(x), 0, 0
    if n == 0:
      return (0, 0, 0)
    if n == 1:
      return (1, len(x[0]), 0)
    for a in x:
  	  mean = mean + len(a)
    mean = mean / float(n)
    for a in x:
  	  std = std + (len(a) - mean)**2
    std = sqrt(std / float(n-1))
    return n, mean, std
  
  def line_len_diff(self, x):
    """ calculate max diff between longest and shortest line of data x[] """
    longest_line_len = 0
    shortest_line_len = 1000
    for line in x:
      longest_line_len = max(longest_line_len, len(line))
      shortest_line_len = min(shortest_line_len, len(line))
    return longest_line_len - shortest_line_len
    
  def shortest_line_len(self, x):
    """ return length of shotest line in x[] """
    shortest_line_len = 1000
    for line in x:
      shortest_line_len = min(shortest_line_len, len(line))
    return shortest_line_len    

  # wrap string into paragraph in t[]
  def wrap_para(self, s,  indent, ll, ti):
    s = s.replace("—", "◠◠") # compensate long dash
    
    # if ti < 0, strip off characters that will be in the hanging margin
    hold = ""
    if ti < 0:
      howmany = -1 * ti
      hold = s[0:howmany]
      s = s[howmany:]

    # if ti > 0, add leading nbsp
    if ti > 0:
      s = "⑧" * ti + s

    # at this point, s is ready to wrap
    mywidth = ll - indent
    t =[]
    while len(s) > mywidth:
      try:
        snip_at = s.rindex(" ", 0, mywidth)
      except:
        # could not find a place to wrap
        snip_at = s.index(" ", mywidth) # Plan B
        self.warn("wide line: {}".format(s))
      t.append(s[:snip_at])
      s = s[snip_at+1:] 
    t.append(s)   
    
    for i, line in enumerate(t):
        t[i] = t[i].replace("◠◠", "—") # restore dash
        t[i] = t[i].replace("⑧", " ")  # leading spaces from .ti
        t[i] = " " * indent + t[i] # indent applies to all
    if hold != "":
      leadstr = " " * (indent + ti) + hold
      t[0] = leadstr + t[0][indent:]
    return t
    
  def wrap(self, s,  indent=0, ll=72, ti=0):
    ta = [] # list of paragraph (lists)
    ts = [] # paragraph stats
    for i in range(0, -8, -2):
      t = self.wrap_para(s, indent, ll+i, ti)
      ta.append(t)
      sll = self.shortest_line_len(t[0:-1])
      if sll >= 55:
        return t # just bail if already good enough
      ts.append(sll)
    
    # if we are here all test paragraphs had some short lines
    # choose the best one we found
    longest_short = 0
    besti = -1
    for i in range(0,len(ta)):
      if ts[i] > longest_short:
        t = ta[i]
        longest_short = ts[i]
        besti = i
        
    # z = self.meanstdv(t[0:-1]) 
    # lld = self.line_len_diff(t[0:-1])
    # zs = "b:{0:d}  t:{1:d}  std dev:{2:.1f}  max diff:{3:d}".format(besti, z[0],z[2],bestdiff)
    # t.append(zs)     
          
    return t

  # -------------------------------------------------------------------------------------
  # preprocess working buffer (text versions)
  def preprocess(self):

    self.preProcessCommon()

    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    # <lang> tags ignored in text version.
    for i in range(len(self.wb)):
      self.wb[i] = re.sub(r"<lang[^>]*>","",self.wb[i])
      self.wb[i] = re.sub(r"<\/lang>","",self.wb[i])

    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    # look for <b>
    # after text generation look for <b> + "="
    self.found_bold = False
    for i in range(len(self.wb)):
      if "<b>" in self.wb[i]:
        self.found_bold = True

    # Text will choose the UTF-8 Greek line or transliteration
    # depending on self.renc requested encoding
    i = 0
    while i < len(self.wb):
      if self.wb[i].startswith('.gu'):
        if self.renc == "u":
          self.wb[i] = re.sub("^\.gu ", "", self.wb[i])
          i += 1
        else:
          del(self.wb[i])
        continue
      if self.wb[i].startswith('.gl'):
        if self.renc == "l":
          self.wb[i] = re.sub("^\.gl ", "", self.wb[i])
          i += 1
        else:
          del(self.wb[i])
        continue
      i += 1

    # remove internal page links
    # two forms: #17# and #The Encounter:ch01#
    text = "\n".join(self.wb)
    text = re.sub(r"#(\d+)#", r"\1", text)
    text = re.sub(r"#(.*?):.*?#", r"\1", text)
    # if there is a named target, then somewhere there
    # is a <target id...> to remove in the text version
    text = re.sub(r"<target.*?>", "", text)
    self.wb = text.splitlines()

    # all page numbers deleted in text version
    i = 0
    while i < len(self.wb): # switch order if pn followed by blank line
      if re.match(r"\.pn", self.wb[i]):
        del self.wb[i]
        i -= 1
      i += 1

    # autonumbered footnotes are assigned numbers
    # footnotes in text
    fncr = 1
    for i in range(len(self.wb)):
      m = re.search("\[#\]", self.wb[i])
      while m:
        self.wb[i] = re.sub("\[#\]", "[{}]".format(fncr), self.wb[i], 1)
        fncr += 1
        m = re.search("\[#\]", self.wb[i])
    # must do separately
    fncr = 1
    i = 0
    while i < len(self.wb):
      if ".fn #" == self.wb[i]:
        self.wb[i:i+1] = [".sp 1",".fn {}".format(fncr)]
        fncr += 1
      i += 1

    # -------------------------------------------------------------------------------------
    # inline markup processing (text)
    # sc small caps ; l large ; xl x-large ; s small ; xs s-small ; u underline
    # g gesperrt ; converted to text form: em, b, i
    
    for i, line in enumerate(self.wb):
    
      # standalone font-size changes dropped
      self.wb[i] = re.sub(r"<\/?l>", "", self.wb[i]) # large
      self.wb[i] = re.sub(r"<\/?xl>", "", self.wb[i]) # x-large
      self.wb[i] = re.sub(r"<\/?xxl>", "", self.wb[i]) # xx-large
      self.wb[i] = re.sub(r"<\/?s>", "", self.wb[i]) # small
      self.wb[i] = re.sub(r"<\/?xs>", "", self.wb[i]) # x-small  
      self.wb[i] = re.sub(r"<\/?xxs>", "", self.wb[i]) # xx-small  
 
      # underline dropped
      self.wb[i] = re.sub(r"<\/?u>", "", self.wb[i]) # underline

      # italics and emphasis
      self.wb[i] = re.sub(r"<\/?i>", "_", self.wb[i])
      self.wb[i] = re.sub(r"<\/?I>", "", self.wb[i]) # alternate italics dropped
      self.wb[i] = re.sub(r"<\/?em>", "_", self.wb[i])
      self.wb[i] = re.sub(r"<\/?b>", "◮", self.wb[i]) # will become "="
      self.wb[i] = re.sub(r"<\/?B>", "", self.wb[i]) # alternate bold dropped

      # strong maps to "=" always
      self.wb[i] = re.sub(r"<\/?strong>", "◮", self.wb[i])

      # cite maps to "_" always
      self.wb[i] = re.sub(r"<\/?cite>", "_", self.wb[i])

      # alternate handling
      # small caps ignored
      self.wb[i] = re.sub(r"<\/?SC>", "", self.wb[i])
          
      # lang dropped (<i> would be separate)
      self.wb[i] = re.sub(r"<\/?lang>", "", self.wb[i])
        
      # gesperrt in text
      self.wb[i] = re.sub(r"<\/?g>", "_", self.wb[i])
      
      # font-size requests dropped
      self.wb[i] = re.sub(r"<\/?fs[^>]*>", "", self.wb[i])
      
      # color dropped
      self.wb[i] = re.sub(r"<c=[^>]+>", "", self.wb[i])
      self.wb[i] = re.sub(r"<\/c>", "", self.wb[i])
    
    # do small caps last since it could uppercase a tag. 
    for i, line in enumerate(self.wb):
      def to_uppercase(m):
        return m.group(1).upper()
        
      while "<sc>" in self.wb[i]:
        if not "</sc>" in self.wb[i]: # multi-line
          t = []
          while "</sc>" not in self.wb[i]:
            t.append(self.wb[i])
            del(self.wb[i])
          t.append(self.wb[i]) # last line
          ts = "\n".join(t) # make all one line
          re_sc = re.compile(r"<sc>(.+?)<\/sc>", re.DOTALL)  
          ts = re.sub(re_sc, to_uppercase, ts)
          t = ts.splitlines() # back to a series of lines
          self.wb[i:i+1] = t
        else: # single line
          re_sc = re.compile(r"<sc>(.*?)<\/sc>")  
          self.wb[i] = re.sub(re_sc, to_uppercase, self.wb[i])      

  # -------------------------------------------------------------------------------------
  # post-process emit buffer (TEXT)

  def postprocess(self):

    # combine space requests
    i = 0
    while i < len(self.eb) - 1:
      m1 = re.match(r"\.RS (\d+)", self.eb[i])
      m2 = re.match(r"\.RS (\d+)", self.eb[i+1])
      if m1 and m2:
        spcrq1 = int(m1.group(1))
        spcrq2 = int(m2.group(1))
        spcrq = max(spcrq1, spcrq2)
        self.eb[i] = ".RS {}".format(spcrq)
        del self.eb[i+1] # combine
        continue
      i += 1

    # convert remaining .RS requests into real spaces
    i = 0
    while i < len(self.eb):
      m = re.match(r"\.RS (\d+)", self.eb[i])
      if m:
        del self.eb[i] # the .RS line
        count = int(m.group(1))
        while count > 0:
          self.eb.insert(i,"")
          count -= 1
      i += 1

    for i, line in enumerate(self.eb):
      self.eb[i] = self.eb[i].replace("ⓓ", ".")
      self.eb[i] = self.eb[i].replace("①", "{")
      self.eb[i] = self.eb[i].replace("②", "}")
      self.eb[i] = self.eb[i].replace("③", "[")
      self.eb[i] = self.eb[i].replace("④", "]")
      self.eb[i] = self.eb[i].replace("⑤", "<")
      self.eb[i] = self.eb[i].replace("⑥", ":")
      self.eb[i] = self.eb[i].replace("⑨", "-")     
      # text space replacement
      self.eb[i] = self.eb[i].replace("ⓢ", " ") # non-breaking space
      self.eb[i] = self.eb[i].replace("Ⓢ", " ") # non-breaking space in a small cap gets upcased.
      self.eb[i] = self.eb[i].replace("ⓣ", "") # zero space
      self.eb[i] = self.eb[i].replace("ⓤ", " ") # thin space
      self.eb[i] = self.eb[i].replace("ⓥ", " ") # thick space
      # ampersand
      self.eb[i] = self.eb[i].replace("Ⓩ", "&")
      # superscripts
      m = re.search(r"◸(.*?)◹", self.eb[i])
      while m:
        supstr = m.group(1)
        if len(supstr) == 1:
          self.eb[i] = re.sub(r"◸.◹", "^"+supstr, self.eb[i],1)
        else:
          self.eb[i] = re.sub(r"◸.*?◹", "^{" + supstr + "}", self.eb[i],1)
        m = re.search(r"◸(.*?)◹", self.eb[i])
      # subscripts
      self.eb[i] = self.eb[i].replace("◺", "_{")
      self.eb[i] = self.eb[i].replace("◿", "}")

      if self.renc == 'u':
        if "[oe]" in self.eb[i]:
          self.warn("unconverted [oe] ligature written to UTF-8 file.")
        if "[ae]" in self.eb[i]:
          self.warn("unconverted [ae] ligature written to UTF-8 file.")

    # checks for <b> and "="
    # if self.found_bold:
    #   self.warn("<b> used in text. TN suggested.")
    equal_sign_seen = False
    for i, line in enumerate(self.eb):
      if "=" in line:
        equal_sign_seen = True
    if equal_sign_seen and self.found_bold:
      self.warn("both <b> and \"=\" found in text. markup conflict.")
    # put the "=" in for bold.
    for i, line in enumerate(self.eb):
      self.eb[i] = self.eb[i].replace("◮", "=")

  # -------------------------------------------------------------------------------------
  # save emit buffer in UTF-8 encoding to specified dstfile (text output, UTF-8)
  def saveFileU(self, fn):
    longcount = 0
    while not self.eb[-1]:
      self.eb.pop()
    f1 = codecs.open(fn, "w", "utf-8")
    for index,t in enumerate(self.eb):
      s = t.rstrip()
      if len(s) > self.linelimitwarning:
        longcount += 1
        if longcount == 4:
          self.warn("additional long lines not reported")
        if longcount < 4:
          m = re.match(r".{0,60}\s", s)
          self.warn("long line (>{}) beginning:\n  {}....".format(self.linelimitwarning, m.group(0)))          
      f1.write( "{:s}\r\n".format(s) )
    f1.close()

  # -------------------------------------------------------------------------------------
  # convert utf-8 to Latin-1 in self.wb
  def utoLat(self):
    described = {}
    d = {
     '\u00A0':' ', '\u00A1':'¡', '\u00A2':'¢', '\u00A3':'£', '\u00A4':'¤', '\u00A5':'¥', '\u00A6':'¦', '\u00A7':'§',
     '\u00A8':'¨', '\u00A9':'©', '\u00AA':'ª', '\u00AB':'«', '\u00AC':'¬', '\u00AD':'­', '\u00AE':'®', '\u00AF':'¯',
     '\u00B0':'°', '\u00B1':'±', '\u00B2':'²', '\u00B3':'³', '\u00B4':'´', '\u00B5':'µ', '\u00B6':'¶', '\u00B7':'·',
     '\u00B8':'¸', '\u00B9':'¹', '\u00BA':'º', '\u00BB':'»', '\u00BC':'¼', '\u00BD':'½', '\u00BE':'¾', '\u00BF':'¿',
     '\u00C0':'À', '\u00C1':'Á', '\u00C2':'Â', '\u00C3':'Ã', '\u00C4':'Ä', '\u00C5':'Å', '\u00C6':'Æ', '\u00C7':'Ç',
     '\u00C8':'È', '\u00C9':'É', '\u00CA':'Ê', '\u00CB':'Ë', '\u00CC':'Ì', '\u00CD':'Í', '\u00CE':'Î', '\u00CF':'Ï',
     '\u00D0':'Ð', '\u00D1':'Ñ', '\u00D2':'Ò', '\u00D3':'Ó', '\u00D4':'Ô', '\u00D5':'Õ', '\u00D6':'Ö', '\u00D7':'×',
     '\u00D8':'Ø', '\u00D9':'Ù', '\u00DA':'Ú', '\u00DB':'Û', '\u00DC':'Ü', '\u00DD':'Ý', '\u00DE':'Þ', '\u00DF':'ß',
     '\u00E0':'à', '\u00E1':'á', '\u00E2':'â', '\u00E3':'ã', '\u00E4':'ä', '\u00E5':'å', '\u00E6':'æ', '\u00E7':'ç',
     '\u00E8':'è', '\u00E9':'é', '\u00EA':'ê', '\u00EB':'ë', '\u00EC':'ì', '\u00ED':'í', '\u00EE':'î', '\u00EF':'ï',
     '\u00F0':'ð', '\u00F1':'ñ', '\u00F2':'ò', '\u00F3':'ó', '\u00F4':'ô', '\u00F5':'õ', '\u00F6':'ö', '\u00F7':'÷',
     '\u00F8':'ø', '\u00F9':'ù', '\u00FA':'ú', '\u00FB':'û', '\u00FC':'ü', '\u00FD':'ý', '\u00FE':'þ', '\u00FF':'ÿ',
     '\u0100':'A', '\u0101':'a', '\u0102':'A', '\u0103':'a', '\u0104':'A', '\u0105':'a', '\u0106':'C', '\u0107':'c',
     '\u0108':'C', '\u0109':'c', '\u010A':'C', '\u010B':'c', '\u010C':'C', '\u010D':'c', '\u010E':'D', '\u010F':'d',
     '\u0110':'D', '\u0111':'d', '\u0112':'E', '\u0113':'e', '\u0114':'E', '\u0115':'e', '\u0116':'E', '\u0117':'e',
     '\u0118':'E', '\u0119':'e', '\u011A':'E', '\u011B':'e', '\u011C':'G', '\u011D':'g', '\u011E':'G', '\u011F':'g',
     '\u0120':'G', '\u0121':'g', '\u0122':'G', '\u0123':'g', '\u0124':'H', '\u0125':'h', '\u0126':'H', '\u0127':'h',
     '\u0128':'I', '\u0129':'i', '\u012A':'I', '\u012B':'i', '\u012C':'I', '\u012D':'i', '\u012E':'I', '\u012F':'i',
     '\u0130':'I', '\u0132':'IJ','\u0133':'ij','\u0134':'J', '\u0135':'j', '\u0136':'K', '\u0137':'k', '\u0139':'L',
     '\u013A':'l', '\u013B':'L', '\u013C':'l', '\u013D':'L', '\u013E':'l', '\u013F':'L', '\u0140':'l', '\u0141':'L',
     '\u0142':'l', '\u0143':'N', '\u0144':'n', '\u0145':'N', '\u0146':'n', '\u0147':'N', '\u0148':'n', '\u0149':'n',
     '\u014C':'O', '\u014D':'o', '\u014E':'O', '\u014F':'o', '\u0150':'O', '\u0151':'o', '\u0152':'OE','\u0153':'oe',
     '\u0154':'R', '\u0155':'r', '\u0156':'R', '\u0157':'r', '\u0158':'R', '\u0159':'r', '\u015A':'S', '\u015B':'s',
     '\u015C':'S', '\u015D':'s', '\u015E':'S', '\u015F':'s', '\u0160':'S', '\u0161':'s', '\u0162':'T', '\u0163':'t',
     '\u0164':'T', '\u0165':'t', '\u0166':'T', '\u0167':'t', '\u0168':'U', '\u0169':'u', '\u016A':'U', '\u016B':'u',
     '\u016C':'U', '\u016D':'u', '\u016E':'U', '\u016F':'u', '\u0170':'U', '\u0171':'u', '\u0172':'U', '\u0173':'u',
     '\u0174':'W', '\u0175':'w', '\u0176':'Y', '\u0177':'y', '\u0178':'Y', '\u0179':'Z', '\u017A':'z', '\u017B':'Z',
     '\u017C':'z', '\u017D':'Z', '\u017E':'z', '\u0180':'b', '\u0181':'B', '\u0182':'B', '\u0183':'b', '\u0186':'O',
     '\u0187':'C', '\u0188':'c', '\u018A':'D', '\u018B':'D', '\u018C':'d', '\u0191':'F', '\u0192':'f', '\u0193':'G',
     '\u0197':'I', '\u0198':'K', '\u0199':'k', '\u019A':'l', '\u019D':'N', '\u019E':'n', '\u019F':'O', '\u01A0':'O',
     '\u01A1':'o', '\u01A4':'P', '\u01A5':'p', '\u01AB':'t', '\u01AC':'T', '\u01AD':'t', '\u01AE':'T', '\u01AF':'U',
     '\u01B0':'u', '\u01B2':'V', '\u01B3':'Y', '\u01B4':'y', '\u01B5':'Z', '\u01B6':'z', '\u01C5':'D', '\u01C8':'L',
     '\u01CB':'N', '\u01CD':'A', '\u01CE':'a', '\u01CF':'I', '\u01D0':'i', '\u01D1':'O', '\u01D2':'o', '\u01D3':'U',
     '\u01D4':'u', '\u01D5':'U', '\u01D6':'u', '\u01D7':'U', '\u01D8':'u', '\u01D9':'U', '\u01DA':'u', '\u01DB':'U',
     '\u01DC':'u', '\u01DE':'A', '\u01DF':'a', '\u01E0':'A', '\u01E1':'a', '\u01E2':'A', '\u01E3':'a', '\u01E4':'G',
     '\u01E5':'g', '\u01E6':'G', '\u01E7':'g', '\u01E8':'K', '\u01E9':'k', '\u01EA':'O', '\u01EB':'o', '\u01EC':'O',
     '\u01ED':'o', '\u01F0':'j', '\u01F2':'D', '\u01F4':'G', '\u01F5':'g', '\u01F8':'N', '\u01F9':'n', '\u01FA':'A',
     '\u01FB':'a', '\u01FC':'A', '\u01FD':'a', '\u01FE':'O', '\u01FF':'o', '\u0200':'A', '\u0201':'a', '\u0202':'A',
     '\u0203':'a', '\u0204':'E', '\u0205':'e', '\u0206':'E', '\u0207':'e', '\u0208':'I', '\u0209':'i', '\u020A':'I',
     '\u020B':'i', '\u020C':'O', '\u020D':'o', '\u020E':'O', '\u020F':'o', '\u0210':'R', '\u0211':'r', '\u0212':'R',
     '\u0213':'r', '\u0214':'U', '\u0215':'u', '\u0216':'U', '\u0217':'u', '\u0218':'S', '\u0219':'s', '\u021A':'T',
     '\u021B':'t', '\u021E':'H', '\u021F':'h', '\u0220':'N', '\u0221':'d', '\u0224':'Z', '\u0225':'z', '\u0226':'A',
     '\u0227':'a', '\u0228':'E', '\u0229':'e', '\u022A':'O', '\u022B':'o', '\u022C':'O', '\u022D':'o', '\u022E':'O',
     '\u022F':'o', '\u0230':'O', '\u0231':'o', '\u0232':'Y', '\u0233':'y', '\u0234':'l', '\u0235':'n', '\u0236':'t',
     '\u0253':'b', '\u0255':'c', '\u0256':'d', '\u0257':'d', '\u0260':'g', '\u0266':'h', '\u0268':'i', '\u026B':'l',
     '\u026C':'l', '\u026D':'l', '\u0271':'m', '\u0272':'n', '\u0273':'n', '\u027C':'r', '\u027D':'r', '\u027E':'r',
     '\u0282':'s', '\u0288':'t', '\u0289':'u', '\u028B':'v', '\u0290':'z', '\u0291':'z', '\u029C':'H', '\u029D':'j',
     '\u02A0':'q', '\u02AE':'h', '\u02AF':'h', '\u040D':'I', '\u045D':'i', '\u04D0':'A', '\u04D1':'a', '\u04D2':'A',
     '\u04D3':'a', '\u04E2':'I', '\u04E3':'i', '\u04E4':'I', '\u04E5':'i', '\u04E6':'O', '\u04E7':'o', '\u04EC':'E',
     '\u04ED':'e', '\u04EE':'U', '\u04EF':'u', '\u04F0':'U', '\u04F1':'u', '\u04F2':'U', '\u04F3':'u', '\u1E00':'A',
     '\u1E01':'a', '\u1E02':'B', '\u1E03':'b', '\u1E04':'B', '\u1E05':'b', '\u1E06':'B', '\u1E07':'b', '\u1E08':'C',
     '\u1E09':'c', '\u1E0A':'D', '\u1E0B':'d', '\u1E0C':'D', '\u1E0D':'d', '\u1E0E':'D', '\u1E0F':'d', '\u1E10':'D',
     '\u1E11':'d', '\u1E12':'D', '\u1E13':'d', '\u1E14':'E', '\u1E15':'e', '\u1E16':'E', '\u1E17':'e', '\u1E18':'E',
     '\u1E19':'e', '\u1E1A':'E', '\u1E1B':'e', '\u1E1C':'E', '\u1E1D':'e', '\u1E1E':'F', '\u1E1F':'f', '\u1E20':'G',
     '\u1E21':'g', '\u1E22':'H', '\u1E23':'h', '\u1E24':'H', '\u1E25':'h', '\u1E26':'H', '\u1E27':'h', '\u1E28':'H',
     '\u1E29':'h', '\u1E2A':'H', '\u1E2B':'h', '\u1E2C':'I', '\u1E2D':'i', '\u1E2E':'I', '\u1E2F':'i', '\u1E30':'K',
     '\u1E31':'k', '\u1E32':'K', '\u1E33':'k', '\u1E34':'K', '\u1E35':'k', '\u1E36':'L', '\u1E37':'l', '\u1E38':'L',
     '\u1E39':'l', '\u1E3A':'L', '\u1E3B':'l', '\u1E3C':'L', '\u1E3D':'l', '\u1E3E':'M', '\u1E3F':'m', '\u1E40':'M',
     '\u1E41':'m', '\u1E42':'M', '\u1E43':'m', '\u1E44':'N', '\u1E45':'n', '\u1E46':'N', '\u1E47':'n', '\u1E48':'N',
     '\u1E49':'n', '\u1E4A':'N', '\u1E4B':'n', '\u1E4C':'O', '\u1E4D':'o', '\u1E4E':'O', '\u1E4F':'o', '\u1E50':'O',
     '\u1E51':'o', '\u1E52':'O', '\u1E53':'o', '\u1E54':'P', '\u1E55':'p', '\u1E56':'P', '\u1E57':'p', '\u1E58':'R',
     '\u1E59':'r', '\u1E5A':'R', '\u1E5B':'r', '\u1E5C':'R', '\u1E5D':'r', '\u1E5E':'R', '\u1E5F':'r', '\u1E60':'S',
     '\u1E61':'s', '\u1E62':'S', '\u1E63':'s', '\u1E64':'S', '\u1E65':'s', '\u1E66':'S', '\u1E67':'s', '\u1E68':'S',
     '\u1E69':'s', '\u1E6A':'T', '\u1E6B':'t', '\u1E6C':'T', '\u1E6D':'t', '\u1E6E':'T', '\u1E6F':'t', '\u1E70':'T',
     '\u1E71':'t', '\u1E72':'U', '\u1E73':'u', '\u1E74':'U', '\u1E75':'u', '\u1E76':'U', '\u1E77':'u', '\u1E78':'U',
     '\u1E79':'u', '\u1E7A':'U', '\u1E7B':'u', '\u1E7C':'V', '\u1E7D':'v', '\u1E7E':'V', '\u1E7F':'v', '\u1E80':'W',
     '\u1E81':'w', '\u1E82':'W', '\u1E83':'w', '\u1E84':'W', '\u1E85':'w', '\u1E86':'W', '\u1E87':'w', '\u1E88':'W',
     '\u1E89':'w', '\u1E8A':'X', '\u1E8B':'x', '\u1E8C':'X', '\u1E8D':'x', '\u1E8E':'Y', '\u1E8F':'y', '\u1E90':'Z',
     '\u1E91':'z', '\u1E92':'Z', '\u1E93':'z', '\u1E94':'Z', '\u1E95':'z', '\u1E96':'h', '\u1E97':'t', '\u1E98':'w',
     '\u1E99':'y', '\u1E9A':'a', '\u1EA0':'A', '\u1EA1':'a', '\u1EA2':'A', '\u1EA3':'a', '\u1EA4':'A', '\u1EA5':'a',
     '\u1EA6':'A', '\u1EA7':'a', '\u1EA8':'A', '\u1EA9':'a', '\u1EAA':'A', '\u1EAB':'a', '\u1EAC':'A', '\u1EAD':'a',
     '\u1EAE':'A', '\u1EAF':'a', '\u1EB0':'A', '\u1EB1':'a', '\u1EB2':'A', '\u1EB3':'a', '\u1EB4':'A', '\u1EB5':'a',
     '\u1EB6':'A', '\u1EB7':'a', '\u1EB8':'E', '\u1EB9':'e', '\u1EBA':'E', '\u1EBB':'e', '\u1EBC':'E', '\u1EBD':'e',
     '\u1EBE':'E', '\u1EBF':'e', '\u1EC0':'E', '\u1EC1':'e', '\u1EC2':'E', '\u1EC3':'e', '\u1EC4':'E', '\u1EC5':'e',
     '\u1EC6':'E', '\u1EC7':'e', '\u1EC8':'I', '\u1EC9':'i', '\u1ECA':'I', '\u1ECB':'i', '\u1ECC':'O', '\u1ECD':'o',
     '\u1ECE':'O', '\u1ECF':'o', '\u1ED0':'O', '\u1ED1':'o', '\u1ED2':'O', '\u1ED3':'o', '\u1ED4':'O', '\u1ED5':'o',
     '\u1ED6':'O', '\u1ED7':'o', '\u1ED8':'O', '\u1ED9':'o', '\u1EDA':'O', '\u1EDB':'o', '\u1EDC':'O', '\u1EDD':'o',
     '\u1EDE':'O', '\u1EDF':'o', '\u1EE0':'O', '\u1EE1':'o', '\u1EE2':'O', '\u1EE3':'o', '\u1EE4':'U', '\u1EE5':'u',
     '\u1EE6':'U', '\u1EE7':'u', '\u1EE8':'U', '\u1EE9':'u', '\u1EEA':'U', '\u1EEB':'u', '\u1EEC':'U', '\u1EED':'u',
     '\u1EEE':'U', '\u1EEF':'u', '\u1EF0':'U', '\u1EF1':'u', '\u1EF2':'Y', '\u1EF3':'y', '\u1EF4':'Y', '\u1EF5':'y',
     '\u1EF6':'Y', '\u1EF7':'y', '\u1EF8':'Y', '\u1EF9':'y', '\u2002':' ', '\u2003':' ', '\u2004':' ', '\u2005':' ',
     '\u2006':' ', '\u2007':' ', '\u2008':' ', '\u2009':' ', '\u200A':' ', '\u2010':'-', '\u2013':'-', '\u2014':'--',
     '\u2016':'|', '\u2017':'_', '\u2018':"'", '\u2019':"'", '\u201A':"'", '\u201B':"'", '\u201C':'"', '\u201D':'"',
     '\u201E':'"', '\u201F':'"', '\u2045':'[', '\u2046':']', '\u2047':'?', '\u2048':'?', '\u2049':'!', '\uFF01':'!',
     '\uFF02':'"', '\uFF03':'#', '\uFF04':'$', '\uFF05':'%', '\uFF06':'&', '\uFF07':';', '\uFF08':'(', '\uFF09':')',
     '\uFF0A':'*', '\uFF0B':'+', '\uFF0C':',', '\uFF0D':'-', '\uFF0E':'.', '\uFF0F':'/', '\uFF10':'0', '\uFF11':'1',
     '\uFF12':'2', '\uFF13':'3', '\uFF14':'4', '\uFF15':'5', '\uFF16':'6', '\uFF17':'7', '\uFF18':'8', '\uFF19':'9',
     '\uFF1A':':', '\uFF1B':';', '\uFF1D':'=', '\uFF1E':'>', '\uFF1F':'?', '\uFF20':'@', '\uFF21':'A', '\uFF22':'B',
     '\uFF23':'C', '\uFF24':'D', '\uFF25':'E', '\uFF26':'F', '\uFF27':'G', '\uFF28':'H', '\uFF29':'I', '\uFF2A':'J',
     '\uFF2B':'K', '\uFF2C':'L', '\uFF2D':'M', '\uFF2E':'N', '\uFF2F':'O', '\uFF30':'P', '\uFF31':'Q', '\uFF32':'R',
     '\uFF33':'S', '\uFF34':'T', '\uFF35':'U', '\uFF36':'V', '\uFF37':'W', '\uFF38':'X', '\uFF39':'Y', '\uFF3A':'Z',
     '\uFF3B':'[', '\uFF3C':'\\','\uFF3D':']', '\uFF3E':'^', '\uFF3F':'_', '\uFF41':'a', '\uFF42':'b', '\uFF43':'c',
     '\uFF44':'d', '\uFF45':'e', '\uFF46':'f', '\uFF47':'g', '\uFF48':'h', '\uFF49':'i', '\uFF4A':'j', '\uFF4B':'k',
     '\uFF4C':'l', '\uFF4D':'m', '\uFF4E':'n', '\uFF4F':'o', '\uFF50':'p', '\uFF51':'q', '\uFF52':'r', '\uFF53':'s',
     '\uFF54':'t', '\uFF55':'u', '\uFF56':'v', '\uFF57':'w', '\uFF58':'x', '\uFF59':'y', '\uFF5A':'z', '\uFF5B':'{',
     '\uFF5C':'|', '\uFF5D':'}', '\uFF5E':'~',
     '\u2042':'***'
    }

    t = defaultdict(int)
    for i, line in enumerate(self.wb):
      s = ""
      for c in line: # for every character
        if c in d: # is it in the list of converting characters?
          s += d[c] # yes, replace with converted Latin-1 character
          t[c] += 1
        else:
          if ord(c) < 0x100:
            s += c # no conversion, transfer character as is
          else:
            s += "[{}]".format(unicodedata.name(c))
            described[c] = 1
      self.wb[i] = s

    # show what was converted
    self.lprint("\nUTF-8 characters converted:")
    self.lprint("  {:5}{:5} {}".format("char","count","description"))
    self.lprint("  {:5}{:5} {}".format("----","-----","----------------------------------------"))
    for ch in t:
      self.lprint("  {:5}{:5} {}".format(d[ch], t[ch], unicodedata.name(ch)))

    while not self.wb[-1]:
      self.eb.pop()

    if len(described) > 0:
      self.lprint("\nUTF8 characters described:")
      self.lprint("  {:11} {}".format("codepoint","description"))
      self.lprint("  {:11} {}".format("-----------","----------------------------------------"))
      for k, v in sorted(described.items()):
        namek = unicodedata.name(k)
        self.lprint('  {:11} {}'.format(k, namek))
      self.lprint("")

  # -------------------------------------------------------------------------------------
  # save emit buffer in Latin-1 encoding to specified latfile
  def saveLat1(self, fn):
    # write Latin-1 file (text output, Latin-1)
    # note: using codecs.open allows specific line terminators.
    # using .open would write platform-specific line terminators.
    f1 = codecs.open(fn, "w", "ISO-8859-1")
    longcount = 0
    for index,t in enumerate(self.eb):
      s = t.rstrip()
      if len(s) > self.linelimitwarning:
        longcount += 1
        if longcount == 4:
          self.warn("additional long lines not reported")
        if longcount < 4:
          m = re.match(r".{0,60}\s", s)
          self.warn("long line (>{}) beginning:\n  {}....".format(self.linelimitwarning, m.group(0)))
      f1.write( "{:s}\r\n".format(s) )
    f1.close()

  # ----- process method group ----------------------------------------------------------

  # .li literal block (pass-through)
  def doLit(self):
    self.cl += 1 # skip the .li
    while self.wb[self.cl] != ".li-":
      self.eb.append(self.wb[self.cl])
      self.cl += 1
    self.cl += 1 # skip the .li-

  # .pb page break
  def doPb(self):
    t = []
    self.eb.append(".RS 1")
    self.eb.append("-" * 72)
    self.eb.append(".RS 1")
    self.cl += 1

  # .hr horizontal rule
  def doHr(self):
    hrpct = 100
    m = re.match(r"\.hr (\d+)%", self.wb[self.cl])
    if m:
      hrpct = int(m.group(1))
    hrcnt = int(72 * hrpct / 100)
    self.eb.append("{:^72}".format('-'*hrcnt))
    self.cl += 1

  # .tb thought break
  def doTbreak(self):
    self.eb.append((" "*18 + "*       "*5).rstrip())
    self.cl += 1

  # h1
  def doH1(self):
    m = re.match(r"\.h1 (.*)", self.wb[self.cl])
    if m: # modifier
      rend = m.group(1)
      if "nobreak" in rend:
        rend = re.sub("nobreak","",rend)
    self.eb.append(".RS 1")
    h2a = self.wb[self.cl+1].split('|')
    for line in h2a:
      self.eb.append(("{:^72}".format(line)).rstrip())
    self.eb.append(".RS 1")
    self.cl += 2

  # h2
  def doH2(self):
    m = re.match(r"\.h2 (.*)", self.wb[self.cl])
    if m: # modifier
      rend = m.group(1)
      if "nobreak" in rend:
        rend = re.sub("nobreak","",rend)
    self.eb.append(".RS 1")
    h2a = self.wb[self.cl+1].split('|')
    for line in h2a:
      self.eb.append(("{:^72}".format(line)).rstrip())
    self.eb.append(".RS 1")
    self.cl += 2

  # h3
  def doH3(self):
    m = re.match(r"\.h3 (.*)", self.wb[self.cl])
    if m: # modifier
      rend = m.group(1)
      if "nobreak" in rend:
        rend = re.sub("nobreak","",rend)
    self.eb.append(".RS 1")
    h2a = self.wb[self.cl+1].split('|')
    for line in h2a:
      self.eb.append(("{:^72}".format(line)).rstrip())
    self.eb.append(".RS 1")
    self.cl += 2

  # .sp n
  def doSpace(self):
    m = re.match(r"\.sp (\d+)", self.wb[self.cl])
    if m:
      howmany = int(m.group(1))
      self.eb.append(".RS {}".format(howmany))
    else:
      self.fatal("malformed space directive: {}".format(self.wb[self.cl]))
    self.cl += 1

  # .fs
  # change font size for following paragraphs
  # no effect in text
  def doFontSize(self):
    del self.wb[self.cl]

  # .il illustrations (text)
  def doIllo(self):
    m = re.match(r"\.il (.*)", self.wb[self.cl])
    if m:
      # ignore the illustration line
      # is the .il line followed by a caption line?
      self.cl += 1 # the illo line
      caption = ""
      if self.cl < len(self.wb) and self.wb[self.cl].startswith(".ca"):
        # there is a caption. it may be on multiple lines
        if ".ca" == self.wb[self.cl]:
          # multiple line caption
          self.cl += 1 # the starting .ca
          s = "[Illustration: {}".format(self.wb[self.cl])
          t = self.wrap(s, 0, self.regLL, 0)
          self.eb += t
          self.cl += 1
          while not (self.wb[self.cl]).startswith(".ca"):
            self.eb.append(self.wb[self.cl])
            self.cl += 1
          self.eb[-1] += "]"
          self.cl += 1 # the closing .ca-
        else:
          # single line
          caption = self.wb[self.cl][4:]
          s = "[Illustration: {}]".format(caption)
          t = self.wrap(s, 0, self.regLL, 0)
          self.eb += t
          self.cl += 1 # caption line

      else:
        # no caption, just illustration
        t = ["[Illustration]"]
        self.eb += t

  # .in left margin indent
  def doIn(self):
    handled = False
    m = re.match(r"\.in \+(.+)", self.wb[self.cl])
    if m:
      self.instack.append(self.regIN)
      self.regIN += int(m.group(1)) # relative
      handled = True

    m = re.match(r"\.in \-(.+)", self.wb[self.cl])
    if not handled and m:
      self.instack.append(self.regIN)
      self.regIN -= int(m.group(1)) # relative
      if self.regIN < 0:
        self.crash_w_context("left margin out of bounds", self.cl)
      handled = True
      
    m = re.match(r"\.in (\d+)", self.wb[self.cl])
    if not handled and m:
      self.instack.append(self.regIN)
      self.regIN = int(m.group(1)) # absolute
      handled = True
      
    if not handled and ".in" == self.wb[self.cl]:
      try:
        self.regIN = self.instack.pop()
      except:
        self.crash_w_context("indent error: no indent to undo", self.cl, 2)
      handled = True

    if handled:
      self.cl += 1
    else:
      self.fatal("malformed .in command: \"{}\"".format(self.wb[self.cl]))

  # .ll line length
  def doLl(self):
    m = re.match(r"\.ll \+(.+)", self.wb[self.cl])
    if m:
      self.llstack.append(self.regLL) # save current line length
      self.regLL += int(m.group(1)) # relative
      if self.regLL <= 0:
        self.crash_w_context("attempt to set line length less than zero", self.cl)
      self.cl += 1
      return

    m = re.match(r"\.ll \-(.+)", self.wb[self.cl])
    if m:
      self.llstack.append(self.regLL) # save current line length
      self.regLL -= int(m.group(1)) # relative
      if self.regLL <= 0:
        self.crash_w_context("attempt to set line length less than zero", self.cl)
      self.cl += 1
      return

    m = re.match(r"\.ll (\d+)", self.wb[self.cl])
    if m:
      self.llstack.append(self.regLL) # save current line length
      self.regLL = int(m.group(1)) # absolute
      if self.regLL <= 0:
        self.crash_w_context("attempt to set line length less than zero", self.cl)
      self.cl += 1
      return

    if ".ll" == self.wb[self.cl]:
      try:
        self.regLL = self.llstack.pop()
      except:
        self.crash_w_context("line length error: no line length to undo", self.cl, 2)
      self.cl += 1
      return

    # if here, has not been handled
    self.fatal("malformed .ll command: \"{}\"".format(self.wb[self.cl]))    

  # .ti temporary indent
  def doTi(self):
    m = re.match(r"\.ti (.+)", self.wb[self.cl])
    if m:
      self.regTI += int(m.group(1))
    self.cl += 1

  # .nr named register (note HTML has its own doNr method)
  def doNr(self):
    m = re.match(r"\.nr (.+) (.+)", self.wb[self.cl])
    if m:
      registerName = m.group(1)
      registerValue = m.group(2)
      if registerName == "psi": # paragraph spacing, indented text
        self.nregs["psi"] = m.group(2)
      elif registerName == "psb": # paragraph spacing, block text
        self.nregs["psb"] = m.group(2)
      elif registerName == "pnc": # page number color
        self.nregs["pnc"] = m.group(2)
      else:
        self.warn("undefined register: {}".format(registerName))
    self.cl += 1

  # no-fill, centered (test)
  def doNfc(self, mo):
    t = []
    i = self.cl + 1 # skip the .nf c line
    while self.wb[i] != ".nf-":      
      xt = self.regLL - self.regIN # width of centered line
      xs = "{:^" + str(xt) + "}"
      t.append(" " * self.regIN + xs.format(self.wb[i].strip()))
      i += 1
    self.cl = i + 1 # skip the closing .nf-
    # see if the block has hit the left margin
    need_pad = False
    for line in t:
      if line[0] != " ":
        need_pad = True
    if need_pad:
      self.warn("inserting leading space in wide .nf c")
      for i,line in enumerate(t):
        t[i] = " "+ t[i]
    t.insert(0, ".RS 1")
    t.append(".RS 1")
    self.eb.extend(t)    

  # calculate block width
  def calculateBW(self, lookfor):
    i = self.cl + 1
    startloc = i
    maxw = 0
    while i < len(self.wb) and not re.match(lookfor, self.wb[i]):
      maxw = max(maxw, len(self.wb[i]))
      i += 1
    if i == len(self.wb):
      # unterminated block
      self.crash_w_context("unterminated block. started with:", self.cl)
    return maxw

  # no-fill, left (text)
  # honors leading spaces; allows .ce and .rj
  def doNfl(self, mo):
    
    regINforced = False
    # if self.regIN is 0, force a leading space just for the block and issue a warning
    if self.regIN == 0:
      self.warn("no-fill, left block at left margin starting:\n  {}".format(self.wb[self.cl+1]))
  
    self.eb.append(".RS 1")
    regBW = self.calculateBW(".nf-")
    i = self.cl + 1 # skip the .nf l line
    while self.wb[i] != ".nf-":

      # special cases: .ce and .rj
      m = re.search(r"\.ce (\d+)", self.wb[i])
      if m:
        count = int(m.group(1))
        i += 1 # skip the .ce
        while count > 0:
          xs = "{:^" + str(regBW) + "}"
          self.eb.append(" " * self.regIN + xs.format(self.wb[i].strip()))
          i += 1
          count -= 1
        continue

      m = re.search(r"\.rj (\d+)", self.wb[i])
      if m:
        count = int(m.group(1))
        i += 1 # skip the .rj
        while count > 0:
          xs = "{:>" + str(regBW) + "}"
          self.eb.append(" " * self.regIN + xs.format(self.wb[i].strip()))
          i += 1
          count -= 1
        continue

      s = (" " * self.regIN + self.wb[i])
      # if the line is shorter than 72 characters, just send it to emit buffer
      # if longer, calculate the leading spaces on line and use as shift amount.
      # a .ti lets it wrap
      if len(s) > 72:
        wi = 0
        m = re.match("^(\s+)(.*)", s)
        if m:
          wi = len(m.group(1))
          s = m.group(2)
        u = self.wrap(s, wi+3, self.regLL, -3)
        for line in u:
          self.eb.append(line)
      else:
        self.eb.append(s)
      i += 1
    self.eb.append(".RS 1")
    self.cl = i + 1 # skip the closing .nf-

  # no-fill, block (text)
  def doNfb(self, mo):
    t = []
    regBW = self.calculateBW(".nf-")
    i = self.cl + 1 # skip the .nf b line
    xt = self.regLL - self.regIN
    lmar = (xt - regBW)//2
    while self.wb[i] != ".nf-":      

      # special cases: .ce and .rj
      m = re.search(r"\.ce (\d+)", self.wb[i])
      if m:
        count = int(m.group(1))
        i += 1 # skip the .ce
        while count > 0:
          xs = "{:^" + str(regBW) + "}"
          t.append(" " * lmar + xs.format(self.wb[i].strip()))
          i += 1
          count -= 1
        continue

      m = re.search(r"\.rj (\d+)", self.wb[i])
      if m:
        count = int(m.group(1))
        i += 1 # skip the .rj
        while count > 0:
          xs = "{:>" + str(regBW) + "}"
          t.append(" " * lmar + xs.format(self.wb[i].strip()))
          i += 1
          count -= 1
        continue

      t.append(" " * self.regIN + " " * lmar + self.wb[i].rstrip())
      i += 1
    self.cl = i + 1 # skip the closing .nf-
    
    # see if the block has hit the left margin
    need_pad = False
    for line in t:
      if line[0] != " ":
        need_pad = True
    if need_pad:
      self.warn("inserting leading space in wide .nf b")
      for i,line in enumerate(t):
        t[i] = " "+ t[i]
    t.insert(0, ".RS 1")
    t.append(".RS 1")
    self.eb.extend(t)

  # no-fill, right (text)
  def doNfr(self, mo):
    self.eb.append(".RS 1")
    regBW = self.calculateBW(".nf-")
    fixed_indent = self.regIN + (self.regLL - regBW)
    i = self.cl + 1 # skip the .nf r line
    while self.wb[i] != ".nf-":      

      # special cases: .ce and .rj
      m = re.search(r"\.ce (\d+)", self.wb[i])
      if m:
        count = int(m.group(1))
        i += 1 # skip the .ce
        while count > 0:
          xs = "{:^" + str(regBW) + "}"
          self.eb.append(" " * fixed_indent + xs.format(self.wb[i].strip()))
          i += 1
          count -= 1
        continue

      m = re.search(r"\.rj (\d+)", self.wb[i])
      if m:
        count = int(m.group(1))
        i += 1 # skip the .rj
        while count > 0:
          xs = "{:>" + str(regBW) + "}"
          self.eb.append(" " * fixed_indent + xs.format(self.wb[i].strip()))
          i += 1
          count -= 1
        continue

      self.eb.append(" " * fixed_indent + self.wb[i].strip())
      i += 1
    self.cl = i + 1 # skip the closing .nf-
    self.eb.append(".RS 1")

  # .nf no-fill blocks, all types (text)
  # called first, then dispatched
  def doNf(self): 
    # not expecting a request to close. get here on open
    # m = re.match(r"\.nf .-", self.wb[self.cl])
    m = re.match(r"\.nf-", self.wb[self.cl])
    if m:
      self.crash_w_context("attempting to close an unopened block with {}".format(self.wb[self.cl]),self.cl)
    m = re.match(r"\.nf (.)", self.wb[self.cl])
    if m:
      margin_override = False
      if re.match(r"\.nf . 0", self.wb[self.cl]):
        margin_override = True # ignored in text
      nftype = m.group(1) # c, l, b or r
      if nftype == 'c':
        self.doNfc(margin_override)
      if nftype == 'l':
        self.doNfl(margin_override)
      if nftype == 'r':
        self.doNfr(margin_override)
      if nftype == 'b':
        self.doNfb(margin_override)

  # footnotes
  # here on footnote start or end
  # note in text do not check for duplicate footnotes. they occur in the wild
  def doFnote(self):

    m = re.match(r"\.fn-", self.wb[self.cl])
    if m: # footnote ends
      self.wb[self.cl] = ".in -2"
      return

    m = re.match(r"\.fn (\d+)", self.wb[self.cl]) # expect numeric
    if m: # footnote start
      fnname = m.group(1)
      self.eb.append("Footnote {}: ".format(fnname))
      self.wb[self.cl] = ".in +2"
      return
    else: # non-numeric footnote
     self.fatal("non-numeric footnote: {}".format(self.wb[self.cl]))

  # footnote mark
  def doFmark(self):
    self.eb.append(".RS 1")
    self.eb.append("-----")
    self.eb.append(".RS 1")
    self.cl += 1
    
  # Table code, text
  def doTable(self):
    
    # get maximum width of specified cell by scanning all rows in table
    # must account for markup
    def getMaxWidth(c,ncols):
      j = self.cl + 1
      maxw = 0
      while self.wb[j] != ".ta-":
        # blank and centerd lines are not considered
        if self.wb[j] == "" or not "|" in self.wb[j]:
          j += 1
          continue        
        u = self.wb[j].split("|")
        if len(u) != ncols:
            self.fatal("table has wrong number of columns:\n{}".format(self.wb[j]))
        t = u[c].strip()
        maxw = max(maxw, len(t)) # ignore lead/trail whitespace
        j += 1
      return maxw
    
    haligns = list() # 'l', 'r', or 'c'  no default; must specify
    valigns = list() # 't', 'b', or 'm' default 't'
    widths = list() # column widths
    totalwidth = 0
    
    # look for continuation characters; restore to one line
    k1 = self.cl
    s = self.wb[k1]
    while k1 < len(self.wb) and self.wb[k1] != ".ta-":        
      while "\\" in self.wb[k1]:
        self.wb[k1] = re.sub(r"\\", "", self.wb[k1])
        self.wb[k1] = self.wb[k1] + " " + self.wb[k1+1]
        del self.wb[k1+1]
      k1 += 1
    if k1 == len(self.wb):
      self.fatal("missing .ta- in table starting: {}".format(s))

    # remove table summary if present.
    if "s=" in self.wb[self.cl]:
      self.wb[self.cl] = self.get_id("s", self.wb[self.cl], 1)
    # remove table options if present.
    if "o=" in self.wb[self.cl]:
      self.wb[self.cl] = self.get_id("o", self.wb[self.cl], 1)
          
    # table forms:
    # .ta r:5 l:20 l:5  => use specified width and wrap if necessary
    # .ta rll  => calculate width of columns, no wrap
    # .ta r:5 l:20 lb:5  => use specified width and wrap if necessary,
    #    floating third column to bottom
    
    # if auto-width, replace the .ta line with widths specified
    # if any widths are specified, all must be specified
    # .ta lr => .ta l:6 r:22
    autosize = False
    if not ":" in self.wb[self.cl]:
      autosize = True
      m = re.match(r"\.ta ([lcr]+)", self.wb[self.cl])
      if m:
        t0 = m.group(1) # all the specifiers
        t = list(t0) # ex: ['r','c','l']
        ncols = len(t) # ex: 3
        s = ".ta "
        for i,x in enumerate(t):
          cwidth = getMaxWidth(i,ncols) # width
          s += "{}t:{} ".format(t0[i],cwidth)
        self.wb[self.cl] = s.strip()  # replace with widths specified
    
    # if vertical alignment not specified, default to "top" now
    # .ta l:6 r:22 => .ta lt:6 rt:22    
    while re.search(r"[^lcr][lcr]:", self.wb[self.cl]):
      self.wb[self.cl] = re.sub(r"([lcr]):", r'\1t:', self.wb[self.cl])
    
  
    t = self.wb[self.cl].split() # ['.ta', 'lt:6', 'rt:22']
    ncols = len(t) - 1  # skip the .ta piece
    j = 1
    while j <= ncols:
      u = t[j].split(':')
      
      if not u[0][0] in ['l','c','r']:
        self.fatal("table horizontal alignment must be 'l', 'c', or 'r' in {}".format(self.wb[self.cl]))        
      if u[0][0] == 'l':
        haligns.append('<')
      if u[0][0] == 'c':
        haligns.append('^')
      if u[0][0] == 'r':
        haligns.append('>')
        
      valigns.append(u[0][1])  # ['t', 't']
      widths.append(int(u[1]))  # ['6', '22']
      totalwidth += int(u[1]) + 1 # added space between columns
      j += 1
    totalwidth -= 1
    
    # margin to center table in 72 character text field
    if totalwidth >= 72:
      tindent = 0
    else:
      tindent = (72 - totalwidth) // 2

    self.eb.append(".RS 1")  # request blank line above table
        
    self.cl += 1 # move into the table rows
    self.twrap = textwrap.TextWrapper()
    
    # if any cell wraps, put a vertical gap between rows
    rowspace = False  
    k1 = self.cl
    while self.wb[k1] != ".ta-":    

      # lines that we don't check: centered or blank
      if empty.match(self.wb[k1]) or not "|" in self.wb[k1]:
        k1 += 1
        continue
        
      t = self.wb[k1].split("|")
      for i in range(0,ncols):
        k2 = textwrap.wrap(t[i].strip(), widths[i])
        if len(k2) > 1:
          rowspace = True
      k1 += 1
  
    # process each row of table
    while self.wb[self.cl] != ".ta-":
              
      # blank line
      # an empty line in source generates a one char vertical gap
      if empty.match(self.wb[self.cl]):
        self.eb.append("")
        self.cl += 1
        continue
        
      # centered line
      # a line in source that has no vertical pipe
      if not "|" in self.wb[self.cl]:
        self.eb.append("{:^72}".format(self.wb[self.cl]))
        self.cl += 1
        continue        

      # split the text into columns
      t = self.wb[self.cl].split("|")
      
      maxheight = 0
      w = [None] * ncols  # a list of lists for this row
      heights = [None] * ncols  # lines in each cell
      for i in range(0,ncols):
        w[i] = textwrap.wrap(t[i].strip(), widths[i])
        for j,line in enumerate(w[i]):
          w[i][j] =line.strip()  # marginal whitespace
        heights[i] = len(w[i])
        maxheight = max(maxheight, heights[i])
      
      # make all columns same height
      for i in range(0,ncols):
        if len(w[i]) < maxheight: # need to add blank lines in this cell
          if not valigns[i] in ['t','b','m']:
            self.fatal("table vertial alignment must be 't', 'b', or 'm'")
          if valigns[i] == 't':
            w[i] = w[i] + [""] * (maxheight - len(w[i]))
          if valigns[i] == 'b':
            w[i] = [""] * (maxheight - len(w[i])) + w[i]
          if valigns[i] == 'm':
            total_add = maxheight - len(w[i])
            top = total_add // 2
            bottom = total_add - top
            w[i] = [""] * top + w[i] + [" "] * bottom            
        
      # emit the row
      for g in range(0,maxheight):
        if tindent == 0:
          s = " " # ensure at least one leading space
        else:
          s = " " * tindent  # center the table
        for col in range(0,ncols):
          fmt = "{" + ":{}{}".format(haligns[col],widths[col]) + "}"
          s += fmt.format(w[col][g])
          if col != ncols - 1:
            s += " "  # inter-column space so "rl" isn't contingent      
        self.eb.append(s)
      if not self.wb[self.cl + 1 ].startswith(".ta-") and rowspace:
        self.eb.append("")
      
      self.cl += 1  # go to next row in table
      
    self.eb.append(".RS 1")  # request blank line below table
    self.cl += 1  # move past .ta-
    
  def doDropimage(self):
    del self.wb[self.cl] # ignore the directive in text

  def doDropcap(self):
    del self.wb[self.cl] # ignore the directive in text

  def doNa(self):
    del self.wb[self.cl] # ignore the directive in text

  def doAd(self):
    del self.wb[self.cl] # ignore the directive in text

  def doPi(self):
    del self.wb[self.cl] # ignore the directive in text

  def doNi(self):
    del self.wb[self.cl] # ignore the directive in text

  # 03-Apr-2014 .rj or .rj 3, etc.
  def doRj(self):
    m = re.match(r"\.rj (\d+)", self.wb[self.cl]) # number of lines specified
    if m:
      nlines = int(m.group(1))
      self.cl += 1
      self.eb.append(".RS 1")
      while nlines > 0:
        t1 = self.regLL - self.regIN
        xs = "{:>" + str(t1) + "}"
        self.eb.append(" "*self.regIN + xs.format(self.wb[self.cl].strip()))
        self.cl += 1
        nlines -= 1
      self.eb.append(".RS 1")
    else:
      self.fatal("malformed .rj directive: {}".format(self.wb[self.cl]))

  # .de CSS definition
  # ignore the directive in text
  def doDef(self):
    while self.wb[self.cl].endswith("\\"):
      del self.wb[self.cl] # multiple line
    del self.wb[self.cl] # last or single line

  def doPara(self):
    t = []
    pstart = self.cl
    # grab the paragraph from the source file into t[]
    j = pstart
    while (j < len(self.wb) and
           self.wb[j] and
           not re.match("\.", self.wb[j])):
      t.append(self.wb[j])
      j += 1
    pend = j
    s = " ".join(t) # one long string for the paragraph
    u = self.wrap(s, self.regIN, self.regLL, self.regTI)
    self.regTI = 0 # reset any temporary indent
    # set paragraph spacing
    u.insert(0, ".RS 1") # before
    u.append(".RS 1") # after
    self.eb += u
    self.cl = pend

  def process(self):
    self.cl = 0
    while self.cl < len(self.wb):
      if "a" in self.debug:
        print(self.wb[self.cl])
      if not self.wb[self.cl]: # skip blank lines
        self.cl += 1
        continue
      # will hit either a dot directive or wrappable text
      if re.match(r"\.", self.wb[self.cl]):
        self.doDot()
      else:
        self.doPara()

  def run(self): # Text
    self.loadFile(self.srcfile)
    # requested encoding is UTF-8 but file is latin1only
    if self.renc == 'u' and self.latin1only == True:
      return # do not make UTF-8 text file
    # file is ASCII->Latin_1 but trying to run as UTF-8
    if self.encoding == "latin_1" and self.renc == 'u':
      return # do not make UTF-8 text file

    if self.renc == "l":
      print("creating Latin-1 text file")
    if self.renc == "u":
      print("creating UTF-8 text file")

    self.preprocess()
    self.process()
    self.postprocess()

    if self.renc == "l":
      self.saveLat1(self.outfile) # Latin-1
    if self.renc == "u":
      self.saveFileU(self.outfile) # UTF-8

# ====== pph ============================================================================

class Pph(Book):

  pvs = 0 # pending vertical space
  fsz = "100%" # font size for paragraphs
  pdc = "" # pending drop cap
  igc = 1 # illustration geometry counter

  def __init__(self, args, renc):
    Book.__init__(self, args, renc)
    self.dstfile = re.sub("-src", "", self.srcfile.split('.')[0]) + ".html"
    self.css = self.userCSS()
  
  # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  # internal class to manage CSS as it is added at runtime
  class userCSS(object):
    def __init__(self):
      self.cssline = {}

    def addcss(self, s):
      if s in self.cssline:
        self.cssline[s] += 1
      else:
        self.cssline[s] = 1

    def show(self):
      t = []
      keys = list(self.cssline.keys())
      keys.sort()
      for s in keys:
        t.append("      " + s[6:])
      return t
    
  # -------------------------------------------------------------------------------------
  # Roman numeral processsing

  # Define digit mapping
  romanNumeralMap = (('m',  1000), ('cm', 900), ('d',  500), ('cd', 400), ('c',  100),
    ('xc', 90), ('l',  50), ('xl', 40), ('x',  10), ('ix', 9), ('v',  5),
    ('iv', 4), ('i',  1))

  def toRoman(self, n):
    """convert integer to Roman numeral"""
    result = ""
    for numeral, integer in self.romanNumeralMap:
        while n >= integer:
            result += numeral
            n -= integer
    return result

  def fromRoman(self, s):
    """convert Roman numeral to integer"""
    result = 0
    index = 0
    for numeral, integer in self.romanNumeralMap:
        while s[index:index+len(numeral)] == numeral:
            result += integer
            index += len(numeral)
    return result

  # -------------------------------------------------------------------------------------
  # utility methods

  # print if debug includes 'd'
  def dprint(self, msg):
    if 'd' in self.debug:
      print("{}: {}".format(self.__class__.__name__, msg))

  # bailout after saving working buffer in bailout.txt
  def bailout(self, buffer):
    f1 = open("bailout.txt", "w", encoding='utf-8')
    for index,t in enumerate(buffer):
      f1.write( "{:s}\r\n".format(t.rstrip()) )
    f1.close()
    exit(1)

  # any style='...' goes to a class in CSS
  def deStyle(self):
    if 's' in self.debug: # keep styles
      return
    # unwrap page number spans
    i = 0
    while i < len(self.wb):
      # m = re.search("(.*?)(<span class='pagenum'><a.*?a></span>)(.*)$", self.wb[i])
      m = re.search("(.*?)(<span class='pageno'>.*?</span>)(.*)$", self.wb[i])  # new 3.24M
      if m:
        t = []
        if m.group(1):
          t.append(m.group(1))
        t.append(m.group(2))
        if m.group(3):
          t.append(m.group(3))
        self.wb[i:i+1] = t
        i += len(t)
      i += 1
    classarray = []
    for i, line in enumerate(self.wb):
      lcopy = line
      m = re.search("style='(.*?)'", lcopy)
      while m:
        lookup = m.group(1)
        if lookup not in classarray:
          classarray.append(lookup)
        lcopy = re.sub("style='(.*?)'", "", lcopy, 1) # multiples possible on same line
        m = re.search("style='(.*?)'", lcopy)
    for i, line in enumerate(classarray):
      self.css.addcss("[{}] .c{:03d} {{ {} }}".format(800+i, i, line))
    # replace styles with generated classes
    for i, line in enumerate(self.wb):
      m = re.search("style='(.*?)'", self.wb[i])
      while m:
        lookup = m.group(1)
        ix = classarray.index(lookup)
        self.wb[i] = re.sub("style='.*?'", "class='c{:03d}'".format(ix), self.wb[i], 1)
        m = re.search("style='(.*?)'", self.wb[i])
    # combine multiple classes
    # needs to handle <p class='class1' class='class2'>...
    for i, line in enumerate(self.wb):
      m = re.search(r"(class='[^>]*?')([^>]*?)(class='[^>]*?')", self.wb[i])
      if m:
        ck0 = m.group(0)
        ck1 = m.group(1)
        ck2 = m.group(2)
        ck3 = m.group(3)
        m = re.search(r"'(.*?)'", ck1)
        ck1c = m.group(1)
        m = re.search(r"'(.*?)'", ck3)
        ck3c = m.group(1)
        self.wb[i] = re.sub(ck0, "class='{0} {1}' {2} ".format(ck1c, ck3c, ck2), self.wb[i])

  # -------------------------------------------------------------------------------------
  # courtesy id check
  #
  # ID and NAME tokens must begin with a letter ([A-Za-z]) and may be followed by any number
  # of letters, digits ([0-9]), hyphens ("-"), underscores ("_"), colons (":"), and periods (".").
  def checkId(self, s):
    if not re.match(r"[A-Za-z][A-Za-z0-9\-_\:\.]*", s):
      self.fatal("illegal identifier: {}".format(s))
  
  # -------------------------------------------------------------------------------------
  # preprocess working buffer (HTML)
  def preprocess(self):

    self.preProcessCommon()
    
    # HTML will always choose the UTF-8 Greek line
    i = 0
    while i < len(self.wb):
      if self.wb[i].startswith('.gu'):
        self.wb[i] = re.sub("^\.gu ", "", self.wb[i])
      if self.wb[i].startswith('.gl'):
        del(self.wb[i])
        i -= 1
      i += 1

    # page numbers
    i = 0
    while i < len(self.wb):

      # page number increment
      # convert increment to absolute page number
      m = re.match(r"\.pn \+(\d+)", self.wb[i])
      if m:
        increment_amount = int(m.group(1))
        if (self.pageno).isnumeric():
          self.pageno = "{}".format(int(self.pageno) + increment_amount)
        else: # Roman
          n = self.fromRoman(self.pageno)
          n += increment_amount
          self.pageno = self.toRoman(n)
        if self.pnshow or self.pnlink:
          self.wb[i] = "⑯{}⑰".format(self.pageno)
        else:
          del self.wb[i]
        continue

      # page number is explicit
      m = re.match(r"\.pn [\"']?(.+?)($|[\"'])", self.wb[i])
      if m:
        self.pageno = m.group(1)
        if self.pnshow or self.pnlink:
          self.wb[i] = "⑯{}⑰".format(self.pageno)
        else:
          del self.wb[i]
        continue

      # a numeric page number incremented in a heading
      m = re.match(r"\.h.*?pn=\+(\d+)", self.wb[i])
      if m:
        increment_amount = int(m.group(1))
        if (self.pageno).isnumeric():
          self.pageno = "{}".format(int(self.pageno) + increment_amount)
        else: # Roman
          n = self.fromRoman(self.pageno)
          n += increment_amount
          self.pageno = self.toRoman(n)
        if self.pnshow or self.pnlink:
          self.wb[i] = re.sub(r"pn=\+\d+", "pn={}".format(self.pageno), self.wb[i])
        else:
          self.wb[i] = re.sub(r"pn=\+\d+", "", self.wb[i])
        i += 1
        continue

      # an arbitrary page "number" set in a heading
      m = re.match(r"\.h.*?pn=[\"']?(.+?)[\"']?($|/s)", self.wb[i])
      if m:
        self.pageno = m.group(1)
        if not self.pnshow and not self.pnlink:
          self.wb[i] = re.sub(r"pn=[\"']?(.+?)[\"']?($|/s)", "", self.wb[i])
        i += 1
        continue

      i += 1

    # merge page numbers (down) into text
    # ⑯14⑰ moves into next paragraph down or into a heading
    # 21-Jun-2014: handle consecutive .pn +1
    i = 0
    while i < len(self.wb):
      m = re.match(r"⑯(.+)⑰", self.wb[i])
      if m:
        pnum = m.group(1) # string
        del self.wb[i]
        found = False
        while not found:
          # it is possible to hit another pn match before finding a suitable home
          m = re.match(r"⑯(.+)⑰", self.wb[i])
          if m:
            pnum = m.group(1)
            del self.wb[i]
            continue
          # check first. only allowed dot command for placing pn
          if re.match(r"\.h[123]", self.wb[i]):
            self.wb[i] += " pn={}".format(pnum)
            found = True
          # plain text
          if self.wb[i] and not self.wb[i].startswith("."):
            self.wb[i] = "⑯{}⑰".format(pnum) + self.wb[i]
            found = True
          i += 1 # keep looking
      i += 1

    # autonumbered footnotes are assigned numbers
    # footnotes in text
    fncr = 1
    i = 0
    while i < len(self.wb):

      # skip literal sections
      if ".li" == self.wb[i]:
        while i < len(self.wb) and not ".li-" == self.wb[i]:
          i += 1
        if i == len(self.wb):
          self.crash_w_context("unclosed .li", i)
        i += 1
        continue

      m = re.search("\[(\d+)\]", self.wb[i]) # explicit
      if m:
        fncr = int(m.group(1)) + 1
        i += 1
        continue

      m = re.search("\[#\]", self.wb[i]) # auto-assigned
      while m:
        self.wb[i] = re.sub("\[#\]", "[{}]".format(fncr), self.wb[i], 1)
        fncr += 1
        m = re.search("\[#\]", self.wb[i])
      i += 1

    # must do separately
    fncr = 1
    i = 0
    while i < len(self.wb):
      m = re.match(r"\.fn (\d+)", self.wb[i]) # explicit
      if m:
        fncr = int(m.group(1)) + 1
        i += 1
        continue
      if ".fn #" == self.wb[i]: # auto-assigned
        self.wb[i] = ".fn {}".format(fncr)
        fncr += 1
      i += 1

    # footnote references
    # in HTML, check for duplicate forward references and do not duplicate the backlink target
    i = 0
    fnlist = []
    while i < len(self.wb):
      # skip literal sections
      if ".li" == self.wb[i]:
        while not ".li-" == self.wb[i]:
          i += 1
        i += 1
        continue

      # this is a reference in the text to a footnote, like this[14].
      # footnote references can be repeated. Back-link is to the first one only
      m = re.search(r"\[(\d+)\]", self.wb[i])
      while m:
        fnname = m.group(1)
        if fnname in fnlist:
          # it's a duplicate forward reference
          self.warn("duplicate footnote reference: [{}]".format(fnname))
          self.wb[i] = re.sub(r"\[\d+\]", \
          "⑪a href='⑦f{0}' style='text-decoration:none'⑫⑪sup⑫⑬{0}⑭⑪/sup⑫⑪/a⑫".format(fnname), \
          self.wb[i], 1)        
        else:
          # it's the first reference
          fnlist.append(fnname)
          self.wb[i] = re.sub(r"\[\d+\]", \
          "⑪a id='r{0}' /⑫⑪a href='⑦f{0}' style='text-decoration:none'⑫⑪sup⑫⑬{0}⑭⑪/sup⑫⑪/a⑫".format(fnname), \
          self.wb[i], 1)
        m = re.search(r"\[(\d+)\]", self.wb[i])
      i += 1

    # target references
    i = 0
    while i < len(self.wb): 
      if "<target id" in self.wb[i]:   
        m = re.search("<target id='(.*?)'>", self.wb[i])
        while m:
          self.wb[i] = re.sub("<target id='(.*?)'>", "<a id='{0}' name='{0}' />".format(m.group(1)), self.wb[i], 1)
          m = re.search("<target id='(.*?)'>", self.wb[i])
        m = re.search("<target id=\"(.*?)\">", self.wb[i])
        while m:
          self.wb[i] = re.sub("<target id=\"(.*?)\">", "<a id='{0}' name='{}' />".format(m.group(1)), self.wb[i], 1)
          m = re.search("<target id=\"(.*?)\">", self.wb[i])
        m = re.search("<target id=(.*?)>", self.wb[i])
        while m:
          self.wb[i] = re.sub("<target id=(.*?)>", "<a id='{0}' name='{0}' />".format(m.group(1)), self.wb[i], 1)
          m = re.search("<target id=(.*?)>", self.wb[i])          
      i += 1
    
    # inline tags across lines in .nf blocks must be applied to each line
    # applies only to HTML b/c no-fills are rendered as <div>
    i = 0
    while i < len(self.wb):
      if self.wb[i].startswith(".nf"): # find a no-fill block
        tagstack = []
        i += 1
        while not self.wb[i].startswith(".nf"): # as long as we are in a .nf
          # find all tags on this line; ignore <a and </a tags completely for this purpose
          t = re.findall("<\/?[^a][^>]*>", self.wb[i]) 
          sstart = "" # what to prepend to the line
          for s in tagstack: # build the start string
            sstart += s
          self.wb[i] = sstart + self.wb[i] # rewrite the line with new start
          for s in t: # we may have more tags on this line
            if not s.startswith("</"): # it is of form <..> an opening tag
              tagstack.append(s) # save it on the stack
            else:  # it is of form </..> a closing tag
              tmp = re.sub("<\/", "<", s) # decide what its opening tag would be
              try:
                if tmp[0:2] != tagstack[-1][0:2]: # needs close the one most recently open
                  self.fatal("mismatched tag {}".format(s))
              except:
                self.fatal("courtesy inline tag processing: {}".format(self.wb[i])) # one too many
              tagstack.pop() # discard both tags on stack, they balanced each other out.
          send = "" # string end
          for s in reversed(tagstack): # if there is something left, tack it on end of line
            closetag =  re.sub("<","</", s) # make it into a closing tag
            if closetag.startswith("</c"): # anything that had arguments closes without them
              closetag = "</c>" # colors
            if closetag.startswith("</fs"):
              closetag = "</fs>" # font size
            if closetag.startswith("</lang"):
              closetag = "</lang>" # language
            send += closetag
          self.wb[i] = self.wb[i] + send
          i += 1
      i += 1
    
    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    # <lang> tags processed in HTML.
    # <lang="fr">merci</lang>
    # <span lang="fr xml:lang="fr">merci</span>
    for i in range(len(self.wb)):
      m = re.search(r"<lang=[\"']?([^>]+)[\"']?>",self.wb[i])
      while m:
        langspec = m.group(1)
        self.wb[i] = re.sub(m.group(0), "<span lang=\"{0}\" xml:lang=\"{0}\">".format(langspec), self.wb[i], 1)
        m = re.search(r"<lang=[\"']?([^>]+)[\"']?>",self.wb[i])
      self.wb[i] = re.sub(r"<\/lang>","</span>",self.wb[i])
    
    # -------------------------------------------------------------------------
    # inline markup (HTML)
  
    for i, line in enumerate(self.wb):

      # promote the "ignore in text" tags
      # do all of these first so look-ahead (i.e. small caps) will find corrected case.
      self.wb[i] = re.sub(r"<I", "<i", self.wb[i])
      self.wb[i] = re.sub(r"<\/I", "</i", self.wb[i])
      self.wb[i] = re.sub(r"<SC", "<sc", self.wb[i])
      self.wb[i] = re.sub(r"<\/SC", "</sc", self.wb[i])
      self.wb[i] = re.sub(r"<B", "<b", self.wb[i])
      self.wb[i] = re.sub(r"<\/B", "</b", self.wb[i])
      
    for i, line in enumerate(self.wb):  

      # if everything inside <sc>...</sc> markup is uppercase, then
      # use font-size:smaller, else use font-variant:small-caps

      m = re.search("<sc>", self.wb[i]) # opening small cap tag
      if m:
        use_class = "sc" # unless changed
        # we have an opening small cap tag. need to examine all the text
        # up to the closing tag, which may be on a separate line.
        stmp = self.wb[i]
        j = i
        while not re.search(r"<\/sc>", stmp):
          stmp += self.wb[j]
          j += 1
        m = re.search(r"<sc>([^<]+?)</sc>", stmp)
        if m:
          scstring = m.group(1)
          if scstring == scstring.lower(): # all lower case
            self.warn("all lower case inside small-caps markup: {}".format(self.wb[i]))
          if scstring == scstring.upper(): # all upper case
            use_class = "fss"
        if use_class == "sc":
          self.wb[i] = re.sub("<sc>", "<span class='sc'>", self.wb[i])
          self.css.addcss("[200] .sc { font-variant:small-caps; }")
        if use_class == "fss":
          self.wb[i] = re.sub("<sc>", "<span class='fss'>", self.wb[i])
          self.css.addcss("[200] .fss { font-size:75%; }")          

      # common closing, may be on separate line
      self.wb[i] = re.sub("<\/sc>", "</span>", self.wb[i])

      m = re.search("<l>", self.wb[i])
      if m:
        self.css.addcss("[201] .large { font-size:large; }")
      self.wb[i] = re.sub("<l>", "<span class='large'>", self.wb[i])
      self.wb[i] = re.sub("<\/l>", "</span>", self.wb[i])

      m = re.search("<xl>", self.wb[i])
      if m:
        self.css.addcss("[202] .xlarge { font-size:x-large; }")
      self.wb[i] = re.sub("<xl>", "<span class='xlarge'>", self.wb[i])
      self.wb[i] = re.sub("<\/xl>", "</span>", self.wb[i])
      
      m = re.search("<xxl>", self.wb[i])
      if m:
        self.css.addcss("[202] .xxlarge { font-size:xx-large; }")
      self.wb[i] = re.sub("<xxl>", "<span class='xxlarge'>", self.wb[i])
      self.wb[i] = re.sub("<\/xxl>", "</span>", self.wb[i])      

      m = re.search("<s>", self.wb[i])
      if m:
        self.css.addcss("[203] .small { font-size:small; }")
      self.wb[i] = re.sub("<s>", "<span class='small'>", self.wb[i])
      self.wb[i] = re.sub("<\/s>", "</span>", self.wb[i])

      m = re.search("<xs>", self.wb[i])
      if m:
        self.css.addcss("[204] .xsmall { font-size:x-small; }")
      self.wb[i] = re.sub("<xs>", "<span class='xsmall'>", self.wb[i])
      self.wb[i] = re.sub("<\/xs>", "</span>", self.wb[i])
      
      m = re.search("<xxs>", self.wb[i])
      if m:
        self.css.addcss("[205] .xxsmall { font-size:xx-small; }")
      self.wb[i] = re.sub("<xxs>", "<span class='xxsmall'>", self.wb[i])
      self.wb[i] = re.sub("<\/xxs>", "</span>", self.wb[i])      

      m = re.search("<u>", self.wb[i])
      if m:
        self.css.addcss("[205] .under { text-decoration:underline; }")
      self.wb[i] = re.sub("<u>", "<span class='under'>", self.wb[i])
      self.wb[i] = re.sub("<\/u>", "</span>", self.wb[i])

      m = re.search(r"<c=[\"']?(.*?)[\"']?>", self.wb[i])
      while m:
        thecolor = m.group(1)
        safename = re.sub("#","", thecolor)
        self.css.addcss("[209] .color_{0} {{ color:{1}; }}".format(safename,thecolor))
        self.wb[i] = re.sub("<c.*?>", "<span class='color_{0}'>".format(safename), self.wb[i], 1)
        m = re.search(r"<c=[\"']?(.*?)[\"']?>", self.wb[i])
      self.wb[i] = re.sub("<\/c>", "</span>", self.wb[i],1)

      # 27-Jun-2014 <g> is now a stylized em in HTML
      m = re.search(r"<g>", self.wb[i])
      if m:
        self.wb[i] = re.sub(r"<g>", "<em class='gesperrt'>", self.wb[i])
        self.css.addcss("[378] em.gesperrt { font-style: normal; letter-spacing: 0.2em; margin-right: -0.2em; }")
        self.css.addcss("[379] @media handheld { em.gesperrt { font-style: italic; letter-spacing: 0; margin-right: 0;}}")
      self.wb[i] = re.sub("<\/g>", "</em>", self.wb[i],1)  

      m = re.search(r"<fs=[\"']?(.*?)[\"']?>", self.wb[i])
      while m:
        self.wb[i] = re.sub(m.group(0), "<span style='font-size:{}'>".format(m.group(1)), self.wb[i], 1)
        m = re.search(r"<fs=[\"']?(.*?)[\"']?>", self.wb[i])
      self.wb[i] = re.sub("<\/fs>", "</span>", self.wb[i])  

  # -------------------------------------------------------------------------------------
  # post-process working buffer

  def postprocess(self):

    for i, line in enumerate(self.wb):
      self.wb[i] = re.sub("ⓓ", ".", self.wb[i])
      self.wb[i] = re.sub("①", "{", self.wb[i])
      self.wb[i] = re.sub("②", "}", self.wb[i])
      self.wb[i] = re.sub("③", "[", self.wb[i])
      self.wb[i] = re.sub("④", "]", self.wb[i])
      self.wb[i] = re.sub("⑤", "&lt;", self.wb[i])
      # text space replacement
      self.wb[i] = re.sub("ⓢ", "&nbsp;", self.wb[i]) # non-breaking space
      self.wb[i] = re.sub("ⓣ", "&#8203;", self.wb[i]) # zero space
      self.wb[i] = re.sub("ⓤ", "&thinsp;", self.wb[i]) # thin space
      self.wb[i] = re.sub("ⓥ", "&#8196;", self.wb[i]) # thick space
      # ampersand
      self.wb[i] = re.sub("Ⓩ", "&amp;", self.wb[i])
      # protected
      self.wb[i] = re.sub("⑪", "<", self.wb[i])
      self.wb[i] = re.sub("⑫", ">", self.wb[i])
      self.wb[i] = re.sub("⑬", "[", self.wb[i])
      self.wb[i] = re.sub("⑭", "]", self.wb[i])

      # superscripts, subscripts
      self.wb[i] = re.sub(r"◸(.*?)◹", r'<sup>\1</sup>', self.wb[i])
      self.wb[i] = re.sub(r"◺(.*?)◿", r'<sub>\1</sub>', self.wb[i])

      # use entities if user is writing any "--" or "----" to the HTML file
      # if this is Latin-1 output. Otherwise, trust the PPer.
      if self.encoding == 'latin_1' and self.renc == "h":
        self.wb[i] = self.wb[i].replace("--", "&mdash;")
      # flag an odd number of dashes
      if "&mdash;-" in self.wb[i]:
        self.warn("&mdash; with hyphen: {}".format(self.wb[i]))
      # ok now to unprotect those we didn't want to go to &mdash; entity
      self.wb[i] = re.sub(r"⑨", '-', self.wb[i])
                           
      self.wb[i] = re.sub(r"\[oe\]", r'&oelig;', self.wb[i])
      self.wb[i] = re.sub(r"\[ae\]", r'&aelig;', self.wb[i])
      self.wb[i] = re.sub(r"\[OE\]", r'&OElig;', self.wb[i])
      self.wb[i] = re.sub(r"\[AE\]", r'&AElig;', self.wb[i])

    i = 0
    while i < len(self.wb):
      m = re.search(r"⑯(.+)⑰", self.wb[i]) # page number
      if m:
        ptmp = m.group(1)
        if self.pnshow:  # visible page number
          # in a paragraph usually, but can be orphaned (repaired later)
          self.wb[i] = re.sub(r"⑯(.+)⑰",
          "<span class='pageno' title='{0}' id='Page_{0}' ></span>".format(ptmp),
          self.wb[i])
          # "<span class='pagenum'><a name='Page_{0}' id='Page_{0}'>{0}</a></span>".format(ptmp)   # pre-3.24M
        elif self.pnlink:  # just the link
          self.wb[i] = re.sub(r"⑯(.+)⑰", "<a name='Page_{0}' id='Page_{0}'></a>".format(ptmp), self.wb[i])
      i += 1

    # internal page links
    # two forms: #17# and #The Encounter:ch01#
    for i in range(len(self.wb)):

      m = re.search(r"#(\d+)#", self.wb[i])
      while m: # page number reference
        s = "<a href='⫉Page_{0}'>{0}</a>".format(m.group(1)) # link to it
        self.wb[i] = re.sub(r"#(\d+)#", s, self.wb[i], 1)
        m = re.search(r"#(\d+)#", self.wb[i])

      m = re.search(r"#(.*?):(.*?)#", self.wb[i]) # named reference
      while m:
        s = "<a href='⫉{}'>{}</a>".format(m.group(2), m.group(1)) # link to that
        self.wb[i] = re.sub(r"#(.*?):(.*?)#", s, self.wb[i], 1)
        m = re.search(r"#(.*?):(.*?)#", self.wb[i])

      self.wb[i] = re.sub("⫉", '#', self.wb[i])
      i += 1

    for i, line in enumerate(self.wb):
      self.wb[i] = re.sub("⑥", ":", self.wb[i])

  # -------------------------------------------------------------------------------------
  # save buffer to specified dstfile (HTML output)
  def saveFile(self, fn):

    # remove double blank lines
    i = 0
    while i < len(self.wb) - 1:
      if not self.wb[i] and not self.wb[i+1]:
        del self.wb[i]
        i -= 1
      i += 1
    f1 = codecs.open(fn, "w", self.encoding)
    for index,t in enumerate(self.wb):
      try:
        f1.write( "{:s}\r\n".format(t))
      except Exception as e:
        print( "internal error:\n  cannot write line: {:s}".format(t) )
        self.fatal("exiting")
    f1.close()

  # ----- makeHTML method group -----

  def doHeader(self):

    # common CSS

    if self.pnshow:
      self.css.addcss("[100] body { margin-left:8%;margin-right:10%; }")
      self.css.addcss("[105] .pageno { right:1%;font-size:x-small;background-color:inherit;color:" + self.nregs["pnc"] + ";")
      self.css.addcss("[106]         text-indent:0em;text-align:right;position:absolute;")
      self.css.addcss("[107]         border:1px solid " + self.nregs["pnc"] + ";padding:1px 3px;font-style:normal;")
      self.css.addcss("[108]         font-variant:normal;font-weight:normal;text-decoration:none; }")
      self.css.addcss("[109] .pageno:after { color: " + self.nregs["pnc"] + "; content: attr(title); }")  # new 3.24M
    else:
      self.css.addcss("[100] body { margin-left:8%;margin-right:8%; }")

    self.css.addcss("[170] p { text-indent:0;margin-top:0.5em;margin-bottom:0.5em;text-align:justify; }") # para style

    # HTML header
    t = []
    t.append("<!DOCTYPE html PUBLIC \"-//W3C//DTD XHTML 1.0 Strict//EN\"")
    t.append("    \"http://www.w3.org/TR/xhtml1/DTD/xhtml1-strict.dtd\">")
    t.append("<html xmlns=\"http://www.w3.org/1999/xhtml\" xml:lang=\"en\" lang=\"en\">")
    t.append("  <head>")

    if self.encoding == "utf_8":
      t.append("    <meta http-equiv=\"Content-Type\" content=\"text/html;charset=UTF-8\" />")
    if self.encoding == "latin_1":
      t.append("    <meta http-equiv=\"Content-Type\" content=\"text/html;charset=ISO-8859-1\" />")

    if self.dtitle != "":
      t.append("    <title>{}</title>".format(self.dtitle))
    else:
      t.append("    <title>{}</title>".format("Unknown"))
    t.append("    <link rel=\"coverpage\" href=\"images/{}\" />".format(self.cimage))
    t.append("    <style type=\"text/css\">")
    t.append("      CSS PLACEHOLDER")
    t.append("    </style>")
    t.append("  </head>")
    t.append("  <body>   ")
    t.append("")
    self.wb = t + self.wb # prepend header

  def doFooter(self):
    self.wb.append("")
    self.wb.append("  </body>")
    if not self.anonymous:
      self.wb.append("  <!-- created with ppgen.py {} on {} -->".format(VERSION, NOW))
    self.wb.append("</html>")

  def placeCSS(self):
    i = 0
    while i < len(self.wb):
      if re.search("CSS PLACEHOLDER", self.wb[i]):
        self.wb[i:i+1] = self.css.show()
        return
      i += 1

  # ----- process method group -----

  # .li literal (pass-through)
  def doLit(self):
    del self.wb[self.cl]  # .li
    while self.wb[self.cl] != ".li-":
      # leave in place
      self.cl += 1
    del self.wb[self.cl]  # .li-

  # .pb page break
  def doPb(self):
    self.css.addcss("[465] div.pbb { page-break-before:always; }")
    self.css.addcss("[466] hr.pb { border:none;border-bottom:1px solid; margin:1em auto; }")        
    self.css.addcss("[467] @media handheld { hr.pb { display:none; }}")
    self.wb[self.cl:self.cl+1] = ["<div class='pbb'></div>", "<hr class='pb' />"]
    self.cl += 2

  # .hr horizontal rule
  def doHr(self):
    hrpct = 100
    m = re.match(r"\.hr (\d+)%", self.wb[self.cl])
    if m:
      hrpct = int(m.group(1))
    if hrpct == 100:
      self.wb[self.cl] = "<hr style='border:none;border-bottom:1px solid;margin:1em auto;' />"
    else:
      lmarp = (100 - hrpct)//2
      rmarp = 100 - hrpct - lmarp
      self.wb[self.cl] = "<hr style='border:none;border-bottom:1px solid;margin-top:1em;margin-bottom:1em; margin-left:{}%; width:{}%; margin-right:{}%' />".format(lmarp,hrpct,rmarp)
    self.cl += 1

  # .tb thought break
  # thought breaks fixed at 35% thin line.
  def doTbreak(self):
    self.wb[self.cl] = "<hr style='border:none;border-bottom:1px solid; margin-top:0.8em;margin-bottom:0.8em;margin-left:35%; margin-right:35%; width:30%' />" # for IE
    self.cl += 1

  # .de CSS definition
  # one liners: .de h1 { color:red; }
  def doDef(self):
    if not self.wb[self.cl].endswith("\\"):
      # single line
      self.wb[self.cl] = re.sub(r"\.de ", "", self.wb[self.cl])
      self.css.addcss("[999] {}".format(self.wb[self.cl])) # put user CSS at end, always.
      del self.wb[self.cl]
    else:
      # multiple line
      self.wb[self.cl] = re.sub(r"\.de ", "", self.wb[self.cl])
      while self.wb[self.cl].endswith("\\"):
        s = re.sub(r"\\", "", self.wb[self.cl])
        self.css.addcss("[{}] {}".format(self.csslc, s))
        self.csslc += 1
        del self.wb[self.cl]
      # final line
      self.css.addcss("[{}] {}".format(self.csslc, self.wb[self.cl]))
      self.csslc += 1
      del self.wb[self.cl]

  # h1
  def doH1(self):
    pnum = ""
    id = ""
    rend = "" # default no rend
    hcss = "text-align:center;font-weight:normal;font-size:1.4em;"
    m = re.match(r"\.h1 (.*)", self.wb[self.cl])
    if m: # modifier
      rend = m.group(1)

      if "nobreak" in rend:
        hcss += "page-break-before:auto;"
      else:
        hcss += "page-break-before:always;"

      m = re.search(r"pn=[\"']?(.+?)($|[\"' ])", rend)
      if m:
        pnum = m.group(1)

      m = re.search(r"id=[\"']?(.+?)($|[\"' ])", rend)
      if m:
        id = m.group(1)
        self.checkId(id)  # validate identifier name

    if self.pvs > 0:
      hcss += "margin-top:{}em;".format(self.pvs)
      self.pvs = 0
    else: # default 1 before, 1 after
      hcss += "margin-top:1em;"
      self.pvs = 1

    del self.wb[self.cl] # the .h line
    s = re.sub(r"\|\|", "<br /> <br />", self.wb[self.cl]) # required for epub
    s = re.sub("\|", "<br />", s)
    t = []

    # new in 1.79
    t.append("<div>")
    if pnum != "":
      if self.pnshow:
        # t.append("  <span class='pagenum'><a name='Page_{0}' id='Page_{0}'>{0}</a></span>".format(pnum))
        t.append("  <span class='pageno' title='{0}' id='Page_{0}' ></span>".format(pnum)) # new 3.24M
      elif self.pnlink:
        t.append("  <a name='Page_{0}' id='Page_{0}'></a>".format(pnum))
    if id != "":
      t.append("  <h1 id='{}' style='{}'>{}</h1>".format(id, hcss, s))
    else:
      t.append("  <h1 style='{}'>{}</h1>".format(hcss, s))
    t.append("</div>")

    self.wb[self.cl:self.cl+1] = t
    self.cl += len(t)

  # h2
  def doH2(self):
    pnum = ""
    id = ""
    hcss = "text-align:center;font-weight:normal;font-size:1.2em;"
    m = re.match(r"\.h2 (.*)", self.wb[self.cl])
    rend = "" # default no rend
    if m: # modifier
      rend = m.group(1)

      if "nobreak" in rend:
        hcss += "page-break-before:auto;"
      else:
        hcss += "page-break-before:always;"

      m = re.search(r"pn=[\"']?(.+?)($|[\"' ])", rend)
      if m:
        pnum = m.group(1)

      m = re.search(r"id=[\"']?(.+?)($|[\"' ])", rend)
      if m:
        id = m.group(1)
        self.checkId(id)

    if self.pvs > 0:
      hcss += "margin-top:{}em;".format(self.pvs)
      self.pvs = 0
    else: # default 4 before, 2 after
      hcss += "margin-top:4em;"
      self.pvs = 2

    del self.wb[self.cl] # the .h line
    s = re.sub(r"\|\|", "<br /> <br />", self.wb[self.cl]) # required for epub
    s = re.sub("\|", "<br />", s)
    t = []

    # new in 1.79
    # I always want a div. If it's not a no-break, give it class='chapter'
    if "nobreak" in rend:
      t.append("<div>")
    else:
      t.append("<div class='chapter'>") # will force file break
      self.css.addcss("[576] .chapter { }")
    if pnum != "":
      if self.pnshow:
        # t.append("  <span class='pagenum'><a name='Page_{0}' id='Page_{0}'>{0}</a></span>".format(pnum))
        t.append("  <span class='pageno' title='{0}' id='Page_{0}' ></span>".format(pnum)) # new 3.24M
      elif self.pnlink:
        t.append("  <a name='Page_{0}' id='Page_{0}'></a>".format(pnum))
    if id != "":
      t.append("  <h2 id='{}' style='{}'>{}</h2>".format(id, hcss, s))
    else:
      t.append("  <h2 style='{}'>{}</h2>".format(hcss, s))
    t.append("</div>")

    self.wb[self.cl:self.cl+1] = t
    self.cl += len(t)

  # h3
  def doH3(self):
    pnum = ""
    id = ""
    hcss = "text-align:center;font-weight:normal;font-size:1.2em;"
    m = re.match(r"\.h3 (.*)", self.wb[self.cl])
    if m: # modifier
      rend = m.group(1)

      if "nobreak" in rend:
        hcss += "page-break-before:auto;"
      else:
        hcss += "page-break-before:always;"

      m = re.search(r"pn=[\"']?(.+?)($|[\"' ])", rend)
      if m:
        pnum = m.group(1)

      m = re.search(r"id=[\"']?(.+?)($|[\"' ])", rend)
      if m:
        id = m.group(1)
        self.checkId(id)

    if self.pvs > 0:
      hcss += "margin-top:{}em;".format(self.pvs)
      self.pvs = 0
    else: # default 4 before, 2 after
      hcss += "margin-top:2em;"
      self.pvs = 1

    del self.wb[self.cl] # the .h line
    s = re.sub(r"\|\|", "<br /> <br />", self.wb[self.cl]) # required for epub
    s = re.sub("\|", "<br />", s)
    t = []

    # new in 1.79
    # sections do not force file breaks. chapters usually do.
    if pnum != "":
      t.append("<div>")
      if self.pnshow:
        # t.append("  <span class='pagenum'><a name='Page_{0}' id='Page_{0}'>{0}</a></span>".format(pnum))
        t.append("  <span class='pageno' title='{0}' id='Page_{0}' ></span>".format(pnum)) # new 3.24M
      elif self.pnlink:
        t.append("  <a name='Page_{0}' id='Page_{0}'></a>".format(pnum))
    if id != "":
      t.append("<h3 id='{}' style='{}'>{}</h3>".format(id, hcss, s))
    else:
      t.append("<h3 style='{}'>{}</h3>".format(hcss, s))
    if pnum != "":
      t.append("</div>")

    self.wb[self.cl:self.cl+1] = t
    self.cl += len(t)


  # .sp n
  # if a space is encountered. for HTML drop it to the next
  # displayable text and generate a top margin.
  def doSpace(self):
    m = re.match(r"\.sp (\d+)", self.wb[self.cl])
    if m:
      self.pvs = int(m.group(1))
      del self.wb[self.cl]
    else:
      self.fatal("malformed space directive: {}".format(self.wb[self.cl]))

  # .fs
  # change font size for following paragraphs
  # em and % only for scalable text in readers
  #   .fs 0.8em  set font size to 0.8em
  #   .fs 80%    set font size to 80%
  #   .fs        shortcut, reset font size to 100%
  def doFontSize(self):
    if ".fs" == self.wb[self.cl]: # .fs with no args resets to 100%
      self.fsz = "100%" # reset font size
      self.wb[self.cl] = "" # processing complete
    m = re.match(r"\.fs (.+)%", self.wb[self.cl])
    if m:
      self.fsz = m.group(1) + "%"
      self.wb[self.cl] = ""
    m = re.match(r"\.fs (.+)em", self.wb[self.cl])
    if m:
      self.fsz = m.group(1) + "em"
      self.wb[self.cl] = ""
    if ".fs" in self.wb[self.cl]:
      self.warn("font-size directive error: {}".format(self.wb[self.cl]))
    del self.wb[self.cl]

  # .il illustrations
  # .il id=i01 fn=illus-fpc.jpg w=332 alt=illus-fpcf.jpg
  # .ca Dick was taken by surprise.
  #
  # cw=  caption width
  # id= identifier (ok)
  # cj=  caption justification
  # fn= filename (ok)
  # link= linked-to file (ok)
  # alt=  alternate text
  # w= displayed width (ok)
  # align= left, center, right default center (ok)
  
  def doIllo(self):
          
    # 02-Jul-2014 thanks for this code, Nigel
    def checkIllo(fname): # assure that fn exists in images folder
      fullname = os.path.join(os.path.dirname(self.srcfile),"images",fname)
      if not os.path.isfile(fullname):
        self.warn("file {} not in images folder".format(fullname))

    linkto_file = ""
    m = re.match(r"\.il (.*)", self.wb[self.cl])
    rep = 1 # source lines to replace
    if m:
      attr = m.group(1)
            
      # pull out optional caption width
      ocw = 0  # zero means it hasn't been set by the user
      if "cw=" in attr:
        attr, ocws = self.get_id("cw",attr)  # as a string
        ocws = re.sub("%", "", ocws)  # remove courtesy %
        ocw = int(ocws)  

      # pull out optional caption justification
      # (l)eft, (c)enter, (r)ight, (f)ull
      cj = 0  # zero means it hasn't been set by the user
      if "cj=" in attr:
        attr, cj = self.get_id("cj",attr)
      
      # pull out id if present
      iid = ""
      if "id=" in attr:
        attr, the_id = self.get_id("id",attr)
        iid = "id='{}' ".format(the_id)    

      # now the filenames
      display_file = ""  # file that is displayed
      if "fn=" in attr:
        attr, display_file = self.get_id("fn", attr)
        checkIllo(display_file)        
      else:
        self.fatal("no display file specified in {}".format(self.wb[self.cl]))

      linkto_file = ""  # file that is linked to
      if "link=" in attr:
        attr, linkto_file = self.get_id("link", attr)
        checkIllo(linkto_file)        
        
      alt_text = ""
      if "alt=" in attr:
        attr, alt_text = self.get_id("alt", attr)

      # image width
      iw = 0
      if "w=" in attr:
        attr, swid = self.get_id("w", attr)
        swid = re.sub("px", "", swid)  # courtesy allow 350px or 350
        iw = int(swid)
      else:  
        self.fatal("no image width specified in {}".format(self.wb[self.cl]))

      # align attributes
      # l, c, r, left, center, right
      img_align = "c"
      if "align=" in attr:
        attr, s = self.get_id("align", attr)
        img_align = s[0]

      caption_present = False
      if self.cl+1 < len(self.wb) and re.match(r"\.ca", self.wb[self.cl+1]):
        caption_present = True

      # build the CSS for this illustration
      if img_align == "c":
        self.css.addcss("[600] .figcenter { clear:both; max-width:100%; margin:2em auto; text-align:center; }")
        if caption_present:
            self.css.addcss("[601] div.figcenter p { text-align:center; text-indent:0; }")
      if img_align == "l":
        self.css.addcss("[602] .figleft { clear:left; float:left; margin:4% 4% 4% 0; }")
        self.css.addcss("[603] @media handheld { .figleft { float:left; }}")
        if caption_present:
            self.css.addcss("[603] div.figleft p { text-align:center; text-indent:0; }")
      if img_align == "r":
        self.css.addcss("[604] .figright { clear:right; float:right; margin:4% 0 4% 4%; }")
        self.css.addcss("[605] @media handheld { .figright { float:right; text-align: right; }}")
        if caption_present:
            self.css.addcss("[603] div.figright p { text-align:center; text-indent:0; }") 
          
      # if any image is in document
      self.css.addcss("[603] img { max-width:100%; height:auto; }")
      
      # make CSS name from igc counter
      ign = "ig{:03d}".format(self.igc)
      icn = "ic{:03d}".format(self.igc)
      self.igc += 1     

      if caption_present:
        if ocw > 0:  # user has set caption width
          oml = (100 - ocw) // 2
          omr = 100 - ocw - oml
          self.css.addcss("[604] .{} {{ width:{}%; margin-left:{}%; margin-right:{}%; }} ".format(icn, ocw, oml, omr))  
        else:
          self.css.addcss("[604] .{} {{ width:{}px; margin: auto; max-width:100%; }} ".format(icn, iw))  
          self.css.addcss("[605] @media handheld {{ .{} {{ width:80%; margin-left: 10%; margin-right: 10%; }}}}".format(icn))
        if cj != "":
          if cj == 'l':
            self.css.addcss("[608] div.{} p {{ text-align:left; }} ".format(icn, iw))  
          elif cj == 'r':
            self.css.addcss("[608] div.{} p {{ text-align:right; }} ".format(icn, iw))  
          elif cj == 'c':
            self.css.addcss("[608] div.{} p {{ text-align:center; }} ".format(icn, iw))  
          elif cj == 'f':
            self.css.addcss("[608] div.{} p {{ text-align:justify; }} ".format(icn, iw))  

      self.css.addcss("[606] .{} {{ width:{}px; }} ".format(ign, iw)) 

      # create replacement stanza for illustration
      u = []

      if img_align == "c":
        u.append("<div {}class='figcenter'>".format(iid))
      if img_align == "l":
        u.append("<div {}class='figleft'>".format(iid))
      if img_align == "r":
        u.append("<div {}class='figright'>".format(iid))

      # 16-Apr-2014: placed link in div
      if linkto_file != "": # link to larger image specified in markup
        u.append("<a href='images/{}'><img src='images/{}' alt='{}' class='{}' /></a>".format(linkto_file,display_file, alt_text, ign))
      else: # no link to larger image
        u.append("<img src='images/{}' alt='{}' class='{}' />".format(display_file, alt_text, ign))

      # is the .il line followed by a caption line?
      if caption_present:
        u.append("<div class='{}'>".format(icn))
        if self.wb[self.cl+1] == ".ca": # multiline
          rep += 1
          j = 2
          s = self.wb[self.cl+j] + "<br />"
          rep += 1
          j += 1
          while self.wb[self.cl+j] != ".ca-":
            s += self.wb[self.cl+j] + "<br />"
            j += 1
            rep += 1
          rep += 1
          caption = s[0:-6] # strip trailing break tag
        else: # single line
          caption = self.wb[self.cl+1][4:]
          rep += 1
        u.append("<p>{}</p>".format(caption))
        u.append("</div>")
      u.append("</div>") # the entire illustration div
      # replace with completed HTML
      self.wb[self.cl:self.cl+rep] = u
      self.cl += len(u)

  # .in left margin indent
  def doIn(self):

    m = re.match(r"\.in \+(.+)", self.wb[self.cl])
    if m:
      self.instack.append(self.regIN)
      self.regIN += int(m.group(1)) # relative
      del self.wb[self.cl]
      return

    m = re.match(r"\.in \-(.+)", self.wb[self.cl])
    if m:
      self.instack.append(self.regIN)
      self.regIN -= int(m.group(1)) # relative
      if self.regIN < 0:
        self.crash_w_context("left margin out of bounds", self.cl)
      del self.wb[self.cl]
      return

    m = re.match(r"\.in (\d+)", self.wb[self.cl])
    if m:
      self.instack.append(self.regIN)
      self.regIN = int(m.group(1)) # absolute
      del self.wb[self.cl]
      return

    if ".in" == self.wb[self.cl]:
      try:
        self.regIN = self.instack.pop()
      except:
        self.crash_w_context("indent error: no indent to undo", self.cl, 2)
      del self.wb[self.cl]
      return

    # should not get here
    self.fatal("malformed .in command: \"{}\"".format(self.wb[self.cl]))

  # .ll line length
  def doLl(self):
    m = re.match(r"\.ll \+(.+)", self.wb[self.cl])
    if m:
      self.llstack.append(self.regLL)
      self.regLL += int(m.group(1)) # relative
      if self.regLL <= 0:
        self.crash_w_context("attempt to set line length less than zero", self.cl)    
      del self.wb[self.cl]
      return

    m = re.match(r"\.ll \-(.+)", self.wb[self.cl])
    if m:
      self.llstack.append(self.regLL)
      self.regLL -= int(m.group(1)) # relative
      if self.regLL <= 0:
        self.crash_w_context("attempt to set line length less than zero", self.cl)
      del self.wb[self.cl]
      return

    m = re.match(r"\.ll (\d+)", self.wb[self.cl])
    if m:
      self.llstack.append(self.regLL)
      self.regLL = int(m.group(1)) # absolute
      if self.regLL <= 0:
        self.crash_w_context("attempt to set line length less than zero", self.cl)
      del self.wb[self.cl]
      return

    if ".ll" == self.wb[self.cl]:
      try:
        self.regLL = self.llstack.pop()
      except:
        self.crash_w_context("line length error: no line length to undo", self.cl, 2)
      del self.wb[self.cl]
      return

    # should not get here
    self.fatal("malformed .ll directive: {}".format(self.wb[self.cl]))

  # .ti temporary indent
  def doTi(self):
    m = re.match(r"\.ti (.+)", self.wb[self.cl])
    if m:
      # special case: forcing a .ti of 0
      if int(m.group(1)) == 0:
        self.regTI = -1000
      else:
        self.regTI += int(m.group(1))
      del self.wb[self.cl]

  # .nr named register
  def doNr(self):
    m = re.match(r"\.nr (.+) (.+)", self.wb[self.cl])
    if m:
      registerName = m.group(1)
      registerValue = m.group(2)
      known_register = False
      if registerName == "psi": # paragraph spacing, indented text
        self.nregs["psi"] = m.group(2)
        known_register = True
      if registerName == "psb": # paragraph spacing, block text
        self.nregs["psb"] = m.group(2)
        known_register = True
      if registerName == "pnc": # page number color
        self.nregs["pnc"] = m.group(2)
        known_register = True        
      if not known_register:
        self.crash_w_context("undefined register: {}".format(registerName), self.cl)
    del self.wb[self.cl]

  # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  # no-fill, centered (HTML)
  # takes no internal justification commands
  # note: mo is currently ignored for centered blocks.
  def doNfc(self, mo):
    s = self.fetchStyle()
    startloc = self.cl
    i = self.cl
    t = []
    t.append("")

    if self.pindent:
      t.append("<div class='nf-center-c0'>")
    else:
      t.append("<div class='nf-center-c1'>")

    if not s:
      t.append("  <div class='nf-center'>")
    else:
      t.append("<div class='nf-center' style='{}'>".format(s))

    if self.pindent:
      self.css.addcss("[876] .nf-center-c0 { text-align:left;margin:0.5em 0; }")  # 17-Jul-2014
    else:
      self.css.addcss("[876] .nf-center-c1 { text-align:left;margin:1em 0; }")

    self.css.addcss("[873] .nf-center { text-align:center; }")
    i += 1
    printable_lines_in_block = 0
    pending_mt = 0
    while self.wb[i] != ".nf-":      
      if "" == self.wb[i]:
        pending_mt += 1
        i += 1
        continue
      if pending_mt > 0:
        t.append("    <div style='margin-top:{}em'>".format(pending_mt) + self.wb[i].strip() + "</div>")
        printable_lines_in_block += 1
        pending_mt = 0
      else:
        t.append("    <div>" + self.wb[i].strip() + "</div>")
        printable_lines_in_block += 1        
      i += 1
    # at block end.
    if printable_lines_in_block == 0:
        self.fatal("empty .nf block")
    # there may be a pending mt at the block end.
    if pending_mt > 0:
      t[-1] = re.sub(r"<div", "<div style='margin-bottom:{}em'".format(pending_mt), t[-1])
      pending_mt = 0    
    t.append("  </div>")
    t.append("</div>")
    t.append("")
    endloc = i
    self.wb[startloc:endloc+1] = t
    self.cl = startloc + len(t)

  # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  # no-fill, block. block type specified. any type except centered
  def doNfb(self, nft, mo):
    # any poetry triggers the same CSS
    if 'b' == nft:
      self.css.addcss("[215] .lg-container-b { text-align: center; }")  # alignment of entire block
      self.css.addcss("[216] @media handheld { .lg-container-b { clear: both; }}")
    if 'l' == nft:
      self.css.addcss("[217] .lg-container-l { text-align: left; }")
      self.css.addcss("[218] @media handheld { .lg-container-l { clear: both; }}")
    if 'r' == nft:
      self.css.addcss("[219] .lg-container-r { text-align: right; }")
      self.css.addcss("[220] @media handheld { .lg-container-r { clear: both; }}")
      
    self.css.addcss("[221] .linegroup { display: inline-block; text-align: left; }")  # alignment inside block
    self.css.addcss("[222] @media handheld { .linegroup { display: block; margin-left: 1.5em; }}")
    if mo:
      self.css.addcss("[223] .linegroup .group0 { margin: 0 auto; }")
    else:
      self.css.addcss("[223] .linegroup .group { margin: 1em auto; }")
    self.css.addcss("[224] .linegroup .line { text-indent: -3em; padding-left: 3em; }")

    ssty = ""
    s = self.fetchStyle() # supplemental style
    if s:
      ssty = " style='{}'".format(s)
    startloc = self.cl
    i = self.cl
    t = []

    closing = ""
    if 'b' == nft:
      t.append("<div class='lg-container-b'>")
      closing = ".nf-"
    if 'l' == nft:
      t.append("<div class='lg-container-l'>")
      closing = ".nf-"
    if 'r' == nft:
      t.append("<div class='lg-container-r'>")
      closing = ".nf-"
    t.append("  <div class='linegroup'{}>".format(ssty))
    if mo:
      t.append("    <div class='group0'>")
    else:
      t.append("    <div class='group'>")

    i += 1
    cpvs = 0
    printable_lines_in_block = 0
    while self.wb[i] != closing:

      # a centered line inside a no-fill block
      m = re.match(r"\.ce (\d+)", self.wb[i])
      if m:
        count = int(m.group(1))
        i += 1 # skip the .ce
        while count > 0:
          pst = "text-align: center;"
          t.append("    <div style='{}'>{}</div>".format(pst, self.wb[i]))
          i += 1
          count -= 1
        continue

      # a right-justified line inside a no-fill block
      m = re.match(r"\.rj (\d+)", self.wb[i])
      if m:
        count = int(m.group(1))
        i += 1 # skip the .rj
        while count > 0:
          pst = "text-align: right;"
          t.append("    <div style='{}'>{}</div>".format(pst, self.wb[i]))
          i += 1
          count -= 1
        continue

      if self.wb[i] == "":
        if cpvs == 0:
          t.append("    </div>")
          t.append("    <div class='group'>")
        else:
          cpvs += 1
      else:
        # need to calculate leading space for this line.
        # there may be some tags *before* the leading space
        tmp = self.wb[i][:]
        ss = ""
        m = re.match(r"^<[^>]+>", tmp)
        while m:
          ss += m.group(0)
          tmp = re.sub(r"^<[^>]+>", "", tmp)
          m = re.match(r"^<[^>]+>", tmp)
        leadsp = len(tmp) - len(tmp.lstrip()) 
        if cpvs > 0:
          spvs = " style='margin-top:{}em' ".format(cpvs)
        else:      
          spvs = ""
        if leadsp > 0:
          # create an indent class
          iclass = "in{}".format(leadsp)
          iamt = str(-3 + leadsp/2) # calculate based on -3 base
          self.css.addcss("[227] .linegroup .{} {{ text-indent: {}em; }}".format(iclass, iamt))
          t.append("      <div class='line {0}' {1}>{2}</div>".format(iclass, spvs, ss+tmp.lstrip()))
          printable_lines_in_block += 1
        else:
          t.append("      <div class='line' {0}>{1}</div>".format(spvs, ss+tmp))
          printable_lines_in_block += 1          
        cpvs = 0  # reset pending vertical space
      i += 1
      
    # at block end.
    if printable_lines_in_block == 0:
        self.fatal("empty .nf block")

    # there may be a pending mt at the block end.
    if cpvs > 0:
      t[-1] = re.sub(r"<div", "<div style='margin-bottom:{}em'".format(cpvs), t[-1])
      cpvs = 0          

    t.append("    </div>")
    t.append("  </div>")
    t.append("</div>")
    t.append("")
    endloc = i
    self.wb[startloc:endloc+1] = t
    self.cl = startloc + len(t)

  # .nf no-fill blocks, all types
  def doNf(self):
    m = re.match(r"\.nf (.)", self.wb[self.cl])
    if m:
      nftype = m.group(1) # c, l, b or r
      margin_override = False
      if re.match(r"\.nf . 0", self.wb[self.cl]):
        margin_override = True # ignored in text
      if nftype == 'c':
        self.doNfc(margin_override)
      if nftype in ['l','r','b']:
        self.doNfb(nftype, margin_override)

  # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

  # .fm footnote mark
  def doFmark(self):
    self.wb[self.cl] = "<hr style='border:none; border-bottom:1px solid; width:10%; margin-left:0; margin-top:1em; text-align:left;' />"
    self.cl += 1

  # .fn footnote
  # here on footnote start or end
  # handle completely different for paragraph indent or block style
  def doFnote(self):

    self.css.addcss("[199] sup { vertical-align: top; font-size: 0.6em; }")

    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - 
    if self.pindent: # indented paragraphs
    
      m = re.match(r"\.fn-", self.wb[self.cl])
      if m: # footnote ends
        self.wb[self.cl] = "</div>"
        self.cl += 1
        return
    
      m = re.match(r"\.fn (\d+)", self.wb[self.cl]) # expect numeric footnote
      if m: # footnote start
        self.css.addcss("[430] div.footnote {}")    
        self.css.addcss("[431] div.footnote>:first-child { margin-top:1em; }")
        self.css.addcss("[432] div.footnote p { text-indent:1em;margin-top:0.0em;margin-bottom:0; }")
        fnname = m.group(1)
        self.wb[self.cl] = "<div class='footnote' id='f{}'>".format(fnname)
        self.cl += 1
        # self.wb[self.cl] = "<a href='#r{0}'>[{0}]</a> {1}".format(fnname, self.wb[self.cl])
        self.wb[self.cl] = "<a href='#r{0}'>{0}</a>. {1}".format(fnname, self.wb[self.cl])
        return
      else: # non-numeric footnote
        self.fatal("non-numeric footnote: {}".format(self.wb[self.cl]))

    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -       
    if not self.pindent: # block paragraphs
        m = re.match(r"\.fn-", self.wb[self.cl])
        if m: # footnote ends
          self.wb[self.cl] = "</div>"
          self.cl += 1
          return

        m = re.match(r"\.fn (\d+)", self.wb[self.cl]) # expect numeric footnote
        if m: # footnote start       
          self.css.addcss("[430] div.footnote {margin-left: 2.5em; }")
          self.css.addcss("[431] div.footnote>:first-child { margin-top:1em; }")
          self.css.addcss("[432] div.footnote .label { display: inline-block; width: 0em; text-indent: -2.5em; text-align: right;}")            
          fnname = m.group(1)
          self.wb[self.cl] = "<div class='footnote' id='f{}'>".format(fnname)
          s = "<span class='label'><a href='#r{0}'>{0}</a>.&nbsp;&nbsp;</span>".format(fnname)
          self.cl += 1
          self.wb[self.cl] = s + self.wb[self.cl]
          return
        else: # non-numeric footnote
         self.fatal("non-numeric footnote: {}".format(self.wb[self.cl]))    

  # tables .ta r:5 l:20 r:5 or .ta rlr
  #
  # tables in HTML and derivatives use percent for geometry.
  # column widths specified in characters with 72 page width max.
  # left margin calculated and applied for epub.
  #
  # s=  summary
  # o=  options. only one implemented: "wide" for unrestricted width table

  def doTable(self): # HTML

    # get maximum width of specified column by scanning all rows in table
    def getMaxWidth(c, ncols):
      j = self.cl + 1
      maxw = 0
      while self.wb[j] != ".ta-":
        # blank and centerd lines are not considered
        if self.wb[j] == "" or not "|" in self.wb[j]:
          j += 1
          continue
        u = self.wb[j].split("|")
        if len(u) != ncols:
            self.fatal("table has wrong number of columns:\n{}".format(self.wb[j]))
        t = re.sub(r"<.*?>", "", u[c].strip())  # adjust column width for inline tags
        maxw = max(maxw, len(t))
        j += 1
      return maxw

    haligns = list() # 'l', 'r', or 'c'  no default; must specify
    valigns = list() # 't', 'b', or 'm' default 't'
    widths = list() # column widths
    totalwidth = 0

    # look for continuation characters; restore to one line
    k1 = self.cl
    while self.wb[k1] != ".ta-":        
      while "\\" in self.wb[k1]:
        self.wb[k1] = re.sub(r"\\", "", self.wb[k1])
        self.wb[k1] = self.wb[k1] + " " + self.wb[k1+1]
        del self.wb[k1+1]
      k1 += 1
      
    # pull out summary if present.
    tsum = ""
    if "s=" in self.wb[self.cl]:
      self.wb[self.cl], tsum = self.get_id("s", self.wb[self.cl])
    
    # pull out options if present.
    topt = ""
    if "o=" in self.wb[self.cl]:
      self.wb[self.cl], topt = self.get_id("o", self.wb[self.cl])
    
    # tables forms:
    # .ta r:5 l:20 l:5  => use specified width and wrap if necessary
    # .ta rll  => calculate width of columns, no wrap
    # .ta r:5 l:20 lb:5  => use specified width and wrap if necessary,
    #    floating third column to bottom
    
    # if auto-width, replace the .ta line with widths specified
    # if any widths are specified, all must be specified
    # .ta lr => .ta l:6 r:22
    autosize = False
    if not ":" in self.wb[self.cl]:
      autosize = True
      m = re.match(r"\.ta ([lcr]+)", self.wb[self.cl])
      if m:
        t0 = m.group(1) # all the specifiers
        t = list(t0) # ex: ['r','c','l']
        ncols = len(t) # ex: 3
        s = ".ta "
        for i,x in enumerate(t):
          cwidth = getMaxWidth(i,ncols) # width
          s += "{}t:{} ".format(t0[i],cwidth)
        self.wb[self.cl] = s.strip()  # replace with widths specified
    
    # if vertical alignment not specified, default to "top" now
    # .ta l:6 r:22 => .ta lt:6 rt:22    
    while re.search(r"[^lcr][lcr]:", self.wb[self.cl]):
      self.wb[self.cl] = re.sub(r"([lcr]):", r'\1t:', self.wb[self.cl])
          
    t = self.wb[self.cl].split() # ['.ta', 'lt:6', 'rt:22']
    ncols = len(t) - 1  # skip the .ta piece
    
    # alignment
    j = 1
    while j <= ncols:
      u = t[j].split(':')

      if not u[0][0] in ['l','c','r']:
        self.fatal("table horizontal alignment must be 'l', 'c', or 'r' in {}".format(self.wb[self.cl]))
      if u[0][0] == 'l':
        haligns.append("text-align:left;")
      if u[0][0] == 'c':
        haligns.append("text-align:center;")
      if u[0][0] == 'r':
        haligns.append("text-align:right;")

      if not u[0][1] in ['t','m','b']:
        self.fatal("table vertial alignment must be 't', 'm', or 'b'")
      if u[0][1] == 't':
        valigns.append("vertical-align:top;")
      if u[0][1] == 'm':
        valigns.append("vertical-align:middle;")
      if u[0][1] == 'b':
        valigns.append("vertical-align:bottom;")

      widths.append(int(u[1]))
      totalwidth += int(u[1]) # no added space in HTML
      j += 1
    totalwidth -= 1    

    pwidths = [None] * ncols
    # convert character widths to percentages for HTML
    tablewidth = int(100*(totalwidth / 72))
    pctused = 0
    for (i,w) in enumerate(widths):
      t0 = int(100*(widths[i]/totalwidth))
      t1 = 100 - pctused
      pwidths[i] = min(t0,t1)  # don't go over 100%
      pctused += pwidths[i]
    lmarpct = int((100 - tablewidth) / 2)

    # at this point:
    # haligns = ['text-align:right;', 'text-align:left;', 'text-align:right;']
    # valigns = ['vertical-align:top;', 'vertical-align:top;', 'vertical-align:bottom;']
    # pwidths = [9, 83, 8]  relative percentages (add to 100%)
    # tablewidth = 58  percentage of page width used by table
    # lmarpct = 21  left margin percent. (2 * lmarpct + tablewidth = 100)
    # totalwidth = width of table in characters

    # unwrap any user-wrapped text in table
    k1 = self.cl + 1
    while self.wb[k1] != ".ta-":    
      while "\\" in self.wb[k1]:
        self.wb[k1] = re.sub(r"\\", "", self.wb[k1])
        self.wb[k1] = self.wb[k1] + " " + self.wb[k1+1]
        del self.wb[k1+1]
      k1 += 1    

    t = []

    # self.tcnt has table counter so each table can have a unique class
    # thisclass_html = 'margin-left:auto; margin-right:auto; width:{}%'.format(tablewidth)
    # self.css.addcss("[520] .tablet{0:02d} {{".format(self.tcnt) + thisclass_html + "}")
    # thisclass_tablet = 'margin-left:{0}%; margin-right:{0}%; width:{1}%'.format(lmarpct,tablewidth)
    # self.css.addcss("[521] @media handheld {{ .tablet{0:02d} {{".format(self.tcnt) + thisclass_tablet + "} }")
    # t.append("<table class='tablet{:02d}'>".format(self.tcnt))

    # if tsum != "":
    #   tsum = re.sub("'", "\\'", tsum)
    # sty = "margin-left: {}%; width:{}%; ".format(lmarpct, tablewidth)
    # if self.pvs > 0:
    #   sty += "margin-top: {}em".format(self.pvs)
    #   self.pvs=0
    # t.append("<table style='{}' summary='{}'>".format(sty, tsum))

    sty = "margin: auto; "
    if not "wide" in topt:
      φ = (1 + sqrt(5))/2.0 # tribute Nigel
      sty += "max-width:{}em; ".format("%.2f" % (totalwidth/φ))
    if self.pvs > 0:  # pending vertical space
      sty += "margin-top: {}em".format(self.pvs)
      self.pvs=0
    t.append("<table style='{}' summary='{}'>".format(sty, tsum))   
    
    # set relative widths of columns
    t.append("<colgroup>")
    for (i,w) in enumerate(widths):
     t.append("<col width='{}%'/>".format(pwidths[i]))
    t.append("</colgroup>")       

    startloc = self.cl
    self.cl += 1 # move into the table rows
    while self.wb[self.cl] != ".ta-":

      # see if blank line
      if "" == self.wb[self.cl]:
        t.append("  <tr><td>&nbsp;</td></tr>")
        self.cl += 1
        continue

      # see if centered line
      if not "|" in self.wb[self.cl]:
        t.append("  <tr><td style='text-align:center' colspan='{}'>{}</td></tr>".format(ncols,self.wb[self.cl]))
        self.cl += 1
        continue

      # if there is a page number here, pull it and save it
      # so leading spaces will work
      # inject it into the data of the first <td> on this line
      savedpage = ""
      m = re.search(r"(⑯.*?⑰)", self.wb[self.cl])
      if m:
        savedpage = m.group(1)
        self.wb[self.cl] = re.sub(m.group(1), "", self.wb[self.cl])

      v = self.wb[self.cl].split('|') #
      t.append("  <tr>")
      # iterate over the td elements
      for k,data in enumerate(v):
        valgn = ""
        padding = ""
                  
        if k < len(v) - 1: # each column not the last gets padding to the right
           padding +='padding-right:1em;'      
        # convert leading spaces to padding
        t1 = v[k]
        t2 = re.sub(r"^ⓢ+","", v[k])
        if len(t1) - len(t2) > 0:
          padleft = (len(t1) - len(t2))*0.7
          padding += 'padding-left:{}em'.format(padleft)
          v[k] = savedpage + t2
        t.append("    <td style='{}{}{}'>".format(valigns[k],haligns[k],padding) + v[k].strip() + "</td>")
      t.append("  </tr>")
      self.cl += 1
    t.append("</table>")
    self.tcnt += 1
    self.wb[startloc:self.cl+1] = t
    self.cl = startloc + len(t)
    
  # Drop Image
  # .di i_b_009.jpg 100 170 1.3
  def doDropimage(self):
    m = re.match(r"\.di (.*?) (\d+) (\d+) (.*)",self.wb[self.cl])
    if m:
      self.warn("CSS3 drop-cap. Please note in upload.")
      d_image = m.group(1)
      d_width = m.group(2)
      d_height = m.group(3)
      d_adj = m.group(4)

      self.css.addcss("[920] img.drop-capi { float:left;margin:0 0.5em 0 0;position:relative;z-index:1; }")
      s_adj = re.sub(r"\.","_", str(d_adj))
      if self.pindent:
        s0 = re.sub("em", "", self.nregs["psi"]) # drop the "em"
        s1 = int(float(s0)*100.0) # in tenths of ems
        s2 = (s1//2)/100 # forces one decimal place
      else:
        s0 = re.sub("em", "", self.nregs["psb"]) # drop the "em"
        s1 = int(float(s0)*100.0) # in tenths of ems
        s2 = (s1//2)/100 # forces one decimal place
      mtop = s2
      mbot = mtop
      self.css.addcss("[921] p.drop-capi{} {{ text-indent:0; margin-top:{}em; margin-bottom:{}em}}".format(s_adj,mtop,mbot))
      self.css.addcss("[922] p.drop-capi{}:first-letter {{ color:transparent; visibility:hidden; margin-left:-{}em; }}".format(s_adj,d_adj))

      self.css.addcss("[923] @media handheld {")
      self.css.addcss("[924]   img.drop-capi { display:none; visibility:hidden; }")
      self.css.addcss("[925]   p.drop-capi{}:first-letter {{ color:inherit; visibility:visible; margin-left:0em; }}".format(s_adj))
      self.css.addcss("[926] }")

      t = []
      t.append("<div>")
      t.append("  <img class='drop-capi' src='images/{}' width='{}' height='{}' alt='' />".format(d_image,d_width,d_height))
      t.append("</div><p class='drop-capi{}'>".format(s_adj))
      self.wb[self.cl:self.cl+1] = t

  # Drop Cap. a single, capital letter
  def doDropcap(self):
    m = re.match(r"\.dc (.*?)\s(.*)", self.wb[self.cl]) # optional adjust
    dcadjs = ""
    dcadj = 0
    if m:
      dcadj = m.group(1)
      dclh = m.group(2)
      dcadjs = "{}_{}".format(dcadj, dclh)
      dcadjs = re.sub(r"\.", "_", dcadjs) # name formatting
    else:
      self.fatal("incorrect format for .dc arg1 arg2 command")
    self.css.addcss("[930] p.drop-capa{0} {{ text-indent:-{1}em; }}".format(dcadjs,dcadj))
    self.css.addcss("[931] p.drop-capa{0}:first-letter {{ float:left;margin:0.1em 0.1em 0em 0em;font-size:250%;line-height:{1}em;text-indent:0 }}".format(dcadjs,dclh))
    self.css.addcss("[933] @media handheld {")
    self.css.addcss("[935]   p.drop-capa{} {{ text-indent:0 }}".format(dcadjs))
    self.css.addcss("[936]   p.drop-capa{}:first-letter {{ float:none;margin:0;font-size:100%; }}".format(dcadjs))
    self.css.addcss("[937] }")
    self.pdc = "drop-capa{}".format(dcadjs)
    del self.wb[self.cl]

  # no adjust
  def doNa(self):
    del self.wb[self.cl]
    self.regAD = 0

  # justification on (default)
  def doAd(self):
    del self.wb[self.cl]
    self.regAD = 1

  # courtesy cleanup of HTML
  # also checks for a single h1 element
  def cleanup(self):
    h1cnt = 0
    for i in range(len(self.wb)):
      self.wb[i] = re.sub("\s+>", ">", self.wb[i])  # spaces before close ">"
      self.wb[i] = re.sub("<p  ", "<p ", self.wb[i])
      # next line broke German, where a space is significant before ">"
      # self.wb[i] = re.sub(" >", ">", self.wb[i])
      self.wb[i] = re.sub("⑦", "#", self.wb[i]) # used in links
      if re.search("<h1", self.wb[i]): # expect to find one h1 in the file
        h1cnt += 1
        
    i = 0
    while not re.search(r"<style type=\"text/css\">", self.wb[i]):
      i += 1
    while not re.search(r"<\/style>", self.wb[i]):
      if len(self.wb[i]) > 90:
        s = self.wb[i]
        splitat = s.rfind(';', 0, 90)
        if splitat > 0:
          s0 = s[:splitat+1]
          s1 = "              " + s[splitat+1:]
          self.wb[i:i+1] = [s0, s1]
      i += 1
    if h1cnt != 1:
      self.warn("exactly one <h1> element is required.")
    
    # puts free-standing pagenumbers into a div
    blvl = 0
    for i in range(len(self.wb)):
      if "<div" in self.wb[i]: blvl += 1
      if "<p" in self.wb[i]: blvl += 1
      if "</div" in self.wb[i]: blvl -= 1
      if "</p" in self.wb[i]: blvl -= 1
      # if blvl == 0 and re.match(r"<span class='pagenum'.*?<\/span>$", self.wb[i]):
      if blvl == 0 and re.match(r"<span class='pageno'.*?<\/span>$", self.wb[i]):      # new 3.24M
        self.wb[i] = "<div>{}</div>".format(self.wb[i])

  # called to retrieve a style string representing current display parameters
  #
  def fetchStyle(self):
    s = ""
    if self.regIN != 0:
      inpct = (self.regIN * 100)/72
      s += "margin-left:{:3.2f}%;".format(inpct)
    if self.regLL != 72:
      llpct = ((72 - self.regLL) * 100)/72
      s += "margin-right:{:3.2f}%;".format(llpct)
    if self.regTI == -1000: # special force of ti=0
      s += "text-indent:0;"
    else: # a possible regular indent
      if self.regTI != 0:
        tipct = (self.regTI * 100)/72
        s += "text-indent:{:3.2f}%;".format(tipct)
    # there may be a pending vertical space.
    if self.pvs > 0:
      s += "margin-top:{}em;".format(self.pvs)
      self.pvs = 0
    if self.fsz != "100%" and self.fsz != "1.0em":
      s += "font-size:{};".format(self.fsz)
    if self.regAD == 0:
      s += "text-align:left;"
    return s

  def doPi(self):
    self.pindent = True
    del self.wb[self.cl]

  def doNi(self):
    self.pindent = False
    del self.wb[self.cl]

  # 03-Apr-2014 .rj or .rj 3, etc. for HTML
  def doRj(self):
    m = re.match(r"\.rj (\d+)", self.wb[self.cl]) # number of lines specified
    if m:
      del self.wb[self.cl]
      nlines = int(m.group(1))
      while nlines > 0:
        s = self.fetchStyle() # style line with current parameters
        rstyle = s + "text-align:right;"
        self.pvs = 0  # if there is a pending vertial space, only use it once on first line
        self.wb[self.cl] = "<div style='{}'>{}</div>".format(rstyle, self.wb[self.cl])
        self.cl += 1
        nlines -= 1
    else:
      self.warn("malformed .rj directive: {}".format(self.wb[i]))

  def doPara(self):
    s = self.fetchStyle() # style line with current parameters

    # if there is a pending drop cap, don't indent
    # if there is a text-indent already, don't change it
    # otherwise, add a text-indent if self.pindent is set.
    if self.pdc == ""  and self.pindent and 'text-indent' not in s:
      s += 'text-indent:1em;'

    # apply either "psi" or "psb" spacing
    if self.pindent:
      # unless there is a margin already set, set top margin
      if "margin-top" not in s:
        # psi represents the entire gap. split it
        s0 = re.sub("em", "", self.nregs["psi"]) # drop the "em"
        s1 = int(float(s0)*100.0) # in tenths of ems
        s2 = (s1//2)/100 # forces one decimal place
        s += 'margin-top:{}em;'.format(s2)
      if "margin-bottom" not in s:
        # psi represents the entire gap. split it
        s0 = re.sub("em", "", self.nregs["psi"]) # drop the "em"
        s1 = int(float(s0)*100.0) # in tenths of ems
        s2 = (s1//2)/100 # forces one decimal place
        s += 'margin-bottom:{}em;'.format(s2)
    else: # not indented, use "psb" spacing
      # unless there is a margin already set, set top margin
      if "margin-top" not in s:
        # psb represents the entire gap. split it
        s0 = re.sub("em", "", self.nregs["psb"]) # drop the "em"
        s1 = int(float(s0)*100.0) # in tenths of ems
        s2 = (s1//2)/100 # forces one decimal place
        s += 'margin-top:{}em;'.format(s2)
      if "margin-bottom" not in s:
        # psb represents the entire gap. split it
        s0 = re.sub("em", "", self.nregs["psb"]) # drop the "em"
        s1 = int(float(s0)*100.0) # in tenths of ems
        s2 = (s1//2)/100 # forces one decimal place
        s += 'margin-bottom:{}em;'.format(s2)

    s_str = "" # empty style string
    if s != "":
      s_str = " style='{}' ".format(s)

    c_str = "" # empty class string
    if self.pdc != "":
      c_str = " class='{}' ".format(self.pdc) # only for drop cap
      self.pdc = ""

    if re.match("<div>", self.wb[self.cl]):
      # if this is a div, such as for a drop cap, apply the pending style to the div
      self.wb[self.cl] = "<div {}{}>".format(c_str,s_str) + self.wb[self.cl][5:] # ouch
    else:
      # it's a normal paragraph
      self.wb[self.cl] = "<p {}{}>".format(c_str,s_str) + self.wb[self.cl]

    while ( self.cl < len(self.wb) \
       # any blank line in source ends paragraph
       and self.wb[self.cl] \
       and self.wb[self.cl][0] != "." ): # any dot command in source ends paragraph
      self.cl += 1
    self.wb[self.cl-1] = self.wb[self.cl-1] + "</p>"

    self.regTI = 0 # any temporary indent has been used.

  def doChecks(self):
    rb = [] # report buffer
    links = {} # map of links
    targets = {} # map of targets
    # build links
    for i,line in enumerate(self.wb):
      m = re.search(r"href=[\"']#(.*?)[\"']", line)
      if m:
        t = m.group(1)
        if t in links:
          if not "Page" in t:
            rb.append("duplicate link: {}".format(t))
        else:
          links[t] = 1
    # rb.append("{} links".format(len(links)))

    # build targets
    for i,line in enumerate(self.wb):

      m = re.search(r"id=[\"'](.+?)[\"']", line)
      while m:
        t = m.group(1)
        if t in targets:
          rb.append("ERROR duplicate target: {}".format(t))
        else:
          targets[t] = 1
        line = re.sub(r"id=[\"'](.+?)[\"']","",line,1)
        m = re.search(r"id=[\"'](.+?)[\"']", line)

    # rb.append("{} targets".format(len(targets)))

    # match links to targets
    misscount = 0
    for key in links:
      if key not in targets:
        misscount += 1
        rb.append("Error: missing target: {}".format(key))

    # for key in targets:
    #  if key not in links:
    #    if not "Page" in key:
    #      rb.append("warning: {} unused".format(key))

    if misscount > 0:
      self.warn("missing link target(s):")
      for w in rb:
        print(w)

  def process(self):
    self.cl = 0
    while self.cl < len(self.wb):
      if "a" in self.debug:
        print(self.wb[self.cl])
      if not self.wb[self.cl]: # skip blank lines
        self.cl += 1
        continue
      # will hit either a dot directive or wrappable text
      if re.match(r"\.", self.wb[self.cl]):
        self.doDot()
      else:
        self.doPara()

  def makeHTML(self):
    self.doHeader()
    self.doFooter()
    self.placeCSS()
    self.cleanup()

  def run(self): # HTML
    self.loadFile(self.srcfile)
    self.preprocess()
    self.process()
    self.postprocess()
    self.deStyle()
    self.makeHTML()
    self.doChecks()
    self.saveFile(self.dstfile)

# ====== ppgen ==========================================================================

# python3 ppgen.py -i secret-src.txt       generates secret.txt, secret.html
# python3 ppgen.py -i secret-src.txt -o t  generates secret.txt only
# python3 ppgen.py -i secret-src.txt -o h  generates secret.html only
# source file must be filename-src.txt, UTF-8.
#
# debug options:
# 'd' enables dprint, 's' retains runtime-generated styles,
# 'a' shows lines as they are processed, 'p' shows architecture

def main():
  # process command line
  parser = argparse.ArgumentParser(description='ppgen generator')
  parser.add_argument('-i', '--infile', help='UTF-8 or Latin-1 input file')
  parser.add_argument('-l', '--log', help="display Latin-1 conversion log", action="store_true")
  parser.add_argument('-d', '--debug', nargs='?', default="", help='debug flags (d,s,a,p)')
  parser.add_argument('-o', '--output_format', default="ht", help='output format "h":HTML "t":text')
  parser.add_argument('-a', '--anonymous', action='store_true', help='do not identify version/timestamp in HTML')
  parser.add_argument("-v", "--version", help="display version and exit", action="store_true")
  args = parser.parse_args()

  # version request. print and exit
  if args.version:
    print("{}".format(VERSION))
    exit(1)

  print("ppgen {}".format(VERSION))

  if 'p' in args.debug:
    print("running on {}".format(platform.system()))

  # infile of mystery-src.txt will generate mystery.txt and mystery.html

  if args.infile == None or not args.infile:
    print("infile must be specified. use \"--help\" for help")
    exit(1)

  if 't' in args.output_format:
    ppt = Ppt(args, "u")
    ppt.run()
    ppt = Ppt(args, "l")
    ppt.run()

  # utf-8 only
  if 'u' in args.output_format:
    ppt = Ppt(args, "u")
    ppt.run()
    
  # Latin-1 only
  # if 'l' in args.output_format:
  #   ppt = Ppt(args, "l")
  #   ppt.run()    

  if 'h' in args.output_format:
    print("creating HTML version")
    pph = Pph(args, "h")
    pph.run()

if __name__ == '__main__':
    main()
