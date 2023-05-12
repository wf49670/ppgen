#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import locale
locale.setlocale(category=locale.LC_ALL, locale="en_US.utf-8") # RT correct invalid locale was en_EN.utf-8

# Note: ppgen uses a number of unicode characters as markers and placeholders to avoid
# interference from or iterfering with PPer-provided text. They are listed at the end of this file,
# before the css keys.
#
# Note: ppgen generates css using a numeric key to ensure that the css statements come out in the
# proper order in the HTML. They are listed at the end of this file, after the unicode characters.

import argparse
from time import gmtime, strftime
try:
  import regex as re
  re.DEFAULT_VERSION = re.VERSION0
  with_regex = " (with regex)"
except:
  import re
  with_regex = ""
#import re
#with_regex = ""
import sys, string, os, platform
import configparser
import textwrap
import codecs
import unicodedata
from collections import defaultdict
import shlex
import random, inspect
from math import sqrt
import struct
import imghdr
import traceback

VERSION="3.57d_GHS_H5" + with_regex   # 03-Mar-2023
#3.57a:
#  Initial 3.57 release
#  Enh: Provide context for "Unclosed tags in .nf block" error
#  Enh: Warn if user has extraneous info on a .h<n> directive.
#  Bug: Properly handle "break" operand on .h4/5/6 directives.
#  Enh: Warn if user apparently has a dot directive immediately following a .h<n> directive
#  Enh: Adjust index-related CSS to better distinguish subentries from overflow/wrapped entries.
#  Bug: Change page number processing to allow for continued .hn or .il statements, as the rest of
#         continuation processing happens after we handle page numbers.
#  Enh: Revise <pm ...> processing to use non-greedy matching to more reliably handle cases where the PPer has
#         included multiple macro invocations on the same source line. (No known problems reported with the
#         old code, though.)
#3.57b:
#  Bug: HTML: Inline tags within an all upper-case <sc> string cause the wrong CSS class to be generated.
#3.57c:
#  Bug: Fix Python trap during execution introduced by 3.57a while checking continued .h<n> and .il directives.
#3.57d:
#  Enh: Updated HTML processing to HTML5.

###  Todo Bug: In HTML, a .sp placed before a .il does not take effect until the next text after the illustration/caption.

NOW = strftime("%Y-%m-%d %H:%M:%S", gmtime()) + " GMT"


"""
  ppgen.py

  Copyright 2014, 2016 Asylum Computer Services LLC
  Licensed under the MIT license:
  http://www.opensource.org/licenses/mit-license.php

  Roger Frank (rfrank@rfrank.net)
  Walt Farrell (walt.farrell@gmail.com)
  Rick Tonsing (okrick@gmail.com) minor HTML5 updates only
  
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

# ====== Book, parent of Ppt (text) and Pph (HTML) classes ==========================================

class Book(object):

  python_macros_allowed = None

  wb = [] # working buffer
  eb = [] # emit buffer
  bb = [] # GG .bin file buffer
  gk_user = [] # PPer-supplied Greek characters
  diacritics_user = [] # PPer-supplied diacritic characters
  srw = []    # .sr "which" array
  srs = []    # .sr "search" array
  srr = []    # .sr "replace" array
  fnlist = [] # buffer for saved footnotes
  regLL = 72 # line length
  regIN = 0 # indent
  regTI = 0 # temporary indent
  regTIp = 0 # persistent temporary indent
  regAD = 1 # 1 if justified, 0 if ragged right
  latin1only = False

  instack = [] # last indent level
  llstack = [] # last line length
  psstack = [] # last para spacing
  nfstack = [] # block stack
  dvstack = [] # stack for nested .dv blocks
  fsstack = [] # stack for .fs push
  fn_pvs_stack = [] # stack for HTML .fn processing to save pvs value
  blkfszstack = [] # stack for font-sizes across footnotes, divs, and lists
  liststack = [] # ul/ol stack
  list_type = None   # no list in progress
  list_item_style = ''  # no item marker for unordered lists yet
  list_item_value = 0   # no item marker value for ordered lists yet
  list_item_width = 0   # no item marker value width for ordered lists yet
  list_space = False
  prev_width = 0        # no previous width yet for lists
  outerwidth = 0
  outerstyle = ''
  outertype = ''
  outerregIN = 0
  list_hang = False
  list_align = ''
  list_item_active = False # no list item active
  dotcmdstack = [] # stack for valid dotcmds
  warnings = [] # warnings displayed
  cl = 0 # current line number
  pindent = False
  pnshow = False # set to True if page numbering found in source file
  pnlink = False # create links but do not show page number
  csslc = 3000 # CSS line counter for user defined classes
  dtitle = "" # display title for HTML
  cimage = "cover.jpg" # default cover image
  bnPresent = False

  nregs = {} # named registers
  nregsusage = {} # usage counters for selected named registers
  macro = {} # user macro storage
  caption_model = {} # storage for named caption models for multi-line captions in text output

  imageDict = {} # dictionary to track used/unused image files

  mau = [] # UTF-8
  mal = [] # user-defined Latin-1

  linelimitwarning = 75  # code changes needed if < 60!

  #  text table horizontal rule dictionary
  #  key is left, up, down, right with * for any undefined positions
  hrule_text_dict = {
  #
  '*││─':'├', '*│*─':'└', '**│─':'┌', # rules with box drawings light vertical, light horizontal
  #
  '─││─':'┼', '─│*─':'┴', '─*│─':'┬',
  #
  '─││*':'┤', '─│**':'┘', '─*│*':'┐',
  #
  '*┃┃━':'┣', '*┃*━':'┗', '**┃━':'┏', # rules with box drawings heavy vertical, heavy horizontal
  #
  '━┃┃━':'╋', '━┃*━':'┻', '━*┃━':'┳',
  #
  '━┃┃*':'┫', '━┃**':'┛', '━*┃*':'┓',
  #
  '*││═':'╞', '*│*═':'╘', '**│═':'╒', # rules with box drawings light vertical, double horizontal
  #
  '═││═':'╪', '═│*═':'╧', '═*│═':'╤',
  #
  '═││*':'╡', '═│**':'╛', '═*│*':'╕',
  #
  '*││━':'┝', '*│*━':'\u2515', '**│━':'\u250d', # rules with box drawings light vertical, heavy horizontal
  #
  '━││━':'┿', '━│*━':'┷', '━*│━':'┯',
  #
  '━││*':'┥', '━│**':'\u2519', '━*│*':'\u2511',
  #
  '*┃┃─':'┠', '*┃*─':'\u2516', '**┃─':'\u250e', # rules with box drawings heavy vertical, light horizontal
  #
  '─┃┃─':'╂', '─┃*─':'┸', '─*┃─':'┰',
  #
  '─┃┃*':'┨', '─┃**':'\u251a', '─*┃*':'\u2512',
  #
  '*┃┃═':'╞', '*┃*═':'╘', '**┃═':'╒', # don't have down heavy, double horizontal, so same as light/light
  #
  '═┃┃═':'╪', '═┃*═':'╧', '═*┃═':'╤',
  #
  '═┃┃*':'╡', '═┃**':'╛', '═*┃*':'╕',
  #
  '*║║─':'╟', '*║*─':'╟', '**║─':'╓',
  #
  '─║║─':'╫', '─║*─':'╨', '─*║─':'╥',
  #
  '─║║*':'╢', '─║**':'╜', '─*║*':'╖',
  #
  '*║║═':'╠', '*║*═':'╚', '**║═':'╔',
  #
  '═║║═':'╬', '═║*═':'╩', '═*║═':'╦',
  #
  '═║║*':'╣', '═║**':'╝', '═*║*':'╗',
  #
  }

  valid_text_hrules = {
    '_':'─',  # single underscore = box drawings light horizontal
    #'__':'━', # double underscore = box drawings heavy horizontal
    '__':'─', # double underscore = box drawings light horizontal (heavy horizontal is wrong width)
    '=':'═',  # single equal sign = box drawings double horizontal
    '==':'═', # double equal sign = box drawings double horizontal (text) or heavier one (html)
    }


  valid_html_hrules = {
    '_':['t', 'btb_'], # thin
    '__':['m', 'btb__'], # medium
    '=':['td', 'btb='], # medium double
    '==':['md', 'btb=='], # medium double
    }


  valid_html_vrules = {
    '|':['t', 'blr|'], # thin
    '||':['m', 'blr||'], # medium
    '=':['td', 'blr='], # medium double
    '==':['md', 'blr=='], # medium double
    }

  html_border_names = {
    'bt':'{ border-top: ',
    'bb':'{ border-bottom: ',
    'bl':'{ border-left: ',
    'br':'{ border-right: ',
    }

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

  # Format of Greek Transliterations:
  # 1. character(s) the user enters
  # 2. character(s) ppgen outputs
  # 3. printable form for .cvglist output listing
  gk = [                              # builtin Greek transliterations

     ('ï/', 'i/+', 'ï/', None, 'ΐ (i/+ is the preferred form)'), # i/u/y alternatives using dieresis
     ('ü/', 'y/+', 'ü/', None, 'ΰ (y/+ is preferred)'), # standardize to doubly marked form and fall into normal processing
     ('ÿ/', 'y/+', 'ÿ/', None, 'ΰ (y/+ is preferred)'),
     ('ï~', 'i~+', 'ï~', None, 'ῗ (i~+ is preferred)'),
     ('ü~', 'y~+', 'ü~', None, 'ῧ (y~+ is preferred)'),
     ('ÿ~', 'y~+', 'ÿ~', None, 'ῧ (y~+ is preferred)'),
     (r'ï\\', 'i\+', 'ï\\', None, 'ῒ (i\+ is preferred)'),
     (r'ü\\', 'y\+', 'ü\\', None, 'ῢ (y\+ is preferred)'),
     (r'ÿ\\', 'y\+', 'ÿ\\', None, 'ῢ (y\+ is preferred)'),
     ('Ï', '\u03AA', 'Ï'),           # just put these directly to the character (because that's the way Tony did it for GG)
     ('ï', '\u03CA', 'ï'),
     ('Ü', '\u03AB', 'Ü'),
     ('ü', '\u03CB', 'ü'),
     ('ÿ', '\u03CB', 'ÿ'),
     (r'a\)\\\|', '\u1F82', 'a)\\|'), # Triply marked letters
     (r'a\(\\\|', '\u1F83', 'a(\\|'),
     ('a\)/\|',   '\u1F84', 'a)/|'),
     ('a\(/\|',   '\u1F85', 'a(/|'),
     ('a~\)\|',   '\u1F86', 'a~)|'),
     ('a~\(\|',   '\u1F87', 'a~(|'),
     (r'A\)\\\|', '\u1F8A', 'A)\\|'),
     (r'A\(\\\|', '\u1F8B', 'A(\\|'),
     ('A\)/\|',   '\u1F8C', 'A)/|'),
     ('A\(/\|',   '\u1F8D', 'A(/|'),
     ('A~\)\|',   '\u1F8E', 'A~)|'),
     ('A~\(\|',   '\u1F8F', 'A~(|'),
     (r'ê\)\\\|', '\u1F92', 'ê)\\|'),
     (r'ê\(\\\|', '\u1F93', 'ê(\\|'),
     (r'ê\)/\|',  '\u1F94', 'ê)/|'),
     (r'ê\(/\|',  '\u1F95', 'ê(/|'),
     ('ê~\)\|',   '\u1F96', 'ê~)|'),
     ('ê~\(\|',   '\u1F97', 'ê~(|'),
     (r'Ê\)\\\|', '\u1F9A', 'Ê)\\|'),
     (r'Ê\(\\\|', '\u1F9B', 'Ê(\\|'),
     ('Ê\)/\|',   '\u1F9C', 'Ê)/|'),
     ('Ê\(/\|',   '\u1F9D', 'Ê(/|'),
     ('Ê~\)\|',   '\u1F9E', 'Ê~)|'),
     ('Ê~\(\|',   '\u1F9F', 'Ê~(|'),
     (r'ô\)\\\|', '\u1FA2', 'ô)\\|'),
     (r'ô\(\\\|', '\u1FA3', 'ô(\\|'),
     ('ô\)/\|',   '\u1FA4', 'ô)/|'),
     ('ô\(/\|',   '\u1FA5', 'ô(/|'),
     ('ô~\)\|',   '\u1FA6', 'ô~)|'),
     ('ô~\(\|',   '\u1FA7', 'ô~(|'),
     (r'Ô\)\\\|', '\u1FAA', 'Ô)\\|'),
     (r'Ô\(\\\|', '\u1FAB', 'Ô(\\|'),
     ('Ô\)/\|',   '\u1FAC', 'Ô)/|'),
     ('Ô\(/\|',   '\u1FAD', 'Ô(/|'),
     ('Ô~\)\|',   '\u1FAE', 'Ô~)|'),
     ('Ô~\(\|',   '\u1FAF', 'Ô~(|'),
     (r'a\)\\',   '\u1F02', 'a)\\'),  # Doubly marked letters
     (r'a\(\\',   '\u1F03', 'a(\\'),
     ('a\)/',     '\u1F04', 'a)/'),
     ('a\(/',     '\u1F05', 'a(/'),
     ('a~\)',     '\u1F06', 'a~)'),
     ('a~\(',     '\u1F07', 'a~('),
     (r'A\)\\',   '\u1F0A', 'A)\\'),
     (r'A\(\\',   '\u1F0B', 'A(\\'),
     ('A\)/',     '\u1F0C', 'A)/'),
     ('A\(/',     '\u1F0D', 'A(/'),
     ('A~\)',     '\u1F0E', 'A~)'),
     ('A~\(',     '\u1F0F', 'A~('),
     (r'e\)\\',   '\u1F12', 'e)\\'),
     (r'e\(\\',   '\u1F13', 'e(\\'),
     ('e\)/',     '\u1F14', 'e)/'),
     ('e\(/',     '\u1F15', 'e(/'),
     (r'E\)\\',   '\u1F1A', 'E)\\'),
     (r'E\(\\',   '\u1F1B', 'E(\\'),
     ('E\)/',     '\u1F1C', 'E)/'),
     ('E\(/',     '\u1F1D', 'E(/'),
     (r'ê\)\\',   '\u1F22', 'ê)\\'),
     (r'ê\(\\',   '\u1F23', 'ê(\\'),
     ('ê\)/',     '\u1F24', 'ê)/'),
     ('ê\(/',     '\u1F25', 'ê(/'),
     ('ê~\)',     '\u1F26', 'ê~)'),
     ('ê~\(',     '\u1F27', 'ê~('),
     (r'Ê\)\\',   '\u1F2A', 'Ê)\\'),
     (r'Ê\(\\',   '\u1F2B', 'Ê(\\'),
     ('Ê\)/',     '\u1F2C', 'Ê)/'),
     ('Ê\(/',     '\u1F2D', 'Ê(/'),
     ('Ê~\)',     '\u1F2E', 'Ê~)'),
     ('Ê~\(',     '\u1F2F', 'Ê~('),
     (r'i\)\\',   '\u1F32', 'i)\\'),
     (r'i\(\\',   '\u1F33', 'i(\\'),
     ('i\)/',     '\u1F34', 'i)/'),
     ('i\(/',     '\u1F35', 'i(/'),
     ('i~\)',     '\u1F36', 'i~)'),
     ('i~\(',     '\u1F37', 'i~('),
     (r'I\)\\',   '\u1F3A', 'I)\\'),
     (r'I\(\\',   '\u1F3B', 'I(\\'),
     ('I\)/',     '\u1F3C', 'I)/'),
     ('I\(/',     '\u1F3D', 'I(/'),
     ('I~\)',     '\u1F3E', 'I~)'),
     ('I~\(',     '\u1F3F', 'I~('),
     (r'o\)\\',   '\u1F42', 'o)\\'),
     (r'o\(\\',   '\u1F43', 'o(\\'),
     ('o\)/',     '\u1F44', 'o)/'),
     ('o\(/',     '\u1F45', 'o(/'),
     (r'O\)\\',   '\u1F4A', 'O)\\'),
     (r'O\(\\',   '\u1F4B', 'O(\\'),
     ('O\)/',     '\u1F4C', 'O)/'),
     ('O\(/',     '\u1F4D', 'O(/'),
     (r'y\)\\',   '\u1F52', 'y)\\'),
     (r'y\(\\',   '\u1F53', 'y(\\'),
     ('y\)/',     '\u1F54', 'y)/'),
     ('y\(/',     '\u1F55', 'y(/'),
     ('y~\)',     '\u1F56', 'y~)'),
     ('y~\(',     '\u1F57', 'y~('),
     (r'Y\(\\',   '\u1F5B', 'Y(\\'),
     ('Y\(/',     '\u1F5D', 'Y(/'),
     ('Y~\(',     '\u1F5F', 'Y~('),
     (r'ô\)\\',   '\u1F62', 'ô)\\'),
     (r'ô\(\\',   '\u1F63', 'ô(\\'),
     ('ô\)/',     '\u1F64', 'ô)/'),
     ('ô\(/',     '\u1F65', 'ô(/'),
     ('ô~\)',     '\u1F66', 'ô~)'),
     ('ô~\(',     '\u1F67', 'ô~('),
     (r'Ô\)\\',   '\u1F6A', 'Ô)\\'),
     (r'Ô\(\\',   '\u1F6B', 'Ô(\\'),
     ('Ô\)/',     '\u1F6C', 'Ô)/'),
     ('Ô\(/',     '\u1F6D', 'Ô(/'),
     ('Ô~\)',     '\u1F6E', 'Ô~)'),
     ('Ô~\(',     '\u1F6F', 'Ô~('),
     ('a\)\|',    '\u1F80', 'a)|'),
     ('a\(\|',    '\u1F81', 'a(|'),
     ('A\)\|',    '\u1F88', 'A)|'),
     ('A\(\|',    '\u1F89', 'A(|'),
     ('ê\)\|',    '\u1F90', 'ê)|'),
     ('ê\(\|',    '\u1F91', 'ê(|'),
     ('Ê\)\|',    '\u1F98', 'Ê)|'),
     ('Ê\(\|',    '\u1F99', 'Ê(|'),
     ('ô\)\|',    '\u1FA0', 'ô)|'),
     ('ô\(\|',    '\u1FA1', 'ô(|'),
     ('Ô\)\|',    '\u1FA8', 'Ô)|'),
     ('Ô\(\|',    '\u1FA9', 'Ô(|'),
     (r'a\\\|',   '\u1FB2', 'a\\|'),
     ('a/\|',     '\u1FB4', 'a/|'),
     ('a~\|',     '\u1FB7', 'a~|'),
     (r'ê\\\|',   '\u1FC2', 'ê\\|'),
     ('ê/\|',     '\u1FC4', 'ê/|'),
     ('ê~\|',     '\u1FC7', 'ê~|'),
     (r'i\\\+',   '\u1FD2', 'i\\+'),
     ('i/\+',     '\u1FD3', 'i/+'),
     ('i~\+',     '\u1FD7', 'i~+'),
     (r'y\\\+',   '\u1FE2', 'y\\+'),
     ('y/\+',     '\u1FE3', 'y/+'),
     ('y~\+',     '\u1FE7', 'y~+'),
     (r'ô\\\|',   '\u1FF2', 'ô\\|'),
     ('ô/\|',     '\u1FF4', 'ô/|'),
     ('ô~\|',     '\u1FF7', 'ô~|'),
     ('i/\+',     '\u0390', 'i/+'),
     ('y/\+',     '\u03B0', 'y/+'),
     ('a\)',      '\u1F00', 'a)'),  # Singly marked letters
     ('a\(',      '\u1F01', 'a('),
     ('A\)',      '\u1F08', 'A)'),
     ('A\(',      '\u1F09', 'A('),
     (r'O\\',     '\u1FF8', 'O\\'),
     ('O/',       '\u1FF9', 'O/'),
     ('e\)',      '\u1F10', 'e)'),
     ('e\(',      '\u1F11', 'e('),
     ('E\)',      '\u1F18', 'E)'),
     ('E\(',      '\u1F19', 'E('),
     ('ê\)',      '\u1F20', 'ê)'),
     ('ê\(',      '\u1F21', 'ê('),
     ('Ê\)',      '\u1F28', 'Ê)'),
     ('Ê\(',      '\u1F29', 'Ê('),
     ('i\)',      '\u1F30', 'i)'),
     ('i\(',      '\u1F31', 'i('),
     ('I\)',      '\u1F38', 'I)'),
     ('I\(',      '\u1F39', 'I('),
     ('o\)',      '\u1F40', 'o)'),
     ('o\(',      '\u1F41', 'o('),
     ('O\)',      '\u1F48', 'O)'),
     ('O\(',      '\u1F49', 'O('),
     ('y\)',      '\u1F50', 'y)'),
     ('y\(',      '\u1F51', 'y('),
     ('Y\(',      '\u1F59', 'Y('),
     ('ô\)',      '\u1F60', 'ô)'),
     ('ô\(',      '\u1F61', 'ô('),
     ('Ô\)',      '\u1F68', 'Ô)'),
     ('Ô\(',      '\u1F69', 'Ô('),
     (r'a\\',     '\u1F70', 'a\\'),
     ('a/',       '\u1F71', 'a/'),
     (r'e\\',     '\u1F72', 'e\\'),
     ('e/',       '\u1F73', 'e/'),
     (r'ê\\',     '\u1F74', 'ê\\'),
     ('ê/',       '\u1F75', 'ê/'),
     (r'i\\',     '\u1F76', 'i\\'),
     ('i/',       '\u1F77', 'i/'),
     (r'o\\',     '\u1F78', 'o\\'),
     ('o/',       '\u1F79', 'o/'),
     (r'y\\',     '\u1F7A', 'y\\'),
     ('y/',       '\u1F7B', 'y/'),
     (r'ô\\',     '\u1F7C', 'ô\\'),
     ('ô/',       '\u1F7D', 'ô/'),
     ('a=',       '\u1FB0', 'a='),
     ('a_',       '\u1FB1', 'a_'),
     ('a\|',      '\u1FB3', 'a|'),
     ('a~',       '\u1FB6', 'a~'),
     ('A=',       '\u1FB8', 'A='),
     ('A_',       '\u1FB9', 'A_'),
     (r'A\\',     '\u1FBA', 'A\\'),
     ('A/',       '\u1FBB', 'A/'),
     ('A\|',      '\u1FBC', 'A|'),
     ('ê\|',      '\u1FC3', 'ê|'),
     ('ê~',       '\u1FC6', 'ê~'),
     (r'E\\',     '\u1FC8', 'E\\'),
     ('E/',       '\u1FC9', 'E/'),
     (r'Ê\\',     '\u1FCA', 'Ê\\'),
     ('Ê/',       '\u1FCB', 'Ê/'),
     ('Ê\|',      '\u1FCC', 'Ê|'),
     ('i=',       '\u1FD0', 'i='),
     ('i_',       '\u1FD1', 'i_'),
     ('i~',       '\u1FD6', 'i~'),
     ('I=',       '\u1FD8', 'I='),
     ('I_',       '\u1FD9', 'I_'),
     (r'I\\',     '\u1FDA', 'I\\'),
     ('I/',       '\u1FDB', 'I/'),
     ('y=',       '\u1FE0', 'y='),
     ('y_',       '\u1FE1', 'y_'),
     ('r\)',      '\u1FE4', 'r)'),
     ('r\(',      '\u1FE5', 'r('),
     ('y~',       '\u1FE6', 'y~'),
     ('Y=',       '\u1FE8', 'Y='),
     ('Y_',       '\u1FE9', 'Y_'),
     (r'Y\\',     '\u1FEA', 'Y\\'),
     ('Y/',       '\u1FEB', 'Y/'),
     ('R\(',      '\u1FEC', 'R('),
     ('ô~',       '\u1FF6', 'ô~'),
     ('ô\|',      '\u1FF3', 'ô|'),
     (r'Ô\\',     '\u1FFA', 'Ô\\'),
     ('Ô/',       '\u1FFB', 'Ô/'),
     ('Ô\|',      '\u1FFC', 'Ô|'),
     ('I\+',      '\u03AA', 'I+'),
     ('Y\+',      '\u03AB', 'Y+'),
     ('i\+',      '\u03CA', 'i+'),
     ('y\+',      '\u03CB', 'y+'),
     #
     #   Basic Greek transliterations
     #
     (r'u\\\+',   '\u1FE2', 'u\\\+'), # U/u alternatives to Y/y
     ('u/\+',     '\u1FE3', 'u/+'),
     ('u~\+',     '\u1FE7', 'u~+'),
     (r'u\)\\',   '\u1F52', 'u)\\'),
     (r'u\(\\',   '\u1F53', 'u(\\'),
     ('u\)\/',    '\u1F54', 'u)/'),
     ('u\(\/',    '\u1F55', 'u(/'),
     ('u~\)',     '\u1F56', 'u~)'),
     ('u~\(',     '\u1F57', 'u~('),
     (r'U\(\\',   '\u1F5B', 'U(\\'),
     ('U\(\/',    '\u1F5D', 'U(/'),
     ('U~\(',     '\u1F5F', 'U~('),
     ('u\+',      '\u03CB', 'u+'),
     ('U\+',      '\u03AB', 'U+'),
     ('u=',       '\u1FE0', 'u='),
     ('u_',       '\u1FE1', 'u_'),
     ('u~',       '\u1FE6', 'u~'),
     ('U=',       '\u1FE8', 'U='),
     ('U_',       '\u1FE9', 'U_'),
     (r'U\\',     '\u1FEA', 'U\\'),
     ('U\/',      '\u1FEB', 'U/'),
     (r'u\\',     '\u1F7A', 'u\\'),
     ('u\/',      '\u1F7B', 'u/'),
     ('u\)',      '\u1F50', 'u)'),
     ('u\(',      '\u1F51', 'u('),
     ('U\(',      '\u1F59', 'U('),
     ('\?',       '\u037E', '?'),
     (';',        '\u0387', ';'),
     ('r\)',      '\u1FE4', 'r)'),
     ('r\(',      '\u1FE5', 'r('),
     ('th',       '\u03B8', 'th'),
     ('T[Hh]',    '\u0398', 'TH or Th'),
     ('\{S[Tt]}', '\u03DA', 'ST or St (Stigma)'),      # must handle stigmas before s (note unusual form
     ('\{st}',    '\u03DB', 'st (stigma)'),            # to uniquely indicate stigma vs sigma tau
     ('^s\'',     '\u03C3\'', 's may be regular', "\u03c3"),    # handle s' as regular sigma as the first characters of the string
     ('([^Pp])s\'', '\\1\u03C3\'', ' sigma or', ""),            # handle s' as regular sigma elsewhere in string
     ('^s($|\\W)', '\u03C2\\1', 'final sigma based', "\u03c2"), # handle solo s at start of string as final sigma
     ('([^Pp])s($|\\W)', '\\1\u03C2\\2', ' on situation', ""),  # handle ending s elsewhere in string as final sigma
     ('nch',      '\u03B3\u03C7', 'nch'), # basic Greek transformations
     ('NCH',      '\u0393\u03A7', 'NCH'),
     ('ch',       '\u03C7', 'ch'),
     ('C[Hh]',    '\u03A7', 'CH or Ch'),
     ('ph',       '\u03C6', 'ph'),
     ('P[Hh]',    '\u03A6', 'PH or Ph'),
     ('ng',       '\u03B3\u03B3', 'ng'),
     ('NG',       '\u0393\u0393', 'NG'),
     ('nk',       '\u03B3\u03BA', 'nk'),
     ('NK',       '\u0393\u039A', 'NK'),
     ('nx',       '\u03B3\u03BE', 'nx'),
     ('NX',       '\u0393\u039E', 'NX'),
     ('rh',       '\u1FE5', 'rh'),
     ('R[Hh]',    '\u1FEC', 'RH or Rh'),
     ('ps',       '\u03C8', 'ps'),
     ('P[Ss]',    '\u03A8', 'PS or Ps'),
     ('ha',       '\u1F01', 'ha'),
     ('he',       '\u1F11', 'he'),
     ('hê',       '\u1F21', 'hê'),
     ('hi',       '\u1F31', 'hi'),
     ('ho',       '\u1F41', 'ho'),
     ('hy',       '\u1F51', 'hy'),
     ('hu',       '\u1F51', 'hu'),
     ('hô',       '\u1F61', 'hô'),
     ('H[Aa]',    '\u1F09', 'HA or Ha'),
     ('H[Ee]',    '\u1F19', 'HE or He'),
     ('H[Êê]',    '\u1F29', 'HÊ or Hê'),
     ('H[Ii]',    '\u1F39', 'HI or Hi'),
     ('H[Oo]',    '\u1F49', 'HO or Ho'),
     ('H[Yy]',    '\u1F59', 'HY or Hy'),
     ('H[Uu]',    '\u1F59', 'HU or Hu'),
     ('HÔ|Hô',    '\u1F69', 'HÔ or Hô'),
     ('ou',       '\u03BF\u03C5', 'ou'),
     ('A',        '\u0391', 'A'),
     ('a',        '\u03B1', 'a'),
     ('B',        '\u0392', 'B'),
     ('b',        '\u03B2', 'b'),
     ('G',        '\u0393', 'G'),
     ('g',        '\u03B3', 'g'),
     ('D',        '\u0394', 'D'),
     ('d',        '\u03B4', 'd'),
     ('E',        '\u0395', 'E'),
     ('e',        '\u03B5', 'e'),
     ('Z',        '\u0396', 'Z'),
     ('z',        '\u03B6', 'z'),
     ('Ê',        '\u0397', 'Ê'),
     ('ê',        '\u03B7', 'ê'),
     ('I',        '\u0399', 'I'),
     ('i',        '\u03B9', 'i'),
     ('K',        '\u039A', 'K'),
     ('k',        '\u03BA', 'k'),
     ('L',        '\u039B', 'L'),
     ('l',        '\u03BB', 'l'),
     ('M',        '\u039C', 'M'),
     ('m',        '\u03BC', 'm'),
     ('N',        '\u039D', 'N'),
     ('n',        '\u03BD', 'n'),
     ('X',        '\u039E', 'X'),
     ('x',        '\u03BE', 'x'),
     ('O',        '\u039F', 'O'),
     ('o',        '\u03BF', 'o'),
     ('P',        '\u03A0', 'P'),
     ('p',        '\u03C0', 'p'),
     ('R',        '\u03A1', 'R'),
     ('r',        '\u03C1', 'r'),
     ('S',        '\u03A3', 'S'),
     ('s',        '\u03C3', 's'),
     ('T',        '\u03A4', 'T'),
     ('t',        '\u03C4', 't'),
     ('Y',        '\u03A5', 'Y'),
     ('y',        '\u03C5', 'y'),
     ('U',        '\u03A5', 'U'),
     ('u',        '\u03C5', 'u'),
     ('Ô',        '\u03A9', 'Ô'),
     ('ô',        '\u03C9', 'ô'),
     ('J',        '\u03D8', 'J (Archaic Koppa)'),
     ('j',        '\u03D9', 'j (archaic koppa)'),
     ('W',        '\u03DC', 'W (Digamma)'),
     ('w',        '\u03DD', 'w (digamma)'),
     ('Q',        '\u03DE', 'Q (Qoppa)'),
     ('q',        '\u03DF', 'q (qoppa)'),
     ('C',        '\u03E0', 'C (Sampi)'),
     ('c',        '\u03E1', 'c (sampi)'),
     ('<γ>',      '<g>',    '<g> (gesperrt emphasis)'),
     ('</γ>',     '</g>',   '</g> (gesperrt emphasis)'),
    ]

  # Format of diacritic table:
  # 1. character(s) the user enters
  # 2. character(s) ppgen outputs
  # 3. printable form for .cvglist output listing
  # 4. If 1, this is a nonstandard form of markup that will generate a warning message
  #      if used.
  diacritics = [
    ('[=A]',    '\u0100', '\\u0100', 0), # LATIN CAPITAL LETTER A WITH MACRON    (Latin Extended-A)
    ('[=a]',    '\u0101', '\\u0101', 0), # LATIN SMALL LETTER A WITH MACRON
    ('[)A]',    '\u0102', '\\u0102', 0), # LATIN CAPITAL LETTER A WITH BREVE
    ('[)a]',    '\u0103', '\\u0103', 0), # LATIN SMALL LETTER A WITH BREVE
    ('[A,]',    '\u0104', '\\u0104', 0), # LATIN CAPITAL LETTER A WITH OGONEK
    ('[a,]',    '\u0105', '\\u0105', 0), # LATIN SMALL LETTER A WITH OGONEK
    ('[\'C]',   '\u0106', '\\u0106', 0), # LATIN CAPITAL LETTER C WITH ACUTE
    ('[\'c]',   '\u0107', '\\u0107', 0), # LATIN SMALL LETTER C WITH ACUTE
    ('[^C]',    '\u0108', '\\u0108', 0), # LATIN CAPITAL LETTER C WITH CIRCUMFLEX
    ('[^c]',    '\u0109', '\\u0109', 0), # LATIN SMALL LETTER C WITH CIRCUMFLEX
    ('[.C]',    '\u010A', '\\u010A', 0), # LATIN CAPITAL LETTER C WITH DOT ABOVE
    ('[.c]',    '\u010B', '\\u010B', 0), # LATIN SMALL LETTER C WITH DOT ABOVE
    ('[vC]',    '\u010C', '\\u010C', 0), # LATIN CAPITAL LETTER C WITH CARON
    ('[vc]',    '\u010D', '\\u010D', 0), # LATIN SMALL LETTER C WITH CARON
    ('[vD]',    '\u010E', '\\u010E', 0), # LATIN CAPITAL LETTER D WITH CARON
    ('[vd]',    '\u010F', '\\u010F', 0), # LATIN SMALL LETTER D WITH CARON
    ('[-D]',    '\u0110', '\\u0110', 0), # LATIN CAPITAL LETTER D WITH STROKE
    ('[-d]',    '\u0111', '\\u0111', 0), # LATIN SMALL LETTER D WITH STROKE
    ('[=E]',    '\u0112', '\\u0112', 0), # LATIN CAPITAL LETTER E WITH MACRON
    ('[=e]',    '\u0113', '\\u0113', 0), # LATIN SMALL LETTER E WITH MACRON
    ('[)E]',    '\u0114', '\\u0114', 0), # LATIN CAPITAL LETTER E WITH BREVE
    ('[)e]',    '\u0115', '\\u0115', 0), # LATIN SMALL LETTER E WITH BREVE
    ('[.E]',    '\u0116', '\\u0116', 0), # LATIN CAPITAL LETTER E WITH DOT ABOVE
    ('[.e]',    '\u0117', '\\u0117', 0), # LATIN SMALL LETTER E WITH DOT ABOVE
    #('[E,]', '\u0118', '\\u0118', 0), # LATIN CAPITAL LETTER E WITH OGONEK  # conflicts with markup for cedilla
    #('[e,]', '\u0119', '\\u0119', 0), # LATIN SMALL LETTER E WITH OGONEK    # conflicts with markup for cedilla
    ('[vE]',    '\u011A', '\\u011A', 0), # LATIN CAPITAL LETTER E WITH CARON
    ('[ve]',    '\u011B', '\\u011B', 0), # LATIN SMALL LETTER E WITH CARON
    ('[^G]',    '\u011C', '\\u011C', 0), # LATIN CAPITAL LETTER G WITH CIRCUMFLEX
    ('[^g]',    '\u011D', '\\u011D', 0), # LATIN SMALL LETTER G WITH CIRCUMFLEX
    ('[)G]',    '\u011E', '\\u011E', 0), # LATIN CAPITAL LETTER G WITH BREVE
    ('[)g]',    '\u011F', '\\u011F', 0), # LATIN SMALL LETTER G WITH BREVE
    ('[.G]',    '\u0120', '\\u0120', 0), # LATIN CAPITAL LETTER G WITH DOT ABOVE
    ('[.g]',    '\u0121', '\\u0121', 0), # LATIN SMALL LETTER G WITH DOT ABOVE
    ('[G,]',    '\u0122', '\\u0122', 0), # LATIN CAPITAL LETTER G WITH CEDILLA
    ('[g,]',    '\u0123', '\\u0123', 0), # LATIN SMALL LETTER G WITH CEDILLA
    ('[^H]',    '\u0124', '\\u0124', 0), # LATIN CAPITAL LETTER H WITH CIRCUMFLEX
    ('[^h]',    '\u0125', '\\u0125', 0), # LATIN SMALL LETTER H WITH CIRCUMFLEX
    ('[-H]',    '\u0126', '\\u0126', 0), # LATIN CAPITAL LETTER H WITH STROKE
    ('[-h]',    '\u0127', '\\u0127', 0), # LATIN SMALL LETTER H WITH STROKE
    ('[~I]',    '\u0128', '\\u0128', 0), # LATIN CAPITAL LETTER I WITH TILDE
    ('[~i]',    '\u0129', '\\u0129', 0), # LATIN SMALL LETTER I WITH TILDE
    ('[=I]',    '\u012A', '\\u012A', 0), # LATIN CAPITAL LETTER I WITH MACRON
    ('[=i]',    '\u012B', '\\u012B', 0), # LATIN SMALL LETTER I WITH MACRON
    ('[)I]',    '\u012C', '\\u012C', 0), # LATIN CAPITAL LETTER I WITH BREVE
    ('[)i]',    '\u012D', '\\u012D', 0), # LATIN SMALL LETTER I WITH BREVE
    ('[I,]',    '\u012E', '\\u012E', 0), # LATIN CAPITAL LETTER I WITH OGONEK
    ('[i,]',    '\u012F', '\\u012F', 0), # LATIN SMALL LETTER I WITH OGONEK
    ('[.I]',    '\u0130', '\\u0130', 0), # LATIN CAPITAL LETTER I WITH DOT ABOVE
    #('[]', '\u0131', '\\u0131', 0), # LATIN SMALL LETTER DOTLESS I
    ('[IJ]',    '\u0132', '\\u0132', 0), # LATIN CAPITAL LIGATURE IJ
    ('[ij]',    '\u0133', '\\u0133', 0), # LATIN SMALL LIGATURE IJ
    ('[^J]',    '\u0134', '\\u0134', 0), # LATIN CAPITAL LETTER J WITH CIRCUMFLEX
    ('[^j]',    '\u0135', '\\u0135', 0), # LATIN SMALL LETTER J WITH CIRCUMFLEX
    ('[K,]',    '\u0136', '\\u0136', 0), # LATIN CAPITAL LETTER K WITH CEDILLA
    ('[k,]',    '\u0137', '\\u0137', 0), # LATIN SMALL LETTER K WITH CEDILLA
    ('[kra]',   '\u0138', '\\u0138', 0), # LATIN SMALL LETTER KRA
    ('[\'L]',   '\u0139', '\\u0139', 0), # LATIN CAPITAL LETTER L WITH ACUTE
    ('[\'l]',   '\u013A', '\\u013A', 0), # LATIN SMALL LETTER L WITH ACUTE
    ('[L,]',    '\u013B', '\\u013B', 0), # LATIN CAPITAL LETTER L WITH CEDILLA
    ('[l,]',    '\u013C', '\\u013C', 0), # LATIN SMALL LETTER L WITH CEDILLA
    ('[vL]',    '\u013D', '\\u013D', 0), # LATIN CAPITAL LETTER L WITH CARON
    ('[vl]',    '\u013E', '\\u013E', 0), # LATIN SMALL LETTER L WITH CARON
    ('[L·]',    '\u013F', '\\u013F', 0), # LATIN CAPITAL LETTER L WITH MIDDLE DOT
    ('[l·]',    '\u0140', '\\u0140', 0), # LATIN SMALL LETTER L WITH MIDDLE DOT
    ('[/L]',    '\u0141', '\\u0141', 0), # LATIN CAPITAL LETTER L WITH STROKE
    ('[/l]',    '\u0142', '\\u0142', 0), # LATIN SMALL LETTER L WITH STROKE
    ('[\'N]',   '\u0143', '\\u0143', 0), # LATIN CAPITAL LETTER N WITH ACUTE
    ('[\'n]',   '\u0144', '\\u0144', 0), # LATIN SMALL LETTER N WITH ACUTE
    ('[N,]',    '\u0145', '\\u0145', 0), # LATIN CAPITAL LETTER N WITH CEDILLA
    ('[n,]',    '\u0146', '\\u0146', 0), # LATIN SMALL LETTER N WITH CEDILLA
    ('[vN]',    '\u0147', '\\u0147', 0), # LATIN CAPITAL LETTER N WITH CARON
    ('[vn]',    '\u0148', '\\u0148', 0), # LATIN SMALL LETTER N WITH CARON
    #('[\'n]', '\u0149', '\\u0149', 0), # LATIN SMALL LETTER N PRECEDED BY APOSTROPHE (conflicts with markup for n with acute)
    ('[Eng]',   '\u014A', '\\u014A', 0), # LATIN CAPITAL LETTER ENG
    ('[eng]',   '\u014B', '\\u014B', 0), # LATIN SMALL LETTER ENG
    ('[=O]',    '\u014C', '\\u014C', 0), # LATIN CAPITAL LETTER O WITH MACRON
    ('[=o]',    '\u014D', '\\u014D', 0), # LATIN SMALL LETTER O WITH MACRON
    ('[)O]',    '\u014E', '\\u014E', 0), # LATIN CAPITAL LETTER O WITH BREVE
    ('[)o]',    '\u014F', '\\u014F', 0), # LATIN SMALL LETTER O WITH BREVE
    ('[\'\'O]', '\u0150', '\\u0150', 0), # LATIN CAPITAL LETTER O WITH DOUBLE ACUTE
    ('[\'\'o]', '\u0151', '\\u0151', 0), # LATIN SMALL LETTER O WITH DOUBLE ACUTE
    ('[OE]',    '\u0152', '\\u0152', 0), # LATIN CAPITAL LIGATURE OE
    ('[oe]',    '\u0153', '\\u0153', 0), # LATIN SMALL LIGATURE OE
    ('[\'R]',   '\u0154', '\\u0154', 0), # LATIN CAPITAL LETTER R WITH ACUTE
    ('[\'r]',   '\u0155', '\\u0155', 0), # LATIN SMALL LETTER R WITH ACUTE
    ('[R,]',    '\u0156', '\\u0156', 0), # LATIN CAPITAL LETTER R WITH CEDILLA
    ('[r,]',    '\u0157', '\\u0157', 0), # LATIN SMALL LETTER R WITH CEDILLA
    ('[vR]',    '\u0158', '\\u0158', 0), # LATIN CAPITAL LETTER R WITH CARON
    ('[vr]',    '\u0159', '\\u0159', 0), # LATIN SMALL LETTER R WITH CARON
    ('[\'S]',   '\u015A', '\\u015A', 0), # LATIN CAPITAL LETTER S WITH ACUTE
    ('[\'s]',   '\u015B', '\\u015B', 0), # LATIN SMALL LETTER S WITH ACUTE
    ('[^S]',    '\u015C', '\\u015C', 0), # LATIN CAPITAL LETTER S WITH CIRCUMFLEX
    ('[^s]',    '\u015D', '\\u015D', 0), # LATIN SMALL LETTER S WITH CIRCUMFLEX
    ('[S,]',    '\u015E', '\\u015E', 0), # LATIN CAPITAL LETTER S WITH CEDILLA
    ('[s,]',    '\u015F', '\\u015F', 0), # LATIN SMALL LETTER S WITH CEDILLA
    ('[vS]',    '\u0160', '\\u0160', 0), # LATIN CAPITAL LETTER S WITH CARON
    ('[vs]',    '\u0161', '\\u0161', 0), # LATIN SMALL LETTER S WITH CARON
    ('[T,]',    '\u0162', '\\u0162', 0), # LATIN CAPITAL LETTER T WITH CEDILLA
    ('[t,]',    '\u0163', '\\u0163', 0), # LATIN SMALL LETTER T WITH CEDILLA
    ('[vT]',    '\u0164', '\\u0164', 0), # LATIN CAPITAL LETTER T WITH CARON
    ('[vt]',    '\u0165', '\\u0165', 0), # LATIN SMALL LETTER T WITH CARON
    ('[-T]',    '\u0166', '\\u0166', 0), # LATIN CAPITAL LETTER T WITH STROKE
    ('[-t]',    '\u0167', '\\u0167', 0), # LATIN SMALL LETTER T WITH STROKE
    ('[~U]',    '\u0168', '\\u0168', 0), # LATIN CAPITAL LETTER U WITH TILDE
    ('[~u]',    '\u0169', '\\u0169', 0), # LATIN SMALL LETTER U WITH TILDE
    ('[=U]',    '\u016A', '\\u016A', 0), # LATIN CAPITAL LETTER U WITH MACRON
    ('[=u]',    '\u016B', '\\u016B', 0), # LATIN SMALL LETTER U WITH MACRON
    ('[)U]',    '\u016C', '\\u016C', 0), # LATIN CAPITAL LETTER U WITH BREVE
    ('[)u]',    '\u016D', '\\u016D', 0), # LATIN SMALL LETTER U WITH BREVE
    ('[°U]',    '\u016E', '\\u016E', 0), # LATIN CAPITAL LETTER U WITH RING ABOVE
    ('[°u]',    '\u016F', '\\u016F', 0), # LATIN SMALL LETTER U WITH RING ABOVE
    ('[\'\'U]', '\u0170', '\\u0170', 0), # LATIN CAPITAL LETTER U WITH DOUBLE ACUTE
    ('[\'\'u]', '\u0171', '\\u0171', 0), # LATIN SMALL LETTER U WITH DOUBLE ACUTE
    ('[U,]',    '\u0172', '\\u0172', 0), # LATIN CAPITAL LETTER U WITH OGONEK
    ('[u,]',    '\u0173', '\\u0173', 0), # LATIN SMALL LETTER U WITH OGONEK
    ('[^W]',    '\u0174', '\\u0174', 0), # LATIN CAPITAL LETTER W WITH CIRCUMFLEX
    ('[^w]',    '\u0175', '\\u0175', 0), # LATIN SMALL LETTER W WITH CIRCUMFLEX
    ('[^Y]',    '\u0176', '\\u0176', 0), # LATIN CAPITAL LETTER Y WITH CIRCUMFLEX
    ('[^y]',    '\u0177', '\\u0177', 0), # LATIN SMALL LETTER Y WITH CIRCUMFLEX
    ('[:Y]',    '\u0178', '\\u0178', 0), # LATIN CAPITAL LETTER Y WITH DIAERESIS
    ('[\'Z]',   '\u0179', '\\u0179', 0), # LATIN CAPITAL LETTER Z WITH ACUTE
    ('[\'z]',   '\u017A', '\\u017A', 0), # LATIN SMALL LETTER Z WITH ACUTE
    ('[.Z]',    '\u017B', '\\u017B', 0), # LATIN CAPITAL LETTER Z WITH DOT ABOVE
    ('[.z]',    '\u017C', '\\u017C', 0), # LATIN SMALL LETTER Z WITH DOT ABOVE
    ('[vZ]',    '\u017D', '\\u017D', 0), # LATIN CAPITAL LETTER Z WITH CARON
    ('[vz]',    '\u017E', '\\u017E', 0), # LATIN SMALL LETTER Z WITH CARON
    ('[s]',     '\u017F', '\\u017F', 0), # LATIN SMALL LETTER LONG S
    ('[-b]',    '\u0180', '\\u0180', 0), # LATIN SMALL LETTER B WITH STROKE     (Latin Extended-B)
    #('[]', '\u0181', '\\u0181', 0), # LATIN CAPITAL LETTER B WITH HOOK
    #('[]', '\u0182', '\\u0182', 0), # LATIN CAPITAL LETTER B WITH TOPBAR
    #('[]', '\u0183', '\\u0183', 0), # LATIN SMALL LETTER B WITH TOPBAR
    #('[]', '\u0184', '\\u0184', 0), # LATIN CAPITAL LETTER TONE SIX
    #('[]', '\u0185', '\\u0185', 0), # LATIN SMALL LETTER TONE SIX
    #('[]', '\u0186', '\\u0186', 0), # LATIN CAPITAL LETTER OPEN O
    #('[]', '\u0187', '\\u0187', 0), # LATIN CAPITAL LETTER C WITH HOOK
    #('[]', '\u0188', '\\u0188', 0), # LATIN SMALL LETTER C WITH HOOK
    #('[]', '\u0189', '\\u0189', 0), # LATIN CAPITAL LETTER AFRICAN D
    #('[]', '\u018A', '\\u018A', 0), # LATIN CAPITAL LETTER D WITH HOOK
    #('[]', '\u018B', '\\u018B', 0), # LATIN CAPITAL LETTER D WITH TOPBAR
    #('[]', '\u018C', '\\u018C', 0), # LATIN SMALL LETTER D WITH TOPBAR
    #('[]', '\u018D', '\\u018D', 0), # LATIN SMALL LETTER TURNED DELTA
    #('[]', '\u018E', '\\u018E', 0), # LATIN CAPITAL LETTER REVERSED E
    ('[Schwa]', '\u018F', '\\u018F', 0), # LATIN CAPITAL LETTER SCHWA
    #('[]', '\u0190', '\\u0190', 0), # LATIN CAPITAL LETTER OPEN E
    #('[]', '\u0191', '\\u0191', 0), # LATIN CAPITAL LETTER F WITH HOOK
    #('[]', '\u0192', '\\u0192', 0), # LATIN SMALL LETTER F WITH HOOK
    #('[]', '\u0193', '\\u0193', 0), # LATIN CAPITAL LETTER G WITH HOOK
    #('[Gamma]', '\u0194', '\\u0194', 0), # LATIN CAPITAL LETTER GAMMA  (use Greek versions instead)
    #('[]', '\u0195', '\\u0195', 0), # LATIN SMALL LETTER HV
    #('[Iota]', '\u0196', '\\u0196', 0), # LATIN CAPITAL LETTER IOTA    (use Greek versions instead)
    ('[-I]',    '\u0197', '\\u0197', 0), # LATIN CAPITAL LETTER I WITH STROKE
    #('[]', '\u0198', '\\u0198', 0), # LATIN CAPITAL LETTER K WITH HOOK
    #('[]', '\u0199', '\\u0199', 0), # LATIN SMALL LETTER K WITH HOOK
    ('[-l]',    '\u019A', '\\u019A', 0), # LATIN SMALL LETTER L WITH BAR
    #('[]', '\u019B', '\\u019B', 0), # LATIN SMALL LETTER LAMBDA WITH STROKE
    #('[]', '\u019C', '\\u019C', 0), # LATIN CAPITAL LETTER TURNED M
    #('[]', '\u019D', '\\u019D', 0), # LATIN CAPITAL LETTER N WITH LEFT HOOK
    #('[]', '\u019E', '\\u019E', 0), # LATIN SMALL LETTER N WITH LONG RIGHT LEG
    #('[]', '\u019F', '\\u019F', 0), # LATIN CAPITAL LETTER O WITH MIDDLE TILDE
    #('[]', '\u01A0', '\\u01A0', 0), # LATIN CAPITAL LETTER O WITH HORN
    #('[]', '\u01A1', '\\u01A1', 0), # LATIN SMALL LETTER O WITH HORN
    ('[OI]',    '\u01A2', '\\u01A2', 0), # LATIN CAPITAL LETTER OI
    ('[oi]',    '\u01A3', '\\u01A3', 0), # LATIN SMALL LETTER OI
    #('[]', '\u01A4', '\\u01A4', 0), # LATIN CAPITAL LETTER P WITH HOOK
    #('[]', '\u01A5', '\\u01A5', 0), # LATIN SMALL LETTER P WITH HOOK
    #('[]', '\u01A6', '\\u01A6', 0), # LATIN LETTER YR
    #('[]', '\u01A7', '\\u01A7', 0), # LATIN CAPITAL LETTER TONE TWO
    #('[]', '\u01A8', '\\u01A8', 0), # LATIN SMALL LETTER TONE TWO
    ('[Esh]',   '\u01A9', '\\u01A9', 0), # LATIN CAPITAL LETTER ESH
    #('[]', '\u01AA', '\\u01AA', 0), # LATIN LETTER REVERSED ESH LOOP
    #('[]', '\u01AB', '\\u01AB', 0), # LATIN SMALL LETTER T WITH PALATAL HOOK
    #('[]', '\u01AC', '\\u01AC', 0), # LATIN CAPITAL LETTER T WITH HOOK
    #('[]', '\u01AD', '\\u01AD', 0), # LATIN SMALL LETTER T WITH HOOK
    #('[]', '\u01AE', '\\u01AE', 0), # LATIN CAPITAL LETTER T WITH RETROFLEX HOOK
    #('[]', '\u01AF', '\\u01AF', 0), # LATIN CAPITAL LETTER U WITH HORN
    #('[]', '\u01B0', '\\u01B0', 0), # LATIN SMALL LETTER U WITH HORN
    #('[Upsilon]', '\u01B1', '\\u01B1', 0), # LATIN CAPITAL LETTER UPSILON    (use Greek versions instead)
    #('[]', '\u01B2', '\\u01B2', 0), # LATIN CAPITAL LETTER V WITH HOOK
    #('[]', '\u01B3', '\\u01B3', 0), # LATIN CAPITAL LETTER Y WITH HOOK
    #('[]', '\u01B4', '\\u01B4', 0), # LATIN SMALL LETTER Y WITH HOOK
    ('[-Z]',    '\u01B5', '\\u01B5', 0), # LATIN CAPITAL LETTER Z WITH STROKE
    ('[-z]',    '\u01B6', '\\u01B6', 0), # LATIN SMALL LETTER Z WITH STROKE
    ('[Zh]',    '\u01B7', '\\u01B7', 0), # LATIN CAPITAL LETTER EZH
    ('[zh]',    '\u0292', '\\u0292', 0), # LATIN SMALL LETTER EZH (out of order just to keep it with the capital)
    #('[]', '\u01B8', '\\u01B8', 0), # LATIN CAPITAL LETTER EZH REVERSED
    #('[]', '\u01B9', '\\u01B9', 0), # LATIN SMALL LETTER EZH REVERSED
    #('[]', '\u01BA', '\\u01BA', 0), # LATIN SMALL LETTER EZH WITH TAIL
    ('[-2]',    '\u01BB', '\\u01BB', 0), # LATIN LETTER TWO WITH STROKE
    #('[]', '\u01BC', '\\u01BC', 0), # LATIN CAPITAL LETTER TONE FIVE
    #('[]', '\u01BD', '\\u01BD', 0), # LATIN SMALL LETTER TONE FIVE
    #('[]', '\u01BE', '\\u01BE', 0), # LATIN LETTER INVERTED GLOTTAL STOP WITH STROKE
    ('[wynn]',  '\u01BF', '\\u01BF', 0), # LATIN LETTER WYNN
    #('[]', '\u01C0', '\\u01C0', 0), # LATIN LETTER DENTAL CLICK
    #('[]', '\u01C1', '\\u01C1', 0), # LATIN LETTER LATERAL CLICK
    #('[]', '\u01C2', '\\u01C2', 0), # LATIN LETTER ALVEOLAR CLICK
    #('[]', '\u01C3', '\\u01C3', 0), # LATIN LETTER RETROFLEX CLICK
    ('[vDZ]',   '\u01C4', '\\u01C4', 0), # LATIN CAPITAL LETTER DZ WITH CARON
    ('[vDz]',   '\u01C5', '\\u01C5', 0), # LATIN CAPITAL LETTER D WITH SMALL LETTER Z WITH CARON
    ('[vdz]',   '\u01C6', '\\u01C6', 0), # LATIN SMALL LETTER DZ WITH CARON
    ('[LJ]',    '\u01C7', '\\u01C7', 0), # LATIN CAPITAL LETTER LJ
    ('[Lj]',    '\u01C8', '\\u01C8', 0), # LATIN CAPITAL LETTER L WITH SMALL LETTER J
    ('[lj]',    '\u01C9', '\\u01C9', 0), # LATIN SMALL LETTER LJ
    ('[NJ]',    '\u01CA', '\\u01CA', 0), # LATIN CAPITAL LETTER NJ
    ('[Nj]',    '\u01CB', '\\u01CB', 0), # LATIN CAPITAL LETTER N WITH SMALL LETTER J
    ('[nj]',    '\u01CC', '\\u01CC', 0), # LATIN SMALL LETTER NJ
    ('[vA]',    '\u01CD', '\\u01CD', 0), # LATIN CAPITAL LETTER A WITH CARON
    ('[va]',    '\u01CE', '\\u01CE', 0), # LATIN SMALL LETTER A WITH CARON
    ('[vI]',    '\u01CF', '\\u01CF', 0), # LATIN CAPITAL LETTER I WITH CARON
    ('[vi]',    '\u01D0', '\\u01D0', 0), # LATIN SMALL LETTER I WITH CARON
    ('[vO]',    '\u01D1', '\\u01D1', 0), # LATIN CAPITAL LETTER O WITH CARON
    ('[vo]',    '\u01D2', '\\u01D2', 0), # LATIN SMALL LETTER O WITH CARON
    ('[vU]',    '\u01D3', '\\u01D3', 0), # LATIN CAPITAL LETTER U WITH CARON
    ('[vu]',    '\u01D4', '\\u01D4', 0), # LATIN SMALL LETTER U WITH CARON
    ('[=Ü]',    '\u01D5', '\\u01D5', 0), # LATIN CAPITAL LETTER U WITH DIAERESIS AND MACRON
    ('[=:U]',   '\u01D5', '\\u01D5', 1), # LATIN CAPITAL LETTER U WITH DIAERESIS AND MACRON
    ('[:=U]',   '\u01D5', '\\u01D5', 1), # LATIN CAPITAL LETTER U WITH DIAERESIS AND MACRON
    ('[=ü]',    '\u01D6', '\\u01D6', 0), # LATIN SMALL LETTER U WITH DIAERESIS AND MACRON
    ('[=:u]',   '\u01D6', '\\u01D6', 1), # LATIN SMALL LETTER U WITH DIAERESIS AND MACRON
    ('[:=u]',   '\u01D6', '\\u01D6', 1), # LATIN SMALL LETTER U WITH DIAERESIS AND MACRON
    ('[\'Ü]',   '\u01D7', '\\u01D7', 0), # LATIN CAPITAL LETTER U WITH DIAERESIS AND ACUTE
    ('[\':U]',  '\u01D7', '\\u01D7', 1), # LATIN CAPITAL LETTER U WITH DIAERESIS AND ACUTE
    ('[:\'U]',  '\u01D7', '\\u01D7', 1), # LATIN CAPITAL LETTER U WITH DIAERESIS AND ACUTE
    ('[:Ú]',    '\u01D7', '\\u01D7', 1), # LATIN CAPITAL LETTER U WITH DIAERESIS AND ACUTE
    ('[\'ü]',   '\u01D8', '\\u01D8', 0), # LATIN SMALL LETTER U WITH DIAERESIS AND ACUTE
    ('[\':u]',  '\u01D8', '\\u01D8', 1), # LATIN SMALL LETTER U WITH DIAERESIS AND ACUTE
    ('[:\'u]',  '\u01D8', '\\u01D8', 1), # LATIN SMALL LETTER U WITH DIAERESIS AND ACUTE
    ('[:ú]',    '\u01D8', '\\u01D8', 1), # LATIN SMALL LETTER U WITH DIAERESIS AND ACUTE
    ('[)Ü]',    '\u01D9', '\\u01D9', 0), # LATIN CAPITAL LETTER U WITH DIAERESIS AND CARON
    ('[):U]',   '\u01D9', '\\u01D9', 1), # LATIN CAPITAL LETTER U WITH DIAERESIS AND CARON
    ('[:)U]',   '\u01D9', '\\u01D9', 1), # LATIN CAPITAL LETTER U WITH DIAERESIS AND CARON
    ('[)ü]',    '\u01DA', '\\u01DA', 0), # LATIN SMALL LETTER U WITH DIAERESIS AND CARON
    ('[):u]',   '\u01DA', '\\u01DA', 1), # LATIN SMALL LETTER U WITH DIAERESIS AND CARON
    ('[:)u]',   '\u01DA', '\\u01DA', 1), # LATIN SMALL LETTER U WITH DIAERESIS AND CARON
    ('[`Ü]',    '\u01DB', '\\u01DB', 0), # LATIN CAPITAL LETTER U WITH DIAERESIS AND GRAVE
    ('[`:U]',   '\u01DB', '\\u01DB', 1), # LATIN CAPITAL LETTER U WITH DIAERESIS AND GRAVE
    ('[:`U]',   '\u01DB', '\\u01DB', 1), # LATIN CAPITAL LETTER U WITH DIAERESIS AND GRAVE
    ('[`ü]',    '\u01DC', '\\u01DC', 0), # LATIN SMALL LETTER U WITH DIAERESIS AND GRAVE
    ('[`:u]',   '\u01DC', '\\u01DC', 1), # LATIN SMALL LETTER U WITH DIAERESIS AND GRAVE
    ('[:`u]',   '\u01DC', '\\u01DC', 1), # LATIN SMALL LETTER U WITH DIAERESIS AND GRAVE
    #('[]', '\u01DD', '\\u01DD', 0), # LATIN SMALL LETTER TURNED E
    ('[=Ä]',    '\u01DE', '\\u01DE', 0), # LATIN CAPITAL LETTER A WITH DIAERESIS AND MACRON
    ('[=:A]',   '\u01DE', '\\u01DE', 1), # LATIN CAPITAL LETTER A WITH DIAERESIS AND MACRON
    ('[:=A]',   '\u01DE', '\\u01DE', 1), # LATIN CAPITAL LETTER A WITH DIAERESIS AND MACRON
    ('[=ä]',    '\u01DF', '\\u01DF', 0), # LATIN SMALL LETTER A WITH DIAERESIS AND MACRON
    ('[=:a]',   '\u01DF', '\\u01DF', 1), # LATIN SMALL LETTER A WITH DIAERESIS AND MACRON
    ('[:=a]',   '\u01DF', '\\u01DF', 1), # LATIN SMALL LETTER A WITH DIAERESIS AND MACRON
    ('[=.A]',   '\u01E0', '\\u01E0', 0), # LATIN CAPITAL LETTER A WITH DOT ABOVE AND MACRON
    ('[.=A]',   '\u01E0', '\\u01E0', 1), # LATIN CAPITAL LETTER A WITH DOT ABOVE AND MACRON
    ('[=.a]',   '\u01E1', '\\u01E1', 0), # LATIN SMALL LETTER A WITH DOT ABOVE AND MACRON
    ('[.=a]',   '\u01E1', '\\u01E1', 1), # LATIN SMALL LETTER A WITH DOT ABOVE AND MACRON
    ('[=AE]',   '\u01E2', '\\u01E2', 0), # LATIN CAPITAL LETTER AE WITH MACRON
    ('[=ae]',   '\u01E3', '\\u01E3', 0), # LATIN SMALL LETTER AE WITH MACRON
    ('[-G]',    '\u01E4', '\\u01E4', 0), # LATIN CAPITAL LETTER G WITH STROKE
    ('[-g]',    '\u01E5', '\\u01E5', 0), # LATIN SMALL LETTER G WITH STROKE
    ('[vG]',    '\u01E6', '\\u01E6', 0), # LATIN CAPITAL LETTER G WITH CARON
    ('[vg]',    '\u01E7', '\\u01E7', 0), # LATIN SMALL LETTER G WITH CARON
    ('[vK]',    '\u01E8', '\\u01E8', 0), # LATIN CAPITAL LETTER K WITH CARON
    ('[vk]',    '\u01E9', '\\u01E9', 0), # LATIN SMALL LETTER K WITH CARON
    ('[O,]',    '\u01EA', '\\u01EA', 0), # LATIN CAPITAL LETTER O WITH OGONEK
    ('[o,]',    '\u01EB', '\\u01EB', 0), # LATIN SMALL LETTER O WITH OGONEK
    ('[=O,]',   '\u01EC', '\\u01EC', 0), # LATIN CAPITAL LETTER O WITH OGONEK AND MACRON
    ('[=o,]',   '\u01ED', '\\u01ED', 0), # LATIN SMALL LETTER O WITH OGONEK AND MACRON
    ('[vZh]',   '\u01EE', '\\u01EE', 0), # LATIN CAPITAL LETTER EZH WITH CARON
    ('[vzh]',   '\u01EF', '\\u01EF', 0), # LATIN SMALL LETTER EZH WITH CARON
    ('[vj]',    '\u01F0', '\\u01F0', 0), # LATIN SMALL LETTER J WITH CARON
    ('[DZ]',    '\u01F1', '\\u01F1', 0), # LATIN CAPITAL LETTER DZ
    ('[Dz]',    '\u01F2', '\\u01F2', 0), # LATIN CAPITAL LETTER D WITH SMALL LETTER Z
    ('[dz]',    '\u01F3', '\\u01F3', 0), # LATIN SMALL LETTER DZ
    ('[\'G]',   '\u01F4', '\\u01F4', 0), # LATIN CAPITAL LETTER G WITH ACUTE
    ('[\'g]',   '\u01F5', '\\u01F5', 0), # LATIN SMALL LETTER G WITH ACUTE
    ('[Hwair]', '\u01F6', '\\u01F6', 0), # LATIN CAPITAL LETTER HWAIR
    ('[Wynn]',  '\u01F7', '\\u01F7', 0), # LATIN CAPITAL LETTER WYNN
    ('[`N]',    '\u01F8', '\\u01F8', 0), # LATIN CAPITAL LETTER N WITH GRAVE
    ('[`n]',    '\u01F9', '\\u01F9', 0), # LATIN SMALL LETTER N WITH GRAVE
    ('[\'Å]',   '\u01FA', '\\u01FA', 0), # LATIN CAPITAL LETTER A WITH RING ABOVE AND ACUTE
    ('[\'å]',   '\u01FB', '\\u01FB', 0), # LATIN SMALL LETTER A WITH RING ABOVE AND ACUTE
    ('[\'AE]',  '\u01FC', '\\u01FC', 0), # LATIN CAPITAL LETTER AE WITH ACUTE
    ('[\'ae]',  '\u01FD', '\\u01FD', 0), # LATIN SMALL LETTER AE WITH ACUTE
    ('[\'Ø]',   '\u01FE', '\\u01FE', 0), # LATIN CAPITAL LETTER O WITH STROKE AND ACUTE
    ('[\'ø]',   '\u01FF', '\\u01FF', 0), # LATIN SMALL LETTER O WITH STROKE AND ACUTE
    ('[``A]',   '\u0200', '\\u0200', 0), # LATIN CAPITAL LETTER A WITH DOUBLE GRAVE
    ('[``a]',   '\u0201', '\\u0201', 0), # LATIN SMALL LETTER A WITH DOUBLE GRAVE
    #('[]', '\u0202', '\\u0202', 0), # LATIN CAPITAL LETTER A WITH INVERTED BREVE
    #('[]', '\u0203', '\\u0203', 0), # LATIN SMALL LETTER A WITH INVERTED BREVE
    ('[``E]',   '\u0204', '\\u0204', 0), # LATIN CAPITAL LETTER E WITH DOUBLE GRAVE
    ('[``e]',   '\u0205', '\\u0205', 0), # LATIN SMALL LETTER E WITH DOUBLE GRAVE
    #('[]', '\u0206', '\\u0206', 0), # LATIN CAPITAL LETTER E WITH INVERTED BREVE
    #('[]', '\u0207', '\\u0207', 0), # LATIN SMALL LETTER E WITH INVERTED BREVE
    ('[``I]',   '\u0208', '\\u0208', 0), # LATIN CAPITAL LETTER I WITH DOUBLE GRAVE
    ('[``i]',   '\u0209', '\\u0209', 0), # LATIN SMALL LETTER I WITH DOUBLE GRAVE
    #('[]', '\u020A', '\\u020A', 0), # LATIN CAPITAL LETTER I WITH INVERTED BREVE
    #('[]', '\u020B', '\\u020B', 0), # LATIN SMALL LETTER I WITH INVERTED BREVE
    ('[``O]',   '\u020C', '\\u020C', 0), # LATIN CAPITAL LETTER O WITH DOUBLE GRAVE
    ('[``o]',   '\u020D', '\\u020D', 0), # LATIN SMALL LETTER O WITH DOUBLE GRAVE
    #('[]', '\u020E', '\\u020E', 0), # LATIN CAPITAL LETTER O WITH INVERTED BREVE
    #('[]', '\u020F', '\\u020F', 0), # LATIN SMALL LETTER O WITH INVERTED BREVE
    ('[``R]',   '\u0210', '\\u0210', 0), # LATIN CAPITAL LETTER R WITH DOUBLE GRAVE
    ('[``r]',   '\u0211', '\\u0211', 0), # LATIN SMALL LETTER R WITH DOUBLE GRAVE
    #('[]', '\u0212', '\\u0212', 0), # LATIN CAPITAL LETTER R WITH INVERTED BREVE
    #('[]', '\u0213', '\\u0213', 0), # LATIN SMALL LETTER R WITH INVERTED BREVE
    ('[``U]',   '\u0214', '\\u0214', 0), # LATIN CAPITAL LETTER U WITH DOUBLE GRAVE
    ('[``u]',   '\u0215', '\\u0215', 0), # LATIN SMALL LETTER U WITH DOUBLE GRAVE
    #('[]', '\u0216', '\\u0216', 0), # LATIN CAPITAL LETTER U WITH INVERTED BREVE
    #('[]', '\u0217', '\\u0217', 0), # LATIN SMALL LETTER U WITH INVERTED BREVE
    #('[S,]', '\u0218', '\\u0218', 0), # LATIN CAPITAL LETTER S WITH COMMA BELOW  # conflicts with cedilla markup
    #('[s,]', '\u0219', '\\u0219', 0), # LATIN SMALL LETTER S WITH COMMA BELOW    # conflicts with cedilla markup
    #('[T,]', '\u021A', '\\u021A', 0), # LATIN CAPITAL LETTER T WITH COMMA BELOW  # conflicts with cedilla markup
    #('[t,]', '\u021B', '\\u021B', 0), # LATIN SMALL LETTER T WITH COMMA BELOW    # conflicts with cedilla markup
    ('[Gh]',    '\u021C', '\\u021C', 0), # LATIN CAPITAL LETTER YOGH
    ('[gh]',    '\u021D', '\\u021D', 0), # LATIN SMALL LETTER YOGH
    ('[vH]',    '\u021E', '\\u021E', 0), # LATIN CAPITAL LETTER H WITH CARON
    ('[vh]',    '\u021F', '\\u021F', 0), # LATIN SMALL LETTER H WITH CARON
    #('[]', '\u0220', '\\u0220', 0), # LATIN CAPITAL LETTER N WITH LONG RIGHT LEG
    #('[]', '\u0221', '\\u0221', 0), # LATIN SMALL LETTER D WITH CURL
    ('[OU]',    '\u0222', '\\u0222', 0), # LATIN CAPITAL LETTER OU
    ('[ou]',    '\u0223', '\\u0223', 0), # LATIN SMALL LETTER OU
    #('[]', '\u0224', '\\u0224', 0), # LATIN CAPITAL LETTER Z WITH HOOK
    #('[]', '\u0225', '\\u0225', 0), # LATIN SMALL LETTER Z WITH HOOK
    ('[.A]',    '\u0226', '\\u0226', 0), # LATIN CAPITAL LETTER A WITH DOT ABOVE
    ('[.a]',    '\u0227', '\\u0227', 0), # LATIN SMALL LETTER A WITH DOT ABOVE
    ('[E,]',    '\u0228', '\\u0228', 0), # LATIN CAPITAL LETTER E WITH CEDILLA
    ('[e,]',    '\u0229', '\\u0229', 0), # LATIN SMALL LETTER E WITH CEDILLA
    ('[=Ö]',    '\u022A', '\\u022A', 0), # LATIN CAPITAL LETTER O WITH DIAERESIS AND MACRON
    ('[=:O]',   '\u022A', '\\u022A', 1), # LATIN CAPITAL LETTER O WITH DIAERESIS AND MACRON
    ('[:=O]',   '\u022A', '\\u022A', 1), # LATIN CAPITAL LETTER O WITH DIAERESIS AND MACRON
    ('[=ö]',    '\u022B', '\\u022B', 0), # LATIN SMALL LETTER O WITH DIAERESIS AND MACRON
    ('[=:o]',   '\u022B', '\\u022B', 1), # LATIN SMALL LETTER O WITH DIAERESIS AND MACRON
    ('[:=o]',   '\u022B', '\\u022B', 1), # LATIN SMALL LETTER O WITH DIAERESIS AND MACRON
    ('[=Õ]',    '\u022C', '\\u022C', 0), # LATIN CAPITAL LETTER O WITH TILDE AND MACRON
    ('[=~O]',   '\u022C', '\\u022C', 1), # LATIN CAPITAL LETTER O WITH TILDE AND MACRON
    ('[~=O]',   '\u022C', '\\u022C', 1), # LATIN CAPITAL LETTER O WITH TILDE AND MACRON
    ('[=õ]',    '\u022D', '\\u022D', 0), # LATIN SMALL LETTER O WITH TILDE AND MACRON
    ('[=~o]',   '\u022D', '\\u022D', 1), # LATIN SMALL LETTER O WITH TILDE AND MACRON
    ('[~=o]',   '\u022D', '\\u022D', 1), # LATIN SMALL LETTER O WITH TILDE AND MACRON
    ('[.O]',    '\u022E', '\\u022E', 0), # LATIN CAPITAL LETTER O WITH DOT ABOVE
    ('[.o]',    '\u022F', '\\u022F', 0), # LATIN SMALL LETTER O WITH DOT ABOVE
    ('[=.O]',   '\u0230', '\\u0230', 0), # LATIN CAPITAL LETTER O WITH DOT ABOVE AND MACRON
    ('[=.o]',   '\u0231', '\\u0231', 0), # LATIN SMALL LETTER O WITH DOT ABOVE AND MACRON
    ('[=Y]',    '\u0232', '\\u0232', 0), # LATIN CAPITAL LETTER Y WITH MACRON
    ('[=y]',    '\u0233', '\\u0233', 0), # LATIN SMALL LETTER Y WITH MACRON
    #('[]', '\u0234', '\\u0234', 0), # LATIN SMALL LETTER L WITH CURL
    #('[]', '\u0235', '\\u0235', 0), # LATIN SMALL LETTER N WITH CURL
    #('[]', '\u0236', '\\u0236', 0), # LATIN SMALL LETTER T WITH CURL
    #('[]', '\u0237', '\\u0237', 0), # LATIN SMALL LETTER DOTLESS J
    ('[db]',    '\u0238', '\\u0238', 0), # LATIN SMALL LETTER DB DIGRAPH
    ('[qp]',    '\u0239', '\\u0239', 0), # LATIN SMALL LETTER QP DIGRAPH
    ('[/A]',    '\u023A', '\\u023A', 0), # LATIN CAPITAL LETTER A WITH STROKE
    ('[/C]',    '\u023B', '\\u023B', 0), # LATIN CAPITAL LETTER C WITH STROKE
    ('[/c]',    '\u023C', '\\u023C', 0), # LATIN SMALL LETTER C WITH STROKE
    ('[-L]',    '\u023D', '\\u023D', 0), # LATIN CAPITAL LETTER L WITH BAR
    ('[/T]',    '\u023E', '\\u023E', 0), # LATIN CAPITAL LETTER T WITH DIAGONAL STROKE
    #('[]', '\u023F', '\\u023F', 0), # LATIN SMALL LETTER S WITH SWASH TAIL
    #('[]', '\u0240', '\\u0240', 0), # LATIN SMALL LETTER Z WITH SWASH TAIL
    #('[]', '\u0241', '\\u0241', 0), # LATIN CAPITAL LETTER GLOTTAL STOP
    #('[]', '\u0242', '\\u0242', 0), # LATIN SMALL LETTER GLOTTAL STOP
    ('[-B]',    '\u0243', '\\u0243', 0), # LATIN CAPITAL LETTER B WITH STROKE
    ('[-U]',    '\u0244', '\\u0244', 0), # LATIN CAPITAL LETTER U BAR
    #('[]', '\u0245', '\\u0245', 0), # LATIN CAPITAL LETTER TURNED V
    ('[/E]',    '\u0246', '\\u0246', 0), # LATIN CAPITAL LETTER E WITH STROKE
    ('[/e]',    '\u0247', '\\u0247', 0), # LATIN SMALL LETTER E WITH STROKE
    ('[-J]',    '\u0248', '\\u0248', 0), # LATIN CAPITAL LETTER J WITH STROKE
    ('[-j]',    '\u0249', '\\u0249', 0), # LATIN SMALL LETTER J WITH STROKE
    #('[]', '\u024A', '\\u024A', 0), # LATIN CAPITAL LETTER SMALL Q WITH HOOK TAIL
    #('[]', '\u024B', '\\u024B', 0), # LATIN SMALL LETTER Q WITH HOOK TAIL
    ('[-R]',    '\u024C', '\\u024C', 0), # LATIN CAPITAL LETTER R WITH STROKE
    ('[-r]',    '\u024D', '\\u024D', 0), # LATIN SMALL LETTER R WITH STROKE
    ('[-Y]',    '\u024E', '\\u024E', 0), # LATIN CAPITAL LETTER Y WITH STROKE
    ('[-y]',    '\u024F', '\\u024F', 0), # LATIN SMALL LETTER Y WITH STROKE
    ('[A°]',    '\u1E00', '\\u1E00', 0), # LATIN CAPITAL LETTER A WITH RING BELOW    (Latin Extended Additional)
    ('[a°]',    '\u1E01', '\\u1E01', 0), # LATIN SMALL LETTER A WITH RING BELOW
    ('[.B]',    '\u1E02', '\\u1E02', 0), # LATIN CAPITAL LETTER B WITH DOT ABOVE
    ('[.b]',    '\u1E03', '\\u1E03', 0), # LATIN SMALL LETTER B WITH DOT ABOVE
    ('[B.]',    '\u1E04', '\\u1E04', 0), # LATIN CAPITAL LETTER B WITH DOT BELOW
    ('[b.]',    '\u1E05', '\\u1E05', 0), # LATIN SMALL LETTER B WITH DOT BELOW
    ('[B=]',    '\u1E06', '\\u1E06', 0), # LATIN CAPITAL LETTER B WITH LINE BELOW
    ('[b=]',    '\u1E07', '\\u1E07', 0), # LATIN SMALL LETTER B WITH LINE BELOW
    ('[\'C,]',  '\u1E08', '\\u1E08', 0), # LATIN CAPITAL LETTER C WITH CEDILLA AND ACUTE
    ('[\'c,]',  '\u1E09', '\\u1E09', 0), # LATIN SMALL LETTER C WITH CEDILLA AND ACUTE
    ('[.D]',    '\u1E0A', '\\u1E0A', 0), # LATIN CAPITAL LETTER D WITH DOT ABOVE
    ('[.d]',    '\u1E0B', '\\u1E0B', 0), # LATIN SMALL LETTER D WITH DOT ABOVE
    ('[D.]',    '\u1E0C', '\\u1E0C', 0), # LATIN CAPITAL LETTER D WITH DOT BELOW
    ('[d.]',    '\u1E0D', '\\u1E0D', 0), # LATIN SMALL LETTER D WITH DOT BELOW
    ('[D=]',    '\u1E0E', '\\u1E0E', 0), # LATIN CAPITAL LETTER D WITH LINE BELOW
    ('[d=]',    '\u1E0F', '\\u1E0F', 0), # LATIN SMALL LETTER D WITH LINE BELOW
    ('[D,]',    '\u1E10', '\\u1E10', 0), # LATIN CAPITAL LETTER D WITH CEDILLA
    ('[d,]',    '\u1E11', '\\u1E11', 0), # LATIN SMALL LETTER D WITH CEDILLA
    ('[D^]',    '\u1E12', '\\u1E12', 0), # LATIN CAPITAL LETTER D WITH CIRCUMFLEX BELOW
    ('[d^]',    '\u1E13', '\\u1E13', 0), # LATIN SMALL LETTER D WITH CIRCUMFLEX BELOW
    ('[`=E]',   '\u1E14', '\\u1E14', 0), # LATIN CAPITAL LETTER E WITH MACRON AND GRAVE
    ('[`=e]',   '\u1E15', '\\u1E15', 0), # LATIN SMALL LETTER E WITH MACRON AND GRAVE
    ('[\'=E]',  '\u1E16', '\\u1E16', 0), # LATIN CAPITAL LETTER E WITH MACRON AND ACUTE
    ('[=É]',    '\u1E16', '\\u1E16', 1), # LATIN CAPITAL LETTER E WITH MACRON AND ACUTE
    ('[\'=e]',  '\u1E17', '\\u1E17', 0), # LATIN SMALL LETTER E WITH MACRON AND ACUTE
    ('[=é]',    '\u1E17', '\\u1E17', 1), # LATIN SMALL LETTER E WITH MACRON AND ACUTE
    ('[E^]',    '\u1E18', '\\u1E18', 0), # LATIN CAPITAL LETTER E WITH CIRCUMFLEX BELOW
    ('[e^]',    '\u1E19', '\\u1E19', 0), # LATIN SMALL LETTER E WITH CIRCUMFLEX BELOW
    ('[E~]',    '\u1E1A', '\\u1E1A', 0), # LATIN CAPITAL LETTER E WITH TILDE BELOW
    ('[e~]',    '\u1E1B', '\\u1E1B', 0), # LATIN SMALL LETTER E WITH TILDE BELOW
    ('[)E,]',   '\u1E1C', '\\u1E1C', 0), # LATIN CAPITAL LETTER E WITH CEDILLA AND BREVE
    ('[)e,]',   '\u1E1D', '\\u1E1D', 0), # LATIN SMALL LETTER E WITH CEDILLA AND BREVE
    ('[.F]',    '\u1E1E', '\\u1E1E', 0), # LATIN CAPITAL LETTER F WITH DOT ABOVE
    ('[.f]',    '\u1E1F', '\\u1E1F', 0), # LATIN SMALL LETTER F WITH DOT ABOVE
    ('[=G]',    '\u1E20', '\\u1E20', 0), # LATIN CAPITAL LETTER G WITH MACRON
    ('[=g]',    '\u1E21', '\\u1E21', 0), # LATIN SMALL LETTER G WITH MACRON
    ('[.H]',    '\u1E22', '\\u1E22', 0), # LATIN CAPITAL LETTER H WITH DOT ABOVE
    ('[.h]',    '\u1E23', '\\u1E23', 0), # LATIN SMALL LETTER H WITH DOT ABOVE
    ('[H.]',    '\u1E24', '\\u1E24', 0), # LATIN CAPITAL LETTER H WITH DOT BELOW
    ('[h.]',    '\u1E25', '\\u1E25', 0), # LATIN SMALL LETTER H WITH DOT BELOW
    ('[:H]',    '\u1E26', '\\u1E26', 0), # LATIN CAPITAL LETTER H WITH DIAERESIS
    ('[:h]',    '\u1E27', '\\u1E27', 0), # LATIN SMALL LETTER H WITH DIAERESIS
    ('[H,]',    '\u1E28', '\\u1E28', 0), # LATIN CAPITAL LETTER H WITH CEDILLA
    ('[h,]',    '\u1E29', '\\u1E29', 0), # LATIN SMALL LETTER H WITH CEDILLA
    ('[H)]',    '\u1E2A', '\\u1E2A', 0), # LATIN CAPITAL LETTER H WITH BREVE BELOW
    ('[h)]',    '\u1E2B', '\\u1E2B', 0), # LATIN SMALL LETTER H WITH BREVE BELOW
    ('[I~]',    '\u1E2C', '\\u1E2C', 0), # LATIN CAPITAL LETTER I WITH TILDE BELOW
    ('[i~]',    '\u1E2D', '\\u1E2D', 0), # LATIN SMALL LETTER I WITH TILDE BELOW
    ('[\'Ï]',   '\u1E2E', '\\u1E2E', 0), # LATIN CAPITAL LETTER I WITH DIAERESIS AND ACUTE
    ('[:Í]',    '\u1E2E', '\\u1E2E', 1), # LATIN CAPITAL LETTER I WITH DIAERESIS AND ACUTE
    ('[\'ï]',   '\u1E2F', '\\u1E2F', 0), # LATIN SMALL LETTER I WITH DIAERESIS AND ACUTE
    ('[:í]',    '\u1E2F', '\\u1E2F', 1), # LATIN SMALL LETTER I WITH DIAERESIS AND ACUTE
    ('[\'K]',   '\u1E30', '\\u1E30', 0), # LATIN CAPITAL LETTER K WITH ACUTE
    ('[\'k]',   '\u1E31', '\\u1E31', 0), # LATIN SMALL LETTER K WITH ACUTE
    ('[K.]',    '\u1E32', '\\u1E32', 0), # LATIN CAPITAL LETTER K WITH DOT BELOW
    ('[k.]',    '\u1E33', '\\u1E33', 0), # LATIN SMALL LETTER K WITH DOT BELOW
    ('[K=]',    '\u1E34', '\\u1E34', 0), # LATIN CAPITAL LETTER K WITH LINE BELOW
    ('[k=]',    '\u1E35', '\\u1E35', 0), # LATIN SMALL LETTER K WITH LINE BELOW
    ('[L.]',    '\u1E36', '\\u1E36', 0), # LATIN CAPITAL LETTER L WITH DOT BELOW
    ('[l.]',    '\u1E37', '\\u1E37', 0), # LATIN SMALL LETTER L WITH DOT BELOW
    ('[=L.]',   '\u1E38', '\\u1E38', 0), # LATIN CAPITAL LETTER L WITH DOT BELOW AND MACRON
    ('[=l.]',   '\u1E39', '\\u1E39', 0), # LATIN SMALL LETTER L WITH DOT BELOW AND MACRON
    ('[L=]',    '\u1E3A', '\\u1E3A', 0), # LATIN CAPITAL LETTER L WITH LINE BELOW
    ('[l=]',    '\u1E3B', '\\u1E3B', 0), # LATIN SMALL LETTER L WITH LINE BELOW
    ('[L^]',    '\u1E3C', '\\u1E3C', 0), # LATIN CAPITAL LETTER L WITH CIRCUMFLEX BELOW
    ('[l^]',    '\u1E3D', '\\u1E3D', 0), # LATIN SMALL LETTER L WITH CIRCUMFLEX BELOW
    ('[\'M]',   '\u1E3E', '\\u1E3E', 0), # LATIN CAPITAL LETTER M WITH ACUTE
    ('[\'m]',   '\u1E3F', '\\u1E3F', 0), # LATIN SMALL LETTER M WITH ACUTE
    ('[.M]',    '\u1E40', '\\u1E40', 0), # LATIN CAPITAL LETTER M WITH DOT ABOVE
    ('[.m]',    '\u1E41', '\\u1E41', 0), # LATIN SMALL LETTER M WITH DOT ABOVE
    ('[M.]',    '\u1E42', '\\u1E42', 0), # LATIN CAPITAL LETTER M WITH DOT BELOW
    ('[m.]',    '\u1E43', '\\u1E43', 0), # LATIN SMALL LETTER M WITH DOT BELOW
    ('[.N]',    '\u1E44', '\\u1E44', 0), # LATIN CAPITAL LETTER N WITH DOT ABOVE
    ('[.n]',    '\u1E45', '\\u1E45', 0), # LATIN SMALL LETTER N WITH DOT ABOVE
    ('[N.]',    '\u1E46', '\\u1E46', 0), # LATIN CAPITAL LETTER N WITH DOT BELOW
    ('[n.]',    '\u1E47', '\\u1E47', 0), # LATIN SMALL LETTER N WITH DOT BELOW
    ('[N=]',    '\u1E48', '\\u1E48', 0), # LATIN CAPITAL LETTER N WITH LINE BELOW
    ('[n=]',    '\u1E49', '\\u1E49', 0), # LATIN SMALL LETTER N WITH LINE BELOW
    ('[N^]',    '\u1E4A', '\\u1E4A', 0), # LATIN CAPITAL LETTER N WITH CIRCUMFLEX BELOW
    ('[n^]',    '\u1E4B', '\\u1E4B', 0), # LATIN SMALL LETTER N WITH CIRCUMFLEX BELOW
    ('[\'Õ]',   '\u1E4C', '\\u1E4C', 0), # LATIN CAPITAL LETTER O WITH TILDE AND ACUTE
    ('[\'~O]',  '\u1E4C', '\\u1E4C', 1), # LATIN CAPITAL LETTER O WITH TILDE AND ACUTE
    ('[~\'O]',  '\u1E4C', '\\u1E4C', 1), # LATIN CAPITAL LETTER O WITH TILDE AND ACUTE
    ('[~Ó]',    '\u1E4C', '\\u1E4C', 1), # LATIN CAPITAL LETTER O WITH TILDE AND ACUTE
    ('[\'õ]',   '\u1E4D', '\\u1E4D', 0), # LATIN SMALL LETTER O WITH TILDE AND ACUTE
    ('[\'~o]',  '\u1E4D', '\\u1E4D', 1), # LATIN SMALL LETTER O WITH TILDE AND ACUTE
    ('[~\'o]',  '\u1E4D', '\\u1E4D', 1), # LATIN SMALL LETTER O WITH TILDE AND ACUTE
    ('[~ó]',    '\u1E4D', '\\u1E4D', 1), # LATIN SMALL LETTER O WITH TILDE AND ACUTE
    ('[:Õ]',    '\u1E4E', '\\u1E4E', 0), # LATIN CAPITAL LETTER O WITH TILDE AND DIAERESIS
    ('[~Ö]',    '\u1E4E', '\\u1E4E', 1), # LATIN CAPITAL LETTER O WITH TILDE AND DIAERESIS
    ('[~:O]',   '\u1E4E', '\\u1E4E', 1), # LATIN CAPITAL LETTER O WITH TILDE AND DIAERESIS
    ('[:~O]',   '\u1E4E', '\\u1E4E', 1), # LATIN CAPITAL LETTER O WITH TILDE AND DIAERESIS
    ('[:õ]',    '\u1E4F', '\\u1E4F', 0), # LATIN SMALL LETTER O WITH TILDE AND DIAERESIS
    ('[~ö]',    '\u1E4F', '\\u1E4F', 1), # LATIN SMALL LETTER O WITH TILDE AND DIAERESIS
    ('[~:o]',   '\u1E4F', '\\u1E4F', 1), # LATIN SMALL LETTER O WITH TILDE AND DIAERESIS
    ('[:~o]',   '\u1E4F', '\\u1E4F', 1), # LATIN SMALL LETTER O WITH TILDE AND DIAERESIS
    ('[`=O]',   '\u1E50', '\\u1E50', 0), # LATIN CAPITAL LETTER O WITH MACRON AND GRAVE
    ('[=`O]',   '\u1E50', '\\u1E50', 1), # LATIN CAPITAL LETTER O WITH MACRON AND GRAVE
    ('[=Ò]',    '\u1E50', '\\u1E50', 1), # LATIN CAPITAL LETTER O WITH MACRON AND GRAVE
    ('[`=o]',   '\u1E51', '\\u1E51', 0), # LATIN SMALL LETTER O WITH MACRON AND GRAVE
    ('[=`o]',   '\u1E51', '\\u1E51', 1), # LATIN SMALL LETTER O WITH MACRON AND GRAVE
    ('[=ò]',    '\u1E51', '\\u1E51', 1), # LATIN SMALL LETTER O WITH MACRON AND GRAVE
    ('[\'=O]',  '\u1E52', '\\u1E52', 0), # LATIN CAPITAL LETTER O WITH MACRON AND ACUTE
    ('[=\'O]',  '\u1E52', '\\u1E52', 1), # LATIN CAPITAL LETTER O WITH MACRON AND ACUTE
    ('[=Ó]',    '\u1E52', '\\u1E52', 1), # LATIN CAPITAL LETTER O WITH MACRON AND ACUTE
    ('[\'=o]',  '\u1E53', '\\u1E53', 0), # LATIN SMALL LETTER O WITH MACRON AND ACUTE
    ('[=\'o]',  '\u1E53', '\\u1E53', 1), # LATIN SMALL LETTER O WITH MACRON AND ACUTE
    ('[=ó]',    '\u1E53', '\\u1E53', 1), # LATIN SMALL LETTER O WITH MACRON AND ACUTE
    ('[\'P]',   '\u1E54', '\\u1E54', 0), # LATIN CAPITAL LETTER P WITH ACUTE
    ('[\'p]',   '\u1E55', '\\u1E55', 0), # LATIN SMALL LETTER P WITH ACUTE
    ('[.P]',    '\u1E56', '\\u1E56', 0), # LATIN CAPITAL LETTER P WITH DOT ABOVE
    ('[.p]',    '\u1E57', '\\u1E57', 0), # LATIN SMALL LETTER P WITH DOT ABOVE
    ('[.R]',    '\u1E58', '\\u1E58', 0), # LATIN CAPITAL LETTER R WITH DOT ABOVE
    ('[.r]',    '\u1E59', '\\u1E59', 0), # LATIN SMALL LETTER R WITH DOT ABOVE
    ('[R.]',    '\u1E5A', '\\u1E5A', 0), # LATIN CAPITAL LETTER R WITH DOT BELOW
    ('[r.]',    '\u1E5B', '\\u1E5B', 0), # LATIN SMALL LETTER R WITH DOT BELOW
    ('[=R.]',   '\u1E5C', '\\u1E5C', 0), # LATIN CAPITAL LETTER R WITH DOT BELOW AND MACRON
    ('[=r.]',   '\u1E5D', '\\u1E5D', 0), # LATIN SMALL LETTER R WITH DOT BELOW AND MACRON
    ('[R=]',    '\u1E5E', '\\u1E5E', 0), # LATIN CAPITAL LETTER R WITH LINE BELOW
    ('[r=]',    '\u1E5F', '\\u1E5F', 0), # LATIN SMALL LETTER R WITH LINE BELOW
    ('[.S]',    '\u1E60', '\\u1E60', 0), # LATIN CAPITAL LETTER S WITH DOT ABOVE
    ('[.s]',    '\u1E61', '\\u1E61', 0), # LATIN SMALL LETTER S WITH DOT ABOVE
    ('[S.]',    '\u1E62', '\\u1E62', 0), # LATIN CAPITAL LETTER S WITH DOT BELOW
    ('[s.]',    '\u1E63', '\\u1E63', 0), # LATIN SMALL LETTER S WITH DOT BELOW
    ('[.\'S]',  '\u1E64', '\\u1E64', 0), # LATIN CAPITAL LETTER S WITH ACUTE AND DOT ABOVE
    ('[.\'s]',  '\u1E65', '\\u1E65', 0), # LATIN SMALL LETTER S WITH ACUTE AND DOT ABOVE
    ('[.vS]',   '\u1E66', '\\u1E66', 0), # LATIN CAPITAL LETTER S WITH CARON AND DOT ABOVE
    ('[.vs]',   '\u1E67', '\\u1E67', 0), # LATIN SMALL LETTER S WITH CARON AND DOT ABOVE
    ('[.S.]',   '\u1E68', '\\u1E68', 0), # LATIN CAPITAL LETTER S WITH DOT BELOW AND DOT ABOVE
    ('[.s.]',   '\u1E69', '\\u1E69', 0), # LATIN SMALL LETTER S WITH DOT BELOW AND DOT ABOVE
    ('[.T]',    '\u1E6A', '\\u1E6A', 0), # LATIN CAPITAL LETTER T WITH DOT ABOVE
    ('[.t]',    '\u1E6B', '\\u1E6B', 0), # LATIN SMALL LETTER T WITH DOT ABOVE
    ('[T.]',    '\u1E6C', '\\u1E6C', 0), # LATIN CAPITAL LETTER T WITH DOT BELOW
    ('[t.]',    '\u1E6D', '\\u1E6D', 0), # LATIN SMALL LETTER T WITH DOT BELOW
    ('[T=]',    '\u1E6E', '\\u1E6E', 0), # LATIN CAPITAL LETTER T WITH LINE BELOW
    ('[t=]',    '\u1E6F', '\\u1E6F', 0), # LATIN SMALL LETTER T WITH LINE BELOW
    ('[T^]',    '\u1E70', '\\u1E70', 0), # LATIN CAPITAL LETTER T WITH CIRCUMFLEX BELOW
    ('[t^]',    '\u1E71', '\\u1E71', 0), # LATIN SMALL LETTER T WITH CIRCUMFLEX BELOW
    ('[U:]',    '\u1E72', '\\u1E72', 0), # LATIN CAPITAL LETTER U WITH DIAERESIS BELOW
    ('[u:]',    '\u1E73', '\\u1E73', 0), # LATIN SMALL LETTER U WITH DIAERESIS BELOW
    ('[U~]',    '\u1E74', '\\u1E74', 0), # LATIN CAPITAL LETTER U WITH TILDE BELOW
    ('[u~]',    '\u1E75', '\\u1E75', 0), # LATIN SMALL LETTER U WITH TILDE BELOW
    ('[U^]',    '\u1E76', '\\u1E76', 0), # LATIN CAPITAL LETTER U WITH CIRCUMFLEX BELOW
    ('[u^]',    '\u1E77', '\\u1E77', 0), # LATIN SMALL LETTER U WITH CIRCUMFLEX BELOW
    ('[\'~U]',  '\u1E78', '\\u1E78', 0), # LATIN CAPITAL LETTER U WITH TILDE AND ACUTE
    ('[~\'U]',  '\u1E78', '\\u1E78', 1), # LATIN CAPITAL LETTER U WITH TILDE AND ACUTE
    ('[~Ú]',    '\u1E78', '\\u1E78', 1), # LATIN CAPITAL LETTER U WITH TILDE AND ACUTE
    ('[\'~u]',  '\u1E79', '\\u1E79', 0), # LATIN SMALL LETTER U WITH TILDE AND ACUTE
    ('[~\'u]',  '\u1E79', '\\u1E79', 1), # LATIN SMALL LETTER U WITH TILDE AND ACUTE
    ('[~ú]',    '\u1E79', '\\u1E79', 1), # LATIN SMALL LETTER U WITH TILDE AND ACUTE
    ('[:=U]',   '\u1E7A', '\\u1E7A', 0), # LATIN CAPITAL LETTER U WITH MACRON AND DIAERESIS
    ('[=Ü]',    '\u1E7A', '\\u1E7A', 1), # LATIN CAPITAL LETTER U WITH MACRON AND DIAERESIS
    ('[:=u]',   '\u1E7B', '\\u1E7B', 0), # LATIN SMALL LETTER U WITH MACRON AND DIAERESIS
    ('[=ü]',    '\u1E7B', '\\u1E7B', 1), # LATIN SMALL LETTER U WITH MACRON AND DIAERESIS
    ('[~V]',    '\u1E7C', '\\u1E7C', 0), # LATIN CAPITAL LETTER V WITH TILDE
    ('[~v]',    '\u1E7D', '\\u1E7D', 0), # LATIN SMALL LETTER V WITH TILDE
    ('[V.]',    '\u1E7E', '\\u1E7E', 0), # LATIN CAPITAL LETTER V WITH DOT BELOW
    ('[v.]',    '\u1E7F', '\\u1E7F', 0), # LATIN SMALL LETTER V WITH DOT BELOW
    ('[`W]',    '\u1E80', '\\u1E80', 0), # LATIN CAPITAL LETTER W WITH GRAVE
    ('[`w]',    '\u1E81', '\\u1E81', 0), # LATIN SMALL LETTER W WITH GRAVE
    ('[\'W]',   '\u1E82', '\\u1E82', 0), # LATIN CAPITAL LETTER W WITH ACUTE
    ('[\'w]',   '\u1E83', '\\u1E83', 0), # LATIN SMALL LETTER W WITH ACUTE
    ('[:W]',    '\u1E84', '\\u1E84', 0), # LATIN CAPITAL LETTER W WITH DIAERESIS
    ('[:w]',    '\u1E85', '\\u1E85', 0), # LATIN SMALL LETTER W WITH DIAERESIS
    ('[.W]',    '\u1E86', '\\u1E86', 0), # LATIN CAPITAL LETTER W WITH DOT ABOVE
    ('[.w]',    '\u1E87', '\\u1E87', 0), # LATIN SMALL LETTER W WITH DOT ABOVE
    ('[W.]',    '\u1E88', '\\u1E88', 0), # LATIN CAPITAL LETTER W WITH DOT BELOW
    ('[w.]',    '\u1E89', '\\u1E89', 0), # LATIN SMALL LETTER W WITH DOT BELOW
    ('[.X]',    '\u1E8A', '\\u1E8A', 0), # LATIN CAPITAL LETTER X WITH DOT ABOVE
    ('[.x]',    '\u1E8B', '\\u1E8B', 0), # LATIN SMALL LETTER X WITH DOT ABOVE
    ('[:X]',    '\u1E8C', '\\u1E8C', 0), # LATIN CAPITAL LETTER X WITH DIAERESIS
    ('[:x]',    '\u1E8D', '\\u1E8D', 0), # LATIN SMALL LETTER X WITH DIAERESIS
    ('[.Y]',    '\u1E8E', '\\u1E8E', 0), # LATIN CAPITAL LETTER Y WITH DOT ABOVE
    ('[.y]',    '\u1E8F', '\\u1E8F', 0), # LATIN SMALL LETTER Y WITH DOT ABOVE
    ('[^Z]',    '\u1E90', '\\u1E90', 0), # LATIN CAPITAL LETTER Z WITH CIRCUMFLEX
    ('[^z]',    '\u1E91', '\\u1E91', 0), # LATIN SMALL LETTER Z WITH CIRCUMFLEX
    ('[Z.]',    '\u1E92', '\\u1E92', 0), # LATIN CAPITAL LETTER Z WITH DOT BELOW
    ('[z.]',    '\u1E93', '\\u1E93', 0), # LATIN SMALL LETTER Z WITH DOT BELOW
    ('[Z=]',    '\u1E94', '\\u1E94', 0), # LATIN CAPITAL LETTER Z WITH LINE BELOW
    ('[z=]',    '\u1E95', '\\u1E95', 0), # LATIN SMALL LETTER Z WITH LINE BELOW
    ('[h=]',    '\u1E96', '\\u1E96', 0), # LATIN SMALL LETTER H WITH LINE BELOW
    ('[:t]',    '\u1E97', '\\u1E97', 0), # LATIN SMALL LETTER T WITH DIAERESIS
    ('[°w]',    '\u1E98', '\\u1E98', 0), # LATIN SMALL LETTER W WITH RING ABOVE
    ('[°y]',    '\u1E99', '\\u1E99', 0), # LATIN SMALL LETTER Y WITH RING ABOVE
    #('[]', '\u1E9A', '\\u1E9A', 0), # LATIN SMALL LETTER A WITH RIGHT HALF RING
    ('[.[s]]',  '\u1E9B', '\\u1E9B', 0), # LATIN SMALL LETTER LONG S WITH DOT ABOVE
    ('[/[s]]',  '\u1E9C', '\\u1E9C', 0), # LATIN SMALL LETTER LONG S WITH DIAGONAL STROKE
    ('[-[s]]',  '\u1E9D', '\\u1E9D', 0), # LATIN SMALL LETTER LONG S WITH HIGH STROKE
    #('[]', '\u1E9E', '\\u1E9E', 0), # LATIN CAPITAL LETTER SHARP S
    #('[delta]', '\u1E9F', '\\u1E9F', 0), # LATIN SMALL LETTER DELTA    (use Greek versions instead)
    ('[A.]',    '\u1EA0', '\\u1EA0', 0), # LATIN CAPITAL LETTER A WITH DOT BELOW
    ('[a.]',    '\u1EA1', '\\u1EA1', 0), # LATIN SMALL LETTER A WITH DOT BELOW
    ('[,A]',    '\u1EA2', '\\u1EA2', 0), # LATIN CAPITAL LETTER A WITH HOOK ABOVE
    ('[,a]',    '\u1EA3', '\\u1EA3', 0), # LATIN SMALL LETTER A WITH HOOK ABOVE
    ('[\'Â]',   '\u1EA4', '\\u1EA4', 0), # LATIN CAPITAL LETTER A WITH CIRCUMFLEX AND ACUTE
    ('[^\'A]',  '\u1EA4', '\\u1EA4', 1), # LATIN CAPITAL LETTER A WITH CIRCUMFLEX AND ACUTE
    ('[^Á]',    '\u1EA4', '\\u1EA4', 1), # LATIN CAPITAL LETTER A WITH CIRCUMFLEX AND ACUTE
    ('[\'â]',   '\u1EA5', '\\u1EA5', 0), # LATIN SMALL LETTER A WITH CIRCUMFLEX AND ACUTE
    ('[^\'a]',  '\u1EA5', '\\u1EA5', 1), # LATIN SMALL LETTER A WITH CIRCUMFLEX AND ACUTE
    ('[^á]',    '\u1EA5', '\\u1EA5', 1), # LATIN SMALL LETTER A WITH CIRCUMFLEX AND ACUTE
    ('[`Â]',    '\u1EA6', '\\u1EA6', 0), # LATIN CAPITAL LETTER A WITH CIRCUMFLEX AND GRAVE
    ('[`^A]',   '\u1EA6', '\\u1EA6', 1), # LATIN CAPITAL LETTER A WITH CIRCUMFLEX AND GRAVE
    ('[^`A]',   '\u1EA6', '\\u1EA6', 1), # LATIN CAPITAL LETTER A WITH CIRCUMFLEX AND GRAVE
    ('[^À]',    '\u1EA6', '\\u1EA6', 1), # LATIN CAPITAL LETTER A WITH CIRCUMFLEX AND GRAVE
    ('[`â]',    '\u1EA7', '\\u1EA7', 0), # LATIN SMALL LETTER A WITH CIRCUMFLEX AND GRAVE
    ('[^`a]',   '\u1EA7', '\\u1EA7', 1), # LATIN SMALL LETTER A WITH CIRCUMFLEX AND GRAVE
    ('[`^a]',   '\u1EA7', '\\u1EA7', 1), # LATIN SMALL LETTER A WITH CIRCUMFLEX AND GRAVE
    ('[^à]',    '\u1EA7', '\\u1EA7', 1), # LATIN SMALL LETTER A WITH CIRCUMFLEX AND GRAVE
    ('[,Â]',    '\u1EA8', '\\u1EA8', 0), # LATIN CAPITAL LETTER A WITH CIRCUMFLEX AND HOOK ABOVE
    ('[^,A]',   '\u1EA8', '\\u1EA8', 1), # LATIN CAPITAL LETTER A WITH CIRCUMFLEX AND HOOK ABOVE
    ('[,^A]',   '\u1EA8', '\\u1EA8', 1), # LATIN CAPITAL LETTER A WITH CIRCUMFLEX AND HOOK ABOVE
    ('[,â]',    '\u1EA9', '\\u1EA9', 0), # LATIN SMALL LETTER A WITH CIRCUMFLEX AND HOOK ABOVE
    ('[,^a]',   '\u1EA9', '\\u1EA9', 1), # LATIN SMALL LETTER A WITH CIRCUMFLEX AND HOOK ABOVE
    ('[^,a]',   '\u1EA9', '\\u1EA9', 1), # LATIN SMALL LETTER A WITH CIRCUMFLEX AND HOOK ABOVE
    ('[~Â]',    '\u1EAA', '\\u1EAA', 0), # LATIN CAPITAL LETTER A WITH CIRCUMFLEX AND TILDE
    ('[~^A]',   '\u1EAA', '\\u1EAA', 1), # LATIN CAPITAL LETTER A WITH CIRCUMFLEX AND TILDE
    ('[^~A]',   '\u1EAA', '\\u1EAA', 1), # LATIN CAPITAL LETTER A WITH CIRCUMFLEX AND TILDE
    ('[^Ã]',    '\u1EAA', '\\u1EAA', 1), # LATIN CAPITAL LETTER A WITH CIRCUMFLEX AND TILDE
    ('[~â]',    '\u1EAB', '\\u1EAB', 0), # LATIN SMALL LETTER A WITH CIRCUMFLEX AND TILDE
    ('[~^a]',   '\u1EAB', '\\u1EAB', 1), # LATIN SMALL LETTER A WITH CIRCUMFLEX AND TILDE
    ('[^~a]',   '\u1EAB', '\\u1EAB', 1), # LATIN SMALL LETTER A WITH CIRCUMFLEX AND TILDE
    ('[^ã]',    '\u1EAB', '\\u1EAB', 1), # LATIN SMALL LETTER A WITH CIRCUMFLEX AND TILDE
    ('[Â.]',    '\u1EAC', '\\u1EAC', 0), # LATIN CAPITAL LETTER A WITH CIRCUMFLEX AND DOT BELOW
    ('[^A.]',   '\u1EAC', '\\u1EAC', 1), # LATIN CAPITAL LETTER A WITH CIRCUMFLEX AND DOT BELOW
    ('[â.]',    '\u1EAD', '\\u1EAD', 0), # LATIN SMALL LETTER A WITH CIRCUMFLEX AND DOT BELOW
    ('[^a.]',   '\u1EAD', '\\u1EAD', 1), # LATIN SMALL LETTER A WITH CIRCUMFLEX AND DOT BELOW
    ('[\')A]',  '\u1EAE', '\\u1EAE', 0), # LATIN CAPITAL LETTER A WITH BREVE AND ACUTE
    ('[)\'A]',  '\u1EAE', '\\u1EAE', 1), # LATIN CAPITAL LETTER A WITH BREVE AND ACUTE
    ('[)Á]',    '\u1EAE', '\\u1EAE', 1), # LATIN CAPITAL LETTER A WITH BREVE AND ACUTE
    ('[\')a]',  '\u1EAF', '\\u1EAF', 0), # LATIN SMALL LETTER A WITH BREVE AND ACUTE
    ('[)\'a]',  '\u1EAF', '\\u1EAF', 1), # LATIN SMALL LETTER A WITH BREVE AND ACUTE
    ('[)á]',    '\u1EAF', '\\u1EAF', 1), # LATIN SMALL LETTER A WITH BREVE AND ACUTE
    ('[`)A]',   '\u1EB0', '\\u1EB0', 0), # LATIN CAPITAL LETTER A WITH BREVE AND GRAVE
    ('[)`A]',   '\u1EB0', '\\u1EB0', 1), # LATIN CAPITAL LETTER A WITH BREVE AND GRAVE
    ('[)À]',    '\u1EB0', '\\u1EB0', 1), # LATIN CAPITAL LETTER A WITH BREVE AND GRAVE
    ('[`)a]',   '\u1EB1', '\\u1EB1', 0), # LATIN SMALL LETTER A WITH BREVE AND GRAVE
    ('[)`a]',   '\u1EB1', '\\u1EB1', 1), # LATIN SMALL LETTER A WITH BREVE AND GRAVE
    ('[)à]',    '\u1EB1', '\\u1EB1', 1), # LATIN SMALL LETTER A WITH BREVE AND GRAVE
    ('[,)A]',   '\u1EB2', '\\u1EB2', 0), # LATIN CAPITAL LETTER A WITH BREVE AND HOOK ABOVE
    ('[),A]',   '\u1EB2', '\\u1EB2', 1), # LATIN CAPITAL LETTER A WITH BREVE AND HOOK ABOVE
    ('[,)a]',   '\u1EB3', '\\u1EB3', 0), # LATIN SMALL LETTER A WITH BREVE AND HOOK ABOVE
    ('[),a]',   '\u1EB3', '\\u1EB3', 1), # LATIN SMALL LETTER A WITH BREVE AND HOOK ABOVE
    ('[~)A]',   '\u1EB4', '\\u1EB4', 0), # LATIN CAPITAL LETTER A WITH BREVE AND TILDE
    ('[)~A]',   '\u1EB4', '\\u1EB4', 1), # LATIN CAPITAL LETTER A WITH BREVE AND TILDE
    ('[)Ã]',    '\u1EB4', '\\u1EB4', 1), # LATIN CAPITAL LETTER A WITH BREVE AND TILDE
    ('[~)a]',   '\u1EB5', '\\u1EB5', 0), # LATIN SMALL LETTER A WITH BREVE AND TILDE
    ('[)~a]',   '\u1EB5', '\\u1EB5', 1), # LATIN SMALL LETTER A WITH BREVE AND TILDE
    ('[)ã]',    '\u1EB5', '\\u1EB5', 1), # LATIN SMALL LETTER A WITH BREVE AND TILDE
    ('[)A.]',   '\u1EB6', '\\u1EB6', 0), # LATIN CAPITAL LETTER A WITH BREVE AND DOT BELOW
    ('[)a.]',   '\u1EB7', '\\u1EB7', 0), # LATIN SMALL LETTER A WITH BREVE AND DOT BELOW
    ('[E.]',    '\u1EB8', '\\u1EB8', 0), # LATIN CAPITAL LETTER E WITH DOT BELOW
    ('[e.]',    '\u1EB9', '\\u1EB9', 0), # LATIN SMALL LETTER E WITH DOT BELOW
    ('[,E]',    '\u1EBA', '\\u1EBA', 0), # LATIN CAPITAL LETTER E WITH HOOK ABOVE
    ('[,e]',    '\u1EBB', '\\u1EBB', 0), # LATIN SMALL LETTER E WITH HOOK ABOVE
    ('[~E]',    '\u1EBC', '\\u1EBC', 0), # LATIN CAPITAL LETTER E WITH TILDE
    ('[~e]',    '\u1EBD', '\\u1EBD', 0), # LATIN SMALL LETTER E WITH TILDE
    ('[\'Ê]',   '\u1EBE', '\\u1EBE', 0), # LATIN CAPITAL LETTER E WITH CIRCUMFLEX AND ACUTE
    ('[^\'E]',  '\u1EBE', '\\u1EBE', 1), # LATIN CAPITAL LETTER E WITH CIRCUMFLEX AND ACUTE
    ('[^É]',    '\u1EBE', '\\u1EBE', 1), # LATIN CAPITAL LETTER E WITH CIRCUMFLEX AND ACUTE
    ('[\'ê]',   '\u1EBF', '\\u1EBF', 0), # LATIN SMALL LETTER E WITH CIRCUMFLEX AND ACUTE
    ('[^\'e]',  '\u1EBF', '\\u1EBF', 1), # LATIN SMALL LETTER E WITH CIRCUMFLEX AND ACUTE
    ('[^é]',    '\u1EBF', '\\u1EBF', 1), # LATIN SMALL LETTER E WITH CIRCUMFLEX AND ACUTE
    ('[`Ê]',    '\u1EC0', '\\u1EC0', 0), # LATIN CAPITAL LETTER E WITH CIRCUMFLEX AND GRAVE
    ('[^`E]',   '\u1EC0', '\\u1EC0', 1), # LATIN CAPITAL LETTER E WITH CIRCUMFLEX AND GRAVE
    ('[`^E]',   '\u1EC0', '\\u1EC0', 1), # LATIN CAPITAL LETTER E WITH CIRCUMFLEX AND GRAVE
    ('[^È]',    '\u1EC0', '\\u1EC0', 1), # LATIN CAPITAL LETTER E WITH CIRCUMFLEX AND GRAVE
    ('[`ê]',    '\u1EC1', '\\u1EC1', 0), # LATIN SMALL LETTER E WITH CIRCUMFLEX AND GRAVE
    ('[^`e]',   '\u1EC1', '\\u1EC1', 1), # LATIN SMALL LETTER E WITH CIRCUMFLEX AND GRAVE
    ('[`^e]',   '\u1EC1', '\\u1EC1', 1), # LATIN SMALL LETTER E WITH CIRCUMFLEX AND GRAVE
    ('[^è]',    '\u1EC1', '\\u1EC1', 1), # LATIN SMALL LETTER E WITH CIRCUMFLEX AND GRAVE
    ('[,Ê]',    '\u1EC2', '\\u1EC2', 0), # LATIN CAPITAL LETTER E WITH CIRCUMFLEX AND HOOK ABOVE
    ('[,^E]',   '\u1EC2', '\\u1EC2', 1), # LATIN CAPITAL LETTER E WITH CIRCUMFLEX AND HOOK ABOVE
    ('[^,E]',   '\u1EC2', '\\u1EC2', 1), # LATIN CAPITAL LETTER E WITH CIRCUMFLEX AND HOOK ABOVE
    ('[,ê]',    '\u1EC3', '\\u1EC3', 0), # LATIN SMALL LETTER E WITH CIRCUMFLEX AND HOOK ABOVE
    ('[,^e]',   '\u1EC3', '\\u1EC3', 1), # LATIN SMALL LETTER E WITH CIRCUMFLEX AND HOOK ABOVE
    ('[^,e]',   '\u1EC3', '\\u1EC3', 1), # LATIN SMALL LETTER E WITH CIRCUMFLEX AND HOOK ABOVE
    ('[~Ê]',    '\u1EC4', '\\u1EC4', 0), # LATIN CAPITAL LETTER E WITH CIRCUMFLEX AND TILDE
    ('[~^E]',   '\u1EC4', '\\u1EC4', 1), # LATIN CAPITAL LETTER E WITH CIRCUMFLEX AND TILDE
    ('[^~E]',   '\u1EC4', '\\u1EC4', 1), # LATIN CAPITAL LETTER E WITH CIRCUMFLEX AND TILDE
    ('[~ê]',    '\u1EC5', '\\u1EC5', 0), # LATIN SMALL LETTER E WITH CIRCUMFLEX AND TILDE
    ('[~^e]',   '\u1EC5', '\\u1EC5', 1), # LATIN SMALL LETTER E WITH CIRCUMFLEX AND TILDE
    ('[^~e]',   '\u1EC5', '\\u1EC5', 1), # LATIN SMALL LETTER E WITH CIRCUMFLEX AND TILDE
    ('[Ê.]',    '\u1EC6', '\\u1EC6', 0), # LATIN CAPITAL LETTER E WITH CIRCUMFLEX AND DOT BELOW
    ('[^E.]',   '\u1EC6', '\\u1EC6', 1), # LATIN CAPITAL LETTER E WITH CIRCUMFLEX AND DOT BELOW
    ('[ê.]',    '\u1EC7', '\\u1EC7', 0), # LATIN SMALL LETTER E WITH CIRCUMFLEX AND DOT BELOW
    ('[^e.]',   '\u1EC7', '\\u1EC7', 1), # LATIN SMALL LETTER E WITH CIRCUMFLEX AND DOT BELOW
    ('[,I]',    '\u1EC8', '\\u1EC8', 0), # LATIN CAPITAL LETTER I WITH HOOK ABOVE
    ('[,i]',    '\u1EC9', '\\u1EC9', 0), # LATIN SMALL LETTER I WITH HOOK ABOVE
    ('[I.]',    '\u1ECA', '\\u1ECA', 0), # LATIN CAPITAL LETTER I WITH DOT BELOW
    ('[i.]',    '\u1ECB', '\\u1ECB', 0), # LATIN SMALL LETTER I WITH DOT BELOW
    ('[O.]',    '\u1ECC', '\\u1ECC', 0), # LATIN CAPITAL LETTER O WITH DOT BELOW
    ('[o.]',    '\u1ECD', '\\u1ECD', 0), # LATIN SMALL LETTER O WITH DOT BELOW
    ('[,O]',    '\u1ECE', '\\u1ECE', 0), # LATIN CAPITAL LETTER O WITH HOOK ABOVE
    ('[,o]',    '\u1ECF', '\\u1ECF', 0), # LATIN SMALL LETTER O WITH HOOK ABOVE
    ('[\'Ô]',   '\u1ED0', '\\u1ED0', 0), # LATIN CAPITAL LETTER O WITH CIRCUMFLEX AND ACUTE
    ('[\'^O]',  '\u1ED0', '\\u1ED0', 1), # LATIN CAPITAL LETTER O WITH CIRCUMFLEX AND ACUTE
    ('[^\'O]',  '\u1ED0', '\\u1ED0', 1), # LATIN CAPITAL LETTER O WITH CIRCUMFLEX AND ACUTE
    ('[^Ó]',    '\u1ED0', '\\u1ED0', 1), # LATIN CAPITAL LETTER O WITH CIRCUMFLEX AND ACUTE
    ('[\'ô]',   '\u1ED1', '\\u1ED1', 0), # LATIN SMALL LETTER O WITH CIRCUMFLEX AND ACUTE
    ('[\'^o]',  '\u1ED1', '\\u1ED1', 1), # LATIN SMALL LETTER O WITH CIRCUMFLEX AND ACUTE
    ('[^\'o]',  '\u1ED1', '\\u1ED1', 1), # LATIN SMALL LETTER O WITH CIRCUMFLEX AND ACUTE
    ('[^ó]',    '\u1ED1', '\\u1ED1', 1), # LATIN SMALL LETTER O WITH CIRCUMFLEX AND ACUTE
    ('[`Ô]',    '\u1ED2', '\\u1ED2', 0), # LATIN CAPITAL LETTER O WITH CIRCUMFLEX AND GRAVE
    ('[`^O]',   '\u1ED2', '\\u1ED2', 1), # LATIN CAPITAL LETTER O WITH CIRCUMFLEX AND GRAVE
    ('[^`O]',   '\u1ED2', '\\u1ED2', 1), # LATIN CAPITAL LETTER O WITH CIRCUMFLEX AND GRAVE
    ('[^Ò]',    '\u1ED2', '\\u1ED2', 1), # LATIN CAPITAL LETTER O WITH CIRCUMFLEX AND GRAVE
    ('[`ô]',    '\u1ED3', '\\u1ED3', 0), # LATIN SMALL LETTER O WITH CIRCUMFLEX AND GRAVE
    ('[`^o]',   '\u1ED3', '\\u1ED3', 1), # LATIN SMALL LETTER O WITH CIRCUMFLEX AND GRAVE
    ('[^`o]',   '\u1ED3', '\\u1ED3', 1), # LATIN SMALL LETTER O WITH CIRCUMFLEX AND GRAVE
    ('[^ò]',    '\u1ED3', '\\u1ED3', 1), # LATIN SMALL LETTER O WITH CIRCUMFLEX AND GRAVE
    ('[,Ô]',    '\u1ED4', '\\u1ED4', 0), # LATIN CAPITAL LETTER O WITH CIRCUMFLEX AND HOOK ABOVE
    ('[,^O]',   '\u1ED4', '\\u1ED4', 1), # LATIN CAPITAL LETTER O WITH CIRCUMFLEX AND HOOK ABOVE
    ('[^,O]',   '\u1ED4', '\\u1ED4', 1), # LATIN CAPITAL LETTER O WITH CIRCUMFLEX AND HOOK ABOVE
    ('[,ô]',    '\u1ED5', '\\u1ED5', 0), # LATIN SMALL LETTER O WITH CIRCUMFLEX AND HOOK ABOVE
    ('[,^o]',   '\u1ED5', '\\u1ED5', 1), # LATIN SMALL LETTER O WITH CIRCUMFLEX AND HOOK ABOVE
    ('[^,o]',   '\u1ED5', '\\u1ED5', 1), # LATIN SMALL LETTER O WITH CIRCUMFLEX AND HOOK ABOVE
    ('[~Ô]',    '\u1ED6', '\\u1ED6', 0), # LATIN CAPITAL LETTER O WITH CIRCUMFLEX AND TILDE
    ('[~^O]',   '\u1ED6', '\\u1ED6', 1), # LATIN CAPITAL LETTER O WITH CIRCUMFLEX AND TILDE
    ('[^~O]',   '\u1ED6', '\\u1ED6', 1), # LATIN CAPITAL LETTER O WITH CIRCUMFLEX AND TILDE
    ('[^Õ]',    '\u1ED6', '\\u1ED6', 1), # LATIN CAPITAL LETTER O WITH CIRCUMFLEX AND TILDE
    ('[~ô]',    '\u1ED7', '\\u1ED7', 0), # LATIN SMALL LETTER O WITH CIRCUMFLEX AND TILDE
    ('[~^o]',   '\u1ED7', '\\u1ED7', 1), # LATIN SMALL LETTER O WITH CIRCUMFLEX AND TILDE
    ('[^~o]',   '\u1ED7', '\\u1ED7', 1), # LATIN SMALL LETTER O WITH CIRCUMFLEX AND TILDE
    ('[^õ]',    '\u1ED7', '\\u1ED7', 1), # LATIN SMALL LETTER O WITH CIRCUMFLEX AND TILDE
    ('[Ô.]',    '\u1ED8', '\\u1ED8', 0), # LATIN CAPITAL LETTER O WITH CIRCUMFLEX AND DOT BELOW
    ('[^O.]',   '\u1ED8', '\\u1ED8', 1), # LATIN CAPITAL LETTER O WITH CIRCUMFLEX AND DOT BELOW
    ('[ô.]',    '\u1ED9', '\\u1ED9', 0), # LATIN SMALL LETTER O WITH CIRCUMFLEX AND DOT BELOW
    ('[^o.]',   '\u1ED9', '\\u1ED9', 1), # LATIN SMALL LETTER O WITH CIRCUMFLEX AND DOT BELOW
    #('[]', '\u1EDA', '\\u1EDA', 0), # LATIN CAPITAL LETTER O WITH HORN AND ACUTE
    #('[]', '\u1EDB', '\\u1EDB', 0), # LATIN SMALL LETTER O WITH HORN AND ACUTE
    #('[]', '\u1EDC', '\\u1EDC', 0), # LATIN CAPITAL LETTER O WITH HORN AND GRAVE
    #('[]', '\u1EDD', '\\u1EDD', 0), # LATIN SMALL LETTER O WITH HORN AND GRAVE
    #('[]', '\u1EDE', '\\u1EDE', 0), # LATIN CAPITAL LETTER O WITH HORN AND HOOK ABOVE
    #('[]', '\u1EDF', '\\u1EDF', 0), # LATIN SMALL LETTER O WITH HORN AND HOOK ABOVE
    #('[]', '\u1EE0', '\\u1EE0', 0), # LATIN CAPITAL LETTER O WITH HORN AND TILDE
    #('[]', '\u1EE1', '\\u1EE1', 0), # LATIN SMALL LETTER O WITH HORN AND TILDE
    #('[]', '\u1EE2', '\\u1EE2', 0), # LATIN CAPITAL LETTER O WITH HORN AND DOT BELOW
    #('[]', '\u1EE3', '\\u1EE3', 0), # LATIN SMALL LETTER O WITH HORN AND DOT BELOW
    ('[U.]',    '\u1EE4', '\\u1EE4', 0), # LATIN CAPITAL LETTER U WITH DOT BELOW
    ('[u.]',    '\u1EE5', '\\u1EE5', 0), # LATIN SMALL LETTER U WITH DOT BELOW
    ('[,U]',    '\u1EE6', '\\u1EE6', 0), # LATIN CAPITAL LETTER U WITH HOOK ABOVE
    ('[,u]',    '\u1EE7', '\\u1EE7', 0), # LATIN SMALL LETTER U WITH HOOK ABOVE
    #('[]', '\u1EE8', '\\u1EE8', 0), # LATIN CAPITAL LETTER U WITH HORN AND ACUTE
    #('[]', '\u1EE9', '\\u1EE9', 0), # LATIN SMALL LETTER U WITH HORN AND ACUTE
    #('[]', '\u1EEA', '\\u1EEA', 0), # LATIN CAPITAL LETTER U WITH HORN AND GRAVE
    #('[]', '\u1EEB', '\\u1EEB', 0), # LATIN SMALL LETTER U WITH HORN AND GRAVE
    #('[]', '\u1EEC', '\\u1EEC', 0), # LATIN CAPITAL LETTER U WITH HORN AND HOOK ABOVE
    #('[]', '\u1EED', '\\u1EED', 0), # LATIN SMALL LETTER U WITH HORN AND HOOK ABOVE
    #('[]', '\u1EEE', '\\u1EEE', 0), # LATIN CAPITAL LETTER U WITH HORN AND TILDE
    #('[]', '\u1EEF', '\\u1EEF', 0), # LATIN SMALL LETTER U WITH HORN AND TILDE
    #('[]', '\u1EF0', '\\u1EF0', 0), # LATIN CAPITAL LETTER U WITH HORN AND DOT BELOW
    #('[]', '\u1EF1', '\\u1EF1', 0), # LATIN SMALL LETTER U WITH HORN AND DOT BELOW
    ('[`Y]',    '\u1EF2', '\\u1EF2', 0), # LATIN CAPITAL LETTER Y WITH GRAVE
    ('[`y]',    '\u1EF3', '\\u1EF3', 0), # LATIN SMALL LETTER Y WITH GRAVE
    ('[Y.]',    '\u1EF4', '\\u1EF4', 0), # LATIN CAPITAL LETTER Y WITH DOT BELOW
    ('[y.]',    '\u1EF5', '\\u1EF5', 0), # LATIN SMALL LETTER Y WITH DOT BELOW
    ('[,Y]',    '\u1EF6', '\\u1EF6', 0), # LATIN CAPITAL LETTER Y WITH HOOK ABOVE
    ('[,y]',    '\u1EF7', '\\u1EF7', 0), # LATIN SMALL LETTER Y WITH HOOK ABOVE
    ('[~Y]',    '\u1EF8', '\\u1EF8', 0), # LATIN CAPITAL LETTER Y WITH TILDE
    ('[~y]',    '\u1EF9', '\\u1EF9', 0), # LATIN SMALL LETTER Y WITH TILDE
    #('[]', '\u1EFA', '\\u1EFA', 0), # LATIN CAPITAL LETTER MIDDLE-WELSH LL
    #('[]', '\u1EFB', '\\u1EFB', 0), # LATIN SMALL LETTER MIDDLE-WELSH LL
    #('[]', '\u1EFC', '\\u1EFC', 0), # LATIN CAPITAL LETTER MIDDLE-WELSH V
    #('[]', '\u1EFD', '\\u1EFD', 0), # LATIN SMALL LETTER MIDDLE-WELSH V
    #('[]', '\u1EFE', '\\u1EFE', 0), # LATIN CAPITAL LETTER Y WITH LOOP
    #('[]', '\u1EFF', '\\u1EFF', 0), # LATIN SMALL LETTER Y WITH LOOP
     ('[Alpha]','\u0391', '\\u0391', 0), #
     ('[alpha]','\u03B1', '\\u03B1', 0), #
     ('[Beta]', '\u0392', '\\u0392', 0), #
     ('[beta]', '\u03B2', '\\u03B2', 0), #
     ('[Gamma]','\u0393', '\\u0393', 0), #
     ('[gamma]','\u03B3', '\\u03B3', 0), #
     ('[Delta]','\u0394', '\\u0394', 0), #
     ('[delta]','\u03B4', '\\u03B4', 0), #
     ('[Epsilon]', '\u0395', '\\u0395', 0), #
     ('[epsilon]', '\u03B5', '\\u03B5', 0), #
     ('[Zeta]', '\u0396', '\\u0396', 0), #
     ('[zeta]', '\u03B6', '\\u03B6', 0), #
     ('[Eta]',  '\u0397', '\\u0397', 0), #
     ('[eta]',  '\u03B7', '\\u03B7', 0), #
     ('[Theta]','\u0398', '\\u0398', 0), #
     ('[theta]','\u03B8', '\\u03B8', 0), #
     ('[Iota]', '\u0399', '\\u0399', 0), #
     ('[iota]', '\u03B9', '\\u03B9', 0), #
     ('[Kappa]','\u039A', '\\u039A', 0), #
     ('[kappa]','\u03BA', '\\u03BA', 0), #
     ('[Lambda]','\u039B', '\\u039B', 0), #
     ('[lambda]','\u03BB', '\\u03BB', 0), #
     ('[Mu]',   '\u039C', '\\u039C', 0), #
     ('[mu]',   '\u03BC', '\\u03BC', 0), #
     ('[Nu]',   '\u039D', '\\u039D', 0), #
     ('[nu]',   '\u03BD', '\\u03BD', 0), #
     ('[Xi]',   '\u039E', '\\u039E', 0), #
     ('[xi]',   '\u03BE', '\\u03BE', 0), #
     ('[Omicron]', '\u039F', '\\u039F', 0), #
     ('[omicron]', '\u03BF', '\\u03BF', 0), #
     ('[Pi]',   '\u03A0', '\\u03A0', 0), #
     ('[pi]',   '\u03C0', '\\u03C0', 0), #
     ('[Rho]',  '\u03A1', '\\u03A1', 0), #
     ('[rho]',  '\u03C1', '\\u03C1', 0), #
     ('[Sigma]','\u03A3', '\\u03A3', 0), #
     ('[sigma]','\u03C3', '\\u03C3', 0), #
     ('[Tau]',  '\u03A4', '\\u03A4', 0), #
     ('[tau]',  '\u03C4', '\\u03C4', 0), #
     ('[Upsilon]', '\u03A5', '\\u03A5', 0), #
     ('[upsilon]', '\u03C5', '\\u03C5', 0), #
     ('[Phi]',  '\u03A6', '\\u03A6', 0), #
     ('[phi]',  '\u03C6', '\\u03C6', 0), #
     ('[Chi]',  '\u03A7', '\\u03A7', 0), #
     ('[chi]',  '\u03C7', '\\u03C7', 0), #
     ('[Psi]',  '\u03A8', '\\u03A8', 0), #
     ('[psi]',  '\u03C8', '\\u03C8', 0), #
     ('[Omega]','\u03A9', '\\u03A9', 0), #
     ('[omega]','\u03C9', '\\u03C9', 0), #
     #('\?', '\u037E', '?', 0), #
     #(';', '\u0387', ';', 0), #
     ('[Koppa]','\u03D8', '\\u03D8', 0), #
     ('[koppa]','\u03D9', '\\u03D9', 0), #
     ('[Digamma]', '\u03DC', '\\u03DC', 0), #
     ('[digamma]', '\u03DD', '\\u03DD', 0), #
     ('[Qoppa]','\u03DE', '\\u03DE', 0), #
     ('[qoppa]','\u03DF', '\\u03DF', 0), #
     ('[Sampi]','\u03E0', '\\u03E0', 0), #
     ('[sampi]','\u03E1', '\\U03E1', 0), #
    ]

  #item_greek_lower = (' \u03B1\u03B2\u03B3\u03B4\u03B5\u03B6\u03B7\u03B8\u03B9\u03BA\u03BB' +
  #                    '\u03BC\u03BD\u03BE\u03BF\u03C0\u03C1\u03C3\u03C4\u03C5\u03C6\u03C7' +
  #                    '\u03C8\u03C9')

  #item_greek_upper = (' \u0391\u0392\u0393\u0394\u0395\u0396\u0397\u0398\u0399\u039A\u039B' +
  #                    '\u039C\u039D\u039E\u039F\u03A0\u03A1\u03A3\u03A4\u03A5\u03A6\u03A7' +
  #                    '\u03A8\u03A9')

  # Initialization routine for class Book
  def __init__(self, args, renc, config, sout, serr):

    self.stdout = sout
    self.stderr = serr

    del self.wb[:]
    del self.eb[:]
    del self.bb[:]
    del self.fnlist[:]
    del self.gk_user[:]
    del self.diacritics_user[:]
    del self.srw[:]
    del self.srs[:]
    del self.srr[:]
    del self.instack[:]
    del self.llstack[:]
    del self.psstack[:]
    del self.nfstack[:]
    del self.dvstack[:]
    del self.fsstack[:]
    del self.blkfszstack[:]
    del self.liststack[:]
    del self.dotcmdstack[:]
    del self.warnings[:]
    del self.mal[:]
    del self.mau[:]
    self.renc = renc.lower() # requested output encoding (t, u, or h)
    self.forceutf8 = (True) if (renc == "U") else (False)
    self.debug = args.debug
    self.srcfile = args.infile
    self.anonymous = args.anonymous
    self.log = args.log
    self.listcvg = args.listcvg
    self.cvgfilter = args.filter
    self.srcbin = args.srcbin
    self.ppqt2 = args.ppqt2
    self.config = config # ConfigParser object
    #self.wrapper = textwrap.TextWrapper()
    #self.wrapper.break_long_words = False
    #self.wrapper.break_on_hyphens = False
    self.nregs["psi"] = "0" # default above/below paragraph spacing for indented text
    self.nregs["pti"] = "1em" # default paragraph indentation for indented text
    self.nregs["psb"] = "1.0em" # default above/below paragraph spacing for block text
    self.nregs["pnc"] = "silver" # use to define page number color in HTML
    self.nregs["pnstyle"] = "content" # use the "content" form of page numbers by default, rather than "title" form
                                      # to avoid the CSS validator bug
    self.nregs["lang"] = "en" # base language for the book (used in HTML header)
    self.nregs["Footnote"] = "Footnote" # English word for Footnote for text files
    self.nregs["Illustration"] = "Illustration" # English word for Illustration for text files
    self.nregs["Sidenote"] = "Sidenote" # English word for Sidenote for text files
    self.nregs["dcs"] = "250%" # drop cap font size
    self.nregs["nfl"] = "-1" # default number of spaces to indent .nf l blocks in text (-1 = disabled)
    self.nregs["tag-i"] = "_" # default to surrounding <i> text with _ in text output
    self.nregs["tag-b"] = "=" # default to surrounding <b> text with = in text output
    self.nregs["tag-g"] = "_" # default to surrounding <g> text with _ in text output
    self.nregs["tag-sc"] = "" # default to surrounding <sc> text with nothing (meaning it will be upper-cased
                              # by default in text output)
    self.nregs["tag-f"] = ""  # default to surrounding <f> text with nothing in text output (meaning <f> is ignored
                              # by default in text)
    self.nregs["tag-em"] = "_" # default to surrounding <em> text with _ in text output
    self.nregs["tag-strong"] = "=" # default to surrounding <strong> text with = in text output
    self.nregs["tag-cite"] = "_" # default to surrounding <cite> text with _ in text output
    self.nregs["tag-u"] = "" # default to surrounding <u> text with nothing in text output (meaning <u> is ignored
                             # by default in text)
    self.nregs["btb_"] = "thin solid" # table border: top/bottom using _
    self.nregs["btb__"] = "medium solid" # table border: top/bottom using __
    self.nregs["btb="] = "medium double" # table border: top/bottom using =
    self.nregs["btb=="] = "thick double" # table border: top/bottom using ==
    self.nregs["blr|"] = "thin solid" # table border: left/right using |
    self.nregs["blr||"] = "medium solid" # table border: left/right using ||
    self.nregs["blr="] = "medium double" # table border: left/right using =
    self.nregs["blr=="] = "thick double" # table border: left/right using =
    self.nregs["border-collapse"] = "collapse" # border-collapse option for table borders
    self.nregs["html-cell-padding-left"] = ".5em" # left cell padding for html tables when borders in use
    self.nregs["html-cell-padding-right"] = ".5em" # rightt cell padding for html tables when borders in use
    self.nregs["text-cell-padding-left"] = "" # left cell padding for text tables when borders in use
    self.nregs["text-cell-padding-right"] = "" # right cell padding for html tables when borders in use
    self.nregs["break-wrap-at"] = "" # set of allowable characters to break wrapping, separated by spaces
                                     # e.g., .nr break-wrap-at "- :" or .nr break-wrap-at "- —"
                                     # note that breaking on space and <br> is always allowed
    self.nregs["nf-spaces-per-em"] = "2" # Used in HTML indentation calculation
    self.nregsusage["nf-spaces-per-em"] = 1 # number of times we've specified this value

    self.encoding = "" # input file encoding
    self.pageno = "" # page number stored as string (null is the same as a Roman numeral 0)
    self.bnmatch = re.compile("^⑱.*?⑱$")  # re to match a .bn line
    self.bnsearch = re.compile("⑱.*?⑱")  # re to find .bn info anywhere within a line
    self.pnmatch = re.compile("^⑯(.*?)⑰$")   # re to match a .pn line
    self.pnsearch = re.compile("⑯(.*?)⑰") # to find .pn info anywhere within a line



    self.list_styles_u = {
      'disc':'●',
      'circle':'○',
      'square':'▪',
      'none':' '
      }

    self.list_styles_o = {
          'decimal':('decimal', self.item_decimal),
      'lower-alpha':('lower-alpha', self.item_lower_alpha),
      'lower-roman':('lower-roman', self.item_lower_roman),
      'upper-alpha':('upper-alpha', self.item_upper_alpha),
      'upper-roman':('upper-roman', self.item_upper_roman),
      }

    self.item_alpha = ' abcdefghijklmnopqrstuvwxyz'

    # format of dotcmds dictionary:
    # 1. key: the dot directive
    # 2. the processing routine for the directive
    # 3. None: no parameters passed to routine
    #    "cl": self.cl passed to routine
    self.fulldotcmds = {          # switches dot directives to processing routines
      ".ad" :  (self.doAd, None),
      # .bn handled separately
      # .ca handled separately
      # .ce handled separately
      # .ci handled separately
      # .cm handled separately
      # .cv handled separately
      ".dc" :  (self.doDropcap, "cl"),
      ".dd" :  (self.doDd, None),  # routine to say "only valid inside a .dl block
      ".de" :  (self.doDef, None),
      ".di" :  (self.doDropimage, None),
      ".dl" :  (self.doDl, None),
      # .dm handled separately
      # .dt outside of a .dl block handled separately
      ".dv" :  (self.doDiv, None),
      ".⓭D" :  (self.doDiv, None),   # special "processed" form of ending tag for .dv-, .⓭DV-
      ".fm" :  (self.doFmark, None),
      ".fn" :  (self.doFnote, None),
      ".fs" :  (self.doFontSize, None),
      # .gk handled separately
      # .gl handled separately
      # .gu handled separately
      ".h1" : (self.doH1, None),
      ".h2" : (self.doH2, None),
      ".h3" : (self.doH3, None),
      ".h4" : (self.doH4, None),
      ".h5" :  (self.doH5, None),
      ".h6" :  (self.doH6, None),
      ".hr" :  (self.doHr, None),
      # .if handled separately
      # .ig handled separately
      ".il" :  (self.doIllo, None),
      ".in" :  (self.doIn, None),
      ".it" :  (self.doIt, None),
      ".ix" :  (self.doIx, None),
      ".li" :  (self.doLit, None),
      ".ll" :  (self.doLl, None),
      # .ma handled separately
      ".na" :  (self.doNa, None),
      ".nf" :  (self.doNf, None),
      ".ni" :  (self.doNi, None),
      ".nr" :  (self.doNr, None),
      ".ol" :  (self.doOl, None),
      ".pb" :  (self.doPb, None),
      ".pi" :  (self.doPi, None),
      # .pm handled separately
      # .pn handled separately
      ".rj" :  (self.doRj, None),
      ".sn" :  (self.doSidenote, None),
      ".sp" :  (self.doSpace, None),
      # .sr handled separately
      ".ta" :  (self.doTable, None),
      ".tb" :  (self.doTbreak, None),
      ".ti" :  (self.doTi, None),
      ".ul" :  (self.doUl, None),
      }

    self.list_dotcmds = {          # restricted set of dot commands within a list (.ul, .ol)
      ".ad" :  (self.doAd, None),
      ".dc" :  (self.doDropcap, "cl"),
      ".dd" :  (self.doDd, None),  # routine to crash and say "only valid inside a .dl block"
      ".de" :  (self.doDef, None),
      ".di" :  (self.doDropimage, None),
      ".dl" :  (self.doDl, None),
      ".dv" :  (self.doDiv, None),
      ".⓭D" :  (self.doDiv, None),   # special "processed" form of ending tag for .dv-
      ".fm" :  (self.rejectWithinList, None),
      ".fn" :  (self.rejectWithinList, None),
      ".fs" :  (self.doFontSize, None),
      ".h1" : (self.rejectWithinList, None),
      ".h2" : (self.rejectWithinList, None),
      ".h3" : (self.rejectWithinList, None),
      ".h4" : (self.rejectWithinList, None),
      ".h5" :  (self.rejectWithinList, None),
      ".h6" :  (self.rejectWithinList, None),
      ".hr" :  (self.doHr, None),
      ".il" :  (self.doIllo, None),
      ".in" :  (self.doIn, None),
      ".it" :  (self.doIt, None),
      ".ix" :  (self.doIx, None),
      ".li" :  (self.doLit, None),
      ".ll" :  (self.doLl, None),
      ".na" :  (self.doNa, None),
      ".nf" :  (self.doNf, None),
      ".ni" :  (self.doNi, None),
      ".nr" :  (self.doNr, None),
      ".ol" :  (self.doOl, None),
      ".pb" :  (self.doPb, None),
      ".pi" :  (self.doPi, None),
      ".rj" :  (self.doRj, None),
      ".sn" :  (self.doSidenote, None),
      ".sp" :  (self.doSpace, None),
      ".ta" :  (self.doTable, None),
      ".tb" :  (self.doTbreak, None),
      ".ti" :  (self.rejectWithinList, None), # can't allow this one without implementing a stack for persistent .ti
      ".ul" :  (self.doUl, None),
      }

    self.dotcmds = self.fulldotcmds # initially allow full set of dot commands
    self.dotcmdstack.append(self.dotcmds)

    self.dlbuffer = []

    # Process any Nregs items in ppgen.ini via our ConfigParser object
    for k in self.config['Nregs']:
      if k in self.nregs:
        self.nregs[k] = self.config['Nregs'][k]
        self.print_msg("setting self.nregs[{}] via .ini file: {}".format(k, self.nregs[k]))
      else:
        self.warn("Ignoring unsupported Nregs key {} from .ini file".format(k))

  # Determine default alignment for h1-h6 headers based on content of ppgen.ini self.config['CSS']
  # type: 'h1', 'h2', etc.
  def getHnAlignment(self, type):
    css = self.config['CSS'][type]
    m = re.search("text-align: *([clr])", css) # look for text-align in the specification and pass back first character
    if m:
      align = m.group(1)[0]
    else:
      align = "" # default to null if none found
    return align

  # Backstop routine to crash and say "only valid inside a .dl block" upon hitting .dd
  #
  # Note: doDl processes and routes all input between .dl and .dl- and also directly
  #  processes .dt and .dd itself. If .dd is ever encountered outside of a .dl block this
  #  routine will get control to reject it.
  def doDd(self):

    self.crash_w_context("{} allowed only as part of a .dl block.".format(self.wb[self.cl][0:3]), self.cl)


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

  def toRoman2(self, n): # like toRoman, but for use in user-provided macros; accepts either string or integer

    try:
      n = n + 0 # did user pass an integer?
    except TypeError: # no, it's a string
      if n.isdigit(): # is it at least all digits?
        n = int(n)    # if yes, convert it to integer
      else:
        n = 0         # else assume 0

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


  # routine to increment a list item number and return it as a decimal number
  # (used in doIt for text output)
  def item_decimal(self):
    self.list_item_value += 1
    return str(self.list_item_value)

  # routine to increment a list item number and return it as a lower-case alpha string
  # a, b, c, ..., z, aa, ..., az, ba, ..., etc
  # (limited to 676 items, zz)
  # (used in doIt for text output)
  def item_lower_alpha(self):
    self.list_item_value += 1
    value = ''
    if self.list_item_value > 676:
      self.crash_w_context("Too many list items for 'lower alpha': {}".format(self.list_item_value), self.cl)
    else:
      if self.list_item_value > 26:
        value = self.item_alpha[self.list_item_value // 26] + self.item_alpha[self.list_item_value % 26]
      else:
        value = self.item_alpha[self.list_item_value]
    return value

  # routine to increment a list item number and return it as an upper-case alpha string
  # A, B, C, ..., Z, AA, ..., AZ, BA, ..., etc
  # (limited to 676 items, ZZ)
  # (used in doIt for text output)
  def item_upper_alpha(self):
    return self.item_lower_alpha().upper()

  # routine to increment a list item number and return it as a lower-case Roman numeral
  # (used in doIt for text output)
  def item_lower_roman(self):
    self.list_item_value += 1
    return self.toRoman(self.list_item_value)

  # routine to increment a list item number and return it as an upper-case Roman numeral
  # (used in doIt for text output)
  def item_upper_roman(self):
    self.list_item_value += 1
    return self.toRoman(self.list_item_value).upper()

  # not needed any more
  ## routine to restore some of the escaped characters (needed for .sr processing)
  ## Note: restores the backslash character, too.
  #def restore_some_escapes(self, text):
  #  text = text.replace("①", "\{")
  #  text = text.replace("②", "\}")
  #  text = text.replace("③", "\[")
  #  text = text.replace("④", "\]")
  #  text = text.replace("⑤", "\<")
  #  text = text.replace("⑳", "\>")
  #  text = text.replace("⑥", "\:")
  #  text = text.replace("⑨", "\-")
  #  text = text.replace("⓪", "\#")
  #  return text

  def cvglist(self):
    if self.listcvg:
      f1 = codecs.open("ppgen-cvglist.txt", "w", encoding="UTF-8")
      f1.write("\r\n\r\nppgen {}\r\n".format(VERSION))
      f1.write("\r\nBuilt-in Greek Characters:\r\n")
      f1.write("User enters:  ppgen generates:\r\n\r\n")
      for s in self.gk:
        if len(s) == 5:
          f1.write("{:<17} {}\r\n".format(s[2], s[4]))
        elif len(s) == 4:
          f1.write("{:<17} {}\r\n".format(s[2], s[3]))
        else:
          f1.write("{:<17} {}\r\n".format(s[2], s[1]))
      f1.write("\r\n\r\nBuilt-in diacritics:\r\n\r\n")
      f1.write("User enters:  ppgen generates:\r\n\r\n")
      for s in self.diacritics:
        #f1.write("{:<14}{:<5} {:<5}  {}\r\n".format(s[0], s[1], s[2], s[4]))
        ns = "**Non-standard markup; will produce warning" if s[3] else ""
        f1.write("{:<14}{:<5} {:<5}  {}  {}\r\n".format(s[0], s[1], s[2], unicodedata.name(s[1]), ns))
      f1.close()
      exit(1)

  # Create special output file after .gk or .cv if requested, and quit
  def cvgbailout(self):
    bailfn = re.sub("-src", "", self.srcfile.split('.')[0]) + "-cvgout-utf8.txt"
    f1 = codecs.open(bailfn, "w", encoding="UTF-8")
    for index,t in enumerate(self.wb):
      # unprotect temporarily protected characters from Greek strings
      t = t.replace("⑩", r"\|") # restore temporarily protected \| and \(space)
      t = t.replace("⑮", r"\ ")
      f1.write( "{:s}\r\n".format(t.rstrip()) )
    f1.close()
    self.print_msg("Terminating as requested after .cv/.gk processing.\n\tOutput file: {}".format(bailfn))
    exit(1)

  # create a ppqt2 metadata file entry
  def ppqtpage(self, name, count, fn=None):
    if not fn: # if first or intermediate call, append data
      if self.ppqtentries == 0:
        self.ppqt.append('{')
        self.ppqt.append('  "PAGETABLE": [')
      else:
        self.ppqt.append('    ],')
      self.ppqt.append('    [')
      self.ppqt.append('      {},'.format(count))
      self.ppqt.append('      "{}",'.format(name))
      self.ppqt.append('      "",')
      self.ppqtentries += 1
      if self.ppqtentries == 1:
        self.ppqt.append('      1,')
        self.ppqt.append('      0,')
      else:
        self.ppqt.append('      0,')
        self.ppqt.append('      3,')
      self.ppqt.append('      {}'.format(self.ppqtentries))
    else: # else final call (filename provided)
      self.ppqt.append('    ]') # finish file contents
      self.ppqt.append('  ]')
      self.ppqt.append('}')
      ppqtfn = fn + ".ppqt"
      f1 = codecs.open(ppqtfn, "w", "ISO-8859-1")
      for index,t in enumerate(self.ppqt):
        f1.write("{:s}\r\n".format(t))
      f1.close()
      self.print_msg("PPQTv2 metadata file {} created".format(ppqtfn))

  # Create a -src.txt.bin file based on the input file to facilitate using GG
  # or PPQTv1 to work on this ppgen project
  # Also create a .ppqt file for use with PPQTv2 if -ppqt2 option was specified
  def createsbin(self):
    bb = []
    bb.append("%::pagenumbers = (") # insert the .bin header into the bb array
    if self.ppqt2:
      self.ppqt = []
      self.ppqtentries = 0
    i = 0
    ccount = 0
    for i, line in enumerate(self.wb):
      if line.startswith(".bn"):
        m = re.search("(\w+?)\.(png|jpg|jpeg)",self.wb[i])
        if m:
          t = " 'Pg{}' => ['offset' => '{}.{}', 'label' => '', 'style' => '', 'action' => '', 'base' => ''],"
          t = t.format(m.group(1), i+1, 0)  # format a line in the .bn array (GG wants a 1-based count)
          t = re.sub("\[","{",t,1)
          t = re.sub("]","}",t,1)
          bb.append(t)
          if self.ppqt2:
            self.ppqtpage(m.group(1), ccount)
      ccount += len(line) + 1
    if self.ppqt2 and len(self.ppqt): # finish ppqt file if needed, and write it out
      self.ppqtpage("", 0, fn=self.srcfile)
    if len(bb) > 1: # Create .bin file if any .bn commands present
      temp = self.srcfile
      temp = os.path.dirname(temp)
      temp = os.path.join(temp, "pngs")
      bb.append(");")  # finish building GG .bin file
      bb.append(r"$::pngspath = '{}\\';".format(os.path.join(os.path.realpath(self.srcfile),"pngs")))
      bb.append("1;")
      binfn = self.srcfile + ".bin"
      f1 = codecs.open(binfn, "w", "ISO-8859-1")
      for index,t in enumerate(bb):
        f1.write("{:s}\r\n".format(t))
      f1.close()
      self.print_msg("Terminating as requested after creating -src.txt.bin file: {}".format(binfn))
    else:
      self.print_msg("Terminating after -sbin processing, but no .bn commands found;\n" +
            "-src.txt.bin file not generated.")
    exit(1)




  # map UTF-8 characters to characters safe for printing on non UTF-8 terminals
  def umap(self, s):
    t = ""
    for c in s: # for every character on the line provided
      if c in self.d: # is it in the list of converting characters?
        c1 = self.d[c] # yes, replace with converted Latin-1 character
      else:
        c1 = c
      if len(c1) > 1 or ord(c1) < 0x80:
        t += c1 # no conversion, transfer character as is
      else:
        t += "*" # use an asterisk if not plain text
    return t

  # -------------------------------------------------------------------------------------
  # courtesy id check
  #
  # ID and NAME tokens must begin with a letter ([A-Za-z]) and may be followed by any number
  # of letters, digits ([0-9]), hyphens ("-"), underscores ("_"), colons (":"), and periods (".").
  def checkId(self, s, id_loc=None):
    if not id_loc:
      id_loc = self.cl
    if not re.match(r"[A-Za-z][A-Za-z0-9\-_\:\.]*$", s):
      self.warn_w_context("illegal identifier: {}".format(s), id_loc)

  # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  # get the value of the requested parameter from attr string
  # remove parameter from string, return string and parameter
  def get_id(self, tgt, attr, np=2):

    done = False
    the_id = None
    m = re.search(r"{}='(.*?)'".format(tgt), attr)  # single quotes
    if m:
      the_id = m.group(1)
      attr = re.sub(re.escape(m.group(0)), "", attr)
      done = True

    if not done:
      m = re.search(r"{}=\"(.*?)\"".format(tgt), attr)  # double quotes
      if m:
        the_id = m.group(1)
        attr = re.sub(re.escape(m.group(0)), "", attr)
        done = True

    if not done:
      #m = re.search(r"{}=(.*?)($|[ >])".format(tgt), attr)  # no quotes
      m = re.search(r"{}=(.*?)($|[ ])".format(tgt), attr)  # no quotes
      if m:
        the_id = m.group(1)
        attr = re.sub(re.escape(m.group(0)), "", attr)
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

  # Check for pppgen special characters in source file
  # ppgen uses a number of special Unicode characters as flags during
  # processing. This routine will scan the PPer's source file to make
  # sure the PPer hasn't chosen to use any of them for some odd reason,
  # as that could lead to odd behavior
  def check_for_pppgen_special_characters(self):
    s = '\n'.join(self.wb)  # make a text blob
    pattern = r"(.*?)([ᒪᒧⓓⓢ①②③④⑤⑥⑦⑧⑨⑩⑪⑫⑬⑭⑮⑯⑰⑱⑲⑳ⓈⓉⓊⓋⓏⓣⓤⓥ⓪⓫⓬⓭⓮⓯⓵⓶⓷⓸⓹⓺⓻⓼⓽◮◸◹◺◿⫉])"

    values = {'ᒪ': '\\u14aa',  #  ᒪ   CANADIAN SYLLABICS MA # precedes lang= info
              'ᒧ': '\\u14a7',  #  ᒧ   CANADIAN SYLLABICS MO # follows lang= info
              'ⓓ': '\\u24d3',  #  ⓓ   CIRCLED LATIN SMALL LETTER D # four dot ellipsis
              'ⓢ': '\\u24e2',  #  ⓢ   CIRCLED LATIN SMALL LETTER D + CIRCLED LATIN SMALL LETTER S repeated 2.5
              '①': '\\u2460',  #  ①   CIRCLED DIGIT ONE   # \{
              '②': '\\u2461',  #  ②   CIRCLED DIGIT TWO   # \}
              '③': '\\u2462',  #  ③   CIRCLED DIGIT THREE # \[
              '④': '\\u2463',  #  ④   CIRCLED DIGIT FOUR  # \]
              '⑤': '\\u2464',  #  ⑤   CIRCLED DIGIT FIVE  # \<
              '⑥': '\\u2465',  #  ⑥   CIRCLED DIGIT SIX   # \:
              '⑦': '\\u2466',  #  ⑦   CIRCLED DIGIT SEVEN # used in footnote processing (along with circled 11/12/13/14)
              '⑧': '\\u2467',  #  ⑧   CIRCLED DIGIT EIGHT # Used for leading nbsp in .ti processing
              '⑨': '\\u2468',  #  ⑨   CIRCLED DIGIT NINE  # \- (so it doesn't become an em-dash later)
              '⑩': '\\u2469',  #  ⑩   CIRCLED NUMBER TEN  # temporarily protect \| during Greek conversion
              '⑪': '\\u246a',  #  ⑪   CIRCLED NUMBER ELEVEN # used in footnote processing (along with 7/12/13/14)
              '⑫': '\\u246b',  #  ⑫   CIRCLED NUMBER TWELVE # used in footnote processing (along with 7/11/13/14)
              '⑬': '\\u246c',  #  ⑬   CIRCLED NUMBER THIRTEEN # used in footnote processing (along with 7/11/12/14)
              '⑭': '\\u246d',  #  ⑭   CIRCLED NUMBER FOURTEEN # used in footnote processing (along with 7/11/12/13)
              '⑮': '\\u246e',  #  ⑮   CIRCLED NUMBER FIFTEEN # temporarily protect \(space) during Greek conversion
              '⑯': '\\u246f',  #  ⑯   CIRCLED NUMBER SIXTEEN # precedes page number info
              '⑰': '\\u2470',  #  ⑰   CIRCLED NUMBER SEVENTEEN # follows page number info
              '⑱': '\\u2471',  #  ⑱   CIRCLED NUMBER EIGHTEEN # surrounds .bn info
              '⑲': '\\u2472',  #  ⑲   CIRCLED NUMBER NINETEEN # Protects PPer supplied links (#...#)
              '⑳': '\\u2473',  #  ⑳   CIRCLED NUMBER TWENTY # \>
              'Ⓢ': '\\u24c8',  #  Ⓢ   CIRCLED LATIN CAPITAL LETTER S # (non-breaking space)
              'Ⓣ': '\\u24c9',  #  Ⓣ   CIRCLED LATIN CAPITAL LETTER T # (zero space)
              'Ⓤ': '\\u24ca',  #  Ⓤ   CIRCLED LATIN CAPITAL LETTER U # (thin space)
              'Ⓥ': '\\u24cb',  #  Ⓥ   CIRCLED LATIN CAPITAL LETTER V # (thick space)
              'Ⓩ': '\\u24cf',  #  Ⓩ   CIRCLED LATIN CAPITAL LETTER Z # &
              #'ⓢ': '\\u24e2',  #  ⓢ   CIRCLED LATIN SMALL LETTER S # non-breaking space (\  or \_ or &nbsp;)
              'ⓣ': '\\u24e3',  #  ⓣ   CIRCLED LATIN SMALL LETTER T # zero space (\&)
              'ⓤ': '\\u24e4',  #  ⓤ   CIRCLED LATIN SMALL LETTER U # thin space (\^)
              'ⓥ': '\\u24e5',  #  ⓥ   CIRCLED LATIN SMALL LETTER V # thick space (\|)
              '⓪': '\\u24ea',  #  ⓪   CIRCLED DIGIT 0 # (\#)
              '⓫': '\\u24eb',  #  ⓫   NEGATIVE CIRCLED NUMBER ELEVEN # temporary substitute for | in inline HTML sidenotes until postprocessing
              '⓬': '\\u24ec',  #  ⓬   NEGATIVE CIRCLED NUMBER TWELVE # temporary substitute for <br> in text wrapping
              '⓭': '\\u24ed',  #  ⓭   NEGATIVE CIRCLED NUMBER THIRTEEN # temporarily marks end of .dv blocks in HTML, .⓭DV-
              '⓮': '\\u24ee',  #  ⓮   NEGATIVE CIRCLED NUMBER FOURTEEN # used to protect/convert ^^ in input to ^ in output
              '⓯': '\\u24ef',  #  ⓯   NEGATIVE CIRCLED NUMBER FIFTEEN  # used to protect/convert __{ in input to _{ in output
              '⓵': '\\u24f5',  #  ⓵   DOUBLE CIRCLED DIGIT ONE # temporary substitute for <i>
              '⓶': '\\u24f6',  #  ⓶   DOUBLE CIRCLED DIGIT TWO # temporary substitute for <b>
              '⓷': '\\u24f7',  #  ⓷   DOUBLE CIRCLED DIGIT THREE # temporary substitute for <g>
              '⓸': '\\u24f8',  #  ⓸   DOUBLE CIRCLED DIGIT FOUR # temporary substitute for <sc>
              '⓹': '\\u24f9',  #  ⓹   DOUBLE CIRCLED DIGIT FIVE # temporary substitute for <f>
              '⓺': '\\u24fa',  #  ⓺   DOUBLE CIRCLED DIGIT SIX # temporary substitute for <em>
              '⓻': '\\u24fb',  #  ⓻   DOUBLE CIRCLED DIGIT SEVEN # temporary substitute for <strong>
              '⓼': '\\u24fc',  #  ⓼   DOUBLE CIRCLED DIGIT EIGHT # temporary substitute for <cite>
              '⓽': '\\u24fd',  #  ⓽   DOUBLE CIRCLED DIGIT NINE # temporary substitute for <u>
              '◮': '\\u25ee',  #  ◮   UP-POINTING TRIANGLE WITH RIGHT HALF BLACK # <b> or <strong> (becomes =)
              '◸': '\\u25f8',  #  ◸   UPPER LEFT TRIANGLE # precedes superscripts
              '◹': '\\u25f9',  #  ◹   UPPER RIGHT TRIANGLE # follows superscripts
              '◺': '\\u25fa',  #  ◺   LOWER LEFT TRIANGLE # precedes subscripts
              '◿': '\\u25ff',  #  ◿   LOWER RIGHT TRIANGLE # follows subscripts
              '⫉': '\\u2ac9',  #  ⫉   SUBSET OF ABOVE ALMOST EQUAL TO # used temporarily during page number reference processing
              }

    start = 0
    found = False
    m = True
    while m and start < len(s):
      m = re.search(pattern, s[start:])
      if m: #  found a prohibited character
        found = True
        c = m.group(2)
        s, count = re.subn(c, "", s) # null out and count the character we found
        self.warn("Restricted character {} ({}) found in source file {} time(s).".format(unicodedata.name(c),
                                                                                         values[c],
                                                                                         count))
        start = len(m.group(1)) + 1 # bump past the character we found

    if found:
      self.fatal("Use of restricted characters in the source file will cause unpredictable ppgen processing")


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
      except Exception as e:
        pass

    if self.encoding == "":
      try:
        wbuf = open(fn, "r", encoding='latin_1').read()
        self.encoding = "latin_1"
        self.wb = wbuf.split("\n")
        self.latin1only = True  # only generate Latin-1 output
      except Exception as e:
        pass

    self.stderr.write("**Detected encoding: " + self.encoding + "\n")

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

    self.check_for_pppgen_special_characters()

  # log print
  def lprint(self, msg):
    if self.log:
      self.print_msg(msg)

  def rp(self, flag, msg):
    self.print_msg("=> {} {}".format(flag,msg))

  # display error message and exit
  def fatal(self, message):
    #s = self.umap(message)
    self.stderr.write("FATAL: " + message + "\n")
    exit(1)

  # display warning
  def warn(self, message):
    #s = self.umap(message)
    if message not in self.warnings: # don't give exact same warning more than once.
      self.warnings.append(message)
      self.stderr.write("**warning: " + message + "\n")

  # display informational message
  def info(self, message):
    self.stderr.write("  info: " + message + "\n")

  # print a message
  def print_msg(self, message):
    self.stdout.write(message + "\n")

  class DefList(object):
    # Definition List Class (Base definition)
    # .dl options
    #    or
    # .dl-
    #
    # options:
    #   break = n (default) | y (Controls, when combine=y, whether line endings are maintained (y) or not (n)
    #   class=<class-value> (specifies a class for the list in HTML; ignored in text)
    #   collapse = n (default) | y (controls whether metric lines without a term, or successive wrapped paragraph lines,
    #                               appear at left margin or aligned after the end of the term)
    #   combine = n (default) | y (controls whether lines without a term (format c) are combined with the prior
    #                              definition value and wrapped as a paragraph, or not)
    #   dintent=<integer>       (indents the definition by that amount (default: 0))
    #   float = y (default) | n (controls whether definition starts on same line as term or not)
    #   hang = n (default) | y  (controls whether definition lines that must be wrapped will have a hanging indent)
    #                           Note: hang=y applies only to style=d.
    #   id=<id-value> (specifies an id for the list in HTML; ignored in text)
    #   style = dl (default) | paragraph (controls whether html is generated using <dl> or <p>)
    #   tindent=<integer>       (indents the term by that amount (default: 0))
    #   w=<integer>             (max length of term or speaker name (default: 10))
    #
    #   debug = n (default) | y (controls printing of debug information for .dl)
    #
    # Options from the .dl directive are maintained in a dictionary:
    #   "break": True, False
    #   "class": string
    #   "collapse": True, False
    #   "combine": True, False
    #   "dindent":  integer
    #   "float": True, False
    #   "hang":     True, False
    #   "id": string
    #   "start": True = .dl; False = .dl-
    #   "style": d(l), p(aragraph)
    #   "tindent": integer
    #   "width": integer
    #
    # Note: Definition lists operate differently from other dot commands. First, the processing is part of an object,
    #       defined in this class definition but subclassed for text and HTML processing. Next, the object is in
    #       control of processing until the matching .dl- is encountered. All lines will either be directly part of
    #       its output, or indirectly if they are consumed/generated by another dot directive inside the .dl block.
    #       That is, .dl allows other dot commands within its scope, and actually invokes their associated
    #       processing routine, until the relevant .dl- is hit.

    def __init__(self, book):
      self.book = book # save a pointer to the Book object (Ppt or PPh "self") that invoked us, as we will need to
                       # reference its attributes
      self.term = ""
      self.paragraph = ""
      self.definition = ""

    # Overridable routine to bump the current line counter
    # (Ppt will simply increment Ppt.cl, which counts lines in self.wb. Pph will delete the current line, as it uses
    #  Pph.wb as its output buffer.)
    def bump_cl(self):
      self.book.crash_w_context("Internal error; class method bump_cl not overridden", self.book.cl)

    def analyze_dl(self):
      # Analyzes the .dl (or .dl-) command, saving options and doing common initialization or termination processing
      #
      # Also sets:
      #   self.book.list_item_style ("p" = paragraph, "d" = dl)
      #   self.book. list_item_width (max width of a term/speaker name)
      #   and some other self. or self.book. things

      b = self.book # short pointer to Ppt or Pph "self"

      dopts = {}
      dopts["align"] = "l"
      dopts["break"] = False
      dopts["class"] = ""
      dopts["collapse"] = False
      dopts["combine"] = False
      dopts["dindent"] = 0
      dopts["float"] = True
      dopts["hang"] = True
      dopts["id"] = ""
      dopts["start"] = True
      dopts["style"] = "d"
      dopts["tindent"] = 0
      dopts["width"] = 10
      dopts["debug"] = False

      if b.wb[b.cl].startswith(".dl-"): # ending a list
        b.crash_w_context("No open .dl block to close with .dl-", b.cl)

      else: # beginning a definition list
        if len(b.liststack) > 0:
          if not b.list_item_active:
            b.crash_w_context("Nested list must occur within a list item", b.cl)
        b.push_list_stack(b.list_dotcmds)
        b.fszpush('.dl')

        b.list_type = "d"
        b.list_item_active = False
        prev_width = b.list_item_width # remember item width for prior level of list, if any

        options = b.wb[b.cl][4:].strip()

        if "align=" in options:
          options, temp = b.get_id("align", options)
          if temp.lower().startswith("l"):
            dopts["align"] = "l"
          elif temp.lower().startswith("r"):
            dopts["align"] = "r"
          else:
            b.crash_w_context("Invalid align value: {}".format(temp), b.cl)

        if "break=" in options:
          options, temp = b.get_id("break", options)
          if temp.lower().startswith("y"):
            dopts["break"] = True
          elif temp.lower().startswith("n"):
            dopts["break"] = False
          else:
            b.crash_w_context("Invalid break value: {}".format(temp), b.cl)

        if "class=" in options:
          options, dopts["class"] = b.get_id("class", options)

        if "collapse=" in options:
          options, temp = b.get_id("collapse", options)
          if temp.lower().startswith("y"):
            dopts["collapse"] = True
          elif temp.lower().startswith("n"):
            dopts["collapse"] = False
          else:
            b.crash_w_context("Invalid collapse value: {}".format(temp), b.cl)

        if "combine=" in options:
          options, temp = b.get_id("combine", options)
          if temp.lower().startswith("y"):
            dopts["combine"] = True
          elif temp.lower().startswith("n"):
            dopts["combine"] = False
          else:
            b.crash_w_context("Invalid combine value: {}".format(temp), b.cl)

        if "break=" in options:
          if dopts["combine"]:
            options, temp = b.get_id("break", options)
            if temp.lower().startswith("y"):
              dopts["break"] = True
            elif temp.lower().startswith("n"):
              dopts["break"] = False
            else:
              b.crash_w_context("Invalid break value: {}".format(temp), b.cl)
          else:
            self.warn_w_context(".dl break option applies only when combine=y", b.cl)

        if "dindent=" in options:
          options, temp = b.get_id("dindent", options)
          try:
            dopts["dindent"] = int(temp)
          except:
            b.crash_w_context("Invalid dindent value: {}".format(temp), b.cl)

        if "float=" in options:
          options, temp = b.get_id("float", options)
          if temp.lower().startswith("y"):
            dopts["float"] = True
          elif temp.lower().startswith("n"):
            dopts["float"] = False
          else:
            b.crash_w_context("Invalid float value: {}".format(temp), b.cl)

        if "style=" in options:
          options, temp = b.get_id("style", options)
          if temp.lower().startswith("d"):
            dopts["style"] = "d"
          elif temp.lower().startswith("p"):
            dopts["style"] = "p"
            dopts["hang"] = False
          else:
            b.crash_w_context("Invalid style value: {}".format(temp), b.cl)
        b.list_item_style = dopts["style"]

        if "hang=" in options:
          options, temp = b.get_id("hang", options)
          if temp.lower().startswith("y"):
            if dopts["style"] == "d":
              dopts["hang"] = True
            else:
              b.warn_w_context("hang=y ignored for .dl with style=p; using hang=n instead.", b.cl)
          elif temp.lower().startswith("n"):
            dopts["hang"] = False
          else:
            b.crash_w_context("Invalid hang value: {}".format(temp), b.cl)

        if "id=" in options:
          options, dopts["id"] = b.get_id("id", options)

        if "tindent=" in options:
          options, temp = b.get_id("tindent", options)
          try:
            dopts["tindent"] = int(temp)
          except:
            b.crash_w_context("Invalid tindent value: {}".format(temp), b.cl)

        if "w=" in options:
          options, temp = b.get_id("w", options)
          try:
            dopts["width"] = int(temp)
          except:
            b.crash_w_context("Invalid w= value: {}".format(w), b.cl)
        b.list_item_width = dopts["width"]

        if "debug=" in options:
          options, temp = b.get_id("debug", options)
          if temp.lower().startswith("y"):
            dopts["debug"] = True
          elif temp.lower().startswith("n"):
            dopts["debug"] = False
          else:
            b.crash_w_context("Invalid debug value: {}".format(temp), b.cl)

        if options.strip() != "":
          b.warn_w_context("Unknown options on .dl directive: {}".format(options), b.cl)

      return dopts

    # Print debug info if requested
    def print_debug(self, info): # Ppt and Pph will override this
      self.print_msg(info)

    # Format debug info if requested
    def format_debug(self): # Basic data gathering.
      if self.options["debug"]:
        b = self.book
        s = []
        s.append("*** " + b.wb[b.cl])
        s.append("*** options: ")
        keylist = list(self.options.keys())
        keylist.sort()
        for key in keylist:
          s.append("             " + key + ": " + str(self.options[key]))
        s.append("***")
        self.print_debug(s) # let Ppt or Pph figure out what to do with it

    # Routine to handle beginning of a .dl
    def begin_dl(self):
      self.book.crash_w_context("Internal error; class method begin_dl not overridden", self.book.cl)

    # Routine to handle .dl-
    def end_dl(self):
      b = self.book
      b.pop_list_stack()
      b.fszpop('.dl')
      self.bump_cl()

    # Routine to wrap a definition line that is too long
    def wrap_def(self):
      self.book.crash_w_context("Internal error; class method wrap_def not overridden", self.book.cl)

    # Routine to layout a term + definition (non-combining mode)
    def layout(self):
      self.book.crash_w_context("Internal error; class method layout not overridden", self.book.cl)

    # Routine to emit term + definition (non-combining mode)
    def emit_def(self):
      self.book.crash_w_context("Internal error; class method emit_def not overridden", self.book.cl)

    # Emit a paragraph of definition/dialog for the case where combining
    def emit_paragraph(self):
      self.book.crash_w_context("Internal error; class being_dl not overridden", self.book.cl)

    # Routine to finish up any necessary .dl processing before .dl- is handled
    def finalize_dl(self):
      self.book.crash_w_context("Internal error; class method finalize_dl not overridden", self.book.cl)

    # Routine to handle blank lines after the first one
    def add_blank(self):
      self.book.crash_w_context("Internal error; class method add_blank not overridden", self.book.cl)

    # Routine to handle class= operand on a .dd statement
    def set_dd_class(self):
      self.book.crash_w_context("Internal error; class method set_dd_class not overridden", self.book.cl)

    # Routine to handle special lines (bn info)
    def emit_special(self, bninfo):
      self.book.crash_w_context("Internal error; class method handle_special_line not overridden", self.book.cl)

    # main processing
    def run(self):

      b = self.book # short pointer to Ppt or Pph "self"

      self.options  = self.analyze_dl()  # Determine kind of .dl and any specified options
      self.format_debug()
      self.bump_cl()

      # Start of definition list
      # (we won't have a .dl- at this point, as analyze_dl() will issue a crash in that case)

      self.begin_dl() # Let Ppt and Pph do any necessary "beginning of .dl" processing

      # Process the block of statements until we find a matching .dl- or end-of-file
      #
      # Each definition line has one of these forms:
      #   a:  term or speaker name |
      #   b1: term or speaker name | definition or line of dialog
      #   b2: | definition or line of dialog (implied term/speaker)
      #   c:  another line of definition or dialog for prior speaker
      #
      #   d:  .dt term or speaker name
      #       .dd optional-parms definition line of form b2 or c
      #           where optional-parms is class=class-name
      # However, we may also find a page number line, or a .bn info line, which we need to handle specially
      #
      # Notes:
      #   1. Definition lines may be continued using a backslash as the last character. Such
      #        lines will be concatenated (the backslash becomes a space) and wrapped.
      #        Alternatively, when using combine=y successive non-blank lines that do NOT contain a |
      #        (known as format c below) will be combined together. If line breaks are significant then
      #        break=y should be specified, along with combine=y.
      #   2. Blanks preceding the | will be deleted. The | may be followed by
      #        0 or 1 blank (which will be removed). If followed by more than 1 blank all
      #        after the first are significant and will be kept. If a line (after processing
      #        continuation characters) has no | characters (format c), it is treated as a definition/dialog
      #        line where all leading blanks are significant for the first line if combine=y or on
      #        all format c lines if combine=n.
      #   3. Only the first unprotected | within a definition line is significant. Any others will
      #        be considered part of the text.
      #   4. Definition entries may contain other blocks, such as .ul, .ol, .nf, etc.
      #   5. Standard DP formatting has each new speaker as a new paragraph, with a blank line before it, and possibly
      #        a blank line before the speech, depending on how the book was printed. Therefore, 1 blank line before
      #        each format a or b line (or the first format c line after a format a line) will be removed. If there is more
      #        than 1 blank line, the others will be significant and affect vertical spacing.
      #   6. For combine=y:
      #           Definition lines of format c occurring after a definition line of format a or b will be
      #           wrapped into a paragraph with the prior text. The first line will start after the speaker name or term.
      #           Subsequent lines will appear at the left margin (self.regIN) if collapse=y, but aligned under
      #           the first line if collapse=n. Exception: if break=y then line breaks will be preserved while wrapping.
      #   7. For combine=n:
      #           Definition lines of format c will not combine with previous lines, and will be
      #           individually left-aligned at the margin (self.regIN) if collapse=y or placed after the implied term if
      #           collapse=n
      #   8. A .dt logically becomes a line of format a. A .dd logically becomes a line of format b2. However, as that
      #        would always result in a blank line between them, they will be combined as though they were a line of
      #        format b1 if the .dd immediately follows the .dt and if the .dd text does not begin with a | character.
      #   9. A blank line will terminate the current definition. By default one blank line will be placed between
      #        definitions in text output. If more are desired, use .sp to specify them.


      bninfo = ""
      self.pageinfo = ""
      combine_dtdd = False

      while b.cl < len(b.wb) and not b.wb[b.cl] == ".dl-":  # process until we hit our .dl-

        # If we hit a dot command, handle it
        if not b.wb[b.cl].startswith(".dt") and not b.wb[b.cl].startswith(".dd"):
          if re.match(r"\.([a-z]|⓭DV-)", b.wb[b.cl]):
            #if self.options["style"] == "p" or (self.options["combine"] and (self.term or self.paragraph)):
            if self.options["combine"] and (self.term or self.paragraph):
              self.emit_paragraph()
            else:
              assert len(self.dlbuffer) == 0, "Trying to invoke a dot directive from .dl while dlbuffer contains data"

            b.doDot()
            continue

        # Not a dot command, must be a definition or blank line or page number or .bn info
        #
        b.list_item_active = True
        i = b.cl
        #while i < (len(b.wb) - 1) and b.wb[i].endswith("\\"): # handle continued lines
        #  b.wb[i] = b.wb[i][:-1] + " " + b.wb[i+1]
        #  del b.wb[i+1]
        #if b.wb[i].endswith("\\"):
        #  b.crash_w_context("File ends with continued definition line: {}".format(b.wb[i]), i)

        # check for a blank line, which terminates any combining paragraph
        if b.wb[b.cl] == "":
          # check for paragraph that we need to emit
          if self.options["combine"] and (self.term or self.paragraph):
            self.emit_paragraph()
          #else:
          #  if blankfound:
          #    self.add_blank() # emit any blank lines after the first one in a group
          #  else:
          #    blankfound = True
          self.bump_cl()
          continue

        # check for .dt or .dd (form d of definition line) and handle
        # Note: text processing is straightforward: turn into form a or b2
        #       We can ignore the optional parameters on .dd

        if b.wb[b.cl].startswith(".dt"):

          b.wb[b.cl] = b.wb[b.cl][4:] + "|"
          if (b.cl < len(b.wb) - 1) and b.wb[b.cl+1].startswith(".dd"):
            m = re.match(r"\.dd( +class=[^ ]*?)? +(.*)", b.wb[b.cl+1])
            if m and not m.group(2).startswith("|"):
              combine_dtdd = True
              saveline = b.wb[b.cl]
              self.bump_cl()
              continue

        if b.wb[b.cl].startswith(".dd"):

          m = re.match(r"\.dd( +class=[^ ]*?)? +(.*)", b.wb[b.cl])
          if m:
            if m.group(1):
              self.set_dd_class(m.group(1))
            if m.group(2).startswith("|"):   # don't add a | if it's already there as the first character
              b.wb[b.cl] = m.group(2)
            elif combine_dtdd:
              b.wb[b.cl] = saveline + m.group(2)
              combine_dtdd = False
            else:
              b.wb[b.cl] = "|" + m.group(2)
          else:
            b.crash_w_context("Error parsing .dd directive: {} \n".format(b.wb[b.cl]), b.cl)

        # Must be .pn or .bn or format a, b1, b2, or c line at this point
        # If .pn or .bn it may take these forms:
        #    .pn info (standalone) if it precedes a .dt or .dd directive
        #        In this case, remember it and skip over the line; emit as for next case
        #    .pn info + rest of line
        #        Rest of line may be one of format a, b1, b2, or c. If format a, b1, or b2. We
        #        can't emit the info without it being inside a <dt> or <dd>, so we extract it
        #        and save it and emit at the front of the next <dt> or <dd> we generate or dump
        #        it out after the </dl> if necessary. If format c we let normal processing handle it.
        #    .bn info
        #        Always stand-alone, and proper handling depends on whether we're combining
        #         or not. If combining, need to wrap onto rest of prior definition, if any,
        #         or emit if no prior definition. If not combining, just emit (we're between defs).
        #
        # check for a line beginning with a page number, or a .bn info line,
        # and handle. Page numbers will be present only in the HTML pass.
        if b.wb[b.cl].startswith("⑯"): # page number, possibly?
          m = re.match(r"(⑯.+?⑰)(.*)", b.wb[b.cl])
          if m: # yes
            if m.group(2): # more on the line?
              if m.group(2).find("|") != -1: # format a/b1/b2?
                self.pageinfo = m.group(1) # grab it and remember
                l = len(m.group(1))          # yes; get length of page number
                b.wb[b.cl] = b.wb[b.cl][l:]  # remove page info from the line (rest of line is normal a/b1/b2 data)
              else:                          # else format c; just let it flow through
                pass
            else: # standalone (before what was a .dt or .dd directive)
              self.pageinfo = m.group(1)
              self.bump_cl()
              continue

        elif b.bnPresent and b.is_bn_line(b.wb[b.cl]): # not a page number; possibly .bn info?
          if not self.options["combine"] or not self.paragraph: # if not combining, or combining but no paragraph yet
            bninfo = b.wb[b.cl] # bninfo is always standalone
            self.emit_special(bninfo)    # handle the page info
            bninfo = ""
            self.bump_cl()                         # and we're done with this line
            continue
          else:                           # combining, and paragraph has data already
            self.paragraph += b.wb[b.cl]  # add the .bn info to the end of the paragraph
            self.bump_cl()                # and we're done with the line
            continue

        # isolate term and definition
        blankfound = False
        t = b.wb[b.cl].split("|", maxsplit=1) # split term and definition
        if len(t) == 2:  # form a or b above
          self.form_c = False
          # new term/speaker needs to force emission of prior paragraph for combine=y
          if self.options["combine"] and (self.term or self.paragraph):
            self.emit_paragraph()

          self.term = t[0].rstrip()
          self.definition = t[1]
          if len(self.definition) >= 1:   # remove at most 1 leading blank from the definition
            if self.definition[0] == " ":
              self.definition = self.definition[1:]

          if self.options["combine"]:
            if self.definition:
              self.paragraph = self.definition
            self.bump_cl()
            continue

        # form c above (no | present in line)
        # bninfo or page number info may precede the data but that's OK, it will be part of
        # the definition but will be found and handled by later processing
        else:
          self.form_c = True
          if not self.options["combine"]: # if not combining,
            self.term = ""
            self.definition = t[0].rstrip() # leading blanks are significant

          else: # combining
            if not self.paragraph: # if first line of definition
              self.term = ""           # nullify the term
              t[0] = t[0].rstrip() # remove only trailing blanks from form c line

            tempbr = "<br>" if (b.booktype == "text") else "<br>" # void element
            separator = tempbr if (self.options["break"]) else " "
            if self.paragraph:
              self.paragraph += separator
            self.paragraph += t[0]
            self.bump_cl()
            continue

        # wrap the definition as needed (Note: only get here if not combining)
        #
        self.wrap_def()

        # layout the term and definition line(s)
        self.layout()

        # append definition line(s) to output
        self.emit_def()

        self.bump_cl()

      # hit eof or .dl-
      if b.cl >= len(b.wb): # oops: no .dl- for me
        b.crash_w_context("Missing .dl- for this .dl block", self.dlstart)

      else:
        if self.options["combine"] and (self.term or self.paragraph):
          self.emit_paragraph()


      # At this point we have hit the .dl- that matches our .dl, so
      # First, we give Ppt or Pph an opportunity to do any final output for the current .dl
      # Then we allow them to do whatever final cleanup may be needed
      self.finalize_dl()
      self.end_dl()

      return

  # all dot commands are switched here
  def doDot(self):
    dotcmd = self.wb[self.cl][0:3]
    try:
      switch = self.dotcmds[dotcmd]
    except KeyError:
      self.crash_w_context("unknown dot command: {}".format(self.wb[self.cl]), self.cl)

    if not switch[1]:
      switch[0]()
    elif switch[1] == "cl": # this is the only value for now
      switch[0](self.cl)


  # Issue error message, show context, and terminate
  def crash_w_context(self, msg, i, r=5):
    self.stderr.write("\nERROR: {}\ncontext:\n".format(msg))
    startline = max(0,i-r)
    endline = min(len(self.wb),i+r)
    self.stderr.write(" -----\n")
    for j in range(startline,endline):
      #s = self.umap(self.wb[j])
      s = self.wb[j]
      if j == i:
        self.stderr.write(">> {}\n".format(s))
      else:
        self.stderr.write("   {}\n".format(s))
    self.stderr.write(" -----\n")
    exit(1)

  def warn_w_context(self, msg, i, r=5):
    self.stderr.write("\n**warning: {}\ncontext:\n".format(msg))
    startline = max(0,i-r)
    endline = min(len(self.wb),i+r)
    self.stderr.write(" -----\n")
    for j in range(startline,endline):
      #s = self.umap(self.wb[j])
      s = self.wb[j]
      if j == i:
        self.stderr.write(">> {}\n".format(s))
      else:
        self.stderr.write("   {}\n".format(s))
    self.stderr.write(" -----\n")

  # Expand encoded superscripts and subscripts
  def expand_supsub(self, s):
    # superscripts
    m = re.search(r"◸(.*?)◹", s)
    while m:
      supstr = m.group(1)
      if len(supstr) == 1 or self.truelen(supstr, expand_supsub=False) == 1:
        s = re.sub(r"◸.◹", "^"+supstr, s, 1)
      else:
        s = re.sub(r"◸.*?◹", "^{" + supstr + "}", s, 1)
      m = re.search(r"◸(.*?)◹", s)
    # subscripts
    s = s.replace("◺", "_{")
    s = s.replace("◿", "}")
    return s


  # Calculate "true" length of a string, accounting for <lang> markup and combining or non-spacing characters in Hebrew, etc.
  # Also, take into account text encoded for super/subscripts, since the eventual decoding will change the text length.
  def truelen(self, s, expand_supsub=True):
    #self.dprint("entered: {}".format(s))
    if self.bnPresent:
      s = self.bnsearch.sub("", s) # remove any bn info before trying to calculate the length
      s = self.pnsearch.sub("", s) # remove any pn info before trying to calculate the length

    if expand_supsub and ("◸" in s or "◺" in s):
      s = self.expand_supsub(s)

    # if string has ⓯ it will become one character longer (⓯ -> _}) so we need
    # to expand it to get the proper length. Note that we do not need to worry
    # about ⓮ which becomes ^ as the length doesn't change.
    if "⓯" in s:
      s = re.sub("⓯", "_{", s)

    l = len(s) # get simplistic length
    for c in s: # examine each character
      cc = ord(c)
      if cc > 767: # No non-spacing characters < \u0300 (768)
        cat = unicodedata.category(c)
        bidi = unicodedata.bidirectional(c)
        name = unicodedata.name(c)
        #self.dprint("name: {}; cat: {}; bidi: {}".format(name, cat, bidi))
        if cat == "Cf" or (cat == "Mn" and bidi == "NSM"): # Control character, or Modifier Non-Spacing-Mark?
          l -= 1 # if so, it doesn't take any space
    return l

  # truefmt: .format() replacement for strings that may contain combining or non-spacing characters
  # fmtspec: a simplified form of normal format specification, :[^<>]len{}
  def truefmt(self, fmtspec, s):
    m = re.match(r"{:([\^<>])(\d+)}", fmtspec)
    if m:
      align = m.group(1)
      width = int(m.group(2))
      len = self.truelen(s)
      if len >= width:
        return s
      elif align == "^":  # centering
        pad = " " * ((width - len)//2) # 1/2 the blanks before & after the string
        padextra = " " * ((width - len)%2) # plus possibly 1 more after
        s2 = pad + s + pad + padextra
      elif align == "<":  # left-aligned
        pad = " " * (width-len)  # all the blanks after
        s2 = s + pad
      else: # right-aligned
        pad = " " * (width-len)  # all the blanks before
        s2 = pad + s
      return s2
    else:
      raise RuntimeError("ppgen: internal error, unexpected truefmt argument: {}".format(fmtspec))

  # Recognize lines that are bn info
  def is_bn_line(self, line):
    return True if (line and line[0] == "⑱" and self.bnmatch.match(line)) else False

  # extract content of an optionally quoted string
  # used in .nr

  def deQuote(self, s, i):
    m = re.match(r"([\"'])(.*)\1", s)  # If properly quoted
    if m:
      return m.group(2)
    elif s.startswith("\"") or s.startswith("'") or s.endswith("\"") or s.endswith("'"):
      self.crash_w_context("incorrect value: {}".format(s), i)
    else:
      return s


  #
  # process saved .sr requests
  #
  def process_SR(self, buffer, srnum):

    def pythonSR(match):
      if not self.pmcount: # if first python macro this pass, initialize a dictionary
        self.savevar = {}  # to allow macros to communicate
      self.pmcount += 1
      var = {}
      var["count"] = 0 # count of input variables; none, as the match object is implicit
      var["match"] = match
      var["name"] = srrMacname # the name of the macro, in case the macro cares for some reason
      var["srchfor"] = self.srs[srnum]
      var["hint"] = srrHint    # the string after the macro name in the replace expression, or None
      var["out"] = [] # place for macro to put its output
      var["type"] = self.booktype # text or html
      var["style"] = ".sr"
      # below 3 lines don't make sense during .sr
      #var["ll"] = self.regLL  # specified line length
      #var["in"] = self.regIN  # specified
      #var["nr-nfl"] = self.nregs["nfl"] # .nr nfl value
      macglobals = __builtins__.__dict__
      macglobals["var"] = var # make macro variables available
      macglobals["re"] = re # make re module available
      macglobals["toRoman"] = self.toRoman2
      macglobals["fromRoman"] = self.fromRoman
      macglobals["debugging"] = [self.bailout, self.wb, -1]
      macglobals["savevar"] = self.savevar # make communication dictionary available
      maclocals = {"__builtins__":None}

      try: # exec the macro
        exec(self.macro[srrMacname][1], macglobals, maclocals)
      except:
        where = traceback.extract_tb(sys.exc_info()[2])[-1]
        if where[0] == "<macro {}>".format(srrMacname):
          macro_line = "{}:".format(where[1]-1) + self.macro[srrMacname][3][where[1]-1]
        else:
          macro_line = "not available"
        mac_info = "Exception occurred running Python macro {} during .sr at\n       Source line {}\n".format(srrMacname,
                                                                                                              macro_line)
        trace_info = traceback.format_exception(*sys.exc_info())
        self.fatal(mac_info + "\n".join(trace_info))

      try: # try to grab its output
        output = var["out"]
      except:
        traceback.print_exc()
        self.fatal("Above error occurred trying to copy output from Python macro {}".format(srrMacname))

      return output

    k = 0
    l = 0
    ll = 0
    restore_srr = "" # no srr string to replace

    # handle python macros as replacement strings
    if self.srr[srnum].startswith("{{python"): # Possibly a python macro call as replace string?
      m = re.match("\{\{python ([^ ]+) ?(.*?)\}\}", self.srr[srnum]) # yes, check syntax
      if m:  # yes, a Python macro call
        restore_srr = self.srr[srnum] # remember original srr string so we can restore it
        self.srr[srnum] = pythonSR    # set srr so it will invoke the pythonSR function during replace processing
        srrMacname = m.group(1)  # capture python macro name
        srrHint = m.group(2)
        # validate macro exists, and is Python
        if not srrMacname in self.macro: # Does the macro exist:
          self.fatal(".sr number {} tried to invoke macro {} that is not defined.".format(srnum+1,
                               srrMacname))
        elif self.macro[srrMacname][0] != "p":        # yes, is it a Python macro?
          self.fatal(".sr number {} tried to invoke non-Python macro {}.".format(srnum+1,
                               srrMacname))

    if "\\n" in self.srs[srnum]: # did user use a regex containing \n ? If so, process all lines in one blob
      text = '\n'.join(buffer) # form lines into a blob
      try:
        m = re.search(self.srs[srnum], text) # search for current search string
      except:
        if 'd' in self.debug:
          traceback.print_exc()
          self.fatal("Above error occurred searching for {} in complete text blob".format(self.srs[srnum]))
        else:
          self.fatal("Error occurred searching for {} in complete text blob".format(self.srs[srnum]))
      if m:                                             # if found
        if 'r' in self.debug:
          self.print_msg("Search string {}:{} found in complete text blob".format(srnum+1, self.srs[srnum]))
        try:
          text, l = re.subn(self.srs[srnum], self.srr[srnum], text) # replace all occurrences in the blob
          ll += l
        except:
          if 'd' in self.debug:
            traceback.print_exc()
            self.fatal("Above error occurred replacing:{}\n  with {}\n  in complete text blob".format(self.srs[srnum], self.srr[srnum]))
          else:
            self.fatal("Error occurred replacing:{}\n  with {}\n  in complete text blob".format(self.srs[srnum], self.srr[srnum]))
        if 'r' in self.debug:
          self.print_msg("Replaced with {}".format(self.srr[srnum]))
      self.print_msg("Search string {}:{} matched in complete text and replaced {} times.".format(srnum+1,
            self.srs[srnum], ll))
      buffer[:] = text.splitlines() # break blob back into individual lines
      text = ""

    else:
      quit = False
      j = 0
      while j < len(buffer) and not quit:
        linecnt = 1 # number of lines replaced into buffer by replace operation (assume only 1)
        try:
          m = re.search(self.srs[srnum], buffer[j]) # search for current search string
        except:
          if 'd' in self.debug:
            traceback.print_exc()
            self.fatal("Above error occurred searching for\n  {}\n in: {}".format(self.srs[srnum], buffer[j]))
          else:
            self.fatal("Error occurred searching for\n  {}\n in: {}".format(self.srs[srnum], buffer[j]))
        if m:                                   # if found
          k += 1
          if 'r' in self.debug or 'p' in self.srw[srnum]: # if debugging, or if prompt requested
            self.print_msg("Search string {}:{} found in:\n    {}".format(srnum+1,
                  self.srs[srnum], buffer[j]))
          try:
            if 'p' in self.srw[srnum]:                                           # prompting requested?
              l = 0
              temp = re.sub(self.srs[srnum], self.srr[srnum], buffer[j])
              self.print_msg("replacement will be:\n    {}".format(temp))
              try:
                reply = input("replace? (y/n/q/r)")
              except EOFError:
                self.print_msg("EOF received on prompt; assuming q")
                reply = "q"
              good_reply = False
              while not good_reply:
                if reply == "y":                                               # if user replied y (yes)
                  #buffer[j], l = re.subn(self.srs[srnum], self.srr[srnum], buffer[j])    # replace all occurrences in the line
                  temp, l = re.subn(self.srs[srnum], self.srr[srnum], buffer[j])    # replace all occurrences in the line
                  good_reply = True
                elif reply == "r":                                             # else if user replied r (run)
                  #buffer[j], l = re.subn(self.srs[srnum], self.srr[srnum], buffer[j])    # replace all occurrences in the line
                  temp, l = re.subn(self.srs[srnum], self.srr[srnum], buffer[j])    # replace all occurrences in the line
                  self.srw[srnum] = self.srw[srnum].replace("p","")                      # and stop prompting
                  good_reply = True
                elif reply == "n":                                             # else if user replied n (no)
                  self.print_msg("skipping that one")
                  good_reply = True
                elif reply == "q":                                             # else if user replied q (quit)
                  self.print_msg("exiting at user request")
                  good_reply = True
                  quit = True
            else:                                                            # not prompting
              #buffer[j], l = re.subn(self.srs[srnum], self.srr[srnum], buffer[j])    # replace all occurrences in the line
              temp, l = re.subn(self.srs[srnum], self.srr[srnum], buffer[j])    # replace all occurrences in the line

            tempbuf = temp.split("\n") # split the result in case .sr added any \n
            buffer[j:j+1] = tempbuf    # assign back into buffer, replacing line j and then inserting any other lines
            #buffer[j] = temp
            linecnt = len(tempbuf)     # get count of total lines for incrementing j past them
            ll += l
          except:
            if 'd' in self.debug:
              traceback.print_exc()
              self.fatal("Above error occurred replacing:{}\n  with {}\n  in: {}".format(self.srs[srnum], self.srr[srnum], buffer[j]))
            else:
              self.fatal("Error occurred replacing:{}\n  with {}\n  in: {}".format(self.srs[srnum], self.srr[srnum], buffer[j]))
          if 'r' in self.debug:
            self.print_msg("Replaced: {}".format(buffer[j]))

        j += linecnt # bump past the line we worked on, or that line plus others we inserted

      if quit:
        exit(1)
      self.print_msg("Search string {}:{} matched in {} lines, replaced {} times.".format(srnum+1,
            self.srs[srnum], k, ll))
      if restore_srr:    # if we had a Python macro as replace string, restore original replace string
        self.srr[srnum] = restore_srr


  # .nr named register
  # we are here if the line starts with .nr
  def doNr(self):
    m = re.match(r"\.nr +(.+?) +(.+)", self.wb[self.cl])
    if not m:
      self.crash_w_context("malformed .nr directive", self.cl)
    else:
      registerName = m.group(1)
      registerValue = m.group(2)
      if registerName in self.nregs:
        self.nregs[registerName] = self.deQuote(m.group(2), self.cl)
        if registerName in self.nregsusage:
          self.nregsusage[registerName] += 1 # bump count of times we've specified this reg
      else:
        self.crash_w_context("undefined register: {}".format(registerName), self.cl)
      del(self.wb[self.cl])

  def rejectWithinList(self):
    cmd = self.wb[self.cl][0:3]
    self.crash_w_context("{} directive not allowed within .ul, .ol, or .dl block".format(cmd), self.cl)

  # push the list-related settings onto a stack when beginning a new list
  def push_list_stack(self, dotcmds):
    self.dotcmdstack.append(self.dotcmds)
    self.outerstyle = self.list_item_style # remember item style for outer level of list, if any
    self.outerwidth = self.list_item_width # also outer item width
    self.outertype = self.list_type        # and outer list type
    self.outerregIN = self.regIN
    # save important info for nested lists
    self.liststack.append((self.list_type,       # 0
                           self.list_item_style, # 1
                           self.list_item_value, # 2
                           self.list_item_width, # 3
                           self.dlbuffer,        # 4
                           self.list_item_active,# 5
                           self.list_space,      # 6
                           self.regIN,           # 7
                           self.outerwidth,      # 8
                           self.regTI,           # 9
                           self.regTIp,          # 10
                           self.outerstyle,      # 11
                           self.outertype,       # 12
                           self.outerregIN,      # 13
                           self.list_hang,       # 14
                           self.list_align))     # 15
    self.dotcmds = dotcmds   # restrict set of valid dot cmds within a list
    self.regTI = 0    # always start these at 0 for a new stack
    self.regTIP = 0

  # pop the stacked list settings and restore to self variables
  def pop_list_stack(self):
    currlist = self.liststack.pop()
    self.list_type = currlist[0]
    self.list_item_style = currlist[1]
    self.list_item_value = currlist[2]
    self.list_item_width = currlist[3]
    self.dlbuffer = currlist[4]
    self.list_item_active = currlist[5]
    self.list_space = currlist[6]
    self.regIN = currlist[7]
    self.outerwidth = currlist[8]
    self.regTI = currlist[9]
    self.regTIp = currlist[10]
    self.outerstyle = currlist[11]
    self.outertype = currlist[12]
    self.outerregIN = currlist[13]
    self.list_hang = currlist[14]
    self.list_align = currlist[15]
    self.dotcmds = self.dotcmdstack.pop()

  # Handle font-size stacking for ppgen blocks (.fn, .ul/ol/dl, .dv) that can contain other elements
  # type: string, '.fn', '.ul', etc.
  # Note: We also push the current fsstack, and set to base state, and then restore it when popping,
  #       so that all font-size effects/changes done within the block are completely local to the block
  def fszpush(self, type):
    self.blkfszstack.append((self.fsz, type, self.fsstack))
    del self.fsstack[:] # reset the fsstack to base state

  def fszpop(self, type):
    if self.blkfszstack:  # restore prior block's font-size if possible and fsstack
      self.fsz, fsztype, self.fsstack = self.blkfszstack.pop()
      if fsztype != type:
        self.crash_w_context("Improper nesting of .fs requests across blocks. Expecting {}-".format(fsztype))
    else:
      self.crash_w_context("Font-size stack empty while processing {}-".format(type))

  # Check for proper termination of .dv block and for proper nesting of any internal
  # .dv, .fn, .ul, .ol, and/or .dl blocks
  # At entry, self.cl points to the initial .dv directive
  def checkDvNest(self):
    j = self.cl

    ulnest = olnest = dlnest = fnnest = 0      # assume we are properly nested within other elements

    while j < len(self.wb):

      if self.wb[j].startswith(".ul-"):
        ulnest -= 1
      elif self.wb[j].startswith(".ul"):
        ulnest += 1
      elif self.wb[j].startswith(".ol-"):
        olnest -= 1
      elif self.wb[j].startswith(".ol"):
        olnest += 1
      elif self.wb[j].startswith(".dl-"):
        dlnest -= 1
      elif self.wb[j].startswith(".dl"):
        dlnest += 1
      elif self.wb[j].startswith(".fn-"):
        fnnest -= 1
      elif self.wb[j].startswith(".fn"):
        fnnest += 1

      else:
        if self.wb[j] == ".dv-":
          nested = ulnest + olnest + dlnest + fnnest
          if nested:
            ul = "ul " if ulnest else ""
            ol = "ol " if olnest else ""
            dl = "dl " if dlnest else ""
            fn = "fn" if fnnest else ""
            nesterr = ul + ol + dl + fn
            self.crash_w_context("Improper block nesting of {} found at .dv-".format(nesterr), j)
          if self.dvstack:
            dummy, (ulnest, olnest, dlnest, fnnest) = self.dvstack.pop()

          else:
            self.crash_w_context(".dv- found, but no open .dv block to close", j)

          if not self.dvstack: # did this .dv- leave us with all open .dv blocks closed?
            break              # yes

        elif self.wb[j].startswith(".dv"):
          self.dvstack.append((j, (ulnest, olnest, dlnest, fnnest))) # remember where we started & block nesting

      j += 1

    if j >= len(self.wb):          # oops; hit end of file before .dv-
      if len(self.dvstack) > 1:    # were we nested?
        self.crash_w_context("{} unclosed nested .dv directives; showing outer one.".format(len(self.dvstack)),
                             self.dvstack[0][0])
      else:
        self.crash_w_context("Unclosed .dv directive:", self.dvstack[0][0])

    return j


  # Parse options on .ul or .ol directives
  # type: "u" (.ul) or "o" (.ol)
  # options:
  #   for .ul:  style="disc | circle | square | none" (default: disc)
  #   for .ol: style="decimal | lower-alpha | lower-roman | upper-alpha | upper-roman" (default: decimal)
  #   indent="2" (indent is to the marker.)
  #   for .ol: w="2" (number of characters allowed for the item "number")
  #   for .ol: align=r (default) or l
  #   space=n (default) or y
  #   hang=n (default) or y
  #   id=<id-value> (ignored in text)
  #   class=<class-value> (ignored in text)
  #   align=r (default) or l (ignored in HTML)
  #
  def parse_UlOl_options(self, type):
      options = self.wb[self.cl][4:].strip()

      id     = ""
      clss   = ""
      indent = -1

      self.ulolopt = {}

      if "indent=" in options:
        options, indent = self.get_id("indent", options)
        if indent:
          try:
            temp = int(indent)
          except:
            self.crash_w_context("Invalid indent= value: {}".format(indent), self.cl)
          else:
            indent = temp
            self.ulolopt["indent"] = indent

      if "style=" in options:
        options, style = self.get_id("style", options)
      else:
        style = ""

      if type == "u":
        if style:
          if style.lower() in self.list_styles_u:
            self.list_item_style = style.lower()
          else:
            self.warn_w_context("Unrecognized list item style {}, disc assumed.".format(style), self.cl)
            self.list_item_style = 'disc'
        else:
          self.list_item_style = ['disc', 'circle', 'square'][(len(self.liststack) - 1) % 3] # figure out marker character for items

      else: # type = "o"
        if style:
          style_tuple = self.list_styles_o.get(style.lower())
          if style_tuple != None:
            self.list_item_style = style_tuple
          else:
            self.warn_w_context("Unrecognized list item style {}, decimal assumed.".format(style), self.cl)
            self.list_item_style = self.list_styles_o.get('decimal')
        else:
          self.list_item_style = self.list_styles_o.get('decimal')

      self.ulolopt["style"] = self.list_item_style

      if type == "o": # handle width for .ol
        if "w=" in options:
          options, w = self.get_id("w", options)
          try:
            self.list_item_width = int(w) + 2 # specified width of number, + 2 for separator and a space
          except:
            self.crash_w_context("Invalid w= value: {}".format(indent), self.cl)
        else:
          self.list_item_width = 4 # default 2 for width of number, + 2 for separator and a space

      else: # handle width for .ul
        if self.list_item_style != "none":
          self.list_item_width = 2 # 1 for the marker character + 1 for a blank
        else:
          self.list_item_width = 0 # no room needed for marker for .ul style=none

      self.ulolopt["indent"] = self.list_item_width

      if "align=" in options:
        options, align = self.get_id("align", options)
        temp = align.lower()[0]
        if temp != "l" and temp != "r":
          self.warn_w_context("Unrecognized align value: {}, r assumed.".format(align))
          self.list_align = "r"
        else:
          self.list_align = temp
      else:
        self.list_align = "r"

      self.ulolopt["align"] = self.list_align

      if "id=" in options:
        options, id = self.get_id("id", options)

      if "class=" in options:
        options, clss = self.get_id("class", options)

      if "hang=" in options:
        options, hang = self.get_id("hang", options)
        if hang.lower().startswith("y"):
          self.list_hang = True
        elif hang.lower().startswith("n"):
          self.list_hang = False
        else:
          self.warn_w_context("Unknown hang value: {}. hang=no assumed".format(hang), self.cl)
          self.list_hang = False
      else:
        self.list_hang = False

      self.ulolopt["hang"] = self.list_hang

      if "space=" in options:
        options, space = self.get_id("space", options)
        if space.lower().startswith("y"):
          self.list_space = True
        elif space.lower().startswith("n"):
          self.list_space = False
        else:
          self.warn_w_context("Unknown spaced value: {}. spaced=no assumed".format(spaced), self.cl)
          self.list_space = False
      else:
        self.list_space = False

      self.ulolopt["space"] = self.list_space

      if options.strip() != "":
        self.warn_w_context("Unknown options on .ul directive: {}".format(options), self.cl)

      return (indent, id, clss)

  # Does common processing for doUl. Returns False if .ul- and True if .ul
  #   note: CSS specifications more limited in some ways; only specific specifications allowed
  #         but also allow none (space). Also, separator is always a "." for ol, ex. for "none".
  #         \u25aa: small black square ▪
  #         \u25cb: circle (unfilled) ○
  #         \u25cf: disc (filled black circle) ●
  #         default order when nested is disc, circle, square ●○▪
  def doUlCommon(self):

    id     = ""
    clss   = ""
    active = self.list_item_active      # remember if a list item was active or not before the .ul/.ul-

    if self.wb[self.cl].startswith(".ul-"): # ending a list
      if self.list_type == None:
        self.crash_w_context("No open .ul block to close with .ul-", self.cl)
      elif self.list_type != "u":
        self.crash_w_context("Cannot close .ol block with .ul-", self.cl)
      self.pop_list_stack()
      self.fszpop('.ul')
      return (False, active, -1, id, clss)

    else: # beginning an unordered list
      if len(self.liststack) > 0:
        if not self.list_item_active:
          self.crash_w_context("Nested list must occur within a list item", self.cl)

      self.push_list_stack(self.list_dotcmds)
      self.fszpush('.ul')

      self.list_type = "u"
      self.list_item_active = False

      indent, id, clss = self.parse_UlOl_options("u")

      return (True, active, indent, id, clss)

  # Does common processing for doOl. Returns False if .ol- and True if .ol
  def doOlCommon(self):

    id     = ""
    clss   = ""
    active = self.list_item_active      # remember if a list item was active or not

    if self.wb[self.cl].startswith(".ol-"): # ending a list
      if self.list_type == None:
        self.crash_w_context("No open .ol block to close with .ol-", self.cl)
      elif self.list_type != "o":
        self.crash_w_context("Cannot close .ul block with .ol-", self.cl)
      self.pop_list_stack()
      self.fszpop('.ol')
      return (False, active, -1, id, clss)

    else: # beginning an ordered list
      if len(self.liststack) > 0:
        if not self.list_item_active:
          self.crash_w_context("Nested list must occur within a list item", self.cl)

      self.push_list_stack(self.list_dotcmds)
      self.fszpush('.ol')

      self.list_type = "o"
      self.list_item_active = False

      self.list_item_value = 0 # will force to start at 1

      indent, id, clss = self.parse_UlOl_options("o")

      return (True, active, indent, id, clss)

  # Does common processing for doIt.
  def doItCommon(self):
    if self.list_type != "o" and self.list_type != "u": # do we have a list?
      self.crash_w_context("No open .ol/.ul block for .it directive", self.cl)
    if self.wb[self.cl] == ".it" or self.wb[self.cl] == ".it-":
      self.crash_w_context("Block form of .it no longer supported.", self.cl)



  def preProcessCommon(self):

    #def pushk(s, i):
    #  self.nfstack.append( (s,i) )

    #def popk():
    #  t = self.nfstack.pop() # pops a tuple
    #  return t

    def gkrepl(gkmatch):
      gkstring = gkmatch.group(1)
      if self.log:
        try:
          self.print_msg("Processing: {}".format(gkstring))
        except:
          print("Processing: {}".format(gkstring))
      count = 0 # count of built-in Greek characters converted
      count1 = 0 # count of PPer-provided Greek characters converted

      # Protect any <pm> tags within the Greek string by saving the pm and macro name, then replacing
      #   them with \u2ac9
      # Later we will restore each saved value.
      pm_found = False
      pm_list = []
      m = re.search(r"(^|[^\\])<(pm +[^ >]+)( .*?[^\\])>", gkstring)
      while m:
        pm_found = True
        pm_list.append(m.group(2))
        gkstring = re.sub(m.group(0), m.group(1) + "<\u2ac9" + m.group(3) + ">", gkstring, 1)
        m = re.search(r"(^|[^\\])<(pm +[^ >]+)( .*?[^\\])>", gkstring)

      if len(self.gk_user) > 0:   # if PPer provided any additional Greek mappings apply them first
        for s in self.gk_user:
          try:
            gkstring, count2 = re.subn(re.escape(s[0]), s[1], gkstring)
            count1 += count2
            if count2 > 0 and 'l' in self.debug:
              try:
                self.print_msg("Replaced PPer-provided Greek character {} {} times.".format(s[0], count2))
              except:
                self.print_msg("Replaced PPer-provided Greek character {} {} times.".format(s[0], count2))
          except:
            self.warn("Error occurred trying to replace PPer-provided Greek character " +
                      "{} with {}. Check replacement value".format(s[0], s[1]))
      for s in self.gk:
        gkstring, count2 = re.subn(s[0], s[1], gkstring)
        count += count2
        if count2 > 0 and 'l' in self.debug:
          try:
            self.print_msg("Replaced Greek {} {} times.".format(s[0], count2))
          except:
            self.print_msg("Replaced Greek {} {} times.".format(s[0], count2))
      if self.log:
        if len(self.gk_user) > 0:
          self.print_msg("Replaced {} PPer-provided Greek characters and {} built-in Greek characters".format(count1, count))
        else:
          self.print_msg("Replaced {} built-in Greek characters".format(count))

      # Restore any protected <pm> tags
      if pm_found:
        for i, pm_string in enumerate(pm_list):
          gkstring = re.sub("\u2ac9", pm_string, gkstring, 1)

      gkorigb = ""
      gkoriga = ""
      if self.gkkeep.lower().startswith("b"): # original before?
        gkorigb = gkmatch.group(0)
      elif self.gkkeep.lower().startswith("a"): # original after?
        gkoriga = gkmatch.group(0)
      gkfull = gkorigb + self.gkpre + gkstring + self.gksuf + gkoriga

      # Check for errant accent marks within the substituted Greek
      temp_gkstring = gkstring
      if "</g>" in temp_gkstring: # make sure that </g> doesn't trigger the warning
        temp_gkstring = re.sub("</?g>", "", temp_gkstring)
      if " \[" in temp_gkstring: # make sure that \[ (escaped [) doesn't trigger the warning
        temp_gkstring = re.sub(r" \\\[", "", temp_gkstring)
      m = re.search(r"[~=_)(/\\|+]", temp_gkstring)
      if m:
        self.warn("Possible accent problem in Greek string {} with result {}".format(gkmatch.group(0), gkstring))

      gkfull = gkfull.replace(r"\|", "⑩") # temporarily protect \| and \(space) so they
      gkfull = gkfull.replace(r"\ ", "⑮") # retain their special meaning within [Greek: ...] tags in case keep was specified
      #gkfull = gkfull.replace(r"\]", "\④") # also \] needs to become protected here, but with an added \
      gkfull = gkfull.replace(r"\]", "④") # also \] needs to become protected here

      return gkfull

    def loadFilter():
      text = []

      if not os.path.isfile(self.cvgfilter):
        self.fatal("specified filter file {} not found".format(self.cvgfilter))

      encoding = ""
      try:
        wbuf = open(self.cvgfilter, "rU", encoding='UTF-8').read()
        encoding = "utf_8"
        text = wbuf.split("\n")
        # remove BOM on first line if present
        t = ":".join("{0:x}".format(ord(c)) for c in text[0])
        if t[0:4] == 'feff':
          text[0] = text[0][1:]
      except:
        pass

      if encoding == "":
        try:
          wbuf = open(self.cvgfilter, "r", encoding='latin_1').read()
          self.encoding = "latin_1"
          text = wbuf.split("\n")
        except Exception as e:
          pass

      if encoding == "":
        self.fatal("cannot determine filter file encoding")

      while text[-1] == "": # no trailing blank lines
        text.pop()

      uncomment(text)  # remove comments and un-escape / characters

      # insert the filter lines at the front of self.wb
      self.wb[0:0] = text
      del text[:]

    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    # Remove comments and un-escape any escaped / characters in the text (\/ becomes /)
    #
    # Note: I trued implementing a warning for continued // and continued .ig but the
    #       warning for // can trigger on the -----File: ... p1\p2\p3\f1\f2\ lines if
    #       the PPer leaves them in as comments. So I did not keep those implementations.
    def uncomment(buffer):
      i = 0
      while i < len(buffer):
        if  re.match(r"//", buffer[i]): # entire line is a comment
          #if buffer[i].endswith("\\"):
          #  self.warn("Continuation \ ignored following //: {}".format(buffer[i]))
          del buffer[i]
          continue

        m = re.match(r"(.*?)//(.*)$", buffer[i])
        if m:
          if m.group(1).endswith("http:") or m.group(1).endswith("https:"):
            self.warn("Use /\/ rather than // if you want this to be a URL instead of the start of a comment: {}".format(buffer[i]))

          buffer[i] = m.group(1)


        #
        # convert escaped / characters
        #
        buffer[i] = re.sub(r"\\/", "/", buffer[i])
        buffer[i] = buffer[i].rstrip()
        i += 1

    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    # ignored text removed in preprocessor
    def handle_ig():
      i = 0
      while i < len(self.wb):
        # detect misplaced .ig-
        if ".ig-" == self.wb[i]:
          self.crash_w_context("Extraneous .ig-; no matching .ig", i)
        # one line
        elif re.match(r"\.ig ",self.wb[i]): # single line
          #if self.wb[i].endswith("\\"):
          #  self.warn("Continuation \ ignored on single-line .ig directive: {}".format(self.wb[i]))
          del self.wb[i]
        elif ".ig" == self.wb[i]: # multi-line
          del self.wb[i]
          while i < len(self.wb) and self.wb[i] != ".ig-":
            if self.wb[i].startswith(".ig"): # hit a .ig while looking for a .ig-?
              self.crash_w_context("Missing .ig- directive: found another .ig inside a .ig block", i)
            del self.wb[i]
          if i < len(self.wb):
            del self.wb[i] # the ".ig-"
          else:
            self.fatal("unterminated .ig command")
        else:
          i += 1

    # .if conditionals (moved to preProcessCommon 28-Aug-2014)
    def handle_if():
      text = []
      keep = True
      inIf = False
      for i, line in enumerate(self.wb):

        m = re.match(r"\.if (\w)", line)  # start of conditional
        if m:
          if inIf:
            self.crash_w_context("Nested .if not supported", i)
          inIf = True
          ifloc = i
          keep = False
          keepType = m.group(1)
          if m.group(1) == 't' and self.renc in "lut":
            keep = True
          elif m.group(1) == 'h' and self.renc == "h":
            keep = True
          continue

        if line == ".if-":
          if not inIf:
            self.crash_w_context(".if- has no matching .if", i)
          keep = True
          keepType = None
          inIf = False
          continue

        if keep:
          text.append(line)
        elif line.startswith(".sr"):
          m2 = re.match(r"\.sr +([^ ]+)", line)
          if m2:
            if keepType == 't' and "h" in m2.group(1):
              self.warn(".sr command for HTML skipped by .if t: {}".format(line))
            elif keepType == 'h':
              m3 = re.search(r"[ult]", m2.group(1))
              if m3:
                self.warn(".sr command for text skipped by .if h: {}".format(line))

      if inIf: # unclosed .if?
        self.crash_w_context("Unclosed .if directive", ifloc)
      self.wb = text
      text = []


    def doGreek():

      def findGreek(text, start):
        found = False
        i = end = newstart = len(text)
        m = re.search(r"(^|[^\\])(\[Greek: ?)", text[start:end], flags=re.DOTALL)
        if m:
          found = True
          newstart = start + m.start(2)
          i = start + m.end(2) # bump past [Greek:
          #end = len(text)
          nest = 0
          done = False
          while i < end and not done:
            if text[i] == "\n" and text[i+1] == ".":
              if (i + 2) < end and re.match("[a-z]", text[i+2]):
                self.fatal("Greek text contains dot directive; closing ] missing? {}".format(text[newstart:i+4]))
            # Balance internal [ and ] if present. Allow " \[" to escape an unbalanced [ if needed.
            # Note: the space before the \ is required. Also, we do not allow escaping of an unbalanced
            #       ] at this time. If we did, it would also require a space: " \]"
            #       The problem is that, for example, "o\]" is an o with a \, followed by a ]. It is not an
            #       o followed by a \].
            if text[i] == "[" and text[i-2:i] != " \\":
              nest += 1
            elif text[i] == "]" and nest == 0:
              done = True
              break
            elif text[i] == "]":
              nest -= 1

            i += 1
          if not done: # error; print up to 100 characters of the unterminated Greek tag
            self.fatal("Unterminated [Greek tag?\n{}".format(text[start+newstart:start+newstart+100]))

        i += 1
        more = True if (i < len(text)) else False

        return found, newstart, i, more



      # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
      # process [Greek: ...] in UTF-8 output if requested to via .gk command
      i = 0
      self.gk_requested = False
      gk_done = False
      self.gkpre = ""
      self.gksuf = ""
      self.gkkeep = "n"
      self.gk_quit = "n"
      while i < len(self.wb) and not gk_done:
        if self.wb[i].startswith(".gk"):
          gkin = ""
          gkout = ""
          if "pre=" in self.wb[i]:
            self.wb[i], self.gkpre = self.get_id("pre", self.wb[i])
            self.gkpre = re.sub(r"\\n", "\n", self.gkpre)
          if "suf=" in self.wb[i]:
            self.wb[i], self.gksuf = self.get_id("suf", self.wb[i])
            self.gksuf = re.sub(r"\\n", "\n", self.gksuf)
          if "keep=" in self.wb[i]:
            self.wb[i], self.gkkeep = self.get_id("keep", self.wb[i])
          if "in=" in self.wb[i]:
            self.wb[i], gkin = self.get_id("in", self.wb[i])
          if "out=" in self.wb[i]:
            self.wb[i], gkout = self.get_id("out", self.wb[i])
          if "quit=" in self.wb[i]:
            self.wb[i], self.gk_quit = self.get_id("quit", self.wb[i])
          if "done" in self.wb[i]:
            gk_done = True
          del self.wb[i]
          self.gk_requested = True

          if gkin and gkout:
            m = re.search(r"\\u[0-9a-fA-F]{4}", gkout) # find any characters defined by unicode constants in output string
            while m:
              found = m.group(0)
              rep = bytes(m.group(0),"utf-8").decode('unicode-escape')
              gkout = re.sub(re.escape(found), rep, gkout)
              m = re.search(r"\\u[0-9a-fA-F]{4}", gkout)
            self.gk_user.append((gkin, gkout))
          continue
        i += 1
      #if self.gk_requested and (self.renc == "u" or self.renc == "h" or self.cvgfilter):
      if self.renc == "u" or self.renc == "h" or self.cvgfilter:
        text = '\n'.join(self.wb) # form all lines into a blob of lines separated by newline characters
        if self.gk_requested:
          more = True
          start = 0
          while more:
            found, start, end, more = findGreek(text, start)
            if found:
              front = text[:start]
              back = text[end:]
              middle = re.sub(r"\[Greek: ?(.*)]", gkrepl, text[start:end], flags=re.DOTALL)
              text = front + middle + back
              start = len(front) + len(middle)

          #text = re.sub(r"\[Greek: ?(.*?)]", gkrepl, text, flags=re.DOTALL)
        # even if Greek processing not requested, [Greek: ...] strings could have \| and \(space)
        # characters we need to protect
        #count = 1
        #while count:
        #  text, count = re.subn(r"(\[Greek:[^]]*?)\\\|([^]]*?\])", r"\1⑩\2", text, flags=re.DOTALL)
        #count = 1
        #while count:
        #  text, count = re.subn(r"(\[Greek:[^]]*?)\\ ([^]]*?\])", r"\1⑮\2", text, flags=re.DOTALL)

        self.wb = text.splitlines()
        text = ""

    def doDiacritics():
      # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
      # process diacritic markup in UTF-8 output if requested to via .cv command
      i = 0
      self.dia_requested = False
      dia_done = False
      dia_blobbed = False
      diapre = ""
      diasuf = ""
      diakeep = "n"
      diatest = False
      self.dia_quit = "n"
      dia_italic = "n"
      dia_bold = "n"
      while i < len(self.wb) and not dia_done:
        if self.wb[i].startswith(".cv"):
          self.dia_requested = True
          orig = self.wb[i]
          diain = ""
          diaout = ""
          if "pre=" in self.wb[i]:
            self.wb[i], diapre = self.get_id("pre", self.wb[i])
            diapre = re.sub(r"\\n", "\n", diapre)
            if diapre:
              diatest = True
          if "suf=" in self.wb[i]:
            self.wb[i], diasuf = self.get_id("suf", self.wb[i])
            diasuf = re.sub(r"\\n", "\n", diasuf)
            if diasuf:
              diatest = True
          if "keep=" in self.wb[i]:
            self.wb[i], diakeep = self.get_id("keep", self.wb[i])
            if not diakeep.lower().startswith("n"):
              diatest = True
          if "in=" in self.wb[i]:
            self.wb[i], diain = self.get_id("in", self.wb[i])
          if "out=" in self.wb[i]:
            self.wb[i], diaout = self.get_id("out", self.wb[i])
          if "quit=" in self.wb[i]:
            self.wb[i], self.dia_quit = self.get_id("quit", self.wb[i])
          if "italic=" in self.wb[i]:
            self.wb[i], dia_italic = self.get_id("italic", self.wb[i])
          if "bold=" in self.wb[i]:
            self.wb[i], dia_bold = self.get_id("bold", self.wb[i])
          if "done" in self.wb[i]:
            dia_done = True
          del self.wb[i]
          if (diain and not diaout) or (diaout and not diain):
            self.warn("Missing in= or out= value: {}".format(orig))
          if diain:
            if diain[0] != "[" or diain[-1] != "]" or len(diain) > 10 or len(diain) < 3:
              self.warn("Ignoring invalid in= value {}: {}".format(diain, orig))
              diain = ""
            inner = diain[1:-1]
            if inner.isdigit():
              self.warn("in= value {} may conflict with footnote processing: {}".format(diain, orig))
          if diain and diaout:
            m = re.search(r"\\u[0-9a-fA-F]{4}", diaout) # find any characters defined by unicode constants in output string
            while m:
              found = m.group(0)
              rep = bytes(m.group(0),"utf-8").decode('unicode-escape')
              diaout = re.sub(re.escape(found), rep, diaout)
              m = re.search(r"\\u[0-9a-fA-F]{4}", diaout)
            if diaout != "ignore":
              self.diacritics_user.append((diain, diaout))
            else:
              ignored = False
              for s in self.diacritics:
                if s[0] == diain:
                  self.diacritics.remove(s)
                  ignored = True
                  break
              if not ignored:
                self.warn("No builtin diacritic {} to ignore: {}".format(diain, orig))
          continue
        i += 1
      if self.dia_requested and (dia_italic.lower().startswith("y") or dia_bold.lower().startswith("y")):
        text = '\n'.join(self.wb) # form all lines into a blob of lines separated by newline characters
        dia_blobbed = True
        #
        # Correct diacritics with <i> markup in them if requested
        #
        if dia_italic.lower().startswith("y"):
          self.print_msg("Checking for <i> within diacritic markup and correcting")
          for s in self.diacritics_user:
            si = "[<i>" + s[0][1:-1] + "</i>]"
            so = "<i>" + s[0] + "</i>"
            try:
              text, count = re.subn(re.escape(si), so, text)
              if count:
                self.print_msg("Replaced {} with {} {} times".format(si, so, count))
            except:
              self.warn("Error occurred trying to replace {} with {}.".format(si, so))
          for s in self.diacritics:
            si = "[<i>" + s[0][1:-1] + "</i>]"
            so = "<i>" + s[0] + "</i>"
            try:
              text, count = re.subn(re.escape(si), so, text)
              if count:
                self.print_msg("Replaced {} with {} {} times".format(si, so, count))
            except:
              self.warn("Error occurred trying to replace {} with {}.".format(si, so))
        if dia_bold.lower().startswith("y"):
          self.print_msg("Checking for <b> within diacritic markup and correcting")
          for s in self.diacritics_user:
            si = "[<b>" + s[0][1:-1] + "</b>]"
            so = "<b>" + s[0] + "</b>"
            try:
              text, count = re.subn(re.escape(si), so, text)
              if count:
                self.print_msg("Replaced {} with {} {} times".format(si, so, count))
            except:
              self.warn("Error occurred trying to replace {} with {}.".format(si, so))
          for s in self.diacritics:
            si = "[<b>" + s[0][1:-1] + "</b>]"
            so = "<b>" + s[0] + "</b>"
            try:
              text, count = re.subn(re.escape(si), so, text)
              if count:
                self.print_msg("Replaced {} with {} {} times".format(si, so, count))
            except:
              self.warn("Error occurred trying to replace {} with {}.".format(si, so))
      if self.dia_requested and (self.renc == "u" or self.renc == "h" or self.cvgfilter):
        if not dia_blobbed:
          text = '\n'.join(self.wb) # form all lines into a blob of lines separated by newline characters
          dia_blobbed = True
        if not diatest:
          if len(self.diacritics_user) > 0:
            for s in self.diacritics_user:
              try:
                text, count = re.subn(re.escape(s[0]), s[1], text)
                self.print_msg("Replaced PPer-provided diacritic {} {} times.".format(s[0], count))
              except:
                self.warn("Error occurred trying to replace PPer-provided diacritic " +
                          "{} with {}. Check replacement value".format(s[0], s[1]))
          for s in self.diacritics:
            text, count = re.subn(re.escape(s[0]), s[1], text)
            if count > 0:
              self.print_msg("Replaced {} {} times.".format(s[0], count))
              if s[3]:
                self.warn("{} is a non-standard markup for {}. Please examine images to confirm character is correct".format(s[0], s[1]))
        else:
          if len(self.diacritics_user) > 0:
            for s in self.diacritics_user:
              if diakeep.lower().startswith("b"): # original before?
                diaorigb = s[0]
                diaoriga = ""
              elif diakeep.lower().startswith("a"): # original after?
                diaoriga = s[0]
                diaorigb = ""
              repl = diaorigb + diapre + s[1] + diasuf + diaoriga
              try:
                text, count = re.subn(re.escape(s[0]), repl, text)
                self.print_msg("Replaced PPer-provided diacritic {} {} times.".format(s[0], count))
              except:
                self.warn("Error occurred trying to replace PPer-provided Greek character" +
                          "{} with {}. Check replacement value".format(s[0], s[1]))
          for s in self.diacritics:
            if diakeep.lower().startswith("b"): # original before?
              diaorigb = s[0]
              diaoriga = ""
            elif diakeep.lower().startswith("a"): # original after?
              diaoriga = s[0]
              diaorigb = ""
            repl = diaorigb + diapre + s[1] + diasuf + diaoriga
            text, count = re.subn(re.escape(s[0]), repl, text)
            if count > 0:
              self.print_msg("Replaced {} {} times.".format(s[0], count))
              if s[3]:
                self.warn("{} is a non-standard markup for {}. Please examine images to confirm character is correct".format(s[0], s[1]))
        if self.log:
          header_needed = True
          text2 = text
          m = re.search(r"\[([^*\]].{1,7}?)]", text2)
          while m:
            matched = m.group(0)
            inner = m.group(1)
            text2, count = re.subn(re.escape(m.group(0)), "", text2)
            if count > 0 and not inner.isdigit():
              if header_needed:
                self.print_msg("Potential diacritics not converted:")
                header_needed = False
              try:
                self.print_msg(" {} occurred {} times.".format(m.group(0), count))
              except:
                self.print_msg("**{} occurred {} times. (Safe-printed due to error.)".format(m.group(0), count))
            m = re.search(r"\[([^*\]].{1,7}?)]", text2)
          if header_needed:
            self.print_msg("No unconverted diacritics seem to remain after conversion.")
          del text2

      if dia_blobbed:
        self.wb = text.splitlines()
        del text

    # handle parsing for any .sr directive
    # Input: line is a .sr directive
    # Output: boolean, which, search, replace
    #
    def parse_sr(line):
      sr_ok = True # assume it works
      which = ""
      search = ""
      replace = ""
      m = re.match(r"\.sr +([ulthfbBp]+) +(.*)", self.wb[i]) # validate first argument of .sr
      if m:
        which = m.group(1)
        m = re.match(r"(.)(.*?)\1(.*?)\1(.*)", m.group(2))  # 1=separator 2=search 3=replacement 4=unexpected trash
        if m:
          if m.group(4) == "":  # ok?
            search = m.group(2)
            replace = m.group(3)
          else:
            self.warn("Problem with .sr arguments: " +
                      "1={} 2={} 3={} 4={} Unexpected 5={}\n             {}".format(
                      which, m.group(1), m.group(2), m.group(3), m.group(4), line))
            sr_ok = False
        else:
          self.warn("Problem with .sr search/replace argument: {}".format(line))
          sr_ok = False
      else:
        self.warn("Problem with .sr first operand; must be one or more characters in set ulthfbBp: {}".format(line))
        sr_ok = False

      return sr_ok, which, search, replace



    def doFilterSR():
      # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
      # capture and remove search/replace directives that specify f for filtering
      # .sr f[p]? /search/replace/
      # which is a string containing some combination of ulthf (UTF-8, Latin-1, Text, HTML, filtering)
      #   or b (before processing, rather than in postprocessing) or p (prompt whether to replace or not)
      # search is  reg-ex search string
      # replace is a reg-ex replace string
      # / is any character not contained within either search or replace
      #
      # Values gathered during preprocessCommon and used during filtering
      i = 0
      filter_sr = False
      sr_error = False
      while i < len(self.wb):
        if self.wb[i].startswith(".sr"):
          sr_ok, which, search, replace = parse_sr(self.wb[i])
          #self.wb[i] = self.restore_some_escapes(self.wb[i])
          if sr_ok:
            if "f" in which:  # if request to do s/r during filtering
              filter_sr = True     # remember the request
              if ("u" in which or "l" in which or "B" in which or
                  "t" in which or "h" in which or "b" in which):
                self.warn(".sr f option can not be used with u, l, t, h, B, or b options:" +
                          "\n             {}".format(self.wb[i]))
                sr_error = True
              if not self.cvgfilter:
                self.warn(".sr f option can only be used with -f command line option:" +
                          "\n             {}".format(self.wb[i]))
                sr_error = True
              if (("\\n" in m.group(2)) and
                  ("p" in which)): # Can't do prompting with \n in request
                  self.warn(".sr p option can not be used with \\n in search string:" +
                            "\n             {}".format(self.wb[i]))
                  sr_error = True
              if replace.startswith("{{python "): # attempt to use python macros during .sr for filtering?
                self.warn(".sr with f option cannot use Python macros in replacement string:" +
                          "\n             {}".format(self.wb[i]))
                sr_error = True
          else:
            sr_error = True

          if not sr_error:
            self.srw.append(which)
            self.srs.append(search)
            self.srr.append(replace)

          del self.wb[i]       # delete this record
          continue

        i += 1

      if sr_error: # if any .sr parsing problems noted
        self.fatal("Terminating due to the .sr issues listed previously.")

      if self.cvgfilter and filter_sr: # if user wants some .sr directives applied in filtering mode do them now
        for i in range(len(self.srw)):
          if ('f' in self.srw[i]):     # if this one applies to filtering mode
            self.process_SR(self.wb, i)
        self.srw = []
        self.srs = []
        self.srr = []

    # Guts of .pm macro processing(so we can also use for <pm processing)
    #
    def pm_guts(line, line_num):
      i = line_num
      #self.dprint("line: {}".format(line))
      try:
        tlex = shlex.split(line)  # ".pm" "tnote" "a" "<li>"
      except:
        if 'd' in self.debug:
          traceback.print_exc()
          self.crash_w_context("Above error occurred while processing macro invocation: {}".format(line), i)
        else:
          self.crash_w_context("Error occurred parsing macro arguments for: {}".format(line), i)

      # ensure macro name present
      if len(tlex) == 1:
        self.crash_w_context("Macro name missing", i)

      # debug if requested
      if 'm' in self.debug:
        if tlex[0].startswith("."):
          self.print_msg("Processing .pm for {} with parameters:\n".format(tlex[1]))
        else:
          self.print_msg("Processing <pm for {} with parameters:\n".format(tlex[1]))
        for i in range(1, len(tlex)):
          self.print_msg("  {}: {}".format(i, tlex[i]))

      macroid = tlex[1]  # "tnote"
      if not macroid in self.macro:
        self.crash_w_context("undefined macro {}: ".format(macroid), i)

      if self.macro[macroid][0] == "n": # "native" ppgen macro?
        t = list(self.macro[macroid][1]) # all the lines in this macro as previously defined
        for j,line in enumerate(t): # for each line
          m = re.search(r'\$(\d{1,2})', t[j]) # is there a substitution?
          while m:
            pnum = int(m.group(1))
            subst = r"\${}".format(pnum)
            if pnum < len(tlex) - 1:
              if 'm' in self.debug:
                self.print_msg("Macro line {} before: {}".format(j, t[j]))
              try:
                t[j] = re.sub(subst, tlex[pnum+1], t[j], 1)
                if 'm' in self.debug:
                  self.print_msg("Macro line {} after: {}".format(j, t[j]))
              except:
                if 'd' in self.debug:
                  traceback.print_exc()
                  self.crash_w_context("Above error occurred while substituting parameter number {} in {}".format(pnum, line), i)
                else:
                  self.crash_w_context("Error occurred while substituting parameter number {} in {}".format(pnum, line), i)
            else:
              self.warn_w_context("Incorrect macro invocation (argument ${} missing): {}".format(pnum, line), i)
              t[j] = re.sub(subst, "***missing***", t[j], 1)
            m = re.search(r'\$(\d{1,2})', t[j]) # another substitution on same line

      else: # python format macro
        if not self.pmcount: # if first python macro this pass, initialize a dictionary
          self.savevar = {}  # to allow macros to communicate
        self.pmcount += 1
        var = {}
        var["count"] = len(tlex) - 2 # count of input variables
        for j in range(2, len(tlex)):
          var[j-2] = tlex[j]
        var["name"] = macroid # the name of the macro, in case the macro cares for some reason
        var["out"] = [] # place for macro to put its output
        var["type"] = self.booktype # text or html
        var["style"] = ".pm" if tlex[0].startswith(".") else "<pm>"
        # below 3 lines don't make sense for .pm as the phase is too early
        #var["ll"] = self.regLL  # specified line length
        #var["in"] = self.regIN  # specified
        #var["nr-nfl"] = self.nregs["nfl"] # .nr nfl value
        macglobals = __builtins__.__dict__
        macglobals["var"] = var # make macro variables available
        macglobals["re"] = re # make re module available
        macglobals["toRoman"] = self.toRoman2
        macglobals["fromRoman"] = self.fromRoman
        macglobals["debugging"] = [self.bailout, self.wb, i]
        macglobals["savevar"] = self.savevar # make communication dictionary available
        maclocals = {"__builtins__":None}

        try: # exec the macro
          exec(self.macro[macroid][1], macglobals, maclocals)
        except:
          where = traceback.extract_tb(sys.exc_info()[2])[-1]
          if where[0] == "<macro {}>".format(macroid):
            macro_line = "{}:".format(where[1]-1) + self.macro[macroid][3][where[1]-1]
          else:
            macro_line = "not available"
          mac_info = "Exception occurred running Python macro {} at\n       Source line {}\n".format(macroid, macro_line)
          trace_info = traceback.format_exception(*sys.exc_info())
          self.crash_w_context(mac_info + "\n".join(trace_info), i)

        try: # try to grab its output
          t = var["out"][:]
        except:
          traceback.print_exc()
          self.crash_w_context("Above error occurred trying to copy output from Python macro {}".format(macroid), i)

      return t


    #
    # Begin Pre-process Common
    #

    # load cvg filter file if specified
    if self.cvgfilter:
      loadFilter()

    # This ends up causing problems for Greek with \], and now that Greek processing properly finds the end
    # of the [Greek: ...] tag we don't need to have this done early any more.
    ## Handle some escaped characters
    #for i, line in enumerate(self.wb):
    #  # some escaped characters
    #  # Note: must handle \| and \(space) and \] later as they are significant to [Greek: ...] processing
    #  self.wb[i] = self.wb[i].replace(r"\{", "①")
    #  self.wb[i] = self.wb[i].replace(r"\}", "②")
    #  self.wb[i] = self.wb[i].replace(r"\[", "③")
    #  self.wb[i] = self.wb[i].replace(r"\]", "④")
    #  self.wb[i] = self.wb[i].replace(r"\<", "⑤")
    #  self.wb[i] = self.wb[i].replace(r"\>", "⑳")
    #  self.wb[i] = self.wb[i].replace(r"\:", "⑥")
    #  self.wb[i] = self.wb[i].replace(r"\-", "⑨")
    #  self.wb[i] = self.wb[i].replace(r"\#", "⓪")


    # Remove commented/ignored stuff if not in filter mode
    #   so they don't impact Greek/Diacritic processing
    # (Also un-escapes any escaped / characters (\/ becomes /)
    if not self.cvgfilter:
      uncomment(self.wb)
      handle_ig()
      handle_if()


    # Handle Greek, Diacritics, .sr for filtering, and terminate with cvg-bailout text if filtering or user requested it
    doGreek()
    doDiacritics()
    if self.cvgfilter:
      doFilterSR()
    if self.gk_quit.lower().startswith("y") or self.dia_quit.lower().startswith("y") or self.cvgfilter:
      self.cvgbailout()  # bail out after .cv/.gk or filter processing if user requested early termination


    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    # capture and remove search/replace directives
    # .sr <which> /search/replace/
    # which is a string containing some combination of ulthf (UTF-8, Latin-1, Text, HTML, filtering)
    #   or b (late in pre-processing (before processing), rather than in postprocessing)
    #   or B (early in pre-processing) or p (prompt whether to replace or not)
    # search is  reg-ex search string
    # replace is a reg-ex replace string or the string {{python <macro-name>}}
    # / is any character not contained within either search or replace
    #
    # Values gathered during preprocessCommon and saved for use during post-processing
    i = 0
    sr_error = False
    self.sr_b = False # if True, some .sr specified the b option
    self.sr_B = False # if True, some .sr specified the B option

    while i < len(self.wb):
      if self.wb[i].startswith(".sr"):
        sr_ok, which, search, replace = parse_sr(self.wb[i])
        if sr_ok:
          if (("\\n" in search) and
              ("p" in which)): # Can't do prompting with \n in request
            self.warn(".sr p option can not be used with \\n in search string:" +
                      "\n             {}".format(self.wb[i]))
            sr_error = True
          if "b" in which:  # remember b option if specified on any .sr
            self.sr_b = True
          if "B" in which:  # remember B option if specified on any .sr
            self.sr_B = True

          if not sr_error:
            self.srw.append(which)
            self.srs.append(search)
            self.srr.append(replace)

        del self.wb[i]       # delete this record
        continue

      i += 1

    if sr_error: # if any .sr parsing problems noted
      self.fatal("Terminating due to the .sr issues listed previously.")


    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    # define macro (processed before continuation characters are handled, so must handle explicitly)
    # .dm name
    # .dm name $1 $2 (optionally: lang=python)
    # macro line 1
    # macro line 2
    # .dm-
    # Notes:
    #    (1) .if processing has already occurred, and has "pruned" macro content to the appropriate statements
    #        for the phase (text, HTML) that we're in.
    #    (2) This implies that a macro definition must include a complete .if block; you cannot start a .if in one
    #        macro and have the .if- in a subsequent macro.
    i = 0
    while i < len(self.wb):
      if self.wb[i].startswith(".dm "):

        while (i < len(self.wb) - 1) and self.wb[i].endswith("\\"):   # allow continuation via ending \ for .dm
          self.wb[i] = re.sub(r"\\$", "", self.wb[i]) + self.wb[i+1]
          del self.wb[i+1]
        if self.wb[i].endswith("\\"):
          self.fatal("file ends with continued .dm")

        self.wb[i], count = re.subn(" lang=python", "", self.wb[i]) # determine if regular or Python macro
        python = True if count else False
        tlex = shlex.split(self.wb[i])
        if len(tlex) > 1:
          macroid = tlex[1] # string
        else:
          self.crash_w_context("incorrect .dm command: macro name missing.", i)
        del self.wb[i]
        t = []
        while i < len(self.wb) and not self.wb[i].startswith(".dm"):  # accumulate statements into the macro until we hit another .dm or a .dm-
          # Note: statements within a macro definition cannot be continued using \ as the final character, as macros
          #       must be able to generate statements ending with \
          t.append(self.wb[i])
          del self.wb[i]
        if i < len(self.wb) and self.wb[i] == ".dm-":       # if we hit a .dm- then delete it and finalize the macro
          del self.wb[i] # the closing .dm-
        else:                                               # quit if we hit end-of-file or a .dm before finding the .dm-
          self.fatal("missing .dm- for macro: " + macroid)
        if not python: # native macro
          # macro is stored in t[]
          self.macro[macroid] = ["n", t, len(tlex)-2] # store as a "native" macro
        else: # python macro
          if not Book.python_macros_allowed: # has user authorized use of Python macros?
            self.print_msg("Warning: Macro(s) contain Python code.")
            good_warn_reply = False
            while not good_warn_reply:
              try:
                answer = input("Allow? (y/n)")
              except EOFError:
                self.print_msg("EOF received on prompt; assuming n")
                answer = "n"
              if answer == "y":
                good_warn_reply = True
                Book.python_macros_allowed = True
              elif answer == "n":
                self.print_msg("Python macros not allowed; quitting")
                exit(1)
          try: # compile the macro
            s = "\n".join(t)
            c = compile(s, "<macro {}>".format(macroid), "exec")
            self.macro[macroid] = ["p", c, len(tlex)-2, t] # store as a compiled python macro
          except:
            traceback.print_exc()
            self.fatal("Above error occurred trying to compile Python code for macro {}".format(macroid))
        i -= 1
      i += 1


    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    # play macro (dot directive, .pm)
    # processed before continuation characters are handled, so must handle explicitly
    # format:
    #  .pm name parameters
    i = 0
    self.pmcount = 0 # number of python macros executed in this phase
    while i < len(self.wb):
      if self.wb[i].startswith(".pm"):
        while (i < len(self.wb) - 1) and self.wb[i].endswith("\\"):   # allow continuation via ending \ for .pm
          self.wb[i] = re.sub(r"\\$", "", self.wb[i]) + " " + self.wb[i+1]
          del self.wb[i+1]
        if self.wb[i].endswith("\\"):
          self.fatal("file ends with continued .pm")

        t = pm_guts(self.wb[i], i) # go play the macro
        self.wb[i:i+1] = t

        i -= 1 # so we can rescan the first line generated by the macro

      i += 1



    # Handle any .sr that have the B option specified
    #
    if self.sr_B:
      for i in range(len(self.srw)):
        if self.booktype == "text":
          if ((('t' in self.srw[i]) or (self.renc in self.srw[i])) and
              ('B' in self.srw[i])): # if this one is for pre-pre-processing and applies to the text form we're generating
            self.process_SR(self.wb, i)
        else : # HTML
          if ('h' in self.srw[i]) and ('B' in self.srw[i]): # if this one is for pre-pre-processing and applies to HTML
            self.process_SR(self.wb, i)

    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    # process character mappings
    # character mappings are from the UTF-8 representation to Latin-1
    i = 0
    self.mau.append("—")   # maps a dash in UTF-8 to "--" in Latin-1
    self.mal.append("--")
    while i < len(self.wb):
      if self.wb[i].startswith(".ma"):

        m = re.match(r"\.ma ([\"'])(.*?)\1 ([\"'])(.*?)\3", self.wb[i])  # both in quotes
        if m:
          self.mau.append(m.group(2))
          self.mal.append(m.group(4))
          del self.wb[i]
          continue

        m = re.match(r"\.ma ([\"'])(.*?)\1 (.*?)$", self.wb[i])  # only first in quotes
        if m:
          self.mau.append(m.group(2))
          self.mal.append(m.group(3))
          del self.wb[i]
          continue

        m = re.match(r"\.ma (.*?) ([\"'])(.*?)\2", self.wb[i])  # only second in quotes
        if m:
          self.mau.append(m.group(1))
          self.mal.append(m.group(3))
          del self.wb[i]
          continue

        m = re.match(r"\.ma (.*?) (.*?)$", self.wb[i])  # neither in quotes
        if m:
          self.mau.append(m.group(1))
          self.mal.append(m.group(2))
          del self.wb[i]
          continue

      i += 1

    # Now that we've gathered mappings, apply them to down-convert
    # if source file is UTF-8 and requested encoding is Latin-1
    if self.encoding == "utf_8" and self.renc == "l":
      for j,ch in enumerate(self.mau):
        for i in range(len(self.wb)): # O=n^2
          self.wb[i] = re.sub(ch, self.mal[j], self.wb[i])
      # user-defined character mapping complete, now do default mapping to Latin-1
      self.utoLat()

    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    # .bn (GG-compatible .bin file maintenance)
    # must happen before continuation lines are processed
    i = 0
    self.bnPresent = False
    image_type = ""
    while i < len(self.wb):
      if self.wb[i].startswith(".bn"):
        m = re.search("(\w+?)\.(png|jpg|jpeg)",self.wb[i])
        if m:
          self.bnPresent = True
          self.wb[i] = "⑱{}⑱".format(m.group(1))
          temp = ("png" if m.group(2) == "png" else "jpg")
          if image_type:
            if image_type != temp:
              self.warn("Project contains both png and jpg proofing images.\n" +
                        "     Please check to ensure no high-res illustrations are missing;\n" +
                        "     if any are missing please contact the PM or db-req for assistance.")
          else:
            image_type = temp
        else:
          self.crash_w_context("malformed .bn directive", i)
      i += 1

    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    # set pnshow, pnlink variables (must happen before page number conversion)
    # if any .pn numeric is seen, pnshow <- True
    # override with .pn off
    override = False
    self.pnshow = False # generate links and show
    self.pnlink = False # generate links but do not display
    i = 0
    while i < len(self.wb):
      if self.wb[i].startswith(".pn link"):
        self.pnlink = True
        del self.wb[i]
        continue

      elif self.wb[i].startswith(".pn off"):
        override = True
        del self.wb[i]
        continue

      elif self.wb[i].startswith(".pn "): # any explicit page number
        self.pnshow = True

      i += 1

    if override:
      self.pnshow = False # disable visible page numbers

    # convert page page numbers to ⑯number⑰
    #
    # Notes:
    #   1. Must happen before continuation is handled, so continuation processing does not see
    #        a .pn directive when continuing a dot command or normal text.
    #   2. All pn handling must happen in one pass through the source file, to ensure that the
    #        numbers remain in a single, continuous range when incrementing.
    #   3. To properly handle situations with continued .hn or .il directives, any continuation
    #      for them must be handled in this code, due to the requirement for a single pass
    #      through the source.
    i = 0
    while i < len(self.wb):

      # page number increment on .pn
      # convert increment to absolute page number
      m = re.match(r"\.pn +\+(\d+)", self.wb[i])
      if m:
        increment_amount = int(m.group(1))
        if increment_amount == 0: # can't have duplicate page numbers
          self.crash_w_context("Invalid .pn increment amount, +0", i)
        if (self.pageno).isnumeric():
          self.pageno = "{}".format(int(self.pageno) + increment_amount)
        else: # Roman, possibly (or maybe null, the default initial value)
          m = re.match(r"^([iIvVxXlLcCdDmM]+|)$", self.pageno)
          if not m:
            self.crash_w_context("Cannot increment non-numeric, non-Roman page number {}".format(self.pageno), i)
          else:
            ucRoman = False
            if not (self.pageno).islower():
              ucRoman = True # page number has at least 1 upper-case Roman numeral (or is null)
              self.pageno = (self.pageno).lower()
            n = self.fromRoman(self.pageno)
            n += increment_amount
            self.pageno = self.toRoman(n)
            if ucRoman:
              self.pageno = (self.pageno).upper()
        if self.pnshow or self.pnlink:
          self.wb[i] = "⑯{}⑰".format(self.pageno)
        else:
          del self.wb[i]
        continue

      # explicit page number on .pn
      m = re.match(r"\.pn +[\"']?(.+?)($|[\"'])", self.wb[i])
      if m:
        self.pageno = m.group(1)

        if self.pnshow or self.pnlink:
          self.wb[i] = "⑯{}⑰".format(self.pageno)
        else:
          del self.wb[i]
        continue

      # Now handle pn= operands on .hn and .il
      #
      # First, for .hn and .il we need to handle any continuation...
      if i < (len(self.wb) - 1) and self.wb[i].endswith("\\"):
        m = re.match(r"\.((h[1-6])|il)", self.wb[i])
        if m: # found continued .hn or .il
          while i < len(self.wb) - 1 and self.wb[i].endswith("\\"):
            if self.wb[i+1].startswith(".pn") or self.wb[i+1].startswith(".bn"):
              self.crash_w_context(".pn or .bn not allowed within a continued dot directive", i)
            elif self.wb[i+1].startswith(".") and re.match("\.[a-z]", self.wb[i+1]):
              self.warn_w_context("Possible continuation problem: next line looks like a dot directive.", i)
            self.wb[i] = re.sub(r"\\$", "", self.wb[i]) + " " + self.wb[i+1]
            del self.wb[i+1]
      #
      # We now have a non-hn/il statement, or a complete .hn/.il
      #
      m = re.match(r"\.((h[1-6])|il).*?pn=\+(\d+)($|\s)", self.wb[i])
      if m:
        increment_amount = int(m.group(3))
        if increment_amount == 0: # can't have duplicate page numbers
          self.crash_w_context("Invalid pn= increment amount, +0", i)
        if (self.pageno).isnumeric():
          self.pageno = "{}".format(int(self.pageno) + increment_amount)
        else: # Roman, possibly
          m = re.match(r"^([iIvVxXlLcCdDmM]+|)$", self.pageno)
          if not m:
            self.crash_w_context("Cannot increment non-numeric, non-Roman page number {}".format(self.pageno), i)
          else:
            ucRoman = False
            if not (self.pageno).islower():
              ucRoman = True # page number has at least 1 upper-case Roman numeral
              self.pageno = (self.pageno).lower()
            n = self.fromRoman(self.pageno)
            n += increment_amount
            self.pageno = self.toRoman(n)
            if ucRoman:
              self.pageno = (self.pageno).upper()
        if self.pnshow or self.pnlink:
          self.wb[i] = re.sub(r"pn=\+\d+", "pn={}".format(self.pageno), self.wb[i])
        else:
          self.wb[i] = re.sub(r"pn=\+\d+", "", self.wb[i])
        i += 1
        continue

      # now check for and warn about non-numeric page number values set in a heading or .il directive
      m = re.match(r"\.((h[1-6])|il).*?pn=[\"']?(.+?)[\"']?($|\s)", self.wb[i])
      if m:
        self.pageno = m.group(3)
        m = re.match(r"\d+|[iIvVxXlLcCdDmM]+$", self.pageno)
        if not m:
          self.warn_w_context("Non-numeric, non-Roman page number {} specified: {}".format(self.pageno, self.wb[i]), i)
        if not self.pnshow and not self.pnlink:
          self.wb[i] = re.sub(r"pn=[\"']?(.+?)[\"']?($|/s)", "", self.wb[i])
        i += 1
        continue

      i += 1


    # Handle continuation:
    #   Long lines of any kind may end with a single backslash. The backslash will be replaced by a blank, and
    #   the next line will be concatenated to it.
    # Notes:
    #     1. .de is exempted here as it needs separate processing.
    #     2. If a line ends with multiple \ characters they are all deleted and replaced by a single blank.
    #     3. A continued dot directive may not be immediately followed by a converted .bn or .pn. However, if
    #          some other line is continued, and it is immediately followed by a converted .bn or .pn the converted
    #          .bn/.pn will be wrapped into the continued line and assumed to be continued, itself.
    #     4. Continuation for .hn and .il is handled above, with page numbering, due to timing issues.
    i = 0
    inde = False
    while i < (len(self.wb) - 1):
      if self.wb[i].startswith(".de") and self.wb[i].endswith("\\"):
        inde = True
      elif self.wb[i].endswith("\\"):
        if not inde:

          # look for illegal condition: a continued dot directive is followed by a .bn or .pn
          if (self.wb[i].startswith(".") and
                (self.wb[i+1].startswith("⑱") or self.wb[i+1].startswith("⑯"))):
            if (re.match("\.[a-z]", self.wb[i]) and
                  (self.bnmatch.match(self.wb[i+1]) or
                   self.pnmatch.match(self.wb[i+1]))):
              self.crash_w_context("Continued dot directive cannot be followed by .pn or .bn", i)

          # now see if next line is a .bn or .pn and if so,
          #   concatenate it to the current line directly (without a blank),
          #   and put a \ at the end to continue it
          # (this makes the presence of the .pn or .bn transparent to continuation processing)
          elif self.wb[i+1].startswith("⑱") or self.wb[i+1].startswith("⑯"):
            if self.bnmatch.match(self.wb[i+1]) or self.pnmatch.match(self.wb[i+1]):
              self.wb[i] = re.sub(r"\\$", "", self.wb[i]) + self.wb[i+1] + '\\'
              del self.wb[i+1]
              continue

          # now see if the next line is some other dot directive, and warn if so as this is probably not intended
          elif self.wb[i+1].startswith(".") and re.match("\.[a-z]", self.wb[i+1]):
            self.warn_w_context("Possible continuation problem: next line looks like a dot directive.", i)

          self.wb[i] = re.sub(r"\\$", "", self.wb[i]) + " " + self.wb[i+1]
          del self.wb[i+1]
          continue
      else:
        inde = False
      i += 1

    if self.wb[-1].endswith("\\"):
      self.crash_w_context("File ends with continued line.", i)


    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    # play macro (inline: <pm...>)
    # format:
    #   <pm name parameters>
    # Notes:
    #   (1) This form is allowed to generate only one line, which will replace the inline macro invocation in the line
    #       that contains the macro definition.
    #   (2) As .if processing has already "pruned" the macro contents, this means that it is OK for the macro to contain
    #         .if t
    #         1 statement
    #         .if-
    #         .if h
    #         1 statement
    #         .if-
    #   ###I'm not sure if (3) below is still correct; need to think about this...
    #   (3) Unfortunately, we have not processed/protected characters yet, so if the PPer used \> so he could have
    #       a > in a macro argument that will still look like \> and not like ⑳. This makes the reg-exes below more
    #       complex as they need to recognize both \< and \> and not consider them as initiating or ending a <pm> tag.
    #       Note: The revised reg-ex below will allow unescaped < and > so long as they are within quotes.  Of course,
    #             for HTML an unescaped < or > is only valid if it's part of an HTML tag. Otherwise, for normal text in
    #             the HTML file the user needs to use \< and \> to generate &lt; and &gt; to pass validation.
    #   Warning: A \< or \> used OUTSIDE of a quoted string in a <pm> argument will lose its escape character. So for
    #            an argument that is intended as plain text, not an HTML tag, be sure to quote the argument.
    i = 0
    #pattern = r"(^|[^\\])<(pm [^ ]+( +|'[^']*'|\"[^\"]*\"|[^>]+)+)>"
    #pattern = r"(^|[^\\])<(pm [^ '\">]+( +|'[^']*'|\"[^\"]*\"|[^> '\"]*)*)>"
    pattern = r"(^|[^\\])<(pm [^ '\">]+( +|'[^']*?'|\"[^\"]*?\"|[^> '\"]*)*?)>"
    #                    <pm corr 114.4 'village.' 'village,'>
    while i < len(self.wb):

      # need to make sure inline macros are properly terminated
      # so we don't get them output as garbage raw text.
      n = re.search(r"(^|[^\\])<pm [^\\>]*$", self.wb[i])
      if n:
        self.crash_w_context("Inline macro (<pm>) invocation does not have a terminator (>).", i)

      # need to make sure inline macros have at least a macro name
      # so we don't get them output as garbage raw text. Also lets us
      # check for <pm> invocations that are so malformed we didn't
      # recognize them at all.
      o = re.search(r"(^|[^\\])<pm", self.wb[i])
      pm_present = True if (o) else False

      # first argument: some non-blank string for the macro name
      # remaining "arguments" spaces, or a quoted string, or a non-quoted string
      #m = re.search(r"(^|[^\\])<(pm [^ ]+" + # first argument: some  non-blank string: macro name
      #              r"( +|'[^']*'|\"[^\"]*\"|[^>]+)+)" + # remaining "arguments": spaces, or a quoted string, or a non-quoted string
      #              r">", self.wb[i])
      m = re.search(pattern, self.wb[i])
      while m:
        t = pm_guts(m.group(2), i) # go play the macro
        if len(t) > 1:
          self.crash_w_context("Inline macro <{}> tried to generate more than one line of output".format(m.group(2)), i)
        else:
          aadbg1 = m.group(0)
          aadbg2 = m.group(1)
          self.wb[i], count = re.subn(re.escape(m.group(0)), m.group(1) + t[0], self.wb[i], 1)
          if count == 0:
            self.warn_w_context("Substituting {} for inline macro <{}> failed.".format(t[0], m.group(2)), i)
            break

        m = re.search(pattern, self.wb[i])
        o = re.search(r"(^|[^\\])<pm", self.wb[i]) # search for a broken <pm again, too.
        pm_present = True if (o) else False

      if pm_present and not m: # if there was a broken <pm> after the last successful one, fail
        self.crash_w_context("Problem parsing inline macro (<pm>) arguments (missing macro name?)", i)


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
    # remaps of protected characters and some escapes

    for i, line in enumerate(self.wb):
      # dots not part of dot directive
      self.wb[i] = self.wb[i].replace("....", "ⓓⓓⓓⓓ") # four dot ellipsis
      self.wb[i] = self.wb[i].replace("...", "ⓓⓓⓓ") # 3 dot ellipsis
      self.wb[i] = self.wb[i].replace(". . .", "ⓓⓢⓓⓢⓓ") # 3 dot ellipsis, spaced
      self.wb[i] = self.wb[i].replace("\. \. \.", "ⓓⓢⓓⓢⓓ") # 3 dot ellipsis, spaced
      # spacing
      self.wb[i] = self.wb[i].replace(r'\ ', "ⓢ") # non-breaking space
      self.wb[i] = self.wb[i].replace(r'\_', "ⓢ") # alternate non-breaking space
      self.wb[i] = self.wb[i].replace(r"\&", "ⓣ") # zero space
      self.wb[i] = self.wb[i].replace(r"\^", "ⓤ") # thin space (after italics)
      self.wb[i] = self.wb[i].replace(r"\|", "ⓥ") # thick space (between ellipsis dots)

      self.wb[i] = self.wb[i].replace(r"\{", "①")
      self.wb[i] = self.wb[i].replace(r"\}", "②")
      self.wb[i] = self.wb[i].replace(r"\[", "③")
      self.wb[i] = self.wb[i].replace(r"\]", "④")
      self.wb[i] = self.wb[i].replace(r"\<", "⑤")
      self.wb[i] = self.wb[i].replace(r"\>", "⑳")
      self.wb[i] = self.wb[i].replace(r"\:", "⑥")
      self.wb[i] = self.wb[i].replace(r"\-", "⑨")
      self.wb[i] = self.wb[i].replace(r"\#", "⓪")
      self.wb[i] = self.wb[i].replace(r"^^", "⓮") # ^^ will eventually become ^ in the output file
      self.wb[i] = self.wb[i].replace(r"__{", "⓯") # __{ will eventually become _{ in the output file

      # special characters
      # leave alone if in literal block (correct way, not yet implemented)
      # map &nbsp; to non-breaking space (edit: use &#160; entity instead
      # 10-Sep-2014: I don't fully understand why I did this mapping
      self.wb[i] = self.wb[i].replace("&#160;", "ⓢ") # non-breaking-space
      self.wb[i] = self.wb[i].replace("&", "Ⓩ") # ampersand

    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    # define caption models for multi-line captions in the text output
    # .cm name
    # first line
    # second line
    # ...
    # .cm-

    i = 0
    while i < len(self.wb):
      if self.wb[i].startswith(".cm"):
        m = re.match(r"\.cm (.*)", self.wb[i])
        if m:
          model_name = m.group(1)
        else:
          self.crash_w_context("incorrect .cm command: model name missing.", i)
        del self.wb[i]
        t = []
        while i < len(self.wb) and not self.wb[i].startswith(".cm"):  # accumulate statements into the model until we hit another .cm or a .cm-
          t.append(self.wb[i])
          del self.wb[i]
        if i < len(self.wb) and self.wb[i] == ".cm-":       # if we hit a .cm- then delete it and finalize the model
          del self.wb[i] # the closing .cm-
        else:                                               # quit if we hit end-of-file or a .cm before finding the .cm-
          self.fatal("missing .cm- for model: " + model_name)
        # model is stored in t[]
        self.caption_model[model_name] = t
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
          self.crash_w_context("malformed .ce directive", i)
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
    # search for display title directive, record and remove
    i = 0
    indl = False
    while i < len(self.wb):
      # option with a value
      if self.wb[i].startswith(".dl ") or self.wb[i] == ".dl":
        indl = True
      elif self.wb[i].startswith(".dl-"):
        indl = False
      elif not indl:
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
    #
    # Superscripts:
    #   Denoted in ppgen source by:
    #                               ^ followed by 1 character
    #                               ^{1 or more characters}
    # Subscripts:
    #   Denoted in ppgen source by:
    #                               _{1 or more characters}
    # Notes:
    #   1. If you have a book that has an actual ^ character in it, use ^^ to represent it.
    #   2. If you have a book that has a superscript ^ character, use the ^{...} form.
    #   3. If you have a book that has the text _{...} in it, on one line, use __{ for the
    #      opening characters (2 underscores, then the { character).

    pat1 = re.compile("\^([^\{])")   # single-character superscript
    pat2 = re.compile("\^\{(.*?)\}") # multi-character superscript
    pat3 = re.compile("_\{(.*?)\}")  # subscript
    for i in range(len(self.wb)):

      m = re.search(pat1, self.wb[i]) # single character superscript
      while m:
        suptext = m.group(1)
        self.wb[i] = re.sub(pat1, "◸{}◹".format(suptext), self.wb[i], 1)
        m = re.search(pat1, self.wb[i])

      m = re.search(pat2, self.wb[i])
      while m:
        suptext = m.group(1)
        self.wb[i] = re.sub(pat2, "◸{}◹".format(suptext), self.wb[i], 1)
        m = re.search(pat2, self.wb[i])

      m = re.search(pat3, self.wb[i])
      while m:
        subtext = m.group(1)
        self.wb[i] = re.sub(pat3, "◺{}◿".format(subtext), self.wb[i], 1)
        m = re.search(pat3, self.wb[i])

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
    # Examine footnote markers (.fm)
    #   Look for .fm with lz=
    #     If any found, set flags for later
    self.footnoteLzT = False
    self.footnoteLzH = False
    for i, t in enumerate(self.wb):
      if t.startswith(".fm"):
        if "lz=" in t:
          t, lz = self.get_id("lz", t)
          if lz == "t" or lz == "th" or lz == "ht":
           self.footnoteLzT = True
          if lz == "h" or lz == "th" or lz == "ht":
            self.footnoteLzH = True


# ====== ppt ============================================================================

# this class is used to generate UTF-8 or Latin-1 (ANSI) text
# it must be re-run for cases where these differ by user conditionals,
# for example, where in UTF-8 Greek characters are used and in Latin-1
# a transliteration is provided by the post-processor

class Ppt(Book):

  long_table_line_count = 0
  fsz = "100%" # font size for paragraphs (ignored in Ppt, but must be defined as it's ref'd in common code)

  # Also see tag_finalize
  tag_substitutes = {"<i>":      "⓵",  # Use as a substitute for <i> until end of text processing
                     "<b>":      "⓶",  # for <b>
                     "<g>":      "⓷",  # <g>
                     "<sc>":     "⓸",  # <sc>
                     "<f>":      "⓹",  # <f>
                     "<em>":     "⓺",  # <em>
                     "<strong>": "⓻",  # <strong>
                     "<cite>":   "⓼",  # <cite>
                     "<u>":      "⓽",  # <u>
                     }

  def __init__(self, args, renc, config, sout, serr):
    Book.__init__(self, args, renc, config, sout, serr)
    if args.pythonmacrosok:
      Book.python_macros_allowed = True
    self.booktype = "text"
    if self.listcvg:
      self.cvglist()
    self.renc = renc.lower() # requested encoding: "l" Latin-1, "u" UTF-8
    if self.renc == "u":
      self.outfile = re.sub("-src", "", self.srcfile.split('.')[0]) + "-utf8.txt"
    if self.renc == "l":
      self.outfile = re.sub("-src", "", self.srcfile.split('.')[0]) + "-lat1.txt"

  # -------------------------------------------------------------------------------------
  # utility methods

  # print if debug includes 'd'
  def dprint(self, msg):
    if 'd' in self.debug:
      self.print_msg("{}: {}".format(self.__class__.__name__, msg))

  # bailout after saving working buffer in bailout.txt
  def bailout(self, buffer):
    if self.encoding == "utf_8":
      encoding = "UTF-8"
    else:
      encoding = "ISO-8859-1"
    f1 = codecs.open("bailout.txt", "w", encoding=encoding)
    for index,t in enumerate(buffer):
      f1.write( "{:s}\r\n".format(t.rstrip()) )
    f1.close()
    exit(1)

  def shortest_line_len(self, x):
    """ return length of shotest line in x[] """
    shortest_line_len = 1000
    BR = "⓬" # temporary replacement for <br> for ease of programming
    for line in x:
      tline = line
      if self.bnPresent: # remove .bn info if any before doing calculation
        tline = re.sub("⑱.*?⑱","",tline)
      if not tline.endswith(BR): # if line does not end with a <br>
        shortest_line_len = min(shortest_line_len, self.truelen(tline))
    return shortest_line_len

  # wrap string into paragraph in t[]
  def wrap_para(self, s,  indent, ll, ti, perturb=False, keep_br=False, warn=False, expand_supsub=True):
    # if ti < 0, strip off characters that will be in the hanging margin
    # perturb is usually False, but during paragraph rewrapping may be set to True
    # if wrap() discovered that all lines wrapped shorter than 55. In that case
    # wrap() will call wrap_para() again specifying perturb=True. This will cause
    # wrap_para() to monitor the line length, and if a line is less than 55
    # it will backtrack, trying to remove a word from a prior line to increase the
    # length of this one, repeating as necessary.
    hold = ""
    BR = "⓬" # temporary replacement for <br> for ease of processing
    if ti < 0:
      howmany = -1 * ti
      if not self.bnPresent:
        hold = s[0:howmany]
        s = s[howmany:]
      else:
        bnloc = s.find("⑱",0,howmany)  # look for .bn info
        if bnloc == -1:       # if no .bn info
          hold = s[0:howmany]
          s = s[howmany:]
        else:  # must account for .bn info
          m = re.match("(.*?)(⑱.*?⑱)(.*)",s)
          if m:
            howmany1 = len(m.group(1))
            howmany2 = howmany - howmany1
            hold = s[0:howmany1] + m.group(2) + m.group(3)[0:howmany2]
            howmany3 = len(hold)
            s = s[howmany3:]
          else:
            self.fatal("error processing .bn info: {}".format(s))

    # if ti > 0, add leading nbsp
    if ti > 0:
      s = "⑧" * ti + s

    # Convert any <br> in the line to ⓬ for easier processing
    s = re.sub(" ?\<br\> ?", BR, s)

    # handle super/subscripts if necessary
    if expand_supsub:
      s = self.expand_supsub(s)

    # at this point, s is ready to wrap
    mywidth = ll - indent
    t = []    # list of lines
    tbr = []  # list of the break characters that ended the lines
    perturb_limit = -1   # index of earliest line we can try to perturb
    twidth = mywidth
    true_len_s = self.truelen(s)
    brloc = s.find(BR, 0, twidth+1) # look for a <br> within the width we're looking at
    # preferrably break on a <br> or a blank, but check others
    breakchars = [BR, " "] + self.nregs["break-wrap-at"].split()
    while true_len_s > mywidth or brloc != -1:
      twidth2 = 0
      if self.bnPresent:
        m = re.match("(.*?)(⑱.*?⑱)(.*)",s)
        while twidth2 < mywidth and m:
          twidth2 += len(m.group(1))
          if twidth2 <= mywidth:  # if .bn info within first mywidth real characters
            twidth += len(m.group(2)) # allow wider split to account for .bn info
            stemp = m.group(3)
            m = re.match("(.*?)(⑱.*?⑱)(.*)",stemp)

      issue_warning = warn
      snip_at = -1 # no snip spot found yet
      # Plan A: snip at a breakchar within first twidth or twidth+1 characters (see below)
      maxfound = -1
      maxchar = ""
      for c in breakchars:
        if c == BR:
          found = s.find(c, 0, twidth+1) # for <br> need to find the first one within the width + 1 to
                                         # to allow the <br> to be just after the allowed width
        else:
          # for others need to find the last one within the width
          # Note that the break "character" could actually be a string, so we need to
          # know its length in some cases.
          # If the break character is a blank allow width+1 as we'll be deleting it anyway, but
          # for non-blank break characters we need to find them within the width as they'll be kept
          if c == ' ':
            found = s.rfind(c, 0, twidth+1) # but for others, the last one
          else:
            found = s.rfind(c, 0, twidth) # but for others, the last one
        if found != -1:
          if c == BR: # if we have a <br> we need to honor it
            break
          else:  # otherwise try for a wider snip
            if found > maxfound: # keep track of the largest snip, but prefer first one among equals
              maxfound = found
              maxchar = c
      else: # no <br> found, all snips tried
        found = maxfound # reset found/c to their max values
        c = maxchar
      if found != -1: # if we found a snip spot
        issue_warning = False
        if c == " ":
          snip_at = found
        else: # not snipping at a blank; need to preserve the character we're snipping around
          snip_at = found + len(c) # bump snip spot past the character
          true_len_s += len(c)     # increase string length accordingly
          s = s[0:snip_at] + " " + s[snip_at:] # add a blank after the snip char (snip will remove this blank)
      # if snip spot not found within specified width, go to plan B
      else:
        # try to snip on any break character, leaving it wider than the specified width
        # but as narrow as possible, and possibly warn later of the width problem
        minfound = 1000 # keep track of the minimum width and the snip character we used
        minchar = ""
        for c in breakchars:
          found = s.find(c) # this time don't restrict the width
          if found != -1: # if we found a spot to snip
            if found < minfound: # keep track of the narrowest snip, but prefer first one among equals
              minfound = found
              minchar = c
        if minfound != 1000: # if found something
          found = minfound # grab the minimum width and character
          c = minchar
        if found != -1: # if we found a snip spot
          if c == " ":
            snip_at = found
          else: # not snipping at a blank; need to preserve the character we're snipping around
            snip_at = found + len(c) # bump snip spot past the character
            true_len_s += len(c)     # increase string length accordingly
            s = s.replace(c, c + " ", 1) # add a blank after the snip character (blank will be deleted)
        else: # if still didn't find a snip spot
          snip_at = len(s) # Plan C: leave the line wide

      if snip_at > twidth and issue_warning:
        stemp = s.replace(BR, "<br>")
        self.warn("Specified width {} too narrow for word: {}".format(twidth, stemp))
      if not perturb or (snip_at + indent) >= 55 or not t: # for normal processing:
                                                #   Not perturbing, line long enough, or first line
        t.append(s[:snip_at]) # append next line
        tbr.append(c)         # remember the break character that caused the line break
        if snip_at < len(s):
          s = s[snip_at+1:]
        else:
          s = ""
        true_len_s = self.truelen(s)
        twidth = mywidth
        brloc = s.find(BR, 0, twidth + 1) # look for a <br> within the string
      else:          # here only if wrap() wanted us to try to avoid short lines,
                     # this line is short, and it's not the first line (which we can't fix)
        savet = t[:]    # save t, s in case need to restore them
        savetbr = tbr[:] # and also save the break characters used
        saves = s
        while (perturb and  # While perturbing and
               t and        # t has data and
               len(t) > perturb_limit and # is long enough to try perturbing and
               not t[-1].endswith(BR)): # last line does not end with a <br>
          for c in breakchars[1:]: # ignore <br> processing for this attempt as it can't match
            # Remember that c can be a string, not just a single character
            # Also, it might be the last "character" of the previous line, and we need to
            # find the one before that, so we actually have something to snip off
            tlen = len(t[-1]) - len(c)
            snip2 = t[-1].rfind(c, 0, tlen) # Can we snip a word from the last line of t?
            if snip2 != -1: # If so,
              if c == " ": # if snipping on a blank
                ttemp = t[-1][:snip2] # make copy of snipped previous line skipping the blank
              else:        # but if snipping on something else (-, em-dash, etc.) we need to
                ttemp = t[-1][:snip2+len(c)] # include the snipping character in the copy
              true_len_ttemp = self.truelen(ttemp) # get its true length
              if true_len_ttemp + indent >= 55: # is prior line still long enough?
                sep = ' ' if (tbr[-1] == ' ') else ''
                s = t[-1][snip2+len(c):] + sep + s # copy last word of the last line of t
                t[-1] = ttemp
                tbr[-1] = c
                true_len_s = self.truelen(s)
                twidth = mywidth
                brloc = s.find(BR, 0, twidth+1) # look for a <br> within the width we're looking at
                break
          else: # if no snips worked
            if len(t) > 1:            # can't perturb last line; try further back if possible
              s2 = t.pop() # get previous line
              sep = ' ' if (tbr.pop() == ' ') else '' # figure out whether we need to add a blank
              s = s2 + sep + s   # first add last line back to s
              continue
            else:                     # perturbing failed; leave this line short
              perturb = False
              break
          break                       # here if snipping worked; break the perturb loop
        else:                          #
          perturb = False
        if not perturb:                # if perturbing failed leave this line short
          t = savet[:]                 # restore t, tbr, s
          tbr = savetbr[:]
          s = saves
          perturb = True               # we can keep going in perturb mode, but can't backtrack beyond here
          peturb_limit = len(t)        # so remember where we failed
          t.append(s[:snip_at])
          tbr.append(c)         # remember the break character that caused the line break
          if snip_at < true_len_s:
            s = s[snip_at+1:]
          else:
            s = ""
          true_len_s = self.truelen(s)
          twidth = mywidth
          brloc = s.find(BR, 0, twidth+1) # look for a <br> within the width we're looking at

    if len(t) == 0 or len(s) > 0: #ensure t has something in it, but don't add a zero length s (blank line) to t unless t is empty
      t.append(s)

    for i, line in enumerate(t):
        t[i] = t[i].replace("⑧", " ")  # leading spaces from .ti
        t[i] = " " * indent + t[i] # indent applies to all
        if not keep_br and t[i].endswith(BR):
          t[i] = t[i].replace(BR, "")
    if hold != "":
      leadstr = " " * (indent + ti) + hold
      t[0] = leadstr + t[0][indent:]
    return t

  # Squash repeated spaces inside a string, preserving any leading spaces
  def squashBlanks(self, s):
    s = self.pnsearch.sub("", s) # treat pn info as blanks
    i = 0
    while i < len(s) and s[i] == ' ': # preserve leading spaces
      i += 1
    if i > 0:
      s0 = s[:i+1]
      s2 = s[i+1:]
    else:
      s0 = ""
      s2 = s
    while '  ' in s2:   # squash any repeated spaces in interior of string
      s2 = s2.replace('  ', ' ')
    return s0 + s2, i   # return squashed string and count of any preserved leading spaces


  def wrap(self, s,  indent=0, ll=72, ti=0, optimal_needed=True):
    ta = [] # list of paragraph (lists)
    ts = [] # paragraph stats
    BR = "⓬" # temporary replacement for <br> for ease of programming
    if indent >= ll: # catch problematic ll vs indent issues
      self.crash_w_context("Cannot wrap text.\n" +
                           "Indent (.in + leading spaces) bigger than line length (.ll):\n" +
                           "line length = {}; indent = {}\n".format(ll, indent) +
                           ".ll = {}; .in = {}\n".format(self.regLL, self.regIN) +
                           "while wrapping: {}".format(s), self.cl)
    done = False

    s, i = self.squashBlanks(s) # squash any repeated spaces in interior of string
                                # i = number of leading spaces preserved
    #i = 0
    #while i < len(s) and s[i] == ' ': # preserve leading spaces
    #  i += 1
    #if i > 0:
    #  s0 = s[:i+1]
    #  s2 = s[i+1:]
    #else:
    #  s0 = ""
    #  s2 = s
    #while '  ' in s2:   # squash any repeated spaces in interior of string
    #  s2 = s2.replace('  ', ' ')
    #s = s0 + s2

    # expand any super/subscripts
    s = self.expand_supsub(s)

    brloc = s.find("<br>") # check for <br> in string

    # avoid wrapping if s is short enough already, does not contain <br>, and we don't need to worry about ti:
    if not ti and (self.truelen(s) + indent <= ll) and brloc == -1:
      if indent:
        s = (indent * " ") + s
      t = [s]

    else:
      # Handle case where we need to wrap
      if optimal_needed and ll > 55: # don't need optimality if we're wrapping shorter than PG's "minimum" of 55 anyway
        for i in range(0, -8, -2):
          t = self.wrap_para(s, indent, ll+i, ti, keep_br=True, expand_supsub=False)
          ta.append(t)
          sll = self.shortest_line_len(t[0:-1])
          if sll >= 55:
            done = True # Done if already good enough
            break
          else:
            ts.append(sll)

        # All had a line shorter than 55. Tell wrap_para() to
        # try again, perturbing the word layout.
        if not done:
          t = self.wrap_para(s, indent, ll, ti, perturb=True, keep_br=True, expand_supsub=False)
          ta.append(t)
          sll = self.shortest_line_len(t[0:-1])
          if sll >= 55:
            done = True # Done if already good enough
          else:
            ts.append(sll)

        # if not done yet then all test paragraphs had some short lines
        # choose the best one we found
        if not done:
          longest_short = 0
          besti = -1
          for i in range(0,len(ta)):
            if ts[i] > longest_short:
              t = ta[i]
              longest_short = ts[i]
              besti = i
      # else handle case where caller wants only a single, simple wrap
      else:
        t = self.wrap_para(s, indent, ll+i, ti, keep_br=True, expand_supsub=False) # don't need optimal wrap, so just do it once

    # remove any <br> from ends of lines
    for i in range(len(t)):
      if t[i].endswith(BR):
        t[i] = t[i].replace(BR, "")
    return t

  # -------------------------------------------------------------------------------------
  # preprocess working buffer (text versions)
  def preprocess(self):

    self.preProcessCommon()

    ###should rewrite to exempt .li blocks from a bunch of this
    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    # <lang> and <abbr> tags ignored in text version.
    for i in range(len(self.wb)):
      self.wb[i] = re.sub(r"<lang[^>]*>","",self.wb[i])
      self.wb[i] = re.sub(r"</lang>","",self.wb[i])
      self.wb[i] = re.sub(r"<abbr[^>]*>","",self.wb[i])
      self.wb[i] = re.sub(r"</abbr>","",self.wb[i])

    # Look for .nr tag-*** directives as they need to be processed early
    i = 0
    while i < len(self.wb):
      if self.wb[i].startswith(".nr "): # below is part of doNR()
        m = re.match(r"\.nr +(.+?) +(.+)", self.wb[i])
        if m: # don't worry about failures; let doNR() handle them later
          registerName = m.group(1)
          registerValue = m.group(2)
          if registerName.startswith("tag-") and registerName in self.nregs:
            self.nregs[registerName] = self.deQuote(m.group(2), i)
            del(self.wb[i])
            continue
      i += 1

    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    # look for <b>, <g>, <i>, <em>, <strong>, <cite>, <f>, <u>, <sc>
    # and remember if any found
    self.found_bold = False
    self.found_strong = False
    self.found_gesperrt = False
    self.found_italic = False
    self.found_em = False
    self.found_sc = False
    self.found_cite = False
    self.found_ftag = False
    self.found_utag = False

    s = '\n'.join(self.wb)    # make a text blob
    if "<b>" in s:
      self.found_bold = True
    if "<strong>" in s:
      self.found_strong = True
    if "<g>" in s:
      self.found_gesperrt = True
    if "<i>" in s:
      self.found_italic = True
    if "<em>" in s:
      self.found_em = True
    if "<sc>" in s:
      self.found_sc = True
    if "<cite>" in s:
      self.found_cite = True
    if "<f>" in s:
      self.found_ftag = True
    if "<u>" in s:
      self.found_utag = True
    s = ""

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
    ### should rewrite to exempt .li blocks
    text = "\n".join(self.wb)
    text = re.sub(r"#(\d+)#", r"\1", text)
    text = re.sub(r"#([iIvVxXlLcCdDmM]+)#", r"\1", text) # don't forget about Roman numerals as page numbers
    #text = re.sub(r"#(.*?):.*?#", r"\1", text)
    #text = re.sub(r"#([^]].*?):[A-Za-z][A-Za-z0-9\-_\:\.]*?#", r"\1", text)
    text = re.sub(r"#([^]\n].*?):.*?[^[]#", r"\1", text)
    # if there is a named target, then somewhere there
    # is a <target id...> to remove in the text version
    text = re.sub(r"<target.*?>", "", text)
    self.wb = text.splitlines()
    text = ""


    # all page numbers deleted in text version
    # Note: Page numbers have been encoded by previous processing.
    #   They may be stand-alone, in which case we delete the complete
    #   line, or (due to continuation) they may be embedded within a
    #   line. In that case we just remove the encoded page number
    i = 0
    while i < len(self.wb): # switch order if pn followed by blank line
      if self.pnmatch.match(self.wb[i]):
        del self.wb[i]
        continue

      else:
        if self.pnsearch.search(self.wb[i]):
          self.wb[i] = self.pnsearch.sub("", self.wb[i])

      i += 1

    # autonumbered footnotes are assigned numbers
    # footnotes in text
    fncr = 1
    i = 0
    while i < len(self.wb):

      # skip literal sections
      if ".li" == self.wb[i]:
        while (i < len(self.wb)) and not ".li-" == self.wb[i]:
          i += 1
        if i == len(self.wb):
          self.crash_w_context("unclosed .li", i)
        i += 1
        continue

      s = self.wb[i]
      explicit = False
      m = re.search("\[(\d+)\]", s) # explicit
      while m:
        explicit = True
        fncr = int(m.group(1)) + 1
        s = re.sub(re.escape(m.group(0)), "", s, 1)
        m = re.search("\[(\d+)\]", s)
      if explicit: # don't support mixing # and explicit in the same line
        i += 1
        continue

      m = re.search("\[#\]", self.wb[i])
      while m:
        self.wb[i] = re.sub("\[#\]", "[{}]".format(fncr), self.wb[i], 1)
        fncr += 1
        m = re.search("\[#\]", self.wb[i])
      i += 1
    # must do separately
    fncr = 1
    i = 0
    fnlevel = 0
    while i < len(self.wb):

    # skip literal sections
      if ".li" == self.wb[i]:
        while not ".li-" == self.wb[i]:
          i += 1
        i += 1 # skip the .li-
        continue

      if self.wb[i].startswith(".fn "):
        if fnlevel == 0:
          fn0 = i
        fnlevel += 1  # track footnote depth
        m = re.match(r"\.fn (\d+)( |$)", self.wb[i]) # explicit
        if m:
          fncr = int(m.group(1)) + 1

        elif ".fn #" == self.wb[i]:### remember to generate footnote spacing in text
          self.wb[i] = ".fn {}".format(fncr)
          fncr += 1

        else:
          m=re.match(r"\.fn ([A-Za-z0-9\-_\:\.]+)( |$)", self.wb[i])
          if not m:
            self.warn("Invalid footnote name/number: {}".format(self.wb[i]))

      elif self.wb[i].startswith(".fn-"):
        if fnlevel == 0:
          self.crash_w_context("Error: .fn- has no opening .fn command", i)
        fnlevel -= 1

      i += 1###
    if fnlevel != 0:
      self.crash_w_context("Error: Unclosed .fn block", fn0)

    # -------------------------------------------------------------------------------------
    # inline markup processing (text)
    # sc small caps ; l large ; xl x-large ; s small ; xs s-small ; u underline
    # g gesperrt ; converted to text form: em, b, i
    # sn: inline sidenote, converted to [Sidenote: text]

    tempSidenote = self.nregs["Sidenote"] # grab initial value of Sidenote special register
    in_nf = False # flags to help determine whether inline sidenotes are inside of .nf blocks, tables, or footnotes
    in_ta = False
    in_fn = False

    for i, line in enumerate(self.wb):

      # standalone font-size changes dropped
      self.wb[i] = re.sub(r"<\/?l>", "", self.wb[i]) # large
      self.wb[i] = re.sub(r"<\/?xl>", "", self.wb[i]) # x-large
      self.wb[i] = re.sub(r"<\/?xxl>", "", self.wb[i]) # xx-large
      self.wb[i] = re.sub(r"<\/?s>", "", self.wb[i]) # small
      self.wb[i] = re.sub(r"<\/?xs>", "", self.wb[i]) # x-small
      self.wb[i] = re.sub(r"<\/?xxs>", "", self.wb[i]) # xx-small

      # Note: The following will convert <i>, <b>, <f>, <u>, <g>, <sc>, <cite>, <em>, <strong> to
      #       temporary values that will later be replaced with the final values. This allows
      #       full control by the PPer of what values are used while still allowing detection of
      #       conflicts

      # underline dropped unless PPer specifies .nr tag-u <value>
      if self.nregs["tag-u"]:
        self.wb[i] = re.sub(r"<\/?u>", self.tag_substitutes["<u>"], self.wb[i])
      else:
        self.wb[i] = re.sub(r"<\/?u>", "", self.wb[i])

      # italics and emphasis
      if self.nregs["tag-i"]: # tag-i is provided by default
        self.wb[i] = re.sub(r"<\/?i>",  self.tag_substitutes["<i>"], self.wb[i])
      else:
        self.wb[i] = re.sub(r"<\/?i>",  "", self.wb[i])
      self.wb[i] = re.sub(r"<\/?I>", "", self.wb[i]) # alternate italics dropped
      if self.nregs["tag-em"]: # tag-em is provided by default
        self.wb[i] = re.sub(r"<\/?em>",  self.tag_substitutes["<em>"], self.wb[i])
      else:
        self.wb[i] = re.sub(r"<\/?em>",  "", self.wb[i])
      if self.nregs["tag-b"]: # tag-b is provided by default
        self.wb[i] = re.sub(r"<\/?b>",  self.tag_substitutes["<b>"], self.wb[i])
      else:
        self.wb[i] = re.sub(r"<\/?b>",  "", self.wb[i])
      self.wb[i] = re.sub(r"<\/?B>", "", self.wb[i]) # alternate bold dropped

      # strong
      if self.nregs["tag-strong"]: # tag-strong is provided by default
        self.wb[i] = re.sub(r"<\/?strong>",  self.tag_substitutes["<strong>"], self.wb[i])
      else:
        self.wb[i] = re.sub(r"<\/?strong>",  "", self.wb[i])

      # <f> dropped unless PPer specifies .nr tag-f <value>
      if self.nregs["tag-f"]:
        self.wb[i] = re.sub(r"<\/?f>",  self.tag_substitutes["<f>"], self.wb[i])
      else:
        self.wb[i] = re.sub(r"<\/?f>",  "", self.wb[i])

      # cite maps to self.nregs["tag-cite"] always (default: _)
      if self.nregs["tag-cite"]:
        self.wb[i] = re.sub(r"<\/?cite>",  self.tag_substitutes["<cite>"], self.wb[i])
      else:
        self.wb[i] = re.sub(r"<\/?cite>",  "", self.wb[i])

      # alternate handling
      # small caps ignored
      self.wb[i] = re.sub(r"<\/?SC>", "", self.wb[i])

      # allow PPer to override normal <sc> handling via .nr tag-sc <value>
      if self.nregs["tag-sc"]:
        self.wb[i] = re.sub(r"<\/?sc>",  self.tag_substitutes["<sc>"], self.wb[i])

      # gesperrt in text
      if self.nregs["tag-g"]: # tag-g is provided by default
        self.wb[i] = re.sub(r"<\/?g>",  self.tag_substitutes["<g>"], self.wb[i])
      else:
        self.wb[i] = re.sub(r"<\/?g>",  "", self.wb[i])

      # font-size requests dropped
      self.wb[i] = re.sub(r"<\/?fs[^>]*>", "", self.wb[i])

      # color dropped
      self.wb[i] = re.sub(r"<c=[^>]+>", "", self.wb[i])
      self.wb[i] = re.sub(r"<\/c>", "", self.wb[i])

      # inline sidenotes <sn>text</sn>
      # note: Must look for .nr Sidenote as most .nr processing happens after this, during process()
      #       We cannot simply move the .nr processing earlier as (in theory) someone could change the
      #       .nr settings multiple times during a run
      if self.wb[i].startswith(".nf "):
        in_nf = True
      elif self.wb[i].startswith(".nf-"):
        in_nf = False
      elif self.wb[i].startswith(".ta "):
        in_ta = True
      elif self.wb[i].startswith(".ta-"):
        in_ta = False
      elif self.wb[i].startswith(".fn "):
        in_fn = True
      elif self.wb[i].startswith(".fn-"):
        in_fn = False
      elif self.wb[i].startswith(".nr Sidenote"):
        m = re.match(r"\.nr Sidenote (.+)", self.wb[i])
        if m:
          tempSidenote = m.group(1) # remember new Sidenote name value
      m = re.match("(.*?<sn(?: class=[^>]+)?>)(.*?\|.*?)(</sn>.*?)$", self.wb[i])
      while m:
        tmp = m.group(2)
        tmp = re.sub(r"\s*\|\s*", " ", tmp)
        self.wb[i] = m.group(1) + tmp + m.group(3)
        m = re.match("(.*?<sn(?: class=[^>]+)?>)(.*?\|.*?)(</sn>.*?)$", self.wb[i])
      self.wb[i], l = re.subn("<sn(?: class=[^>]+)?>", "[{}: ".format(tempSidenote), self.wb[i])
      self.wb[i] = re.sub("</sn>", "]", self.wb[i])
      if l and (in_nf or in_ta or in_fn):
        self.warn_w_context("Inline sidenote probably won't work well here:", i)

    # do small caps last since it could uppercase a tag.
    if not self.nregs["tag-sc"]: # ignore if we're doing <sc> with tags instead of UPPERCASE

      def to_uppercase(m):
        return m.group(1).upper()

      re_scmult = re.compile(r"<sc>(.+?)<\/sc>", re.DOTALL)
      re_scsing = re.compile(r"<sc>(.*?)<\/sc>")
      #for i, line in enumerate(self.wb):
      i = 0
      while i < len(self.wb):

        # todo: check for and reject nested <sc> and other tags
        # todo: complain if blank lines found
        while "<sc>" in self.wb[i]:
          if not "</sc>" in self.wb[i]: # multi-line
            t = []
            j = i
            while j < len(self.wb) and "</sc>" not in self.wb[j]:
              t.append(self.wb[j])
              #del self.wb[i]
              j += 1
              if j < len(self.wb):
                if self.wb[j].startswith("."): # check for possible dot directive
                  if re.match(r"\.[a-z]", self.wb[j]):
                    self.crash_w_context("Missing </sc>: Apparent dot directive within <sc> string", j)
                elif not self.wb[j]:           # check for a blank line
                  self.crash_w_context("Missing </sc>: Blank line within <sc> string", j)
            if j < len(self.wb):
              t.append(self.wb[j]) # last line (contains </sc>)
            else:
              self.crash_w_context("Missing </sc> for <sc> on flagged line", i)
            ts = "\n".join(t) # make all one line
            ts = re.sub(re_scmult, to_uppercase, ts)
            t = ts.splitlines() # back to a series of lines
            self.wb[i:j+1] = t
          else: # single line
            self.wb[i] = re.sub(re_scsing, to_uppercase, self.wb[i])

        i += 1

    #
    # Handle any .sr for text that have the b option specified
    if self.sr_b:
      #self.dprint("Processing .sr for text with b specified")
      for i in range(len(self.srw)):
        if ((('t' in self.srw[i]) or (self.renc in self.srw[i])) and
            ('b' in self.srw[i])): # if this one is for pre-processing and applies to the text form we're generating
          self.process_SR(self.wb, i)

  # -------------------------------------------------------------------------------------
  # post-process emit buffer (TEXT)

  def postprocess(self):

    # ensure .bn info does not interfere with combining/collapsing space requests
    # by detecting the sequence .RS / .bn info / .RS and swapping to end up with
    #   .RS / .RS / .bn info
    i = 0
    if self.bnPresent:
      while i < len(self.eb) - 2:
        if self.eb[i].startswith(".RS") and self.is_bn_line(self.eb[i+1]):  # if .RS and possibly .bn info
          # handle case of .RS , .bn (from above), .bn by advancing over a sequence of .bn until we find .RS or data
          # if we end on .RS then remove that .RS and insert it before the first .bn in the sequence
          # i => first .RS
          # i + 1 => first .bn
          # i + 2,3,... => possible subsequent .bn
          j = i + 2
          while j < len(self.eb) - 1:
            if self.is_bn_line(self.eb[j]):  # .bn info
              j += 1
            elif self.eb[j].startswith(".RS"): # .RS line; need to move it
              temp = self.eb[j]    # make a copy
              del self.eb[j]  # delete the .RS line
              self.eb.insert(i+1, temp)  # insert it after the first .RS
            else: # everything else (data, or .bn + data) falls through as it can't affect .RS combining
              break
        i += 1

    # remove any left-over .RS -3 directives
    i = 0
    while i < len(self.eb):
      if self.eb[i] == ".RS -3": # if special internal flag for .ul/.ol/.it processing survived, delete it
        del self.eb[i]
        continue
      i += 1

    # combine space requests
    i = 0
    while i < len(self.eb) - 1:
      if self.eb[i] == ".RS c": # if special flag for .ul/.ol/.it processing survived, convert to normal spacing request
        self.eb[i] = ".RS 1"
      m1 = re.match(r"\.RS (-?)(\d+)", self.eb[i])
      m2 = re.match(r"\.RS (-?)(\d+)", self.eb[i+1])
      if m1 and m2:
        spcrq1 = int(m1.group(2))
        spcrq2 = int(m2.group(2))
        # special case for beginning of .it block, with
        # marker line
        # .rs -2
        # .rs 1
        # stuff
        # where we will delete the .RS 1 and append "stuff" to the marker line
        if (m1.group(1) == "-" and m1.group(2) == "2" and
            m2.group(1) == "" and m2.group(2) == "1"):
          if i < len(self.eb) - 2 and not self.eb[i+2].startswith("."):
            t = []
            t.append(self.eb[i-1] + self.eb[i+2].strip())
            self.eb[i-1:i+3] = t
            continue
        if m1.group(1) == "-" and m2.group(1) == "":
          spcrq = spcrq2 - spcrq1
        elif m1.group(1) == "" and m2.group(1) == "-":
          spcrq = spcrq1 - spcrq2
        else:
          spcrq = max(spcrq1, spcrq2)
        self.eb[i] = ".RS {}".format(spcrq)
        del self.eb[i+1] # combine
        continue
      elif m1:
        # special case for .ol/.ul of .RS -1 before an item
        # without another .RS after it. Delete a blank line (if there is
        # one) and delete the .RS -1
        if m1.group(1) == "-" and m1.group(2) == "1":
          if i > 0 and self.eb[i-1] == "":
            del self.eb[i]
            del self.eb[i-1]
          elif i < (len(self.eb)-1) and self.eb[i+1] == "":
            del self.eb[i+1]
            del self.eb[i]
          else:
            del self.eb[i]
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

    # remove possible final .RS c
    if self.eb[-1] == ".RS c":
      del self.eb[-1]

    # restore tokens
    for i, line in enumerate(self.eb):
      self.eb[i] = re.sub("ⓓ|Ⓓ", ".", self.eb[i])  # ellipsis dots
      self.eb[i] = self.eb[i].replace("①", "{")
      self.eb[i] = self.eb[i].replace("②", "}")
      self.eb[i] = self.eb[i].replace("③", "[")
      self.eb[i] = self.eb[i].replace("④", "]")
      self.eb[i] = self.eb[i].replace("⑤", "<")
      self.eb[i] = self.eb[i].replace("⑳", ">")
      self.eb[i] = self.eb[i].replace("⑥", ":")
      self.eb[i] = self.eb[i].replace("⑨", "-")
      self.eb[i] = self.eb[i].replace("⓪", "#")
      self.eb[i] = self.eb[i].replace("⑩", r"\|") # restore temporarily protected \| and \(space)
      self.eb[i] = self.eb[i].replace("⑮", r"\ ")
      self.eb[i] = self.eb[i].replace("⓮", "^")
      self.eb[i] = self.eb[i].replace("⓯", "_{")
      self.eb[i] = re.sub("ⓢ|Ⓢ", " ", self.eb[i]) # non-breaking space (becomes regular space in text output
                                                  # should be OK except if someone rewraps the text file later)
      self.eb[i] = re.sub("ⓣ|Ⓣ", " ", self.eb[i]) # zero space
      self.eb[i] = re.sub("ⓤ|Ⓤ", " ", self.eb[i]) # thin space
      self.eb[i] = re.sub("ⓥ|Ⓥ", " ", self.eb[i]) # thick space
      # ampersand
      self.eb[i] = self.eb[i].replace("Ⓩ", "&")
      # superscripts and subscripts
      if "◸" in self.eb[i] or "◺" in self.eb[i]:
        self.eb[i] = self.expand_supsub(self.eb[i])

      # unprotect temporarily protected characters from Greek strings
      self.eb[i] = self.eb[i].replace("⑩", r"\|") # restore temporarily protected \| and \(space)
      self.eb[i] = self.eb[i].replace("⑮", r"\ ")

      if self.renc == 'u':
        if "[oe]" in self.eb[i]:
          self.warn("unconverted [oe] ligature written to UTF-8 file.")
        if "[ae]" in self.eb[i]:
          self.warn("unconverted [ae] ligature written to UTF-8 file.")

    # Warn about inline tags that won't convert (will be deleted) because their .nr tag-*** values are null
    if self.found_bold and not self.nregs["tag-b"]:
        self.warn("Source file contains <b> but .nr tag-b value is null; <b> will not be marked in text output.")
    if self.found_strong and not self.nregs["tag-strong"]:
        self.warn("Source file contains <strong> but .nr tag-strong value is null; <strong> will not be marked in text output.")
    if self.found_gesperrt and not self.nregs["tag-g"]:
        self.warn("Source file contains <g> but .nr tag-g value is null; <g> will not be marked in text output.")
    if self.found_italic and not self.nregs["tag-i"]:
        self.warn("Source file contains <i> but .nr tag-i value is null; <i> will not be marked in text output.")
    if self.found_em and not self.nregs["tag-em"]:
        self.warn("Source file contains <em> but .nr tag-em value is null; <em> will not be marked in text output.")
    if self.found_cite and not self.nregs["tag-cite"]:
        self.warn("Source file contains <cite> but .nr tag-cite value is null; <cite> will not be marked in text output.")
    if self.found_ftag and not self.nregs["tag-f"]:
        self.warn("Source file contains <f> but .nr tag-f value is null; <f> will not be marked in text output.")
    if self.found_utag and not self.nregs["tag-u"]:
        self.warn("Source file contains <u> but .nr tag-u value is null; <u> will not be marked in text output.")

    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    # look for <b>, <g>, <i>, <em>, <strong>, <cite>, <f>, <u>, <sc>
    # then look for conflicts (both <b> and the b-tag character, etc.)
    bold_char = self.nregs["tag-b"]
    strong_char = self.nregs["tag-strong"]
    gesperrt_char = self.nregs["tag-g"]
    italic_char = self.nregs["tag-i"]
    em_char = self.nregs["tag-em"]
    cite_char = self.nregs["tag-cite"]
    ftag_char = self.nregs["tag-f"]
    utag_char = self.nregs["tag-u"]
    sc_char = self.nregs["tag-sc"]
    found_bold_char = False
    found_strong_char = False
    found_gesperrt_char = False
    found_italic_char = False
    found_em_char = False
    found_cite_char = False
    found_ftag_char = False
    found_utag_char = False
    found_sc_char = False
    tag_check = ""

    # setup to warn of conflicts between tag characters (e.g., <b> and <em> present and using same character)
    # warn of any direct conflicts (e.g., <b> and = present and .nr tab-b "=")
    s = '\n'.join(self.eb)  # make text blob
    if self.found_bold and bold_char and bold_char in s:
      found_bold_char = True
      tag_check += bold_char
      self.warn("both <b> and \"{}\" found in text. markup conflict?".format(bold_char))
    if self.found_strong and strong_char and strong_char in s:
      found_strong_char = True
      tag_check += strong_char
      self.warn("both <strong> and \"{}\" found in text. markup conflict?".format(strong_char))
    if self.found_gesperrt and gesperrt_char and gesperrt_char in s:
      found_gesperrt_char = True
      tag_check += gesperrt_char
      self.warn("both <g> and \"{}\" found in text. markup conflict?".format(gesperrt_char))
    if self.found_italic and italic_char and italic_char in s:
      found_italic_char = True
      tag_check += italic_char
      self.warn("both <i> and \"{}\" found in text. markup conflict?".format(italic_char))
    if self.found_em and em_char and em_char in s:
      found_em_char = True
      tag_check += em_char
      self.warn("both <em> and \"{}\" found in text. markup conflict?".format(em_char))
    if self.found_cite and cite_char and cite_char in s:
      found_cite_char = True
      tag_check += cite_char
      self.warn("both <cite> and \"{}\" found in text. markup conflict?".format(cite_char))
    if self.found_ftag and ftag_char and ftag_char in s:
      found_ftag_char = True
      tag_check += ftag_char
      self.warn("both <f> and \"{}\" found in text. markup conflict?".format(ftag_char))
    if self.found_utag and utag_char and utag_char in s:
      found_utag_char = True
      tag_check += utag_char
      self.warn("both <u> and \"{}\" found in text. markup conflict?".format(utag_char))
    if self.found_sc and sc_char and sc_char in s:
      found_sc_char = True
      tag_check += sc_char
      self.warn("both <sc> and \"{}\" found in text. markup conflict?".format(sc_char))

    # warn if any character conflicts between tags found
    if self.found_bold and tag_check.count(bold_char) > 1:
      self.warn("<b> character " + bold_char + " may be used for multiple purposes in the text output. TN needed?")
    if self.found_strong and tag_check.count(strong_char) > 1:
      self.warn("<strong> character " + strong_char + " may be used for multiple purposes in the text output. TN needed?")
    if self.found_gesperrt and tag_check.count(gesperrt_char) > 1:
      self.warn("<g> character " + gesperrt_char + " may be used for multiple purposes in the text output. TN needed?")
    if self.found_italic and tag_check.count(italic_char) > 1:
      self.warn("<i> character " + italic_char + " may be used for multiple purposes in the text output. TN needed?")
    if self.found_em and tag_check.count(em_char) > 1:
      self.warn("<em> character " + em_char + " may be used for multiple purposes in the text output. TN needed?")
    if self.found_cite and tag_check.count(cite_char) > 1:
      self.warn("<cite> character " + cite_char + " may be used for multiple purposes in the text output. TN needed?")
    if self.found_ftag and ftag_char and tag_check.count(ftag_char) > 1:
      self.warn("<f> character " + ftag_char + " may be used for multiple purposes in the text output. TN needed?")
    if self.found_utag and utag_char and tag_check.count(utag_char) > 1:
      self.warn("<u> character " + utag_char + " may be used for multiple purposes in the text output. TN needed?")
    if self.found_sc and sc_char and tag_check.count(sc_char) > 1:
      self.warn("<sc> character " + sc_char + " may be used for multiple purposes in the text output. TN needed?")


    tag_finalize = [(self.found_italic, "⓵", "tag-i"), # Final substitution list
                    (self.found_bold, "⓶", "tag-b"),
                    (self.found_gesperrt, "⓷", "tag-g"),
                    (self.found_sc, "⓸", "tag-sc"),
                    (self.found_ftag, "⓹", "tag-f"),
                    (self.found_em, "⓺", "tag-em"),
                    (self.found_strong, "⓻", "tag-strong"),
                    (self.found_cite, "⓼", "tag-cite"),
                    (self.found_utag, "⓽", "tag-u"),
                    ]

    # put in the final characters for <b>, <i>, etc. as requested by PPer
    for t in tag_finalize:
      if t[0]:
        s = s.replace(t[1], self.nregs[t[2]])

    self.eb = s.split('\n')

    # process saved search/replace strings for text, if any
    # but only if our output format matches something in the saved "which" value

    #self.dprint("processing .sr for text without b specified")
    for i in range(len(self.srw)):
      if ((('t' in self.srw[i]) or (self.renc in self.srw[i])) and not
          ('b' in self.srw[i] or 'B' in self.srw[i])): # if this one is for post-processing and applies to the text form we're generating
        self.process_SR(self.eb, i)

    # build GG .bin info if needed
    if self.bnPresent:  # if any .bn were found
      self.bb.append("%::pagenumbers = (") # insert the .bin header into the bb array
      i = 0
      ccount = 0
      if self.ppqt2:
        self.ppqt = []
        self.ppqtentries = 0
      while i < len(self.eb):
        bnInLine = False
        offset1 = 0
        offset2 = 0
        m = re.search("(.*?)⑱(.*?)⑱(.*)",self.eb[i])  # find any .bn information in this line
        while m:
          bnInLine = True
          t = " 'Pg{}' => ['offset' => '{}.{}', 'label' => '', 'style' => '', 'action' => '', 'base' => ''],".format(m.group(2),i+1,len(m.group(1)))  # format a line in the .bn array (GG wants a 1-based count)
          t = re.sub("\[","{",t,1)
          t = re.sub("]","}",t,1)
          self.bb.append(t)
          if self.ppqt2:
            ccount += len(m.group(1)) - offset1 # count characters we haven't counted so far
            offset1 = len(m.group(1))
            offset2 = len(m.group(3))
            self.ppqtpage(m.group(2), ccount)
          self.eb[i] = re.sub("⑱.*?⑱", "", self.eb[i], 1)  # remove the .bn information
          m = re.search("(.*?)⑱(.*?)⑱(.*)",self.eb[i])  # look for another one on the same line
        if self.ppqt2:
          if not bnInLine: # if no bn info in this line
            ccount += len(self.eb[i]) + 1
          elif self.eb[i] != "":
            ccount += offset2 + 1
        if bnInLine and self.eb[i] == "": # delete line if it was only .bn info
          del self.eb[i]
        else:
          i += 1
      self.bb.append(");")  # finish building GG .bin file
      #self.bb.append("$::pngspath = '{}\\';".format(os.path.join(os.path.dirname(self.srcfile),"pngs")))
      self.bb.append(r"$::pngspath = '{}\\';".format(os.path.join(os.path.realpath(self.srcfile),"pngs")))
      self.bb.append("1;")

  # -------------------------------------------------------------------------------------
  # save emit buffer in UTF-8 encoding to specified dstfile (text output, UTF-8)
  def saveFileU(self, fn):
    longcount = 0
    while (len(self.eb) > 0) and not self.eb[-1]:
      self.eb.pop()
    f1 = codecs.open(fn, "w", "utf-8")
    for index,t in enumerate(self.eb):
      s = t.rstrip()
      if self.truelen(s) > self.linelimitwarning:
        longcount += 1
        if longcount == 4:
          self.warn("additional long lines not reported")
        if longcount < 4:
          self.warn("long line (>{}) beginning:\n  {} ...".format(self.linelimitwarning, s[:60]))
      f1.write( "{:s}\r\n".format(s) )
    f1.close()

    # save GG .bin file if needed
    if self.bnPresent:
      fnb = fn + ".bin"
      f1 = codecs.open(fnb, "w", "ISO-8859-1")
      for index,t in enumerate(self.bb):
        f1.write("{:s}\r\n".format(t))
      f1.close()
      self.print_msg("GG .bin file {} created.".format(fnb))
      if self.ppqt2: # and PPQTv2 metadata, if requested
        self.ppqtpage("", 0, fn=fn)

  # -------------------------------------------------------------------------------------
  # convert utf-8 to Latin-1 in self.wb
  def utoLat(self):
    described = {}
    t = defaultdict(int)
    for i, line in enumerate(self.wb):
      s = ""
      for c in line: # for every character
        if c in self.d: # is it in the list of converting characters?
          s += self.d[c] # yes, replace with converted Latin-1 character
          t[c] += 1
        else:
          if ord(c) < 0x80:  # safe limit for code page 437
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
      self.lprint("  {:5}{:5} {}".format(self.d[ch], t[ch], unicodedata.name(ch)))

    while not self.wb[-1]:
      self.wb.pop()

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
          self.warn("long line (>{}) beginning:\n  {} ...".format(self.linelimitwarning, s[:60]))
      f1.write( "{:s}\r\n".format(s) )
    f1.close()

    # save GG .bin file if needed
    if self.bnPresent:
      fnb = fn + ".bin"
      f1 = codecs.open(fnb, "w", "ISO-8859-1")
      for index,t in enumerate(self.bb):
        f1.write("{:s}\r\n".format(t))
      f1.close()
      self.print_msg("GG .bin file {} created.".format(fnb))
      if self.ppqt2: # and PPQTv2 metadata, if requested
        self.ppqtpage("", 0, fn=fn)

  # ----- process method group ----------------------------------------------------------

  # .li literal block (pass-through)
  def doLit(self):
    if self.wb[self.cl] == ".li":
      self.cl += 1 # skip the .li
      while (self.cl < len(self.wb)) and self.wb[self.cl] != ".li-":
        self.eb.append(self.wb[self.cl])
        self.cl += 1
      if self.cl < len(self.wb):
        self.cl += 1 # skip the .li-
      else:
        self.crash_w_context("unclosed .li", self.cl)
    elif self.wb[self.cl] == ".li-":
      self.crash_w_context(".li- occurred with no preceding .li", self.cl)
    else:
      self.crash_w_context("Malformed .li directive", self.cl)

  # .pb page break
  def doPb(self):
    t = []
    self.eb.append(".RS 1")
    self.eb.append("-" * 72)
    self.eb.append(".RS 1")
    self.cl += 1

  # doDiv (text)
  def doDiv(self):

    j = self.checkDvNest()

    self.wb[j] = ""              # delete the .dv- and force paragraph break after .dv block if closed properly
    del(self.wb[self.cl])        # simply delete the .dv directive for text processing

  # .hr horizontal rule
  def doHr(self):
    hrpct = 100
    m = re.match(r"\.hr +(w=)?(\d+)%$", self.wb[self.cl])
    if m:
      hrpct = int(m.group(2))
    elif self.wb[self.cl] != ".hr":
      self.warn_w_context("Unrecognized .hr options: {}".format(self.wb[self.cl][3:]), self.cl)
    hrcnt = int(72 * hrpct / 100)
    self.eb.append("{:^72}".format('-'*hrcnt))
    self.cl += 1

  # .tb thought break
  def doTbreak(self):
    self.eb.append((" "*18 + "*       "*5).rstrip())
    self.cl += 1

  #Guts of doH"n" for text
  def doHnText(self, m):
    rend = ""
    hnType = "h" + m.group(0)[2]
    align = self.getHnAlignment(hnType)
    #align = "c" # default all to centered
    if m.group(1): # modifier
      rend = m.group(1) # for text we'll ignore everything except a possible align= operand
      if "align=" in rend:
        rend, align = self.get_id("align", rend)
        align = align.lower()
    if align == "c":
      fmt = "{:^72}"
    elif align == "l" or not align: # l specified or nothing specified (assume l)
      fmt = "{:<72}"
    elif align == "r":
      fmt = "{:>72}"
    else:
      self.crash_w_context("Incorrect align= value (not c, l, or r):", self.cl)

    # clean up options on .hn that text doesn't care about
    #
    if rend:
      if "id=" in rend:
        rend, dummy = self.get_id("id", rend) # ignore id=
      if "pn=" in rend:
        rend, dummy = self.get_id("pn", rend) # ignore pn=
      if "title=" in rend:
        rend, dummy = self.get_id("title", rend) # ignore title=
      if "break" in rend:
        rend = re.sub("(no)?break", "", rend) # ignore break/nobreak
      if rend and rend != " ":
        self.warn_w_context(".hn directive contains extraneous text: {}".format(rend), self.cl)

    #Check for possible error of having a dot directive immediately after a .hn
    if self.cl < len(self.wb) and self.wb[self.cl+1].startswith("."):
      self.warn_w_context("Warning: dot-directive should not immediately follow .hn directive: {}".format(self.wb[self.cl+1]),
        self.cl)

    self.eb.append(".RS 1")
    if self.bnPresent and self.is_bn_line(self.wb[self.cl+1]):    # account for a .bn that immediately follows a .h1/2/3/etc
      self.eb.append(self.wb[self.cl+1])    # append the .bn info to eb as-is
      self.cl += 1                          # and ignore it for handling this .h"n"
    h2a = self.wb[self.cl+1].split('|')
    for line in h2a:
      line = line.strip()
      if self.truelen(line) <= self.regLL: # wrapping is not needed
        while '  ' in line:   # squash any repeated internal spaces
          line = line.replace('  ', ' ')
        self.eb.append(self.truefmt(fmt, line).rstrip())
      else: # wrapping is needed
        s = self.wrap(line, ll=self.regLL, optimal_needed=False)
        for t in s:
          self.eb.append(self.truefmt(fmt, t).rstrip())

    self.eb.append(".RS 1")
    self.cl += 2

  # h1
  def doH1(self):
    m = re.match(r"\.h1 ?(.*)", self.wb[self.cl])
    self.doHnText(m)

  # h2
  def doH2(self):
    m = re.match(r"\.h2 ?(.*)", self.wb[self.cl])
    self.doHnText(m)

  # h3
  def doH3(self):
    m = re.match(r"\.h3 ?(.*)", self.wb[self.cl])
    self.doHnText(m)

  # h4
  def doH4(self):
    m = re.match(r"\.h4 ?(.*)", self.wb[self.cl])
    self.doHnText(m)

  # h5
  def doH5(self):
    m = re.match(r"\.h5 ?(.*)", self.wb[self.cl])
    self.doHnText(m)

  # h6
  def doH6(self):
    m = re.match(r"\.h6 ?(.*)", self.wb[self.cl])
    self.doHnText(m)

  # .sp n
  def doSpace(self):
    m = re.match(r"\.sp (\d+)", self.wb[self.cl])
    if m:
      howmany = int(m.group(1))
      self.eb.append(".RS {}".format(howmany))
    else:
      self.crash_w_context("malformed .sp directive", self.cl)
    self.cl += 1

  # .fs
  # change font size for following paragraphs (and lists, divs, footnotes)
  # no effect in text
  def doFontSize(self):
    del self.wb[self.cl]

  # .il illustrations (text)
  def doIllo(self):

    def parse_illo(s):   # simplified parse_illo; supports caption model and alt=, ignoring the rest
      s0 = s[:]  # original .il line
      ia = {}

      # caption model
      cm = ""
      if "cm=" in s:
        s, cm = self.get_id("cm", s)
      ia["cm"] = cm

      # alt text
      alt = ""
      if "alt=" in s:
        s, alt = self.get_id("alt",s)
        # don't escape single-quotes in the text version, silly!
        #alt = re.sub("'","&#39;",alt) # escape any '
      ia["alt"] = alt

      return(ia)

    m = re.match(r"\.il (.*)", self.wb[self.cl])
    if m:
      # ignore the illustration line except for any cm= info and possible alt= text
      ia = parse_illo(self.wb[self.cl]) # parse .il line
      # is the .il line followed by a caption line?
      self.eb.append(".RS 1") # request at least one space in text before illustration
      self.cl += 1 # the illo line
      caption = ""
      if self.cl < len(self.wb) and self.wb[self.cl].startswith(".ca"):
        # there is a caption. it may be on multiple lines
        if ".ca" == self.wb[self.cl]: # multiple line caption
          self.cl += 1 # skip the starting .ca
          if ia["cm"] == "": # if no caption model specified
            s = "[{}: ".format(self.nregs["Illustration"])
            self.eb.append(s)
            self.eb.append("")
            i = self.cl        # remember where we started
            while (self.cl < len(self.wb)) and not (self.wb[self.cl]).startswith(".ca-"):
              s = self.wb[self.cl]
              t = self.wrap(s, 4, self.regLL, -2)
              self.eb += t
              self.cl += 1
            if self.cl == len(self.wb):
              self.crash_w_context("Unclosed .ca directive(1).", i-1)
            self.eb.append("]")
            self.cl += 1 # skip the closing .ca-
          else: # caption model specified
            model = self.caption_model[ia["cm"]]
            j = 0
            k = 1
            i = self.cl
            while j < len(model) and self.cl < len(self.wb):
              t = []
              ss = "\${}".format(k)
              s = model[j]
              if re.search(ss,s): # if caption line has a $"n" marker in it, perform substitution
                if self.wb[self.cl].startswith(".ca-"):
                  self.crash_w_context("End of caption before end of model(1).", i-1)
                s = re.sub(ss,self.wb[self.cl], s)
                k += 1
                self.cl += 1
                if self.truelen(s) > self.regLL: # must wrap the string, and indent the leftover part
                  m = re.match(r"(\s*)(.*)",s)
                  if m:
                    tempindent = self.truelen(m.group(1)) + 2
                    s = m.group(2)
                    t = self.wrap(s, tempindent, self.regLL, -2)
                  else:
                    self.crash_w_context("Oops. Unexpected problem with caption.", i-1)
                else:
                  t.append(s) # no need to wrap, as it's short enough already ### need to squash blanks?
              else: # caption line does not have marker, so it's literal text, just wrap to LL if necessary and assume user knows what he's doing
                if self.truelen(s) > self.regLL:
                  t = self.wrap(s, 0, self.regLL, 0, optimal_needed=False)
                else: # no need to wrap if it's short enough ### need to squash blanks?
                  t.append(s)
              self.eb += t
              j += 1
            if j < len(model):
              self.crash_w_context("End of caption before end of model(2).", i-1)
            if self.cl == len(self.wb):
              self.crash_w_context("Unclosed .ca directive(2).", i-1)
            if self.wb[self.cl] != ".ca-":
              self.crash_w_context("Caption and model lengths do not match properly.", i-1)
            self.cl += 1
        else:
          # single line
          if ia["cm"] != "": # if caption model specified
            self.warn("Caption model specified for a single-line caption: {}".format(self.wb[self.cl-1]))
          caption = self.wb[self.cl][4:]
          s = "[{}: {}]".format(self.nregs["Illustration"],caption)
          t = self.wrap(s, 0, self.regLL, 0, optimal_needed=False)
          self.eb += t
          self.cl += 1 # caption line
      else:
        # no caption, just illustration
        if ia["alt"]: # use alt text if available
          t = self.wrap("[{}: {}]".format(self.nregs["Illustration"], ia["alt"]), 0, self.regLL, 0)
        else:
          t = ["[{}]".format(self.nregs["Illustration"])]
        self.eb += t
      self.eb.append(".RS c") # request at least one space in text after illustration
                              # (special flag for .ul/.ol/.it processing)
    else:
      self.crash_w_context("Malformed .il directive: {}".format(self.wb[self.cl]), self.cl)

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
      self.crash_w_context("malformed .in directive", self.cl)

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
    self.crash_w_context("malformed .ll directive", self.cl)

  # .ti temporary indent
  def doTi(self):
    s = self.wb[self.cl].split()
    if len(s) > 1:         # will always be true, as we converted ".ti" with no argument to ".ti 2" earlier
      if s[1].isdigit() or s[1].startswith('-') or s[1].startswith('+'):
        self.regTI += int(s[1])
      elif s[1] == "end": # remove persistent temporary indent?
        self.regTI = 0
        self.regTIp = 0
      else:
        self.crash_w_context("Malformed .ti directive.", self.cl)
    if len(s) > 2:
      if s[2] == "begin":
        self.regTIp = self.regTI # start persistent temporary indent
      elif s[2] == "end":
        self.regTIp = 0
      else:
        self.crash_w_context("Malformed .ti directive.", self.cl)
    else:
      self.regTIp = 0 # force end of persistent temporary indent if .ti found without "begin"
    self.cl += 1

  # no-fill, centered (text)
  def doNfc(self, mo):
    t = []
    i = self.cl + 1 # skip the .nf c line
    while self.wb[i] != ".nf-":
      bnInBlock = False
      if self.bnPresent and self.is_bn_line(self.wb[i]): #just copy .bn info lines, don't change them at all
        bnInBlock = True
        t.append(self.wb[i])
        i += 1
        continue

      if self.wb[i].startswith(".dc") or self.wb[i].startswith(".di"):
        del self.wb[i]
        continue

      xt = self.regLL - self.regIN # width of centered line
      xs = "{:^" + str(xt) + "}"
      line = self.wb[i].strip()
      len2 = self.truelen(line) # actual length of line, ignoring non-spacing Unicode characters
      indent = self.regIN
      ###below is the start of what would be needed if we want text processing to handle .ti in .nf c
      ###like HTML processing does
      ###if self.regTI != 0 and self.regTI != -1000: # apply any non-zero temporary indent
      ###  indent += self.regTI
      ###  self.regTI = 0
      if len2 <= xt:
        t.append(" " * indent + self.truefmt(xs, line)) # just format it if it fits within the width
      else:                                                 # else wrap it with a hanging indent
        s = line
        wi = 0
        m = re.match("^(\s+)(.*)", s)
        if m:
          wi = len(m.group(1))
          s = m.group(2)
        #u = self.wrap(s, wi+3, xt, -3, optimal_needed=False)
        u = self.wrap(s, 0, xt, 0, optimal_needed=False)
        for line in u:
          t.append(" " * indent + self.truefmt(xs, line))
        # code below wrapped a long centered line and then used a hanging indent. New code (above) centers each line of
        # the wrapped text
        #line = u[0]
        #u[0] = " " * indent + self.truefmt(xs, line)
        #t.append(u[0]) # output first line
        #bcnt = 0
        #while bcnt < len(u[0]) and u[0][bcnt] == " ": bcnt += 1 # count leading blanks in first line
        #blanks = " " * bcnt
        #for line in u[1:]: # then output other lines, padded with that number of blanks ### does this work?
        #  t.append(blanks + line)

      i += 1
    self.cl = i + 1 # skip the closing .nf-
    # see if the block has hit the left margin
    need_pad = False
    for line in t:
      if line and line[0] != " ":
        if not bnInBlock or not self.is_bn_line(line):
          need_pad = True
          break
    if need_pad:
      self.warn("inserting leading space in wide .nf c (or .ce)")
      for i,line in enumerate(t):
        t[i] = " "+ t[i]
    t.insert(0, ".RS 1")
    t.append(".RS c") # (special flag for .ul/.ol/.it processing)
    self.eb.extend(t)

  # calculate block width
  def calculateBW(self, lookfor):
    i = self.cl + 1
    startloc = i
    maxw = 0
    while i < len(self.wb) and not self.wb[i] == lookfor:
      maxw = max(maxw, self.truelen(self.wb[i]))
      i += 1
    if i == len(self.wb):
      # unterminated block
      self.crash_w_context("unterminated block. started with:", self.cl)
    return maxw

  # no-fill, left (text)
  # honors leading spaces; allows .ce and .rj
  def doNfl(self, mo):

    try: # determine the indentation for this .nf l block
      indent = int(self.nregs["nfl"])
    except:
      self.warn("Invalid .nr nfl value: {}".format(self.nregs["nfl"]))
      indent = -1
    if indent < 0:
      indent = self.regIN
      if self.regIN == 0:
        self.warn("no-fill, left block at left margin starting:\n  {}".format(self.wb[self.cl+1]))
    else:
      if self.regIN != 0 and self.regIN != indent:
        indent = self.regIN
        #self.warn("Both .in {} and .nr nfl {} specified; ".format(self.regIN, self.nregs["nfl"]) +
        #          "using .in value for no-fill block starting:\n  {}".format(self.wb[self.cl+1]))

    self.eb.append(".RS 1")
    regBW = min(self.calculateBW(".nf-"), self.regLL)
    i = self.cl + 1 # skip the .nf l line
    while self.wb[i] != ".nf-":

      if self.wb[i].startswith(".dc") or self.wb[i].startswith(".di"):
        del self.wb[i]
        continue

      # special cases: .ce and .rj
      m = re.search(r"\.ce (\d+)", self.wb[i])
      if m:
        count = int(m.group(1))
        i += 1 # skip the .ce
        while count > 0:
          if self.bnPresent and self.is_bn_line(self.wb[i]):  # if this line is bn info then just put it in the output as-is
            self.eb.append(self.wb[i])
            i += 1
            continue
          xs = "{:^" + str(regBW) + "}"
          line = self.wb[i].strip()
          self.eb.append(" " * indent + self.truefmt(xs, line))
          i += 1
          count -= 1
        continue

      m = re.search(r"\.rj (\d+)", self.wb[i])
      if m:
        count = int(m.group(1))
        i += 1 # skip the .rj
        while count > 0:
          if self.bnPresent and self.is_bn_line(self.wb[i]):  # if this line is bn info then just put it in the output as-is
            self.eb.append(self.wb[i])
            i += 1
            continue
          xs = "{:>" + str(regBW) + "}"
          line = self.wb[i].strip()
          self.eb.append(" " * indent + self.truefmt(xs, line))
          # but it may look off with proportional fonts, esp. if the rj text is Hebrew or another rtl language
          i += 1
          count -= 1
        continue

      if self.bnPresent and self.is_bn_line(self.wb[i]):   # just copy .bn info lines, don't change them at all
        self.eb.append(self.wb[i])
        i += 1
        continue

      s = (" " * indent + self.wb[i])
      # if the line is shorter than 72 characters (really, the line length), just send it to emit buffer
      # if longer, calculate the leading spaces on line and use as shift amount.
      # a .ti lets it wrap
      if self.truelen(s) > self.regLL:
        wi = 0
        m = re.match("^(\s+)(.*)", s)
        if m:
          wi = len(m.group(1))
          s = m.group(2)
        u = self.wrap(s, wi+3, self.regLL, -3, optimal_needed=False)
        for line in u:
          self.eb.append(line)
      else:
        self.eb.append(s) ### need to squash blanks?
      i += 1
    self.eb.append(".RS c") # (special flag for .ul/.ol/.it processing)
    self.cl = i + 1 # skip the closing .nf-

  # no-fill, block (text)
  def doNfb(self, mo):
    t = []
    firstline = self.cl
    regBW = min(self.calculateBW(".nf-"), self.regLL)
    i = self.cl + 1 # skip the .nf b line
    xt = self.regLL - self.regIN
    lmar = max((xt - regBW)//2, 0)
    bnInBlock = False                # no .bn info encountered in this block yet
    while self.wb[i] != ".nf-":

      if self.wb[i].startswith(".dc") or self.wb[i].startswith(".di"):
        del self.wb[i]
        continue

      # special cases: .ce and .rj
      m = re.search(r"\.ce (\d+)", self.wb[i])
      if m:
        count = int(m.group(1))
        i += 1 # skip the .ce
        while count > 0:
          if self.bnPresent and self.is_bn_line(self.wb[i]): # if this line is bn info then just put it in the output as-is
            bnInBlock = True
            t.append(self.wb[i])
            i += 1
            continue
          xs = "{:^" + str(regBW) + "}"
          line = self.wb[i].strip()
          t.append(" " * self.regIN + " " * lmar + self.truefmt(xs, line))
          i += 1
          count -= 1
        continue

      m = re.search(r"\.rj (\d+)", self.wb[i])
      if m:
        count = int(m.group(1))
        i += 1 # skip the .rj
        while count > 0:
          if self.bnPresent and self.is_bn_line(self.wb[i]):  # if this line is bn info then just put it in the output as-is
            bnInBlock = True
            t.append(self.wb[i])
            i += 1
            continue
          xs = "{:>" + str(regBW) + "}"
          line = self.wb[i].strip()
          t.append(" " * self.regIN + " " * lmar + self.truefmt(xs, line))
          i += 1
          count -= 1
        continue

      if self.bnPresent and self.is_bn_line(self.wb[i]):   #just copy .bn info lines, don't change them at all
        bnInBlock = True
        t.append(self.wb[i])
        i += 1
        continue

      s = (" " * self.regIN + " " * lmar + self.wb[i].rstrip())
      if self.truelen(s) > self.regLL:
        wi = 0
        m = re.match("^(\s+)(.*)", s)
        if m:
          wi = len(m.group(1))
          s = m.group(2)
        u = self.wrap(s, wi+3, self.regLL, -3)
        for line in u:
          t.append(line)
      else:
        t.append(s) ### need to squash blanks?
      i += 1
    self.cl = i + 1 # skip the closing .nf-

    # see if the block has hit the left margin
    need_pad = False
    for line in t:
      if line and line[0] != " ":
        if not bnInBlock or not self.is_bn_line(line):
          need_pad = True
          break
    if need_pad:
      self.warn_w_context("inserting leading space in wide .nf b", firstline)
      for i,line in enumerate(t):
        t[i] = " "+ t[i]
    t.insert(0, ".RS 1")
    t.append(".RS c") # (special flag for .ul/.ol/.it processing)
    self.eb.extend(t)

  # no-fill, right (text)
  def doNfr(self, mo):
    self.eb.append(".RS 1")
    regBW = min(self.calculateBW(".nf-"), self.regLL)
    #fixed_indent = self.regIN + (self.regLL - regBW)
    fixed_indent = self.regIN if (self.regLL == regBW) else self.regLL - regBW
    i = self.cl + 1 # skip the .nf r line
    while self.wb[i] != ".nf-":

      if self.wb[i].startswith(".dc") or self.wb[i].startswith(".di"):
        del self.wb[i]
        continue

      # special cases: .ce and .rj
      m = re.search(r"\.ce (\d+)", self.wb[i])
      if m:
        count = int(m.group(1))
        i += 1 # skip the .ce
        while count > 0:
          if self.bnPresent and self.is_bn_line(self.wb[i]):  # if this line is bn info then just put it in the output as-is
            self.eb.append(self.wb[i])
            i += 1
            continue
          xs = "{:^" + str(regBW) + "}"
          line = self.wb[i].strip()
          self.eb.append(" " * fixed_indent + self.truefmt(xs, line))
          i += 1
          count -= 1
        continue

      m = re.search(r"\.rj (\d+)", self.wb[i])
      if m:
        count = int(m.group(1))
        i += 1 # skip the .rj
        while count > 0:
          if self.bnPresent and self.is_bn_line(self.wb[i]):  # if this line is bn info then just put it in the output as-is
            self.eb.append(self.wb[i])
            i += 1
            continue
          xs = "{:>" + str(regBW) + "}"
          line = self.wb[i].strip()
          self.eb.append(" " * fixed_indent + self.truefmt(xs, line))
          i += 1
          count -= 1
        continue

      if self.bnPresent and self.is_bn_line(self.wb[i]):   #just copy .bn info lines, don't change them at all
        self.eb.append(self.wb[i])
        i += 1
        continue

      s = (" " * fixed_indent + self.wb[i].rstrip())
      if self.truelen(self.wb[i].rstrip()) > self.regLL:
        wi = 0
        m = re.match("^(\s+)(.*)", s)
        if m:
          wi = len(m.group(1))
          s = m.group(2)
        u = self.wrap(s, wi+3, self.regLL, -3, optimal_needed=False)
        for line in u:
          self.eb.append(line)
      else:
        self.eb.append(s) ### need to squash blanks?
      i += 1
    self.cl = i + 1 # skip the closing .nf-
    self.eb.append(".RS c") # (special flag for .ul/.ol/.it processing)

  # .nf no-fill blocks, all types (text)
  # called first, then dispatched
  def doNf(self):
    # not expecting a request to close. get here on open
    # m = re.match(r"\.nf .-", self.wb[self.cl])
    m = re.match(r"\.nf-", self.wb[self.cl])
    if m:
      self.crash_w_context("attempting to close an unopened block with {}".format(self.wb[self.cl]),self.cl)
    m = re.match(r"\.nf (.)", self.wb[self.cl])
    nf_handled = False
    if m:
      margin_override = False
      if re.match(r"\.nf . 0", self.wb[self.cl]):
        margin_override = True # ignored in text
      nftype = m.group(1) # c, l, b or r
      if nftype == 'c':
        nf_handled = True
        self.doNfc(margin_override)
      elif nftype == 'l':
        nf_handled = True
        self.doNfl(margin_override)
      elif nftype == 'r':
        nf_handled = True
        self.doNfr(margin_override)
      elif nftype == 'b':
        nf_handled = True
        self.doNfb(margin_override)
    if not nf_handled:
      self.crash_w_context("invalid .nf option: {}".format(self.wb[self.cl]),self.cl)

  # footnotes (Text)
  # here on footnote start or end
  # note: in text do not check for duplicate footnotes. they occur in the wild
  # note: invalid footnote names generated warning messages earlier during pre-processing
  def doFnote(self):
    m = re.match(r"\.fn-", self.wb[self.cl])
    if m: # footnote ends
      if self.footnoteLzT and not self.keepFnHere: # if special footnote landing zone in effect (and not disabled for this footnote)
        self.grabFootnoteT()
      self.regIN -= 2
      del self.wb[self.cl]
      return
    else: # footnote begins
      fnname = ""
      m = re.match(r"\.fn (\d+)( |$)(lz=here|tlz=here)?", self.wb[self.cl]) # First look for numeric
      if m: # footnote start
        fnname = m.group(1)
        self.keepFnHere = True if (m.group(3)) else False # test for lz=here and remember for .fn- processing
      else:                       # then check for named footnote
        m = re.match(r"\.fn ([A-Za-z0-9\-_\:\.]+)( |$)(lz=here|tlz=here)?", self.wb[self.cl])
        if m:
          fnname = m.group(1)
          self.keepFnHere = True if (m.group(3)) else False # test for lz=here and remember for .fn- processing
        else:
          fnname = "<<Invalid footnote name; see messages>>"
      self.eb.append("{} {}:".format(self.nregs["Footnote"], fnname))
      if self.keepFnHere and not self.footnoteLzT:
        if m.group(3).startswith("tlz"):
          self.warn(".fn specifies tlz=here but landing zones not in effect for text output:{}".format(self.wb[self.cl]))
        elif m.group(3).startswith("lz") and not self.footnoteLzT and not self.footnoteLzH:
          self.warn(".fn specifies lz=here but no landing zones are in effect:{}".format(self.wb[self.cl]))
      if self.footnoteLzT and not self.keepFnHere: # if special footnote landing zone processing in effect
        self.footnoteStart = len(self.eb) - 1 # remember where this footnote started
      self.regIN += 2
      del self.wb[self.cl]

  # grab a complete footnote out of self.eb and save it for later
  def grabFootnoteT(self):
    t = [] # buffer for the footnote label and text
    i = self.footnoteStart
    while i < len(self.eb):
      t.append(self.eb[i]) # grab a line then delete it
      del self.eb[i]
    self.fnlist.append(t) # when done, append complete list into fnlist for later use

  # footnote mark
  def doFmark(self):
    rend = True
    lz = False
    m = re.match(r"\.fm (.*)", self.wb[self.cl])
    if m:
      options = m.group(1)
      if "norend" in options:
        rend = False
      if "rend=" in options:
        options, rendvalue = self.get_id("rend", options)
        if rendvalue == "no" or rendvalue == "norend" or not "t" in rendvalue:
          rend = False
      rendafter = False
      if "rendafter=" in options:
        options, rendaval = self.get_id("rendafter", options)
        if rendaval.startswith("y"):
          rendafter = True
      if "lz=" in options:
        options, lzvalue = self.get_id("lz", options)
        if "t" in lzvalue:
          lz = True
        else:
          rend = False  # If this .fm is a landing zone for html but not text, don't do rend for it either
      if "=" in options:
        self.warn("Unrecognized option in .fm command: {}".format(self.wb[self.cl]))
    if rend and ((not lz) or (lz and len(self.fnlist))):
      self.eb.append(".RS 1")
      self.eb.append("-----")
      self.eb.append(".RS 1")
    else:
      rend = False
    if lz:
      # emit saved footnotes
      if len(self.fnlist): # make sure there's something to generate
        for t in self.fnlist:
          for s in t:
            self.eb.append(s)
        del self.fnlist[:]  # remove everything we handled
        self.fnlist = []
        if rend and rendafter:
          self.eb.append(".RS 1")
          self.eb.append("-----")
          self.eb.append(".RS 1")
      else:
        self.warn_w_context("No footnotes saved for this landing zone.", self.cl)
    self.cl += 1

  # Table code, text
  # Note: tables center in a 72-character line. Should they instead center in the PPer-specified line width?
  def doTable(self):

    # get maximum width of specified cell by scanning all rows in table
    # must account for markup
    def getMaxWidth(c,ncols):
      j = self.cl + 1
      maxw = 0
      while self.wb[j] != ".ta-":
        # blank and centered and .bn info lines are not considered
        if self.wb[j] == "" or not "|" in self.wb[j]:
          j += 1
          continue
        u = self.wb[j].split("|")
        if len(u) != ncols:
            self.crash_w_context("table has wrong number of columns:{}".format(self.wb[j]), j)
        t = u[c].strip()
        if len(t) >= 4 and t[0:4] == "<th>": # if cell starts with <th> remove it
          t = t[4:]
        if len(t) >= 6 and t[0:4] == "<al=": # possible alignment directive?
          t = re.sub(r"^<al=[lrch]>", "", t, 1) # ignore any alignment directives
        if t != "<span>": # ignore <span> cells for purposes of figuring max width of this column
          maxw = max(maxw, self.truelen(t)) # ignore lead/trail whitespace and account for non-spacing characters
        j += 1
      return maxw

    if self.wb[self.cl] == ".ta-":
      self.crash_w_context(".ta- found outside of table", self.cl)
    table_start = self.cl
    haligns = list() # 'h', 'l', 'r', or 'c'  no default; must specify
    valigns = list() # 't', 'b', or 'm' default 't'
    widths = list() # column widths
    totalwidth = 0

    # look for continuation characters; restore to one line (now, just ensure .ta- is found)
    k1 = self.cl
    s = self.wb[k1]
    while k1 < len(self.wb) and self.wb[k1] != ".ta-":
      #while self.wb[k1].endswith("\\"):
      #  self.wb[k1] = re.sub(r"\\$", "", self.wb[k1])
      #  self.wb[k1] = self.wb[k1] + " " + self.wb[k1+1]
      #  del self.wb[k1+1]
      k1 += 1
    if k1 == len(self.wb):
      self.crash_w_context("missing .ta- in table starting: {}".format(s), self.cl)

    # remove table summary if present.
    if "s=" in self.wb[self.cl]:
      self.wb[self.cl] = self.get_id("s", self.wb[self.cl], 1)

    # pull out optional user-specified Epub//Mobi width %
    tw_epub = ""
    if "ew=" in self.wb[self.cl]:
      self.wb[self.cl], tw_epub = self.get_id("ew", self.wb[self.cl])

    # pull out optional user-specified HTML width %
    tw_html = ""
    if "w=" in self.wb[self.cl]:
      self.wb[self.cl], tw_html = self.get_id("w", self.wb[self.cl])

    # remove id= if present
    if "id=" in self.wb[self.cl]:
      self.wb[self.cl] = self.get_id("id", self.wb[self.cl], 1)

    # pull out bl= (blank line) option
    # bl=none (PPer in total control; don't add any blank lines) or
    #    auto (add a blank line if cell wraps, unless PPer already suppiied one)
    temp = "y"
    if "bl=" in self.wb[self.cl]:
      self.wb[self.cl], temp = self.get_id("bl", self.wb[self.cl])
      temp = temp.lower()[0] # lower-case and grab first character
    if temp == "y":
      add_blank_lines = True
    elif temp == "n":
      add_blank_lines = False
    else:
      self.warn_w_context("Unexpected bl= value on .ta {} ignored; assuming y".format(temp), self.cl)

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
      m = re.match(r"\.ta ([hlcr]+)", self.wb[self.cl])
      if m:
        t0 = m.group(1) # all the specifiers
        t = list(t0) # ex: ['r','c','l', 'h']
        ncols = len(t) # ex: 3
        s = ".ta "
        for i,x in enumerate(t):
          cwidth = getMaxWidth(i,ncols) # width
          s += "{}t:{} ".format(t0[i],cwidth)
        self.wb[self.cl] = s.strip()  # replace with widths specified
    #self.dprint("doTable (text), specified or calculated column widths: {}".format(self.wb[self.cl]))

    # if vertical alignment not specified, default to "top" now
    # .ta l:6 r:22 => .ta lt:6 rt:22
    while re.search(r"[^hlcr][hlcr]:", self.wb[self.cl]):
      self.wb[self.cl] = re.sub(r"([hlcr]):", r'\1t:', self.wb[self.cl])

    t = self.wb[self.cl].split() # ['.ta', 'lt:6', 'rt:22']
    ncols = len(t) - 1  # skip the .ta piece
    j = 1
    bbefore = list() # border characters before cells
    bafter  = list() # and after cells
    while j <= ncols:
      u = t[j].split(':')
      if len(u) != 2:
        self.crash_w_context("Incorrect column specification (missing the colon), {}".format(t[j]), self.cl)

      appended = False
      m = re.match(r"([|=]*)(..)", u[0]) # extract border-before character(s)
      if m:
        u[0] = m.group(2)
        bspec = m.group(1)
        if bspec and self.renc == "l": # ignore borders if Latin-1 output
          self.warn("Table borders ignored for Latin-1 output.")
        elif bspec == '|':
          bbefore.append('│' + self.nregs["text-cell-padding-left"]) # box drawings light vertical \u2502
          appended = True
        elif bspec == '||':
          bbefore.append('│' + self.nregs["text-cell-padding-left"]) # box drawings light vertical \u2502
          appended = True
        elif bspec == "=":
          bbefore.append('║' + self.nregs["text-cell-padding-left"]) # box drawings double vertical \u2551
          appended = True
        elif bspec == "==":
          bbefore.append('║' + self.nregs["text-cell-padding-left"]) # box drawings double vertical \u2551
          appended = True
        elif not bspec:
          pass
        else:
          self.warn_w_context("Unrecognized cell border specification character(s): {}".format(bspec), self.cl)
      if not appended: # if no before border appended
        if len(bbefore) == 0: # assume all columns but first have a blank left border
          bbefore.append('')
        else:
          bbefore.append(' ')

      appended = False
      m = re.match(r"([^|=]+)([|=]*)", u[1]) # extract border-after character(s)
      if m:
        u[1] = m.group(1)
        bspec = m.group(2)
        if bspec and self.renc == "l": # ignore borders if Latin-1 output
          self.warn("Table borders ignored for Latin-1 output.")
        elif bspec == '|':
          bafter.append(self.nregs["text-cell-padding-right"] + '│') # box drawings light vertical \u2502
          appended = True
        elif bspec == '||':
          bafter.append(self.nregs["text-cell-padding-right"] + '│') # box drawings light vertical \u2502
          appended = True
        elif bspec == "=":
          bafter.append(self.nregs["text-cell-padding-right"] + '║') # box drawings double vertical \u2551
          appended = True
        elif bspec == "==":
          bafter.append(self.nregs["text-cell-padding-right"] + '║') # box drawings double vertical \u2551
          appended = True
        elif not bspec:
          pass
        else:
          self.warn_w_context("Unrecognized cell border specification character(s): {}".format(bspec), self.cl)
      if not appended: # if no after border appended
        bafter.append('') # assume null right border if none specified

      if u[0][0] == 'l':
        haligns.append('<')
      elif u[0][0] == 'c':
        haligns.append('^')
      elif u[0][0] == 'r':
        haligns.append('>')
      elif u[0][0] == 'h':
        haligns.append('h') # will use < later for actual formatting of the cell/row
      else:
        self.fatal("table horizontal alignment must be 'l', 'c', 'h', or 'r' in {}".format(self.wb[self.cl]))

      valigns.append(u[0][1])  # ['t', 't']
      try:
        widths.append(int(u[1]))  # ['6', '22']
        totalwidth += int(u[1])   #
      except ValueError:
        self.fatal("cell width {} is not numeric: {}".format(u[1], self.wb[self.cl]))
      j += 1

    # figure out amount borders add to total width, ensuring we don't double inner border space when
    # both are blank
    totalwidth += len(bbefore[0]) # always add in left border for first column
    for i in range(1, len(bbefore)):
      totalwidth += len(bafter[i - 1]) # add in right border of previous column, if any
      if bafter[i - 1] and (bbefore[i] == ' '): # nullify blank left border following a right border
        bbefore[i] = ''
      totalwidth += len(bbefore[i]) # add in left border if it survived
    totalwidth += len(bafter[-1]) # add in right border of rightmost column

    #self.dprint("doTable (text), total table width not including indent: {}".format(totalwidth))

    # margin to center table in 72 character text field
    if totalwidth >= 72:
      tindent = 0 # a 1-space indent will be added later for this case
      if not autosize:
        self.warn("PPer-supplied table width (including leading indent and space\n" + "           " +
                  "between columns) of {} is greater than 72 characters:\n           {}".format(totalwidth+1, self.wb[self.cl]))
    else:
      tindent = (72 - totalwidth) // 2
    rindent = max(tindent, 1) # position of first rule character in line if using horizontal rules
    #self.dprint("doTable (text), table indent: {}".format(tindent))

    self.eb.append(".RS 1")  # request blank line above table

    self.cl += 1 # move into the table rows
    #self.twrap = textwrap.TextWrapper()

    # if any cell wraps, put a vertical gap between rows
    # except for cases where the PPer supplies a blank line or a horizontal border or specified bl=n
    rowspace = False
    k1 = self.cl
    while add_blank_lines and self.wb[k1] != ".ta-" and not rowspace:

      # lines that we don't check: centered or blank (or .bn info)
      if empty.match(self.wb[k1]) or not "|" in self.wb[k1]:
        k1 += 1
        continue

      t = self.wb[k1].split("|")
      if len(t) != ncols:
        self.crash_w_context("table has wrong number of columns:{}".format(self.wb[k1]), k1)
      for i in range(0,ncols):
        t1 = t[i].strip()
        if len(t1) >= 4 and t1[0:4] == "<th>": # if <th> at start of cell remove it
          t1 = t1[4:]
        if len(t1) >= 6 and t1[0:4] == "<al=":
          t1 = re.sub(r"^<al=[lrch]>", "", t1, 1) # ignore any alignment directives
        if t1.strip() != "<span>":
          w1 = widths[i]
          for j in range(i+1, ncols):
            if t[j].strip() == "<span>":
              w1 += widths[j]
            else:
              break
          if self.truelen(t1) > w1:
            k2 = self.wrap_para(t1, 0, w1, 0, warn=True) # should handle combining characters properly
            if len(k2) > 1:
              rowspace = True
      k1 += 1

    # process each row of table
    hrules = list() # keep track of horizontal rules the PPer generates (by line number in self.eb)
    table_start = len(self.eb)
    while self.wb[self.cl] != ".ta-":

      # horizontal border
      # Signified by _ for a single line or = for a double line
      if len(self.wb[self.cl]) < 3 and self.wb[self.cl] in self.valid_text_hrules:
        if self.renc == "l":
          self.warn("Table borders ignored for Latin-1 output.")
        else:
          hrules.append(len(self.eb)) # remember this line number for fixup later
          self.eb.append((rindent * ' ') + (totalwidth * self.valid_text_hrules[self.wb[self.cl]]))
        self.cl += 1
        continue

      # blank line
      # an empty line in source generates a one char vertical gap
      if empty.match(self.wb[self.cl]):
        self.eb.append("")
        self.cl += 1
        continue

      # .bn info line
      if self.bnPresent and self.is_bn_line(self.wb[self.cl]):
        self.eb.append(self.wb[self.cl])   # copy the .bn info into the table (deleted much later during postprocessing)
        self.cl += 1
        continue

      # "centered" line
      # a line in source that has no vertical pipe
      # (Note: Honors <al=r/l> if specified.)
      if not "|" in self.wb[self.cl]:
        line = self.wb[self.cl].strip()
        if len(line) >= 4 and line[0:4] == "<th>": # remove any <th> from front of cell
          line = line[4:]
        if len(line) >= 6 and line[0:4] == "<al=":
          m = re.match(r"^<al=([lrch])>", line) # pick up possible alignment directive
          if m:
            if m.group(1) == "l":
              align = "<"
            elif m.group(1) == "r":
              align = ">"
            elif m.group(1) == "c":
              align = "^"
            elif m.group(1) == "h":
              align = "^"
              self.warn_w_context("<al=h> not supported for centered table lines",self.cl)
            line = line[6:] # remove the alignment tag
        else:
          align = "^"
        #fmtstring = "{:" + align + "72}"
        fmtstring = "{:" + align + "{}".format(totalwidth) + "}"
        if tindent == 0:
          s = " " # ensure at least one leading space
        else:
          s = " " * tindent  # indentation to center the line with the table
        if self.truelen(line) <= totalwidth:
          self.eb.append(s + self.truefmt(fmtstring, line))
        else:
          self.warn("Wrapping long line in table: {}".format(line))
          t = self.wrap_para(line, 0, totalwidth, 0, warn=True)
          for line in t:
            self.eb.append(s + self.truefmt(fmtstring, line))
        self.cl += 1
        continue

      # split the text into columns
      t = self.wb[self.cl].split("|")
      if len(t) != ncols:
        self.crash_w_context("table has wrong number of columns:{}".format(self.wb[self.cl]), self.cl)

      maxheight = 0
      w = [None] * ncols  # a list of lists for this row
      heights = [None] * ncols  # lines in each cell
      caligns = haligns[:] # copy standard alignment into cell override list
      for i in range(0,ncols):
        cell_text = t[i].strip()
        if len(cell_text) >= 4 and cell_text[0:4] == "<th>":
          cell_text = cell_text[4:]
        if len(cell_text) >= 6 and cell_text[0:4] == "<al=":
          m = re.match(r"^<al=([lrch])>", cell_text) # pick up possible alignment directive
          if m:
            if m.group(1) == "l":
              caligns[i] = "<"
            elif m.group(1) == "r":
              caligns[i] = ">"
            elif m.group(1) == "c":
              caligns[i]= "^"
            else:
              caligns[i] = "h"
            cell_text = cell_text[6:] # remove the alignment tag
        w1 = widths[i]
        for j in range(i+1, ncols):
          if t[j].strip() == "<span>":
            w1 += widths[j] + len(bafter[j-1]) + len(bbefore[j]) # account for space between columns
          else:
            break
         # don't bother wrapping a <span> column or one whose naive length is short enough to fit, unless
         # if contains a <br>
        if (cell_text == "<span>" or self.truelen(cell_text) < w1) and (cell_text.find("<br>") == -1):
          w[i] = [cell_text]
        elif caligns[i] != 'h': # if not hanging indent, wrap normally
          w[i] = self.wrap_para(cell_text, 0, w1, 0, warn=True) # should handle combining characters properly
        else: # use a 2-character indent, -2 ti if hanging indent
          w[i] = self.wrap_para(cell_text, 2, w1, -2, warn=True)
        if caligns[i] == "h":
          caligns[i] = "<"
        for j,line in enumerate(w[i]):
          w[i][j] = line.rstrip()  # marginal whitespace (only remove spaces at ends of lines)
        heights[i] = len(w[i])
        maxheight = max(maxheight, heights[i])

      # make all columns same height
      for i in range(0,ncols):
        if len(w[i]) < maxheight: # need to add blank lines in this cell
          if not valigns[i] in ['t','b','m']:
            self.fatal("table vertial alignment must be 't', 'b', or 'm'")
          if valigns[i] == 't' or w[i][0].strip() == "<span>": # force <span> to top of cell to make it easier to recognize and remove
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
          w1 = widths[col]
          temp_bafter = -1
          for j in range(col+1, ncols):
            if w[j][0].strip() == "<span>":
              w1 += widths[j] + len(bafter[j-1]) + len(bbefore[j]) # account for space between columns
              temp_bafter = bafter[j]
            else:
              break
          fmt = "{" + ":{}{}".format(caligns[col], w1) + "}"
          line = w[col][g]
          if w[col][0] != "<span>":
            s += bbefore[col]
            s += self.truefmt(fmt, line)
            if temp_bafter != -1:
              s += temp_bafter
            else:
              s += bafter[col]
        self.eb.append(s)
      j = self.cl + 1
      # find next line that is not a .bn line (could theoretically have multiple sequential .bn lines)
      nextline = ""
      done = False
      while j < len(self.wb) and not done:
        nextline = self.wb[j]
        if (self.bnPresent and self.is_bn_line(nextline)):
          j += 1
        else:
          done = True
      nextline = nextline.replace("<span>", "") # recognize the special case of a blank line
      nextline = nextline.replace("|", "")      # which has the form  | <span> | <span>
      nextline = nextline.strip()
      if (not nextline.startswith(".ta-") and # if not end of table and
          rowspace and # cells are multi-line and
          nextline and # next line is non-blank and
          not hrules): # and there are no horizontal rules
        self.eb.append("")

      self.cl += 1  # go to next row in table

    # Fixup horizontal rules, if any, adding corners and joining the verticals
    # p = previous self.eb line number in table, or -1
    # n = next self.eb line number in table, or -1
    # r = self.eb line number of this horizontal rule

    for i, r in enumerate(hrules):
      p = r - 1 if (i > 0 or r > table_start) else -1
      n = r + 1 if (r < len(self.eb) - 1) else -1

      # Deal with encoded .bn lines, which are shorter than other table lines and
      # not indented (for centering) as they are. We must totally ignore such
      # lines and reset p and n to pretend they are not present as needed.
      if self.bnPresent:
        while p != -1 and self.is_bn_line(self.eb[p]):
          p = p - 1 if (p > 0) else -1
        while n != -1 and self.is_bn_line(self.eb[n]):
          n = n + 1 if (n < len(self.eb) - 1) else -1

      # handle top rule
      if p == -1 and n != -1:
        #key = 'ludr'
        kl = '*' # no left to begin with
        ku = '*' # no up at all for this row
        line = rindent * ' '
        temp = self.eb[r][rindent]
        temp_linen = self.expand_supsub(self.eb[n])
        for l in range(rindent, len(self.eb[r])):
          kd = temp_linen[l]  if (l < self.truelen(temp_linen)) else '*' # down character
          if kd not in '│┃║':
            kd = '*'
          kr = self.eb[r][l + 1] if (l < len(self.eb[r]) - 1) else '*' # right character, or *
          key = kl + ku + kd + kr
          if kd + ku != '**':
            line += self.hrule_text_dict[key] # lookup replacement character
          else:
            line += temp
          kl = temp # set next "left" character from remembered first character of the rule
        self.eb[r] = line

      # handle a middle rule
      elif p != -1 and n != -1:
        #key = 'ludr'
        kl = '*' # no left to begin with
        line = rindent * ' '
        temp = self.eb[r][rindent]
        temp_linen = self.expand_supsub(self.eb[n])
        temp_linep = self.expand_supsub(self.eb[p])
        for l in range(rindent, len(self.eb[r])):
          ku = temp_linep[l] if (l < self.truelen(temp_linep)) else '*' # up character
          if ku not in '│┃║':
            ku = '*'
          kd = temp_linen[l] if (l < self.truelen(temp_linen)) else '*' # down character
          if kd not in '│┃║':
            kd = '*'
          kr = self.eb[r][l + 1] if (l < len(self.eb[r]) - 1) else '*' # right character, or *
          key = kl + ku + kd + kr
          if kd + ku != '**':
            line += self.hrule_text_dict[key] # lookup replacement character
          else:
            line += temp
          kl = temp # set next "left" character from remembered first character of rule
        self.eb[r] = line

      # handle last rule
      elif p != -1 and n == -1:
        #key = 'ludr'
        kl = '*' # no left to begin with
        kd = '*' # no down at all for this row
        line = rindent * ' '
        temp = self.eb[r][rindent]
        temp_linep = self.expand_supsub(self.eb[p])
        for l in range(rindent, len(self.eb[r])):
          ku = temp_linep[l]  if (l < self.truelen(temp_linep)) else '*' # up character
          if ku not in '│┃║':
            ku = '*'
          kr = self.eb[r][l + 1] if (l < len(self.eb[r]) - 1) else '*' # right character, or *
          key = kl + ku + kd + kr
          if kd + ku != '**':
            line += self.hrule_text_dict[key] # lookup replacement character
          else:
            line += temp
          kl = temp # set next "left" character from remembered character

        # replace horizontal border with modified rule
        self.eb[r] = line

    self.eb.append(".RS c")  # request blank line below table (special flag for .ul/.ol/.it processing)
    self.cl += 1  # move past .ta-

  def doDropimage(self):
    del self.wb[self.cl] # ignore the directive in text

  def doDropcap(self, line): # line is always self.cl in text version
    del self.wb[line] # ignore the directive in text

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
      t1 = self.regLL - self.regIN
      xs = "{:>" + str(t1) + "}"
      while nlines > 0:
        line = self.wb[self.cl].strip()
        self.eb.append(" " * self.regIN + self.truefmt(xs, line))
        self.cl += 1
        nlines -= 1
      self.eb.append(".RS 1")
    else:
      self.crash_w_context("malformed .rj directive", self.cl)

  # .de CSS definition
  # ignore the directive in text
  def doDef(self):
    while (self.cl < len(self.wb) - 1) and self.wb[self.cl].endswith("\\"): # this version of continuation still needed
                                                                            # as it behaves differently from others.
      del self.wb[self.cl] # multiple line
    if not self.wb[self.cl].endswith("\\"):
      del self.wb[self.cl] # last or single line
    else:
      self.fatal("source file ends with continued .de command: {}".format(self.wb[self.cl]))

  def doSidenote(self):
    # handle sidenotes outside paragraphs, sidenotes inside paragraphs are handled as <sn>-style markup
    self.snPresent = True
    m = re.match(r"\.sn (.*)", self.wb[self.cl])
    if m:
      self.eb.append(".RS 1") # request at least one space in text before sidenote
      t = m.group(1).split("|") # split the sidenote on | characters, if any
      t[0] = t[0].strip()
      header_len = len(self.nregs["Sidenote"]) + 3
      for i in range(1, len(t)): # offset subsequent lines of the sidenote for alignment with first line of sidenote text
          t[i] = (' ' * header_len + t[i].strip()).rstrip()
      if len(t) > 1: # handle a multi-line sidenote
        self.eb.append("[{}: {}".format(self.nregs["Sidenote"], t[0]))
        t[-1] += "]"
        self.eb.extend(t[1:])
      else: # single, possibly long, sidenote
        self.eb.extend(self.wrap_para("[{}: {}]".format(self.nregs["Sidenote"], t[0]), # string to wrap
                                      header_len, # indent
                                      self.regLL, # line length
                                      (0 - header_len))) # ti
      self.eb.append(".RS 1") # request at least one space in text after sidenote
      self.cl += 1
    else:
      self.crash_w_context("malformed .sn directive", self.cl) # should never hit this as preprocesscommon() checked it

  # Index processing (Text)
  ### To do: ensure that text and HTML output is compatible. Also, text form ignoring blank lines? Should it include 1
  ###   between major entries? Should that be a .ix option?)
  def doIx(self):
    indent = self.regIN if (self.regIN) else 1 # ensure indented at least 1 space
    self.eb.append(".RS 1")
    regBW = min(self.calculateBW(".ix-"), self.regLL)
    i = self.cl + 1 # skip the .ix
    while self.wb[i] != ".ix-": # calculateBW will have complained if .ix- is missing

      if self.bnPresent and self.is_bn_line(self.wb[i]):   # just copy .bn info lines, don't change them at all
        self.eb.append(self.wb[i])
        i += 1
        continue

      s = (" " * indent + self.wb[i])
      # if the line is shorter than the line length just send it to emit buffer
      # if longer, calculate the leading spaces on line and use as shift amount during
      # wrapping
      if self.truelen(self.squashBlanks(s)[0]) > self.regLL:
        wi = 0
        m = re.match("^(\s+)(.*)", s)
        if m:
          wi = len(m.group(1))
          s = m.group(2)
        u = self.wrap(s, wi+3, self.regLL, -3, optimal_needed=False)
        for line in u:
          self.eb.append(line)
      else:
        self.eb.append(self.squashBlanks(s)[0])
      i += 1
    self.eb.append(".RS 1")
    self.cl = i + 1 # skip the closing .ix-

  # Process a paragraph (Text)
  def doPara(self):
    t = []
    bnt = []
    pstart = self.cl
    if self.regTIp != 0: # if persistent temporary indent in effect, pretend we got a .ti directive
      self.regTI = self.regTIp

    # grab the paragraph from the source file into t[]
    # note: we will transform encoded sidenote information within the paragraph into
    # its final format here, as it will affect wrapping. This differs from the handling
    # for HTML where it is handled during post-processing, as our HTML processing for
    # paragraphs does not wrap the text, leaving that to the browser or other rendering engine.
    j = pstart
    while (j < len(self.wb) and
           self.wb[j]): # any blank line or dot directive ends paragraph
      if self.wb[j].startswith("."):
        m = re.match(r"\.[a-z]", self.wb[j])
        if m:
          break
      t.append(self.wb[j])
      j += 1
    pend = j
    s = " ".join(t) # one long string for the paragraph
    textInPara = True
    if self.bnPresent:
      bnInPara = False
      m=re.match(".*⑱.*?⑱.*",s)                # any bn info in this paragraph?
      if m:                                                         # if yes, make sure there are no blanks after it and
        bnInPara = True                                 # see if there's any real text
        # this seems like a long way to do it, rather than using re.sub, but
        # I had some odd problems trying to use re.sub as I couldn't get \1
        # to substitute back in properly. So I loop using re.match instead.
        m = re.match("(.*?)(⑱.*?⑱) (.*)",s)
        while m:
          s = m.group(1) + m.group(2) + m.group(3)
          m = re.match("(.*?)(⑱.*?⑱) (.*)",s)
        if s.endswith("⑱"):                      # if there's .bn info at end of s remove any blank preceding it
          m = re.match("^(.*) (⑱.*?⑱)$",s)
          if m:
            s = m.group(1) + m.group(2)
        stemp = re.sub("⑱.*?⑱", "", s) #  make copy of s with bn info removed
        if stemp == "":                              # if it was all bn info, note that there's no text to wrap.
          textInPara = False
    if textInPara:  # only wrap and add blank lines if there was actual text in the paragraph
      u = self.wrap(s, self.regIN, self.regLL, self.regTI)
      self.regTI = 0 # reset any temporary indent
      # set paragraph spacing
      u.insert(0, ".RS 1") # before
      u.append(".RS c") # after (special flag for .ul/.ol/.it processing)
      self.eb += u
    elif bnInPara:
      bnt.append(s)
      self.eb += bnt     # if only .bn info, append it.
    else:
      self.crash_w_context("Unexpected problem with .bn info",pstart)
    self.cl = pend

  # Unordered List (Text)
  # .ul options
  #    or
  # .ul-
  #
  # options:
  #   style="disc | circle | square | none" (default: disc)
  #   indent="2" (indent is to the marker.)
  #   hang=n (default) or y
  #   space=n (default) or y
  #   id=<id-value> (ignored in text)
  #   class=<class-value> (ignored in text)
  #
  def doUl(self):

    (startUl, li_active, indent, id, clss) = self.doUlCommon()  # id, clss ignored for text

    if not startUl: # end of unordered list
      self.eb.append(".RS 1")

    else:     # beginning an unordered list

      if indent != -1: # indent specified
        if indent==0 and self.regIN == 0:
          indent = 1 # must indent a list by at least 1 space in text
        self.regIN += int(indent) # indent specified is to marker; regIN is to text, not marker
        if self.list_item_style != "none":
          self.regIN += 2
        if self.regIN == 0:
          self.regIN += 1 # must indent a list by at least 1 space in text

      else: # indent not specified
        #if len(self.liststack) > 1: # nested?
        #  self.regIN += self.list_item_width # indent to new text position
        #elif self.list_item_style != "none":
        #  self.regIN += 2 # if no indent specified, indent text by 2 (marker + space)
        #else:
        #  pass # don't adjust indent if no indent specified and style = none
        if self.regIN == 0:
          self.regIN += 1 # must indent a list by at least 1 space in text
        temp_indent = self.outerwidth if (len(self.liststack) > 1) else 0
        if self.list_item_style != "none":
          temp_indent += 2
        self.regIN += temp_indent

    self.cl += 1


  # Ordered List (Text)
  # .ol options
  #   or
  # .ol-
  #
  # options: (default values shown)
  #   style="decimal | lower-alpha | lower-roman | upper-alpha | upper-roman" (default: decimal)
  #   w="2" (number of digits allowed in the item number)
  #   indent="2" (indent to the item number.)
  #   hang=n (default) or y
  #   space=n (default) or y
  #   id=<id-value> (ignored in text)
  #   class=<class-value> (ignored in text)
  #
  # note: to match HTML, separator is always "."
  #
  def doOl(self):

    (startOl, li_active, indent, id, clss) = self.doOlCommon() # id, clss ignored for text

    if not startOl:  # end of ordered list
      self.eb.append(".RS 1")

    else:            # beginning an ordered list

      if indent != -1:
        self.regIN = int(indent) + self.list_item_width # indent specified is to marker; regIN is to text, not marker
        #self.regIN += int(indent)
        if self.regIN == 0:
          self.regIN += 1 # must indent a list by at least 1 space in text

      else:
        #if len(self.liststack) > 1: # nested? ### need to adjust this
        #  self.regIN += self.list_item_width # indent to new text position
        #else:
        #  self.regIN = self.list_item_width if (self.regIN) else self.list_item_width + 1 # ensure a leading blank
        temp_indent = self.outerwidth if (len(self.liststack) > 1) else 0
        self.regIN += temp_indent + self.list_item_width

    self.cl += 1

  # List item (Text)
  def doIt(self):
    self.doItCommon()

    self.list_item_active = True
    indent = self.regIN
    #if self.list_item_style == "none":
    #  indent += 2

    # Calculate amount of hanging indent. By default, -1 * self.list_item_width means that if an item wraps it
    # will look like this:
    #    1. Here is the first part of the item and
    #       it continues directly under the first part.
    # However, if hang=y is specified on .ol/.ul then it will look like this:
    #    1. Here is the first part of the item and
    #         it continues with a further indent.
    # Note that this can be more important with .ul with style=none to avoid confusion:
    #    Here is the first part of the item and
    #    it continues directly under the first part.
    #    Here is the second item
    # vs
    #    Here is the first part of the item and
    #      it continues with a further indent
    #    Here is the second item
    hang = -1 * self.list_item_width # needed for wrapping marker + text
    if self.list_hang: # additional needed
      hang   -= 2
      indent += 2

    # determine content of marker and build it
    if self.list_type == "o":
      value = self.list_item_style[1]()
      fmt = "{:>" if (self.list_align == "r") else "{:<"
      fmt += "{}".format(self.list_item_width - 1) + "}"
      l = fmt.format(str(value) + ".") + " "
    else:
      l = (self.list_styles_u[self.list_item_style] + " ") if (self.list_item_style != "none") else ""

    # layout the text after the marker, wrap if needed, and append to output buffer
    l += self.wb[self.cl][4:].strip()
    t = self.wrap(l, indent, self.regLL, hang)
    self.eb += t

    # add a blank line after the item if we're spacing this list
    if self.list_space:
      self.eb.append(".RS 1")

    self.cl += 1

  # Definition List (Text)
  # Note: doDl operates differently from most other dot commands. It creates a definition list object that will
  #       be in control of processing until the matching .dl- is encountered. All lines up to the .dl will be
  #       processed either directly by the object or if they are another dot directive
  #       their processing routine will be invoked indirectly by the object.
  #
  #       doDl will define its own subclass of the definition list object to tailor the processing for what is
  #       needed in Ppt.
  def doDl(self):

    class PptDefList(Book.DefList):

      # "Print" debugging info (place it into the output text) if requested
      def print_debug(self, info): # Ppt and Pph will override this
        b = self.book
        b.eb += info


      # Routine to bump the current line pointer
      # (Called by code in base DefList class)
      def bump_cl(self):
        self.book.cl += 1

      # Routine to handle special lines (.bn info)
      # (called by code in base DefList class)
      def emit_special(self, bninfo):

        b = self.book

        # bninfo is purely passthrough for the text phase
        if bninfo:
          b.eb.append(bninfo)

      # Emit a paragraph of definition/dialog for the case where style=paragraph
      # (overrides method in DefList)
      def emit_paragraph(self):
        b = self.book

        # wrap the definition paragraph as needed
        #
        indent_first = self.options["tindent"] + b.list_item_width + 1 + self.options["dindent"]
        wraplen = b.regLL - b.regIN

        if self.options["collapse"]: # if collapsing need to temporarily pad first line to account for term
          indent_chars = "~" * indent_first
          s = indent_chars + self.paragraph
        else:
          s = self.paragraph
          wraplen -= indent_first # if not collapsing, need to reduce wrap width by indent width

        if self.options["hang"]:
          ti = -2
          indent = 2
        else:
          ti = 0
          indent = 0

        # wrap parameters: s,  indent=0, ll=72, ti=0, optimal_needed=True
        t = b.wrap(s, indent, wraplen, ti)

        if self.options["collapse"]: # if collapsing need to remove temporary pad from first line
          t[0] = t[0][indent_first:]

        # layout the term and definition line(s)

        s = []

        # handle alignment of term
        l = b.truelen(self.term)

        if l >= b.list_item_width:
          ltrm = self.term + " " # just pad with a blank (as separator) if the term is full-width or longer

        # else term is narrow, so align to the left or right as requested
        elif self.options["align"] == "l": # if aligning narrow term to the left of its block
          ltrm = self.term + " " * (b.list_item_width - l + 1)
        else: # aligning narrow term to the right of its block
          ltrm = " " * (b.list_item_width - l) + self.term + " "

        if self.options["float"]:
          #if self.term:
          blanks = (self.options["dindent"]) * " "

          s.append(".RS 1")
          s.append(self.indent_padding + (self.options["tindent"] * " ") + ltrm + blanks + t[0].rstrip())

        else:                 # non-floated style (first line is term, if we have one)
          s.append(".RS 1")
          if self.term:
            s.append(self.indent_padding + (self.options["tindent"] * " ") + ltrm)

          l = t[0].rstrip()
          if l: # avoid adding another blank line
            s.append(self.indent_padding + self.definition_padding + t[0].rstrip())

        if not self.options["collapse"]:
          for i in range(1, len(t)):    # handle remaining lines
            s.append(self.indent_padding + (self.options["tindent"] * " ") + self.definition_padding + t[i].rstrip())
        else:
          for i in range(1, len(t)):    # handle remaining lines
            s.append(self.indent_padding + self.dindent_padding + t[i].rstrip())

        # append definition line(s) to output
        ### could simplify this and append directly to self.eb above, instead of appending to s as an intermediate
        b.eb += s

        self.term = ""
        self.paragraph = ""

      # start the definition list
      # (overrides method in DefList)
      def begin_dl(self):
        b = self.book
        self.dlstart = b.cl
        self.dlbuffer = [] # we don't use this in text processing, but it must be defined

        # We need to ensure an indent of at least 1 if we're not combining lines, to avoid problems with potential
        # future rewrapping outside of DP's control (like for .nf, .ta, etc.)
        if b.regIN == 0 and self.options["style"] != "p":
          b.regIN = 1 # note: prior value saved on stack by doDlCommon, will be restored when handling .dl-

        self.indent_padding = b.regIN * " "
        self.definition_padding = (self.options["width"] + 1 + self.options["tindent"]) * " "
        self.dindent_padding = self.options["dindent"] * " " # additional amount to indent collapsed definition lines

      # Emit a blank line when necessary
      # (overrides method in DefList)
      def add_blank(self):
        self.book.eb.append(" ") # emit any blank lines after the first one in a group

      # Ignore class= on .dd directive
      def set_dd_class(self, clss):
        pass

      # wrap a definition line as needed (Note: non-combining mode)
      # (overrides method in DefList)
      def wrap_def(self):
        b = self.book
        indent_first = self.options["tindent"] + b.list_item_width + 1 # + dindent?
        wraplen = b.regLL - b.regIN
        if not self.options["collapse"]:
          wraplen -= indent_first
        else:
          wraplen -= self.options["dindent"]

        if self.options["collapse"]:
          if self.options["hang"]: ### does this need to differ depending on whether term has data?
            windent = self.options["dindent"] + 2
            wti = -2
          else:
            windent = self.options["dindent"]
            wti = 0
        else:
          if self.options["hang"]:
            windent = 2
            wti = -2
          else:
            windent = 0
            wti = 0

        # wrap parameters: s,  indent=0, ll=72, ti=0, optimal_needed=True
        if not self.options["collapse"]:
          t = b.wrap(self.definition, windent, wraplen, wti) # not collapse, either float or not float

        elif self.options["float"]: # collapse, float
          t = b.wrap(self.definition, windent, wraplen, indent_first)
          t[0] = t[0][indent_first:]

        else: # collapse, not float
          if self.options["hang"]:
            t = b.wrap(self.definition, windent, wraplen, wti)
          else:
            t = b.wrap(self.definition, windent, wraplen, 0)

        self.definition = t

      # Layout term and definition (non-combining)
      # (Overrides method in DefList)
      def layout(self):
        b = self.book
        ### screwed up? need to figure out how indents work with wrapping
        s = []
        l = b.truelen(self.term)

        if l >= b.list_item_width:
          ltrm = self.term + " " # just pad with a blank (as separator) if the term is full-width or longer

        # else term is narrow, so align to the left or right as requested
        elif self.options["align"] == "l": # if aligning narrow term to the left of its block
          ltrm = self.term + " " * (b.list_item_width - l + 1)
        else: # aligning narrow term to the right of its block
          ltrm = " " * (b.list_item_width - l) + self.term + " "

        t = self.definition
        if self.options["float"]:  # floated style (first line is term + 1st line of definition)
          s.append(".RS 1") # want a blank line between entries
          if self.term or not self.form_c:
            s.append(self.indent_padding + (self.options["tindent"] * " ") + ltrm + t[0].rstrip())
          else: # no term, or form c
            if t[0].strip(): # if we have a definition
              if not self.options["collapse"]:
                s.append(self.indent_padding + self.definition_padding + t[0].rstrip())
              else: # collapse
                s.append(self.indent_padding + self.dindent_padding + t[0].rstrip())
          start = 1

        else:                 # non-floated style (first line is term, if we have one)
          s.append(".RS 1")   # want blank line between entries
          if ltrm.strip(): # if term is non-blank add it (but avoid adding another blank line)
            s.append(self.indent_padding + (self.options["tindent"] * " ") + ltrm)
          start = 0

        if not self.options["collapse"]:
          for i in range(start, len(t)):    # handle remaining lines, starting from t[0] (nofloat) or t[1] (float)
            if t[i].strip(): # avoid blank lines
              s.append(self.indent_padding + (self.options["tindent"] * " ") + self.definition_padding + t[i])
        else:
          for i in range(start, len(t)):    # handle remaining lines, starting from t[0] (nofloat) or t[1] (float)
            if t[i].strip(): # avoid blank lines
              s.append(self.indent_padding + t[i])
        self.defbuffer = s
        self.definition = ""

      # Emit a term/definition (non-combining)
      # (Overrides method in DefList)
      def emit_def(self):
        # append definition line(s) to output
        self.book.eb += self.defbuffer

      # Finalize Dl
      # (Overrides method in DefList)
      def finalize_dl(self):
        self.book.eb.append(".RS 1")

    # main processing for doDl (Text):

    dlobj = PptDefList(self) # create the object
    dlobj.run()              # turn over control


  # Main processing routine for text
  def process(self):
    self.keepFnHere = False
    self.cl = 0
    while self.cl < len(self.wb):
      if "a" in self.debug:
        s = self.wb[self.cl]
        self.print_msg( s )  # print the current line
      if not self.wb[self.cl]: # skip blank lines
        self.cl += 1
        continue

      # don't turn standalone .bn info lines into paragraphs
      if self.bnPresent and self.is_bn_line(self.wb[self.cl]):
        self.eb.append(self.wb[self.cl])
        self.cl += 1
        continue

      # will hit either a dot directive or wrappable text
      if re.match(r"\.[a-z]", self.wb[self.cl]): # don't need check for .⓭DV- here; it's never in text
        self.doDot()
        continue
      self.doPara()

    if len(self.fnlist):  # any saved footnotes that didn't have a .fm to generate them?
      self.warn("Footnotes encountered after last \".fm lz=t\" have not been generated. Missing a .fm somewhere?")

  def run(self): # Text
    self.loadFile(self.srcfile)

    if self.srcbin: # if user just wants a -src.txt.bin file created
      self.createsbin() # go create it (and exit)

    # requested encoding is UTF-8 but file is latin1only
    if self.renc == 'u' and self.latin1only == True and not self.forceutf8 and not self.cvgfilter:
      return # do not make UTF-8 text file
    # file is ASCII->Latin_1 but trying to run as UTF-8
    if self.encoding == "latin_1" and self.renc == 'u' and not self.forceutf8 and not self.cvgfilter:
      return # do not make UTF-8 text file

    if self.renc == "l":
      self.print_msg("creating Latin-1 text file")
    if self.renc == "u":
      self.print_msg("creating UTF-8 text file")

    self.preprocess()
    self.process()
    self.postprocess()

    if self.renc == "l":
      self.saveLat1(self.outfile), # LATIN-1
    if self.renc == "u":
      self.saveFileU(self.outfile) # UTF-8

# ====== pph ============================================================================

class Pph(Book):

  pvs = 0 # pending vertical space
  fsz = "100%" # font size for paragraphs
  pdc = "" # pending drop cap
  igc = 1 # illustration geometry counter
  fnlist = [] # list of footnotes
  imageCssDict = {} # list of css specifications for illustrations, with the number that defined them.
  dl_classnum = 0 # used to generate unique class names for .dl with unique characteristics
  dl_dict = {} # initialize dictionary to track unique .dl characteristics
  ul_classnum = 0 # same for ul and ol
  ul_dict = {}
  ol_classnum = 0
  ol_dict = {}
  table_list = []

  booktype = "html"

  def __init__(self, args, renc, config, sout, serr):
    Book.__init__(self, args, renc, config, sout, serr)
    if self.listcvg:
      self.cvglist()
    self.dstfile = re.sub("-src", "", self.srcfile.split('.')[0]) + ".html"
    self.css = self.userCSS()
    self.linkinfo = self.linkMsgs()
    self.imageCheck = args.imagecheck
    self.musicCheck = args.musiccheck

  # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  # internal class to manage CSS as it is added at runtime
  class userCSS(object):
    def __init__(self):
      self.cssline = {}

    def addcss(self, s):
      if s.endswith("}"):
        s = s[:-1].rstrip() + " }"
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

    def showde(self): # return only the CSS created by the PPer using .de
      t = []
      keys = list(self.cssline.keys())
      keys.sort()
      for s in keys:
        if s >= "[3000]":
          t.append(s[6:])
      return t

  # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  # internal class to manage link-check error/warning messages
  class linkMsgs(object):
    def __init__(self):
      self.linkmsg = {}

    def add(self, s):
      if s in self.linkmsg:
        self.linkmsg[s] += 1
      else:
        self.linkmsg[s] = 1

    def show(self):
      t = []
      keys = list(self.linkmsg.keys())
      keys.sort()
      for s in keys:
        t.append("  " + s[3:])
      return t


  # -------------------------------------------------------------------------------------
  # utility methods

  # print if debug includes 'd'
  def dprint(self, msg):
    if 'd' in self.debug:
      self.print_msg("{}: {}".format(self.__class__.__name__, msg))

  # bailout after saving working buffer in bailout.txt
  def bailout(self, buffer):
    f1 = codecs.open("bailout.txt", "w", encoding='utf-8')
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
      self.css.addcss("[{}] .c{:03d} {{ {} }}".format(2000+i, i, line))
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
        self.wb[i] = re.sub("\s\s*", " ", self.wb[i]) # courtesy whitespace cleanup
    # fix FF problem with interaction between pageno and drop-caps
    i = 0
    while i < len(self.wb):
      m = re.search("(.*?)(<p class='drop-capa.*>)(<span class='pageno'.*?>.*?</span>)(.*)$", self.wb[i])  # look for drop-cap HTML before pageno HTML
      ### replicate for div for .nf blocks?
      if m:
        t = []
        if m.group(1):
          t.append(m.group(1))
        t.append(m.group(3))      # move the pageno span to before the drop-cap paragraph (it will end up in its own div)
        t.append(m.group(2))
        if m.group(4):
          t.append(m.group(4))
        self.wb[i:i+1] = t
        i += len(t)
      i += 1

  # -------------------------------------------------------------------------------------
  # preprocess working buffer (HTML)
  def preprocess(self):

    def fnDupCheck(name):
      string = r"\[{}\]".format(name)
      if name in fnlist:
        # it's a duplicate forward reference
        self.warn("duplicate footnote reference: [{}]".format(name))
        self.wb[i] = re.sub(string, \
        "⑪a href='⑦f{0}' style='text-decoration: none; '⑫⑪sup⑫⑬{0}⑭⑪/sup⑫⑪/a⑫".format(name), \
        self.wb[i], 1)
      else:
        # it's the first reference
        fnlist.append(name)
        self.wb[i] = re.sub(string, \
        "⑪a id='r{0}'⑫⑪/a⑫⑪a href='⑦f{0}' style='text-decoration: none; '⑫⑪sup⑫⑬{0}⑭⑪/sup⑫⑪/a⑫".format(name), \
        self.wb[i], 1)

    self.preProcessCommon()

    self.snPresent = False

    # protect PPer-supplied internal link information
    # two forms: #number# and #name:id-value#
    # also #RomanNumerals#
    # for either, replace the # symbols with ⑲ so they can be found uniquely later
    # without interference from other HTML markup ppgen may have added
    i = 0
    while i < len(self.wb):

      # skip literal sections, as we shouldn't mess around in them
      if ".li" == self.wb[i]:
        while i < len(self.wb) and not ".li-" == self.wb[i]:
          i += 1
        if i == len(self.wb):
          self.crash_w_context("unclosed .li", i)
        i += 1
        continue

      # skip .de statements (including continuations), too, to avoid affecting RGB color specifications
      if self.wb[i].startswith(".de"):
        while (i < len(self.wb) - 1) and self.wb[i].endswith("\\"): # this version of continuation still needed
          i += 1
        if not self.wb[i].endswith("\\"):
          i += 1
        else:
          self.fatal("source file ends with continued .de command: {}".format(self.wb[i]))
        continue

      self.wb[i] = re.sub(r"#(\d+)#", r"⑲\1⑲", self.wb[i])
      self.wb[i] = re.sub(r"#([iIvVxXlLcCdDmM]+)#", r"⑲\1⑲", self.wb[i])
      #self.wb[i] = re.sub(r"#(.*?:.*?)#", r"⑲\1⑲", self.wb[i])
      #self.wb[i] = re.sub(r"#([^]].*?:[A-Za-z][A-Za-z0-9\-_\:\.]*?)#", r"⑲\1⑲", self.wb[i])
      self.wb[i] = re.sub(r"#([^]\n].*?:.*?[^[])#", r"⑲\1⑲", self.wb[i])
      i += 1

    # HTML will always choose the UTF-8 Greek line
    i = 0
    while i < len(self.wb):
      if self.wb[i].startswith('.gu'):
        self.wb[i] = re.sub("^\.gu ", "", self.wb[i])
      if self.wb[i].startswith('.gl'):
        del(self.wb[i])
        i -= 1
      i += 1

    # merge page numbers (down) into text
    # ⑯14⑰ moves into next paragraph down or into a heading
    # 21-Jun-2014: handle consecutive .pn +1
    i = 0
    while i < len(self.wb):
      m = self.pnmatch.match(self.wb[i])
      if m:
        pnum = m.group(1) # string
        del self.wb[i]
        found = False
        while not found and (i < len(self.wb)):    # loop until we find a valid insertion spot

          # if we hit the start of a .li, warn the user and put the page number line back in.
          # it can't float into or over the .li, so it will appear wherever it appears
          if self.wb[i].startswith(".li"):
            self.warn(".li encountered while placing page number: {}".format(pnum))
            self.wb.insert(i,"⑯{}⑰".format(pnum)) # insert page number before the .li
            i += 2 # bump past new page number line and the .li
            found = True
            continue
          if self.wb[i].startswith(".dv"):
            self.warn(".dv encountered while placing page number: {}".format(pnum))
            self.wb.insert(i,"⑯{}⑰".format(pnum)) # insert page number before the .dv
            i += 2 # bump past new page number line and the .dv
            found = True
            continue
          if self.wb[i].startswith(".ta"): # we can't put it on the .ta, but don't want it added to the next line, either
                                           # as that can interfere with table horizontal border processing
            self.wb.insert(i+1,"⑯{}⑰".format(pnum)) # insert page number after the .ta
            i += 2 # bump past the .ta and the new page number line
            found = True
            continue

          # it is possible to hit another pn match before finding a suitable home
          m = re.match(r"⑯(.+)⑰", self.wb[i])  # must be on line by itself
          if m:
            pnum = m.group(1)  # the page number
            del self.wb[i]     # original line gone
            continue           # now go and place it
          # placing the page number
          #  if we see a heading, place it there
          #  if not, look for any line of plain text and insert it
          if re.match(r"\.h[1-6]", self.wb[i]):
            self.wb[i] += " pn={}".format(pnum)
            found = True
          if self.wb[i].startswith(".il"):
            self.wb[i] += " pn={}".format(pnum)
            found = True
          # don't place on a .bn info line
          if self.bnPresent and self.is_bn_line(self.wb[i]):
            i += 1
            continue
          if self.wb[i].startswith(".it "): # .it line?
            self.wb[i] = ".it " + "⑯{}⑰".format(pnum) + self.wb[i][4:] # merge it onto the line after the ".it "
            i += 1
            found = True
            continue
          if (self.wb[i].startswith(".dt") or # we can't put it on .dt or .dd but we can't let
              self.wb[i].startswith(".dd")):  # it slide beyond, either, so insert it before
            self.wb.insert(i,"⑯{}⑰".format(pnum)) # insert page number before current line
            i += 2 # bump past the new page number line and old current line
            found = True
            continue
          # plain text
          if self.wb[i] and not self.wb[i].startswith("."):
            self.wb[i] = "⑯{}⑰".format(pnum) + self.wb[i]
            found = True
          i += 1 # keep looking
      else:       # only increment if first match above failed
        i += 1    # as if it worked we deleted the matching line


    # convert any <br> outside of .li blocks to <br>
    i = 0
    while i < len(self.wb):

      # skip literal sections
      if ".li" == self.wb[i]:
        while (i < len(self.wb)) and not ".li-" == self.wb[i]:
          i += 1
        if i == len(self.wb):
          self.crash_w_context("unclosed .li", i)
        i += 1
        continue

      self.wb[i] = self.wb[i].replace("<br>", "<br>") # void element
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

      s = self.wb[i]
      explicit = False
      m = re.search("\[(\d+)\]", s) # explicit
      while m:
        explicit = True
        fncr = int(m.group(1)) + 1
        s = re.sub(re.escape(m.group(0)), "", s, 1)
        m = re.search("\[(\d+)\]", s)
      if explicit: # don't support mixing # and explicit in the same line
        i += 1
        continue

      m = re.search("\[#\]", self.wb[i]) # auto-assigned
      while m:
        self.wb[i] = re.sub(re.escape(m.group(0)), "[{}]".format(fncr), self.wb[i], 1)
        fncr += 1
        m = re.search("\[#\]", self.wb[i])
      i += 1

    # must do separately
    fncr = 1
    i = 0
    fnlevel = 0
    self.fn_name_length = 0
    fnlist2 = defaultdict(int)  # list of non-numeric footnotes encountered in the file
    while i < len(self.wb):

      # skip literal sections
      if ".li" == self.wb[i]:
        while not ".li-" == self.wb[i]:
          i += 1
        i += 1
        continue

      if self.wb[i].startswith(".fn "):
        if fnlevel == 0: # remember most recent outermost .fn
          fn0 = i
        fnlevel += 1  # track footnote depth
        m = re.match(r"\.fn (\d+)( |$)", self.wb[i]) # explicit
        if m:
          fncr = int(m.group(1)) + 1
          fnname = m.group(1)

        elif ".fn #" == self.wb[i]: # auto-assigned
          self.wb[i] = ".fn {}".format(fncr)
          fnname = "{}".format(fncr)
          fncr += 1

        else:
          m=re.match(r"\.fn ([A-Za-z0-9\-_\:\.]+)( |$)", self.wb[i])
          if m:
            fnlist2[m.group(1)] += 1 # Remember this non-numeric footnote name
            fnname = m.group(1)
          else:
            self.warn("Invalid footnote name/number: {}".format(self.wb[i]))
        self.fn_name_length = max(len(fnname), self.fn_name_length)

      elif self.wb[i].startswith(".fn-"):
        if fnlevel == 0:
          self.crash_w_context("Error: .fn- has no opening .fn command", i)
        fnlevel -= 1

      i += 1
    if fnlevel != 0:
      self.crash_w_context("Error: Unclosed .fn block", fn0)

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
      #
      # non-numeric footnote references can only be recognized if we found a .fn
      # for them in the earlier pass through the text
      m = re.search(r"\[(\d+)\]", self.wb[i])  # look for standard numeric footnote references
      while m:
        fnname = m.group(1)
        fnDupCheck(fnname)
        m = re.search(r"\[(\d+)\]", self.wb[i])

      line = self.wb[i]  # now look for named footnote references
      m2 = re.search(r"\[([A-Za-z0-9\-_\:\.]+)\]", line)
      while m2:
        name = m2.group(1)
        if name in fnlist2:  # if it's there, we have a reference to a footnote
          fnlist2[name] += 1 # remember we saw a reference to it
          fnDupCheck(name)
        name = '[' + name + ']'
        line = re.sub(re.escape(name), "", line, 1) # remove the hit so we can look for another
        m2 = re.search(r"\[([A-Za-z0-9\-_\:\.]+)\]", line)

      i += 1

    # now check to see if all non-numeric footnotes were referenced so we can give a good message
    for name in fnlist2:
      header_needed = True
      if fnlist2[name] < 2:  # value is 1 when defined, +1 for each reference
        if header_needed:
          self.warn("No references found for these named footnotes:")
          header_needed = False
        self.print_msg("               {}".format(name))

    # target references
    # Originally <target id='something'> but also allow id="something" and id=something for convenience
    # Also, now allow <target=something>
    i = 0
    while i < len(self.wb):
      if "<target id" in self.wb[i]:
        m = re.search("<target id='(.*?)'>", self.wb[i])
        while m:
          self.wb[i] = re.sub("<target id='(.*?)'>", "<a id='{0}'></a>".format(m.group(1)), self.wb[i], 1)
          self.checkId(m.group(1), id_loc=i)
          m = re.search("<target id='(.*?)'>", self.wb[i])
        m = re.search("<target id=\"(.*?)\">", self.wb[i])
        while m:
          self.wb[i] = re.sub("<target id=\"(.*?)\">", "<a id='{0}'></a>".format(m.group(1)), self.wb[i], 1)
          self.checkId(m.group(1), id_loc=i)
          m = re.search("<target id=\"(.*?)\">", self.wb[i])
        m = re.search("<target id=(.*?)>", self.wb[i])
        while m:
          self.wb[i] = re.sub("<target id=(.*?)>", "<a id='{0}'></a>".format(m.group(1)), self.wb[i], 1)
          self.checkId(m.group(1), id_loc=i)
          m = re.search("<target id=(.*?)>", self.wb[i])
      elif "<target=" in self.wb[i]:
        m = re.search("<target=(.*?)>", self.wb[i])
        while m:
          self.wb[i] = re.sub("<target(.*?)>", "<a id='{0}'></a>".format(m.group(1)), self.wb[i], 1)
          self.checkId(m.group(1), id_loc=i)
          m = re.search("<target(.*?)>", self.wb[i])

      i += 1

    # inline tags across lines in .nf blocks must be applied to each line
    # applies only to HTML b/c no-fills are rendered as <div>
    i = 0
    while i < len(self.wb):
      if self.wb[i].startswith(".nf"): # find a no-fill block
        m = re.match(r"\.nf ([lrcb])", self.wb[i])
        if m:
          tagstack = []
          i += 1 # step inside the .nf block
          while i < len(self.wb) and not self.wb[i].startswith(".nf-"): # as long as we are in a .nf
            if self.wb[i].startswith(".nf "):
              self.crash_w_context("nested no-fill block:", i)
            # ignore .bn lines; just pass them through
            if self.bnPresent and self.is_bn_line(self.wb[i]):
              i += 1
              continue
            if self.wb[i] == "": # ignore empty lines
              i += 1
              continue
            # find all tags on this line; ignore <a and </a tags completely for this purpose
            tmpline = re.sub("<a [^>]*>", "", self.wb[i])
            tmpline = re.sub("</a>", "", tmpline)
            t = re.findall("<\/?[^>]*>", tmpline)
            sstart = "" # what to prepend to the line
            for s in tagstack: # build the start string
              sstart += s
            m = re.match(r"( *)(.*)", self.wb[i])
            if m:
              self.wb[i] = m.group(1) + sstart + m.group(2) # put start tags after blanks (if any)
            else: # should not happen?
              self.dprint("tagstack code problem?\ni = {}\nline = >>{}<<".format(i, self.wb[i]))
              self.wb[i] = sstart + self.wb[i] # rewrite the line with new start
            for s in t: # we may have more tags on this line
              if s.endswith("/>"): # it is a self-closing tag
                continue           # ignore it
              elif not s.startswith("</"): # it is an opening tag
                if s in tagstack:
                  self.warn("Nested {} tags in .nf block: {}".format(s, tmpline))
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
              m = re.match(r"</(\w+) .*>", s) # is it a tag with parameters?
              if m:                           # if so, drop them
                s = "</m.group(1)>"
              # next remove arguments from any ppgen inline tag that has arguments
              # without a preceding space (e.g., <c=red> or <fs=120%>)
              if closetag.startswith("</c"):
                closetag = "</c>" # colors
              if closetag.startswith("</fs"):
                closetag = "</fs>" # font size
              if closetag.startswith("</lang"):
                closetag = "</lang>" # language
              if closetag.startswith("</sn"):
                closetag = "</sn>" # inline sidenote
              if closetag.startswith("</abbr"):
                closetag = "</abbr>" # abbreviation
              send += closetag
            self.wb[i] = self.wb[i] + send
            i += 1
          if len(tagstack):
            self.warn_w_context("Unclosed tags in .nf block: {}".format(tagstack), i)

      i += 1

    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    # <lang> tags processed in HTML.
    # <lang="fr">merci</lang>
    i = 0
    while i < len(self.wb):
      if self.wb[i] == ".li":         # ignore literal blocks
        while i < len(self.wb) and self.wb[i] != ".li-":
          i += 1
        i += 1  # skip over .li- command
      else:
        # m = re.search(r"<lang=[\"']?([^>]+)[\"']?>",self.wb[i])
        m = re.search(r"<lang=[\"']?([^\"'>]+)[\"']?>",self.wb[i])
        while m:
          langspec = m.group(1)
          self.wb[i] = re.sub(re.escape(m.group(0)), "ᒪ'{}'".format(langspec), self.wb[i])
          # self.wb[i] = re.sub(m.group(0), "<span lang=\"{0}\">".format(langspec), self.wb[i], 1)
          m = re.search(r"<lang=[\"']?([^\"'>]+)[\"']?>",self.wb[i])
        if "<lang" in self.wb[i]:
          self.fatal("incorrect lang markup: {}".format(self.wb[i]))
        self.wb[i] = re.sub(r"</lang>", "ᒧ",self.wb[i])
        i += 1

    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    # <abbr> tags processed in HTML.
    # (1) <abbr="Saint">St.</abbr> or <abbr=Saint>St.</abbr>
    #       would generate <abbr title='Saint'>St.</abbr>
    # (2) <abbr rend=arabic>XXX</abbr>
    #       would generate <abbr title='30'>XXX</abbr>
    # (3) <abbr rend=spell>Ph.D.</abbr>
    #       would generate <abbr class='spell'>Ph.D.</abbr>
    #       along with CSS: abbr.spell { speak: spell-out; }
    # Any use of <abbr> will generate CSS: abbr { border-bottom-width: thin; border-bottom-style: dotted; }
    i = 0
    abbrfound = False
    while i < len(self.wb):
      if self.wb[i] == ".li":         # ignore literal blocks
        while i < len(self.wb) and self.wb[i] != ".li-":
          i += 1
        i += 1  # skip over .li- command
      else:
        temp = self.wb[i]
        # look for form 1 of abbr tag
        m = re.search(r"<abbr=[\"']?([^\"'>]+)[\"']?>",temp)
        while m:
          abbrfound = True
          abbrtitle = re.sub("'","&#39;",m.group(1)) # escape any ' in the title string
          temp = re.sub(re.escape(m.group(0)), "", temp) # remove the abbr tag from the temporary copy of the line
          self.wb[i] = re.sub(re.escape(m.group(0)), "<abbr title='{}'>".format(abbrtitle), self.wb[i]) # replace in original line
          m = re.search(r"<abbr=[\"']?([^\"'>]+)[\"']?>",temp) # search for more <abbr= tags in copy
        # look for form 2 of abbr tag
        m = re.search(r"<abbr rend=[\"']?arabic[\"']?>([iIvVxXlLcCdDmM]+)",temp)
        while m:
          abbrfound = True
          abbrtitle = self.fromRoman(m.group(1).lower())
          temp = re.sub(re.escape(m.group(0)), "", temp) # remove the abbr tag from the temporary copy of the line
          self.wb[i] = re.sub(re.escape(m.group(0)), "<abbr title='{}'>{}".format(abbrtitle, m.group(1)), self.wb[i]) # replace in original line
          m = re.search(r"<abbr rend=[\"']?arabic[\"']?>([iIvVxXlLcCdDmM]+)",temp) # search for more <abbr rend=arabic tags in copy
        # look for form 3 of abbr tag
        spellfound = False
        m = re.search(r"<abbr rend=[\"']?spell[\"']?>",temp)
        while m:
          abbrfound = True
          spellfound = True
          temp = re.sub(re.escape(m.group(0)), "", temp) # remove the abbr tag from the temporary copy of the line
          self.wb[i] = re.sub(re.escape(m.group(0)), "<abbr class='spell'>", self.wb[i]) # replace in original line
          m = re.search(r"<abbr rend=[\"']?spell[\"']?>",temp) # search for more <abbr rend=spell tags in copy
        if abbrfound:
          self.css.addcss("[1210] abbr { border-bottom-width: thin; border-bottom-style: dotted; }")
        if spellfound:
          self.css.addcss("[1210] abbr.spell { speak: spell-out; }")
        if "<abbr" in temp: # should not have any <abbr tags left in the temp copy
          self.crash_w_context("incorrect abbr markup: {}".format(temp), i)
        i += 1

    # -------------------------------------------------------------------------
    # inline markup (HTML)

    # list of simple inline tags:
    simple_tags = ['l', 'xl', 'xxl', 's', 'xs', 'xxs', 'i', 'b', 'f', 'g',
                   'u', 'em', 'strong', 'cite', 'sn', 'br']
    # inline tags of the form <x=...>
    complex_tags1 = ['c', 'fs', 'abbr']
    # inline tags of the form <x ...>
    complex_tags2 = ['abbr']
    for i, line in enumerate(self.wb):

      # promote the "ignore in text" tags
      # do all of these first so look-ahead (i.e. small caps) will find corrected case.
      self.wb[i] = re.sub(r"<I", "<i", self.wb[i])
      self.wb[i] = re.sub(r"<\/I", "</i", self.wb[i])
      self.wb[i] = re.sub(r"<SC", "<sc", self.wb[i])
      self.wb[i] = re.sub(r"<\/SC", "</sc", self.wb[i])
      self.wb[i] = re.sub(r"<B", "<b", self.wb[i])
      self.wb[i] = re.sub(r"<\/B", "</b", self.wb[i])

    in_nf = False
    in_ta = False
    in_fn = False
    for i, line in enumerate(self.wb):

      if self.wb[i].startswith(".nf "):
        in_nf = True
      elif self.wb[i].startswith(".nf-"):
        in_nf = False
      elif self.wb[i].startswith(".ta "):
        in_ta = True
      elif self.wb[i].startswith(".ta-"):
        in_ta = False
      if self.wb[i].startswith(".fn "):
        in_fn = True
      elif self.wb[i].startswith(".fn-"):
        in_fn = False

      # if everything inside <sc>...</sc> markup is uppercase, then
      # use font-size:smaller, else use font-variant:small-caps

      m = re.search("<sc>", self.wb[i]) # opening small cap tag
      while m:
        use_class = "sc" # unless changed
        # we have an opening small cap tag. need to examine all the text
        # up to the closing tag, which may be on a separate line.
        stmp = self.wb[i]
        j = i + 1
        # old version: m = re.search(r"<sc>([^<]+?)</sc>", stmp)
        m = re.search(r"<sc>(.*?)</sc>", stmp)
        while j < len(self.wb) and not m:
          stmp += self.wb[j]
          j += 1
          m = re.search(r"<sc>(.*?)</sc>", stmp)
        # old version: m = re.search(r"<sc>([^<]+?)</sc>", stmp)
        if m:
          scstring = self.htmlTokenRestore(m.group(1)) # need to undo our remappings in order to properly check case of string

          # need to remove any <a> resulting from <target> directives which will confuse the checking
          scstring = re.sub("<a [^>]*>.*?</a>", "", scstring)

          # inline tags created directly by the PPer also confuse the checking:
          #   l, xl, xxl, s, xs, xxs, i, b, f, g, u, em, strong, cite,
          #   c=, fs=, abbr, lang (span), sn (?), br (?)
          for tag in simple_tags:
            scstring = re.sub("</?" + tag + ">", "", scstring)
          for tag in complex_tags1:
            scstring = re.sub("<" + tag + "=[^>]*>", "", scstring)
            scstring = re.sub("</" + tag + ">", "", scstring)
          for tag in complex_tags2:
            scstring = re.sub("<" + tag + " [^>]*>", "", scstring)
            scstring = re.sub("</" + tag + ">", "", scstring)

          ###
          # warn about all lower case, but not within .nf as
          # we will have replicated the <sc> tags that cross lines
          # of the .nf block, which could leave some all lower-case
          # line alone within the <sc> </sc>, but it's not an error
          if not in_nf and scstring == scstring.lower():
            self.warn("all lower case inside small-caps markup: {}".format(self.wb[i]))
          if scstring == scstring.upper(): # all upper case
            use_class = "fss"
        else:
          self.warn("Unexpected problem interpreting <sc> string, assuming mixed-case.\nLine number:{}\nCurrent line: {}\nCurrent string:{}".format(i, self.wb[i],stmp))
        if use_class == "sc":
          self.wb[i] = re.sub("<sc>", "<span class='sc'>", self.wb[i], 1)
          self.css.addcss("[1200] .sc { font-variant: small-caps; }")
        if use_class == "fss":
          self.wb[i] = re.sub("<sc>", "<span class='fss'>", self.wb[i], 1)
          self.css.addcss("[1200] .fss { font-size: 75%; }")
        self.wb[i] = re.sub("<\/sc>", "</span>", self.wb[i], 1) # since we had a <sc> replace 1 </sc> if present on this line
        m = re.search("<sc>", self.wb[i]) # look for another opening small cap tag

      # common closing, may be on separate line
      self.wb[i] = re.sub("<\/sc>", "</span>", self.wb[i])

      m = re.search("<l>", self.wb[i])
      if m:
        self.css.addcss("[1201] .large { font-size: large; }")
      self.wb[i] = re.sub("<l>", "<span class='large'>", self.wb[i])
      self.wb[i] = re.sub("<\/l>", "</span>", self.wb[i])

      m = re.search("<xl>", self.wb[i])
      if m:
        self.css.addcss("[1202] .xlarge { font-size: x-large; }")
      self.wb[i] = re.sub("<xl>", "<span class='xlarge'>", self.wb[i])
      self.wb[i] = re.sub("<\/xl>", "</span>", self.wb[i])

      m = re.search("<xxl>", self.wb[i])
      if m:
        self.css.addcss("[1202] .xxlarge { font-size: xx-large; }")
      self.wb[i] = re.sub("<xxl>", "<span class='xxlarge'>", self.wb[i])
      self.wb[i] = re.sub("<\/xxl>", "</span>", self.wb[i])

      m = re.search("<s>", self.wb[i])
      if m:
        self.css.addcss("[1203] .small { font-size: small; }")
      self.wb[i] = re.sub("<s>", "<span class='small'>", self.wb[i])
      self.wb[i] = re.sub("<\/s>", "</span>", self.wb[i])

      m = re.search("<xs>", self.wb[i])
      if m:
        self.css.addcss("[1204] .xsmall { font-size: x-small; }")
      self.wb[i] = re.sub("<xs>", "<span class='xsmall'>", self.wb[i])
      self.wb[i] = re.sub("<\/xs>", "</span>", self.wb[i])

      m = re.search("<xxs>", self.wb[i])
      if m:
        self.css.addcss("[1205] .xxsmall { font-size: xx-small; }")
      self.wb[i] = re.sub("<xxs>", "<span class='xxsmall'>", self.wb[i])
      self.wb[i] = re.sub("<\/xxs>", "</span>", self.wb[i])

      m = re.search("<u>", self.wb[i])
      if m:
        self.css.addcss("[1205] .under { text-decoration: underline; }")
      self.wb[i] = re.sub("<u>", "<span class='under'>", self.wb[i])
      self.wb[i] = re.sub("<\/u>", "</span>", self.wb[i])

      m = re.search(r"<c=[\"']?(.*?)[\"']?>", self.wb[i])
      while m:
        thecolor = m.group(1)
        safename = re.sub("#","", thecolor)
        self.css.addcss("[1209] .color_{0} {{ color: {1}; }}".format(safename,thecolor))
        self.wb[i] = re.sub(re.escape(m.group(0)), "<span class='color_{0}'>".format(safename), self.wb[i])
        m = re.search(r"<c=[\"']?(.*?)[\"']?>", self.wb[i])
      self.wb[i] = re.sub("<\/c>", "</span>", self.wb[i])

      # <g> is now a stylized em in HTML
      # using a @media handheld, in epub/mobi it is italicized, with normal letter spacing
      m = re.search(r"<g>", self.wb[i])
      if m:
        self.wb[i] = re.sub(r"<g>", "<em class='gesperrt'>", self.wb[i])
        self.css.addcss("[1378] em.gesperrt { font-style: normal; letter-spacing: 0.2em; margin-right: -0.2em; }")
        self.css.addcss("[1379] .x-ebookmaker em.gesperrt { font-style: italic; letter-spacing: 0; margin-right: 0;}")
      self.wb[i] = re.sub("<\/g>", "</em>", self.wb[i])

      m = re.search(r"<fs=[\"']?(.*?)[\"']?>", self.wb[i])
      while m:
        self.wb[i] = re.sub(m.group(0), "<span style='font-size⑥ {}; '>".format(m.group(1)), self.wb[i], 1)
        m = re.search(r"<fs=[\"']?(.*?)[\"']?>", self.wb[i])
      self.wb[i] = re.sub("<\/fs>", "</span>", self.wb[i])

      # <sn>...</sn> becomes a span
      tmpline = self.wb[i]
      m = re.search(r"<sn[^>]*>.*?</sn>", tmpline) # find sidenote contents and replace any | with <br>
      while m:
        sn = m.group(0).replace('|', '<br>') 
        self.wb[i] = re.sub(re.escape(m.group(0)), sn, self.wb[i])
        tmpline = re.sub(re.escape(m.group(0)), "", tmpline)
        m = re.search(r"<sn[^>]*>.*?</sn>", tmpline)
      self.wb[i], count = re.subn("<sn>", "<span class='sni'><span class='hidev'>⓫</span>", self.wb[i]) # replace <sn>
      m = re.search(r"<sn class=([\"'])(\w*)\1>", self.wb[i])  # replace <sn class=...>
      while m:
        self.wb[i], count2 = re.subn(re.escape(m.group(0)), "<span class='sni {}'><span class='hidev'>⓫</span>".format(m.group(2)),
                                     self.wb[i])
        count += count2
        m = re.search(r"<sn class=([\"'])(\w*)\1>", self.wb[i])
      self.wb[i] = re.sub("</sn>", "<span class='hidev'>⓫</span></span>", self.wb[i]) # replace </sn>
      #if not self.snPresent and tmpline != self.wb[i]:
      if count:
        self.snPresent = True
      if count and (in_nf or in_ta or in_fn):
        self.warn_w_context("Inline sidenote probably won't work well here:", i)

    #
    # Handle any .sr for HTML that have the b option specified
    if self.sr_b:
      #self.dprint("processing .sr for HTML with b specified")
      for i in range(len(self.srw)):
        if ('h' in self.srw[i]) and ('b' in self.srw[i]): # if this one is for pre-processing and applies to HTML
          self.process_SR(self.wb, i)

  # -------------------------------------------------------------------------------------
  # restore tokens in HTML text

  def htmlTokenRestore(self, text):
    text = re.sub("ⓓ", ".", text)
    text = re.sub("①", "{", text)
    text = re.sub("②", "}", text)
    text = re.sub("③", "[", text)
    text = re.sub("④", "]", text)
    text = re.sub("⑤", "&lt;", text) # for future reference: &#60;
    text = re.sub("⑳", "&gt;", text) # for future reference: &#62;
    text = re.sub("⓪", "#", text)
    text = re.sub("⓫", "|", text)
    text = re.sub("⑩", r"\|", text) # restore temporarily protected \| and \(space)
    text = re.sub("⑮", r"\ ", text)
    text = re.sub("ⓢ", "&#160;", text) # non-breaking space (edit: use &#160; instead of &nbsp;)
    text = re.sub("ⓣ", "&#8203;", text) # zero space
    text = re.sub("ⓤ", "&#8201;", text) # thin space (edit: use &#8201; instead of &thinsp;)
    text = re.sub("ⓥ", "&#8196;", text) # thick space
    # ampersand
    text = re.sub("Ⓩ", "&#38;", text) # (use &#38; instead of &amp;)
    # protected
    text = re.sub("⑪", "<", text)
    text = re.sub("⑫", ">", text)
    text = re.sub("⑬", "[", text)
    text = re.sub("⑭", "]", text)
    text = re.sub("⓮", "^", text)
    text = re.sub("⓯", "_{", text)

    # unprotect temporarily protected characters from Greek strings
    text = re.sub("⑩", "\|", text) # restore temporarily protected \| and \(space)
    text = re.sub("⑮", "\ ", text)


    return text


  # -------------------------------------------------------------------------------------
  # post-process working buffer

  def postprocess(self):

    for i, line in enumerate(self.wb):
      # basic tokens
      self.wb[i] = self.htmlTokenRestore(self.wb[i])

      # superscripts, subscripts
      self.wb[i] = re.sub(r"◸(.*?)◹", r'<sup>\1</sup>', self.wb[i])
      self.wb[i] = re.sub(r"◺(.*?)◿", r'<sub>\1</sub>', self.wb[i])

      # use entities if user is writing any "--" or "----" to the HTML file
      # if this is Latin-1 output. Otherwise, trust the PPer.
      if self.encoding == 'latin_1' and self.renc == "h": 
        self.wb[i] = self.wb[i].replace("--", "&#8212;") # (edit: use &#8212; instead of &mdash;)
      # flag an odd number of dashes
      if "&#8212;-" in self.wb[i]:
        self.warn("&mdash; with hyphen: {}".format(self.wb[i])) #named token is ok for output
      # ok now to unprotect those we didn't want to go to &mdash; entity
      self.wb[i] = re.sub(r"⑨", '-', self.wb[i])

      self.wb[i] = re.sub(r"\[oe\]", r'&#339;', self.wb[i])  #(edit: use &#339; instead of &oelig;)
      self.wb[i] = re.sub(r"\[ae\]", r'&#230;', self.wb[i])  #(edit: use &#230; instead of &aelig;)
      self.wb[i] = re.sub(r"\[OE\]", r'&#338;', self.wb[i])  #(edit: use &#338; instead of &OElig;)
      self.wb[i] = re.sub(r"\[AE\]", r'&#198;', self.wb[i])  #(edit: use &#198; instead of &AElig;)

    i = 0
    while i < len(self.wb):
      m = re.search(r"⑯(.+)⑰", self.wb[i]) # page number
      if m:
        ptmp = m.group(1)
        if self.pnshow:  # visible page number
          # in a paragraph usually, but can be orphaned (repaired later)
          if self.nregs["pnstyle"] == "title" or "x" in self.debug:
            self.wb[i] = re.sub(r"⑯(.+)⑰",
                                "<span class='pageno' title='{0}' id='Page_{0}' ></span>".format(ptmp),
                                self.wb[i])
          else:
            self.wb[i] = re.sub(r"⑯(.+)⑰",
                                "<span class='pageno' id='Page_{0}' >{0}</span>".format(ptmp),
                                self.wb[i])
        elif self.pnlink:  # just the link
          self.wb[i] = re.sub(r"⑯(.+)⑰", "<a id='Page_{0}'></a>".format(ptmp), self.wb[i])
      i += 1

    # internal page links
    # two forms: #17# and #The Encounter:ch01#
    # also allow Roman numbered pages
    # which at this point are actually using ⑲ instead of the # signs
    for i in range(len(self.wb)):

      m = re.search(r"⑲(\d+?)⑲", self.wb[i])
      while m: # page number reference
        s = "<a href='⫉Page_{0}'>{0}</a>".format(m.group(1)) # link to it
        self.wb[i] = re.sub(m.group(0), s, self.wb[i], 1)
        m = re.search(r"⑲(\d+?)⑲", self.wb[i])

      m = re.search(r"⑲([iIvVxXlLcCdDmM]+)⑲", self.wb[i]) # Roman numeral reference
      while m:
        s = "<a href='⫉Page_{0}'>{0}</a>".format(m.group(1)) # link to that
        self.wb[i] = re.sub(m.group(0), s, self.wb[i], 1)
        m = re.search(r"⑲([iIvVxXlLcCdDmM]+)⑲", self.wb[i])

      m = re.search(r"⑲(.*?):(music/.*\.mid)⑲", self.wb[i]) # named music file reference
      while m:
        s = "<a href='{}'>{}</a>".format(m.group(2), m.group(1)) # link to that
        self.wb[i] = re.sub(re.escape(m.group(0)), s, self.wb[i], 1)
        m = re.search(r"⑲(.*?):(music/.*\.mid)⑲", self.wb[i])

      m = re.search(r"⑲(.*?):(.*?)⑲", self.wb[i]) # named text reference
      while m:
        s = "<a href='⫉{}'>{}</a>".format(m.group(2), m.group(1)) # link to that
        self.checkId(m.group(2), id_loc=i)
        self.wb[i] = re.sub(re.escape(m.group(0)), s, self.wb[i], 1)
        m = re.search(r"⑲(.*?):(.*?)⑲", self.wb[i])

      self.wb[i] = re.sub("⫉", '#', self.wb[i])

    for i, line in enumerate(self.wb):  ### extraneous and should be deleted?
      self.wb[i] = re.sub("⑥", ":", self.wb[i])

    for i, line in enumerate(self.wb):
      # lang specifications
      m = re.search(r"ᒪ'(.+?)'", self.wb[i])
      while m:
        self.wb[i] = re.sub(m.group(0), "<span lang=\"{0}\">".format(m.group(1)), self.wb[i], 1) # RT remove the deprecated xml declaration
        m = re.search(r"ᒪ'(.+?)'", self.wb[i])
      self.wb[i] = re.sub("ᒧ", "</span>", self.wb[i])

  # -------------------------------------------------------------------------------------
  # save buffer to specified dstfile (HTML output)
  def saveFile(self, fn):
    f1 = codecs.open(fn, "w", self.encoding)
    for index,t in enumerate(self.wb):
      try:
        f1.write( "{:s}\r\n".format(t))
      except Exception as e:
        self.print_msg( "internal error:\n  cannot write line: {:s}".format(t))
        self.fatal("exiting")
    f1.close()

    # save GG .bin file if needed
    if self.bnPresent:
      fnb = fn + ".bin"
      f1 = codecs.open(fnb, "w", "ISO-8859-1")
      for index,t in enumerate(self.bb):
        f1.write("{:s}\r\n".format(t))
      f1.close()
      self.print_msg("GG .bin file {} created.".format(fnb))
      if self.ppqt2: # and PPQTv2 metadata, if requested
        self.ppqtpage("", 0, fn=fn)

  # ----- makeHTML method group -----

  def doHeader(self):

    # common CSS

    if self.pnshow:
      self.css.addcss("[1100] body { margin-left: 8%; margin-right: 10%; }")
      self.css.addcss("[1105] .pageno { right: 1%; font-size: x-small; background-color: inherit; color: " + self.nregs["pnc"] + "; ")
      self.css.addcss("[1106]         text-indent: 0em; text-align: right; position: absolute; ")
      self.css.addcss("[1107]         border: thin solid " + self.nregs["pnc"] + "; padding: .1em .2em; font-style: normal; ")
      self.css.addcss("[1108]         font-variant: normal; font-weight: normal; text-decoration: none; }")
      if self.nregs["pnstyle"] == "title" or "x" in self.debug:
        self.css.addcss("[1109] .pageno:after { color: " + self.nregs["pnc"] + "; content: attr(title); }")  # new 3.24M
      elif self.nregs["pnstyle"] != "content":
        self.warn("Invalid .nr pnstyle value {}; content assumed".format(self.nregs["pnstyle"]))
        self.nregs["pnstyle"] = "content"

    else:
      self.css.addcss("[1100] body { margin-left: 8%; margin-right: 8%; }")

    self.css.addcss("[1170] p { text-indent: 0; margin-top: 0.5em; margin-bottom: 0.5em; text-align: justify; }") # para style

    # generate CSS for sidenotes if any are present in the text
    if self.snPresent:
      # CSS taken from http://www.pgdp.net/wiki/Sidenotes with changes.
      self.css.addcss("[1500] .sidenote, .sni { text-indent: 0; text-align: left; width: 9em; min-width: 9em; " +
                      "max-width: 9em; padding-bottom: .1em; padding-top: .1em; padding-left: .3em; " +
                      "padding-right: .3em; margin-right: 3.5em; float: left; clear: left; margin-top: 0em; " +
                      "margin-bottom: 0em; font-size: small; color: black; background-color: #eeeeee; " +
                      "border: thin dotted gray; font-style: normal; font-weight: normal; font-variant: normal; " +
                      "letter-spacing: 0em; text-decoration: none; }"
                      )
      self.css.addcss("[1501] .x-ebookmaker .sidenote, .sni { float: left; clear: none; font-weight: bold; }")
      self.css.addcss("[1502] .sni { text-indent: -.2em; }")
      self.css.addcss("[1503] .hidev { visibility: hidden; }")

    # HTML header
    t = []
    #t.append("<!DOCTYPE html PUBLIC \"-//W3C//DTD XHTML 1.0 Strict//EN\"")
    #t.append("    \"http://www.w3.org/TR/xhtml1/DTD/xhtml1-strict.dtd\">")
    t.append("<!DOCTYPE html>")
    t.append("<html lang=\"" + self.nregs["lang"] + "\">") # include base language in header RT removed deprecated xmlns and xml declarations
    t.append("  <head>")

    if self.encoding == "utf_8":
      #t.append("    <meta http-equiv=\"Content-Type\" content=\"text/html;charset=UTF-8\">")
      t.append("    <meta charset=\"UTF-8\">")
    elif self.encoding == "latin_1":
      t.append("    <meta http-equiv=\"Content-Type\" content=\"text/html;charset=ISO-8859-1\">")

    if self.dtitle != "":
      t.append("    <title>{}</title>".format(self.htmlTokenRestore(self.dtitle)))
    else:
      t.append("    <title>{}</title>".format("Unknown"))
    t.append("    <link rel=\"icon\" href=\"images/{}\" type=\"image/x-cover\">".format(self.cimage))
    self.checkIllo(self.cimage)
    #t.append("    <style type=\"text/css\">")
    t.append("    <style>") # RT removed the deprecated CDATA comment opening
    t.append("      CSS PLACEHOLDER")
    #t.append("    </style>")
    t.append("    </style>") # RT removed the closing of the deprecated CDATA comment
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

  #----------------------------------------------------
  # process saved search/replace strings, if any
  # but only if our output format matches something in the saved "which" value
  def doHTMLSr(self):
    #self.dprint("processing .sr for HTML without b specified")
    for i in range(len(self.srw)):
      if ('h' in self.srw[i]) and not ('b' in self.srw[i] or 'B' in self.srw[i]): # if this one applies to HTML and was not already handled
        self.process_SR(self.wb, i)

  # ----- process method group -----

  # .li literal (pass-through)
  def doLit(self):
    if self.pvs > 0: # handle any pending vertical space before the .li
      self.wb[self.cl] = "<div style='margin-top: {}em; '></div>".format(self.pvs)
      self.pvs = 0
    else:
      del self.wb[self.cl]  # .li
    while (self.cl < len(self.wb)) and self.wb[self.cl] != ".li-":
      # leave in place
      self.cl += 1
    if self.cl < len(self.wb):
      del self.wb[self.cl]  # .li-
    else:
      self.crash_w_context("unclosed .li", self.cl)

  # .pb page break
  # display a page break in HTML on a browser.
  # in epub/mobi, a physical page break is used so use a
  # @media handheld to make the horizontal rule invisible
  def doPb(self):
    # if there is a pending vertical space, include it in style
    hcss = "margin-top: 1em; "  # default
    if self.pvs > 0:
      hcss = "margin-top: {}em; ".format(self.pvs)
      self.pvs = 0

    self.css.addcss("[1465] div.pbb { page-break-before: always; }")
    self.css.addcss("[1466] hr.pb { border: none; border-bottom: thin solid; margin-bottom: 1em; }")
    self.css.addcss("[1467] .x-ebookmaker hr.pb { display: none; }")
    self.wb[self.cl:self.cl+1] = ["<div class='pbb'>",
                                  "  <hr class='pb' style='{}'>".format(hcss),
                                  "</div>"]
    self.cl += 2

  # extract any "class=" argument from string s
  def dvGetClass(self, s):
    if "class='" in s:
      m = re.search(r"class='(.*?)'", s)
      if m:
        return m.group(1)
    elif "class=\"" in s:
      m = re.search(r"class=\"(.*?)\"", s)
      if m:
        return m.group(1)
    elif "class=" in s:
      m = re.search(r"class=(.*)( |$)", s)
      if m:
        return m.group(1)
    else:
      return ""

  # extract any "fs=" argument from string s
  def dvGetFs(self, s, i):
    if "fs=" in s:
      m = re.search(r"fs=(.*?%) ?", s)
      if m:
        return m.group(1)
      else:
        m = re.search(r"fs=(.*?em) ?", s)
        if m:
          return m.group(1)
        else:
          self.crash_w_context("Improper fs= specification on .dv", i)

  # doDiv (HTML)
  def doDiv(self):

    if self.wb[self.cl] == ".⓭DV-": # have we hit our special ending tag for a processed .dv-?
      self.fszpop('.dv')           # pop the fsz stack
      self.wb[self.cl] = ""        # replace the special ending tag with a null line
      self.cl += 1
      return

    j = self.cl                   # remember where we started

    self.fszpush('.dv')           # push current .fs value onto fsz stack
    fs = ""
    if "fs=" in self.wb[j]:       # did user ask for a different font size for the division?
      fs = self.dvGetFs(self.wb[j], j)
    elif self.fsz != "100%" and self.fsz != "1.0em":
      fs = self.fsz
    if fs:
      fs = " style='font-size: {};'".format(fs)
    self.fsz = "100%" # reset self.fsz to 100% in any case; it was either already 100% or we've captured the
                      # different value and will use it on our <div>, restoring it later on the .⓭DV-

    clss = self.dvGetClass(self.wb[j])  # get the specified classname, if any
    if clss:
      clss = " class='{}'".format(clss)

    if not clss and not fs:     # if we're about to generate a simple <div> mark it so we can ignore it later
      clss = "⓭"                # and not affect dopara processing (esp. resulting from doDropImage)

    k = self.checkDvNest()      # go check for proper .dv termination and .dv nesting and find our .dv- line

    self.wb[k:k+1] = [".⓭DV-", "</div>"]   # insert special end directive and ending </div> in place of our .dv-
    self.wb[j:j+1] = ["<div{}{}>".format(clss, fs), ""] # insert <div> and blank line
                                      # in place of our .dv

  # .hr horizontal rule
  def doHr(self):
    # if there is a pending vertical space, include it in style
    hcss = ""
    if self.pvs > 0:
      hcss = "margin-top: {}em; ".format(self.pvs)
      self.pvs = 0
    hrpct = 100
    m = re.match(r"\.hr +(w=)?(\d+)%$", self.wb[self.cl])
    if m:
      hrpct = int(m.group(2))
    elif self.wb[self.cl] != ".hr":
      self.warn_w_context("Unrecognized .hr options: {}".format(self.wb[self.cl][3:]), self.cl)
    if hrpct == 100:
      self.wb[self.cl] = "<hr style='border: none; border-bottom: thin solid; margin: 1em auto; {}'>".format(hcss)
    else:
      lmarp = (100 - hrpct)//2
      rmarp = 100 - hrpct - lmarp
      self.wb[self.cl] = "<hr style='border: none; border-bottom: thin solid; margin-top: 1em; margin-bottom: 1em; margin-left: {}%; width: {}%; margin-right: {}%; {}'>".format(lmarp,hrpct,rmarp, hcss)
    self.cl += 1

  # .tb thought break
  # thought breaks fixed at 35% thin line.
  def doTbreak(self):
    # if there is a pending vertical space, include it in style
    hcss = ""
    if self.pvs > 0:
      hcss = "margin-top: {}em; ".format(self.pvs)
      self.pvs = 0
      self.wb[self.cl] = "<hr style='border: none; border-bottom: thin solid; margin-bottom: 0.8em; margin-left: 35%; margin-right: 35%; width: 30%; {}'>".format(hcss) # for IE
    else:
      self.wb[self.cl] = "<hr style='border: none; border-bottom: thin solid; margin-top: 0.8em; margin-bottom: 0.8em; margin-left: 35%; margin-right: 35%; width: 30%; '>" # for IE
    self.cl += 1

  # .de CSS definition
  # one liners: .de h1 { color:red; }
  # this version of continuation still needed as it behaves differently from regular one
  def doDef(self):
    if not self.wb[self.cl].endswith("\\"):
      # single line
      self.wb[self.cl] = re.sub(r"\.de ", "", self.wb[self.cl])
      self.css.addcss("[{}] {}".format(self.csslc, self.wb[self.cl])) # put user CSS at end, always.
      self.csslc += 1
      del self.wb[self.cl]
    else:
      # multiple line
      self.wb[self.cl] = re.sub(r"\.de ", "", self.wb[self.cl])
      while (self.cl < len(self.wb) - 1) and self.wb[self.cl].endswith("\\"):
        s = re.sub(r"\\", "", self.wb[self.cl])
        self.css.addcss("[{}] {}".format(self.csslc, s))
        self.csslc += 1
        del self.wb[self.cl]
      # final line
      if not self.wb[self.cl].endswith("\\"):
        self.css.addcss("[{}] {}".format(self.csslc, self.wb[self.cl]))
        self.csslc += 1
        del self.wb[self.cl]
      else:
        self.fatal("source file ends with continued .de command: {}".format(self.wb[self.cl]))


  def doHnHTML(self, hnString):

    pnum = ""
    id = ""
    break_wanted = True if hnString in ['h1', 'h2', 'h3'] else False
    rend = ""
    #rend = "" if hnString in ['h1', 'h2', 'h3'] else "nobreak" # default to break for h1-h3
    hcss = ""
    alignDefault = self.getHnAlignment(hnString)
    align = ""
    title = ""

    hnCss = self.config['CSS'][hnString]
    if hnCss:
      self.css.addcss("[1100] {} {{ {} }}".format(hnString, hnCss))

    m = re.match(r"\.h[1-6]( .*)", self.wb[self.cl])
    if m: # modifier
      #if hnString in ['h1', 'h2', 'h3']:
      #  rend = m.group(1)
      #else:
      #  rend += m.group(1)
      rend = m.group(1)

      if "pn=" in rend:
        rend, pnum = self.get_id("pn", rend)

      if "id=" in rend:
        rend, id = self.get_id("id", rend)

      if "align=" in rend:
        rend, align = self.get_id("align", rend)

      if hnString in ['h1', 'h2'] and "title=" in rend:
        rend, title = self.get_id("title", rend)
        title = title.replace("'","&#39;") # escape any ' in the title string
        title = "title='{}'".format(title)

      if " break" in rend:
        break_wanted = True;
      elif " nobreak" in rend:
        break_wanted = False;
      rend = re.sub(" (no)?break", "", rend)

    # Check for garbage on .hn line (possible PP error putting title there)
    #
    if rend.strip():
      self.warn_w_context(".hn directive contains extraneous text: {}".format(rend), self.cl)

    if not align:
      align = (alignDefault if alignDefault else 'l') # default to left if no specification found

    if align != alignDefault:
      if align == "l":
        hcss += "text-align: left; "
      elif align == "r":
        hcss += "text-align: right; "
      elif align == "c":
        hcss += "text-align: center; "
      else:
        self.crash_w_context("Incorrect align= value (not c, l, or r):", self.cl)

    if hnString in ['h1', 'h3']:        # I'm not sure why we have h3 defaulting to "break" as that seems odd
      if not break_wanted:
        hcss += "page-break-before: auto; "
      else:
        hcss += "page-break-before: always; "

    elif hnString == 'h2':
      hcss += "page-break-before:auto; " # always have this on an <h2> element; if a break
                                         # is needed we'll have the <h2> inside a
                                         # <div class='chapter'> to force one. If it's not on
                                         # the <h2> then epubmaker's CSS for <h2> will override
                                         # and may force a second page break

    else: # h4-h6
      if break_wanted:
        hcss += "page-break-before: always; "
      else:
        hcss += "page-break-before: auto; "


    if hnString in ['h1', 'h4', 'h5', 'h6']: # for h1, h4-6 default 1 before 1 after
      hcss += "margin-top: {}em; ".format(self.pvs if self.pvs else 1)
      self.pvs = 1

    elif hnString == 'h2': # else for h2 default 4 before, 2 after
      hcss += "margin-top: {}em; ".format(self.pvs if self.pvs else 4)
      self.pvs = 2

    elif hnString == 'h3': # else for h3 default 2 before, 1 after
      hcss += "margin-top: {}em; ".format(self.pvs if self.pvs else 2)
      self.pvs = 1

    #Check for possible error of having a dot directive immediately after a .hn
    if self.cl < len(self.wb) and self.wb[self.cl+1].startswith("."):
      self.warn_w_context("Warning: dot-directive should not immediately follow .hn directive: {}".format(self.wb[self.cl+1]),
        self.cl)

    del self.wb[self.cl] # the .h line

    # if we have .bn info after the .h and before the header join them together
    if self.bnPresent and self.is_bn_line(self.wb[self.cl]):
      i = self.cl
      if i < len(self.wb) - 1:
        self.wb[i] = self.wb[i] + self.wb[i+1]
        del self.wb[i+1]
    s = re.sub(r"\|\|", "<br> <br>", self.wb[self.cl]) # required for epub
    s = re.sub("\|", "<br>", s)
    t = []

    endDiv = False
    if hnString == 'h1': # always want a <div> around the <h1>
      t.append("<div>")
      endDiv = True

    elif hnString == 'h2': # always want a div for <h2>. If it's not a no-break, give it class='chapter'
      if break_wanted:
        t.append("<div class='chapter'>") # will force file break
        self.css.addcss("[1576] .chapter { clear: both; page-break-before: always;}")
      else:
        t.append("<div>")
      endDiv = True

    if pnum != "" and (self.pnshow or self.pnlink):
      if hnString in ['h3', 'h4', 'h5', 'h6']:
        t.append("<div>")
        endDiv = True
      if self.pnshow:
        if self.nregs["pnstyle"] == "title" or "x" in self.debug:
          t.append("  <span class='pageno' title='{0}' id='Page_{0}' ></span>".format(pnum)) # new 3.24M
        else:
          t.append("  <span class='pageno' id='Page_{0}' >{0}</span>".format(pnum))
      elif self.pnlink:
        t.append("  <a id='Page_{0}'></a>".format(pnum))

    if hnString in ['h1', 'h2'] or (pnum != "" and (self.pnshow or self.pnlink)):
      tempbl = "  "
    else:
      tempbl = ""
    if id != "":
      t.append("{}<{} id='{}' style='{}' {}>{}</{}>".format(tempbl, hnString, id, hcss, title, s, hnString))
    else:
      t.append("{}<{} style='{}' {}>{}</{}>".format(tempbl, hnString, hcss, title, s, hnString))

    if endDiv:
      t.append("</div>")

    self.wb[self.cl:self.cl+1] = t
    self.cl += len(t)


  # h1
  def doH1(self):

    self.doHnHTML('h1')

  # h2
  def doH2(self):

    self.doHnHTML('h2')

  # h3
  def doH3(self):

    self.doHnHTML('h3')

  # h4
  def doH4(self):

    self.doHnHTML('h4')

  # h5
  def doH5(self):

    self.doHnHTML('h5')

  # h6
  def doH6(self):

    self.doHnHTML('h6')


  # .sp n
  # if a space is encountered. for HTML drop it to the next
  # displayable item and generate a top margin.
  def doSpace(self):
    m = re.match(r"\.sp (\d+)", self.wb[self.cl])
    if m:
      howmany = int(m.group(1))
      self.pvs = max(howmany, self.pvs)  # honor if larger than current pvs
      del self.wb[self.cl]
    else:
      self.crash_w_context("malformed .sp directive", self.cl)

  # .fs
  # change font size for following paragraphs
  # em and % only for scalable text in readers
  #   .fs 0.8em  set font size to 0.8em
  #   .fs 80%    set font size to 80%
  #   .fs push   saves current font size on the fsstack
  #   .fs        shortcut, pop fsstack (if any) and reset font size to that value, or
  #              reset font size to 100% if fsstack was empty
  def doFontSize(self):
    if ".fs" == self.wb[self.cl]: # .fs with no args: pops fsstack and resets to that value, or resets to 100%
      if self.fsstack:                # any pushed value?
        self.fsz = self.fsstack.pop() # yes, use it
      else:
        self.fsz = "100%"             # no, reset font size to 100%

    else: # something specified
      m = re.match(r"\.fs +([^ ]+) *%$", self.wb[self.cl])  # % form?
      if m:
        self.fsz = m.group(1) + "%"
        self.wb[self.cl] = ""
      m = re.match(r"\.fs +([^ ]+) *em$", self.wb[self.cl]) # em form?
      if m:
        self.fsz = m.group(1) + "em"
        if self.fsz == "1em":
          self.fsz = "1.0em"  # reset to standard format for our purposes
        self.wb[self.cl] = ""
      m = re.match(r"\.fs +push$", self.wb[self.cl])   # push form?
      if m:
        self.fsstack.append(self.fsz)
        self.wb[self.cl] = ""

      if ".fs" in self.wb[self.cl]:    # was it handled? if not, crash
        self.crash_w_context("malformed .fs directive", self.cl)

    del self.wb[self.cl]

  # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  # check that image file exists
  #
  def checkIllo(self, fname): # assure that fn exists in images folder
    if " " in fname:
      self.warn("cannot have spaces in illustration filenames: {}".format(fname))
    if re.search("[A-Z]", fname):
      self.warn("illustration filenames must be lower case: {}".format(fname))
    if self.imageDirectoryOK:
      if not fname in self.imageDict:
        self.warn("file {} not in images folder".format(fname))
      else:
        self.imageDict[fname] += 1
    else:
      self.warn("image checking bypassed; unable to open images folder")


  # .il illustrations
  # .il id=i01 fn=illus-fpc.jpg w=332 alt=illus-fpcf.jpg
  # .ca Dick was taken by surprise.

  def doIllo(self):

    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    # given the .il line, parse all arguments
    # returns an "ia" dictionary:
    #    "ifn"    fn="image-001.jpg"
    #    "link"   optional link="image-001f.jpg"
    #    "cw"     optional caption width ("50%", "%" only)
    #    "align"  (l)eft, (c)enter, (r)ight
    #    "iw"     requested browser image width, in percent
    #    "ew"     requested epub image width, in percent
    #    "eh"     epub height (experimental)
    #    "cj"     caption justification
    #    "id"     user-supplied id for image
    #    "alt"    alternate text for image
    #    "pageno" page number
    #
    def parse_illo(s):
      s0 = s[:]  # original .il line
      ia = {}

      # primary image filename
      ifn = ""
      if "fn=" in s:
        s, ifn = self.get_id("fn", s)
      else:
        self.fatal("no display file specified in {}".format(s0))
      self.checkIllo(ifn)
      ia["ifn"] = ifn

      # link to alternate (larger) image
      link = ""
      if "link=" in s:
        s, link = self.get_id("link", s)
        self.checkIllo(link)
      ia["link"] = link

      # optional caption width
      cw = ""
      if "cw=" in s:
        s, cw = self.get_id("cw",s)
        if "%" not in cw:
          self.fatal("caption width must be specified in percent")
      ia["cw"] = cw

      # align attributes. l, c, r, left, center, right
      img_align = "c" # default
      if "align=" in s:
        s, s1 = self.get_id("align", s)
        img_align = s1[0]  # use first letter "right" -> "r"
      ia["align"] = img_align

      # user-requested image width
      # can be pixels (px) or percent (%) at this point
      iw = ""
      if "w=" in s:
        s, iw = self.get_id("w", s)
        # if not "%" in iw:
        #   self.fatal("width, if specified, must be in percent")
      ia["iw"] = iw
      if (not iw.endswith("%")) and (not iw.endswith("px")):
        self.warn("image width (w=) does not end in px or %. The image will not display properly:\n    {}".format(s0))

      # user-requested epub width in %
      ew = ""
      if "ew=" in s:
        s, ew = self.get_id("ew", s)
        if not "%" in ew:
          self.fatal("epub width, if specified, must be in percent")
      ia["ew"] = ew

      # user-requested epub height in %
      eh = ""
      if "eh=" in s:
        s, eh = self.get_id("eh", s)
        if not "%" in eh:
          self.fatal("epub height, if specified, must be in percent")
      ia["eh"] = eh

      # caption justification; (l)eft, (c)enter, (r)ight, (f)ull
      my_cj = ""
      if "cj=" in s:
        s, cj = self.get_id("cj",s)
        my_cj = cj[0]
      ia["cj"] = my_cj

      # user-requested id
      iid = ""
      if "id=" in s:
        s, iid = self.get_id("id",s)
        iid = "id='{}' ".format(iid)  # fix for missing id= problem
      ia["id"] = iid

      # alt text for image
      alt = ""
      if "alt=" in s:
        s, alt = self.get_id("alt",s)
        alt = re.sub("'","&#39;",alt) # escape any '
      ia["alt"] = alt

      # page number
      pageno = ""
      if "pn=" in s:
        s, pageno = self.get_id("pn",s)
      ia["pageno"] = pageno
      # below not needed; all validation happens in separate pass
      #if pageno:
      #  m = re.match(r"\d+|[iIvVxXlLcCdDmM]+$", pageno)
      #  if not m:
      #    self.warn("Non-numeric, non-Roman page number {} specified: {}".format(pageno, s0))

      # caption model (ignored in HTML)
      if "cm=" in s:
        s, cm = self.get_id("cm",s)

      # no "=" should remain in .il string
      if "=" in s:
        s = re.sub("\.il", "", s).strip()
        self.warn_w_context("unprocessed value in illustration: {}".format(s), self.cl)
      return(ia)

    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    # entry point to process illustration (HTML)

    ia = parse_illo(self.wb[self.cl]) # parse .il line

    caption_present = False
    try:
      caption_present = self.wb[self.cl+1].startswith(".ca")
    except:
      pass

    # build the CSS for this illustration
    #
    # using a @media handheld, we specify float:left inside @media, even though it would
    # already be set to that using normal CSS cascading. Epubmaker removes float:left
    # from the first figleft definition (breaking the cascade) but, perhaps due to an
    # oversight, it doesn't remove float:left inside the @media handheld.

    if ia["align"] == "c":
      self.css.addcss("[1600] .figcenter { clear: both; max-width: 100%; margin: 2em auto; text-align: center; }")
      if caption_present:
          self.css.addcss("[1601] div.figcenter p { text-align: center; text-indent: 0; }")
      self.css.addcss("[1608] .figcenter img { max-width: 100%; height: auto; }")

    if ia["align"] == "l":
      self.css.addcss("[1600] .figleft { clear: left; float: left; max-width: 100%; margin: 0.5em 1em 1em 0; text-align: left; }")
      if caption_present:
          self.css.addcss("[1601] div.figleft p { text-align: center; text-indent: 0; }")
      self.css.addcss("[1602] .x-ebookmaker .figleft { float: left; }")
      self.css.addcss("[1608] .figleft img { max-width: 100%; height: auto; }")

    if ia["align"] == "r":
      self.css.addcss("[1600] .figright { clear: right; float: right; max-width: 100%; margin: 0.5em 0 1em 1em; text-align: right; }")
      if caption_present:
          self.css.addcss("[1601] div.figright p { text-align: center; text-indent: 0; }")
      self.css.addcss("[1602] .x-ebookmaker .figright { float: right; }")
      self.css.addcss("[1608] .figright img { max-width: 100%; height: auto; }")

    # make CSS names from igc counter
    idn = "id{:03d}".format(self.igc)
    ign = "ig{:03d}".format(self.igc)
    icn = "ic{:03d}".format(self.igc)

    # build illustration width info
    lookup1610 = "[1610] .idn {{ width:{}; }}".format(ia["iw"])
    build1610a = "[1610] .{} {{ width:{}; }}".format(idn, ia["iw"]) # the HTML illustration width

    if ia['ew'] == "":
      if ia["iw"] != "":
        ia["ew"] = ia["iw"]
      else:
        self.warn("cannot determine epub image width, 50% assumed so ppgen can continue: {}".format(self.wb[self.cl]))
        ia["ew"] = "50%"  # assume a value to allow calculations below to work

    # if epub width in pixels, convert it now
    if "px" in ia["ew"]:
      my_width = int(re.sub("px", "", ia["ew"]))
      ia["ew"] = "{}%".format(min(100, int(100*my_width/800)))

    if ia['align'] == 'c':
      my_width = int(re.sub("%", "", ia["ew"]))
      my_lmar = (100 - my_width) // 2
      my_rmar = 100 - my_width - my_lmar
      lookup1610 += "[1610] .x-ebookmaker  .idn {{ margin-left:{}%; width:{}; }}".format(my_lmar, ia["ew"])
      build1610b = "[1610] .x-ebookmaker  .{} {{ margin-left:{}%; width:{}; }}".format(idn, my_lmar, ia["ew"])
    else:  # floated l or right
      lookup1610 += "[1610] .x-ebookmaker .idn {{ width:{}; }}".format(ia["ew"])
      build1610b = "[1610] .x-ebookmaker .{} {{ width:{}; }}".format(idn, ia["ew"])

    # if user has set caption width (in percent) we use that for both HTML and epub.
    # If user hasn’t specified it, we use the width of the image in a browser or
    # 80% in epub using a @media handheld because we cannot rely on max-width on these devices
    #
    lookup161113 = ""
    build1611 = ""
    build1613 = ""
    if caption_present:

      ocw, oml, omr = (0,0,0)  # width, left, right margins as percent
      if ia["cw"] != "":  # user has set caption width
        ocw = int(re.sub("%", "", ia["cw"]))  # numeric part
        if ia["cj"] == 'c' or ia["cj"] == '' or ia["cj"] == 'f':  # centered or justified
          oml = (100 - ocw) // 2
          omr = 100 - ocw - oml
        if ia["cj"] == 'l':  # left and right need to incorporate caption width
          oml = (100 - ocw) // 2  # fixed
          omr = 100 - ocw - oml
        if ia["cj"] == 'r':
          omr = (100 - ocw) // 2  # fixed
          oml = 100 - ocw - omr
        lookup161113 += "[1611] .icn {{ width:{}%; margin-left:{}%; margin-right:{}%; }} ".format(ocw, oml, omr)
        build1611 = "[1611] .{} {{ width:{}%; margin-left:{}%; margin-right:{}%; }} ".format(icn, ocw, oml, omr)
      else:
        lookup161113 += "[1611] .icn {{ width:100%; }} ".format(ia["iw"])
        build1611 = "[1611] .{} {{ width:100%; }} ".format(icn, ia["iw"])

      if ia["cj"] != "":
        if ia["cj"] == 'l':
          lookup161113 += "[1613] div.icn p { text-align:left; } "
          build1613 = "[1613] div.{} p {{ text-align:left; }} ".format(icn)
        elif ia["cj"] == 'r':
          lookup161113 += "[1613] div.icn p { text-align:right; } "
          build1613 = "[1613] div.{} p {{ text-align:right; }} ".format(icn)
        elif ia["cj"] == 'c':
          lookup161113 += "[1613] div.icn p { text-align:center; } "
          build1613 = "[1613] div.{} p {{ text-align:center; }} ".format(icn)
        elif ia["cj"] == 'f':
          lookup161113 += "[1613] div.icn p { text-align:justify; } "
          build1613 = "[1613] div.{} p {{ text-align:justify; }} ".format(icn)

    lookup1614 = "[1614] .ign {{ width:100%; }} ".format(ia["iw"])
    build1614 = "[1614] .{} {{ width:100%; }} ".format(ign, ia["iw"])

    # see if we have an image with these characteristics defined already
    saved1610 = self.imageCssDict.get(lookup1610) # try to get the definition info
    if lookup161113:
      saved161113 = self.imageCssDict.get(lookup161113)
    saved1614 = self.imageCssDict.get(lookup1614)
    bumpcounter = False
    if not saved1610: # if no matching [1610] found
      self.imageCssDict[lookup1610] = idn # add it to the dictionary, remembering the idn value
      self.css.addcss(build1610a) # add the [1610] css we just built
      self.css.addcss(build1610b)
      bumpcounter = True
    else:
      idn = saved1610
    if lookup161113:
      if not saved161113: # if no matching [1611/13] found
        self.imageCssDict[lookup161113] = icn # add it to the dictionary, remembering the icn value
        self.css.addcss(build1611) # add the [1611] css we just built
        if build1613:
          self.css.addcss(build1613) # add the [1613] css we just built
        bumpcounter = True
      else:
        icn = saved161113
    if not saved1614: # if no matching [1614] found
      self.imageCssDict[lookup1614] = ign # add it to the dictionary, remembering the ign value
      self.css.addcss(build1614) # add the [1614] css we just built
      bumpcounter = True
    else:
      ign = saved1614
    if bumpcounter:
      self.igc += 1 # bump the counter if we used any of the new CSS

    # create replacement stanza for illustration
    u = []

    #if self.pvs > 0: # pending vertical space?
    #  mtop = " style='margin-top: {}em; '".format(self.pvs)
    #  self.pvs=0
    #else:
    mtop = "" # prepare for experimental version that applies pvs to illos

    if ia["align"] == "c":  # with fix for missing id= problem
      u.append("<div {}{} class='figcenter {}'>".format(ia["id"], mtop, idn))
    if ia["align"] == "l":
      u.append("<div {}{} class='figleft {}'>".format(ia["id"], mtop, idn))
    if ia["align"] == "r":
      u.append("<div {}{} class='figright {}'>".format(ia["id"], mtop, idn))


    page_link = ""
    if ia["pageno"] != "":
      if self.pnshow:
        if self.nregs["pnstyle"] == "title" or "x" in self.debug:
          u.append("<span class='pageno' title='{0}' id='Page_{0}' ></span>".format(ia["pageno"])) # new 3.24M
        else:
          u.append("<span class='pageno' id='Page_{0}' >{0}</span>".format(ia["pageno"]))
        #u.append("<span class='pageno' title='{0}' id='Page_{0}' ></span>".format(ia["pageno"]))
      elif self.pnlink:
        if ia["link"]:
          page_link = "id='Page_{0}' ".format(ia["pageno"])
        else:
          page_link = "<a id='Page_{0}'></a>".format(ia["pageno"])
      ia["pageno"] = ""

    # 16-Apr-2014: placed link in div
    if ia["link"] != "": # link to larger image specified in markup
      u.append("<a {}href='images/{}'><img src='images/{}' alt='{}' class='{}'></a>".format(page_link, ia["link"],
                                                                                              ia["ifn"], ia["alt"], ign))
    else: # no link to larger image
      u.append("{}<img src='images/{}' alt='{}' class='{}'>".format(page_link, ia["ifn"], ia["alt"], ign))

    rep = 1 # source lines to replace

    # is the .il line followed by a caption line?
    if caption_present:
      u.append("<div class='{}'>".format(icn))
      if self.wb[self.cl+1] == ".ca": # multiline
        rep += 1
        j = 2
        s = self.wb[self.cl+j] + "<br>  " #RT Added 2 blank characters to fix issue with character deletion in captions
        rep += 1
        j += 1
        while ((self.cl + j) < len(self.wb)) and self.wb[self.cl+j] != ".ca-":
          s += self.wb[self.cl+j] + "<br>  " #RT Added 2 blank characters to fix issue with character deletion in captions
          j += 1
          rep += 1
        if (self.cl + j) == len(self.wb):
          self.crash_w_context("Unclosed .ca directive.", self.cl)
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
    self.crash_w_context("malformed .in directive", self.cl)

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
    self.crash_w_context("malformed .ll directive", self.cl)

  # .ti temporary indent
  def doTi(self):
    s = self.wb[self.cl].split()
    if len(s) > 1:         # will always be true, as we converted ".ti" with no argument to ".ti 2" earlier
      # special case: forcing a .ti of 0
      if s[1].isdigit() or s[1].startswith('-') or s[1].startswith('+'):
        if int(s[1]) == 0:
          self.regTI = -1000
        else:
          self.regTI += int(s[1])
      elif s[1] == "end": # remove persistent temporary indent?
        self.regTI = 0
        self.regTIp = 0
      else:
        self.crash_w_context("Malformed .ti directive.", self.cl)
    if len(s) > 2:
      if s[2] == "begin":
        self.regTIp = self.regTI
      elif s[2] == "end":
        self.regTIp = 0
      else:
        self.crash_w_context("Malformed .ti directive.", self.cl)
    else:
      self.regTIp = 0 # force end of persistent temporary indent if .ti found without "begin"
    del self.wb[self.cl]

  # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  # no-fill, centered (HTML)
  # takes no internal justification commands
  # note: mo is currently ignored for centered blocks.
  def doNfc(self, mo):
    s = self.fetchStyle(nfc=True)
    startloc = self.cl
    i = self.cl
    t = []
    t.append("")
    nf_pdi = False
    nf_pdc = False

    if self.pindent:
      t.append("<div class='nf-center-c0'>")
    else:
      t.append("<div class='nf-center-c1'>")

    if not s:
      t.append("  <div class='nf-center'>")
    else:
      t.append("<div class='nf-center' style='{}'>".format(s))

    if self.pindent:
      self.css.addcss("[1876] .nf-center-c0 { text-align: left; margin: 0.5em 0; }")  # 17-Jul-2014
    else:
      self.css.addcss("[1876] .nf-center-c1 { text-align: left; margin: 1em 0; }")

    self.css.addcss("[1873] .nf-center { text-align: center; }")
    i += 1
    printable_lines_in_block = 0
    pending_mt = 0
    while self.wb[i] != ".nf-":

      if self.bnPresent and self.is_bn_line(self.wb[i]):  # if this line is bn info then just leave it in the output as-is
        i += 1
        continue

      if self.wb[i].startswith(".dc"):
        self.warn(".dc not supported within .nf c block: {}".format(self.wb[i]))
        del self.wb[i]
        continue

      if self.wb[i].startswith(".di"):
        self.warn(".di not supported within .nf block: {}".format(self.wb[i]))
        del self.wb[i]
        continue

      if "" == self.wb[i]:
        pending_mt += 1
        i += 1
        continue
      if pending_mt > 0:
        if nf_pdc:
          nf_pdc = False
          t.append("    <div  class='{}' style='margin-top: {}em; '>".format(self.pdc, pending_mt) + self.wb[i].strip() + "</div>")
        else:
          t.append("    <div style='margin-top: {}em; '>".format(pending_mt) + self.wb[i].strip() + "</div>")
        printable_lines_in_block += 1
        pending_mt = 0
      else:
        if nf_pdc:
          nf_pdc = False
          t.append("    <div  class='{}'>".format(self.pdc) + self.wb[i].strip() + "</div>")
        else:
          t.append("    <div>" + self.wb[i].strip() + "</div>")
        printable_lines_in_block += 1
      i += 1
    # at block end.
    if printable_lines_in_block == 0:
        self.crash_w_context("empty .nf block", i)
    # there may be a pending mt at the block end.
    if pending_mt > 0:
      if "<div style='" not in t[-1]:
        t[-1] = re.sub(r"<div", "<div style='margin-bottom: {}em; '".format(pending_mt), t[-1])
      else:
        t[-1] = re.sub(r"<div style='", "<div style='margin-bottom: {}em; ".format(pending_mt), t[-1])
      pending_mt = 0
    t.append("  </div>")
    t.append("</div>")
    t.append("")
    endloc = i
    self.wb[startloc:endloc+1] = t
    self.cl = startloc + len(t)

  # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  # no-fill, block. block type specified. any type except centered
  #
  # in epub/mobi, the @media handheld ... (explain....)
  def doNfb(self, nft, mo):
    # any poetry triggers the same CSS
    nf_pdc = False
    nf_pdi = False
    if 'b' == nft:
      self.css.addcss("[1215] .lg-container-b { text-align: center; }")  # alignment of entire block
      self.css.addcss("[1216] .x-ebookmaker .lg-container-b { clear: both; }")
    if 'l' == nft:
      self.css.addcss("[1217] .lg-container-l { text-align: left; }")
      self.css.addcss("[1218] .x-ebookmaker .lg-container-l { clear: both; }")
    if 'r' == nft:
      self.css.addcss("[1219] .lg-container-r { text-align: right; }")
      self.css.addcss("[1220] .x-ebookmaker .lg-container-r { clear: both; }")

    self.css.addcss("[1221] .linegroup { display: inline-block; text-align: left; }")  # alignment inside block
    self.css.addcss("[1222] .x-ebookmaker .linegroup { display: block; margin-left: 1.5em; }")
    if mo:
      self.css.addcss("[1223] .linegroup .group0 { margin: 0 auto; }")
    else:
      self.css.addcss("[1223] .linegroup .group { margin: 1em auto; }")
    self.css.addcss("[1224] .linegroup .line { text-indent: -3em; padding-left: 3em; }")

    self.css.addcss("[1225] div.linegroup > :first-child { margin-top: 0; }")

    ssty = ""
    s = self.fetchStyle() # supplemental style
    if s:
      ssty = " style='{}'".format(s)
    startloc = self.cl
    i = self.cl
    t = []

    if 'b' == nft:
      t.append("<div class='lg-container-b'{}>".format(ssty))
    elif 'l' == nft:
      t.append("<div class='lg-container-l'{}>".format(ssty))
    elif 'r' == nft:
      t.append("<div class='lg-container-r'{}>".format(ssty))
    t.append("  <div class='linegroup'>")
    if mo:
      t.append("    <div class='group0'>")
    else:
      t.append("    <div class='group'>")

    i += 1
    cpvs = 0
    printable_lines_in_block = 0
    while self.wb[i] != ".nf-":

      # if this line is just bn info then just leave it in the output as-is
      if self.bnPresent and self.is_bn_line(self.wb[i]):
        i += 1
        continue

      # a centered line inside a no-fill block (Note: support for drop-cap not implemented here)
      m = re.match(r"\.ce (\d+)", self.wb[i])
      if m:
        count = int(m.group(1))
        i += 1 # skip the .ce
        while count > 0 and i < len(self.wb):
          if self.bnPresent and self.is_bn_line(self.wb[i]):  # if this line is bn info then just leave it in the output as-is
            i += 1
            continue
          pst = "text-align: center; "
          if cpvs > 1:
            spvs = "margin-top: {}em; ".format(cpvs)
          else:
            spvs = ""
          cpvs = 0;
          if self.wb[i].startswith(".dc"):
            self.warn(".dc not supported on centered line within .nf block: {}".format(self.wb[i]))
          elif self.wb[i].startswith(".di"):
            self.warn(".di not supported within .nf block: {}".format(self.wb[i]))
          else:
            t.append("      <div style='{}{}'>{}</div>".format(pst, spvs, self.wb[i]))
            printable_lines_in_block += 1
          i += 1
          count -= 1
        continue

      # a right-justified line inside a no-fill block (Note: support for drop-cap not implemented here)
      m = re.match(r"\.rj (\d+)", self.wb[i])
      if m:
        count = int(m.group(1))
        i += 1 # skip the .rj
        while count > 0:
          if self.bnPresent and self.is_bn_line(self.wb[i]):  # if this line is bn info then just leave it in the output as-is
            i += 1
            continue
          pst = "text-align: right; "
          if cpvs > 1:
            spvs = "margin-top: {}em; ".format(cpvs)
          else:
            spvs = ""
          cpvs = 0;
          if self.wb[i].startswith(".dc"):
            self.warn(".dc not supported on right-justified line within .nf block: {}".format(self.wb[i]))
          elif self.wb[i].startswith(".di"):
            self.warn(".di not supported within .nf block: {}".format(self.wb[i]))
          else:
            t.append("      <div style='{}{}'>{}</div>".format(pst, spvs, self.wb[i]))
            printable_lines_in_block += 1
          i += 1
          count -= 1
        continue

      if self.wb[i].startswith(".dc"):
        nf_pdc = True
        self.doDropcap(i, type="nf")
        continue

      if self.wb[i].startswith(".di"):
        self.warn(".di not supported within .nf block: {}".format(self.wb[i]))
        del self.wb[i]
        continue

      if self.wb[i] == "":
        if cpvs == 0:
          t.append("    </div>")
          t.append("    <div class='group'>")
          cpvs += 1
        else:
          cpvs += 1
      else:
        # need to calculate leading space for this line.
        # there may be some tags *before* the leading space
        # (Not as of 3.52a, which places them after the leading space.)
        # But there may still be .bn info before leading space, so account for it
        tmp = self.wb[i][:]
        ss = ""
        #m = re.match(r"^(<[^>]+>|⑯\w+⑰)", tmp)
        m = re.match(r"^(⑯\w+⑰)", tmp)
        while m:
          ss += m.group(0)
          #tmp = re.sub(r"^<[^>]+>|⑯\w+⑰", "", tmp, 1)
          tmp = re.sub(r"^⑯\w+⑰", "", tmp, 1)
          #m = re.match(r"^<[^>]+>|⑯\w+⑰", tmp)
          m = re.match(r"⑯\w+⑰", tmp)
        leadsp = len(tmp) - len(tmp.lstrip())
        if cpvs > 1:
          spvs = "style='margin-top: {}em; ' ".format(cpvs)
        else:
          spvs = ""
        if leadsp > 0: # (Note: support for drop-cap not fully implemented for indented lines)
          if nf_pdc:
            self.warn("drop-cap may not work well on indented line in .nf block: {}".format(ss+tmp))
            nf_pdc = False
            iclass = "in{}dc".format(leadsp)  # create an indent class
            iamt = "0"
            t.append("      <div class='linedc {0} {1}' {2}>{3}</div>".format(iclass, self.pdc, spvs, ss+tmp.lstrip()))
          else:
            iclass = "in{}".format(leadsp)  # create an indent class
            if self.nregsusage["nf-spaces-per-em"] > 1:
              iclass += "_{}".format(self.nregsusage["nf-spaces-per-em"])
            #iamt = str(-3 + leadsp/2) # calculate based on -3 base
            divisor = float(self.nregs["nf-spaces-per-em"])
            iamt = str(3 + round(leadsp/divisor, 1)) # calculate based on 2 spaces per em, and
                                               #  add in the 3em base padding-left.
            t.append("      <div class='line {0}' {1}>{2}</div>".format(iclass, spvs, ss+tmp.lstrip()))
          self.css.addcss("[1227] .linegroup .{} {{ padding-left: {}em; }}".format(iclass, iamt))
          printable_lines_in_block += 1
        else:
          if nf_pdc:
            nf_pdc = False
            t.append("    <div  class='linedc {0}' {1}>{2}</div>".format(self.pdc, spvs, ss+tmp))
          else:
            t.append("      <div class='line' {0}>{1}</div>".format(spvs, ss+tmp))
          printable_lines_in_block += 1
        cpvs = 0  # reset pending vertical space
      i += 1

    # at block end.
    if printable_lines_in_block == 0:
        self.fatal("empty .nf block")

    # there may be a pending mt at the block end.
    if cpvs > 1:
      if "style='" in t[-1]:
        t[-1] = re.sub(r"style='", "style='margin-bottom: {}em; ".format(cpvs), t[-1])
      else:
        t[-1] = re.sub(r"<div", "<div style='margin-bottom: {}em; '".format(cpvs), t[-1])
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
    m = re.match(r"\.nf-", self.wb[self.cl]) ### this can't happen, can it?  Also, HTML processing doesn't verify .nf- occurs
    if m:
      self.crash_w_context("attempting to close an unopened block with {}".format(self.wb[self.cl]),self.cl)
    nf_handled = False
    m = re.match(r"\.nf (.)", self.wb[self.cl])
    if m:
      nftype = m.group(1) # c, l, b or r
      margin_override = False
      if re.match(r"\.nf . 0", self.wb[self.cl]):
        margin_override = True # ignored in text
      if nftype == 'c':
        nf_handled = True
        self.doNfc(margin_override)
      elif nftype in ['l','r','b']:
        nf_handled = True
        self.doNfb(nftype, margin_override)
    if not nf_handled:
      self.crash_w_context("invalid .nf option: {}".format(self.wb[self.cl]),self.cl)

  # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

  # .fm footnote mark (HTML)
  def doFmark(self):
    rend = True
    lz = False
    m = re.match(r"\.fm (.*)", self.wb[self.cl])
    if m:
      options = m.group(1)
      if "norend" in options:
        rend = False
      if "rend=" in options:
        options, rendvalue = self.get_id("rend", options)
        if rendvalue == "no" or rendvalue == "norend" or not "h" in rendvalue:
          rend = False
      rendafter = False
      if "rendafter=" in options:
        options, rendaval = self.get_id("rendafter", options)
        if rendaval.startswith("y"):
          rendafter = True
      if "lz=" in options:
        options, lzvalue = self.get_id("lz", options)
        if "h" in lzvalue:
          lz = True
        else:
          rend = False  # If this .fm is a landing zone for text but not html, don't do rend for it either
      if "=" in options:
        self.warn("Unrecognized option in .fm command: {}".format(self.wb[self.cl]))
    if rend and ((not lz) or (lz and len(self.fnlist))):
      if self.pvs > 0:
        self.wb[self.cl] = ("<hr style='border: none; border-bottom: thin solid; width: 10%; margin-left: 0; " +
                            "margin-top: {}em; text-align: left; '>".format(self.pvs))
        self.pvs = 0
      else:
        self.wb[self.cl] = ("<hr style='border: none; border-bottom: thin solid; width: 10%; margin-left: 0; " +
                            "margin-top: 1em; text-align: left; '>")
      self.cl += 1
    else:
      rend = False
      del self.wb[self.cl]
    if lz:
      # emit saved footnotes
      if len(self.fnlist): # make sure there's something to generate
        first_fn = True
        for t in self.fnlist:
          for s in t:
            if first_fn:
              first_fn = False
              if self.pvs: # handle adjusting top margin for first footnote if necessary
                if s.startswith("<div class='footnote' id='f"):
                  s2 = "margin-top: {}em; ".format(self.pvs)
                  self.pvs = 0
                  s, count = re.subn("style='font-size", "style='{}font-size".format(s2), s, 1)
                  if not count:
                    self.warn("Footnote HTML substitution failed for: {}::{}".format(s, s2))
                else:
                  self.warn("Unexpected footnote HTML: {}".format(s))
            if self.cl < len(self.wb):
              self.wb.insert(self.cl, s)
            else:
              self.wb.append(s)
            self.cl += 1
        del self.fnlist[:]  # remove everything we handled
        self.fnlist = []
        if rend and rendafter:
          self.wb.append("<hr style='border: none; border-bottom: thin solid; width: 10%; margin-left: 0; margin-top: 1em; text-align: left; '>")
          self.cl += 1
      else:
        self.warn_w_context("No footnotes saved for this landing zone.", self.cl)

  # Footnotes (HTML)
  # here on footnote start or end
  # handle completely different for paragraph indent or block style
  # Note: messages for invalid footnote names were issued during pre-processing
  def doFnote(self):

    self.css.addcss("[1199] sup { vertical-align: top; font-size: 0.6em; }")

    m = re.match(r"\.fn-", self.wb[self.cl])
    if m: # footnote ends
      self.wb[self.cl] = "</div>"
      self.cl += 1

      self.fszpop('.fn')

      if self.footnoteLzH and not self.keepFnHere: # if special footnote landing zone in effect and not disabled for this footnote
        self.grabFootnoteH()

        # restore self.pvs after footnote if not being generated here
        temp_pvs = self.fn_pvs_stack.pop() # get prior self.pvs value
        if temp_pvs != -1:
          self.pvs = temp_pvs
      return

    m = re.match(r"\.fn (\d+)( |$)(lz=here|hlz=here)?", self.wb[self.cl]) # First try numeric footnote
    if m: # footnote start
      fnname = m.group(1)
      self.keepFnHere = True if (m.group(3)) else False # test for lz=here and remember for .fn- processing
    else:
      m = re.match(r"\.fn ([A-Za-z0-9\-_\:\.]+)( |$)(lz=here|hlz=here)?", self.wb[self.cl]) # then named
      if m:
        fnname = m.group(1)
        self.keepFnHere = True if (m.group(3)) else False # test for lz=here and remember for .fn- processing
      else:
        fnname = "<<Invalid footnote name; see messages>>"
    if self.keepFnHere and not self.footnoteLzH:
      if m.group(3).startswith("hlz"):
        self.warn(".fn specifies hlz=here but landing zones not in effect for HTML output:{}".format(self.wb[self.cl]))
      elif m.group(3).startswith("lz") and not self.footnoteLzT and not self.footnoteLzH:
        self.warn(".fn specifies lz=here but no landing zones are in effect:{}".format(self.wb[self.cl]))

    # preserve self.pvs across footnote if not being generated here
    if self.footnoteLzH and not self.keepFnHere:
      temp_pvs = self.pvs
      self.pvs = 0
    else:
      temp_pvs = -1
    self.fn_pvs_stack.append(temp_pvs)

    myfsz = self.fsz                  # capture current font size
    self.fszpush('.fn')               # stack current size for later restoration
    if myfsz != "100%" and myfsz != "1.0em": # if font-size non-standard
      self.fsz = "100%"               # set global font size to 100% for inner elements
                                      #(we'll use the other value on our <div>)
    else:  # standard font size
      myfsz = ""

    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    if self.pindent: # indented paragraphs

      # Calculate top/bottom margins for paragraphs in footnote
      s0 = re.sub("em", "", self.nregs["psi"]) # drop the "em"
      s1 = int(float(s0)*100.0) # in tenths of ems
      s2 = (s1//2)/100 # forces one decimal place

      if myfsz:                                          # if we have a font-size override
        myfsz = " style='font-size: {}; '".format(myfsz)  # build a style string for it

      #self.css.addcss("[1430] div.footnote {}")
      self.css.addcss("[1431] div.footnote > :first-child { margin-top: 1em; }")
      self.css.addcss("[1432] div.footnote p {{ text-indent: 1em; margin-top: {0}em; margin-bottom: {1}em; }}".format(s2,s2))
      self.wb[self.cl] = "<div class='footnote' id='f{}'{}>".format(fnname, myfsz)
      if self.footnoteLzH: # if special footnote landing zone processing in effect
        self.footnoteStart = self.cl # remember where this footnote started
      self.cl += 1
      # self.wb[self.cl] = "<a href='#r{0}'>[{0}]</a> {1}".format(fnname, self.wb[self.cl])
      self.wb[self.cl] = "<a href='#r{0}'>{0}</a>. {1}".format(fnname, self.wb[self.cl])

    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    else: # block paragraphs

      half_length = max((int(self.fn_name_length/2) + 1), 2.5) # 2.5 was the old value; use that as our minimum
      margin = "{}".format(half_length)
      self.css.addcss("[1430] div.footnote {{margin-left: {0}em; }}".format(margin))
      self.css.addcss("[1431] div.footnote > :first-child { margin-top: 1em; }")
      self.css.addcss("[1432] div.footnote .label {{ display: inline-block; width: 0em; text-indent: -{0}em; text-align: right; }}".format(margin))

      # if there is a pending vertical space, include it in style
      hcss = ""
      if self.pvs > 0:
        hcss = "margin-top: {}em; ".format(self.pvs)
        self.pvs = 0

      if myfsz:                                  # if font-size override, build into style string
        hcss += "font-size: {}; ".format(myfsz)  # build a style string

      if hcss != "":
        self.wb[self.cl] = "<div class='footnote' id='f{}' style='{}'>".format(fnname, hcss)
      else:
        self.wb[self.cl] = "<div class='footnote' id='f{}'>".format(fnname)
      if self.footnoteLzH: # if special footnote landing zone processing in effect
        self.footnoteStart = self.cl # remember where this footnote started
      s = "<span class='label'><a href='#r{0}'>{0}</a>.&#160;&#160;</span>".format(fnname) #(&nbsp; replaced with &#160;)
      self.cl += 1
      self.wb[self.cl] = s + self.wb[self.cl]

  # grab a complete footnote out of self.wb and save it for later
  def grabFootnoteH(self):
    t = [] # buffer for the footnote label and text
    i = self.footnoteStart
    while i < self.cl:
      t.append(self.wb[i]) # grab a line then delete it
      del self.wb[i]
      self.cl -= 1
    self.fnlist.append(t) # when done, append complete list into fnlist for later use
    #self.cl = i


  # tables .ta r:5 l:20 r:5 or .ta rlr
  #
  # tables in HTML and derivatives use percent for geometry.
  # column widths specified in characters with 72 page width max.
  # left margin calculated and applied for epub.
  #
  # s=  summary

  def doTable(self): # HTML

    # get maximum width of specified column by scanning all rows in table
    def getMaxWidth(c, ncols):
      j = self.cl + 1
      maxw = 0
      while self.wb[j] != ".ta-":
        # blank and centered and .bn info lines are not considered
        if self.wb[j] == "" or not "|" in self.wb[j]:
          j += 1
          continue
        u = self.wb[j].split("|")
        if len(u) != ncols:
            self.crash_w_context("table has wrong number of columns:{}".format(self.wb[j]), j)
        t = re.sub(r"<.*?>", "", u[c].strip())  # adjust column width for inline tags
        if len(t) >= 4 and t[0:4] == "<th>": # if cell starts with <th> remove it
          t = t[4:]
        if len(t) >= 6 and t[0:4] == "<al=": # possible alignment directive?
          t = re.sub(r"^<al=[lrch]>", "", t, 1) # ignore any alignment directives
        if t != "<span>": # ignore <span> cells for purposes of figuring max width of this column
          maxw = max(maxw, self.truelen(t))
        j += 1
      return maxw

    def make_tb_border_class(line, data_found):
      classname = 'bb' if (data_found) else 'bt' # first part of class name
      classname += self.valid_html_hrules[line][0] # finish class name
      border_css = "[1672] ." + classname + ' '
      border_css += self.html_border_names[classname[0:2]]
      key = self.valid_html_hrules[line][1]
      border_css += self.nregs[key] +'; }'
      self.css.addcss(border_css)
      return classname

    def make_lr_border_class(prefix, spec):
      classname = prefix
      rule = self.valid_html_vrules[spec]
      classname += rule[0]
      key = rule[1]
      border_css = "[1672] ." + classname + ' '
      border_css += self.html_border_names[prefix]
      border_css += self.nregs[key] +'; }'
      self.css.addcss(border_css)
      return classname

    if self.wb[self.cl] == ".ta-":
      self.crash_w_context(".ta- found outside of table", self.cl)
    haligns = list() # 'h', 'l', 'r', or 'c'  no default; must specify
    valigns = list() # 't', 'b', or 'm' default 't'
    widths = list() # column widths
    totalwidth = 0
    il_line = self.wb[self.cl]
    border_tag = "<" + NOW + ">" # tag showing a horizontal border line is already processed

    # look for continuation characters; restore to one line (now, just look for .ta-)
    k1 = self.cl
    while k1 < len(self.wb) and self.wb[k1] != ".ta-":
      #while self.wb[k1].endswith("\\"):
      #  self.wb[k1] = re.sub(r"\\$", "", self.wb[k1])
      #  self.wb[k1] = self.wb[k1] + " " + self.wb[k1+1]
      #  del self.wb[k1+1]
      k1 += 1
    if k1 == len(self.wb):
      self.crash_w_context("missing .ta- in table starting: {}".format(s), self.cl)

    # pull out summary if present.
    tsum = ""
    if "s=" in self.wb[self.cl]:
      self.wb[self.cl], tsum = self.get_id("s", self.wb[self.cl])

    # pull out optional user-specified Epub//Mobi width %
    tw_epub = ""
    if "ew=" in self.wb[self.cl]:
      self.wb[self.cl], tw_epub = self.get_id("ew", self.wb[self.cl])
      if "%" not in tw_epub:
        self.fatal("please specify table epub width as percent, i.e. \"{0}%\" \n on line: {1}".format(tw_epub, il_line))

    # pull out optional user-specified HTML width %
    tw_html = ""
    if "w=" in self.wb[self.cl]:
      self.wb[self.cl], tw_html = self.get_id("w", self.wb[self.cl])
      if tw_html != "none" and "%" not in tw_html:
        self.fatal("please specify table HTML width as percent, i.e. \"{0}%\" \n on line: {1}".format(tw_html, il_line))

    # pull out optional id=
    tid = ""
    if "id=" in self.wb[self.cl]:
      self.wb[self.cl], tid = self.get_id("id", self.wb[self.cl])
      if tid:
        tid = " id='{}'".format(tid)

    # pull out bl= (blank line) option, but ignore in HTML except for validation
    # bl=none (PPer in total control; don't add any blank lines) or
    #    auto (add a blank line if cell wraps, unless PPer already suppiied one)
    temp = "y"
    if "bl=" in self.wb[self.cl]:
      self.wb[self.cl], temp = self.get_id("bl", self.wb[self.cl])
      temp = temp.lower()[0] # lower-case and grab first character
    if temp == "y":
      add_blank_lines = True
    elif temp == "n":
      add_blank_lines = False
    else:
      self.warn_w_context("Unexpected bl= value on .ta {} ignored; assuming y".format(temp), self.cl)

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
      m = re.match(r"\.ta ([hlcr]+)", self.wb[self.cl])
      if m:
        t0 = m.group(1) # all the specifiers
        t = list(t0) # ex: ['r','c','l','h']
        ncols = len(t) # ex: 3
        s = ".ta "
        for i,x in enumerate(t):
          cwidth = getMaxWidth(i,ncols) # width
          s += "{}t:{} ".format(t0[i],cwidth)
        self.wb[self.cl] = s.strip()  # replace with widths specified

    # if vertical alignment not specified, default to "top" now
    # .ta l:6 r:22 => .ta lt:6 rt:22
    while re.search(r"[^hlcr][hlcr]:", self.wb[self.cl]):
      self.wb[self.cl] = re.sub(r"([hlcr]):", r'\1t:', self.wb[self.cl])

    t = self.wb[self.cl].split() # ['.ta', 'lt:6', 'rt:22']
    ncols = len(t) - 1  # skip the .ta piece

    # alignment and borders
    bbefore = list() # border characters before cells
    bafter  = list() # and after cells
    borders_present = False
    j = 1
    while j <= ncols:
      u = t[j].split(':')

      appended = False
      m = re.match(r"([|=]*)(..)", u[0]) # extract border-before character(s)
      if m:
        u[0] = m.group(2)
        bspec = m.group(1)
        if bspec in ['|', '||', '=', '==']:
          class_name = make_lr_border_class('bl', bspec)
          bbefore.append(class_name)
          appended = True
          borders_present = True
        elif not bspec:
          pass
        else:
          self.warn_w_context("Unrecognized cell border specification character(s): {}".format(bspec), self.cl)
      if not appended: # if no before border appended
        bbefore.append('')

      appended = False
      m = re.match(r"([^|=]+)([|=]*)", u[1]) # extract border-after character(s)
      if m:
        u[1] = m.group(1)
        bspec = m.group(2)
        if bspec in ['|', '||', '=', '==']:
          class_name = make_lr_border_class('br', bspec)
          bafter.append(class_name)
          appended = True
          borders_present = True
        elif not bspec:
          pass
        else:
          self.warn_w_context("Unrecognized cell border specification character(s): {}".format(bspec), self.cl)
      if not appended: # if no after border appended
        bafter.append('') # assume null right border if none specified

      if not u[0][0] in ['l','c','r','h']:
        self.fatal("table horizontal alignment must be 'l', 'c', 'h', or 'r' in {}".format(self.wb[self.cl]))
      if u[0][0] == 'l':
        haligns.append("text-align: left; ")
      if u[0][0] == 'c':
        haligns.append("text-align: center; ")
      if u[0][0] == 'r':
        haligns.append("text-align: right; ")
      if u[0][0] == 'h': # hanging indent
        if not borders_present:
          haligns.append("text-align: left; text-indent: -1em; padding-left: 1em; ")
        else: # borders present, and hanging indent, need to bump the padding-left a bit
          m = re.match("(.+)em", self.nregs["html-cell-padding-left"])
          if m:
            tpadding = round(1 + float(m.group(1)), 1)
            haligns.append("text-align: left; text-indent: -1em; padding-left: {}em; ".format(tpadding))
          else:
            self.warn_w_context("Unable to calculate proper cell padding because self.nregs[\"html-cell-padding-left\"] has unexpected format: {}".format(self.nregs["html-cell-padding-left"]),
                                self.cl)
            haligns.append("text-align: left; text-indent: -1em; padding-left: 1em; ")

      if not u[0][1] in ['t','m','b']:
        self.fatal("table vertial alignment must be 't', 'm', or 'b'")
      if u[0][1] == 't':
        valigns.append("vertical-align: top; ")
      if u[0][1] == 'm':
        valigns.append("vertical-align: middle; ")
      if u[0][1] == 'b':
        valigns.append("vertical-align: bottom; ")

      try:
        widths.append(int(u[1]))
        totalwidth += int(u[1]) # no added space in HTML
      except ValueError:
        self.fatal("cell width {} is not numeric: {}".format(u[1], self.wb[self.cl]))
      j += 1

    pwidths = [None] * ncols

    # make sure we have a table
    if totalwidth == 0:
      self.fatal("no columns detected in table starting: {}".format(il_line))

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

    t = []

    s = "margin: auto; "  # start building class for table

    if self.pvs > 0:  # pending vertical space
      s += "margin-top: {}em; ".format(self.pvs)
      self.pvs=0

    # if user specified table width (in %), put in a class and attach to table
    # if user also specified table width for epub, put that in a media handheld class
    # fudge factor if ppgen calculates it: 20% to allow for an ALL CAPS (wide) column
    if tw_html != "none":
      if tw_html != "":
        s += "width: {}; ".format(tw_html)  # use what we are told
      else:
        our_width = min( 100, int(120*(totalwidth/72)) )  # limit to 100%
        left_indent_pct = (100 - our_width) // 2
        right_indent_pct = 100 - our_width - left_indent_pct
        s += "margin-left: {}%; margin-right: {}%; width: {}%; ".format( left_indent_pct, right_indent_pct, our_width )

    if borders_present:
      s += "border-collapse: {}; ".format(self.nregs["border-collapse"])

    if tw_html != "none" and tw_epub != "":
      epw = int(re.sub("%", "", tw_epub)) # as integer
      left_indent_pct = (100 - epw) // 2
      right_indent_pct = 100 - epw - left_indent_pct
    else:
      left_indent_pct = right_indent_pct = epw = 0

    lookup = (s, left_indent_pct, right_indent_pct, epw)
    try:
      ix = self.table_list.index(lookup)
    except ValueError:
      self.table_list.append(lookup)
      ix = len(self.table_list) - 1
      self.css.addcss("[1670] .table{0} {{ {1} }}".format(ix, s))
      if left_indent_pct or right_indent_pct or epw:
        self.css.addcss("[1671] .x-ebookmaker { .table{} {{ margin-left: {}%; margin-right: {}%; width: {}%; }} }".format(ix,
                                                                                                                              left_indent_pct,
                                                                                                                              right_indent_pct,
                                                                                                                              epw))

    if tsum:
     t.append("<table class='table{}' summary='{}'{}>".format(ix, tsum, tid))
    else:
      t.append("<table class='table{}' {}>".format(ix, tid))

    # set relative widths of columns
    if tw_html != "none":
      t.append("<colgroup>")
      for (i,w) in enumerate(widths):
       #t.append("<col width='{}%'>".format(pwidths[i]))
       t.append("<col class='colwidth{}'>".format(pwidths[i])) # col is a VOID element
       self.css.addcss("[1700] .colwidth{} {{ width:{}% ;}}".format(pwidths[i],pwidths[i]))
      t.append("</colgroup>")

    startloc = self.cl
    self.cl += 1 # move into the table rows
    data_row_found = False
    border_top = ''
    border_bottom = ''
    while self.wb[self.cl] != ".ta-":

      # see if .bn info line
      if self.bnPresent and self.is_bn_line(self.wb[self.cl]):
        t.append(self.wb[self.cl])   # copy the .bn info into the table (deleted much later during postprocessing)
        self.cl += 1
        continue

      # see if blank line (will not have borders)
      if "" == self.wb[self.cl]:
        t.append("  <tr><td>&#160;</td></tr>") #(replaced &nbsp; with &#160;)
        self.cl += 1
        data_row_found = False
        border_top = ''
        border_bottom = ''
        continue

      # horizontal border (top, because bottom borders are handled via lookahead while processing
      # a data row
      # Signified by _ for a single line or = for a double line (__ or == for medium weight)
      # Class names generated:
      # btt (border top thin) / btm (border top medium)
      # bttd (border top medium double) / btmd (border top medium double)
      # and correspondingly bbt/btm/bttd/btmd for border top classes
      if len(self.wb[self.cl]) < 3 and self.wb[self.cl] in self.valid_html_hrules:
        class_name = make_tb_border_class(self.wb[self.cl], data_row_found)
        border_top = class_name
        self.cl += 1
        continue

      # previously processed horizontal (bottom) border (via lookahead from a data row)
      # (Restore contents, skip line)
      if self.wb[self.cl].startswith(border_tag):
        self.wb[self.cl] = self.wb[self.cl][len(border_tag):]
        self.cl += 1
        continue

      # see if centered line (will not have borders)
      if not "|" in self.wb[self.cl]:
        line = self.wb[self.cl].strip()
        align = "text-align: center; "
        if len(line) >= 4 and line[0:4] == "<th>": # header row?
          cell_type1 = "<th"
          cell_type2 = "</th>"
          line = line[4:]
        else:
          cell_type1 = "<td"
          cell_type2 = "</td>"
        if len(line) >= 6 and line[0:4] == "<al=":
          m = re.match(r"^<al=([lrch])>", line) # pick up possible alignment directive
          if m:
            if m.group(1) == "l":
              align = "text-align: left; "
            elif m.group(1) == "r":
              align = "text-align: right; "
            elif m.group(1) == "c":
              align = "text-align: center; "
            elif m.group(1) == "h":
              align = "text-align: center; "
              self.warn_w_context("<al=h> not supported for centered table lines", self.cl)
          line = line[6:]
        t.append("  <tr>{} style='{}' colspan='{}'>{}{}</tr>".format(cell_type1, align,
                                                                      ncols, line, cell_type2))
        data_row_found = False
        border_top = ''
        border_bottom = ''
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
      if len(v) != ncols:
        self.crash_w_context("table has wrong number of columns:{}".format(self.wb[self.cl]), self.cl)

      data_row_found = True

      # check for horizontal rule following this row
      if len(self.wb[self.cl + 1]) < 3 and self.wb[self.cl + 1] in self.valid_html_hrules:
        class_name = make_tb_border_class(self.wb[self.cl + 1], data_row_found)
        border_bottom = class_name
        self.wb[self.cl + 1] = border_tag + self.wb[self.cl + 1] # flag the line for special handling

      t.append("  <tr>")
      # iterate over the cells
      caligns = haligns[:] # copy alignment specifications
      for k,data in enumerate(v):
        # adjust alignment if override given
        v[k] = v[k].strip(' ')
        # the below 2 lines were commented out, but that caused an issue with row borders when all
        # cells on a line are blank. I'm not sure whether setting the blank cells to &nbsp; is the
        # proper fix, but it seems to work.
        if not v[k]:
          v[k] = '&#160;' # force blank cells to nbsp (&#160;)
        if k == 0: # for first cell, check for <th> flag to indicate a header row
          if len(v[k]) >= 4 and v[k][0:4] == "<th>": # header row?
            cell_type1 = "<th"
            cell_type2 = "</th>"
            v[k] = v[k][4:] # remove the tag
          else:
            cell_type1 = "<td"
            cell_type2 = "</td>"
        if len(v[k]) >= 6 and v[k][0:4] == "<al=":
          m = re.match(r"^<al=([lrch])>", v[k]) # pick up possible alignment directive
          if m:
            if m.group(1) == "l":
              caligns[k] = "text-align: left; "
            elif m.group(1) == "r":
              caligns[k] = "text-align: right; "
            elif m.group(1) == "c":
              caligns[k]= "text-align: center; "
            else: # must be h
              m = re.match("(.+)em", self.nregs["html-cell-padding-left"])
              if m:
                tpadding = round(1 + float(m.group(1)), 1)
                caligns[k] = "text-align: left; text-indent: -1em; padding-left: {}em; ".format(tpadding)
              else:
                self.warn_w_context("Unable to calculate proper cell padding because self.nregs[\"html-cell-padding-left\"] has unexpected format: {}".format(self.nregs["html-cell-padding-left"]),
                                    self.cl)
                caligns[k] = "text-align: left; text-indent: -1em; padding-left: 1em; "
            v[k] = v[k][6:] # remove the alignment tag
        valgn = ""
        padding = ""

        if v[k] != "<span>":
          if not borders_present: # if no left/right borders in table
            if k < len(v) - 1:    # If we appear not to be the last column, need to check for
                                  #   all columns to the right being <span> as that could still
                                  #   make us the last column
              lastcol = True       # assume we're the last column
              for kk in range(k+1, len(v)):
                if v[kk].strip() != "<span>": # if some column after us is not <span>
                  lastcol = False             # then we're not the last column
                  break
              if not lastcol:
                padding += 'padding-right: 1em; '
          # convert leading protected spaces (\  or \_) to padding
          t1 = v[k]
          t2 = re.sub(r"^ⓢ+","", v[k])
          if len(t1) - len(t2) > 0:
            if "text-indent:" in caligns[k]: # can't have protected leading spaces and hanging-indent
              self.warn_w_context("Protected leading spaces ignored for table cell with hanging indent in column {}".format(k),
                                  self.cl)
            else:
              padleft = round((len(t1) - len(t2))*0.7, 1)
              padding += 'text-indent: {}em; '.format(padleft) # was padding-left, but that has problems if cell text wraps
          if borders_present: # if no leading spaces, and borders in use, add padding as needed
            if "padding-left:" not in caligns[k]: # don't add left padding if already there
              padding += 'padding-left: ' + self.nregs["html-cell-padding-left"] + '; '
            #if borders_present: # if borders in use add right-padding
            padding += 'padding-right: ' + self.nregs["html-cell-padding-right"] + '; '

          # inject saved page number if this is first column
          if k == 0:
            v[k] = savedpage + t2
          else: # added in 3.50b; was missing, resulting in excess padding (both padding and &nbsp;)
            v[k] = t2
          colspan = 1 #  look for <span> in next column(s) to setup colspan
          border_after = bafter[k] # figure out colspan and proper "after" border, depending on <span>
          for kk in range(k+1, len(v)):
            if v[kk].strip() == "<span>":
              colspan += 1
              border_after = bafter[kk]
            else:
              break
          colspan = " colspan='{}'".format(colspan) if (colspan > 1) else ""

          # force a spanning cell that is all blank to be &nbsp; so it doesn't disappear
          if colspan and not v[k].strip():
            v[k] = '&#160;'

          border_classes = border_top + ' ' + border_bottom + ' ' + bbefore[k] + ' ' + border_after
          border_classes = border_classes.strip()
          if border_classes:
            border_classes = "class='{}' ".format(border_classes)
          t.append("    {} {}style='{}{}{}'{}>".format(cell_type1, border_classes, valigns[k],
                                                        caligns[k], padding,
                                                        colspan) + v[k].strip() + cell_type2)
      t.append("  </tr>")
      border_top = '' # done with these two borders
      border_bottom = ''
      self.cl += 1
    t.append("</table>")
    self.wb[startloc:self.cl+1] = t
    self.cl = startloc + len(t)

  # Guts of doDropimage
  # (split out during development of drop caps for .nf blocks)
  def doDropimageGuts(self, line, type="p"):
    di={}
    m = re.match(r"\.di +(\S+) +(\d+) +(\S+)$",self.wb[line]) # 3 argument version: image, width, adjust
    if m:
      di["d_image"] = m.group(1)
      di["d_width"] = m.group(2)
      di["d_height"] = ""
      d_adj = m.group(3)
    else:
      m = re.match(r"\.di +(\S+) +(\d+) +(\d+) +(\S+)$",self.wb[self.cl]) # 4 argument version
      if m:
        di["d_image"] = m.group(1)
        di["d_width"] = m.group(2)
        di["d_height"] = m.group(3)
        d_adj = m.group(4)
      else:
        self.crash_w_context("malformed drop image directive", line)
    self.checkIllo(di["d_image"])
    di["s_adj"] = re.sub(r"\.","_", str(d_adj))
    if self.pindent:
      s0 = re.sub("em", "", self.nregs["psi"]) # drop the "em"
    else:
      s0 = re.sub("em", "", self.nregs["psb"]) # drop the "em"
    s1 = int(float(s0)*100.0) # in tenths of ems
    s2 = (s1//2)/100 # forces one decimal place
    mtop = s2
    mbot = mtop
    self.css.addcss("[1920] img.drop-capi { float: left; margin: 0 0.5em 0 0; position: relative; z-index: 1; }")
    if type == "p":
      self.css.addcss("[1921] p.drop-capi{} {{ text-indent: 0; margin-top: {}em; margin-bottom: {}em; }}".format(di["s_adj"],mtop,mbot))
      self.css.addcss("[1922] p.drop-capi{}:first-letter {{ color: transparent; visibility: hidden; margin-left: -{}em; }}".format(di["s_adj"],d_adj))
      # self.css.addcss("[1923] /* */") RT this markup causes HTML5 to fail
      self.css.addcss("[1924]  .x-ebookmaker img.drop-capi { display: none; visibility: hidden; }")
      self.css.addcss("[1925]  .x-ebookmaker  p.drop-capi{}:first-letter {{ color: inherit; visibility: visible; margin-left: 0em; }}".format(di["s_adj"]))
      # self.css.addcss("[1926] /* */}") RT this markup causes HTML5 to fail
    else:
      self.css.addcss("[1941] div.drop-capinf{} {{ text-indent: 0; margin-top: {}em; margin-bottom: {}em}}".format(di["s_adj"],mtop,mbot))
      self.css.addcss("[1942] div.drop-capinf{}:first-letter {{ color: transparent; visibility: hidden; margin-left: -{}em; }}".format(di["s_adj"],d_adj))
      # self.css.addcss("[1943] /* */ {") RT this markup causes HTML5 to fail
      self.css.addcss("[1944]  .x-ebookmaker img.drop-capinf { display: none; visibility: hidden; }")
      self.css.addcss("[1945]  .x-ebookmaker div.drop-capinf{}:first-letter {{ color: inherit; visibility: visible; margin-left: 0em; }}".format(di["s_adj"]))
      # self.css.addcss("[1946] /* */}") RT this markup causes HTML5 to fail
    self.warn("CSS3 drop-cap. Please note in upload.")
    return di

  # Drop Image
  # two formats:
  #   .di i_b_009.jpg 100 170 1.3 (width, height, adjust specified)
  #   .di i_b_009.jpg 100 1.3 (width, adjust specified)
  def doDropimage(self):

    di = self.doDropimageGuts(self.cl)
    t = []
    t.append("<div>")
    if di["d_height"] == "":
      t.append("  <img class='drop-capi' src='images/{}' width='{}' alt='' >".format(di["d_image"],di["d_width"]))
    else:
      t.append("  <img class='drop-capi' src='images/{}' width='{}' height='{}' alt='' >".format(di["d_image"],di["d_width"],di["d_height"]))
    t.append("</div><p class='drop-capi{}'>".format(di["s_adj"]))
    self.wb[self.cl:self.cl+1] = t

  # Drop Cap. a single, capital letter
  def doDropcap(self, line, type="p"):
    #m = re.match(r"\.dc (.*?)\s(.*?)(\s|$)", self.wb[line]) # optional adjust
    m = re.match(r"\.dc +(.*?) +(.*?)( +(.*)|$)", self.wb[line]) # optional adjust
    dcadjs = ""
    dcadj = 0
    if m:
      if m.group(4):
        self.crash_w_context("Unexpected (extra) argument(s) to .dc: {}".format(m.group(4), line))
      dcadj = m.group(1)
      dclh = m.group(2)
      dcadjs = "{}_{}".format(dcadj, dclh)
      dcadjs = re.sub(r"\.", "_", dcadjs) # name formatting
      mt = (250.0 / float(re.sub("%","",self.nregs["dcs"]))) * 0.1
      mr = (250.0 / float(re.sub("%","",self.nregs["dcs"]))) * 0.1
    else:
      self.crash_w_context("incorrect format for .dc arg1 arg2 command", line)
    if type == "p":
      self.css.addcss("[1930] p.drop-capa{} {{ text-indent: -{}em; }}".format(dcadjs,dcadj))
      self.css.addcss("[1931] p.drop-capa{}:first-letter {{ float: left; margin: {:0.3f}em {:0.3f}em 0em 0em; font-size: {}; line-height: {}em; text-indent: 0; }}".format(dcadjs,mt,mr,self.nregs["dcs"],dclh))
      # self.css.addcss("[1933] /* */") RT this markup causes HTML5 to fail
      self.css.addcss("[1935] .x-ebookmaker p.drop-capa{} {{ text-indent: 0; }}".format(dcadjs))
      self.css.addcss("[1936] .x-ebookmaker   p.drop-capa{}:first-letter {{ float: none; margin: 0; font-size: 100%; }}".format(dcadjs))
      # self.css.addcss("[1937] /* */") RT this markup causes HTML5 to fail
      self.pdc = "drop-capa{}".format(dcadjs)
    else:
      self.css.addcss("[1950] div.drop-capanf{} {{ text-indent: -{}em; }}".format(dcadjs,dcadj))
      self.css.addcss("[1951] div.drop-capanf{}:first-letter {{ float: left; margin: {:0.3f}em {:0.3f}em 0em 0em; font-size: {}; line-height: {}em; text-indent: 0; }}".format(dcadjs,mt,mr,self.nregs["dcs"],dclh))
      # self.css.addcss("[1953] /* */") RT this markup causes HTML5 to fail
      self.css.addcss("[1955] .x-ebookmaker div.drop-capanf{} {{ text-indent: 0; }}".format(dcadjs))
      self.css.addcss("[1956] .x-ebookmaker div.drop-capanf{}:first-letter {{ float: none; margin:0; font-size: 100%; }}".format(dcadjs))
      # self.css.addcss("[1957] /* */") RT this markup causes HTML5 to fail
      self.pdc = "drop-capanf{}".format(dcadjs)
    del self.wb[line]

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
    foundbody = False
    for i in range(len(self.wb)):
      if not foundbody:
        if '<body>' in self.wb[i]:
          foundbody = True
      else:
        #self.wb[i] = re.sub("\s+>", ">", self.wb[i])  # spaces before close ">"
        self.wb[i] = re.sub(r"(<.*?')\s+>", r"\1>", self.wb[i])  # remove spaces before
                                                                 # closing HTML ">"
        self.wb[i] = re.sub("<p  ", "<p ", self.wb[i])
        # next line broke German, where a space is significant before ">"
        # self.wb[i] = re.sub(" >", ">", self.wb[i])
        self.wb[i] = re.sub("⑦", "#", self.wb[i]) # used in links
        if re.search("<h1", self.wb[i]): # expect to find one h1 in the file
          h1cnt += 1

    i = 0
    #while not re.search(r"<style type=\"text/css\">", self.wb[i]):
    while not re.search(r"<style>", self.wb[i]): # RT removed deprecated CDATA comment opening
      i += 1
    #while not re.search(r"<\/style>", self.wb[i]):
    while not re.search(r"<\/style>", self.wb[i]):  # RT removed deprecated CDATA comment closing
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
      if blvl == 0 and re.match(r"\s*<span class='pageno'.*?<\/span>$", self.wb[i]):
        self.wb[i] = "<div>{}</div>".format(self.wb[i])

    # remove double blank lines (must be done before creating .bin file)
    i = 0
    while i < len(self.wb) - 1:
      if not self.wb[i] and not self.wb[i+1]:
        del self.wb[i]
        continue
      i += 1

    #build GG .bin file if any .bn commands found  in postprocess
    if self.bnPresent:
      self.bb.append("%::pagenumbers = (")
      i = 0
      if self.ppqt2:
        self.ppqt = []
        self.ppqtentries = 0
        ccount = 0
      while i < len(self.wb):
        bnInLine = False
        if self.wb[i] == "":              # skip blank lines, but remember we had one
          if self.ppqt2:
            ccount += 1
          i += 1
          continue
        offset1 = 0
        offset2 = 0
        ppqtfound = False
        temp = self.wb[i]
        m = re.search("(.*?)⑱(.*?)⑱(.*)",self.wb[i])  # find any .bn information in this line
        while m:
          bnInLine = True
          t = " 'Pg{}' => ['offset' => '{}.{}', 'label' => '', 'style' => '', 'action' => '', 'base' => ''],".format(m.group(2),i+1,len(m.group(1)))  # format a line in the .bn array (GG expects 1-based line number)
          t = re.sub("\[","{",t,1)
          t = re.sub("]","}",t,1)
          self.bb.append(t)
          if self.ppqt2:
            ccount += len(m.group(1)) - offset1 # count characters we haven't counted so far
            offset1 = len(m.group(1))
            offset2 = len(m.group(3))
            self.ppqtpage(m.group(2), ccount)
          self.wb[i] = re.sub("⑱.*?⑱","",self.wb[i],1)  # remove the .bn information
          temp = self.wb[i]
          m = re.search("(.*?)⑱(.*?)⑱(.*)",self.wb[i])  # look for another one on the same line
        if self.ppqt2:
          if not bnInLine:
            ccount += len(self.wb[i]) + 1
          else:
            ccount += offset2 + 1
        if bnInLine and self.wb[i] == "":  # delete line if it ended up blank
          del self.wb[i]
          if self.ppqt2:
            ccount -= 1
          if i > 0 and self.wb[i-1] == "" and self.wb[i] == "":      # If line before .bn info and line after both blank
            del self.wb[i]                          # delete the next one, too.
            if self.ppqt2:
              ccount -= 1
        else:
          i += 1
      self.bb.append(");")
      #self.bb.append("$::pngspath = '{}\\';".format(os.path.join(os.path.dirname(self.srcfile),"pngs")))
      self.bb.append(r"$::pngspath = '{}\\';".format(os.path.join(os.path.realpath(self.srcfile),"pngs")))
      self.bb.append("1;")


  # called to retrieve a style string representing current display parameters
  #
  def fetchStyle(self, nfc=False, rj=False):
    s = ""
    if self.regIN != 0 and not self.list_item_active:
      inpct = (self.regIN * 100)/72
      s += "margin-left: {:3.2f}%; ".format(inpct)
    if self.regLL != 72 and not self.list_item_active:
      llpct = ((72 - self.regLL) * 100)/72
      s += "margin-right: {:3.2f}%; ".format(llpct)
    if self.regTI == -1000: # special force of ti=0
      s += "text-indent: 0; "
    else: # a possible regular indent
      if self.regTI != 0:
        tipct = (self.regTI * 100)/72
        s += "text-indent: {:3.2f}%; ".format(tipct)
    # there may be a pending vertical space.
    if self.pvs > 0:
      s += "margin-top: {}em; ".format(self.pvs)
      self.pvs = 0
    if self.fsz != "100%" and self.fsz != "1.0em":
      s += "font-size: {}; ".format(self.fsz)
    if not nfc and not rj and self.regAD == 0:
      s += "text-align: left; "
    return s

  # Called to retrieve a style string representing current display parameters
  #   for a .ul, .ol, or .dl
  # Unlike the other version this one ignores self.regTI and self.fsz (which
  #   must be handled separately) and has no support for .nf or .rj
  def list_fetchStyle(self):

    marginlr = ""
    margintop = ""
    if self.regIN != 0 and not self.list_item_active:
      inpct = (self.regIN * 100)/72
      marginlr += "margin-left: {:3.2f}%; ".format(inpct)
    if self.regLL != 72 and not self.list_item_active:
      llpct = ((72 - self.regLL) * 100)/72
      marginlr += "margin-right: {:3.2f}%; ".format(llpct)

    if self.pvs > 0: # there may be a pending vertical space
      margintop += "margin-top: {}em; ".format(self.pvs)
      self.pvs = 0
    return margintop, marginlr

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
        s = self.fetchStyle(rj=True) # style line with current parameters
        rstyle = s + "text-align: right; "
        self.pvs = 0  # if there is a pending vertial space, only use it once on first line
        self.wb[self.cl] = "<div style='{}'>{}</div>".format(rstyle, self.wb[self.cl])
        self.cl += 1
        nlines -= 1
    else:
      self.crash_w_context("malformed .rj directive", self.cl)

  def doSidenote(self):
    # handle sidenotes outside paragraphs, sidenotes inside paragraphs are done in <sn>-style markup
    self.snPresent = True  # remember we have sidenotes
    m = re.match(r"\.sn (.*)", self.wb[self.cl])
    if m:
      t = m.group(1).split("|") # split sidenote on | characters if any
      for i in range(len(t)):
        t[i] = t[i].strip()
      t = "<br>".join(t)
      if self.pvs > 0: # handle any pending vertical space before the .sn
        # need to apply vertical space separately so sidenote and following text are placed
        # properly
        s = "<div  style='margin-top: {}em; '></div>".format(self.pvs)
        self.wb.insert(self.cl, s)
        self.wb[self.cl+1] = "<div class='sidenote'>{}</div>".format(t)
        self.pvs = 0
        self.cl += 2
      else:
        self.wb[self.cl] = "<div class='sidenote'>{}</div>".format(t)
        self.cl += 1
    else:
      self.crash_w_context("malformed .sn directive", self.cl)

  # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  # Index Processing (HTML)
  def doIx(self):

    def trimsp(linenum):
      tmp = self.wb[linenum][:]
      if tmp.startswith("⑯"):
        m = re.match(r"^(⑯\w+⑰)(\s+)(.*)", tmp)
        if m:
          tmp = m.group(1) + m.group(3)
          leadsp = len(m.group(2))
        else:
          leadsp = 0
      else:
        tmp2 = tmp.lstrip()
        leadsp = len(tmp) - len(tmp2)
        tmp = tmp2
      return tmp, leadsp

    # Figure out if this line needs a </li> or not. If the next line has the same, or smaller
    # indentation, it does. If next line has greater indentation, then leave the <li> open so
    # we can nest the inner <ul> properly.
    def checknext(linenum):
      linenum += 1
      while (linenum < len(self.wb) and
             self.bnPresent and
             self.is_bn_line(self.wb[linenum])):
        linenum += 1
      s = "</li>" # assume next line is same indentation
      if linenum < len(self.wb) and self.wb[linenum] != ".ix-":
        tmp, leadsp = trimsp(linenum)
        if (leadsp > rindent): # don't add </li> if next line has larger indentation
          s = ""
      return s

    self.css.addcss("[1240] .index ul {list-style-type: none;  padding-left: 0; }") ##3.57a
    self.css.addcss("[1240] ul.index  {list-style-type: none;  padding-left: 0; }")
    self.css.addcss("[1240] .index li {text-indent: -1em; padding-left: 1em; }") ##3.57a
    ssty = ""
    s = self.fetchStyle() # supplemental style
    if s:
      ssty = " style='{}'".format(s)
    startloc = self.cl
    i = self.cl
    t = []
    t.append("<ul class='index'{}>".format(ssty))

    i += 1
    cpvs = 0
    rindent = 0 # relative indent of current line(s) based on leading spaces in input
    ulindent = 0 # leading spaces in output (first ul at 0, 2nd ul at 4, ...)

    while i < len(self.wb) and self.wb[i] != ".ix-":

      # if this line is just bn info then just leave it in the output as-is
      if self.bnPresent and self.is_bn_line(self.wb[i]):
        i += 1
        continue

      if self.wb[i] == "":
        cpvs += 1
      else:
        # need to calculate leading space for this line.
        # there may be some tags *before* the leading space
        # (Not as of 3.52a, which places them after the leading space.)
        # But there may still be .bn info before leading space, so account for it
        tmp, leadsp = trimsp(i)

        if cpvs > 1:
          spvs = " style='margin-top: {}em; ' ".format(cpvs)
          cpvs = 0
        else:
          spvs = ""

        if leadsp == rindent: # Indentation did not change; just need <li>
          if spvs == "" and rindent == 0:
            spvs = " style='margin-top: .5em; ' "
            cpvs = 0
          s = (" " * (ulindent + 2)) + "<li{}>".format(spvs) + tmp
          s += checknext(i) # add </li> if next line at same or smaller indent
          t.append(s)

        elif leadsp > rindent: # Indentation increased; need possible additional <li>, then <ul> <li>
          diff = leadsp - rindent
          if diff%2: # if not an even number of spaces
            self.crash_w_context("Indentation in index not a multiple of 2", i)
          while (diff > 0):
            ulindent += 4
            t.append((" " * ulindent) + "<ul{}>".format(spvs))
            spvs = ''
            if diff > 2:
              t.append((" " * (ulindent + 2)) + "<li>")
            rindent += 2
            diff -= 2
          s = (" " * (ulindent + 2)) + "<li>" + tmp
          s += checknext(i) # add </li> if next line at same or smaller indent
          t.append(s)
        else: # Indentation decreased; need </ul>, then </li>, then need to figure out what level we're at
          diff = rindent - leadsp
          if diff%2: # if not an even number of spaces
            self.crash_w_context("Indentation in index not a multiple of 2", i)
          while (diff > 0):
            t.append((" " * ulindent) + "</ul>")
            ulindent -= 4
            t.append((" " * (ulindent + 2)) + "</li>")
            rindent -= 2
            diff -= 2
          if spvs == "" and rindent == 0:
            spvs = " style='margin-top: .5em; ' "
            cpvs = 0
          s = (" " * (ulindent + 2)) + "<li{}>".format(spvs) + tmp
          s += checknext(i) # add </li> if next line at same or smaller indent
          t.append(s)
        cpvs = 0  # reset pending vertical space
      i += 1

    # at block end.
    if self.wb[i] != ".ix-":
        self.fatal("File ends with unclosed .ix block")

    while (rindent > 0): # close out any inner lists
      t.append((" " * ulindent) +
               "</ul>")
      ulindent -= 4
      t.append((" " * (ulindent + 2)) + "</li>")
      rindent -= 2

    if cpvs > 0: # pending empty space?
      spvs = " style='margin-bottom: {}em; ' ".format(cpvs)
      cpvs = 0
    else:
      spvs = ""

    t.append("</ul{}>".format(spvs)) # finish out the block

    endloc = i
    self.wb[startloc:endloc+1] = t # replace source lines with generated list
    self.cl = startloc + len(t)

  # Handle paragraph (HTML)
  def doPara(self):
    if self.regTIp != 0: # If persistent temporary indent in effect, pretend we got a .ti command
      self.regTI = self.regTIp

    s = self.fetchStyle() # style line with current parameters

    s_top = s_bot = ""

    # if there is a pending drop cap, don't indent
    # if there is a text-indent already, don't change it
    # otherwise, add a text-indent if self.pindent is set.
    if self.pdc == ""  and self.pindent and 'text-indent' not in s:
      s += 'text-indent: {}; '.format(self.nregs["pti"])

    # apply either "psi" or "psb" spacing
    if self.pindent:
      # unless there is a margin already set, set top margin
      if "margin-top" not in s:
        # psi represents the entire gap. split it
        s0 = re.sub("em", "", self.nregs["psi"]) # drop the "em"
        s1 = int(float(s0)*100.0) # in tenths of ems
        s2 = (s1//2)/100 # forces one decimal place
        s_top = 'margin-top: {}em; '.format(s2)
        if not self.list_item_active:
          s += s_top
      if "margin-bottom" not in s:
        # psi represents the entire gap. split it
        s0 = re.sub("em", "", self.nregs["psi"]) # drop the "em"
        s1 = int(float(s0)*100.0) # in tenths of ems
        s2 = (s1//2)/100 # forces one decimal place
        s_bot = 'margin-bottom: {}em; '.format(s2)
        if not self.list_item_active:
          s += s_bot
    else: # not indented, use "psb" spacing
      # unless there is a margin already set, set top margin
      if "margin-top" not in s:
        # psb represents the entire gap. split it
        s0 = re.sub("em", "", self.nregs["psb"]) # drop the "em"
        s1 = int(float(s0)*100.0) # in tenths of ems
        s2 = (s1//2)/100 # forces one decimal place
        s_top = 'margin-top: {}em; '.format(s2)
        if not self.list_item_active:
          s += s_top
      if "margin-bottom" not in s:
        # psb represents the entire gap. split it
        s0 = re.sub("em", "", self.nregs["psb"]) # drop the "em"
        s1 = int(float(s0)*100.0) # in tenths of ems
        s2 = (s1//2)/100 # forces one decimal place
        s_bot = 'margin-bottom: {}em; '.format(s2)
        if not self.list_item_active:
          s += s_bot

    # setup CSS for paragraphs inside list items
    if self.list_item_active and (self.list_type == "o" or self.list_type == "u"):
      self.css.addcss("[1171] .li-p-first {" + s_top + s_bot + "}")
      if s_top or s_bot:
        self.css.addcss("[1171] .li-p-mid {" + s_top + s_bot + "}")
      self.css.addcss("[1171] .li-p-last {" + s_top + s_bot + "}")
      self.css.addcss("[1171] .li-p-only { margin-top: inherit; margin-bottom: inherit; }")

    s_str = "" # empty style string
    if s != "":
      s_str = "style='{}' ".format(s)

    c_str = "" # empty class string
    if self.pdc != "":
      c_str = "class='{}' ".format(self.pdc) # only for drop cap
      self.pdc = ""

    if re.match("<div>", self.wb[self.cl]):
      # if this is a div, such as for a drop cap, apply the pending style to the div
      self.wb[self.cl] = "<div {}{}>".format(c_str,s_str) + self.wb[self.cl][5:] # ouch
    else:
      # it's a normal paragraph
      pstart = self.cl  # remember where paragraph starts
      if self.list_item_active:
        if self.list_item_empty:
          self.wb[self.cl] = "<p class='li-p-first' {}{}>".format(c_str,s_str) + self.wb[self.cl]
          self.list_item_empty = False
        else:
          self.wb[self.cl] = "<p class='li-p-mid' {}{}>".format(c_str,s_str) + self.wb[self.cl]
      else:
        self.wb[self.cl] = "<p {}{}>".format(c_str,s_str) + self.wb[self.cl]

    while ( self.cl < len(self.wb) and
            self.wb[self.cl]): # any blank line or dot command ends paragraph
      if self.wb[self.cl].startswith("."):
        m = re.match(r"\.([a-z]|⓭DV-)", self.wb[self.cl])
        if m:
          break
      self.cl += 1
    i = self.cl - 1
    # if para ended with .bn info, place the </p> before it, not after it to avoid extra
    # blank lines after we remove the .bn info later
    while self.bnPresent and self.is_bn_line(self.wb[i]):
      i -= 1
    self.wb[i] = self.wb[i] + "</p>"

    if (self.list_item_active and self.cl < len(self.wb) and
       (self.wb[self.cl].startswith(".it") or self.wb[self.cl].startswith(".ul") or
        self.wb[self.cl].startswith(".ol"))):
      self.wb[pstart], count = re.subn("li-p-mid", "li-p-last", self.wb[pstart], 1)
      if count == 0:
        self.wb[pstart], count = re.subn("li-p-first", "li-p-only", self.wb[pstart], 1)

    self.regTI = 0 # any temporary indent has been used.

  # Unordered List (HTML)
  # .ul options
  #    or
  # .ul-
  #
  # options:
  #   style="disc | circle | square | none" (default: disc)
  #   indent="2" (indent is to the marker. Text is indented a further 2 spaces)
  #   hang=n (default) or y
  #   space=n (default) or y
  #   id=<id-value>
  #   class=<class-value>
  #
  #
  # HTML notes:
  # <ul>  ...
  def doUl(self):


    def ulGetClass(clss, csstuple):
      # Make a new class for this .ul, or reuse a matching existing class, or use PPer-supplied class
      if clss:
        try:
          if csstuple != self.ul_dict[clss]:
            self.warn_w_context("Conflicting .ul CSS characteristics for PPer-supplied class {}".format(clss), self.cl)
            if 'd' in self.debug:
              self.print_msg("Older definition requires: {}".format(self.ul_dict[clss]))
              self.print_msg("New definition requires: {}".format(csstuple))
        except KeyError: # if key doesn't exist, save it
          self.ul_dict[clss] = csstuple
      else:
        for k in self.ul_dict.keys():
          if csstuple == self.ul_dict[k]:
            clss = str(k)
            break
        else: # no match found; build new class name and create new entry in dictionary to remember it
          self.ul_classnum += 1
          clss = "ul_" + str(self.ul_classnum)
          self.ul_dict[clss] = csstuple

      return clss


    (startul, li_active, indent, id, clss) = self.doUlCommon()

    t = []
    depth = len(self.liststack) - 1
    ulspaces = 2 + (depth * 4)
    lispaces = ulspaces + 6
    prev_lispaces = ((depth - 1) * 4)

    # ending an unordered list
    if not startul:
      if li_active:
        t.append((lispaces * " ") + "</li>")
      t.append(((ulspaces + 4) * " ") + "</ul>")

    # beginning an unordered list
    else:

      self.list_item_active = False

      if indent != -1: # indent specified
        self.regIN += int(indent)
        if self.list_item_style != "none":
          self.regIN += 2

      else: # indent not specified
        temp_indent = self.outerwidth if (len(self.liststack) > 1) else 0
        if self.list_item_style != "none":
          temp_indent += 2
        self.regIN += temp_indent

      ulparms = "[1241] ul.{} {{"
      liparms = "[1241] .{} li {{"
      saveliparmlen = len(liparms) # remember original length to know if we've added anything

      ulparms += "padding-left: 0; "

      if self.list_hang:
        liparms += "padding-left: 1em; text-indent: -1em; "

      margintop, marginlr = self.list_fetchStyle()

      s = marginlr + "margin-top: .5em; margin-bottom: .5em; " # margin-top may be overriden in HTML later

      if self.fsz != "100%" and self.fsz != "1.0em":
        s += "font-size: {}; ".format(self.fsz)
        self.fsz = "100%" # reset so inner elements aren't further reduced (will be restored when popping list stack)

      s += "list-style-type: " + self.list_item_style + "; "

      ulparms += s
      ulparms += " }}"
      clss = ulGetClass(clss, (ulparms, liparms)) # determine and/or validate class name for this .ul
      self.css.addcss(ulparms.format(clss))
      if len(liparms) > saveliparmlen:
        liparms += " }}"
        self.css.addcss(liparms.format(clss))

      if id:
        id = " id=" + id
      clss = " class='{}'".format(clss)

      cvs = ""
      if margintop:
        cvs = " style='{}'".format(margintop)

      t.append((ulspaces * " ") + "<ul {}{}{}>".format(id, clss, cvs))

    self.wb[self.cl:self.cl+1] = t
    self.cl += len(t)


  # Ordered List (HTML)
  # .ol options
  #   or
  # .ol-
  #
  # options: (default values shown)
  #   style="decimal | lower-alpha | lower-roman | upper-alpha | upper-roman" (default: decimal)
  #   w="2" (number of digits allowed in the item number) (ignored in HTML)
  #   indent="2" (indent to the item number; text is indented a further width + 1 + 1 spaces)
  #   hang=n (default) or y
  #   space=n (default) or y
  #   id=<id-value>
  #   class=<class-value>
  #
  def doOl(self):


    def olGetClass(clss, csstuple):
      # Make a new class for this .ol, or reuse a matching existing class, or use PPer-supplied class
      if clss:
        try:
          if csstuple != self.ol_dict[clss]:
            self.warn_w_context("Conflicting .ol CSS characteristics for PPer-supplied class {}".format(clss), self.cl)
            if 'd' in self.debug:
              self.print_msg("Older definition requires: {}".format(self.ul_dict[clss]))
              self.print_msg("New definition requires: {}".format(csstuple))
        except KeyError: # if key doesn't exist, save it
          self.ol_dict[clss] = csstuple
      else:
        for k in self.ol_dict.keys():
          if csstuple == self.ol_dict[k]:
            clss = str(k)
            break
        else: # no match found; build new class name and create new entry in dictionary to remember it
          self.ol_classnum += 1
          clss = "ol_" + str(self.ol_classnum)
          self.ol_dict[clss] = csstuple

      return clss


    (startol, li_active, indent, id, clss) = self.doOlCommon()

    t = []
    depth = len(self.liststack) - 1
    olspaces = 2 + (depth * 4)
    lispaces = olspaces + 6
    prev_lispaces = ((depth - 1) * 4)

    # ending an ordered list
    if not startol:
      if li_active:
        t.append((lispaces * " ") + "</li>")
      t.append(((olspaces + 4) * " ") + "</ol>")

    # beginning an ordered list
    else:

      self.list_item_active = False

      if indent != -1: # indent specified
        self.regIN += int(indent)
        if self.list_item_style != "none":
          self.regIN += 2

      else: # indent not specified
        temp_indent = self.outerwidth if (len(self.liststack) > 1) else 0
        if self.list_item_style != "none":
          temp_indent += 2
        self.regIN += temp_indent

      olparms = "[1241] ol.{} {{"
      liparms = "[1241] .{} li {{"
      saveliparmlen = len(liparms) # remember original length to know if we've added anything

      olparms += "padding-left: 0; "

      if self.list_hang:
        liparms += "padding-left: 1em; text-indent: -1em; "

      margintop, marginlr = self.list_fetchStyle()

      s = marginlr + "margin-top: .5em; margin-bottom: .5em; " # margin-top may be overriden in HTML later

      if self.fsz != "100%" and self.fsz != "1.0em":
        s += "font-size: {}; ".format(self.fsz)
        self.fsz = "100%" # reset so inner elements aren't further reduced (will be restored when popping list stack)

      s += "list-style-type: " + self.list_item_style[0] + "; "

      olparms += s
      olparms += " }}"
      clss = olGetClass(clss, (olparms, liparms)) # determine and/or validate class name for this .ol
      self.css.addcss(olparms.format(clss))
      if len(liparms) > saveliparmlen:
        liparms += " }}"
        self.css.addcss(liparms.format(clss))

      if id:
        id = " id=" + id
      clss = " class='{}'".format(clss)

      cvs = ""
      if margintop:
        cvs = " style='{}'".format(margintop)

      t.append((olspaces * " ") + "<ol {}{}{}>".format(id, clss, cvs))

    self.wb[self.cl:self.cl+1] = t
    self.cl += len(t)

  # List item (HTML)
  def doIt(self):

    startIt = self.doItCommon()

    t = []
    depth = len(self.liststack) - 1
    ulolspaces = 2 + (depth * 4)
    lispaces = ulolspaces + 2

    if self.list_item_active:
      t.append((lispaces * " ") + "</li>") # insert ending tag for prior item
    else:
      self.list_item_active = True

    margintop, marginlr = self.list_fetchStyle()
    cvs = ""
    if margintop:
      cvs = " style='{}'".format(margintop)
    l = "<li{}>".format(cvs) + self.wb[self.cl][4:].strip() # append item text to line
    self.list_item_empty = False

    # to make editing/viewing the raw HTML easier, try to split the (long) line to a reasonable length
    while len(l) > 90:
      splitat = l.rfind(' ', 0, 90)
      if splitat == -1: # if no blanks found, split at position 90 anyway
        splitat = 90
      s = (lispaces * " ") + l[:splitat+1]
      t.append(s)
      l = l[splitat+1:]
    else:
      t.append((lispaces * " ") + l)

    self.wb[self.cl:self.cl+1] = t      # replace the .it with whatever we generated
    self.cl += len(t)

    if self.list_space: # add a blank line after this one if we're spacing the list
      self.pvs += 1

  # Definition List (HTML)
  # .dl options
  #    or
  # .dl-
  #
  # options:
  #   style="float | nofloat | paragraph" (default: float)
  #   w=<number> max length of term or speaker name
  #   indent="2"
  #   id=<id-value> (ignored in text)
  #   class=<class-value> (ignored in text)
  #   align=l (default) or r or c ### needs to be added
  ### Also, need to make sure .ul/.ol nest properly within .dl, so some more options need to be set/saved on
  ### the stack.
  #
  # Note: doDl operates differently from most other dot commands. It is in control of processing until
  #       the matching .dl- is encountered. All lines will either be directly part of its output,
  #       or indirectly if they are consumed/generated by another dot directive inside the .dl block. That is,
  #       doDl allows other dot commands within its scope, and actually invokes their associated
  #       processing routine, until the relevant .dl- is hit.
  #
  # see CSS and HTML suggestion at http://www.pgdp.net/wiki/Dialogue
  def doDl(self):

    class PphDefList(Book.DefList):

      # "Print" debugging info (place it into the output text) if requested
      def print_debug(self, info):
        b = self.book
        buff = "<p>" + "<br>\n".join(info) + "</p>"
        self.dlbuffer = buff.split("\n")
        self.emit()

      # Routine to "bump" the current line pointer
      # (Called by code in base DefList class)
      # Since we're working in the source buffer (unlike Ppt, which has a separate emit buffer) we will
      # delete the current line rather than bumping past it. All insertion of HTML code in PphDefList
      # happens by inserting before the current line pointer and bumping the current line pointer so it is
      # after the inserted code. This leaves the apparent "next" input line unchanged. When we are done
      # processing that line of code it must actually be deleted, rather than simply bumping a counter as
      # happens in Ppt and PptDefList.
      def bump_cl(self):
        del self.book.wb[self.book.cl]

      # Routine to handle special lines (.bn info)
      # (called by code in base DefList class)
      def emit_special(self, bninfo):

        b = self.book

        #if self.dd_active: # if a dd is active, end it
        #  self.build_dd("", True)

        if bninfo: # if bninfo passed, insert it into the output buffer before the current line pointer
          b.wb[b.cl:b.cl] = [bninfo]
          b.cl += 1

      # Routine to wrap a definition line
      # Nothing needed for HTML version
      def wrap_def(self):
        pass

      # Begin a dl
      def begin_dl(self):

        def dlGetClass(csstuple):
          # Make a new class for this .dl, or reuse a matching existing class, or use PPer-supplied class
          if self.options["class"]:
            self.dl_class = self.options["class"]
            try:
              if csstuple != b.dl_dict[self.dl_class]:
                self.warn_w_context("Conflicting .dl CSS characteristics required for PPer-supplied class {}".format(self.dl_class), b.cl)
                if 'd' in self.debug:
                  self.print_msg("Older definition requires: {}".format(b.dl_dict[self.dl_class]))
                  self.print_msg("New definition requires: {}".format(csstuple))
            except KeyError: # if key doesn't exist, save it
              b.dl_dict[self.dl_class] = csstuple
          else:
            for k in b.dl_dict.keys():
              if csstuple == b.dl_dict[k]:
                self.dl_class = str(k)
                break
            else: # no match found; build new class name and create new entry in dictionary to remember it
              b.dl_classnum += 1
              self.dl_class = "dl_" + str(b.dl_classnum)
              b.dl_dict[self.dl_class] = csstuple

            if self.options["debug"]:
              s = []
              s.append("***Generated class name: " + self.dl_class)
              self.print_debug(s)

        b = self.book
        self.dlstart = b.cl
        self.dlbuffer = []
        self.dd_class = ""
        self.dd_indent_class = ""
        self.dd_active = False
        self.dd_padding = 0 # set during emit_dl()
        self.dlnumspaces = len(b.liststack) * 2
        self.dlspaces = self.dlnumspaces * " "
        self.dtddnumspaces = self.dlnumspaces + 2
        self.dtddspaces = self.dtddnumspaces * " "

        self.paragraph = "" # in case combine=y initialize an empty paragraph
        self.dl_ptxtindent = 0
        self.dl_pindent = 0

        divisor = float(b.nregs["nf-spaces-per-em"]) # figure out width for term
        tindent = round(self.options["tindent"]/divisor, 1)
        dindent = round(self.options["dindent"]/divisor, 1)
        width = round(self.options["width"]/divisor, 1)
        dtwidth = width + tindent
        dtalign = "left" if (self.options["align"] == "l") else "right"

        margintop, marginlr = b.list_fetchStyle()

        if self.options["style"] == "d": # the following only for <dl> style output

          dlparms = "[1241] dl.{} {{"
          dtparms = "[1241] .{} dt {{"
          dtplen = len(dtparms)
          dtmparms = "" # will hold any generated @media handheld parameters
          ddparms = "[1241] .{} dd {{"

          if self.options["debug"]:
            dtparms += " background-color: #FFC0CB;" # set a pink background for the dt if debugging

          if self.options["collapse"]:
            dtparms += " line-height: .99;" # make <dt> line-height slightly smaller so collapsing works reliably

          dlparms += marginlr # set left/right margins
          dlparms += " margin-top: .5em; margin-bottom: .5em;" # CSS assumes .5em top margin; HTML will override if needed

          if b.fsz != "100%" and b.fsz != "1.0em":
            dlparms += " font-size: {};".format(b.fsz)
            b.fsz = "100%" # reset so inner elements aren't further reduced (will be restored when popping list stack)

          if self.options["float"]: # float=y
            dtparms += " float: left; clear: left; text-align: {}; width: {}em;".format(dtalign, dtwidth)
            dtparms += " padding-top: .5em; padding-right: .5em;"
            if self.options["tindent"]: # tindent non-zero?
              dtparms += " text-indent: {}em;".format(tindent)
            ddparms += " text-align: left; padding-top: .5em;"
            if dtalign == "right":
              ddparms += " padding-left: .5em;"

            if self.options["combine"]: # combine=y
              if self.options["collapse"]: # collapse=y
                if self.options["dindent"]:
                  ddparms += " text-indent: {}em;".format(dindent)
                else:
                  ddparms += " text-indent: .2em;" # allow a bit of padding when floated
                if self.options["hang"]: # hang=y
                  ddparms += " margin-left: 1em;"
                else: # hang=n
                  ddparms += " margin-left: 0em;"

              else: # collapse=n
                extra = 0 if (dindent) else .2 # allow a bit of left padding (via margin) if dindent not specified
                if self.options["hang"]: # hang=y
                  ddparms += " margin-left: {}em; text-indent: -1em;".format(dtwidth + 1 + dindent + extra)
                else: # hang=n
                  ddparms += " margin-left: {}em;".format(dtwidth + dindent + extra)

            else: # combine=n
              if self.options["collapse"]: # collapse=y
                if self.options["hang"]: # hang=y
                  ddparms += " margin-left: 1em;"
                else: # hang=n
                  ddparms += " margin-left: 0em;"
                #ddparms += " text-indent: {}em;".format(dtwidth + dindent)
                if self.options["dindent"]:
                  ddparms += " text-indent: {}em;".format(dindent)

              else: # collapse=n
                if self.options["hang"]: # hang=y
                  ddparms += " margin-left: {}em; text-indent: -1em;".format(dtwidth + 1 + dindent)
                else: # hang=n
                  ddparms += " margin-left: {}em;".format(dtwidth + dindent)

            dtmparms = dtparms[dtplen:] # completely respecify for mobile formats when floating

          else: # float=n
            dtparms += " text-align: {}; padding-top: .5em; width: {}em;".format(dtalign, dtwidth)
            ddparms += " text-align: left; padding-top: .5em; padding-left: .5em; "
            if self.options["tindent"]: # tindent non-zero?
              dtparms += " text-indent: {}em;".format(tindent)

            if self.options["combine"]: # combine=y
              if self.options["collapse"]: # collapse=y
                ddparms += " text-indent: {}em;".format(dtwidth + dindent)
                if self.options["hang"]: # hang=y
                  ddparms += " margin-left: 1em;"
                else: # hang=n
                  ddparms += " margin-left: 0em;"

              else: # collapse=n
                if self.options["hang"]: # hang=y
                  ddparms += " margin-left: {}em; text-indent: -1em;".format(dtwidth + 1 + dindent)
                else: # hang=n
                  ddparms += " margin-left: {}em;".format(dtwidth + dindent)

            else: # combine=n
              if self.options["collapse"]: # collapse=y
                ddparms += " text-indent: {}em;".format(dtwidth + dindent)
                if self.options["hang"]: # hang=y
                  ddparms += " margin-left: 1em;"
                else: # hang=n
                  ddparms += " margin-left: 0em;"

              else: # collapse=n
                if self.options["hang"]: # hang=y
                  ddparms += " margin-left: {}em; text-indent: -1em;".format(dtwidth + 1 + dindent)
                else: # hang=n
                  ddparms += " margin-left: {}em;".format(dtwidth + dindent)

          dlparms += " }}"
          dtparms += " }}"
          ddparms += " }}"
          dlGetClass((dlparms, dtparms, ddparms)) # determine and/or validate consistency of class name
          b.css.addcss(dlparms.format(self.dl_class))
          b.css.addcss(dtparms.format(self.dl_class))
          b.css.addcss(ddparms.format(self.dl_class))
          if dtmparms: # if anything added to dtmparms
            dtmparms = "[1241] .x-ebookmaker  .{} dt {{" + dtmparms + " }} "
            b.css.addcss(dtmparms.format(self.dl_class))

        else:  # <p> style output
          dldivparms = "[1241] div.{}  {{"
          dlparaparms = "[1241] .{} p {{"
          dlspanparms = "[1241] span.{} {{"

          dldivparms += marginlr # set left/right margins
          dldivparms += " margin-top: .5em; margin-bottom: .5em;" # assume top margin of .5em; HTML will override if needed

          dldivparms += " text-align: left;"
          dlparaparms += " text-align: left; margin-top: .5em; margin-bottom: .5em;"

          if b.fsz != "100%" and b.fsz != "1.0em":
            dlparms += " font-size: {};".format(self.fsz)
            b.fsz = "100%" # reset so inner elements aren't further reduced (will be restored when popping list stack)

          if self.options["debug"]:
            dlspanparms += " background-color: #FFC0CB;" # set a pink background for the dt if debugging

          if self.options["tindent"] != 0:
            dlspanparms += " text-indent: {}em;".format(tindent)

          if self.options["float"]: # float=y

            if self.options["collapse"]: # collapse=y
              #if self.options["hang"]: # hang=y
              #  dlparaparms += " padding-left: 1em; text-indent: -1em;"
              #else: # hang=n
              dlspanparms += " display: inline-block; text-align: {}; width: {}em;".format(dtalign, dtwidth-.2)

            else: # collapse=n
              #if self.options["hang"]: # hang=y
              #  dlparaparms += " padding-left: {0}em; text-indent: -1em;".format(dtwidth+1)
              #else: # hang=n
              dlspanparms += " text-indent: 0em; display: inline-block; text-align: {}; width: {}em;".format(dtalign, dtwidth-.2)
              dlparaparms += " padding-left: {}em; text-indent: -{}em; ".format(dtwidth, dtwidth)

          else: #float=n

            dlspanparms += " display: inline-block; text-align: {}; width: {}em;".format(dtalign, dtwidth)
            if self.options["collapse"]: # collapse=y
              #if self.options["hang"]: # hang=y
              #  dlparaparms += " padding-left: 1em; text-indent: {}em;".format(dtwidth-1)
              #else: # hang=n
              dlparaparms += " text-indent: {}em;".format(dtwidth)

            else: # collapse=n
              #if self.options["hang"]: # hang=y
              #  dlparaparms += " padding-left: {0}em; text-indent: -1em;".format(dtwidth+1)
              #else: # hang=n
              dlparaparms += " padding-left: {}em;".format(dtwidth)

          # define span/padding CSS for paragraph format
          #dlspanparms += " padding-left: {}em;".format(dd_padding-2))
          #self.dl_ptxtindent = self.dl_pindent + self.dd_padding # amount to indent a paragraph style dd that has an empty dt

          dldivparms += " }}"
          dlparaparms += " }}"
          dlspanparms += " }}"
          dlGetClass((dldivparms, dlparaparms, dlspanparms)) # determine and/or validate consistency of class name
          b.css.addcss(dldivparms.format(self.dl_class))
          b.css.addcss(dlparaparms.format(self.dl_class))
          b.css.addcss(dlspanparms.format(self.dl_class))

        cvs = ""
        if margintop:
          cvs = " style='{}'".format(margintop)

        if self.options["style"] == "d": # <dl> style
          self.dlbuffer.append(self.dlspaces + "<dl class='{}'{}>".format(self.dl_class, cvs))

        else: # <p> style
          self.dlbuffer.append(self.dlspaces + "<div class='{}'{}>".format(self.dl_class, cvs))

        self.emit()

      # Finalize a dl
      def finalize_dl(self):
        b = self.book

        if self.dd_active:
          self.build_dd("", endit=True)

        if self.options["style"] == "p": # <p> style
          self.dlbuffer.append(self.dlspaces + "  </div>")
        else:
          self.dlbuffer.append(self.dlspaces + "  </dl>")

        self.emit()


      # Split long lines of text for readability when added into the HTML
      def split_line(self, l):
        b = self.book
        t = []
        while b.truelen(l) > 90:
          splitat = l.rfind(' ', 0, 90)
          if splitat == -1: # if no blanks, split at 90
            splitat = 90
          s = l[:splitat+1]
          t.append(s)
          l = l[splitat+1:]
        else:
          t.append(l)
        return t

      # Layout the term and definition (non-combining mode)
      def layout(self):
        self.build_dt()
        self.build_dd(self.definition)
        self.definition = "" # needed? Or already done in DefList base class?

      # Emit the laid-out term/definition (non-combining mode)
      def emit_def(self):
        self.emit()

      # Build HTML for term into the buffer
      def build_dt(self):

        b = self.book
        if self.dd_active:
          self.build_dd("", True)

        b.list_item_active = True
        self.cvs = ""
        if b.pvs:
          self.cvs = " style='margin-top: {}em; '".format(b.pvs)
          b.pvs = 0

        term = self.term.rstrip()
        if self.pageinfo:   # pending page info?
          term += self.pageinfo
          self.pageinfo = ""
        if not term:
          term = "&#160;"
        if self.options["style"] == "d": # style=d
          if self.options["float"] or term != "&#160;":
            self.dlbuffer.append(self.dtddspaces + "<dt{}>".format(self.cvs) + term + "</dt>")

        else: # style=p
          if self.options["float"]:
            self.dlbuffer.append(self.dtddspaces + "<p{}>".format(self.cvs) +
                                 "<span class='{}'>".format(self.dl_class) + term + "</span>")

          else: # float=n
            self.dlbuffer.append(self.dtddspaces +
                                 "<span class='{}'{}>".format(self.dl_class, self.cvs) + term + "</span>" +
                                 "<p{}>".format(self.cvs))


      # Build HTML for definition into the buffer (may be a single line of definition, or a paragraph if combine=y)
      # s: possibly long string (even paragraph length) containing the dd info
      # endit: will be set if we need to force the close of a <dd> (paragraphs are always closed)
      def build_dd(self, s, endit=False):

        b = self.book

        clss = ""
        #cvs = ""
        cstyle = ""
        #ctxt = ""
        cindent = ""
        extraspaces = ""

        if endit:
          if self.pageinfo:  # is there pending page info?
            self.dlbuffer.append(self.pageinfo)
            self.pageinfo = ""
          if self.options["style"] == "d":
            self.dlbuffer.append(self.dtddspaces + "</dd>")
          self.dd_active = False
          b.list_item_active = False
          return

        b.list_item_active = True
        self.dd_active = True

        if self.options["style"] == "d" and not s:
          s = "&#160;"

        if not self.options["combine"]: ### why only combine=n?
          # calculate leading spaces in definition line if needed (non-combining only)
          tmp = s
          ss = ""
          m = re.match(r"^(⑯\w+⑰)", tmp) # remove any leading .bn info before calculating
          while m:
            ss += m.group(0)
            tmp = re.sub(r"^⑯\w+⑰", "", tmp, 1)
            m = re.match(r"^⑯\w+⑰", tmp)
          leadsp = len(tmp) - len(tmp.lstrip())

          # define an indent class if needed
          ### TODO:
          ### recognize duplicates; need different name if so? Or detect and reject?
          ### Handle indents differently: setup a span as <span class='indent_class'>&nbsp;</span>rest of text
          ### where indent_class is calculated based on the leading blanks, and defined as
          ### width: m.nem; display: inline-block
          if leadsp > 0:
            dd_indent_class = "dd_in{}".format(leadsp)  # create an indent class
            if b.nregsusage["nf-spaces-per-em"] > 1:
              dd_indent_class += "_{}".format(self.nregsusage["nf-spaces-per-em"])

            divisor = float(b.nregs["nf-spaces-per-em"])
            iamt = round(leadsp/divisor, 1) # calculate based on "2" spaces per em, and
                                               #  add in the base padding-left calculated from self.list_item_width
            if self.options["hang"]: # hang=y
              b.css.addcss("[1241] .{} {{ padding-left: {}em; text-indent: -1em}}".format(dd_indent_class, iamt+1))
            else: # hang=n
              b.css.addcss("[1241] .{} {{ padding-left: {}em}}".format(dd_indent_class, iamt))

        if self.dd_indent_class or self.dd_class:
          if self.dd_indent_class and self.dd_class:
            dd_indent_class += " "
          clss = " class='{}{}'".format(self.dd_indent_class, self.dd_class)

        if b.truelen(s) > 90:
          t = self.split_line(s)
        else:
          t = [s]
        #if b.pvs:
        #  cvs = "margin-top: {}em; ".format(b.pvs)
        #  b.pvs = 0

        #if self.options["style"] == "p":
        #  if not self.term and self.dl_ptxtindent != 0:
        #    ctxt = "text-indent: {}em; ".format(self.dl_ptxtindent)
        #  elif self.dl_pindent:
        #    ctxt = "text-indent: {}em; ".format(self.dl_pindent)

        if self.cvs:
          cstyle = self.cvs
          self.cvs = ""

        if self.options["style"] == "d":
          self.dlbuffer.append(self.dtddspaces + "<dd{}{}>".format(clss, cstyle) + t[0])
        else: # style=p
          #if self.term:
          #  self.dlbuffer.append(self.dtddspaces + "<p{}{}>".format(clss, cstyle) + self.term + " ")
          #  extraspaces = "  "
          #  self.dlbuffer.append(self.dtddspaces + extraspaces + "<span class='dlpspan'>" + t[0])
          #else:
          #  self.dlbuffer.append(self.dtddspaces + "<p{}{}>".format(clss, cstyle) + t[0])
          extraspaces = "  "
          t[-1] += "</p>" # always close paragraphs
          self.dlbuffer.append(self.dtddspaces + extraspaces + t[0])

        for i in range(1, len(t)): # handle remaining lines, if any, of this definition
          self.dlbuffer.append(self.dtddspaces + extraspaces + t[i])

        self.dd_class = ""
        self.dd_indent_class = ""


      # build HTML for a definition that is a paragraph
      def emit_paragraph(self):

        self.build_dt()
        self.build_dd(self.paragraph)
        self.emit()
        self.term = ""
        self.paragraph = ""

      # Routine to handle blank lines after the first one
      def add_blank(self):
        self.book.pvs += 1

      # Handle class= on .dd directive
      def set_dd_class(self, clss):
        self.dd_class = clss

      # Actually add the buffer into Pph.wb (will insert before Pph.cl)
      def emit(self):

        b = self.book

        if self.dlbuffer:
          b.wb[b.cl:b.cl] = self.dlbuffer
          b.cl += len(self.dlbuffer)
          self.dlbuffer = []

    # main processing for doDl (HTML):

    dlobj = PphDefList(self) # create the object
    dlobj.run()              # turn over control

  # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  # check that music file exists
  #
  def checkMusic(self, fname): # assure that fn exists in images folder
    if " " in fname:
      self.warn("cannot have spaces in music filenames: {}".format(fname))
    if re.search("[A-Z]", fname):
      self.warn("music filenames must be lower case: {}".format(fname))
    if self.musicDirectoryOK:
      if not fname in self.musicDict:
        self.warn("file {} not in music folder".format(fname))
      else:
        self.musicDict[fname] += 1
    else:
      self.warn("music checking bypassed; unable to open music folder")

  # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  # report on possible image or music file problems (used too many times, not used at all)
  #
  # which: "image" or "music file"
  # flag:  self.imageDirectory or self.musicDirectory
  # dict:  self.imageDict or self.musicDict
  # option: self.imageCheck or self.musicCheck
  # whichoption: "-img" or "-mus"
  def fileReport(self, which, flag, dict, option, whichoption):
    if flag:
      msgIssued = False
      notUsed = 0
      notUsedList = []
      multiplyUsed = 0
      multiplyUsedList = []
      for k in dict:
        if dict[k] == 0: # unused file
          notUsed += 1
          notUsedList.append(k)
        elif (which == "music" or k != self.cimage) and dict[k] > 1: # used multiple times (exempt cover image
                                                         # in case PPer decided to use it in HTML)
          multiplyUsed += 1
          multiplyUsedList.append(k)

      notUsedS = "s" if notUsed > 1 else ""
      multiplyUsedS = "s" if multiplyUsed > 1 else ""

      if option: # full report?
        if notUsed:
          self.warn("{} {}{} apparently not used:".format(notUsed, which, notUsedS))
          for t in notUsedList:
            self.warn("  {}".format(t))
        if multiplyUsed:
          self.info("{} {}{} used multiple times:".format(multiplyUsed, which, multiplyUsedS))
          for t in multiplyUsedList:
            self.info("  {} ({}x)".format(t, dict[t]))

      else:  # summary only
        if notUsed:
          self.warn("{} {}{} apparently unused. Rerun with {} option for more information".format(notUsed, which, notUsedS, whichoption))
        if multiplyUsed:
          self.info("{} {}{} used multiple times. Rerun with {} option for more information".format(multiplyUsed, which, multiplyUsedS, whichoption))



  def doChecks(self):
    rb = [] # report buffer
    links = {} # map of links
    targets = {} # map of targets
    nonlowerl = {} # mixed-case links
    nonlowert = {}
    # build links
    for i,line in enumerate(self.wb):
      m = re.search(r"href=[\"']#(.*?)[\"']", line)
      while m:            # could have more than one in a line
        t = m.group(1)
        if not "Page" in t:
          tl = t.lower()
          if t != tl: # remember any mixed- or upper-case links in a set in nonlowerl
            if tl in nonlowerl:
              nonlowerl[tl].add(t)
            else:
              nonlowerl[tl] = set()
              nonlowerl[tl].add(t)
        if t in links:
          if not "Page" in t:
            self.linkinfo.add("[7] ")
            self.linkinfo.add("[7]Note: duplicate link: {}".format(t))
        else:
          links[t] = 1
        line = re.sub(re.escape(m.group(0)), "", line, 1) # remove the one we found
        m = re.search(r"href=[\"']#(.*?)[\"']", line)  # look for another one

      m = re.search(r"href=[\"']([^#].*?)[\"']", line) # now look for external links that we can't check
      while m:            # could have more than one in a line
        t = m.group(1)
        if t.startswith("music/"):  # handle links to music files
          t = t[6:]
          self.checkMusic(t)
        elif not t.startswith("images/"):    # don't worry about links to our image files
          self.linkinfo.add("[4] ")
          self.linkinfo.add("[4]Warning: cannot validate external link: {}".format(t))
        line = re.sub(re.escape(m.group(0)), "", line, 1) # remove the one we found
        m = re.search(r"href=[\"']([^#].*?)[\"']", line)  # look for another one

    # build targets
    for i,line in enumerate(self.wb):

      m = re.search(r"id=[\"'](.+?)[\"']", line)
      while m:
        t = m.group(1)
        if not "Page" in t:
          tl = t.lower()
          if t != tl: # remember any mixed- or upper-case targets in a set in nonlowert
            if tl in nonlowert:
              nonlowert[tl].add(t)
            else:
              nonlowert[tl] = set()
              nonlowert[tl].add(t)
        if t in targets:
          self.linkinfo.add("[3] ")
          self.linkinfo.add("[3]Error: Duplicate target: {}".format(t))
        else:
          targets[t] = 1
        line = re.sub(re.escape(m.group(0)), "", line, 1)
        m = re.search(r"id=[\"'](.+?)[\"']", line)

    # match links to targets
    for key in links:
      if key not in targets:
        self.linkinfo.add("[2] ")
        self.linkinfo.add("[2]Error: Missing target: {}".format(key))
        kl = key.lower()
        if kl in nonlowert:
          self.linkinfo.add("[2]Note:  Check for case mismatch; target {} exists as {}".format(key, nonlowert[kl]))

    de_css = self.css.showde()

    for key in targets:
      if key not in links:
        if not "Page" in key:
          found = False
          # need to examine PPer-supplied CSS, if any, as "target" could just be an id= used for CSS
          if de_css:      # if any PPer-supplied CSS
            key2 = "#" + key
            for s in de_css:
              if key2 in s:
                found = True
          if not found:
            self.linkinfo.add("[5] ")
            self.linkinfo.add("[5]Note: Unused target: {} ".format(key))
            kl = key.lower()
            if kl != key:
              if kl in nonlowerl:
                self.linkinfo.add("[6]Note: Check for case mismatch; a link to {} exists as {}".format(key, nonlowerl[kl]))
              elif kl in links:
                self.linkinfo.add("[6]Note: Check for case mismatch; a link to {} exists as {}".format(key, kl))


    rb = self.linkinfo.show()
    if len(rb):
      self.warn("Possible link or target problems:")
      for w in rb:
        self.stderr.write(w + '\n')

    # report on image or music files used too many times or not used at all
    self.fileReport("image", self.imageDirectoryOK, self.imageDict, self.imageCheck, "-img")
    self.fileReport("music file", self.musicDirectoryOK, self.musicDict, self.musicCheck, "-mus")


  def process(self):

    self.keepFnHere = False
    self.cl = 0
    while self.cl < len(self.wb):
      if "a" in self.debug:
        s = self.wb[self.cl]
        self.print_msg( s)  # print the current line
      if not self.wb[self.cl]: # skip blank lines
        self.cl += 1
        continue
      # will hit either a dot directive, a user-defined <div>, or wrappable text
      if re.match(r"\.([a-z]|⓭DV-)", self.wb[self.cl]):
        self.doDot()
        continue
      if (self.wb[self.cl].startswith("<div class=") or # skip over several <div> cases generated by .dv
          self.wb[self.cl].startswith("<div style=") or
          self.wb[self.cl] == "</div>"):
        self.cl += 1
        continue
      if self.wb[self.cl] == "<div⓭>": # one more case of .dv to skip over, but this one needs fixup
        self.wb[self.cl] = "<div>"    # remove the ⓭ that marked this one for us
        self.cl += 1
        continue

      # don't turn standalone .bn info lines into paragraphs
      if self.bnPresent and self.is_bn_line(self.wb[self.cl]):
        self.cl += 1
        continue

      # don't turn standalone .pn info lines into paragraphs, either
      if self.wb[self.cl].startswith("⑯"): # could it be page info?
        m = self.pnmatch.match(self.wb[self.cl]) # Yes; see if it's just (solely) a page number
        if m:      # yes, it's solely a page number
          self.cl += 1 # leave it in place for later handling
          continue

      self.doPara() # it's a paragraph to wrap

    if len(self.fnlist):  # any saved footnotes that didn't have a .fm to generate them?
      self.warn("Footnotes encountered after last \".fm lz=h\" have not been generated. Missing a .fm somewhere?")

  def makeHTML(self):
    self.doHeader()
    self.doFooter()
    self.placeCSS()
    self.cleanup()
    self.doHTMLSr()

  # build dictionary of files in images or music directory
  # later we'll check which were used
  def buildFilesDict(self):

    # which: string, images or music
    # filetypes: list of allowable file types
    def buildDict(which, filetypes, msginsert):
      fileDict = {}
      filepath = os.path.join(os.path.dirname(self.srcfile), which)
      DirectoryOK = True
      try:
        filelist = os.listdir(filepath)
      except FileNotFoundError:
        DirectoryOK = False

      if DirectoryOK:
        for s in filelist:
          found = False
          for t in filetypes:
            if s.endswith(t):
              found = True
              fileDict[s] = 0
          if not found:
            self.warn("file {} in {} folder does not have type {}".format(s, which, msginsert))

      if which == "images":
        self.imageDirectoryOK = DirectoryOK
        self.imageDict = fileDict
      else:
        self.musicDirectoryOK = DirectoryOK
        self.musicDict = fileDict

    buildDict("images", [".jpg", ".png"], ".jpg or .png")
    buildDict("music", [".mid"], ".mid")


  def run(self): # HTML
    self.loadFile(self.srcfile)
    self.buildFilesDict()
    self.preprocess()
    if self.gk_requested or self.dia_requested: # override output encoding if doing Greek or diacritics
      self.encoding = "utf_8"
    self.process()
    self.postprocess()
    self.deStyle()
    self.makeHTML()
    self.doChecks()
    self.saveFile(self.dstfile)

# ====== ppgen ==========================================================================

# python3 ppgen.py -i secret-src.txt       generates secret-utf8.txt, secret.html
# python3 ppgen.py -i secret-src.txt -o t  generates secret-utf8.txt only
# python3 ppgen.py -i secret-src.txt -o h  generates secret.html only
# source file must be filename-src.txt, UTF-8 is detected.
#
# debug options:
# 'd' enables dprint, 's' retains runtime-generated styles,
# 'a' shows lines as they are processed, 'p' shows architecture
# 'r' shows regex results for .sr, 'l' provides detailed logging for Greek conversions
# 'x' produces "title" style page numbering regardless of .nr pnstyle setting (intended for regression testing)

# Load configuration file (ppgen.ini) and provide defaults
def loadConfig(ini_file):
  config = configparser.ConfigParser(allow_no_value=True)

  # set default values
  config.read_dict({'CSS':
                       {'h1': 'text-align: center; font-weight: normal; font-size: 1.4em;',
                        'h2': 'text-align: center; font-weight: normal; font-size: 1.2em;',
                        'h3': 'text-align: center; font-weight: normal; font-size: 1.2em;',
                        'h4': 'text-align: center; font-weight: normal; font-size: 1.0em;',
                        'h5': 'text-align: center; font-weight: normal; font-size: 1.0em;',
                        'h6': 'text-align: center; font-weight: normal; font-size: 1.0em;',
                        },
                   'Nregs': {}
                   })

  config_encoding = ""
  fn = ""

  if ini_file != "none":  # if user wants use to use a .ini file

    if ini_file:
      s = "ppgen-" + ini_file + ".ini"
    else:
      s = "ppgen.ini"

    # determine location of config file
    if os.path.isfile(s): # prefer local version
      fn = s
    else:
      s = os.path.join(os.path.dirname(os.path.realpath(__file__)), s) # alternate location
      if os.path.isfile(s):
        fn = s
    if fn:
      try:
        config_file = open(fn, "r", encoding='ascii').read()
        config_encoding = "ASCII" # we consider ASCII as a subset of Latin-1 for DP purposes
      except Exception as e:
        pass

      if config_encoding == "":
        try:
          config_file = open(fn, "rU", encoding='utf-8-sig').read()
          config_encoding = "utf_8"
        except Exception as e:
          pass

      if config_encoding == "":
        try:
          config_file = open(fn, "r", encoding='latin_1').read()
          config_encoding = "latin_1"
        except Exception as e:
          pass

    if config_encoding:
      print("Processing ini file {}".format(fn))

      try:
        config.read(fn, encoding=config_encoding)
      except:
        traceback.print_exc()
        sys.stderr.write("Above error occurred while reading ini file {}\n".format(fn))

  # convert any multi-line header values to single line
  for k in config['CSS']:
    config['CSS'][k] = config['CSS'][k].replace('\n', ' ')

  return config


def main():
  # process command line
  parser = argparse.ArgumentParser(description='ppgen generator')
  parser.add_argument('-i', '--infile', help='UTF-8 or Latin-1 input file')
  parser.add_argument('-l', '--log', help="display Latin-1, diacritic, and Greek conversion logs",
                      action="store_true")
  parser.add_argument('-d', '--debug', nargs='?', default="", help='debug flags (d,s,a,p,r,l,x,e,m)')
  # debug "a" logs (many of the) source lines processed
  # debug "d" forces additional debugging info in some error cases (.sr, .pm/<pm>, .ul/ol/dl class generation)
  # debug "e" forces all messages to stderr, even informational ones
  # debug "l" forces additional reporting in Greek processing
  # debug "m" forces additional debugging info for .pm/<pm>
  # debig "p" causes ppgen to print platform info
  # debug "r" forces additional reporting in .sr processing
  # debug "s" forces ppgen to keep style= info rather than generating unique classes
  # debug "x" forces "title" style for page numbering, rather than "content"
  parser.add_argument('-o', '--output_format', default="hu",
                      help='output format (HTML:h, text:t, u or l)')
  parser.add_argument('-a', '--anonymous', action='store_true',
                      help='do not identify version/timestamp in HTML')
  parser.add_argument("-v", "--version", help="display version and exit", action="store_true")
  parser.add_argument("-cvg", "--listcvg",
                      help="list Greek and diacritic table to file ppgen-cvglist.txt and exit",
                      action="store_true")
  parser.add_argument("-f", "--filter",
                      help="UTF-8 filter file for .cv/.gk commands (also terminates after .cv and .gk processing)")
  parser.add_argument("-sbin", "--srcbin", action="store_true",
                      help="create -src.txt.bin file and terminate")
  parser.add_argument("-ppqt2", "--ppqt2", action="store_true",
                      help="create .ppqt file in addition to any .bin file")
  parser.add_argument("-pmok", "--pythonmacrosok", action="store_true",
                      help="allow macros written in Python without prompting user for permission")
  parser.add_argument("-img", "--imagecheck", action="store_true",
                      help="create detailed report of unused image files")
  parser.add_argument("-mus", "--musiccheck", action="store_true",
                      help="create detailed report of unused music files")
  parser.add_argument("-ini", "--ini_file",
                      help="ini file suffix (or none)")
  parser.add_argument("-std", "--stdout", action="store_true",
                      help="force all messages to stdout (useful for testing)")


  args = parser.parse_args()

  #setup stdout and stderr so they can handle UTF-8 output on Windows
  ppgen_stderr = open(sys.stderr.fileno(), mode='w', encoding='utf-8', buffering=1)
  if 'e' in args.debug:
    ppgen_stdout = ppgen_stderr
  else:
    ppgen_stdout = open(sys.stdout.fileno(), mode='w', encoding='utf-8', buffering=1)

  # version request. print and exit
  if args.version:
    ppgen_stdout.write("{}".format(VERSION) + '\n')
    exit(1)

  ppgen_stdout.write("ppgen {}".format(VERSION) + '\n')

  if 'p' in args.debug:
    ppgen_stdout.write("running on {}".format(platform.system()) + '\n')
    ppgen_stdout.write("Python version: {}".format(platform.python_version()) + '\n')

  # -f and -sbin are mutually exclusive
  if args.filter and args.srcbin:
    ppgen_stderr.write("Error: Both -f (--filter) and -sbin (--srcbin) specified; terminating" + '\n')
    exit(1)

  # infile of mystery-src.txt will generate mystery.txt and mystery.html

  if not args.listcvg and (args.infile == None or not args.infile):
    ppgen_stderr.write("infile must be specified. use \"--help\" for help" + '\n')
    exit(1)

  # Handle config file (ppgen.ini)
  config = loadConfig(args.ini_file)

  # if PPer did not explicitly ask for utf-8, only create it if input is encoded in utf-8
  if 't' in args.output_format:
    ppt = Ppt(args, "u", config, ppgen_stdout, ppgen_stderr)
    ppt.run()
    ppt = Ppt(args, "l", config, ppgen_stdout, ppgen_stderr)
    ppt.run()


  # if PPer explicitly asked for utf-8 always create it, even if input is encoded in Latin-1 or ASCII
  # UTF-8 only
  if 'u' in args.output_format:
    ppt = Ppt(args, "U", config, ppgen_stdout, ppgen_stderr)
    ppt.run()


  # Latin-1 only
  if 'l' in args.output_format:
   ppt = Ppt(args, "l", config, ppgen_stdout, ppgen_stderr)
   ppt.run()


  if 'h' in args.output_format:
    ppgen_stdout.write("creating HTML version" + '\n')
    pph = Pph(args, "h", config, ppgen_stdout, ppgen_stderr)
    pph.run()

  ppgen_stdout.write("done." + '\n')



if __name__ == '__main__':
    main()

# Special unicode characters used within ppgen to avoid iterference with PPer-provided text, assuming
#   that for some reason the PPer doesn't decide to use one of them for some other purpose.
#
# Note: When adding characters to this table be sure to update check_for_pppgen_special_characters()
#       so it can properly complain if the PPer happens to use any of these characters.
#
# \u14aa  ᒪ   CANADIAN SYLLABICS MA # precedes lang= info
# \u14a7  ᒧ   CANADIAN SYLLABICS MO # follows lang= info
# 4\u24d3 ⓓ   CIRCLED LATIN SMALL LETTER D # four dot ellipsis
# 3\u24d3 ⓓ   CIRCLED LATIN SMALL LETTER D # three dot ellipsis
# \u24d3\u24e2.. ⓢ    CIRCLED LATIN SMALL LETTER D + CIRCLED LATIN SMALL LETTER S repeated 2.5
#                     times # 3 dot ellipsis, spaced
# \u2460  ①   CIRCLED DIGIT ONE   # \{
# \u2461  ②   CIRCLED DIGIT TWO   # \}
# \u2462  ③   CIRCLED DIGIT THREE # \[
# \u2463  ④   CIRCLED DIGIT FOUR  # \]
# \u2464  ⑤   CIRCLED DIGIT FIVE  # \<
# \u2465  ⑥   CIRCLED DIGIT SIX   # \:
# \u2466  ⑦   CIRCLED DIGIT SEVEN # used in footnote processing (along with circled 11/12/13/14)
# \u2467  ⑧   CIRCLED DIGIT EIGHT # Used for leading nbsp in .ti processing
# \u2468  ⑨   CIRCLED DIGIT NINE  # \- (so it doesn't become an em-dash later)
# \u2469  ⑩   CIRCLED NUMBER TEN  # temporarily protect \| during Greek conversion
# \u246a  ⑪   CIRCLED NUMBER ELEVEN # used in footnote processing (along with 7/12/13/14)
# \u246b  ⑫   CIRCLED NUMBER TWELVE # used in footnote processing (along with 7/11/13/14)
# \u246c  ⑬   CIRCLED NUMBER THIRTEEN # used in footnote processing (along with 7/11/12/14)
# \u246d  ⑭   CIRCLED NUMBER FOURTEEN # used in footnote processing (along with 7/11/12/13)
#                 "⑪" becomes "<" in final HTML
#                 "⑫"         ">"
#                 "⑬"         "["
#                 "⑭"         "]"
# \u246e  ⑮   CIRCLED NUMBER FIFTEEN # temporarily protect \(space) during Greek conversion
# \u246f  ⑯   CIRCLED NUMBER SIXTEEN # precedes page number info
# \u2470  ⑰   CIRCLED NUMBER SEVENTEEN # follows page number info
# \u2471  ⑱   CIRCLED NUMBER EIGHTEEN # surrounds .bn info
# \u2472  ⑲   CIRCLED NUMBER NINETEEN # Protects PPer supplied links (#...#)
# \u2473  ⑳   CIRCLED NUMBER TWENTY # \>
# \u24c8  Ⓢ   CIRCLED LATIN CAPITAL LETTER S # (non-breaking space)
# \u24c9  Ⓣ   CIRCLED LATIN CAPITAL LETTER T # (zero space)
# \u24ca  Ⓤ   CIRCLED LATIN CAPITAL LETTER U # (thin space)
# \u24cb  Ⓥ   CIRCLED LATIN CAPITAL LETTER V # (thick space)
# \u24cf  Ⓩ   CIRCLED LATIN CAPITAL LETTER Z # &
# \u24e2  ⓢ   CIRCLED LATIN SMALL LETTER S # non-breaking space (\  or \_ or &nbsp;)
# \u24e3  ⓣ   CIRCLED LATIN SMALL LETTER T # zero space (\&)
# \u24e4  ⓤ   CIRCLED LATIN SMALL LETTER U # thin space (\^)
# \u24e5  ⓥ   CIRCLED LATIN SMALL LETTER V # thick space (\|)
# \u24ea  ⓪   CIRCLED DIGIT 0 # (\#)
# \u24eb  ⓫   NEGATIVE CIRCLED NUMBER ELEVEN # temporary substitute for | in inline HTML sidenotes until postprocessing
# \u24ec  ⓬   NEGATIVE CIRCLED NUMBER TWELVE # temporary substitute for <br> in text wrapping
# \u24ed  ⓭   NEGATIVE CIRCLED NUMBER THIRTEEN # temporarily marks end of .dv blocks in HTML, .⓭DV-
#                                                and beginning of the div for .dv without a class or style element
# \u24ee  ⓮   NEGATIVE CIRCLED NUMBER FOURTEEN # used to protect/convert ^^ in input text to ^ in output text
# \u24ef  ⓯   NEGATIVE CIRCLED NUMBER FIFTEEN  # used to protect/convert __{ in input text to _{ in output text
# \u24f5  ⓵   DOUBLE CIRCLED DIGIT ONE # temporary substitute for <i>
# \u24f6  ⓶   DOUBLE CIRCLED DIGIT TWO # temporary substitute for <b>
# \u24f7  ⓷   DOUBLE CIRCLED DIGIT THREE # temporary substitute for <g>
# \u24f8  ⓸   DOUBLE CIRCLED DIGIT FOUR # temporary substitute for <sc>
# \u24f9  ⓹   DOUBLE CIRCLED DIGIT FIVE # temporary substitute for <f>
# \u24fa  ⓺   DOUBLE CIRCLED DIGIT SIX # temporary substitute for <em>
# \u24fb  ⓻   DOUBLE CIRCLED DIGIT SEVEN # temporary substitute for <strong>
# \u24fc  ⓼   DOUBLE CIRCLED DIGIT EIGHT # temporary substitute for <cite>
# \u24fd  ⓽   DOUBLE CIRCLED DIGIT NINE # temporary substitute for <u>
# \u25ee  ◮   UP-POINTING TRIANGLE WITH RIGHT HALF BLACK # <b> or <strong> (becomes =) (Not used any more; see \u24f6)
# \u25f8  ◸   UPPER LEFT TRIANGLE # precedes superscripts
# \u25f9  ◹   UPPER RIGHT TRIANGLE # follows superscripts
# \u25fa  ◺   LOWER LEFT TRIANGLE # precedes subscripts
# \u25ff  ◿   LOWER RIGHT TRIANGLE # follows subscripts
# \u2ac9  ⫉   SUBSET OF ABOVE ALMOST EQUAL TO # used temporarily during page number reference processing and Greek processing
#
#
# ppgen css numbers:
#
# 1100      body if pnshow
# 1100      body if not pnshow
# 1100      h1
# 1100      h2
# 1100      h3
# 1100      h4
# 1100      h5
# 1100      h6
# 1105-1108 .pageno if pnshow
# 1109      .pageno:after if pnshow
# 1170      p
# 1171      .li-p-first, -mid, -last, -only
# 1202      <xl>
# 1202      <xxl>
# 1203      <s>
# 1204      <xs>
# 1205      <xxs>
# 1205      <u>
# 1209      <c>     will duplicate for various colors
# 1210      <abbr> and abbr.spell
# 1215      .nf b: .lg-container-b
# 1216             @media handheld
# 1217      .nf l: .lg-container-l
# 1218             @media handheld
# 1219      .nf r: .lg-container-r
# 1220             @media handheld
# 1221      .nf b/l/r: .linegroup
# 1222                 @media handheld
# 1223                .linegroup .group0 (if override to margin 0)
# 1223                .linegroup .group
# 1224                .linegroup .line
# 1225                div.linegroup > :first-child
# 1227                .linegroup .<indent-class-name>
# 1240      .ix: ul, li
# 1241      .dl/dt/dd
# 1378      <g>     gesperrt
# 1379      Handheld version of <g>
# 1430      div.footnote
# 1431      div.footnote>:first-child
# 1432      div.footnote p (if indented paragraphs)
# 1432      div.footnote .label (if block paragraphs)
# 1465-1467 .pb (div.pbb, hr.pb, and handheld version)
# 1500      .sidenote, .sni
# 1501      @media handheld sidenote
# 1502      .sni
# 1503      .hidev
# 1576      .chapter
# 1600      .figcenter
# 1600      .figleft
# 1600      .figright
# 1601      div.figcenter p
# 1601      div.figleft p
# 1601      div.figright p
# 1602      Handheld version of .figleft
# 1602      Handheld version of .figright
# 1608      .figcenter img
# 1608      .figleft img
# 1608      .figright img
# 1610      various illustration widths (idn)
# 1610      various epub illustration widths
# 1611      various caption widths (icn)
# 1613      various caption alignments (icn)
# 1614      something else about image widths (ign)
# 1670      .table<number> width
# 1671      .table<number> width in epub
# 1672      table border class definitions
# 1700      table column width
# 1873      .nf c: .nf-center
# 1876             .nf-center-c0 (if indented paragraphs)
# 1876             .nf-center-c1 (if block paragraphs)
# 1920      img.drop-capi
# 1921      .di: p.drop-capi<number>
# 1922           p.drop-capi<number>:first-letter
# 1923-1926      @media handheld version of 1921-1922
# 1930      .dc: p.drop-capa<number>
# 1931           p.drop-capa<number>:first-letter
# 1933-1937      @media handheld version of 1930-1931
# 2000-up   Dynamic styles created from styles needed in the text
# 3000-up   User supplied css from .de
