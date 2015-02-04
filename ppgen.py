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
import struct
import imghdr
import traceback

VERSION="3.46eGreekf"  # 3-Feb-2015    Greek conversion + diacritic conversion


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
  bb = [] # GG .bin file buffer
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
  csslc = 3000 # CSS line counter for user defined classes
  dtitle = "" # display title for HTML
  cimage = "cover.jpg" # default cover image

  nregs = {} # named registers
  macro = {} # user macro storage
  caption_model = {} # storage for named caption models for multi-line captions in text output

  mau = [] # UTF-8
  mal = [] # user-defined Latin-1

  linelimitwarning = 75

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

  gk_user = []                          # PPer provided Greek transliterations will go here

  gk = [                               # builtin Greek transliterations
     ('S[Tt]', '\u03DA', 'ST or St (Stigma)'),      # must handle stigmas before s
     ('st', '\u03DB', 'st (stigma)'),
     ('^s\'', '\u03C3\'', 's may be regular', "\u03c3"),    # handle s' as regular sigma as the first characters of the string
     ('([^Pp])s\'', '\\1\u03C3\'', ' sigma or', ""),  # handle s' as regular sigma elsewhere in string
     ('^s($|\\W)', '\u03C2\\1', 'final sigma based', "\u03c2"),       # handle solo s at start of string as final sigma
     ('([^Pp])s($|\\W)', '\\1\u03C2\\2', ' on situation', ""),  # handle ending s elsewhere in string as final sigma
     #('s($|\\W)', '\u03C2\\1', 's($|\\W)'),  # final s (this expression from Guiguts replaced by the 4 above)
     ('th', '\u03B8', 'th'),
     ('ph', '\u03C6', 'ph'),
     ('T[Hh]', '\u0398', 'TH or Th'),
     ('P[Hh]', '\u03A6', 'PH or Ph'),
     (r'u\\\+', '\u1FE2', 'u\\\+'),
     ('u/\+', '\u1FE3', 'u/+'),
     ('u~\+', '\u1FE7', 'u~+'),
     #('u/\+', '\u03B0', 'u/+'),    # u/+ has two values?
     (r'u\)\\', '\u1F52', 'u)\\'),
     (r'u\(\\', '\u1F53', 'u(\\'),
     ('u\)\/', '\u1F54', 'u)/'),
     ('u\(\/', '\u1F55', 'u(/'),
     ('u~\)', '\u1F56', 'u~)'),
     ('u~\(', '\u1F57', 'u~('),
     (r'U\(\\', '\u1F5B', 'U(\\'),
     ('U\(\/', '\u1F5D', 'U(/'),
     ('U~\(', '\u1F5F', 'U~('),
     ('u\+', '\u03CB', 'u+'),
     ('U\+', '\u03AB', 'U+'),
     ('u=', '\u1FE0', 'u='),
     ('u_', '\u1FE1', 'u_'),
     ('r\)', '\u1FE4', 'r)'),
     ('r\(', '\u1FE5', 'r('),
     ('u~', '\u1FE6', 'u~'),
     ('U=', '\u1FE8', 'U='),
     ('U_', '\u1FE9', 'U_'),
     (r'U\\', '\u1FEA', 'U\\'),
     ('U\/', '\u1FEB', 'U/'),
     (r'u\\', '\u1F7A', 'u\\'),
     ('u\/', '\u1F7B', 'u/'),
     ('u\)', '\u1F50', 'u)'),
     ('u\(', '\u1F51', 'u('),
     ('U\(', '\u1F59', 'U('),
     ('\?', '\u037E', '?'),
     (';', '\u0387', ';'),
     (r'a\)\\\|', '\u1F82', 'a)\\|'), # grkbeta3
     (r'a\(\\\|', '\u1F83', 'a(\\|'),
     ('a\)/\|', '\u1F84', 'a)/|'),
     ('a\(/\|', '\u1F85', 'a(/|'),
     ('a~\)\|', '\u1F86', 'a~)|'),
     ('a~\(\|', '\u1F87', 'a~(|'),
     (r'A\)\\\|', '\u1F8A', 'A)\\|'),
     (r'A\(\\\|', '\u1F8B', 'A(\\|'),
     ('A\)/\|', '\u1F8C', 'A)/|'),
     ('A\(/\|', '\u1F8D', 'A(/|'),
     ('A~\)\|', '\u1F8E', 'A~)|'),
     ('A~\(\|', '\u1F8F', 'A~(|'),
     (r'ê\)\\\|', '\u1F92', 'ê)\\|'),
     (r'ê\(\\\|', '\u1F93', 'ê(\\|'),
     (r'ê\)/\|', '\u1F94', 'ê)/|'),
     (r'ê\(/\|', '\u1F95', 'ê(/|'),
     ('ê~\)\|', '\u1F96', 'ê~)|'),
     ('ê~\(\|', '\u1F97', 'ê~(|'),
     (r'Ê\)\\\|', '\u1F9A', 'Ê)\\|'),
     (r'Ê\(\\\|', '\u1F9B', 'Ê(\\|'),
     ('Ê\)/\|', '\u1F9C', 'Ê)/|'),
     ('Ê\(/\|', '\u1F9D', 'Ê(/|'),
     ('Ê~\)\|', '\u1F9E', 'Ê~)|'),
     ('Ê~\(\|', '\u1F9F', 'Ê~(|'),
     (r'ô\)\\\|', '\u1FA2', 'ô)\\|'),
     (r'ô\(\\\|', '\u1FA3', 'ô(\\|'),
     ('ô\)/\|', '\u1FA4', 'ô)/|'),
     ('ô\(/\|', '\u1FA5', 'ô(/|'),
     ('ô~\)\|', '\u1FA6', 'ô~)|'),
     ('ô~\(\|', '\u1FA7', 'ô~(|'),
     (r'Ô\)\\\|', '\u1FAA', 'Ô)\\|'),
     (r'Ô\(\\\|', '\u1FAB', 'Ô(\\|'),
     ('Ô\)/\|', '\u1FAC', 'Ô)/|'),
     ('Ô\(/\|', '\u1FAD', 'Ô(/|'),
     ('Ô~\)\|', '\u1FAE', 'Ô~)|'),
     ('Ô~\(\|', '\u1FAF', 'Ô~(|'),
     (r'a\)\\', '\u1F02', 'a)\\'),  #grkbeta2
     (r'a\(\\', '\u1F03', 'a(\\'),
     ('a\)/', '\u1F04', 'a)/'),
     ('a\(/', '\u1F05', 'a(/'),
     ('a~\)', '\u1F06', 'a~)'),
     ('a~\(', '\u1F07', 'a~('),
     (r'A\)\\', '\u1F0A', 'A)\\'),
     (r'A\(\\', '\u1F0B', 'A(\\'),
     ('A\)/', '\u1F0C', 'A)/'),
     ('A\(/', '\u1F0D', 'A(/'),
     ('A~\)', '\u1F0E', 'A~)'),
     ('A~\(', '\u1F0F', 'A~('),
     (r'e\)\\', '\u1F12', 'e)\\'),
     (r'e\(\\', '\u1F13', 'e(\\'),
     ('e\)/', '\u1F14', 'e)/'),
     ('e\(/', '\u1F15', 'e(/'),
     (r'E\)\\', '\u1F1A', 'E)\\'),
     (r'E\(\\', '\u1F1B', 'E(\\'),
     ('E\)/', '\u1F1C', 'E)/'),
     ('E\(/', '\u1F1D', 'E(/'),
     (r'ê\)\\', '\u1F22', 'ê)\\'),
     (r'ê\(\\', '\u1F23', 'ê(\\'),
     ('ê\)/', '\u1F24', 'ê)/'),
     ('ê\(/', '\u1F25', 'ê(/'),
     ('ê~\)', '\u1F26', 'ê~)'),
     ('ê~\(', '\u1F27', 'ê~('),
     (r'Ê\)\\', '\u1F2A', 'Ê)\\'),
     (r'Ê\(\\', '\u1F2B', 'Ê(\\'),
     ('Ê\)/', '\u1F2C', 'Ê)/'),
     ('Ê\(/', '\u1F2D', 'Ê(/'),
     ('Ê~\)', '\u1F2E', 'Ê~)'),
     ('Ê~\(', '\u1F2F', 'Ê~('),
     (r'i\)\\', '\u1F32', 'i)\\'),
     (r'i\(\\', '\u1F33', 'i(\\'),
     ('i\)/', '\u1F34', 'i)/'),
     ('i\(/', '\u1F35', 'i(/'),
     ('i~\)', '\u1F36', 'i~)'),
     ('i~\(', '\u1F37', 'i~('),
     (r'I\)\\', '\u1F3A', 'I)\\'),
     (r'I\(\\', '\u1F3B', 'I(\\'),
     ('I\)/', '\u1F3C', 'I)/'),
     ('I\(/', '\u1F3D', 'I(/'),
     ('I~\)', '\u1F3E', 'I~)'),
     ('I~\(', '\u1F3F', 'I~('),
     (r'o\)\\', '\u1F42', 'o)\\'),
     (r'o\(\\', '\u1F43', 'o(\\'),
     ('o\)/', '\u1F44', 'o)/'),
     ('o\(/', '\u1F45', 'o(/'),
     (r'O\)\\', '\u1F4A', 'O)\\'),
     (r'O\(\\', '\u1F4B', 'O(\\'),
     ('O\)/', '\u1F4C', 'O)/'),
     ('O\(/', '\u1F4D', 'O(/'),
     (r'y\)\\', '\u1F52', 'y)\\'),
     (r'y\(\\', '\u1F53', 'y(\\'),
     ('y\)/', '\u1F54', 'y)/'),
     ('y\(/', '\u1F55', 'y(/'),
     ('y~\)', '\u1F56', 'y~)'),
     ('y~\(', '\u1F57', 'y~('),
     (r'Y\(\\', '\u1F5B', 'Y(\\'),
     ('Y\(/', '\u1F5D', 'Y(/'),
     ('Y~\(', '\u1F5F', 'Y~('),
     (r'ô\)\\', '\u1F62', 'ô)\\'),
     (r'ô\(\\', '\u1F63', 'ô(\\'),
     ('ô\)/', '\u1F64', 'ô)/'),
     ('ô\(/', '\u1F65', 'ô(/'),
     ('ô~\)', '\u1F66', 'ô~)'),
     ('ô~\(', '\u1F67', 'ô~('),
     (r'Ô\)\\', '\u1F6A', 'Ô)\\'),
     (r'Ô\(\\', '\u1F6B', 'Ô(\\'),
     ('Ô\)/', '\u1F6C', 'Ô)/'),
     ('Ô\(/', '\u1F6D', 'Ô(/'),
     ('Ô~\)', '\u1F6E', 'Ô~)'),
     ('Ô~\(', '\u1F6F', 'Ô~('),
     ('a\)\|', '\u1F80', 'a)|'),
     ('a\(\|', '\u1F81', 'a(|'),
     ('A\)\|', '\u1F88', 'A)|'),
     ('A\(\|', '\u1F89', 'A(|'),
     ('ê\)\|', '\u1F90', 'ê)|'),
     ('ê\(\|', '\u1F91', 'ê(|'),
     ('Ê\)\|', '\u1F98', 'Ê)|'),
     ('Ê\(\|', '\u1F99', 'Ê(|'),
     ('ô\)\|', '\u1FA0', 'ô)|'),
     ('ô\(\|', '\u1FA1', 'ô(|'),
     ('Ô\)\|', '\u1FA8', 'Ô)|'),
     ('Ô\(\|', '\u1FA9', 'Ô(|'),
     (r'a\\\|', '\u1FB2', 'a\\|'),
     ('a/\|', '\u1FB4', 'a/|'),
     ('a~\|', '\u1FB7', 'a~|'),
     (r'ê\\\|', '\u1FC2', 'ê\\|'),
     ('ê/\|', '\u1FC4', 'ê/|'),
     ('ê~\|', '\u1FC7', 'ê~|'),
     (r'i\\\+', '\u1FD2', 'i\\+'),
     ('i/\+', '\u1FD3', 'i/+'),
     ('i~\+', '\u1FD7', 'i~+'),
     (r'y\\\+', '\u1FE2', 'y\\+'),
     ('y/\+', '\u1FE3', 'y/+'),
     ('y~\+', '\u1FE7', 'y~+'),
     (r'ô\\\|', '\u1FF2', 'ô\\|'),
     ('ô/\|', '\u1FF4', 'ô/|'),
     ('ô~\|', '\u1FF7', 'ô~|'),
     ('i/\+', '\u0390', 'i/+'),
     ('y/\+', '\u03B0', 'y/+'),
     ('a\)', '\u1F00', 'a)'),  #grkbeta1
     ('a\(', '\u1F01', 'a('),
     ('A\)', '\u1F08', 'A)'),
     ('A\(', '\u1F09', 'A('),
     (r'O\\', '\u1FF8', 'O\\'),
     ('O/', '\u1FF9', 'O/'),
     (r'Ô\\', '\u1FFA', 'Ô\\'),
     ('Ô/', '\u1FFB', 'Ô/'),
     ('Ô\|', '\u1FFC', 'Ô|'),
     ('e\)', '\u1F10', 'e)'),
     ('e\(', '\u1F11', 'e('),
     ('E\)', '\u1F18', 'E)'),
     ('E\(', '\u1F19', 'E('),
     ('ê\)', '\u1F20', 'ê)'),
     ('ê\(', '\u1F21', 'ê('),
     ('Ê\)', '\u1F28', 'Ê)'),
     ('Ê\(', '\u1F29', 'Ê('),
     ('i\)', '\u1F30', 'i)'),
     ('i\(', '\u1F31', 'i('),
     ('I\)', '\u1F38', 'I)'),
     ('I\(', '\u1F39', 'I('),
     ('o\)', '\u1F40', 'o)'),
     ('o\(', '\u1F41', 'o('),
     ('O\)', '\u1F48', 'O)'),
     ('O\(', '\u1F49', 'O('),
     ('y\)', '\u1F50', 'y)'),
     ('y\(', '\u1F51', 'y('),
     ('Y\(', '\u1F59', 'Y('),
     ('ô\)', '\u1F60', 'ô)'),
     ('ô\(', '\u1F61', 'ô('),
     ('Ô\)', '\u1F68', 'Ô)'),
     ('Ô\(', '\u1F69', 'Ô('),
     (r'a\\', '\u1F70', 'a\\'),
     ('a/', '\u1F71', 'a/'),
     (r'e\\', '\u1F72', 'e\\'),
     ('e/', '\u1F73', 'e/'),
     (r'ê\\', '\u1F74', 'ê\\'),
     ('ê/', '\u1F75', 'ê/'),
     (r'i\\', '\u1F76', 'i\\'),
     ('i/', '\u1F77', 'i/'),
     (r'o\\', '\u1F78', 'o\\'),
     ('o/', '\u1F79', 'o/'),
     (r'y\\', '\u1F7A', 'y\\'),
     ('y/', '\u1F7B', 'y/'),
     (r'ô\\', '\u1F7C', 'ô\\'),
     ('ô/', '\u1F7D', 'ô/'),
     ('a=', '\u1FB0', 'a='),
     ('a_', '\u1FB1', 'a_'),
     ('a\|', '\u1FB3', 'a|'),
     ('a~', '\u1FB6', 'a~'),
     ('A=', '\u1FB8', 'A='),
     ('A_', '\u1FB9', 'A_'),
     (r'A\\', '\u1FBA', 'A\\'),
     ('A/', '\u1FBB', 'A/'),
     ('A\|', '\u1FBC', 'A|'),
     ('ê\|', '\u1FC3', 'ê|'),
     ('ê~', '\u1FC6', 'ê~'),
     (r'E\\', '\u1FC8', 'E\\'),
     ('E/', '\u1FC9', 'E/'),
     (r'Ê\\', '\u1FCA', 'Ê\\'),
     ('Ê/', '\u1FCB', 'Ê/'),
     ('Ê\|', '\u1FCC', 'Ê|'),
     ('i=', '\u1FD0', 'i='),
     ('i_', '\u1FD1', 'i_'),
     ('i~', '\u1FD6', 'i~'),
     ('I=', '\u1FD8', 'I='),
     ('I_', '\u1FD9', 'I_'),
     (r'I\\', '\u1FDA', 'I\\'),
     ('I/', '\u1FDB', 'I/'),
     ('y=', '\u1FE0', 'y='),
     ('y_', '\u1FE1', 'y_'),
     ('r\)', '\u1FE4', 'r)'),
     ('r\(', '\u1FE5', 'r('),
     ('y~', '\u1FE6', 'y~'),
     ('Y=', '\u1FE8', 'Y='),
     ('Y_', '\u1FE9', 'Y_'),
     (r'Y\\', '\u1FEA', 'Y\\'),
     ('Y/', '\u1FEB', 'Y/'),
     ('R\(', '\u1FEC', 'R('),
     ('ô~', '\u1FF6', 'ô~'),
     ('ô\|', '\u1FF3', 'ô|'),
     ('I\+', '\u03AA', 'I+'),
     ('Y\+', '\u03AB', 'Y+'),
     ('i\+', '\u03CA', 'i+'),
     ('y\+', '\u03CB', 'y+'),
     ('\*#1', '\u03DE', '*#1'),
     ('#1', '\u03DE', '#1'),
     ('\*#2', '\u03DA', '*#2'),
     ('#2', '\u03DB', '#2'),
     ('\*#3', '\u03D8', '*#3'),
     ('#3', '\u03D9', '#3'),
     ('\*#5', '\u03E0', '*#5'),
     ('#5', '\u03E1', '#5'),
     ('#6', '\u20EF', '#6'),
     ('#10', '\u03FD', '#10'),
     ('#11', '\u03FF', '#11'),
     ('#13', '\u203B', '#13'),
     ('#14', '\u2E16', '#14'),
     ('#16', '\u03FE', '#16'),
     ('#55', '\u0259', '#55'),
     ('#73', '\u205A', '#73'),
     ('#74', '\u205D', '#74'),
     ('th', '\u03B8', 'th'),  # basic Greek transformations
     ('nch', '\u03B3\u03C7', 'nch'),
     ('ch', '\u03C7', 'ch'),
     ('ph', '\u03C6', 'ph'),
     ('C[Hh]', '\u03A7', 'CH or Ch'),
     ('T[Hh]', '\u0398', 'TH or Th'),
     ('P[Hh]', '\u03A6', 'PH or Ph'),
     ('ng', '\u03B3\u03B3', 'ng'),
     ('nk', '\u03B3\u03BA', 'nk'),
     ('nx', '\u03B3\u03BE', 'nx'),
     ('rh', '\u1FE5', 'rh'),
     ('ps', '\u03C8', 'ps'),
     ('ha', '\u1F01', 'ha'),
     ('he', '\u1F11', 'he'),
     ('hê', '\u1F21', 'hê'),
     ('hi', '\u1F31', 'hi'),
     ('ho', '\u1F41', 'ho'),
     ('hy', '\u1F51', 'hy'),
     ('hô', '\u1F61', 'hô'),
     ('ou', '\u03BF\u03C5', 'ou'),
     ('P[Ss]', '\u03A8', 'PS or Ps'),
     ('H[Aa]', '\u1F09', 'HA or Ha'),
     ('H[Ee]', '\u1F19', 'HE or He'),
     ('HÊ|Hê', '\u1F29', 'HÊ or Hê'),
     ('H[Ii]', '\u1F39', 'HI or Hi'),
     ('H[Oo]', '\u1F49', 'HO or Ho'),
     ('H[Yy]', '\u1F59', 'HY or Hy'),
     ('HÔ|Hô', '\u1F69', 'HÔ or Hô'),
     ('A', '\u0391', 'A'),
     ('a', '\u03B1', 'a'),
     ('B', '\u0392', 'B'),
     ('b', '\u03B2', 'b'),
     ('G', '\u0393', 'G'),
     ('g', '\u03B3', 'g'),
     ('D', '\u0394', 'D'),
     ('d', '\u03B4', 'd'),
     ('E', '\u0395', 'E'),
     ('e', '\u03B5', 'e'),
     ('Z', '\u0396', 'Z'),
     ('z', '\u03B6', 'z'),
     ('Ê', '\u0397', 'Ê'),
     ('ê', '\u03B7', 'ê'),
     ('I', '\u0399', 'I'),
     ('i', '\u03B9', 'i'),
     ('K', '\u039A', 'K'),
     ('k', '\u03BA', 'k'),
     ('L', '\u039B', 'L'),
     ('l', '\u03BB', 'l'),
     ('M', '\u039C', 'M'),
     ('m', '\u03BC', 'm'),
     ('N', '\u039D', 'N'),
     ('n', '\u03BD', 'n'),
     ('X', '\u039E', 'X'),
     ('x', '\u03BE', 'x'),
     ('O', '\u039F', 'O'),
     ('o', '\u03BF', 'o'),
     ('P', '\u03A0', 'P'),
     ('p', '\u03C0', 'p'),
     ('R', '\u03A1', 'R'),
     ('r', '\u03C1', 'r'),
     ('S', '\u03A3', 'S'),
     ('s', '\u03C3', 's'),
     ('T', '\u03A4', 'T'),
     ('t', '\u03C4', 't'),
     ('Y', '\u03A5', 'Y'),
     ('y', '\u03C5', 'y'),
     ('U', '\u03A5', 'U'),
     ('u', '\u03C5', 'u'),
     ('Ô', '\u03A9', 'Ô'),
     ('ô', '\u03C9', 'ô'),
     #('\?', '\u037E', '?'),
     #(';', '\u0387', ';'),
     ('J', '\u03D8', 'J (Archaic Koppa)'),
     ('j', '\u03D9', 'j (archaic koppa)'),
     ('W', '\u03DC', 'W (Digamma)'),
     ('w', '\u03DD', 'w (digamma)'),
     ('Q', '\u03DE', 'Q (Qoppa)'),
     ('q', '\u03DF', 'q (qoppa)'),
     ('C', '\u03E0', 'C (Sampi)'),
     ('c', '\u03E1', 'c (sampi)'),
    ]

  diacritics_user = []  # PPer-supplied diacritic markup will go here

  diacritics = [
    ('[=A]', '\u0100', '\\u0100'), # LATIN CAPITAL LETTER A WITH MACRON    (Latin Extended-A)
    ('[=a]', '\u0101', '\\u0101'), # LATIN SMALL LETTER A WITH MACRON
    ('[)A]', '\u0102', '\\u0102'), # LATIN CAPITAL LETTER A WITH BREVE
    ('[)a]', '\u0103', '\\u0103'), # LATIN SMALL LETTER A WITH BREVE
    ('[A,]', '\u0104', '\\u0104'), # LATIN CAPITAL LETTER A WITH OGONEK
    ('[a,]', '\u0105', '\\u0105'), # LATIN SMALL LETTER A WITH OGONEK
    ('[\'C]', '\u0106', '\\u0106'), # LATIN CAPITAL LETTER C WITH ACUTE
    ('[\'c]', '\u0107', '\\u0107'), # LATIN SMALL LETTER C WITH ACUTE
    ('[^C]', '\u0108', '\\u0108'), # LATIN CAPITAL LETTER C WITH CIRCUMFLEX
    ('[^c]', '\u0109', '\\u0109'), # LATIN SMALL LETTER C WITH CIRCUMFLEX
    ('[.C]', '\u010A', '\\u010A'), # LATIN CAPITAL LETTER C WITH DOT ABOVE
    ('[.c]', '\u010B', '\\u010B'), # LATIN SMALL LETTER C WITH DOT ABOVE
    ('[vC]', '\u010C', '\\u010C'), # LATIN CAPITAL LETTER C WITH CARON
    ('[vc]', '\u010D', '\\u010D'), # LATIN SMALL LETTER C WITH CARON
    ('[vD]', '\u010E', '\\u010E'), # LATIN CAPITAL LETTER D WITH CARON
    ('[vd]', '\u010F', '\\u010F'), # LATIN SMALL LETTER D WITH CARON
    ('[-D]', '\u0110', '\\u0110'), # LATIN CAPITAL LETTER D WITH STROKE
    ('[-d]', '\u0111', '\\u0111'), # LATIN SMALL LETTER D WITH STROKE
    ('[=E]', '\u0112', '\\u0112'), # LATIN CAPITAL LETTER E WITH MACRON
    ('[=e]', '\u0113', '\\u0113'), # LATIN SMALL LETTER E WITH MACRON
    ('[)E]', '\u0114', '\\u0114'), # LATIN CAPITAL LETTER E WITH BREVE
    ('[)e]', '\u0115', '\\u0115'), # LATIN SMALL LETTER E WITH BREVE
    ('[.E]', '\u0116', '\\u0116'), # LATIN CAPITAL LETTER E WITH DOT ABOVE
    ('[.e]', '\u0117', '\\u0117'), # LATIN SMALL LETTER E WITH DOT ABOVE
    #('[E,]', '\u0118', '\\u0118'), # LATIN CAPITAL LETTER E WITH OGONEK  # conflicts with markup for cedilla
    #('[e,]', '\u0119', '\\u0119'), # LATIN SMALL LETTER E WITH OGONEK    # conflicts with markup for cedilla
    ('[vE]', '\u011A', '\\u011A'), # LATIN CAPITAL LETTER E WITH CARON
    ('[ve]', '\u011B', '\\u011B'), # LATIN SMALL LETTER E WITH CARON
    ('[^G]', '\u011C', '\\u011C'), # LATIN CAPITAL LETTER G WITH CIRCUMFLEX
    ('[^g]', '\u011D', '\\u011D'), # LATIN SMALL LETTER G WITH CIRCUMFLEX
    ('[)G]', '\u011E', '\\u011E'), # LATIN CAPITAL LETTER G WITH BREVE
    ('[)g]', '\u011F', '\\u011F'), # LATIN SMALL LETTER G WITH BREVE
    ('[.G]', '\u0120', '\\u0120'), # LATIN CAPITAL LETTER G WITH DOT ABOVE
    ('[.g]', '\u0121', '\\u0121'), # LATIN SMALL LETTER G WITH DOT ABOVE
    ('[G,]', '\u0122', '\\u0122'), # LATIN CAPITAL LETTER G WITH CEDILLA
    ('[g,]', '\u0123', '\\u0123'), # LATIN SMALL LETTER G WITH CEDILLA
    ('[^H]', '\u0124', '\\u0124'), # LATIN CAPITAL LETTER H WITH CIRCUMFLEX
    ('[^h]', '\u0125', '\\u0125'), # LATIN SMALL LETTER H WITH CIRCUMFLEX
    ('[-H]', '\u0126', '\\u0126'), # LATIN CAPITAL LETTER H WITH STROKE
    ('[-h]', '\u0127', '\\u0127'), # LATIN SMALL LETTER H WITH STROKE
    ('[~I]', '\u0128', '\\u0128'), # LATIN CAPITAL LETTER I WITH TILDE
    ('[~i]', '\u0129', '\\u0129'), # LATIN SMALL LETTER I WITH TILDE
    ('[=I]', '\u012A', '\\u012A'), # LATIN CAPITAL LETTER I WITH MACRON
    ('[=i]', '\u012B', '\\u012B'), # LATIN SMALL LETTER I WITH MACRON
    ('[)I]', '\u012C', '\\u012C'), # LATIN CAPITAL LETTER I WITH BREVE
    ('[)i]', '\u012D', '\\u012D'), # LATIN SMALL LETTER I WITH BREVE
    ('[I,]', '\u012E', '\\u012E'), # LATIN CAPITAL LETTER I WITH OGONEK
    ('[i,]', '\u012F', '\\u012F'), # LATIN SMALL LETTER I WITH OGONEK
    ('[.I]', '\u0130', '\\u0130'), # LATIN CAPITAL LETTER I WITH DOT ABOVE
    #('[]', '\u0131', '\\u0131'), # LATIN SMALL LETTER DOTLESS I
    ('[IJ]', '\u0132', '\\u0132'), # LATIN CAPITAL LIGATURE IJ
    ('[ij]', '\u0133', '\\u0133'), # LATIN SMALL LIGATURE IJ
    ('[^J]', '\u0134', '\\u0134'), # LATIN CAPITAL LETTER J WITH CIRCUMFLEX
    ('[^j]', '\u0135', '\\u0135'), # LATIN SMALL LETTER J WITH CIRCUMFLEX
    ('[K,]', '\u0136', '\\u0136'), # LATIN CAPITAL LETTER K WITH CEDILLA
    ('[k,]', '\u0137', '\\u0137'), # LATIN SMALL LETTER K WITH CEDILLA
    ('[kra]', '\u0138', '\\u0138'), # LATIN SMALL LETTER KRA
    ('[\'L]', '\u0139', '\\u0139'), # LATIN CAPITAL LETTER L WITH ACUTE
    ('[\'l]', '\u013A', '\\u013A'), # LATIN SMALL LETTER L WITH ACUTE
    ('[L,]', '\u013B', '\\u013B'), # LATIN CAPITAL LETTER L WITH CEDILLA
    ('[l,]', '\u013C', '\\u013C'), # LATIN SMALL LETTER L WITH CEDILLA
    ('[vL]', '\u013D', '\\u013D'), # LATIN CAPITAL LETTER L WITH CARON
    ('[vl]', '\u013E', '\\u013E'), # LATIN SMALL LETTER L WITH CARON
    ('[L·]', '\u013F', '\\u013F'), # LATIN CAPITAL LETTER L WITH MIDDLE DOT
    ('[l·]', '\u0140', '\\u0140'), # LATIN SMALL LETTER L WITH MIDDLE DOT
    ('[/L]', '\u0141', '\\u0141'), # LATIN CAPITAL LETTER L WITH STROKE
    ('[/l]', '\u0142', '\\u0142'), # LATIN SMALL LETTER L WITH STROKE
    ('[\'N]', '\u0143', '\\u0143'), # LATIN CAPITAL LETTER N WITH ACUTE
    ('[\'n]', '\u0144', '\\u0144'), # LATIN SMALL LETTER N WITH ACUTE
    ('[N,]', '\u0145', '\\u0145'), # LATIN CAPITAL LETTER N WITH CEDILLA
    ('[n,]', '\u0146', '\\u0146'), # LATIN SMALL LETTER N WITH CEDILLA
    ('[vN]', '\u0147', '\\u0147'), # LATIN CAPITAL LETTER N WITH CARON
    ('[vn]', '\u0148', '\\u0148'), # LATIN SMALL LETTER N WITH CARON
    #('[\'n]', '\u0149', '\\u0149'), # LATIN SMALL LETTER N PRECEDED BY APOSTROPHE (conflicts with markup for n with acute)
    ('[Eng]', '\u014A', '\\u014A'), # LATIN CAPITAL LETTER ENG
    ('[eng]', '\u014B', '\\u014B'), # LATIN SMALL LETTER ENG
    ('[=O]', '\u014C', '\\u014C'), # LATIN CAPITAL LETTER O WITH MACRON
    ('[=o]', '\u014D', '\\u014D'), # LATIN SMALL LETTER O WITH MACRON
    ('[)O]', '\u014E', '\\u014E'), # LATIN CAPITAL LETTER O WITH BREVE
    ('[)o]', '\u014F', '\\u014F'), # LATIN SMALL LETTER O WITH BREVE
    ('[\'\'O]', '\u0150', '\\u0150'), # LATIN CAPITAL LETTER O WITH DOUBLE ACUTE
    ('[\'\'o]', '\u0151', '\\u0151'), # LATIN SMALL LETTER O WITH DOUBLE ACUTE
    ('[OE]', '\u0152', '\\u0152'), # LATIN CAPITAL LIGATURE OE
    ('[oe]', '\u0153', '\\u0153'), # LATIN SMALL LIGATURE OE
    ('[\'R]', '\u0154', '\\u0154'), # LATIN CAPITAL LETTER R WITH ACUTE
    ('[\'r]', '\u0155', '\\u0155'), # LATIN SMALL LETTER R WITH ACUTE
    ('[R,]', '\u0156', '\\u0156'), # LATIN CAPITAL LETTER R WITH CEDILLA
    ('[r,]', '\u0157', '\\u0157'), # LATIN SMALL LETTER R WITH CEDILLA
    ('[vR]', '\u0158', '\\u0158'), # LATIN CAPITAL LETTER R WITH CARON
    ('[vr]', '\u0159', '\\u0159'), # LATIN SMALL LETTER R WITH CARON
    ('[\'S]', '\u015A', '\\u015A'), # LATIN CAPITAL LETTER S WITH ACUTE
    ('[\'s]', '\u015B', '\\u015B'), # LATIN SMALL LETTER S WITH ACUTE
    ('[^S]', '\u015C', '\\u015C'), # LATIN CAPITAL LETTER S WITH CIRCUMFLEX
    ('[^s]', '\u015D', '\\u015D'), # LATIN SMALL LETTER S WITH CIRCUMFLEX
    ('[S,]', '\u015E', '\\u015E'), # LATIN CAPITAL LETTER S WITH CEDILLA
    ('[s,]', '\u015F', '\\u015F'), # LATIN SMALL LETTER S WITH CEDILLA
    ('[vS]', '\u0160', '\\u0160'), # LATIN CAPITAL LETTER S WITH CARON
    ('[vs]', '\u0161', '\\u0161'), # LATIN SMALL LETTER S WITH CARON
    ('[T,]', '\u0162', '\\u0162'), # LATIN CAPITAL LETTER T WITH CEDILLA
    ('[t,]', '\u0163', '\\u0163'), # LATIN SMALL LETTER T WITH CEDILLA
    ('[vT]', '\u0164', '\\u0164'), # LATIN CAPITAL LETTER T WITH CARON
    ('[vt]', '\u0165', '\\u0165'), # LATIN SMALL LETTER T WITH CARON
    ('[-T]', '\u0166', '\\u0166'), # LATIN CAPITAL LETTER T WITH STROKE
    ('[-t]', '\u0167', '\\u0167'), # LATIN SMALL LETTER T WITH STROKE
    ('[~U]', '\u0168', '\\u0168'), # LATIN CAPITAL LETTER U WITH TILDE
    ('[~u]', '\u0169', '\\u0169'), # LATIN SMALL LETTER U WITH TILDE
    ('[=U]', '\u016A', '\\u016A'), # LATIN CAPITAL LETTER U WITH MACRON
    ('[=u]', '\u016B', '\\u016B'), # LATIN SMALL LETTER U WITH MACRON
    ('[)U]', '\u016C', '\\u016C'), # LATIN CAPITAL LETTER U WITH BREVE
    ('[)u]', '\u016D', '\\u016D'), # LATIN SMALL LETTER U WITH BREVE
    ('[°U]', '\u016E', '\\u016E'), # LATIN CAPITAL LETTER U WITH RING ABOVE
    ('[°u]', '\u016F', '\\u016F'), # LATIN SMALL LETTER U WITH RING ABOVE
    ('[\'\'U]', '\u0170', '\\u0170'), # LATIN CAPITAL LETTER U WITH DOUBLE ACUTE
    ('[\'\'u]', '\u0171', '\\u0171'), # LATIN SMALL LETTER U WITH DOUBLE ACUTE
    ('[U,]', '\u0172', '\\u0172'), # LATIN CAPITAL LETTER U WITH OGONEK
    ('[u,]', '\u0173', '\\u0173'), # LATIN SMALL LETTER U WITH OGONEK
    ('[^W]', '\u0174', '\\u0174'), # LATIN CAPITAL LETTER W WITH CIRCUMFLEX
    ('[^w]', '\u0175', '\\u0175'), # LATIN SMALL LETTER W WITH CIRCUMFLEX
    ('[^Y]', '\u0176', '\\u0176'), # LATIN CAPITAL LETTER Y WITH CIRCUMFLEX
    ('[^y]', '\u0177', '\\u0177'), # LATIN SMALL LETTER Y WITH CIRCUMFLEX
    ('[:Y]', '\u0178', '\\u0178'), # LATIN CAPITAL LETTER Y WITH DIAERESIS
    ('[\'Z]', '\u0179', '\\u0179'), # LATIN CAPITAL LETTER Z WITH ACUTE
    ('[\'z]', '\u017A', '\\u017A'), # LATIN SMALL LETTER Z WITH ACUTE
    ('[.Z]', '\u017B', '\\u017B'), # LATIN CAPITAL LETTER Z WITH DOT ABOVE
    ('[.z]', '\u017C', '\\u017C'), # LATIN SMALL LETTER Z WITH DOT ABOVE
    ('[vZ]', '\u017D', '\\u017D'), # LATIN CAPITAL LETTER Z WITH CARON
    ('[vz]', '\u017E', '\\u017E'), # LATIN SMALL LETTER Z WITH CARON
    ('[s]', '\u017F', '\\u017F'), # LATIN SMALL LETTER LONG S
    ('[-b]', '\u0180', '\\u0180'), # LATIN SMALL LETTER B WITH STROKE     (Latin Extended-B)
    #('[]', '\u0181', '\\u0181'), # LATIN CAPITAL LETTER B WITH HOOK
    #('[]', '\u0182', '\\u0182'), # LATIN CAPITAL LETTER B WITH TOPBAR
    #('[]', '\u0183', '\\u0183'), # LATIN SMALL LETTER B WITH TOPBAR
    #('[]', '\u0184', '\\u0184'), # LATIN CAPITAL LETTER TONE SIX
    #('[]', '\u0185', '\\u0185'), # LATIN SMALL LETTER TONE SIX
    #('[]', '\u0186', '\\u0186'), # LATIN CAPITAL LETTER OPEN O
    #('[]', '\u0187', '\\u0187'), # LATIN CAPITAL LETTER C WITH HOOK
    #('[]', '\u0188', '\\u0188'), # LATIN SMALL LETTER C WITH HOOK
    #('[]', '\u0189', '\\u0189'), # LATIN CAPITAL LETTER AFRICAN D
    #('[]', '\u018A', '\\u018A'), # LATIN CAPITAL LETTER D WITH HOOK
    #('[]', '\u018B', '\\u018B'), # LATIN CAPITAL LETTER D WITH TOPBAR
    #('[]', '\u018C', '\\u018C'), # LATIN SMALL LETTER D WITH TOPBAR
    #('[]', '\u018D', '\\u018D'), # LATIN SMALL LETTER TURNED DELTA
    #('[]', '\u018E', '\\u018E'), # LATIN CAPITAL LETTER REVERSED E
    ('[Schwa]', '\u018F', '\\u018F'), # LATIN CAPITAL LETTER SCHWA
    #('[]', '\u0190', '\\u0190'), # LATIN CAPITAL LETTER OPEN E
    #('[]', '\u0191', '\\u0191'), # LATIN CAPITAL LETTER F WITH HOOK
    #('[]', '\u0192', '\\u0192'), # LATIN SMALL LETTER F WITH HOOK
    #('[]', '\u0193', '\\u0193'), # LATIN CAPITAL LETTER G WITH HOOK
    #('[Gamma]', '\u0194', '\\u0194'), # LATIN CAPITAL LETTER GAMMA  (use Greek versions instead)
    #('[]', '\u0195', '\\u0195'), # LATIN SMALL LETTER HV
    #('[Iota]', '\u0196', '\\u0196'), # LATIN CAPITAL LETTER IOTA    (use Greek versions instead)
    ('[-I]', '\u0197', '\\u0197'), # LATIN CAPITAL LETTER I WITH STROKE
    #('[]', '\u0198', '\\u0198'), # LATIN CAPITAL LETTER K WITH HOOK
    #('[]', '\u0199', '\\u0199'), # LATIN SMALL LETTER K WITH HOOK
    ('[-l]', '\u019A', '\\u019A'), # LATIN SMALL LETTER L WITH BAR
    #('[]', '\u019B', '\\u019B'), # LATIN SMALL LETTER LAMBDA WITH STROKE
    #('[]', '\u019C', '\\u019C'), # LATIN CAPITAL LETTER TURNED M
    #('[]', '\u019D', '\\u019D'), # LATIN CAPITAL LETTER N WITH LEFT HOOK
    #('[]', '\u019E', '\\u019E'), # LATIN SMALL LETTER N WITH LONG RIGHT LEG
    #('[]', '\u019F', '\\u019F'), # LATIN CAPITAL LETTER O WITH MIDDLE TILDE
    #('[]', '\u01A0', '\\u01A0'), # LATIN CAPITAL LETTER O WITH HORN
    #('[]', '\u01A1', '\\u01A1'), # LATIN SMALL LETTER O WITH HORN
    ('[OI]', '\u01A2', '\\u01A2'), # LATIN CAPITAL LETTER OI
    ('[oi]', '\u01A3', '\\u01A3'), # LATIN SMALL LETTER OI
    #('[]', '\u01A4', '\\u01A4'), # LATIN CAPITAL LETTER P WITH HOOK
    #('[]', '\u01A5', '\\u01A5'), # LATIN SMALL LETTER P WITH HOOK
    #('[]', '\u01A6', '\\u01A6'), # LATIN LETTER YR
    #('[]', '\u01A7', '\\u01A7'), # LATIN CAPITAL LETTER TONE TWO
    #('[]', '\u01A8', '\\u01A8'), # LATIN SMALL LETTER TONE TWO
    ('[Esh]', '\u01A9', '\\u01A9'), # LATIN CAPITAL LETTER ESH
    #('[]', '\u01AA', '\\u01AA'), # LATIN LETTER REVERSED ESH LOOP
    #('[]', '\u01AB', '\\u01AB'), # LATIN SMALL LETTER T WITH PALATAL HOOK
    #('[]', '\u01AC', '\\u01AC'), # LATIN CAPITAL LETTER T WITH HOOK
    #('[]', '\u01AD', '\\u01AD'), # LATIN SMALL LETTER T WITH HOOK
    #('[]', '\u01AE', '\\u01AE'), # LATIN CAPITAL LETTER T WITH RETROFLEX HOOK
    #('[]', '\u01AF', '\\u01AF'), # LATIN CAPITAL LETTER U WITH HORN
    #('[]', '\u01B0', '\\u01B0'), # LATIN SMALL LETTER U WITH HORN
    #('[Upsilon]', '\u01B1', '\\u01B1'), # LATIN CAPITAL LETTER UPSILON    (use Greek versions instead)
    #('[]', '\u01B2', '\\u01B2'), # LATIN CAPITAL LETTER V WITH HOOK
    #('[]', '\u01B3', '\\u01B3'), # LATIN CAPITAL LETTER Y WITH HOOK
    #('[]', '\u01B4', '\\u01B4'), # LATIN SMALL LETTER Y WITH HOOK
    ('[-Z]', '\u01B5', '\\u01B5'), # LATIN CAPITAL LETTER Z WITH STROKE
    ('[-z]', '\u01B6', '\\u01B6'), # LATIN SMALL LETTER Z WITH STROKE
    ('[Zh]', '\u01B7', '\\u01B7'), # LATIN CAPITAL LETTER EZH
    ('[zh]', '\u0292', '\\u0292'), # LATIN SMALL LETTER EZH (out of order just to keep it with the capital)
    #('[]', '\u01B8', '\\u01B8'), # LATIN CAPITAL LETTER EZH REVERSED
    #('[]', '\u01B9', '\\u01B9'), # LATIN SMALL LETTER EZH REVERSED
    #('[]', '\u01BA', '\\u01BA'), # LATIN SMALL LETTER EZH WITH TAIL
    ('[-2]', '\u01BB', '\\u01BB'), # LATIN LETTER TWO WITH STROKE
    #('[]', '\u01BC', '\\u01BC'), # LATIN CAPITAL LETTER TONE FIVE
    #('[]', '\u01BD', '\\u01BD'), # LATIN SMALL LETTER TONE FIVE
    #('[]', '\u01BE', '\\u01BE'), # LATIN LETTER INVERTED GLOTTAL STOP WITH STROKE
    ('[wynn]', '\u01BF', '\\u01BF'), # LATIN LETTER WYNN
    #('[]', '\u01C0', '\\u01C0'), # LATIN LETTER DENTAL CLICK
    #('[]', '\u01C1', '\\u01C1'), # LATIN LETTER LATERAL CLICK
    #('[]', '\u01C2', '\\u01C2'), # LATIN LETTER ALVEOLAR CLICK
    #('[]', '\u01C3', '\\u01C3'), # LATIN LETTER RETROFLEX CLICK
    ('[vDZ]', '\u01C4', '\\u01C4'), # LATIN CAPITAL LETTER DZ WITH CARON
    ('[vDz]', '\u01C5', '\\u01C5'), # LATIN CAPITAL LETTER D WITH SMALL LETTER Z WITH CARON
    ('[vdz]', '\u01C6', '\\u01C6'), # LATIN SMALL LETTER DZ WITH CARON
    ('[LJ]', '\u01C7', '\\u01C7'), # LATIN CAPITAL LETTER LJ
    ('[Lj]', '\u01C8', '\\u01C8'), # LATIN CAPITAL LETTER L WITH SMALL LETTER J
    ('[lj]', '\u01C9', '\\u01C9'), # LATIN SMALL LETTER LJ
    ('[NJ]', '\u01CA', '\\u01CA'), # LATIN CAPITAL LETTER NJ
    ('[Nj]', '\u01CB', '\\u01CB'), # LATIN CAPITAL LETTER N WITH SMALL LETTER J
    ('[nj]', '\u01CC', '\\u01CC'), # LATIN SMALL LETTER NJ
    ('[vA]', '\u01CD', '\\u01CD'), # LATIN CAPITAL LETTER A WITH CARON
    ('[va]', '\u01CE', '\\u01CE'), # LATIN SMALL LETTER A WITH CARON
    ('[vI]', '\u01CF', '\\u01CF'), # LATIN CAPITAL LETTER I WITH CARON
    ('[vi]', '\u01D0', '\\u01D0'), # LATIN SMALL LETTER I WITH CARON
    ('[vO]', '\u01D1', '\\u01D1'), # LATIN CAPITAL LETTER O WITH CARON
    ('[vo]', '\u01D2', '\\u01D2'), # LATIN SMALL LETTER O WITH CARON
    ('[vU]', '\u01D3', '\\u01D3'), # LATIN CAPITAL LETTER U WITH CARON
    ('[vu]', '\u01D4', '\\u01D4'), # LATIN SMALL LETTER U WITH CARON
    ('[=Ü]', '\u01D5', '\\u01D5'), # LATIN CAPITAL LETTER U WITH DIAERESIS AND MACRON
    ('[=ü]', '\u01D6', '\\u01D6'), # LATIN SMALL LETTER U WITH DIAERESIS AND MACRON
    ('[\'Ü]', '\u01D7', '\\u01D7'), # LATIN CAPITAL LETTER U WITH DIAERESIS AND ACUTE
    ('[\'ü]', '\u01D8', '\\u01D8'), # LATIN SMALL LETTER U WITH DIAERESIS AND ACUTE
    ('[)Ü]', '\u01D9', '\\u01D9'), # LATIN CAPITAL LETTER U WITH DIAERESIS AND CARON
    ('[)ü]', '\u01DA', '\\u01DA'), # LATIN SMALL LETTER U WITH DIAERESIS AND CARON
    ('[`Ü]', '\u01DB', '\\u01DB'), # LATIN CAPITAL LETTER U WITH DIAERESIS AND GRAVE
    ('[`ü]', '\u01DC', '\\u01DC'), # LATIN SMALL LETTER U WITH DIAERESIS AND GRAVE
    #('[]', '\u01DD', '\\u01DD'), # LATIN SMALL LETTER TURNED E
    ('[=Ä]', '\u01DE', '\\u01DE'), # LATIN CAPITAL LETTER A WITH DIAERESIS AND MACRON
    ('[=ä]', '\u01DF', '\\u01DF'), # LATIN SMALL LETTER A WITH DIAERESIS AND MACRON
    ('[=.A]', '\u01E0', '\\u01E0'), # LATIN CAPITAL LETTER A WITH DOT ABOVE AND MACRON
    ('[=.a]', '\u01E1', '\\u01E1'), # LATIN SMALL LETTER A WITH DOT ABOVE AND MACRON
    ('[=AE]', '\u01E2', '\\u01E2'), # LATIN CAPITAL LETTER AE WITH MACRON
    ('[=ae]', '\u01E3', '\\u01E3'), # LATIN SMALL LETTER AE WITH MACRON
    ('[-G]', '\u01E4', '\\u01E4'), # LATIN CAPITAL LETTER G WITH STROKE
    ('[-g]', '\u01E5', '\\u01E5'), # LATIN SMALL LETTER G WITH STROKE
    ('[vG]', '\u01E6', '\\u01E6'), # LATIN CAPITAL LETTER G WITH CARON
    ('[vg]', '\u01E7', '\\u01E7'), # LATIN SMALL LETTER G WITH CARON
    ('[vK]', '\u01E8', '\\u01E8'), # LATIN CAPITAL LETTER K WITH CARON
    ('[vk]', '\u01E9', '\\u01E9'), # LATIN SMALL LETTER K WITH CARON
    ('[O,]', '\u01EA', '\\u01EA'), # LATIN CAPITAL LETTER O WITH OGONEK
    ('[o,]', '\u01EB', '\\u01EB'), # LATIN SMALL LETTER O WITH OGONEK
    ('[=O,]', '\u01EC', '\\u01EC'), # LATIN CAPITAL LETTER O WITH OGONEK AND MACRON
    ('[=o,]', '\u01ED', '\\u01ED'), # LATIN SMALL LETTER O WITH OGONEK AND MACRON
    ('[vZh]', '\u01EE', '\\u01EE'), # LATIN CAPITAL LETTER EZH WITH CARON
    ('[vzh]', '\u01EF', '\\u01EF'), # LATIN SMALL LETTER EZH WITH CARON
    ('[vj]', '\u01F0', '\\u01F0'), # LATIN SMALL LETTER J WITH CARON
    ('[DZ]', '\u01F1', '\\u01F1'), # LATIN CAPITAL LETTER DZ
    ('[Dz]', '\u01F2', '\\u01F2'), # LATIN CAPITAL LETTER D WITH SMALL LETTER Z
    ('[dz]', '\u01F3', '\\u01F3'), # LATIN SMALL LETTER DZ
    ('[\'G]', '\u01F4', '\\u01F4'), # LATIN CAPITAL LETTER G WITH ACUTE
    ('[\'g]', '\u01F5', '\\u01F5'), # LATIN SMALL LETTER G WITH ACUTE
    ('[Hwair]', '\u01F6', '\\u01F6'), # LATIN CAPITAL LETTER HWAIR
    ('[Wynn]', '\u01F7', '\\u01F7'), # LATIN CAPITAL LETTER WYNN
    ('[`N]', '\u01F8', '\\u01F8'), # LATIN CAPITAL LETTER N WITH GRAVE
    ('[`n]', '\u01F9', '\\u01F9'), # LATIN SMALL LETTER N WITH GRAVE
    ('[\'Å]', '\u01FA', '\\u01FA'), # LATIN CAPITAL LETTER A WITH RING ABOVE AND ACUTE
    ('[\'å]', '\u01FB', '\\u01FB'), # LATIN SMALL LETTER A WITH RING ABOVE AND ACUTE
    ('[\'AE]', '\u01FC', '\\u01FC'), # LATIN CAPITAL LETTER AE WITH ACUTE
    ('[\'ae]', '\u01FD', '\\u01FD'), # LATIN SMALL LETTER AE WITH ACUTE
    ('[\'Ø]', '\u01FE', '\\u01FE'), # LATIN CAPITAL LETTER O WITH STROKE AND ACUTE
    ('[\'ø]', '\u01FF', '\\u01FF'), # LATIN SMALL LETTER O WITH STROKE AND ACUTE
    ('[``A]', '\u0200', '\\u0200'), # LATIN CAPITAL LETTER A WITH DOUBLE GRAVE
    ('[``a]', '\u0201', '\\u0201'), # LATIN SMALL LETTER A WITH DOUBLE GRAVE
    #('[]', '\u0202', '\\u0202'), # LATIN CAPITAL LETTER A WITH INVERTED BREVE
    #('[]', '\u0203', '\\u0203'), # LATIN SMALL LETTER A WITH INVERTED BREVE
    ('[``E]', '\u0204', '\\u0204'), # LATIN CAPITAL LETTER E WITH DOUBLE GRAVE
    ('[``e]', '\u0205', '\\u0205'), # LATIN SMALL LETTER E WITH DOUBLE GRAVE
    #('[]', '\u0206', '\\u0206'), # LATIN CAPITAL LETTER E WITH INVERTED BREVE
    #('[]', '\u0207', '\\u0207'), # LATIN SMALL LETTER E WITH INVERTED BREVE
    ('[``I]', '\u0208', '\\u0208'), # LATIN CAPITAL LETTER I WITH DOUBLE GRAVE
    ('[``i]', '\u0209', '\\u0209'), # LATIN SMALL LETTER I WITH DOUBLE GRAVE
    #('[]', '\u020A', '\\u020A'), # LATIN CAPITAL LETTER I WITH INVERTED BREVE
    #('[]', '\u020B', '\\u020B'), # LATIN SMALL LETTER I WITH INVERTED BREVE
    ('[``O]', '\u020C', '\\u020C'), # LATIN CAPITAL LETTER O WITH DOUBLE GRAVE
    ('[``o]', '\u020D', '\\u020D'), # LATIN SMALL LETTER O WITH DOUBLE GRAVE
    #('[]', '\u020E', '\\u020E'), # LATIN CAPITAL LETTER O WITH INVERTED BREVE
    #('[]', '\u020F', '\\u020F'), # LATIN SMALL LETTER O WITH INVERTED BREVE
    ('[``R]', '\u0210', '\\u0210'), # LATIN CAPITAL LETTER R WITH DOUBLE GRAVE
    ('[``r]', '\u0211', '\\u0211'), # LATIN SMALL LETTER R WITH DOUBLE GRAVE
    #('[]', '\u0212', '\\u0212'), # LATIN CAPITAL LETTER R WITH INVERTED BREVE
    #('[]', '\u0213', '\\u0213'), # LATIN SMALL LETTER R WITH INVERTED BREVE
    ('[``U]', '\u0214', '\\u0214'), # LATIN CAPITAL LETTER U WITH DOUBLE GRAVE
    ('[``u]', '\u0215', '\\u0215'), # LATIN SMALL LETTER U WITH DOUBLE GRAVE
    #('[]', '\u0216', '\\u0216'), # LATIN CAPITAL LETTER U WITH INVERTED BREVE
    #('[]', '\u0217', '\\u0217'), # LATIN SMALL LETTER U WITH INVERTED BREVE
    #('[S,]', '\u0218', '\\u0218'), # LATIN CAPITAL LETTER S WITH COMMA BELOW  # conflicts with cedilla markup
    #('[s,]', '\u0219', '\\u0219'), # LATIN SMALL LETTER S WITH COMMA BELOW    # conflicts with cedilla markup
    #('[T,]', '\u021A', '\\u021A'), # LATIN CAPITAL LETTER T WITH COMMA BELOW  # conflicts with cedilla markup
    #('[t,]', '\u021B', '\\u021B'), # LATIN SMALL LETTER T WITH COMMA BELOW    # conflicts with cedilla markup
    ('[Gh]', '\u021C', '\\u021C'), # LATIN CAPITAL LETTER YOGH
    ('[gh]', '\u021D', '\\u021D'), # LATIN SMALL LETTER YOGH
    ('[vH]', '\u021E', '\\u021E'), # LATIN CAPITAL LETTER H WITH CARON
    ('[vh]', '\u021F', '\\u021F'), # LATIN SMALL LETTER H WITH CARON
    #('[]', '\u0220', '\\u0220'), # LATIN CAPITAL LETTER N WITH LONG RIGHT LEG
    #('[]', '\u0221', '\\u0221'), # LATIN SMALL LETTER D WITH CURL
    ('[OU]', '\u0222', '\\u0222'), # LATIN CAPITAL LETTER OU
    ('[ou]', '\u0223', '\\u0223'), # LATIN SMALL LETTER OU
    #('[]', '\u0224', '\\u0224'), # LATIN CAPITAL LETTER Z WITH HOOK
    #('[]', '\u0225', '\\u0225'), # LATIN SMALL LETTER Z WITH HOOK
    ('[.A]', '\u0226', '\\u0226'), # LATIN CAPITAL LETTER A WITH DOT ABOVE
    ('[.a]', '\u0227', '\\u0227'), # LATIN SMALL LETTER A WITH DOT ABOVE
    ('[E,]', '\u0228', '\\u0228'), # LATIN CAPITAL LETTER E WITH CEDILLA
    ('[e,]', '\u0229', '\\u0229'), # LATIN SMALL LETTER E WITH CEDILLA
    ('[=Ö]', '\u022A', '\\u022A'), # LATIN CAPITAL LETTER O WITH DIAERESIS AND MACRON
    ('[=ö]', '\u022B', '\\u022B'), # LATIN SMALL LETTER O WITH DIAERESIS AND MACRON
    ('[=Õ]', '\u022C', '\\u022C'), # LATIN CAPITAL LETTER O WITH TILDE AND MACRON
    ('[=õ]', '\u022D', '\\u022D'), # LATIN SMALL LETTER O WITH TILDE AND MACRON
    ('[.O]', '\u022E', '\\u022E'), # LATIN CAPITAL LETTER O WITH DOT ABOVE
    ('[.o]', '\u022F', '\\u022F'), # LATIN SMALL LETTER O WITH DOT ABOVE
    ('[=.O]', '\u0230', '\\u0230'), # LATIN CAPITAL LETTER O WITH DOT ABOVE AND MACRON
    ('[=.o]', '\u0231', '\\u0231'), # LATIN SMALL LETTER O WITH DOT ABOVE AND MACRON
    ('[=Y]', '\u0232', '\\u0232'), # LATIN CAPITAL LETTER Y WITH MACRON
    ('[=y]', '\u0233', '\\u0233'), # LATIN SMALL LETTER Y WITH MACRON
    #('[]', '\u0234', '\\u0234'), # LATIN SMALL LETTER L WITH CURL
    #('[]', '\u0235', '\\u0235'), # LATIN SMALL LETTER N WITH CURL
    #('[]', '\u0236', '\\u0236'), # LATIN SMALL LETTER T WITH CURL
    #('[]', '\u0237', '\\u0237'), # LATIN SMALL LETTER DOTLESS J
    ('[db]', '\u0238', '\\u0238'), # LATIN SMALL LETTER DB DIGRAPH
    ('[qp]', '\u0239', '\\u0239'), # LATIN SMALL LETTER QP DIGRAPH
    ('[/A]', '\u023A', '\\u023A'), # LATIN CAPITAL LETTER A WITH STROKE
    ('[/C]', '\u023B', '\\u023B'), # LATIN CAPITAL LETTER C WITH STROKE
    ('[/c]', '\u023C', '\\u023C'), # LATIN SMALL LETTER C WITH STROKE
    ('[-L]', '\u023D', '\\u023D'), # LATIN CAPITAL LETTER L WITH BAR
    ('[/T]', '\u023E', '\\u023E'), # LATIN CAPITAL LETTER T WITH DIAGONAL STROKE
    #('[]', '\u023F', '\\u023F'), # LATIN SMALL LETTER S WITH SWASH TAIL
    #('[]', '\u0240', '\\u0240'), # LATIN SMALL LETTER Z WITH SWASH TAIL
    #('[]', '\u0241', '\\u0241'), # LATIN CAPITAL LETTER GLOTTAL STOP
    #('[]', '\u0242', '\\u0242'), # LATIN SMALL LETTER GLOTTAL STOP
    ('[-B]', '\u0243', '\\u0243'), # LATIN CAPITAL LETTER B WITH STROKE
    ('[-U]', '\u0244', '\\u0244'), # LATIN CAPITAL LETTER U BAR
    #('[]', '\u0245', '\\u0245'), # LATIN CAPITAL LETTER TURNED V
    ('[/E]', '\u0246', '\\u0246'), # LATIN CAPITAL LETTER E WITH STROKE
    ('[/e]', '\u0247', '\\u0247'), # LATIN SMALL LETTER E WITH STROKE
    ('[-J]', '\u0248', '\\u0248'), # LATIN CAPITAL LETTER J WITH STROKE
    ('[-j]', '\u0249', '\\u0249'), # LATIN SMALL LETTER J WITH STROKE
    #('[]', '\u024A', '\\u024A'), # LATIN CAPITAL LETTER SMALL Q WITH HOOK TAIL
    #('[]', '\u024B', '\\u024B'), # LATIN SMALL LETTER Q WITH HOOK TAIL
    ('[-R]', '\u024C', '\\u024C'), # LATIN CAPITAL LETTER R WITH STROKE
    ('[-r]', '\u024D', '\\u024D'), # LATIN SMALL LETTER R WITH STROKE
    ('[-Y]', '\u024E', '\\u024E'), # LATIN CAPITAL LETTER Y WITH STROKE
    ('[-y]', '\u024F', '\\u024F'), # LATIN SMALL LETTER Y WITH STROKE
    ('[A°]', '\u1E00', '\\u1E00'), # LATIN CAPITAL LETTER A WITH RING BELOW    (Latin Extended Additional)
    ('[a°]', '\u1E01', '\\u1E01'), # LATIN SMALL LETTER A WITH RING BELOW
    ('[.B]', '\u1E02', '\\u1E02'), # LATIN CAPITAL LETTER B WITH DOT ABOVE
    ('[.b]', '\u1E03', '\\u1E03'), # LATIN SMALL LETTER B WITH DOT ABOVE
    ('[B.]', '\u1E04', '\\u1E04'), # LATIN CAPITAL LETTER B WITH DOT BELOW
    ('[b.]', '\u1E05', '\\u1E05'), # LATIN SMALL LETTER B WITH DOT BELOW
    ('[B=]', '\u1E06', '\\u1E06'), # LATIN CAPITAL LETTER B WITH LINE BELOW
    ('[b=]', '\u1E07', '\\u1E07'), # LATIN SMALL LETTER B WITH LINE BELOW
    ('[\'C,]', '\u1E08', '\\u1E08'), # LATIN CAPITAL LETTER C WITH CEDILLA AND ACUTE
    ('[\'c,]', '\u1E09', '\\u1E09'), # LATIN SMALL LETTER C WITH CEDILLA AND ACUTE
    ('[.D]', '\u1E0A', '\\u1E0A'), # LATIN CAPITAL LETTER D WITH DOT ABOVE
    ('[.d]', '\u1E0B', '\\u1E0B'), # LATIN SMALL LETTER D WITH DOT ABOVE
    ('[D.]', '\u1E0C', '\\u1E0C'), # LATIN CAPITAL LETTER D WITH DOT BELOW
    ('[d.]', '\u1E0D', '\\u1E0D'), # LATIN SMALL LETTER D WITH DOT BELOW
    ('[D=]', '\u1E0E', '\\u1E0E'), # LATIN CAPITAL LETTER D WITH LINE BELOW
    ('[d=]', '\u1E0F', '\\u1E0F'), # LATIN SMALL LETTER D WITH LINE BELOW
    ('[D,]', '\u1E10', '\\u1E10'), # LATIN CAPITAL LETTER D WITH CEDILLA
    ('[d,]', '\u1E11', '\\u1E11'), # LATIN SMALL LETTER D WITH CEDILLA
    ('[D^]', '\u1E12', '\\u1E12'), # LATIN CAPITAL LETTER D WITH CIRCUMFLEX BELOW
    ('[d^]', '\u1E13', '\\u1E13'), # LATIN SMALL LETTER D WITH CIRCUMFLEX BELOW
    ('[`=E]', '\u1E14', '\\u1E14'), # LATIN CAPITAL LETTER E WITH MACRON AND GRAVE
    ('[`=e]', '\u1E15', '\\u1E15'), # LATIN SMALL LETTER E WITH MACRON AND GRAVE
    ('[=É]', '\u1E16', '\\u1E16'), # LATIN CAPITAL LETTER E WITH MACRON AND ACUTE
    ('[=é]', '\u1E17', '\\u1E17'), # LATIN SMALL LETTER E WITH MACRON AND ACUTE
    ('[E^]', '\u1E18', '\\u1E18'), # LATIN CAPITAL LETTER E WITH CIRCUMFLEX BELOW
    ('[e^]', '\u1E19', '\\u1E19'), # LATIN SMALL LETTER E WITH CIRCUMFLEX BELOW
    ('[E~]', '\u1E1A', '\\u1E1A'), # LATIN CAPITAL LETTER E WITH TILDE BELOW
    ('[e~]', '\u1E1B', '\\u1E1B'), # LATIN SMALL LETTER E WITH TILDE BELOW
    ('[)E,]', '\u1E1C', '\\u1E1C'), # LATIN CAPITAL LETTER E WITH CEDILLA AND BREVE
    ('[)e,]', '\u1E1D', '\\u1E1D'), # LATIN SMALL LETTER E WITH CEDILLA AND BREVE
    ('[.F]', '\u1E1E', '\\u1E1E'), # LATIN CAPITAL LETTER F WITH DOT ABOVE
    ('[.f]', '\u1E1F', '\\u1E1F'), # LATIN SMALL LETTER F WITH DOT ABOVE
    ('[=G]', '\u1E20', '\\u1E20'), # LATIN CAPITAL LETTER G WITH MACRON
    ('[=g]', '\u1E21', '\\u1E21'), # LATIN SMALL LETTER G WITH MACRON
    ('[.H]', '\u1E22', '\\u1E22'), # LATIN CAPITAL LETTER H WITH DOT ABOVE
    ('[.h]', '\u1E23', '\\u1E23'), # LATIN SMALL LETTER H WITH DOT ABOVE
    ('[H.]', '\u1E24', '\\u1E24'), # LATIN CAPITAL LETTER H WITH DOT BELOW
    ('[h.]', '\u1E25', '\\u1E25'), # LATIN SMALL LETTER H WITH DOT BELOW
    ('[:H]', '\u1E26', '\\u1E26'), # LATIN CAPITAL LETTER H WITH DIAERESIS
    ('[:h]', '\u1E27', '\\u1E27'), # LATIN SMALL LETTER H WITH DIAERESIS
    ('[H,]', '\u1E28', '\\u1E28'), # LATIN CAPITAL LETTER H WITH CEDILLA
    ('[h,]', '\u1E29', '\\u1E29'), # LATIN SMALL LETTER H WITH CEDILLA
    ('[H)]', '\u1E2A', '\\u1E2A'), # LATIN CAPITAL LETTER H WITH BREVE BELOW
    ('[h)]', '\u1E2B', '\\u1E2B'), # LATIN SMALL LETTER H WITH BREVE BELOW
    ('[I~]', '\u1E2C', '\\u1E2C'), # LATIN CAPITAL LETTER I WITH TILDE BELOW
    ('[i~]', '\u1E2D', '\\u1E2D'), # LATIN SMALL LETTER I WITH TILDE BELOW
    ('[\'Ï]', '\u1E2E', '\\u1E2E'), # LATIN CAPITAL LETTER I WITH DIAERESIS AND ACUTE
    ('[\'ï]', '\u1E2F', '\\u1E2F'), # LATIN SMALL LETTER I WITH DIAERESIS AND ACUTE
    ('[\'K]', '\u1E30', '\\u1E30'), # LATIN CAPITAL LETTER K WITH ACUTE
    ('[\'k]', '\u1E31', '\\u1E31'), # LATIN SMALL LETTER K WITH ACUTE
    ('[K.]', '\u1E32', '\\u1E32'), # LATIN CAPITAL LETTER K WITH DOT BELOW
    ('[k.]', '\u1E33', '\\u1E33'), # LATIN SMALL LETTER K WITH DOT BELOW
    ('[K=]', '\u1E34', '\\u1E34'), # LATIN CAPITAL LETTER K WITH LINE BELOW
    ('[k=]', '\u1E35', '\\u1E35'), # LATIN SMALL LETTER K WITH LINE BELOW
    ('[L.]', '\u1E36', '\\u1E36'), # LATIN CAPITAL LETTER L WITH DOT BELOW
    ('[l.]', '\u1E37', '\\u1E37'), # LATIN SMALL LETTER L WITH DOT BELOW
    ('[=L.]', '\u1E38', '\\u1E38'), # LATIN CAPITAL LETTER L WITH DOT BELOW AND MACRON
    ('[=l.]', '\u1E39', '\\u1E39'), # LATIN SMALL LETTER L WITH DOT BELOW AND MACRON
    ('[L=]', '\u1E3A', '\\u1E3A'), # LATIN CAPITAL LETTER L WITH LINE BELOW
    ('[l=]', '\u1E3B', '\\u1E3B'), # LATIN SMALL LETTER L WITH LINE BELOW
    ('[L^]', '\u1E3C', '\\u1E3C'), # LATIN CAPITAL LETTER L WITH CIRCUMFLEX BELOW
    ('[l^]', '\u1E3D', '\\u1E3D'), # LATIN SMALL LETTER L WITH CIRCUMFLEX BELOW
    ('[\'M]', '\u1E3E', '\\u1E3E'), # LATIN CAPITAL LETTER M WITH ACUTE
    ('[\'m]', '\u1E3F', '\\u1E3F'), # LATIN SMALL LETTER M WITH ACUTE
    ('[.M]', '\u1E40', '\\u1E40'), # LATIN CAPITAL LETTER M WITH DOT ABOVE
    ('[.m]', '\u1E41', '\\u1E41'), # LATIN SMALL LETTER M WITH DOT ABOVE
    ('[M.]', '\u1E42', '\\u1E42'), # LATIN CAPITAL LETTER M WITH DOT BELOW
    ('[m.]', '\u1E43', '\\u1E43'), # LATIN SMALL LETTER M WITH DOT BELOW
    ('[.N]', '\u1E44', '\\u1E44'), # LATIN CAPITAL LETTER N WITH DOT ABOVE
    ('[.n]', '\u1E45', '\\u1E45'), # LATIN SMALL LETTER N WITH DOT ABOVE
    ('[N.]', '\u1E46', '\\u1E46'), # LATIN CAPITAL LETTER N WITH DOT BELOW
    ('[n.]', '\u1E47', '\\u1E47'), # LATIN SMALL LETTER N WITH DOT BELOW
    ('[N=]', '\u1E48', '\\u1E48'), # LATIN CAPITAL LETTER N WITH LINE BELOW
    ('[n=]', '\u1E49', '\\u1E49'), # LATIN SMALL LETTER N WITH LINE BELOW
    ('[N^]', '\u1E4A', '\\u1E4A'), # LATIN CAPITAL LETTER N WITH CIRCUMFLEX BELOW
    ('[n^]', '\u1E4B', '\\u1E4B'), # LATIN SMALL LETTER N WITH CIRCUMFLEX BELOW
    ('[\'Õ]', '\u1E4C', '\\u1E4C'), # LATIN CAPITAL LETTER O WITH TILDE AND ACUTE
    ('[\'õ]', '\u1E4D', '\\u1E4D'), # LATIN SMALL LETTER O WITH TILDE AND ACUTE
    ('[:Õ]', '\u1E4E', '\\u1E4E'), # LATIN CAPITAL LETTER O WITH TILDE AND DIAERESIS
    ('[:õ]', '\u1E4F', '\\u1E4F'), # LATIN SMALL LETTER O WITH TILDE AND DIAERESIS
    ('[`=O]', '\u1E50', '\\u1E50'), # LATIN CAPITAL LETTER O WITH MACRON AND GRAVE
    ('[`=o]', '\u1E51', '\\u1E51'), # LATIN SMALL LETTER O WITH MACRON AND GRAVE
    ('[\'=O]', '\u1E52', '\\u1E52'), # LATIN CAPITAL LETTER O WITH MACRON AND ACUTE
    ('[\'=o]', '\u1E53', '\\u1E53'), # LATIN SMALL LETTER O WITH MACRON AND ACUTE
    ('[\'P]', '\u1E54', '\\u1E54'), # LATIN CAPITAL LETTER P WITH ACUTE
    ('[\'p]', '\u1E55', '\\u1E55'), # LATIN SMALL LETTER P WITH ACUTE
    ('[.P]', '\u1E56', '\\u1E56'), # LATIN CAPITAL LETTER P WITH DOT ABOVE
    ('[.p]', '\u1E57', '\\u1E57'), # LATIN SMALL LETTER P WITH DOT ABOVE
    ('[.R]', '\u1E58', '\\u1E58'), # LATIN CAPITAL LETTER R WITH DOT ABOVE
    ('[.r]', '\u1E59', '\\u1E59'), # LATIN SMALL LETTER R WITH DOT ABOVE
    ('[R.]', '\u1E5A', '\\u1E5A'), # LATIN CAPITAL LETTER R WITH DOT BELOW
    ('[r.]', '\u1E5B', '\\u1E5B'), # LATIN SMALL LETTER R WITH DOT BELOW
    ('[=R.]', '\u1E5C', '\\u1E5C'), # LATIN CAPITAL LETTER R WITH DOT BELOW AND MACRON
    ('[=r.]', '\u1E5D', '\\u1E5D'), # LATIN SMALL LETTER R WITH DOT BELOW AND MACRON
    ('[R=]', '\u1E5E', '\\u1E5E'), # LATIN CAPITAL LETTER R WITH LINE BELOW
    ('[r=]', '\u1E5F', '\\u1E5F'), # LATIN SMALL LETTER R WITH LINE BELOW
    ('[.S]', '\u1E60', '\\u1E60'), # LATIN CAPITAL LETTER S WITH DOT ABOVE
    ('[.s]', '\u1E61', '\\u1E61'), # LATIN SMALL LETTER S WITH DOT ABOVE
    ('[S.]', '\u1E62', '\\u1E62'), # LATIN CAPITAL LETTER S WITH DOT BELOW
    ('[s.]', '\u1E63', '\\u1E63'), # LATIN SMALL LETTER S WITH DOT BELOW
    ('[\'.S]', '\u1E64', '\\u1E64'), # LATIN CAPITAL LETTER S WITH ACUTE AND DOT ABOVE
    ('[\'.s]', '\u1E65', '\\u1E65'), # LATIN SMALL LETTER S WITH ACUTE AND DOT ABOVE
    ('[.vS]', '\u1E66', '\\u1E66'), # LATIN CAPITAL LETTER S WITH CARON AND DOT ABOVE
    ('[.vs]', '\u1E67', '\\u1E67'), # LATIN SMALL LETTER S WITH CARON AND DOT ABOVE
    ('[.S.]', '\u1E68', '\\u1E68'), # LATIN CAPITAL LETTER S WITH DOT BELOW AND DOT ABOVE
    ('[.s.]', '\u1E69', '\\u1E69'), # LATIN SMALL LETTER S WITH DOT BELOW AND DOT ABOVE
    ('[.T]', '\u1E6A', '\\u1E6A'), # LATIN CAPITAL LETTER T WITH DOT ABOVE
    ('[.t]', '\u1E6B', '\\u1E6B'), # LATIN SMALL LETTER T WITH DOT ABOVE
    ('[T.]', '\u1E6C', '\\u1E6C'), # LATIN CAPITAL LETTER T WITH DOT BELOW
    ('[t.]', '\u1E6D', '\\u1E6D'), # LATIN SMALL LETTER T WITH DOT BELOW
    ('[T=]', '\u1E6E', '\\u1E6E'), # LATIN CAPITAL LETTER T WITH LINE BELOW
    ('[t=]', '\u1E6F', '\\u1E6F'), # LATIN SMALL LETTER T WITH LINE BELOW
    ('[T^]', '\u1E70', '\\u1E70'), # LATIN CAPITAL LETTER T WITH CIRCUMFLEX BELOW
    ('[t^]', '\u1E71', '\\u1E71'), # LATIN SMALL LETTER T WITH CIRCUMFLEX BELOW
    ('[U:]', '\u1E72', '\\u1E72'), # LATIN CAPITAL LETTER U WITH DIAERESIS BELOW
    ('[u:]', '\u1E73', '\\u1E73'), # LATIN SMALL LETTER U WITH DIAERESIS BELOW
    ('[U~]', '\u1E74', '\\u1E74'), # LATIN CAPITAL LETTER U WITH TILDE BELOW
    ('[u~]', '\u1E75', '\\u1E75'), # LATIN SMALL LETTER U WITH TILDE BELOW
    ('[U^]', '\u1E76', '\\u1E76'), # LATIN CAPITAL LETTER U WITH CIRCUMFLEX BELOW
    ('[u^]', '\u1E77', '\\u1E77'), # LATIN SMALL LETTER U WITH CIRCUMFLEX BELOW
    ('[\'~U]', '\u1E78', '\\u1E78'), # LATIN CAPITAL LETTER U WITH TILDE AND ACUTE
    ('[\'~u]', '\u1E79', '\\u1E79'), # LATIN SMALL LETTER U WITH TILDE AND ACUTE
    ('[:=U]', '\u1E7A', '\\u1E7A'), # LATIN CAPITAL LETTER U WITH MACRON AND DIAERESIS
    ('[:=u]', '\u1E7B', '\\u1E7B'), # LATIN SMALL LETTER U WITH MACRON AND DIAERESIS
    ('[~V]', '\u1E7C', '\\u1E7C'), # LATIN CAPITAL LETTER V WITH TILDE
    ('[~v]', '\u1E7D', '\\u1E7D'), # LATIN SMALL LETTER V WITH TILDE
    ('[V.]', '\u1E7E', '\\u1E7E'), # LATIN CAPITAL LETTER V WITH DOT BELOW
    ('[v.]', '\u1E7F', '\\u1E7F'), # LATIN SMALL LETTER V WITH DOT BELOW
    ('[`W]', '\u1E80', '\\u1E80'), # LATIN CAPITAL LETTER W WITH GRAVE
    ('[`w]', '\u1E81', '\\u1E81'), # LATIN SMALL LETTER W WITH GRAVE
    ('[\'W]', '\u1E82', '\\u1E82'), # LATIN CAPITAL LETTER W WITH ACUTE
    ('[\'w]', '\u1E83', '\\u1E83'), # LATIN SMALL LETTER W WITH ACUTE
    ('[:W]', '\u1E84', '\\u1E84'), # LATIN CAPITAL LETTER W WITH DIAERESIS
    ('[:w]', '\u1E85', '\\u1E85'), # LATIN SMALL LETTER W WITH DIAERESIS
    ('[.W]', '\u1E86', '\\u1E86'), # LATIN CAPITAL LETTER W WITH DOT ABOVE
    ('[.w]', '\u1E87', '\\u1E87'), # LATIN SMALL LETTER W WITH DOT ABOVE
    ('[W.]', '\u1E88', '\\u1E88'), # LATIN CAPITAL LETTER W WITH DOT BELOW
    ('[w.]', '\u1E89', '\\u1E89'), # LATIN SMALL LETTER W WITH DOT BELOW
    ('[.X]', '\u1E8A', '\\u1E8A'), # LATIN CAPITAL LETTER X WITH DOT ABOVE
    ('[.x]', '\u1E8B', '\\u1E8B'), # LATIN SMALL LETTER X WITH DOT ABOVE
    ('[:X]', '\u1E8C', '\\u1E8C'), # LATIN CAPITAL LETTER X WITH DIAERESIS
    ('[:x]', '\u1E8D', '\\u1E8D'), # LATIN SMALL LETTER X WITH DIAERESIS
    ('[.Y]', '\u1E8E', '\\u1E8E'), # LATIN CAPITAL LETTER Y WITH DOT ABOVE
    ('[.y]', '\u1E8F', '\\u1E8F'), # LATIN SMALL LETTER Y WITH DOT ABOVE
    ('[^Z]', '\u1E90', '\\u1E90'), # LATIN CAPITAL LETTER Z WITH CIRCUMFLEX
    ('[^z]', '\u1E91', '\\u1E91'), # LATIN SMALL LETTER Z WITH CIRCUMFLEX
    ('[Z.]', '\u1E92', '\\u1E92'), # LATIN CAPITAL LETTER Z WITH DOT BELOW
    ('[z.]', '\u1E93', '\\u1E93'), # LATIN SMALL LETTER Z WITH DOT BELOW
    ('[Z=]', '\u1E94', '\\u1E94'), # LATIN CAPITAL LETTER Z WITH LINE BELOW
    ('[z=]', '\u1E95', '\\u1E95'), # LATIN SMALL LETTER Z WITH LINE BELOW
    ('[h=]', '\u1E96', '\\u1E96'), # LATIN SMALL LETTER H WITH LINE BELOW
    ('[:t]', '\u1E97', '\\u1E97'), # LATIN SMALL LETTER T WITH DIAERESIS
    ('[°w]', '\u1E98', '\\u1E98'), # LATIN SMALL LETTER W WITH RING ABOVE
    ('[°y]', '\u1E99', '\\u1E99'), # LATIN SMALL LETTER Y WITH RING ABOVE
    #('[]', '\u1E9A', '\\u1E9A'), # LATIN SMALL LETTER A WITH RIGHT HALF RING
    ('[.[s]]', '\u1E9B', '\\u1E9B'), # LATIN SMALL LETTER LONG S WITH DOT ABOVE
    ('[/[s]]', '\u1E9C', '\\u1E9C'), # LATIN SMALL LETTER LONG S WITH DIAGONAL STROKE
    ('[-[s]]', '\u1E9D', '\\u1E9D'), # LATIN SMALL LETTER LONG S WITH HIGH STROKE
    #('[]', '\u1E9E', '\\u1E9E'), # LATIN CAPITAL LETTER SHARP S
    #('[delta]', '\u1E9F', '\\u1E9F'), # LATIN SMALL LETTER DELTA    (use Greek versions instead)
    ('[A.]', '\u1EA0', '\\u1EA0'), # LATIN CAPITAL LETTER A WITH DOT BELOW
    ('[a.]', '\u1EA1', '\\u1EA1'), # LATIN SMALL LETTER A WITH DOT BELOW
    ('[,A]', '\u1EA2', '\\u1EA2'), # LATIN CAPITAL LETTER A WITH HOOK ABOVE
    ('[,a]', '\u1EA3', '\\u1EA3'), # LATIN SMALL LETTER A WITH HOOK ABOVE
    ('[\'Â]', '\u1EA4', '\\u1EA4'), # LATIN CAPITAL LETTER A WITH CIRCUMFLEX AND ACUTE
    ('[\'â]', '\u1EA5', '\\u1EA5'), # LATIN SMALL LETTER A WITH CIRCUMFLEX AND ACUTE
    ('[`Â]', '\u1EA6', '\\u1EA6'), # LATIN CAPITAL LETTER A WITH CIRCUMFLEX AND GRAVE
    ('[`â]', '\u1EA7', '\\u1EA7'), # LATIN SMALL LETTER A WITH CIRCUMFLEX AND GRAVE
    ('[,Â]', '\u1EA8', '\\u1EA8'), # LATIN CAPITAL LETTER A WITH CIRCUMFLEX AND HOOK ABOVE
    ('[,â]', '\u1EA9', '\\u1EA9'), # LATIN SMALL LETTER A WITH CIRCUMFLEX AND HOOK ABOVE
    ('[~Â]', '\u1EAA', '\\u1EAA'), # LATIN CAPITAL LETTER A WITH CIRCUMFLEX AND TILDE
    ('[~â]', '\u1EAB', '\\u1EAB'), # LATIN SMALL LETTER A WITH CIRCUMFLEX AND TILDE
    ('[Â.]', '\u1EAC', '\\u1EAC'), # LATIN CAPITAL LETTER A WITH CIRCUMFLEX AND DOT BELOW
    ('[â.]', '\u1EAD', '\\u1EAD'), # LATIN SMALL LETTER A WITH CIRCUMFLEX AND DOT BELOW
    ('[\')A]', '\u1EAE', '\\u1EAE'), # LATIN CAPITAL LETTER A WITH BREVE AND ACUTE
    ('[\')a]', '\u1EAF', '\\u1EAF'), # LATIN SMALL LETTER A WITH BREVE AND ACUTE
    ('[`)A]', '\u1EB0', '\\u1EB0'), # LATIN CAPITAL LETTER A WITH BREVE AND GRAVE
    ('[`)a]', '\u1EB1', '\\u1EB1'), # LATIN SMALL LETTER A WITH BREVE AND GRAVE
    ('[,)A]', '\u1EB2', '\\u1EB2'), # LATIN CAPITAL LETTER A WITH BREVE AND HOOK ABOVE
    ('[,)a]', '\u1EB3', '\\u1EB3'), # LATIN SMALL LETTER A WITH BREVE AND HOOK ABOVE
    ('[~)A]', '\u1EB4', '\\u1EB4'), # LATIN CAPITAL LETTER A WITH BREVE AND TILDE
    ('[~)a]', '\u1EB5', '\\u1EB5'), # LATIN SMALL LETTER A WITH BREVE AND TILDE
    ('[)A.]', '\u1EB6', '\\u1EB6'), # LATIN CAPITAL LETTER A WITH BREVE AND DOT BELOW
    ('[)a.]', '\u1EB7', '\\u1EB7'), # LATIN SMALL LETTER A WITH BREVE AND DOT BELOW
    ('[E.]', '\u1EB8', '\\u1EB8'), # LATIN CAPITAL LETTER E WITH DOT BELOW
    ('[e.]', '\u1EB9', '\\u1EB9'), # LATIN SMALL LETTER E WITH DOT BELOW
    ('[,E]', '\u1EBA', '\\u1EBA'), # LATIN CAPITAL LETTER E WITH HOOK ABOVE
    ('[,e]', '\u1EBB', '\\u1EBB'), # LATIN SMALL LETTER E WITH HOOK ABOVE
    ('[~E]', '\u1EBC', '\\u1EBC'), # LATIN CAPITAL LETTER E WITH TILDE
    ('[~e]', '\u1EBD', '\\u1EBD'), # LATIN SMALL LETTER E WITH TILDE
    ('[\'Ê]', '\u1EBE', '\\u1EBE'), # LATIN CAPITAL LETTER E WITH CIRCUMFLEX AND ACUTE
    ('[\'ê]', '\u1EBF', '\\u1EBF'), # LATIN SMALL LETTER E WITH CIRCUMFLEX AND ACUTE
    ('[`Ê]', '\u1EC0', '\\u1EC0'), # LATIN CAPITAL LETTER E WITH CIRCUMFLEX AND GRAVE
    ('[`ê]', '\u1EC1', '\\u1EC1'), # LATIN SMALL LETTER E WITH CIRCUMFLEX AND GRAVE
    ('[,Ê]', '\u1EC2', '\\u1EC2'), # LATIN CAPITAL LETTER E WITH CIRCUMFLEX AND HOOK ABOVE
    ('[,ê]', '\u1EC3', '\\u1EC3'), # LATIN SMALL LETTER E WITH CIRCUMFLEX AND HOOK ABOVE
    ('[~Ê]', '\u1EC4', '\\u1EC4'), # LATIN CAPITAL LETTER E WITH CIRCUMFLEX AND TILDE
    ('[~ê]', '\u1EC5', '\\u1EC5'), # LATIN SMALL LETTER E WITH CIRCUMFLEX AND TILDE
    ('[Ê.]', '\u1EC6', '\\u1EC6'), # LATIN CAPITAL LETTER E WITH CIRCUMFLEX AND DOT BELOW
    ('[ê.]', '\u1EC7', '\\u1EC7'), # LATIN SMALL LETTER E WITH CIRCUMFLEX AND DOT BELOW
    ('[,I]', '\u1EC8', '\\u1EC8'), # LATIN CAPITAL LETTER I WITH HOOK ABOVE
    ('[,i]', '\u1EC9', '\\u1EC9'), # LATIN SMALL LETTER I WITH HOOK ABOVE
    ('[I.]', '\u1ECA', '\\u1ECA'), # LATIN CAPITAL LETTER I WITH DOT BELOW
    ('[i.]', '\u1ECB', '\\u1ECB'), # LATIN SMALL LETTER I WITH DOT BELOW
    ('[O.]', '\u1ECC', '\\u1ECC'), # LATIN CAPITAL LETTER O WITH DOT BELOW
    ('[o.]', '\u1ECD', '\\u1ECD'), # LATIN SMALL LETTER O WITH DOT BELOW
    ('[,O]', '\u1ECE', '\\u1ECE'), # LATIN CAPITAL LETTER O WITH HOOK ABOVE
    ('[,o]', '\u1ECF', '\\u1ECF'), # LATIN SMALL LETTER O WITH HOOK ABOVE
    ('[\'Ô]', '\u1ED0', '\\u1ED0'), # LATIN CAPITAL LETTER O WITH CIRCUMFLEX AND ACUTE
    ('[\'ô]', '\u1ED1', '\\u1ED1'), # LATIN SMALL LETTER O WITH CIRCUMFLEX AND ACUTE
    ('[`Ô]', '\u1ED2', '\\u1ED2'), # LATIN CAPITAL LETTER O WITH CIRCUMFLEX AND GRAVE
    ('[`ô]', '\u1ED3', '\\u1ED3'), # LATIN SMALL LETTER O WITH CIRCUMFLEX AND GRAVE
    ('[,Ô]', '\u1ED4', '\\u1ED4'), # LATIN CAPITAL LETTER O WITH CIRCUMFLEX AND HOOK ABOVE
    ('[,ô]', '\u1ED5', '\\u1ED5'), # LATIN SMALL LETTER O WITH CIRCUMFLEX AND HOOK ABOVE
    ('[~Ô]', '\u1ED6', '\\u1ED6'), # LATIN CAPITAL LETTER O WITH CIRCUMFLEX AND TILDE
    ('[~ô]', '\u1ED7', '\\u1ED7'), # LATIN SMALL LETTER O WITH CIRCUMFLEX AND TILDE
    ('[Ô.]', '\u1ED8', '\\u1ED8'), # LATIN CAPITAL LETTER O WITH CIRCUMFLEX AND DOT BELOW
    ('[ô.]', '\u1ED9', '\\u1ED9'), # LATIN SMALL LETTER O WITH CIRCUMFLEX AND DOT BELOW
    #('[]', '\u1EDA', '\\u1EDA'), # LATIN CAPITAL LETTER O WITH HORN AND ACUTE
    #('[]', '\u1EDB', '\\u1EDB'), # LATIN SMALL LETTER O WITH HORN AND ACUTE
    #('[]', '\u1EDC', '\\u1EDC'), # LATIN CAPITAL LETTER O WITH HORN AND GRAVE
    #('[]', '\u1EDD', '\\u1EDD'), # LATIN SMALL LETTER O WITH HORN AND GRAVE
    #('[]', '\u1EDE', '\\u1EDE'), # LATIN CAPITAL LETTER O WITH HORN AND HOOK ABOVE
    #('[]', '\u1EDF', '\\u1EDF'), # LATIN SMALL LETTER O WITH HORN AND HOOK ABOVE
    #('[]', '\u1EE0', '\\u1EE0'), # LATIN CAPITAL LETTER O WITH HORN AND TILDE
    #('[]', '\u1EE1', '\\u1EE1'), # LATIN SMALL LETTER O WITH HORN AND TILDE
    #('[]', '\u1EE2', '\\u1EE2'), # LATIN CAPITAL LETTER O WITH HORN AND DOT BELOW
    #('[]', '\u1EE3', '\\u1EE3'), # LATIN SMALL LETTER O WITH HORN AND DOT BELOW
    ('[U.]', '\u1EE4', '\\u1EE4'), # LATIN CAPITAL LETTER U WITH DOT BELOW
    ('[u.]', '\u1EE5', '\\u1EE5'), # LATIN SMALL LETTER U WITH DOT BELOW
    ('[,U]', '\u1EE6', '\\u1EE6'), # LATIN CAPITAL LETTER U WITH HOOK ABOVE
    ('[,u]', '\u1EE7', '\\u1EE7'), # LATIN SMALL LETTER U WITH HOOK ABOVE
    #('[]', '\u1EE8', '\\u1EE8'), # LATIN CAPITAL LETTER U WITH HORN AND ACUTE
    #('[]', '\u1EE9', '\\u1EE9'), # LATIN SMALL LETTER U WITH HORN AND ACUTE
    #('[]', '\u1EEA', '\\u1EEA'), # LATIN CAPITAL LETTER U WITH HORN AND GRAVE
    #('[]', '\u1EEB', '\\u1EEB'), # LATIN SMALL LETTER U WITH HORN AND GRAVE
    #('[]', '\u1EEC', '\\u1EEC'), # LATIN CAPITAL LETTER U WITH HORN AND HOOK ABOVE
    #('[]', '\u1EED', '\\u1EED'), # LATIN SMALL LETTER U WITH HORN AND HOOK ABOVE
    #('[]', '\u1EEE', '\\u1EEE'), # LATIN CAPITAL LETTER U WITH HORN AND TILDE
    #('[]', '\u1EEF', '\\u1EEF'), # LATIN SMALL LETTER U WITH HORN AND TILDE
    #('[]', '\u1EF0', '\\u1EF0'), # LATIN CAPITAL LETTER U WITH HORN AND DOT BELOW
    #('[]', '\u1EF1', '\\u1EF1'), # LATIN SMALL LETTER U WITH HORN AND DOT BELOW
    ('[`Y]', '\u1EF2', '\\u1EF2'), # LATIN CAPITAL LETTER Y WITH GRAVE
    ('[`y]', '\u1EF3', '\\u1EF3'), # LATIN SMALL LETTER Y WITH GRAVE
    ('[Y.]', '\u1EF4', '\\u1EF4'), # LATIN CAPITAL LETTER Y WITH DOT BELOW
    ('[y.]', '\u1EF5', '\\u1EF5'), # LATIN SMALL LETTER Y WITH DOT BELOW
    ('[,Y]', '\u1EF6', '\\u1EF6'), # LATIN CAPITAL LETTER Y WITH HOOK ABOVE
    ('[,y]', '\u1EF7', '\\u1EF7'), # LATIN SMALL LETTER Y WITH HOOK ABOVE
    ('[~Y]', '\u1EF8', '\\u1EF8'), # LATIN CAPITAL LETTER Y WITH TILDE
    ('[~y]', '\u1EF9', '\\u1EF9'), # LATIN SMALL LETTER Y WITH TILDE
    #('[]', '\u1EFA', '\\u1EFA'), # LATIN CAPITAL LETTER MIDDLE-WELSH LL
    #('[]', '\u1EFB', '\\u1EFB'), # LATIN SMALL LETTER MIDDLE-WELSH LL
    #('[]', '\u1EFC', '\\u1EFC'), # LATIN CAPITAL LETTER MIDDLE-WELSH V
    #('[]', '\u1EFD', '\\u1EFD'), # LATIN SMALL LETTER MIDDLE-WELSH V
    #('[]', '\u1EFE', '\\u1EFE'), # LATIN CAPITAL LETTER Y WITH LOOP
    #('[]', '\u1EFF', '\\u1EFF'), # LATIN SMALL LETTER Y WITH LOOP
     ('[Alpha]', '\u0391', '\\u0391'),
     ('[alpha]', '\u03B1', '\\u03B1'),
     ('[Beta]', '\u0392', '\\u0392'),
     ('[beta]', '\u03B2', '\\u03B2'),
     ('[Gamma]', '\u0393', '\\u0393'),
     ('[gamma]', '\u03B3', '\\u03B3'),
     ('[Delta]', '\u0394', '\\u0394'),
     ('[delta]', '\u03B4', '\\u03B4'),
     ('[Epsilon]', '\u0395', '\\u0395'),
     ('[epsilon]', '\u03B5', '\\u03B5'),
     ('[Zeta]', '\u0396', '\\u0396'),
     ('[zeta]', '\u03B6', '\\u03B6'),
     ('[Eta]', '\u0397', '\\u0397'),
     ('[eta]', '\u03B7', '\\u03B7'),
     ('[Theta]', '\u0398', '\\u0398'),
     ('[theta]', '\u03B8', '\\u03B8'),
     ('[Iota]', '\u0399', '\\u0399'),
     ('[iota]', '\u03B9', '\\u03B9'),
     ('[Kappa]', '\u039A', '\\u039A'),
     ('[kappa]', '\u03BA', '\\u03BA'),
     ('[Lamda]', '\u039B', '\\u039B'),
     ('[lamda]', '\u03BB', '\\u03BB'),
     ('[Mu]', '\u039C', '\\u039C'),
     ('[mu]', '\u03BC', '\\u03BC'),
     ('[Nu]', '\u039D', '\\u039D'),
     ('[nu]', '\u03BD', '\\u03BD'),
     ('[Xi]', '\u039E', '\\u039E'),
     ('[xi]', '\u03BE', '\\u03BE'),
     ('[Omicron]', '\u039F', '\\u039F'),
     ('[omicron]', '\u03BF', '\\u03BF'),
     ('[Pi]', '\u03A0', '\\u03A0'),
     ('[pi]', '\u03C0', '\\u03C0'),
     ('[Rho]', '\u03A1', '\\u03A1'),
     ('[rho]', '\u03C1', '\\u03C1'),
     ('[Sigma]', '\u03A3', '\\u03A3'),
     ('[sigma]', '\u03C3', '\\u03C3'),
     ('[Tau]', '\u03A4', '\\u03A4'),
     ('[tau]', '\u03C4', '\\u03C4'),
     ('[Upsilon]', '\u03A5', '\\u03A5'),
     ('[upsilon]', '\u03C5', '\\u03C5'),
     ('[Phi]', '\u03A6', '\\u03A6'),
     ('[phi]', '\u03C6', '\\u03C6'),
     ('[Chi]', '\u03A7', '\\u03A7'),
     ('[chi]', '\u03C7', '\\u03C7'),
     ('[Psi]', '\u03A8', '\\u03A8'),
     ('[psi]', '\u03C8', '\\u03C8'),
     ('[Omega]', '\u03A9', '\\u03A9'),
     ('[omega]', '\u03C9', '\\u03C9'),
     #('\?', '\u037E', '?'),
     #(';', '\u0387', ';'),
     ('[Koppa]', '\u03D8', '\\u03D8'),
     ('[koppa]', '\u03D9', '\\u03D9'),
     ('[Digamma]', '\u03DC', '\\u03DC'),
     ('[digamma]', '\u03DD', '\\u03DD'),
     ('[Qoppa]', '\u03DE', '\\u03DE'),
     ('[qoppa]', '\u03DF', '\\u03DF'),
     ('[Sampi]', '\u03E0', '\\u03E0'),
     ('[sampi]', '\u03E1', '\\U03E1'),
    ]

  def __init__(self, args, renc):
    del self.wb[:]
    del self.eb[:]
    self.renc = renc # requested output encoding (t, u, or h)
    self.debug = args.debug
    self.srcfile = args.infile
    self.anonymous = args.anonymous
    self.log = args.log
    self.listcvg = args.listcvg
    self.cvgfilter = args.filter
    self.wrapper = textwrap.TextWrapper()
    self.wrapper.break_long_words = False
    self.wrapper.break_on_hyphens = False
    self.nregs["psi"] = "0" # default above/below paragraph spacing for indented text
    self.nregs["psb"] = "1.0em" # default above/below paragraph spacing for block text
    self.nregs["pnc"] = "silver" # use to define page number color in HTML
    self.nregs["lang"] = "en" # base language for the book (used in HTML header)
    self.nregs["Footnote"] = "Footnote" # English word for Footnote for text files
    self.nregs["Illustration"] = "Illustration" # English word for Illustration for text files
    self.nregs["dcs"] = "250%" # drop cap font size
    self.encoding = "" # input file encoding
    self.pageno = "" # page number stored as string

  def cvglist(self):
    if self.listcvg:
      f1 = codecs.open("ppgen-cvglist.txt", "w", encoding="UTF-8")
      f1.write("\r\n\r\nppgen {}\r\n".format(VERSION))
      f1.write("\r\nBuilt-in Greek Characters:\r\n\r\n")
      for s in self.gk:
        if len(s) == 4:
          f1.write("{:<17} {}\r\n".format(s[2], s[3]))
        else:
          f1.write("{:<17} {}\r\n".format(s[2], s[1]))
      f1.write("\r\n\r\nBuilt-in diacritics:\r\n\r\n")
      for s in self.diacritics:
        #f1.write("{:<14}{:<5} {:<5}  {}\r\n".format(s[0], s[1], s[2], s[4]))
        f1.write("{:<14}{:<5} {:<5}  {}\r\n".format(s[0], s[1], s[2], unicodedata.name(s[1])))
      f1.close()
      exit(1)

  # Create special output file after .gk or .cv if requested, and quit
  def cvgbailout(self):
    bailfn = re.sub("-src", "", self.srcfile.split('.')[0]) + "-cvgout-utf8.txt"
    f1 = codecs.open(bailfn, "w", encoding="UTF-8")
    for index,t in enumerate(self.wb):
      f1.write( "{:s}\r\n".format(t.rstrip()) )
    f1.close()
    print("Terminating as requested after .cv/.gk processing.\n\tOutput file: {}".format(bailfn))
    exit(1)

  # map UTF-8 characters to characters safe for printing on non UTF-8 terminals
  def umap(self, s):
    t = ""
    for c in s: # for every character on the line provided
      if c in self.d: # is it in the list of converting characters?
        t += self.d[c] # yes, replace with converted Latin-1 character
      else:
        if ord(c) < 0x100:
          t += c # no conversion, transfer character as is
        else:
          t += "*" # use an asterisk if not plain text
    return t

  # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  # get the value of the requested parameter from attr string
  # remove parameter from string, return string and parameter
  def get_id(self, tgt, attr, np=2):

    done = False
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
      m = re.search(r"{}=(.*?)($|[ >])".format(tgt), attr)  # no quotes
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
    s = self.umap(message)
    sys.stderr.write("FATAL: " + s + "\n")
    exit(1)

  # display warning
  def warn(self, message):
    if message not in self.warnings: # don't give exact same warning more than once.
      s = self.umap(message)
      self.warnings.append(s)
      sys.stderr.write("**warning: " + s + "\n")

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
    elif ".h4" == dotcmd:
      self.doH4()
    elif ".h5" == dotcmd:
      self.doH5()
    elif ".h6" == dotcmd:
      self.doH6()
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
    elif ".dv" == dotcmd: # user-specifice <div> for HTML
      self.doDiv()
    else:
      self.crash_w_context("unhandled dot command: {}".format(self.wb[self.cl]), self.cl)

  def crash_w_context(self, msg, i, r=5):
    print("{}\ncontext:".format(msg))
    startline = max(0,i-r)
    endline = min(len(self.wb),i+r)
    for j in range(startline,endline):
      s = self.umap(self.wb[j])
      if j == i:
        print(">> {}".format(s))
      else:
        print("   {}".format(s))
    self.fatal("exiting")

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


  # .nr named register
  # we are here if the line starts with .nr
  def doNr(self):
    m = re.match(r"\.nr (.+?) (.+)", self.wb[self.cl])
    if not m:
      self.crash_w_context("malformed .nr command: {}".format(self.wb[self.cl]), self.cl)
    else:
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
      if registerName == "lang": # base language
        self.nregs["lang"] = m.group(2)
        known_register = True
      if registerName == "Footnote": # foreign language translation for "Footnote"
        self.nregs["Footnote"] = self.deQuote(m.group(2), self.cl)
        known_register = True
      if registerName == "Illustration": # foreign language translation for "Illustration"
        self.nregs["Illustration"] = self.deQuote(m.group(2), self.cl)
        known_register = True
      if registerName == "dcs": # drop cap font size
        self.nregs["dcs"] = m.group(2)
        known_register = True
      if not known_register:
        self.crash_w_context("undefined register: {}".format(registerName), self.cl)
      del(self.wb[self.cl])

  def preProcessCommon(self):

    def pushk(s, i):
      self.nfstack.append( (s,i) )

    def popk():
      t = self.nfstack.pop() # pops a tuple
      return t

    def gkrepl(gkmatch):
      gkstring = gkmatch.group(1)
      if len(self.gk_user) > 0:   # if PPer provided any additional Greek mappings apply them first
        for s in self.gk_user:
          gkstring, count = re.subn(re.escape(s[0]), re.escape(s[1]), gkstring)
          print(self.umap("Replaced PPer-provided Greek character {} {} times.".format(s[0], count)))
      for s in self.gk:
        gkstring, count = re.subn(s[0], s[1], gkstring)
        if count > 0:
          print("Replaced Greek {} {} times.".format(s[0], count))
      gkorigb = ""
      gkoriga = ""
      if self.gkkeep.lower().startswith("b"): # original before?
        gkorigb = gkmatch.group(0) + " "
      elif self.gkkeep.lower().startswith("a"): # original after?
        gkoriga = " " + gkmatch.group(0)
      gkfull = gkorigb + self.gkpre + gkstring + self.gksuf + gkoriga
      gkfull = gkfull.replace(r"\|", "⑩") # temporarily protect \| and \(space)
      gkfull = gkfull.replace(r"\ ", "⑮")
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

      # insert the filter lines at the front of self.wb
      self.wb[0:0] = text


    #
    # Begin Pre-process Common
    #

    # if source file is UTF-8 and requested encoding is Latin-1, down-convert
    if self.encoding == "utf_8" and self.renc == "l" and not self.cvgfilter:
      for j,ch in enumerate(self.mau):
        for i in range(len(self.wb)): # O=n^2
          self.wb[i] = re.sub(ch, self.mal[j], self.wb[i])
      # user-defined character mapping complete, now do default mapping to Latin-1
      self.utoLat()

    # .if conditionals (moved to preProcessCommon 28-Aug-2014)
    if not self.cvgfilter:
      text = []
      keep = True
      for line in self.wb:

        m = re.match(r"\.if (\w)", line)  # start of conditional
        if m:
          keep = False
          keepType = m.group(1)
          if m.group(1) == 't' and self.renc in "lut":
            keep = True
          elif m.group(1) == 'h' and self.renc == "h":
            keep = True
          continue

        if line == ".if-":
          keep = True
          keepType = None
          continue

        if keep:
          text.append(line)
        elif line.startswith(".sr"):
          m2 = re.match(r"\.sr (\w+)", line)
          if m2:
            if keepType == 't' and "h" in m2.group(1):
              self.warn(".sr command for HTML skipped by .if t: {}".format(self.umap(line)))
            elif keepType == 'h':
              m3 = re.match(r"h*[ult]", m2.group(1))
              if m3:
                self.warn(".sr command for text skipped by .if h: {}".format(self.umap(line)))

    self.wb = text
    text = []

    # load cvg filter file if specified
    if self.cvgfilter:
      loadFilter()

    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    # process [Greek: ...] in UTF-8 output if requested to via .gk command
    i = 0
    gk_requested = False
    gk_done = False
    self.gkpre = ""
    self.gksuf = ""
    self.gkkeep = "n"
    gk_quit = "n"
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
          self.wb[i], gk_quit = self.get_id("quit", self.wb[i])
        if "done" in self.wb[i]:
          gk_done = True
        del self.wb[i]
        gk_requested = True

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
    if gk_requested and (self.renc == "u" or self.renc == "h" or self.cvgfilter):
      text = '\n'.join(self.wb) # form all lines into a blob of lines separated by newline characters
      text = re.sub(r"\[Greek: (.*?)]", gkrepl, text, flags=re.DOTALL)

      self.wb = text.splitlines()

    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    # process diacritic markup in UTF-8 output if requested to via .cv command
    i = 0
    dia_requested = False
    dia_done = False
    diapre = ""
    diasuf = ""
    diakeep = "n"
    diatest = False
    dia_quit = "n"
    while i < len(self.wb) and not dia_done:
      if self.wb[i].startswith(".cv"):
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
          self.wb[i], dia_quit = self.get_id("quit", self.wb[i])
        if "done" in self.wb[i]:
          dia_done = True
        del self.wb[i]
        dia_requested = True
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
    if dia_requested and (self.renc == "u" or self.renc == "h" or self.cvgfilter):
      text = '\n'.join(self.wb) # form all lines into a blob of lines separated by newline characters
      if not diatest:
        if len(self.diacritics_user) > 0:
          for s in self.diacritics_user:
            text, count = re.subn(re.escape(s[0]), re.escape(s[1]), text)
            print(self.umap("Replaced PPer-provided diacritic {} {} times.".format(s[0], count)))
        for s in self.diacritics:
          text, count = re.subn(re.escape(s[0]), re.escape(s[1]), text)
          if count > 0:
            print("Replaced {} {} times.".format(s[0], count))
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
            text, count = re.subn(re.escape(s[0]), re.escape(repl), text)
            print(self.umap("Replaced PPer-provided diacritic {} {} times.".format(s[0], count)))
        for s in self.diacritics:
          if diakeep.lower().startswith("b"): # original before?
            diaorigb = s[0]
            diaoriga = ""
          elif diakeep.lower().startswith("a"): # original after?
            diaoriga = s[0]
            diaorigb = ""
          repl = diaorigb + diapre + s[1] + diasuf + diaoriga
          text, count = re.subn(re.escape(s[0]), re.escape(repl), text)
          if count > 0:
            print("Replaced {} {} times.".format(s[0], count))
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
              print("Potential diacritics not converted:")
              header_needed = False
            try:
              print(" {} occurred {} times.".format(m.group(0), count))
            except:
              print(self.umap("**{} occurred {} times. (Safe-printed due to error.)".format(m.group(0), count)))
          m = re.search(r"\[([^*\]].{1,7}?)]", text2)
        if header_needed:
          print("No unconverted diacritics seem to remain after conversion.")
        text2 = []
      self.wb = text.splitlines()

    if gk_quit.lower().startswith("y") or dia_quit.lower().startswith("y") or self.cvgfilter:
      self.cvgbailout()  # bail out after .cv/.gk processing if user requested early termination

    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    # process character mappings
    # character mappings are from the UTF-8 representation to Latin-1
    i = 0
    del self.mau[:]
    del self.mal[:]
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

    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    # process search/replace strings
    # .sr <which> /search/replace/
    # which is a string containing some combination of ulth (UTF-8, Latin-1, Text, HTML)
    # search is  reg-ex search string
    # replace is a reg-ex replace string
    # / is any character not contained within either search or replace
    #
    # Values gathered during preprocessCommon and saved for use during post-processing
    i = 0
    self.srw = []    # "which" array
    self.srs = []    # "search" array
    self.srr = []    # "replace" array
    while i < len(self.wb):
      if self.wb[i].startswith(".sr"):

        m = re.match(r"\.sr (.*?) (.)(.*)\2(.*)\2(.*)", self.wb[i])  # 1=which 2=separator 3=search 4=replacement 5=unexpected trash
        if m:
          self.srw.append(m.group(1))
          self.srs.append(m.group(3))
          self.srr.append(m.group(4))
          if m.group(5) != "":           # if anything here then the user's expression was wrong, somehow
            self.crash_w_context("Problem with .sr arguments: 1={} 2={} 3={} 4={} Unexpected 5={}".format(m.group(1),m.group(2), m.group(3), m.group(4), m.group(5)), i)
          del self.wb[i]
          continue
        else:
          self.crash_w_context("Problem parsing .sr arguments.", i)

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
      self.wb[i] = self.wb[i].replace(r"\>", "⑳")
      self.wb[i] = self.wb[i].replace(r"\:", "⑥")
      self.wb[i] = self.wb[i].replace(r"\-", "⑨")
      # spacing
      self.wb[i] = self.wb[i].replace(r'\ ', "ⓢ") # non-breaking space
      self.wb[i] = self.wb[i].replace(r'\_', "ⓢ") # alternate non-breaking space
      self.wb[i] = self.wb[i].replace(r"\&", "ⓣ") # zero space
      self.wb[i] = self.wb[i].replace(r"\^", "ⓤ") # thin space (after italics)
      self.wb[i] = self.wb[i].replace(r"\|", "ⓥ") # thick space (between ellipsis dots)

      # unprotect temporarily protected characters from Greek strings
      self.wb[i] = self.wb[i].replace("⑩", r"\|") # restore temporarily protected \| and \(space)
      self.wb[i] = self.wb[i].replace("⑮", r"\ ")

      # special characters
      # leave alone if in literal block (correct way, not yet implemented)
      # map &nbsp; to non-breaking space
      # 10-Sep-2014: I don't fully understand why I did this mapping
      self.wb[i] = self.wb[i].replace("&nbsp;", "ⓢ") # ampersand
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
        if len(tlex) > 1:
          macroid = tlex[1] # string
        else:
          self.crash_w_context("incorrect .dm command: macro name missing.", i)
        del self.wb[i]
        t = []
        while i < len(self.wb) and not self.wb[i].startswith(".dm"):  # accumulate statements into the macro until we hit another .dm or a .dm-
          t.append(self.wb[i])
          del self.wb[i]
        if i < len(self.wb) and self.wb[i] == ".dm-":       # if we hit a .dm- then delete it and finalize the macro
          del self.wb[i] # the closing .dm-
        else:                                               # quit if we hit end-of-file or a .dm before finding the .dm-
          self.fatal("missing .dm- for macro: " + macroid)
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
        while (i < len(self.wb) - 1) and self.wb[i].endswith("\\"):   # allow continuation via ending \ for .pm
          self.wb[i] = re.sub(r"\\$", "", self.wb[i]) + self.wb[i+1]
          del self.wb[i+1]
        if self.wb[i].endswith("\\"):
          self.fatal("file ends with continued .pm")
        try:
          tlex = shlex.split(self.wb[i])  # ".pm" "tnote" "a" "<li>"
        except:
          if 'd' in self.debug:
            traceback.print_exc()
            self.fatal("Above error occurred while processing line: {}".format(self.wb[i]))
          else:
            self.fatal("Error occurred parsing .pm arguments for: {}".format(self.wb[i]))
        macroid = tlex[1]  # "tnote"
        # t = self.macro[macroid].copy() # after 3.3 only
        # t = self.macro[macroid][:] # another way
        if not macroid in self.macro:
          self.fatal("undefined macro {}: ".format(macroid, self.wb[i]))
        t = list(self.macro[macroid]) # all the lines in this macro as previously defined
        for j,line in enumerate(t): # for each line
          m = re.search(r'\$(\d{1,2})', t[j]) # is there a substitution?
          while m:
            pnum = int(m.group(1))
            subst = r"\${}".format(pnum)
            if pnum < len(tlex) - 1:
              t[j] = re.sub(subst, tlex[pnum+1], t[j], 1)
            else:
              self.warn("Incorrect macro invocation (argument ${} missing): {}".format(pnum, self.wb[i]))
              t[j] = re.sub(subst, "***missing***", t[j], 1)
            m = re.search(r'\$(\d{1,2})', t[j]) # another substitution on same line
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
    # .bn (GG-compatible .bin file maintenance)
    i = 0
    self.bnPresent = False
    while i < len(self.wb):
      if self.wb[i].startswith(".bn"):
        m = re.search("(\w+?)\.png",self.wb[i])
        if m:
          self.bnPresent = True
          self.wb[i] = "⑱{}⑱".format(m.group(1))
        else:
          self.crash_w_context("malformed .bn command",i)
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
  bb = [] # GG .bin buffer

  long_table_line_count = 0

  def __init__(self, args, renc):
    Book.__init__(self, args, renc)
    if self.listcvg:
      self.cvglist()
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
    if self.encoding == "utf_8":
      encoding = "UTF-8"
    else:
      encoding = "ISO-8859-1"
    f1 = codecs.open("bailout.txt", "w", encoding=encoding)
    for index,t in enumerate(buffer):
      f1.write( "{:s}\r\n".format(t.rstrip()) )
    f1.close()
    exit(1)

  def line_len_diff(self, x):
    """ calculate max diff between longest and shortest line of data x[] """
    longest_line_len = 0
    shortest_line_len = 1000
    for line in x:
      tline = line
      if self.bnPresent:  # remove .bn info if any before doing calculation
        tline = re.sub("⑱.*?⑱","",tline)
      longest_line_len = max(longest_line_len, len(tline))
      shortest_line_len = min(shortest_line_len, len(tline))
    return longest_line_len - shortest_line_len

  def shortest_line_len(self, x):
    """ return length of shotest line in x[] """
    shortest_line_len = 1000
    for line in x:
      tline = line
      if self.bnPresent: # remove .bn info if any before doing calculation
        tline = re.sub("⑱.*?⑱","",tline)
      shortest_line_len = min(shortest_line_len, len(tline))
    return shortest_line_len

  # wrap string into paragraph in t[]
  def wrap_para(self, s,  indent, ll, ti):
    # if ti < 0, strip off characters that will be in the hanging margin
    hold = ""
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
            hold = s[0:howmany1] + m.group(2) + m.group3[0:howmany2]
            howmany3 = len(hold)
            s = s[howmany3:]
          else:
            self.fatal("error processing .bn info: {}".format(s))

    # if ti > 0, add leading nbsp
    if ti > 0:
      s = "⑧" * ti + s

    # at this point, s is ready to wrap
    mywidth = ll - indent
    t =[]
    twidth = mywidth
    while len(s) > twidth:
      twidth2 = 0
      if self.bnPresent:
        m = re.match("(.*?)(⑱.*?⑱)(.*)",s)
        while twidth2 < mywidth and m:
          twidth2 += len(m.group(1))
          if twidth2 <= mywidth:  # if .bn info within first mywidth real characters
            twidth += len(m.group(2)) # allow wider split to account for .bn info
            stemp = m.group(3)
            m = re.match("(.*?)(⑱.*?⑱)(.*)",stemp)
      if len(s) > twidth:
        try:
          snip_at = s.rindex(" ", 0, twidth)
        except:
          # could not find a place to wrap
          try: # this one might fail, too, so catch exceptions
            snip_at = s.index(" ", twidth) # Plan B
          except:
            snip_at = len(s)
          if len(t) == 0:
            self.warn("wide line: {}".format(hold + s)) # include any "hold" characters if wrapping first line
          else:
            self.warn("wide line: {}".format(s)) # else just include the current line.
        t.append(s[:snip_at])
        if snip_at < len(s):
          s = s[snip_at+1:]
        else:
          s = ""
        twidth = mywidth
    if len(t) == 0 or len(s) > 0: #ensure t has something in it, but don't add a zero length s (blank line) to t unless t is empty
      t.append(s)

    for i, line in enumerate(t):
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
    text = re.sub(r"#([iIvVxXlLcCdDmM]+)#", r"\1", text) # don't forget about Roman numerals as page numbers
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
        s = re.sub("\[(\d+)\]", "", s, 1)
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
    while i < len(self.wb):

    # skip literal sections
      if ".li" == self.wb[i]:
        while not ".li-" == self.wb[i]:
          i += 1
        i += 1
        continue

      m = re.match(r"\.fn (\d+)", self.wb[i]) # explicit
      if m:
        fncr = int(m.group(1)) + 1
        i += 1
        continue

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

    # ensure .bn info does not interfere with combining/collapsing space requests
    # by detecting the sequence .RS / .bn info / .RS and swapping to end up with
    #   .RS / .RS / .bn info
    i = 0
    if self.bnPresent:
      while i < len(self.eb) - 2:
        if self.eb[i].startswith(".RS") and self.eb[i+1].startswith("⑱"):  # if .RS and possibly .bn info
          m = re.match("^⑱.*?⑱(.*)$",self.eb[i+1])  # confirm .bn info only (no other data on line)
          if m and m.group(1) == "":         # if so

                # handle case of .RS , .bn (from above), .bn by advancing over a sequence of .bn until we find .RS or data
                # if we end on .RS then remove that .RS and insert it before the first .bn in the sequence
                # i => first .RS
                # i + 1 => first .bn
                # i + 2,3,... => possible subsequent .bn
                j = i + 2
                m = True
                while m and j < len(self.eb) - 1:
                  m = False
                  if self.eb[j].startswith("⑱"):  # possible .bn info
                    m  =  re.match("^⑱.*?⑱(.*)$",self.eb[j])  # confirm .bn info only (no other data on line)
                    if m and m.group(1) == "":
                      j += 1
                  elif self.eb[j].startswith(".RS"): # .RS line; need to move it
                    temp = self.eb[j]    # make a copy
                    del self.eb[j]  # delete the .RS line
                    self.eb.insert(i+1, temp)  # insert it after the first .RS
                  else:
                    m = False
                  # everything else (data, or .bn + data) falls through as it can't affect .RS combining
        i += 1

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
      # text space replacement
      self.eb[i] = re.sub("ⓢ|Ⓢ", " ", self.eb[i]) # non-breaking space
      self.eb[i] = re.sub("ⓣ|Ⓣ", " ", self.eb[i]) # zero space
      self.eb[i] = re.sub("ⓤ|Ⓤ", " ", self.eb[i]) # thin space
      self.eb[i] = re.sub("ⓥ|Ⓥ", " ", self.eb[i]) # thick space
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


    # process saved search/replace strings, if any
    # but only if our output format matches something in the saved "which" value

    blobbed = False
    for i in range(len(self.srw)):
      if ('t' in self.srw[i]) or (self.renc in self.srw[i]): # if this one applies to the text form we're generating
        k = 0
        l = 0
        ll = 0
        if "\\n" in self.srs[i]: # did user use a regex containing \n ? If so, process all lines in one blob
          if not blobbed:
            text = '\n'.join(self.eb) # form lines into a blob
            blobbed = True
          try:
            m = re.search(self.srs[i], text) # search for current search string
          except:
            if 'd' in self.debug:
              traceback.print_exc()
              self.fatal("Above error occurred searching for {} in complete text blob".format(self.srs[i]))
            else:
              self.fatal("Error occurred searching for {} in complete text blob".format(self.srs[i]))
          if m:                                             # if found
            if 'r' in self.debug:
              print("{} found in complete text blob".format(self.srs[i]))
            try:
              text, l = re.subn(self.srs[i], self.srr[i], text) # replace all occurrences in the blob
              ll += l
            except:
              if 'd' in self.debug:
                traceback.print_exc()
                self.fatal("Above error occurred replacing:{}\n  with {}\n  in complete text blob".format(self.srs[i], self.srr[i]))
              else:
                self.fatal("Error occurred replacing:{}\n  with {}\n  in complete text blob".format(self.srs[i], self.srr[i]))
            if 'r' in self.debug:
              print("Replaced with {}".format(self.srr[i]))
          print("Search string {}:{} matched in complete text and replaced {} times.".format(i+1, self.srs[i], ll))

        else:
          if blobbed:
            self.eb = text.splitlines() # break blob back into individual lines
            blobbed = False
          for j in range(len(self.eb)):
            try:
              m = re.search(self.srs[i], self.eb[j])               # search for current search string
            except:
              if 'd' in self.debug:
                traceback.print_exc()
                self.fatal("Above error occurred searching for\n  {}\n in: {}".format(self.srs[i], self.eb[j]))
              else:
                self.fatal("Error occurred searching for\n  {}\n in: {}".format(self.srs[i], self.eb[j]))
            if m:                                             # if found
              k += 1
              if 'r' in self.debug:
                print("{} found in: {}".format(self.srs[i], self.eb[j]))
              try:
                self.eb[j], l = re.subn(self.srs[i], self.srr[i], self.eb[j])      # replace all occurrences in the line
                ll += l
              except:
                if 'd' in self.debug:
                  traceback.print_exc()
                  self.fatal("Above error occurred replacing:{}\n  with {}\n  in: {}".format(self.srs[i], self.srr[i], self.eb[j]))
                else:
                  self.fatal("Error occurred replacing:{}\n  with {}\n  in: {}".format(self.srs[i], self.srr[i], self.eb[j]))
              if 'r' in self.debug:
                print("Replaced: {}".format(self.eb[j]))
          print("Search string {}:{} matched in {} lines, replaced {} times.".format(i+1, self.srs[i], k, ll))

    if blobbed:
      self.eb = text.splitlines() # break blob back into individual lines
      blobbed = False

    # build GG .bin info if needed
    if self.bnPresent:  # if any .bn were found
      self.bb.append("%::pagenumbers = (") # insert the .bin header into the bb array
      i = 0
      while i < len(self.eb):
        bnInLine = False
        m = re.search("(.*?)⑱(.*?)⑱.*",self.eb[i])  # find any .bn information in this line
        while m:
          bnInLine = True
          t = " 'Pg{}' => ['offset' => '{}.{}', 'label' => '', 'style' => '', 'action' => '', 'base' => ''],".format(m.group(2),i+1,len(m.group(1)))  # format a line in the .bn array (GG wants a 1-based count)
          t = re.sub("\[","{",t,1)
          t = re.sub("]","}",t,1)
          self.bb.append(t)
          self.eb[i] = re.sub("⑱.*?⑱", "", self.eb[i], 1)  # remove the .bn information
          m = re.search("(.*?)⑱(.*?)⑱.*",self.eb[i])  # look for another one on the same line
        if bnInLine and self.eb[i] == "": # delete line if it was only .bn info
          del self.eb[i]
        else:
          i += 1
      self.bb.append(");")  # finish building GG .bin file
      self.bb.append("$::pngspath = '{}';".format(os.path.join(os.path.dirname(self.srcfile),"pngs")))
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
      if len(s) > self.linelimitwarning:
        longcount += 1
        if longcount == 4:
          self.warn("additional long lines not reported")
        if longcount < 4:
          m = re.match(r".{0,60}\s", s)
          self.warn("long line (>{}) beginning:\n  {}....".format(self.linelimitwarning, m.group(0)))
      f1.write( "{:s}\r\n".format(s) )
    f1.close()

    # save GG .bin file if needed
    if self.bnPresent:
      fnb = fn + ".bin"
      f1 = codecs.open(fnb, "w", "ISO-8859-1")
      for index,t in enumerate(self.bb):
        f1.write("{:s}\r\n".format(t))
      f1.close()

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
          m = re.match(r".{0,60}\s", s)
          self.warn("long line (>{}) beginning:\n  {}....".format(self.linelimitwarning, m.group(0)))
      f1.write( "{:s}\r\n".format(s) )
    f1.close()

    # save GG .bin file if needed
    if self.bnPresent:
      fnb = fn + ".bin"
      f1 = codecs.open(fnb, "w", "ISO-8859-1")
      for index,t in enumerate(self.bb):
        f1.write("{:s}\r\n".format(t))
      f1.close()

  # ----- process method group ----------------------------------------------------------

  # .li literal block (pass-through)
  def doLit(self):
    self.cl += 1 # skip the .li
    while (self.cl < len(self.wb)) and self.wb[self.cl] != ".li-":
      self.eb.append(self.wb[self.cl])
      self.cl += 1
    if self.cl < len(self.wb):
      self.cl += 1 # skip the .li-
    else:
      self.crash_w_context("unclosed .li", self.cl)

  # .pb page break
  def doPb(self):
    t = []
    self.eb.append(".RS 1")
    self.eb.append("-" * 72)
    self.eb.append(".RS 1")
    self.cl += 1

  # doDiv (text)
  def doDiv(self):
    j = self.cl
    while j < len(self.wb) and self.wb[j] != ".dv-":   # skip over .dv block
      j += 1
    if j < len(self.wb):
      self.wb[j] = ""                                  # force paragraph break after .dv block if closed properly
    else:
      self.crash_w_context("unclosed .dv directive.",self.cl)
    del(self.wb[self.cl])                              # delete the .dv directive.

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

  #Guts of doH"n" for text
  def doHnText(self, m):
    align = "c" # default all to centered
    if m: # modifier
      rend = m.group(1) # for text we'll ignore everything except a possible align= operand
      if "align=" in rend:
        rend, align = self.get_id("align", rend)
        align = align.lower()
    if align == "c":
      fmt = "{:^72}"
    elif align == "l":
      fmt = "{:<72}"
    elif align == "r":
      fmt = "{:>72}"
    else:
      self.crash_w_context("Incorrect align= value (not c, l, or r):", self.cl)
    self.eb.append(".RS 1")
    if self.bnPresent and self.wb[self.cl+1].startswith("⑱"):    # account for a .bn that immediately follows a .h1/2/3/etc
      m = re.match("^⑱.*?⑱(.*)",self.wb[self.cl+1])
      if m and m.group(1) == "":
        self.eb.append(self.wb[self.cl+1])    # append the .bn info to eb as-is
        self.cl += 1                                           # and ignore it for handling this .h"n"
    h2a = self.wb[self.cl+1].split('|')
    for line in h2a:
      self.eb.append((fmt.format(line)).rstrip())
    self.eb.append(".RS 1")
    self.cl += 2

  # h1
  def doH1(self):
    m = re.match(r"\.h1 (.*)", self.wb[self.cl])
    self.doHnText(m)

  # h2
  def doH2(self):
    m = re.match(r"\.h2 (.*)", self.wb[self.cl])
    self.doHnText(m)

  # h3
  def doH3(self):
    m = re.match(r"\.h3 (.*)", self.wb[self.cl])
    self.doHnText(m)

  # h4
  def doH4(self):
    m = re.match(r"\.h4 (.*)", self.wb[self.cl])
    self.doHnText(m)

  # h5
  def doH5(self):
    m = re.match(r"\.h5 (.*)", self.wb[self.cl])
    self.doHnText(m)

  # h6
  def doH6(self):
    m = re.match(r"\.h6 (.*)", self.wb[self.cl])
    self.doHnText(m)

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

    def parse_illo(s):   # simplified parse_illo; supports only caption model (cm=) and ignores rest of .il line
      s0 = s[:]  # original .il line
      ia = {}

      # caption model
      cm = ""
      if "cm=" in s:
        s, cm = self.get_id("cm", s)
      ia["cm"] = cm
      return(ia)

    m = re.match(r"\.il (.*)", self.wb[self.cl])
    if m:
      # ignore the illustration line except for any cm= info
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
                if len(s) > self.regLL: # must wrap the string, and indent the leftover part
                  m = re.match(r"(\s*)(.*)",s)
                  if m:
                    tempindent = len(m.group(1)) + 2
                    s = m.group(2)
                    t = self.wrap(s, tempindent, self.regLL, -2)
                  else:
                    self.crash_w_context("Oops. Unexpected problem with caption.", i-1)
                else:
                  t.append(s) # no need to wrap, as it's short enough already
              else: # caption line does not have marker, so it's literal text, just wrap to LL if necessary and assume user knows what he's doing
                if len(s) > self.regLL:
                  t = self.wrap(s, 0, self.regLL, 0)
                else: # no need to wrap if it's short enough
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
          t = self.wrap(s, 0, self.regLL, 0)
          self.eb += t
          self.cl += 1 # caption line
      else:
        # no caption, just illustration
        t = ["[{}]".format(self.nregs["Illustration"])]
        self.eb += t
      self.eb.append(".RS 1") # request at least one space in text after illustration

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
    if m:         # will always be true, as we converted ".ti" with no argument to ".ti 2" earlier
      self.regTI += int(m.group(1))
    self.cl += 1

  # no-fill, centered (text)
  def doNfc(self, mo):
    t = []
    i = self.cl + 1 # skip the .nf c line
    while self.wb[i] != ".nf-":
      bnInBlock = False
      if self.bnPresent and self.wb[i].startswith("⑱"):   #just copy .bn info lines, don't change them at all
        m =re.match("^⑱.*?⑱(.*)", self.wb[i])
        if m and m.group(1) == "":
          bnInBlock = True
          t.append(self.wb[i])
          i += 1
          continue

      xt = self.regLL - self.regIN # width of centered line
      xs = "{:^" + str(xt) + "}"
      t.append(" " * self.regIN + xs.format(self.wb[i].strip()))
      i += 1
    self.cl = i + 1 # skip the closing .nf-
    # see if the block has hit the left margin
    need_pad = False
    for line in t:
      if line[0] != " ":
        if bnInBlock and line[0] == "⑱":
          m =re.match("^⑱.*?⑱(.*)", line)
          if not (m and m.group(1) == ""):
            need_pad = True
        else:
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
          if self.bnPresent and self.wb[i].startswith("⑱"):  # if this line is bn info then just put it in the output as-is
            m = re.match("^⑱.*?⑱(.*)",self.wb[i])
            if m and m.group(1) == "":
              self.eb.append(self.wb[i])
              i += 1
              continue
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
          if self.bnPresent and self.wb[i].startswith("⑱"):  # if this line is bn info then just put it in the output as-is
            m = re.match("^⑱.*?⑱(.*)",self.wb[i])
            if m and m.group(1) == "":
              self.eb.append(self.wb[i])
              i += 1
              continue
          xs = "{:>" + str(regBW) + "}"
          self.eb.append(" " * self.regIN + xs.format(self.wb[i].strip()))
          i += 1
          count -= 1
        continue

      if self.bnPresent and self.wb[i].startswith("⑱"):   #just copy .bn info lines, don't change them at all
        m =re.match("^⑱.*?⑱(.*)", self.wb[i])
        if m and m.group(1) == "":
          self.eb.append(self.wb[i])
          i += 1
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
    bnInBlock = False                # no .bn info encountered in this block yet
    while self.wb[i] != ".nf-":

      # special cases: .ce and .rj
      m = re.search(r"\.ce (\d+)", self.wb[i])
      if m:
        count = int(m.group(1))
        i += 1 # skip the .ce
        while count > 0:
          if self.bnPresent and self.wb[i].startswith("⑱"):  # if this line is bn info then just put it in the output as-is
            m = re.match("^⑱.*?⑱(.*)",self.wb[i])
            if m and m.group(1) == "":
              bnInBlock = True
              t.append(self.wb[i])
              i += 1
              continue
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
          if self.bnPresent and self.wb[i].startswith("⑱"):  # if this line is bn info then just put it in the output as-is
            m = re.match("^⑱.*?⑱(.*)",self.wb[i])
            if m and m.group(1) == "":
              bnInBlock = True
              t.append(self.wb[i])
              i += 1
              continue
          xs = "{:>" + str(regBW) + "}"
          t.append(" " * lmar + xs.format(self.wb[i].strip()))
          i += 1
          count -= 1
        continue

      if self.bnPresent and self.wb[i].startswith("⑱"):   #just copy .bn info lines, don't change them at all
        m =re.match("^⑱.*?⑱(.*)", self.wb[i])
        if m and m.group(1) == "":
          bnInBlock = True
          t.append(self.wb[i])
        else:
          t.append(" " * self.regIN + " " * lmar + self.wb[i].rstrip())
      else:
        t.append(" " * self.regIN + " " * lmar + self.wb[i].rstrip())
      i += 1
    self.cl = i + 1 # skip the closing .nf-

    # see if the block has hit the left margin
    need_pad = False
    for line in t:
      if line[0] != " ":
        if bnInBlock and line[0] == "⑱":
          m =re.match("^⑱.*?⑱(.*)", line)
          if not (m and m.group(1) == ""):
            need_pad = True
        else:
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
          if self.bnPresent and self.wb[i].startswith("⑱"):  # if this line is bn info then just put it in the output as-is
            m = re.match("^⑱.*?⑱(.*)",self.wb[i])
            if m and m.group(1) == "":
              self.eb.append(self.wb[i])
              i += 1
              continue
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
          if self.bnPresent and self.wb[i].startswith("⑱"):  # if this line is bn info then just put it in the output as-is
            m = re.match("^⑱.*?⑱(.*)",self.wb[i])
            if m and m.group(1) == "":
              self.eb.append(self.wb[i])
              i += 1
              continue
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
      self.eb.append("{} {}:".format(self.nregs["Footnote"], fnname))
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
        # blank and centered and .bn info lines are not considered
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

    # pull out optional user-specified Epub//Mobi width %
    tw_epub = ""
    if "ew=" in self.wb[self.cl]:
      self.wb[self.cl], tw_epub = self.get_id("ew", self.wb[self.cl])

    # pull out optional user-specified HTML width %
    tw_html = ""
    if "w=" in self.wb[self.cl]:
      self.wb[self.cl], tw_html = self.get_id("w", self.wb[self.cl])

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

      # lines that we don't check: centered or blank (or .bn info)
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

      # .bn info line
      if self.bnPresent and self.wb[self.cl].startswith("⑱"):
        m = re.match("^⑱.*?⑱(.*)",self.wb[self.cl])
        if m and m.group(1) == "":
          self.eb.append(self.wb[self.cl])   # copy the .bn info into the table (deleted much later during postprocessing)
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
    while (self.cl < len(self.wb) - 1) and self.wb[self.cl].endswith("\\"):
      del self.wb[self.cl] # multiple line
    if not self.wb[self.cl].endswith("\\"):
      del self.wb[self.cl] # last or single line
    else:
      self.fatal("source file ends with continued .de command: {}".format(self.wb[self.cl]))

  def doPara(self):
    t = []
    bnt = []
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
      u.append(".RS 1") # after
      self.eb += u
    elif bnInPara:
      bnt.append(s)
      self.eb += bnt     # if only .bn info, append it.
    else:
      self.crash_w_context("Unexpected problem with .bn info",pstart)
    self.cl = pend

  def process(self):
    self.cl = 0
    while self.cl < len(self.wb):
      if "a" in self.debug:
        s = self.wb[self.cl]
        print( self.umap(s) )  # safe print the current line
      if not self.wb[self.cl]: # skip blank lines
        self.cl += 1
        continue

      # don't turn standalone .bn info lines into paragraphs
      if self.bnPresent and self.wb[self.cl].startswith("⑱"):
        m = re.match("^⑱.*?⑱(.*)",self.wb[self.cl])  # look for standalone .bn info
        if m and m.group(1) == "":   # and just append to eb if found
          self.eb.append(self.wb[self.cl])
          self.cl += 1
        continue

      # will hit either a dot directive or wrappable text
      if re.match(r"\.", self.wb[self.cl]):
        self.doDot()
        continue
      self.doPara()

  def run(self): # Text
    self.loadFile(self.srcfile)
    # requested encoding is UTF-8 but file is latin1only
    if self.renc == 'u' and self.latin1only == True and not self.cvgfilter:
      return # do not make UTF-8 text file
    # file is ASCII->Latin_1 but trying to run as UTF-8
    if self.encoding == "latin_1" and self.renc == 'u' and not self.cvgfilter:
      return # do not make UTF-8 text file

    if self.renc == "l":
      print("creating Latin-1 text file")
    if self.renc == "u":
      print("creating UTF-8 text file")

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

  def __init__(self, args, renc):
    Book.__init__(self, args, renc)
    if self.listcvg:
      self.cvglist()
    self.dstfile = re.sub("-src", "", self.srcfile.split('.')[0]) + ".html"
    self.css = self.userCSS()
    self.linkinfo = self.linkMsgs()

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
  # courtesy id check
  #
  # ID and NAME tokens must begin with a letter ([A-Za-z]) and may be followed by any number
  # of letters, digits ([0-9]), hyphens ("-"), underscores ("_"), colons (":"), and periods (".").
  def checkId(self, s):
    if not re.match(r"[A-Za-z][A-Za-z0-9\-_\:\.]*", s):
      self.warn("illegal identifier: {}".format(s))

  # -------------------------------------------------------------------------------------
  # preprocess working buffer (HTML)
  def preprocess(self):

    self.preProcessCommon()

    # protect PPer-supplied internal link information
    # two forms: #number# and #name:id-value#
    # also #RomanNumerals#
    # for either, replace the # symbols with ⑲ so they can be found uniquely later
    # without interference from other HTML markup ppgen may have added
    i = 0
    while i < len(self.wb):
      self.wb[i] = re.sub(r"#(\d+)#", r"⑲\1⑲", self.wb[i])
      self.wb[i] = re.sub(r"#([iIvVxXlLcCdDmM]+)#", r"⑲\1⑲", self.wb[i])
      self.wb[i] = re.sub(r"#(.*?:.*?)#", r"⑲\1⑲", self.wb[i])
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
          self.wb[i] = "⑯{}⑰".format(self.pageno)
        else:
          del self.wb[i]
        continue

      # page number is explicit
      m = re.match(r"\.pn [\"']?(.+?)($|[\"'])", self.wb[i])
      if m:
        self.pageno = m.group(1)
        m = re.match(r"\d+|[iIvVxXlLcCdDmM]+$", self.pageno)
        if not m:
          self.warn("Non-numeric, non-Roman page number {} specified: {}".format(self.pageno, self.wb[i]))
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

      # an arbitrary page "number" set in a heading
      m = re.match(r"\.h.*?pn=[\"']?(.+?)[\"']?($|/s)", self.wb[i])
      if m:
        self.pageno = m.group(1)
        m = re.match(r"\d+|[iIvVxXlLcCdDmM]+$", self.pageno)
        if not m:
          self.warn("Non-numeric, non-Roman page number {} specified: {}".format(self.pageno, self.wb[i]))
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
          # it is possible to hit another pn match before finding a suitable home
          m = re.match(r"⑯(.+)⑰", self.wb[i])  # must be on line by itself
          if m:
            pnum = m.group(1)  # the page number
            del self.wb[i]     # original line gone
            continue           # now go and place it
          # placing the page number
          #  if we see a heading, place it there
          #  if not, look for any line of plain text and insert it
          if re.match(r"\.h[123]", self.wb[i]):
            self.wb[i] += " pn={}".format(pnum)
            found = True
          if self.wb[i].startswith(".il"):
            self.wb[i] += " pn={}".format(pnum)
            found = True
          # don't place on a .bn info line
          if self.bnPresent and self.wb[i].startswith("⑱"):
            m = re.match("^⑱.*?⑱(.*)",self.wb[i])
            if m and m.group(1) == "":
              i += 1
              continue
          # plain text
          if self.wb[i] and not self.wb[i].startswith("."):
            self.wb[i] = "⑯{}⑰".format(pnum) + self.wb[i]
            found = True
          i += 1 # keep looking
      else:       # only increment if first match above failed
        i += 1    # as if it worked we deleted the matching line

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
        s = re.sub("\[(\d+)\]", "", s, 1)
        m = re.search("\[(\d+)\]", s)
      if explicit: # don't support mixing # and explicit in the same line
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

      # skip literal sections
      if ".li" == self.wb[i]:
        while not ".li-" == self.wb[i]:
          i += 1
        i += 1
        continue


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
          self.wb[i] = re.sub("<target id='(.*?)'>", "<a id='{0}' name='{0}'></a>".format(m.group(1)), self.wb[i], 1)
          self.checkId(m.group(1))
          m = re.search("<target id='(.*?)'>", self.wb[i])
        m = re.search("<target id=\"(.*?)\">", self.wb[i])
        while m:
          self.wb[i] = re.sub("<target id=\"(.*?)\">", "<a id='{0}' name='{}'></a>".format(m.group(1)), self.wb[i], 1)
          self.checkId(m.group(1))
          m = re.search("<target id=\"(.*?)\">", self.wb[i])
        m = re.search("<target id=(.*?)>", self.wb[i])
        while m:
          self.wb[i] = re.sub("<target id=(.*?)>", "<a id='{0}' name='{0}'></a>".format(m.group(1)), self.wb[i], 1)
          self.checkId(m.group(1))
          m = re.search("<target id=(.*?)>", self.wb[i])
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
            tmpline = self.wb[i]
            if self.wb[i].startswith(".nf "):
              self.crash_w_context("nested no-fill block:", i)
            # ignore .bn lines; just pass them through
            if self.bnPresent and self.wb[i].startswith("⑱"):
              m = re.match("^⑱.*?⑱(.*)",self.wb[i])
              if m and m.group(1) == "":
                i += 1
                continue
            # find all tags on this line; ignore <a and </a tags completely for this purpose
            t = re.findall("<\/?[^a>]*>", self.wb[i])
            sstart = "" # what to prepend to the line
            for s in tagstack: # build the start string
              sstart += s
            self.wb[i] = sstart + self.wb[i] # rewrite the line with new start
            for s in t: # we may have more tags on this line
              if not s.startswith("</"): # it is of form <..> an opening tag
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
              if closetag.startswith("</c"): # anything that had arguments closes without them
                closetag = "</c>" # colors
              if closetag.startswith("</fs"):
                closetag = "</fs>" # font size
              if closetag.startswith("</lang"):
                closetag = "</lang>" # language
              send += closetag
            self.wb[i] = self.wb[i] + send
            i += 1
          if len(tagstack):
            self.warn("Unclosed tags in .nf block: {}".format(tagstack))
            if 'd' in self.debug:
              self.crash_w_context("Error context:", i)
      i += 1

    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    # <lang> tags processed in HTML.
    # <lang="fr">merci</lang>
    # <span lang="fr xml:lang="fr">merci</span>
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
          self.wb[i] = re.sub(m.group(0), "ᒪ'{}'".format(langspec), self.wb[i], 1)
          # self.wb[i] = re.sub(m.group(0), "<span lang=\"{0}\" xml:lang=\"{0}\">".format(langspec), self.wb[i], 1)
          m = re.search(r"<lang=[\"']?([^\"'>]+)[\"']?>",self.wb[i])
        if "lang=" in self.wb[i]:
          self.fatal("incorrect lang markup: {}".format(self.wb[i]))
        self.wb[i] = re.sub(r"<\/lang>", "ᒧ",self.wb[i])
        i += 1


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

    inNF = False
    for i, line in enumerate(self.wb):

      # if everything inside <sc>...</sc> markup is uppercase, then
      # use font-size:smaller, else use font-variant:small-caps

      if self.wb[i].startswith(".nf "):
        inNF = True
      elif self.wb[i].startswith(".nf-"):
        inNF = False
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
          # warn about all lower case, but not within .nf as
          # we will have replicated the <sc> tags that cross lines
          # of the .nf block, which could leave some all lower-case
          # line alone within the <sc> </sc>, but it's not an error
          if not inNF and scstring == scstring.lower():
            self.warn("all lower case inside small-caps markup: {}".format(self.wb[i]))
          if scstring == scstring.upper(): # all upper case
            use_class = "fss"
        else:
          self.warn("Unexpected problem interpreting <sc> string, assuming mixed-case.\nLine number:{}\nCurrent line: {}\nCurrent string:{}".format(i, self.wb[i],stmp))
        if use_class == "sc":
          self.wb[i] = re.sub("<sc>", "<span class='sc'>", self.wb[i], 1)
          self.css.addcss("[1200] .sc { font-variant:small-caps; }")
        if use_class == "fss":
          self.wb[i] = re.sub("<sc>", "<span class='fss'>", self.wb[i], 1)
          self.css.addcss("[1200] .fss { font-size:75%; }")
        self.wb[i] = re.sub("<\/sc>", "</span>", self.wb[i], 1) # since we had a <sc> replace 1 </sc> if present on this line
        m = re.search("<sc>", self.wb[i]) # look for another opening small cap tag

      # common closing, may be on separate line
      self.wb[i] = re.sub("<\/sc>", "</span>", self.wb[i])

      m = re.search("<l>", self.wb[i])
      if m:
        self.css.addcss("[1201] .large { font-size:large; }")
      self.wb[i] = re.sub("<l>", "<span class='large'>", self.wb[i])
      self.wb[i] = re.sub("<\/l>", "</span>", self.wb[i])

      m = re.search("<xl>", self.wb[i])
      if m:
        self.css.addcss("[1202] .xlarge { font-size:x-large; }")
      self.wb[i] = re.sub("<xl>", "<span class='xlarge'>", self.wb[i])
      self.wb[i] = re.sub("<\/xl>", "</span>", self.wb[i])

      m = re.search("<xxl>", self.wb[i])
      if m:
        self.css.addcss("[1202] .xxlarge { font-size:xx-large; }")
      self.wb[i] = re.sub("<xxl>", "<span class='xxlarge'>", self.wb[i])
      self.wb[i] = re.sub("<\/xxl>", "</span>", self.wb[i])

      m = re.search("<s>", self.wb[i])
      if m:
        self.css.addcss("[1203] .small { font-size:small; }")
      self.wb[i] = re.sub("<s>", "<span class='small'>", self.wb[i])
      self.wb[i] = re.sub("<\/s>", "</span>", self.wb[i])

      m = re.search("<xs>", self.wb[i])
      if m:
        self.css.addcss("[1204] .xsmall { font-size:x-small; }")
      self.wb[i] = re.sub("<xs>", "<span class='xsmall'>", self.wb[i])
      self.wb[i] = re.sub("<\/xs>", "</span>", self.wb[i])

      m = re.search("<xxs>", self.wb[i])
      if m:
        self.css.addcss("[1205] .xxsmall { font-size:xx-small; }")
      self.wb[i] = re.sub("<xxs>", "<span class='xxsmall'>", self.wb[i])
      self.wb[i] = re.sub("<\/xxs>", "</span>", self.wb[i])

      m = re.search("<u>", self.wb[i])
      if m:
        self.css.addcss("[1205] .under { text-decoration:underline; }")
      self.wb[i] = re.sub("<u>", "<span class='under'>", self.wb[i])
      self.wb[i] = re.sub("<\/u>", "</span>", self.wb[i])

      m = re.search(r"<c=[\"']?(.*?)[\"']?>", self.wb[i])
      while m:
        thecolor = m.group(1)
        safename = re.sub("#","", thecolor)
        self.css.addcss("[1209] .color_{0} {{ color:{1}; }}".format(safename,thecolor))
        self.wb[i] = re.sub("<c.*?>", "<span class='color_{0}'>".format(safename), self.wb[i], 1)
        m = re.search(r"<c=[\"']?(.*?)[\"']?>", self.wb[i])
      self.wb[i] = re.sub("<\/c>", "</span>", self.wb[i],1)

      # <g> is now a stylized em in HTML
      # using a @media handheld, in epub/mobi it is italicized, with normal letter spacing
      m = re.search(r"<g>", self.wb[i])
      if m:
        self.wb[i] = re.sub(r"<g>", "<em class='gesperrt'>", self.wb[i])
        self.css.addcss("[1378] em.gesperrt { font-style: normal; letter-spacing: 0.2em; margin-right: -0.2em; }")
        self.css.addcss("[1379] @media handheld { em.gesperrt { font-style: italic; letter-spacing: 0; margin-right: 0;}}")
      self.wb[i] = re.sub("<\/g>", "</em>", self.wb[i],1)

      m = re.search(r"<fs=[\"']?(.*?)[\"']?>", self.wb[i])
      while m:
        self.wb[i] = re.sub(m.group(0), "<span style='font-size:{}'>".format(m.group(1)), self.wb[i], 1)
        m = re.search(r"<fs=[\"']?(.*?)[\"']?>", self.wb[i])
      self.wb[i] = re.sub("<\/fs>", "</span>", self.wb[i])

  # -------------------------------------------------------------------------------------
  # restore tokens in HTML text

  def htmlTokenRestore(self, text):
    text = re.sub("ⓓ", ".", text)
    text = re.sub("①", "{", text)
    text = re.sub("②", "}", text)
    text = re.sub("③", "[", text)
    text = re.sub("④", "]", text)
    text = re.sub("⑤", "&lt;", text)
    text = re.sub("⑳", "&gt;", text)
    # text space replacement
    text = re.sub("ⓢ", "&nbsp;", text) # non-breaking space
    text = re.sub("ⓣ", "&#8203;", text) # zero space
    text = re.sub("ⓤ", "&thinsp;", text) # thin space
    text = re.sub("ⓥ", "&#8196;", text) # thick space
    # ampersand
    text = re.sub("Ⓩ", "&amp;", text)
    # protected
    text = re.sub("⑪", "<", text)
    text = re.sub("⑫", ">", text)
    text = re.sub("⑬", "[", text)
    text = re.sub("⑭", "]", text)
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
    # also allow Roman numbered pages
    # which at this point are actually using ⑲ instead of the # signs
    for i in range(len(self.wb)):

      m = re.search(r"⑲(\d+?)⑲", self.wb[i])
      while m: # page number reference
        s = "<a href='⫉Page_{0}'>{0}</a>".format(m.group(1)) # link to it
        self.wb[i] = re.sub(r"⑲(\d+?)⑲", s, self.wb[i], 1)
        m = re.search(r"⑲(\d+?)⑲", self.wb[i])

      m = re.search(r"⑲([iIvVxXlLcCdDmM]+)⑲", self.wb[i]) # Roman numeral reference
      while m:
        s = "<a href='⫉Page_{0}'>{0}</a>".format(m.group(1)) # link to that
        self.wb[i] = re.sub(r"⑲[iIvVxXlLcCdDmM]+⑲", s, self.wb[i], 1)
        m = re.search(r"⑲([iIvVxXlLcCdDmM]+)⑲", self.wb[i])

      m = re.search(r"⑲(.*?):(.*?)⑲", self.wb[i]) # named reference
      while m:
        s = "<a href='⫉{}'>{}</a>".format(m.group(2), m.group(1)) # link to that
        self.checkId(m.group(2))
        self.wb[i] = re.sub(r"⑲(.*?):(.*?)⑲", s, self.wb[i], 1)
        m = re.search(r"⑲(.*?):(.*?)⑲", self.wb[i])

      self.wb[i] = re.sub("⫉", '#', self.wb[i])

    for i, line in enumerate(self.wb):
      self.wb[i] = re.sub("⑥", ":", self.wb[i])

    for i, line in enumerate(self.wb):
      # lang specifications
      m = re.search(r"ᒪ'(.+?)'", self.wb[i])
      while m:
        self.wb[i] = re.sub(m.group(0), "<span lang=\"{0}\" xml:lang=\"{0}\">".format(m.group(1)), self.wb[i], 1)
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
        print( "internal error:\n  cannot write line: {:s}".format(self.umap(t)) )
        self.fatal("exiting")
    f1.close()

    # save GG .bin file if needed
    if self.bnPresent:
      fnb = fn + ".bin"
      f1 = codecs.open(fnb, "w", "ISO-8859-1")
      for index,t in enumerate(self.bb):
        f1.write("{:s}\r\n".format(t))
      f1.close()

  # ----- makeHTML method group -----

  def doHeader(self):

    # common CSS

    if self.pnshow:
      self.css.addcss("[1100] body { margin-left:8%;margin-right:10%; }")
      self.css.addcss("[1105] .pageno { right:1%;font-size:x-small;background-color:inherit;color:" + self.nregs["pnc"] + ";")
      self.css.addcss("[1106]         text-indent:0em;text-align:right;position:absolute;")
      self.css.addcss("[1107]         border:1px solid " + self.nregs["pnc"] + ";padding:1px 3px;font-style:normal;")
      self.css.addcss("[1108]         font-variant:normal;font-weight:normal;text-decoration:none; }")
      self.css.addcss("[1109] .pageno:after { color: " + self.nregs["pnc"] + "; content: attr(title); }")  # new 3.24M
    else:
      self.css.addcss("[1100] body { margin-left:8%;margin-right:8%; }")

    self.css.addcss("[1170] p { text-indent:0;margin-top:0.5em;margin-bottom:0.5em;text-align:justify; }") # para style

    # HTML header
    t = []
    t.append("<!DOCTYPE html PUBLIC \"-//W3C//DTD XHTML 1.0 Strict//EN\"")
    t.append("    \"http://www.w3.org/TR/xhtml1/DTD/xhtml1-strict.dtd\">")
    t.append("<html xmlns=\"http://www.w3.org/1999/xhtml\" xml:lang=\"" + self.nregs["lang"] + "\" lang=\"" + self.nregs["lang"] + "\">") # include base language in header
    t.append("  <head>")

    if self.encoding == "utf_8":
      t.append("    <meta http-equiv=\"Content-Type\" content=\"text/html;charset=UTF-8\" />")
    if self.encoding == "latin_1":
      t.append("    <meta http-equiv=\"Content-Type\" content=\"text/html;charset=ISO-8859-1\" />")

    if self.dtitle != "":
      t.append("    <title>{}</title>".format(self.htmlTokenRestore(self.dtitle)))
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

  #----------------------------------------------------
  # process saved search/replace strings, if any
  # but only if our output format matches something in the saved "which" value
  def doHTMLSr(self):
    blobbed = False
    for i in range(len(self.srw)):
      if ('h' in self.srw[i]):       # if this one applies to HTML
        k = 0
        l = 0
        ll = 0
        if "\\n" in self.srs[i]: # did user use a regex containing \n ? If so, process all lines in one blob
          if not blobbed:
            text = '\n'.join(self.wb) # form lines into a blob of text
            blobbed = True
          try:
            m = re.search(self.srs[i], text)   # search for current search string
          except:
            if 'd' in self.debug:
              traceback.print_exc()
              self.fatal("Above error occurred searching for {} in complete text blob".format(self.srs[i]))
            else:
              self.fatal("Error occurred searching for {} in complete text blob".format(self.srs[i]))
          if m:                                             # if found
            if 'r' in self.debug:
              print("{} found in complete text blob".format(self.srs[i]))
            try:
              text, l = re.subn(self.srs[i], self.srr[i], text) # replace all occurrences in the blob of text
              ll += l
            except:
              if 'd' in self.debug:
                traceback.print_exc()
                self.fatal("Above error occurred replacing:{}\n  with {}\n  in complete text blob".format(self.srs[i], self.srr[i]))
              else:
                self.fatal("Error occurred replacing:{}\n  with {}\n  in complete text blob".format(self.srs[i], self.srr[i]))
            if 'r' in self.debug:
              print("Replaced with: {}".format(self.srr[i]))
          print("Search string {}:{} matched and replaced {} times in complete text blob.".format(i+1, self.srs[i], ll))

        else:
          if blobbed:
            self.wb = text.splitlines() # restore individual lines from the blob
            blobbed = False
          for j in range(len(self.wb)):
            try:
              m = re.search(self.srs[i], self.wb[j])               # search for current search string
            except:
              if 'd' in self.debug:
                traceback.print_exc()
                self.fatal("Above error occurred searching for\n  {}\n in: {}".format(self.srs[i], self.wb[j]))
              else:
                self.fatal("Error occurred searching for\n  {}\n in: {}".format(self.srs[i], self.wb[j]))
            if m:                                             # if found
              k += 1
              if 'r' in self.debug:
                print("{} found in: {}".format(self.srs[i], self.wb[j]))
              try:
                self.wb[j], l = re.subn(self.srs[i], self.srr[i], self.wb[j])      # replace all occurrences in the line
                ll += l
              except:
                if 'd' in self.debug:
                  traceback.print_exc()
                  self.fatal("Above error occurred replacing:{}\n  with {}\n  in: {}".format(self.srs[i], self.srr[i], self.wb[j]))
                else:
                  self.fatal("Error occurred replacing:{}\n  with {}\n  in: {}".format(self.srs[i], self.srr[i], self.wb[j]))
              if 'r' in self.debug:
                print("Replaced: {}".format(self.wb[j]))
          print("Search string {}:{} matched in {} lines, replaced {} times.".format(i+1, self.srs[i], k, ll))

    if blobbed:
      self.wb = text.splitlines() # restore individual lines from the blob
      blobbed = False

  # ----- process method group -----

  # .li literal (pass-through)
  def doLit(self):
    if self.pvs > 0: # handle any pending vertical space before the .li
      self.wb[self.cl] = "<div style=\"margin-top:{}em;\"></div>".format(self.pvs)
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
    hcss = "margin-top:1em; "  # default
    if self.pvs > 0:
      hcss = " margin-top:{}em; ".format(self.pvs)
      self.pvs = 0

    self.css.addcss("[1465] div.pbb { page-break-before:always; }")
    self.css.addcss("[1466] hr.pb { border:none;border-bottom:1px solid; margin-bottom:1em; }")
    self.css.addcss("[1467] @media handheld { hr.pb { display:none; }}")
    self.wb[self.cl:self.cl+1] = ["<div class='pbb'></div>", "<hr class='pb' style='{}' />".format(hcss)]
    self.cl += 2

  # extract any "class=" argument from string s
  def getClass(self, s):
    if "class='" in s:
      m = re.search(r"class='(.*?)'", s)
      if m:
        self.wb[self.cl] = re.sub(m.group(0), "", self.wb[self.cl])
        return m.group(1)
    if "class=\"" in s:
      m = re.search(r"class=\"(.*?)\"", s)
      if m:
        self.wb[self.cl] = re.sub(m.group(0), "", self.wb[self.cl])
        return m.group(1)
    return ""

  # doDiv (HTML)
  def doDiv(self):
    self.wb[self.cl:self.cl+1] = ["<div class='{}'>".format(self.getClass(self.wb[self.cl])), ""]
    j = self.cl
    while j < len(self.wb) and self.wb[j] != ".dv-":
      j += 1
    if j < len(self.wb):
      self.wb[j:j+1] = ["", "</div>"]
    else:
      self.crash_w_context("unclosed .dv directive.",self.cl)

  # .hr horizontal rule
  def doHr(self):
    # if there is a pending vertical space, include it in style
    hcss = ""
    if self.pvs > 0:
      hcss = " margin-top:{}em; ".format(self.pvs)
      self.pvs = 0
    hrpct = 100
    m = re.match(r"\.hr (\d+)%", self.wb[self.cl])
    if m:
      hrpct = int(m.group(1))
    if hrpct == 100:
      self.wb[self.cl] = "<hr style='border:none;border-bottom:1px solid;margin:1em auto; {}' />".format(hcss)
    else:
      lmarp = (100 - hrpct)//2
      rmarp = 100 - hrpct - lmarp
      self.wb[self.cl] = "<hr style='border:none;border-bottom:1px solid;margin-top:1em;margin-bottom:1em; margin-left:{}%; width:{}%; margin-right:{}%; {}' />".format(lmarp,hrpct,rmarp, hcss)
    self.cl += 1

  # .tb thought break
  # thought breaks fixed at 35% thin line.
  def doTbreak(self):
    # if there is a pending vertical space, include it in style
    hcss = ""
    if self.pvs > 0:
      hcss = " margin-top:{}em; ".format(self.pvs)
      self.pvs = 0
      self.wb[self.cl] = "<hr style='border:none;border-bottom:1px solid; margin-bottom:0.8em; margin-left:35%; margin-right:35%; width:30%; {}' />".format(hcss) # for IE
    else:
      self.wb[self.cl] = "<hr style='border:none;border-bottom:1px solid; margin-top:0.8em;margin-bottom:0.8em;margin-left:35%; margin-right:35%; width:30%;' />" # for IE
    self.cl += 1

  # .de CSS definition
  # one liners: .de h1 { color:red; }
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


  # h1
  def doH1(self):
    pnum = ""
    id = ""
    rend = "" # default no rend
    hcss = ""
    align = "c" # default to centered heading

    self.css.addcss("[1100] h1 { text-align:center;font-weight:normal;font-size:1.4em; }")

    m = re.match(r"\.h1 (.*)", self.wb[self.cl])
    if m: # modifier
      rend = m.group(1)

      if "pn=" in rend:
        rend, pnum = self.get_id("pn", rend)

      if "id=" in rend:
        rend, id = self.get_id("id", rend)

      if "align=" in rend:
        rend, align = self.get_id("align", rend)

    if align == "l":
      hcss += "text-align:left;"
    elif align == "r":
      hcss += "text-align:right;"
    elif align != "c":
      self.crash_w_context("Incorrect align= value (not c, l, or r):", self.cl)

    if "nobreak" in rend:
      hcss += "page-break-before:auto;"
    else:
      hcss += "page-break-before:always;"

    if self.pvs > 0:
      hcss += "margin-top:{}em;".format(self.pvs)
      self.pvs = 0
    else: # default 1 before, 1 after
      hcss += "margin-top:1em;"
    self.pvs = 1

    del self.wb[self.cl] # the .h line

    # if we have .bn info after the .h and before the header join them together
    if self.bnPresent and self.wb[self.cl].startswith("⑱"):
      m = re.match("^⑱.*?⑱(.*)",self.wb[self.cl])
      if m and m.group(1) == "":
        i = self.cl
        if i < len(self.wb) -1:
          self.wb[i] = self.wb[i] + self.wb[i+1]
          del self.wb[i+1]
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
    hcss = ""
    rend = "" # default no rend
    align = "c" # default to centered heading

    self.css.addcss("[1100] h2 { text-align:center;font-weight:normal;font-size:1.2em; }")

    m = re.match(r"\.h2 (.*)", self.wb[self.cl])
    if m: # modifier
      rend = m.group(1)

      if "pn=" in rend:
        rend, pnum = self.get_id("pn", rend)

      if "id=" in rend:
        rend, id = self.get_id("id", rend)

      if "align=" in rend:
        rend, align = self.get_id("align", rend)

    if align == "l":
      hcss += "text-align:left;"
    elif align == "r":
      hcss += "text-align:right;"
    elif align != "c":
      self.crash_w_context("Incorrect align= value (not c, l, or r):", self.cl)

    if "nobreak" in rend:
      hcss += "page-break-before:auto;"
    else:
      hcss += "page-break-before:always;"

    if self.pvs > 0:
      hcss += "margin-top:{}em;".format(self.pvs)
      self.pvs = 0
    else: # default 4 before, 2 after
      hcss += "margin-top:4em;"
    self.pvs = 2

    del self.wb[self.cl] # the .h line

    # if we have .bn info after the .h and before the header join them together
    if self.bnPresent and self.wb[self.cl].startswith("⑱"):
      m = re.match("^⑱.*?⑱(.*)",self.wb[self.cl])
      if m and m.group(1) == "":
        i = self.cl
        if i < len(self.wb) -1:
          self.wb[i] = self.wb[i] + self.wb[i+1]
          del self.wb[i+1]
    s = re.sub(r"\|\|", "<br /> <br />", self.wb[self.cl]) # required for epub
    s = re.sub("\|", "<br />", s)
    t = []

    # new in 1.79
    # I always want a div. If it's not a no-break, give it class='chapter'
    if not "nobreak" in rend:
      t.append("<div class='chapter'></div>") # will force file break
      self.css.addcss("[1576] .chapter { clear:both; }")
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

    self.wb[self.cl:self.cl+1] = t
    self.cl += len(t)

  # h3
  def doH3(self):
    pnum = ""
    id = ""
    hcss = ""
    rend = "" # default no rend
    align = "c" # default to centered heading

    self.css.addcss("[1100] h3 { text-align:center;font-weight:normal;font-size:1.2em; }")

    m = re.match(r"\.h3 (.*)", self.wb[self.cl])
    if m: # modifier
      rend = m.group(1)

      if "pn=" in rend:
        rend, pnum = self.get_id("pn", rend)

      if "id=" in rend:
        rend, id = self.get_id("id", rend)

      if "align=" in rend:
        rend, align = self.get_id("align", rend)

    if align == "l":
      hcss += "text-align:left;"
    elif align == "r":
      hcss += "text-align:right;"
    elif align != "c":
      self.crash_w_context("Incorrect align= value (not c, l, or r):", self.cl)

    if "nobreak" in rend: # default to "break" in .h3 (seems odd to me, change this?)
      hcss += "page-break-before:auto;"
    else:
      hcss += "page-break-before:always;"

    if self.pvs > 0:
      hcss += "margin-top:{}em;".format(self.pvs)
      self.pvs = 0
    else: # default 2 before, 1 after
      hcss += "margin-top:2em;"
    self.pvs = 1

    del self.wb[self.cl] # the .h line

    # if we have .bn info after the .h and before the header join them together
    if self.bnPresent and self.wb[self.cl].startswith("⑱"):
      m = re.match("^⑱.*?⑱(.*)",self.wb[self.cl])
      if m and m.group(1) == "":
        i = self.cl
        if i < len(self.wb) -1:
          self.wb[i] = self.wb[i] + self.wb[i+1]
          del self.wb[i+1]
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

  # h4
  def doH4(self):
    pnum = ""
    id = ""
    hcss = ""
    rend = "nobreak"
    align = "c" # default to centered heading

    self.css.addcss("[1100] h4 { text-align:center;font-weight:normal;font-size:1.0em; }")

    m = re.match(r"\.h4( .*)", self.wb[self.cl])
    if m: # modifier
      rend += m.group(1) # add user-supplied values to default rend value of nobreak

      if "pn=" in rend:
        rend, pnum = self.get_id("pn", rend)

      if "id=" in rend:
        rend, id = self.get_id("id", rend)

      if "align=" in rend:
        rend, align = self.get_id("align", rend)

    if align == "l":
      hcss += "text-align:left;"
    elif align == "r":
      hcss += "text-align:right;"
    elif align != "c":
      self.crash_w_context("Incorrect align= value (not c, l, or r):", self.cl)

    if " break" in rend: # .h4/5/6 default to nobreak, so look for break (preceded by space) that user may have supplied
      hcss += "page-break-before:always;"
    else:
      hcss += "page-break-before:auto;"

    if self.pvs > 0:
      hcss += "margin-top:{}em;".format(self.pvs)
      self.pvs = 0
    else: # default 1 before, 1 after
      hcss += "margin-top:1em;"
    self.pvs = 1

    del self.wb[self.cl] # the .h line

    # if we have .bn info after the .h and before the header join them together
    if self.bnPresent and self.wb[self.cl].startswith("⑱"):
      m = re.match("^⑱.*?⑱(.*)",self.wb[self.cl])
      if m and m.group(1) == "":
        i = self.cl
        if i < len(self.wb) -1:
          self.wb[i] = self.wb[i] + self.wb[i+1]
          del self.wb[i+1]
    s = re.sub(r"\|\|", "<br /> <br />", self.wb[self.cl]) # required for epub
    s = re.sub("\|", "<br />", s)
    t = []

    if pnum != "":
      t.append("<div>")
      if self.pnshow:
        # t.append("  <span class='pagenum'><a name='Page_{0}' id='Page_{0}'>{0}</a></span>".format(pnum))
        t.append("  <span class='pageno' title='{0}' id='Page_{0}' ></span>".format(pnum)) # new 3.24M
      elif self.pnlink:
        t.append("  <a name='Page_{0}' id='Page_{0}'></a>".format(pnum))
      t.append("</div>")
    if id != "":
      t.append("<h4 id='{}' style='{}'>{}</h4>".format(id, hcss, s))
    else:
      t.append("<h4 style='{}'>{}</h4>".format(hcss, s))

    self.wb[self.cl:self.cl+1] = t
    self.cl += len(t)

  # h5
  def doH5(self):
    pnum = ""
    id = ""
    hcss = ""
    rend = "nobreak"
    align = "c" # default to centered heading

    self.css.addcss("[1100] h5 { text-align:center;font-weight:normal;font-size:1.0em; }")

    m = re.match(r"\.h5( .*)", self.wb[self.cl])
    if m: # modifier
      rend += m.group(1) # add user-supplied values to default rend value of nobreak

      if "pn=" in rend:
        rend, pnum = self.get_id("pn", rend)

      if "id=" in rend:
        rend, id = self.get_id("id", rend)

      if "align=" in rend:
        rend, align = self.get_id("align", rend)

    if align == "l":
      hcss += "text-align:left;"
    elif align == "r":
      hcss += "text-align:right;"
    elif align != "c":
      self.crash_w_context("Incorrect align= value (not c, l, or r):", self.cl)

    if " break" in rend: # .h4/5/6 default to nobreak, so look for break (preceded by space) that user may have supplied
      hcss += "page-break-before:always;"
    else:
      hcss += "page-break-before:auto;"

    if self.pvs > 0:
      hcss += "margin-top:{}em;".format(self.pvs)
      self.pvs = 0
    else: # default 1 before, 1 after
      hcss += "margin-top:1em;"
    self.pvs = 1

    del self.wb[self.cl] # the .h line

    # if we have .bn info after the .h and before the header join them together
    if self.bnPresent and self.wb[self.cl].startswith("⑱"):
      m = re.match("^⑱.*?⑱(.*)",self.wb[self.cl])
      if m and m.group(1) == "":
        i = self.cl
        if i < len(self.wb) -1:
          self.wb[i] = self.wb[i] + self.wb[i+1]
          del self.wb[i+1]
    s = re.sub(r"\|\|", "<br /> <br />", self.wb[self.cl]) # required for epub
    s = re.sub("\|", "<br />", s)
    t = []

    if pnum != "":
      t.append("<div>")
      if self.pnshow:
        # t.append("  <span class='pagenum'><a name='Page_{0}' id='Page_{0}'>{0}</a></span>".format(pnum))
        t.append("  <span class='pageno' title='{0}' id='Page_{0}' ></span>".format(pnum)) # new 3.24M
      elif self.pnlink:
        t.append("  <a name='Page_{0}' id='Page_{0}'></a>".format(pnum))
      t.append("</div>")
    if id != "":
      t.append("<h5 id='{}' style='{}'>{}</h5>".format(id, hcss, s))
    else:
      t.append("<h5 style='{}'>{}</h5>".format(hcss, s))

    self.wb[self.cl:self.cl+1] = t
    self.cl += len(t)

  # h6
  def doH6(self):
    pnum = ""
    id = ""
    hcss = ""
    rend = "nobreak"
    align = "c" # default to centered heading

    self.css.addcss("[1100] h6 { text-align:center;font-weight:normal;font-size:1.0em; }")

    m = re.match(r"\.h6( .*)", self.wb[self.cl])
    if m: # modifier
      rend += m.group(1) # add user-supplied values to default rend value of nobreak

      if "pn=" in rend:
        rend, pnum = self.get_id("pn", rend)

      if "id=" in rend:
        rend, id = self.get_id("id", rend)

      if "align=" in rend:
        rend, align = self.get_id("align", rend)

    if align == "l":
      hcss += "text-align:left;"
    elif align == "r":
      hcss += "text-align:right;"
    elif align != "c":
      self.crash_w_context("Incorrect align= value (not c, l, or r):", self.cl)

    if " break" in rend: # .h4/5/6 default to nobreak, so look for break (preceded by space) that user may have supplied
      hcss += "page-break-before:always;"
    else:
      hcss += "page-break-before:auto;"

    if self.pvs > 0:
      hcss += "margin-top:{}em;".format(self.pvs)
      self.pvs = 0
    else: # default 1 before, 1 after
      hcss += "margin-top:1em;"
    self.pvs = 1

    del self.wb[self.cl] # the .h line

    # if we have .bn info after the .h and before the header join them together
    if self.bnPresent and self.wb[self.cl].startswith("⑱"):
      m = re.match("^⑱.*?⑱(.*)",self.wb[self.cl])
      if m and m.group(1) == "":
        i = self.cl
        if i < len(self.wb) -1:
          self.wb[i] = self.wb[i] + self.wb[i+1]
          del self.wb[i+1]
    s = re.sub(r"\|\|", "<br /> <br />", self.wb[self.cl]) # required for epub
    s = re.sub("\|", "<br />", s)
    t = []

    if pnum != "":
      t.append("<div>")
      if self.pnshow:
        # t.append("  <span class='pagenum'><a name='Page_{0}' id='Page_{0}'>{0}</a></span>".format(pnum))
        t.append("  <span class='pageno' title='{0}' id='Page_{0}' ></span>".format(pnum)) # new 3.24M
      elif self.pnlink:
        t.append("  <a name='Page_{0}' id='Page_{0}'></a>".format(pnum))
      t.append("</div>")
    if id != "":
      t.append("<h6 id='{}' style='{}'>{}</h6>".format(id, hcss, s))
    else:
      t.append("<h6 style='{}'>{}</h6>".format(hcss, s))

    self.wb[self.cl:self.cl+1] = t
    self.cl += len(t)

  # .sp n
  # if a space is encountered. for HTML drop it to the next
  # displayable text and generate a top margin.
  def doSpace(self):
    m = re.match(r"\.sp (\d+)", self.wb[self.cl])
    if m:
      self.pvs = max(int(m.group(1)), self.pvs)  # honor if larger than current pvs
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

  def doIllo(self):

    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    # check that file exists
    #
    def checkIllo(fname): # assure that fn exists in images folder
      if " " in fname:
        self.warn("cannot have spaces in illustration filenames.")
      if re.search("[A-Z]", fname):
        self.warn("illustration filenames must be lower case.")
      fullname = os.path.join(os.path.dirname(self.srcfile),"images",fname)
      if not os.path.isfile(fullname):
        self.warn("file {} not in images folder".format(fullname))

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
      checkIllo(ifn)
      ia["ifn"] = ifn

      # link to alternate (larger) image
      link = ""
      if "link=" in s:
        s, link = self.get_id("link", s)
        checkIllo(link)
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
      if pageno:
        m = re.match(r"\d+|[iIvVxXlLcCdDmM]+$", pageno)
        if not m:
          self.warn("Non-numeric, non-Roman page number {} specified: {}".format(pageno, s0))

      # caption model (ignored in HTML)
      if "cm=" in s:
        s, cm = self.get_id("cm",s)

      # no "=" should remain in .il string
      if "=" in s:
        s = re.sub("\.il", "", s).strip()
        self.warn("unprocessed value in illustration: {}".format(s))
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
      self.css.addcss("[1600] .figcenter { clear:both; max-width:100%; margin:2em auto; text-align:center; }")
      if caption_present:
          self.css.addcss("[1601] div.figcenter p { text-align:center; text-indent:0; }")
      self.css.addcss("[1608] .figcenter img { max-width:100%; height:auto; }")

    if ia["align"] == "l":
      self.css.addcss("[1600] .figleft { clear:left; float:left; max-width:100%; margin:0.5em 1em 1em 0; text-align: left;}")
      if caption_present:
          self.css.addcss("[1601] div.figleft p { text-align:center; text-indent:0; }")
      self.css.addcss("[1602] @media handheld { .figleft { float:left; }}")
      self.css.addcss("[1608] .figleft img { max-width:100%; height:auto; }")

    if ia["align"] == "r":
      self.css.addcss("[1600] .figright { clear:right; float:right; max-width:100%; margin:0.5em 0 1em 1em; text-align: right;}")
      if caption_present:
          self.css.addcss("[1601] div.figright p { text-align:center; text-indent:0; }")
      self.css.addcss("[1602] @media handheld { .figright { float:right; }}")
      self.css.addcss("[1608] .figright img { max-width:100%; height:auto; }")


    # make CSS names from igc counter
    idn = "id{:03d}".format(self.igc)
    ign = "ig{:03d}".format(self.igc)
    icn = "ic{:03d}".format(self.igc)
    self.igc += 1

    # set the illustration width
    self.css.addcss("[1610] .{} {{ width:{}; }}".format(idn, ia["iw"])) # the HTML illustration width

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
      self.css.addcss("[1610] @media handheld {{ .{} {{ margin-left:{}%; width:{}; }}}}".format(idn, my_lmar, ia["ew"]))
    else:  # floated l or right
     self.css.addcss("[1610] @media handheld {{ .{} {{ width:{}; }}}}".format(idn, ia["ew"]))

    # if user has set caption width (in percent) we use that for both HTML and epub.
    # If user hasn’t specified it, we use the width of the image in a browser or
    # 80% in epub using a @media handheld because we cannot rely on max-width on these devices
    #
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
        self.css.addcss("[1611] .{} {{ width:{}%; margin-left:{}%; margin-right:{}%; }} ".format(icn, ocw, oml, omr))
      else:
        self.css.addcss("[1611] .{} {{ width:100%; }} ".format(icn, ia["iw"]))

      if ia["cj"] != "":
        if ia["cj"] == 'l':
          self.css.addcss("[1613] div.{} p {{ text-align:left; }} ".format(icn))
        elif ia["cj"] == 'r':
          self.css.addcss("[1613] div.{} p {{ text-align:right; }} ".format(icn))
        elif ia["cj"] == 'c':
          self.css.addcss("[1613] div.{} p {{ text-align:center; }} ".format(icn))
        elif ia["cj"] == 'f':
          self.css.addcss("[1613] div.{} p {{ text-align:justify; }} ".format(icn))

    self.css.addcss("[1614] .{} {{ width:100%; }} ".format(ign, ia["iw"]))

    # create replacement stanza for illustration
    u = []

    if ia["align"] == "c":  # with fix for missing id= problem
      u.append("<div {} class='figcenter {}'>".format(ia["id"], idn))
    if ia["align"] == "l":
      u.append("<div {} class='figleft {}'>".format(ia["id"], idn))
    if ia["align"] == "r":
      u.append("<div {} class='figright {}'>".format(ia["id"], idn))

    if ia["pageno"] != "":
      u.append("<span class='pageno' title='{0}' id='Page_{0}' ></span>".format(ia["pageno"]))
      ia["pageno"] = ""

    # 16-Apr-2014: placed link in div
    if ia["link"] != "": # link to larger image specified in markup
      u.append("<a href='images/{}'><img src='images/{}' alt='{}' class='{}' /></a>".format(ia["link"], ia["ifn"], ia["alt"], ign))
    else: # no link to larger image
      u.append("<img src='images/{}' alt='{}' class='{}' />".format(ia["ifn"], ia["alt"], ign))

    rep = 1 # source lines to replace

    # is the .il line followed by a caption line?
    if caption_present:
      u.append("<div class='{}'>".format(icn))
      if self.wb[self.cl+1] == ".ca": # multiline
        rep += 1
        j = 2
        s = self.wb[self.cl+j] + "<br />"
        rep += 1
        j += 1
        while ((self.cl + j) < len(self.wb)) and self.wb[self.cl+j] != ".ca-":
          s += self.wb[self.cl+j] + "<br />"
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
    if m:     # will always be true, as we converted ".ti" with no argument to ".ti 2" earlier
      # special case: forcing a .ti of 0
      if int(m.group(1)) == 0:
        self.regTI = -1000
      else:
        self.regTI += int(m.group(1))
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

    if self.pindent:
      t.append("<div class='nf-center-c0'>")
    else:
      t.append("<div class='nf-center-c1'>")

    if not s:
      t.append("  <div class='nf-center'>")
    else:
      t.append("<div class='nf-center' style='{}'>".format(s))

    if self.pindent:
      self.css.addcss("[1876] .nf-center-c0 { text-align:left;margin:0.5em 0; }")  # 17-Jul-2014
    else:
      self.css.addcss("[1876] .nf-center-c1 { text-align:left;margin:1em 0; }")

    self.css.addcss("[1873] .nf-center { text-align:center; }")
    i += 1
    printable_lines_in_block = 0
    pending_mt = 0
    while self.wb[i] != ".nf-":

      if self.bnPresent and self.wb[i].startswith("⑱"):  # if this line is bn info then just leave it in the output as-is
        m = re.match("^⑱.*?⑱(.*)",self.wb[i])
        if m and m.group(1) == "":
          i += 1
          continue

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
  #
  # in epub/mobi, the @media handheld ... (explain....)
  def doNfb(self, nft, mo):
    # any poetry triggers the same CSS
    if 'b' == nft:
      self.css.addcss("[1215] .lg-container-b { text-align: center; }")  # alignment of entire block
      self.css.addcss("[1216] @media handheld { .lg-container-b { clear: both; }}")
    if 'l' == nft:
      self.css.addcss("[1217] .lg-container-l { text-align: left; }")
      self.css.addcss("[1218] @media handheld { .lg-container-l { clear: both; }}")
    if 'r' == nft:
      self.css.addcss("[1219] .lg-container-r { text-align: right; }")
      self.css.addcss("[1220] @media handheld { .lg-container-r { clear: both; }}")

    self.css.addcss("[1221] .linegroup { display: inline-block; text-align: left; }")  # alignment inside block
    self.css.addcss("[1222] @media handheld { .linegroup { display: block; margin-left: 1.5em; }}")
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

    closing = ""
    if 'b' == nft:
      t.append("<div class='lg-container-b'{}>".format(ssty))
      closing = ".nf-"
    if 'l' == nft:
      t.append("<div class='lg-container-l'{}>".format(ssty))
      closing = ".nf-"
    if 'r' == nft:
      t.append("<div class='lg-container-r'{}>".format(ssty))
      closing = ".nf-"
    t.append("  <div class='linegroup'>")
    if mo:
      t.append("    <div class='group0'>")
    else:
      t.append("    <div class='group'>")

    i += 1
    cpvs = 0
    printable_lines_in_block = 0
    while self.wb[i] != closing:

      # if this line is just bn info then just leave it in the output as-is
      if self.bnPresent and self.wb[i].startswith("⑱"):
        m = re.match("^⑱.*?⑱(.*)",self.wb[i])
        if m and m.group(1)=="":
          i += 1
          continue

      # a centered line inside a no-fill block
      m = re.match(r"\.ce (\d+)", self.wb[i])
      if m:
        count = int(m.group(1))
        i += 1 # skip the .ce
        while count > 0 and i < len(self.wb):
          if self.bnPresent and self.wb[i].startswith("⑱"):  # if this line is bn info then just leave it in the output as-is
            m = re.match("^⑱.*?⑱(.*)",self.wb[i])
            if m and m.group(1) == "":
              i += 1
              continue
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
          if self.bnPresent and self.wb[i].startswith("⑱"):  # if this line is bn info then just leave it in the output as-is
            m = re.match("^⑱.*?⑱(.*)",self.wb[i])
            if m and m.group(1) == "":
              i += 1
              continue
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
        m = re.match(r"^(<[^>]+>|⑯\w+⑰)", tmp)
        while m:
          ss += m.group(0)
          tmp = re.sub(r"^<[^>]+>|⑯\w+⑰", "", tmp, 1)
          m = re.match(r"^<[^>]+>|⑯\w+⑰", tmp)
        leadsp = len(tmp) - len(tmp.lstrip())
        if cpvs > 0:
          spvs = " style='margin-top:{}em' ".format(cpvs)
        else:
          spvs = ""
        if leadsp > 0:
          # create an indent class
          iclass = "in{}".format(leadsp)
          iamt = str(-3 + leadsp/2) # calculate based on -3 base
          self.css.addcss("[1227] .linegroup .{} {{ text-indent: {}em; }}".format(iclass, iamt))
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
    m = re.match(r"\.nf-", self.wb[self.cl])
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

  # .fm footnote mark
  def doFmark(self):
    self.wb[self.cl] = "<hr style='border:none; border-bottom:1px solid; width:10%; margin-left:0; margin-top:1em; text-align:left;' />"
    self.cl += 1

  # .fn footnote
  # here on footnote start or end
  # handle completely different for paragraph indent or block style
  def doFnote(self):

    self.css.addcss("[1199] sup { vertical-align: top; font-size: 0.6em; }")

    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    if self.pindent: # indented paragraphs

      m = re.match(r"\.fn-", self.wb[self.cl])
      if m: # footnote ends
        self.wb[self.cl] = "</div>"
        self.cl += 1
        return

      m = re.match(r"\.fn (\d+)", self.wb[self.cl]) # expect numeric footnote
      if m: # footnote start
        self.css.addcss("[1430] div.footnote {}")
        self.css.addcss("[1431] div.footnote>:first-child { margin-top:1em; }")
        self.css.addcss("[1432] div.footnote p { text-indent:1em;margin-top:0.0em;margin-bottom:0; }")
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
          self.css.addcss("[1430] div.footnote {margin-left: 2.5em; }")
          self.css.addcss("[1431] div.footnote>:first-child { margin-top:1em; }")
          self.css.addcss("[1432] div.footnote .label { display: inline-block; width: 0em; text-indent: -2.5em; text-align: right;}")
          fnname = m.group(1)

          # if there is a pending vertical space, include it in style
          hcss = ""
          if self.pvs > 0:
            hcss = " margin-top:{}em; ".format(self.pvs)
            self.pvs = 0

          if hcss != "":
            self.wb[self.cl] = "<div class='footnote' id='f{}' style='{}'>".format(fnname, hcss)
          else:
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
        # blank and centered and .bn info lines are not considered
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
    il_line = self.wb[self.cl]

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
      if "%" not in tw_html:
        self.fatal("please specify table HTML width as percent, i.e. \"{0}%\" \n on line: {1}".format(tw_html, il_line))

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

    # unwrap any user-wrapped text in table
    k1 = self.cl + 1
    while self.wb[k1] != ".ta-":
      while "\\" in self.wb[k1]:
        self.wb[k1] = re.sub(r"\\", "", self.wb[k1])
        self.wb[k1] = self.wb[k1] + " " + self.wb[k1+1]
        del self.wb[k1+1]
      k1 += 1

    t = []

    s = "margin: auto;"  # start building class for table

    if self.pvs > 0:  # pending vertical space
      s += " margin-top: {}em; ".format(self.pvs)
      self.pvs=0

    # if user specified table width (in %), put in a class and attach to table
    # if user also specified table width for epub, put that in a media handheld class
    # fudge factor if ppgen calculates it: 20% to allow for an ALL CAPS (wide) column
    if tw_html != "":
      s += " width:{}; ".format(tw_html)  # use what we are told
    else:
      our_width = min( 100, int(120*(totalwidth/72)) )  # limit to 100%
      left_indent_pct = (100 - our_width) // 2
      right_indent_pct = 100 - our_width - left_indent_pct
      s += " margin-left: {}%; margin-right:{}%; width:{}%; ".format( left_indent_pct, right_indent_pct, our_width )
    self.css.addcss("[1670] .table{0} {{ {1} }}".format(self.tcnt, s))

    if tw_epub != "":
      epw = int(re.sub("%", "", tw_epub)) # as integer
      left_indent_pct = (100 - epw) // 2
      right_indent_pct = 100 - epw - left_indent_pct
      self.css.addcss("[1671] @media handheld {{ .table{} {{ margin-left: {}%; margin-right:{}%; width:{}%; }} }}".format(self.tcnt, left_indent_pct, right_indent_pct, epw))

    t.append("<table class='table{}' summary='{}'>".format(self.tcnt, tsum))

    # set relative widths of columns
    t.append("<colgroup>")
    for (i,w) in enumerate(widths):
     t.append("<col width='{}%' />".format(pwidths[i]))
    t.append("</colgroup>")

    startloc = self.cl
    self.cl += 1 # move into the table rows
    while self.wb[self.cl] != ".ta-":

      # see if .bn info line
      if self.bnPresent and self.wb[self.cl].startswith("⑱"):
        m = re.match("^⑱.*?⑱(.*)",self.wb[self.cl])
        if m and m.group(1) == "":
          t.append(self.wb[self.cl])   # copy the .bn info into the table (deleted much later during postprocessing)
          self.cl += 1
          continue

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
        # inject saved page number if this is first column
        if k == 0:
          v[k] = savedpage + t2
        t.append("    <td style='{}{}{}'>".format(valigns[k],haligns[k],padding) + v[k].strip() + "</td>")
      t.append("  </tr>")
      self.cl += 1
    t.append("</table>")
    self.tcnt += 1
    self.wb[startloc:self.cl+1] = t
    self.cl = startloc + len(t)

  # Drop Image
  # two formats:
  #   .di i_b_009.jpg 100 170 1.3 (width, height, adjust specified)
  #   .di i_b_009.jpg 100 1.3 (width, adjust specified)
  def doDropimage(self):
    m = re.match(r"\.di (\S+) (\d+) (\S+)$",self.wb[self.cl])
    if m:
      d_image = m.group(1)
      d_width = m.group(2)
      d_height = ""
      d_adj = m.group(3)
    else:
      m = re.match(r"\.di (\S+) (\d+) (\d+) (\S+)$",self.wb[self.cl])
      if m:
        d_image = m.group(1)
        d_width = m.group(2)
        d_height = m.group(3)
        d_adj = m.group(4)
      else:
        self.crash_w_context("malformed drop image directive", self.cl)

    self.warn("CSS3 drop-cap. Please note in upload.")
    self.css.addcss("[1920] img.drop-capi { float:left;margin:0 0.5em 0 0;position:relative;z-index:1; }")
    s_adj = re.sub(r"\.","_", str(d_adj))
    if self.pindent:
      s0 = re.sub("em", "", self.nregs["psi"]) # drop the "em"
    else:
      s0 = re.sub("em", "", self.nregs["psb"]) # drop the "em"
    s1 = int(float(s0)*100.0) # in tenths of ems
    s2 = (s1//2)/100 # forces one decimal place
    mtop = s2
    mbot = mtop
    self.css.addcss("[1921] p.drop-capi{} {{ text-indent:0; margin-top:{}em; margin-bottom:{}em}}".format(s_adj,mtop,mbot))
    self.css.addcss("[1922] p.drop-capi{}:first-letter {{ color:transparent; visibility:hidden; margin-left:-{}em; }}".format(s_adj,d_adj))

    self.css.addcss("[1923] @media handheld {")
    self.css.addcss("[1924]   img.drop-capi { display:none; visibility:hidden; }")
    self.css.addcss("[1925]   p.drop-capi{}:first-letter {{ color:inherit; visibility:visible; margin-left:0em; }}".format(s_adj))
    self.css.addcss("[1926] }")

    t = []
    t.append("<div>")
    if d_height == "":
      t.append("  <img class='drop-capi' src='images/{}' width='{}' alt='' />".format(d_image,d_width))
    else:
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
      mt = (250.0 / float(re.sub("%","",self.nregs["dcs"]))) * 0.1
      mr = (250.0 / float(re.sub("%","",self.nregs["dcs"]))) * 0.1
    else:
      self.fatal("incorrect format for .dc arg1 arg2 command")
    self.css.addcss("[1930] p.drop-capa{} {{ text-indent:-{}em; }}".format(dcadjs,dcadj))
    self.css.addcss("[1931] p.drop-capa{}:first-letter {{ float:left;margin:{:0.3f}em {:0.3f}em 0em 0em;font-size:{};line-height:{}em;text-indent:0 }}".format(dcadjs,mt,mr,self.nregs["dcs"],dclh))
    self.css.addcss("[1933] @media handheld {")
    self.css.addcss("[1935]   p.drop-capa{} {{ text-indent:0 }}".format(dcadjs))
    self.css.addcss("[1936]   p.drop-capa{}:first-letter {{ float:none;margin:0;font-size:100%; }}".format(dcadjs))
    self.css.addcss("[1937] }")
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
      while i < len(self.wb):
        bnInLine = False
        if self.wb[i] == "":              # skip blank lines, but remember we had one
          i += 1
          continue
        m = re.search("(.*?)⑱(.*?)⑱.*",self.wb[i])  # find any .bn information in this line
        while m:
          bnInLine = True
          t = " 'Pg{}' => ['offset' => '{}.{}', 'label' => '', 'style' => '', 'action' => '', 'base' => ''],".format(m.group(2),i+1,len(m.group(1)))  # format a line in the .bn array (GG expects 1-based line number)
          t = re.sub("\[","{",t,1)
          t = re.sub("]","}",t,1)
          self.bb.append(t)
          self.wb[i] = re.sub("⑱.*?⑱","",self.wb[i],1)  # remove the .bn information
          m = re.search("(.*?)⑱(.*?)⑱.*",self.wb[i])  # look for another one on the same line
        if bnInLine and self.wb[i] == "":  # delete line if it ended up blank
          del self.wb[i]
          if i > 0 and self.wb[i-1] == "" and self.wb[i] == "":      # If line before .bn info and line after both blank
              del self.wb[i]                          # delete the next one, too.
        else:
          i += 1
      self.bb.append(");")
      self.bb.append("$::pngspath = '{}';".format(os.path.join(os.path.dirname(self.srcfile),"pngs")))
      self.bb.append("1;")


  # called to retrieve a style string representing current display parameters
  #
  def fetchStyle(self, nfc=False):
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
    if not nfc and self.regAD == 0:
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
    i = self.cl - 1
    # if para ended with .bn info, place the </p> before it, not after it to avoid extra
    # blank lines after we remove the .bn info later
    if self.bnPresent and self.wb[i].startswith("⑱"):
      m = re.match("^⑱.*?⑱(.*)",self.wb[i])
      while m and m.group(1) == "":
        i -= 1
        m = re.match("^⑱.*?⑱(.*)",self.wb[i])
    self.wb[i] = self.wb[i] + "</p>"

    self.regTI = 0 # any temporary indent has been used.

  def doChecks(self):
    rb = [] # report buffer
    links = {} # map of links
    targets = {} # map of targets
    # build links
    for i,line in enumerate(self.wb):
      m = re.search(r"href=[\"']#(.*?)[\"']", line)
      while m:            # could have more than one in a line
        t = m.group(1)
        if t in links:
          if not "Page" in t:
            self.linkinfo.add("[6] ")
            self.linkinfo.add("[6]Note: duplicate link: {}".format(t))
        else:
          links[t] = 1
        line = re.sub(re.escape(m.group(0)), "", line, 1) # remove the one we found
        m = re.search(r"href=[\"']#(.*?)[\"']", line)  # look for another one

      m = re.search(r"href=[\"']([^#].*?)[\"']", line) # now look for external links that we can't check
      while m:            # could have more than one in a line
        t = m.group(1)
        if not t.startswith("images/"):    # don't worry about links to our image files
          self.linkinfo.add("[4] ")
          self.linkinfo.add("[4]Warning: cannot validate external link: {}".format(t))
        line = re.sub(re.escape(m.group(0)), "", line, 1) # remove the one we found
        m = re.search(r"href=[\"']([^#].*?)[\"']", line)  # look for another one

    # build targets
    for i,line in enumerate(self.wb):

      m = re.search(r"id=[\"'](.+?)[\"']", line)
      while m:
        t = m.group(1)
        if t in targets:
          self.linkinfo.add("[3] ")
          self.linkinfo.add("[3]Error: duplicate target: {}".format(t))
        else:
          targets[t] = 1
        line = re.sub(re.escape(m.group(0)), "", line, 1)
        m = re.search(r"id=[\"'](.+?)[\"']", line)

    # match links to targets
    for key in links:
      if key not in targets:
        self.linkinfo.add("[2] ")
        self.linkinfo.add("[2]Error: missing target: {}".format(key))

    for key in targets:
     if key not in links:
       if not "Page" in key:
         self.linkinfo.add("[5] ")
         self.linkinfo.add("[5]Note: unused target: {} ".format(key))

    rb = self.linkinfo.show()
    if len(rb):
      self.warn("Possible link and target problems:")
      for w in rb:
        print(self.umap(w))

  #def doUdiv(self):
  #  print(self.wb[self.cl])

  def process(self):

    self.cl = 0
    while self.cl < len(self.wb):
      if "a" in self.debug:
        s = self.wb[self.cl]
        print( self.umap(s) )  # safe print the current line
      if not self.wb[self.cl]: # skip blank lines
        self.cl += 1
        continue
      # will hit either a dot directive, a user-defined <div>, or wrappable text
      if re.match(r"\.", self.wb[self.cl]):
        self.doDot()
        continue
      if self.wb[self.cl].startswith("<div class="):
        self.cl += 1
        continue
      if self.wb[self.cl] == "</div>":
        self.cl += 1
        continue

      # don't turn standalone .bn info lines into paragraphs
      if self.bnPresent and self.wb[self.cl].startswith("⑱"):
        m = re.match("^⑱.*?⑱(.*)",self.wb[self.cl])  # look for standalone .bn info
        if m and m.group(1) == "":   # and skip over it if found
          self.cl += 1
        continue

      self.doPara() # it's a paragraph to wrap

  def makeHTML(self):
    self.doHeader()
    self.doFooter()
    self.placeCSS()
    self.cleanup()
    self.doHTMLSr()

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
  parser.add_argument('-l', '--log', help="display Latin-1, diacritic, and Greek conversion logs", action="store_true")
  parser.add_argument('-d', '--debug', nargs='?', default="", help='debug flags (d,s,a,p,r)') # r = report regex results
  parser.add_argument('-o', '--output_format', default="ht", help='output format (HTML:h, text:t, u or l)')
  parser.add_argument('-a', '--anonymous', action='store_true', help='do not identify version/timestamp in HTML')
  parser.add_argument("-v", "--version", help="display version and exit", action="store_true")
  parser.add_argument("-cvg", "--listcvg", help="list Greek and diacritic table to file ppgen-cvglist.txt and exit", action="store_true")
  parser.add_argument("-f", "--filter", help="UTF-8 filter file for .cv/.gk commands (also terminates after .cv and .gk processing)")
  args = parser.parse_args()

  # version request. print and exit
  if args.version:
    print("{}".format(VERSION))
    exit(1)

  print("ppgen {}".format(VERSION))

  if 'p' in args.debug:
    print("running on {}".format(platform.system()))

  # infile of mystery-src.txt will generate mystery.txt and mystery.html

  if not args.listcvg and (args.infile == None or not args.infile):
    print("infile must be specified. use \"--help\" for help")
    exit(1)

  if 't' in args.output_format:
    ppt = Ppt(args, "u")
    ppt.run()
    ppt = Ppt(args, "l")
    ppt.run()

  # UTF-8 only
  if 'u' in args.output_format:
    ppt = Ppt(args, "u")
    ppt.run()

  # Latin-1 only
  if 'l' in args.output_format:
   ppt = Ppt(args, "l")
   ppt.run()

  if 'h' in args.output_format:
    print("creating HTML version")
    pph = Pph(args, "h")
    pph.run()

  print("done.")

if __name__ == '__main__':
    main()
