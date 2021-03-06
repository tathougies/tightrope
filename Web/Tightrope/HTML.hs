{-# LANGUAGE OverloadedStrings #-}

module Web.Tightrope.HTML where

import Web.Tightrope.Types
import Web.Tightrope.Element

a_, abbr_, acronym_, address_, applet_, area_, article_, aside_, audio_, b_,
  base_, basefont_, bdi_, bdo_, big_, blockquote_, body_, br_, button_, canvas_,
  caption_, center_, cite_, code_, col_, colgroup_, datalist_, dd_, del_,
  details_, dfn_, dialog_, dir_, div_, dl_, dt_, em_, embed_, fieldset_,
  figcaption_, figure_, font_, footer_, form_, frame_, frameset_, h1_, h2_, h3_,
  h4_, h5_, h6_, head_, header_, hr_, html_, i_, iframe_, img_, input_, ins_,
  kbd_, keygen_, label_, legend_, li_, link_, main_, map_, mark_, menu_,
  menuitem_, meta_, meter_, nav_, noframes_, noscript_, object_, ol_, optgroup_,
  option_, output_, p_, param_, picture_, pre_, progress_, q_, rp_, rt_, ruby_,
  s_, samp_, script_, section_, select_, small_, source_, span_, strike_,
  strong_, style_, sub_, summary_, sup_, table_, tbody_, td_, textarea_, tfoot_,
  th_, thead_, time_, title_, tr_, track_, tt_, u_, ul_, var_, video_, wbr_
   :: GenericSnippet

a_          = el "a"
abbr_       = el "abbr"
acronym_    = el "acronym"
address_    = el "address"
applet_     = el "applet"
area_       = el "area"
article_    = el "article"
aside_      = el "aside"
audio_      = el "audio"
b_          = el "b"
base_       = el "base"
basefont_   = el "basefont"
bdi_        = el "bdi"
bdo_        = el "bdo"
big_        = el "big"
blockquote_ = el "blockquote"
body_       = el "body"
br_         = el "br"
button_     = el "button"
canvas_     = el "canvas"
caption_    = el "caption"
center_     = el "center"
cite_       = el "cite"
code_       = el "code"
col_        = el "col"
colgroup_   = el "colgroup"
datalist_   = el "datalist"
dd_         = el "dd"
del_        = el "del"
details_    = el "details"
dfn_        = el "dfn"
dialog_     = el "dialog"
dir_        = el "dir"
div_        = el "div"
dl_         = el "dl"
dt_         = el "dt"
em_         = el "em"
embed_      = el "embed"
fieldset_   = el "fieldset"
figcaption_ = el "figcaption"
figure_     = el "figure"
font_       = el "font"
footer_     = el "footer"
form_       = el "form"
frame_      = el "frame"
frameset_   = el "frameset"
h1_         = el "h1"
h2_         = el "h2"
h3_         = el "h3"
h4_         = el "h4"
h5_         = el "h5"
h6_         = el "h6"
head_       = el "head"
header_     = el "header"
hr_         = el "hr"
html_       = el "html"
i_          = el "i"
iframe_     = el "iframe"
img_        = el "img"
input_      = el "input"
ins_        = el "ins"
kbd_        = el "kbd"
keygen_     = el "keygen"
label_      = el "label"
legend_     = el "legend"
li_         = el "li"
link_       = el "link"
main_       = el "main"
map_        = el "map"
mark_       = el "mark"
menu_       = el "menu"
menuitem_   = el "menuitem"
meta_       = el "meta"
meter_      = el "meter"
nav_        = el "nav"
noframes_   = el "noframes"
noscript_   = el "noscript"
object_     = el "object"
ol_         = el "ol"
optgroup_   = el "optgroup"
option_     = el "option"
output_     = el "output"
p_          = el "p"
param_      = el "param"
picture_    = el "picture"
pre_        = el "pre"
progress_   = el "progress"
q_          = el "q"
rp_         = el "rp"
rt_         = el "rt"
ruby_       = el "ruby"
s_          = el "s"
samp_       = el "samp"
script_     = el "script"
section_    = el "section"
select_     = el "select"
small_      = el "small"
source_     = el "source"
span_       = el "span"
strike_     = el "strike"
strong_     = el "strong"
style_      = el "style"
sub_        = el "sub"
summary_    = el "summary"
sup_        = el "sup"
table_      = el "table"
tbody_      = el "tbody"
td_         = el "td"
textarea_   = el "textarea"
tfoot_      = el "tfoot"
th_         = el "th"
thead_      = el "thead"
time_       = el "time"
title_      = el "title"
tr_         = el "tr"
track_      = el "track"
tt_         = el "tt"
u_          = el "u"
ul_         = el "ul"
var_        = el "var"
video_      = el "video"
wbr_        = el "wbr"
