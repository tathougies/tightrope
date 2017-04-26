{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DataKinds #-}

module Web.Tightrope.HTML.Attributes where

import Web.Tightrope.Types
import Web.Tightrope.Attributes

type GenericAttribute =
    forall impl strategy x out st algebra.
    ( strategy ~ AttrStrategy x
    , TightropeImpl impl, Attrable strategy x st) =>
    x -> Attribute' impl out st algebra

class_ :: GenericAttribute
class_ = attr "class"

accept_, acceptCharset_, accesskey_, action_, align_, alt_, async_,
  autocomplete_, autofocus_, autoplay_, bgcolor_, border_, challenge_, charset_,
  checked_, cite_, color_, cols_, colspan_, content_, contenteditable_,
  contextmenu_, controls_, coords_, data_, datetime_, default_, defer_, dir_,
  dirname_, disabled_, download_, draggable_, dropzone_, enctype_, for_, form_,
  formaction_, headers_, height_, hidden_, high_, href_, hreflang_, httpEquiv_,
  id_, ismap_, keytype_, kind_, label_, lang_, language_, list_, loop_, low_,
  manifest_, max_, maxlength_, media_, method_, min_, multiple_, muted_, name_,
  novalidate_, open_, optimum_, pattern_, placeholder_, poster_, preload_,
  readonly_, rel_, required_, reversed_, rows_, rowspan_, sandbox_, scope_,
  scoped_, selected_, shape_, size_, sizes_, span_, spellcheck_, src_, srcdoc_,
  srclang_, srcset_, start_, step_, style_, tabindex_, target_, title_,
  translate_, type_, usemap_, value_, width_, wrap_
    :: GenericAttribute

accept_          = attr "accept"
acceptCharset_   = attr "accept-charset"
accesskey_       = attr "accesskey"
action_          = attr "action"
align_           = attr "align"
alt_             = attr "alt"
async_           = attr "async"
autocomplete_    = attr "autocomplete"
autofocus_       = attr "autofocus"
autoplay_        = attr "autoplay"
bgcolor_         = attr "bgcolor"
border_          = attr "border"
challenge_       = attr "challenge"
charset_         = attr "charset"
checked_         = attr "checked"
cite_            = attr "cite"
color_           = attr "color"
cols_            = attr "cols"
colspan_         = attr "colspan"
content_         = attr "content"
contenteditable_ = attr "contenteditable"
contextmenu_     = attr "contextmenu"
controls_        = attr "controls"
coords_          = attr "coords"
data_            = attr "data"
datetime_        = attr "datetime"
default_         = attr "default"
defer_           = attr "defer"
dir_             = attr "dir"
dirname_         = attr "dirname"
disabled_        = attr "disabled"
download_        = attr "download"
draggable_       = attr "draggable"
dropzone_        = attr "dropzone"
enctype_         = attr "enctype"
for_             = attr "for"
form_            = attr "form"
formaction_      = attr "formaction"
headers_         = attr "headers"
height_          = attr "height"
hidden_          = attr "hidden"
high_            = attr "high"
href_            = attr "href"
hreflang_        = attr "hreflang"
httpEquiv_       = attr "http-equiv"
id_              = attr "id"
ismap_           = attr "ismap"
keytype_         = attr "keytype"
kind_            = attr "kind"
label_           = attr "label"
lang_            = attr "lang"
language_        = attr "language"
list_            = attr "list"
loop_            = attr "loop"
low_             = attr "low"
manifest_        = attr "manifest"
max_             = attr "max"
maxlength_       = attr "maxlength"
media_           = attr "media"
method_          = attr "method"
min_             = attr "min"
multiple_        = attr "multiple"
muted_           = attr "muted"
name_            = attr "name"
novalidate_      = attr "novalidate"
open_            = attr "open"
optimum_         = attr "optimum"
pattern_         = attr "pattern"
placeholder_     = attr "placeholder"
poster_          = attr "poster"
preload_         = attr "preload"
readonly_        = attr "readonly"
rel_             = attr "rel"
required_        = attr "required"
reversed_        = attr "reversed"
rows_            = attr "rows"
rowspan_         = attr "rowspan"
sandbox_         = attr "sandbox"
scope_           = attr "scope"
scoped_          = attr "scoped"
selected_        = attr "selected"
shape_           = attr "shape"
size_            = attr "size"
sizes_           = attr "sizes"
span_            = attr "span"
spellcheck_      = attr "spellcheck"
src_             = attr "src"
srcdoc_          = attr "srcdoc"
srclang_         = attr "srclang"
srcset_          = attr "srcset"
start_           = attr "start"
step_            = attr "step"
style_           = attr "style"
tabindex_        = attr "tabindex"
target_          = attr "target"
title_           = attr "title"
translate_       = attr "translate"
type_            = attr "type"
usemap_          = attr "usemap"
value_           = attr "value"
width_           = attr "width"
wrap_            = attr "wrap"

-- * Units

cm_ :: x -> Unit x "cm"
cm_ = Unit

ch_ :: x -> Unit x "ch"
ch_ = Unit

em_ :: x -> Unit x "em"
em_ = Unit

ex_ :: x -> Unit x "ex"
ex_ = Unit

in_ :: x -> Unit x "in"
in_ = Unit

mm_ :: x -> Unit x "mm"
mm_ = Unit

pc_ :: x -> Unit x "pc"
pc_ = Unit

pct_ :: x -> Unit x "%"
pct_ = Unit

pt_ :: x -> Unit x "pt"
pt_ = Unit

px_ :: x -> Unit x "px"
px_ = Unit

rem_ :: x -> Unit x "rem"
rem_ = Unit

vh_ :: x -> Unit x "vh"
vh_ = Unit

vmax_ :: x -> Unit x "vmax"
vmax_ = Unit

vmin_ :: x -> Unit x "vmin"
vmin_ = Unit

vw_ :: x -> Unit x "vw"
vw_ = Unit
