import helpers
import tables
import strutils
import future

const max_length : int = 16

type
  uint4 = enum
    byte0, byte1, byte2, byte3, byte4, byte5, byte6, byte7,
    byte8, byte9, bytea, byteb, bytec, byted, bytee, bytef
  sf_value_t*  = uint32  # pamtimo tip, index lijeve form, index desne f
  sf_index_t*  = uint4   # uint4 for length up to 16, uint8 for 256, uint16 for 65k
  sf_index_nt* = uint8   # when a proper number is needed
  prop_impl_type* = char
  set_of_fs* = set[sf_index_t]   # ovo moraju biti bas indexi, ne slova, inace se moze dogodit mesanje (jer modalni u istom skupu)
  interpretation_impl_type* = set_of_fs
  subformula_item_t* = enum
    content,
    left,
    right
  formula_type* = enum
    undefined
    falsum
    verum
    conditional
    land
    lor
    neg
    box
    diamond
    rhd
    prop
  formula* = object # for formula UP TO 128 subformulas
    ast*      : array[max_length, sf_value_t]
    boxed_sf* : set_of_fs
    rhd_sf*   : set_of_fs
    prop_sf*  : set_of_fs
    root*     : sf_index_nt


when sf_value_t is uint32:
  proc sf_get*(sf : sf_value_t, j : subformula_item_t) : sf_index_nt =
    result = case j
      of content: sf and 0x000000ff
      of left:    (sf shr 8)  and 0x000000ff
      of right:   (sf shr 16) and 0x000000ff
when sf_value_t is uint16:
  proc sf_get*(sf : sf_value_t, j : subformula_item_t) : sf_index_nt =
    result = case j
      of content: sf and 0x000f
      of left:    (sf shr 4)  and 0x000f
      of right:   (sf shr 8) and 0x000f

proc sf_type*(sf : sf_value_t) : formula_type =
 let fcontent = sf_get(sf, content)
 if fcontent <= ord high formula_type: formula_type(fcontent) else: prop

when sf_value_t is uint32:
  proc sf_set*(sf: var sf_value_t, j : subformula_item_t,  value: sf_index_nt) : void = # TODO : sf_index_nt =
    case j
      of content: sf = (sf and (uint32)0xffffff00) or value
      of left:    sf = (sf and (uint32)0xffff00ff) or (sf_value_t(value) shl 8)
      of right:   sf = (sf and (uint32)0xff00ffff) or (sf_value_t(value) shl 16)
when sf_value_t is uint16:
  proc sf_set*(sf: var sf_value_t, j : subformula_item_t,  value: sf_index_nt) : void = # TODO : sf_index_nt =
    case j
      of content: sf = (sf and (uint16)0xfff0) or value
      of left:    sf = (sf and (uint16)0xff0f) or (sf_value_t(value) shl 4)
      of right:   sf = (sf and (uint16)0xf0ff) or (sf_value_t(value) shl 8)


method `[]`*(f : formula, i : sf_index_nt, j : subformula_item_t) : sf_index_nt = sf_get(f.ast[i], j)
method `[]=`*(f: var formula, i: sf_index_nt, j : subformula_item_t,  value: sf_index_nt) : void = sf_set(f.ast[i], j, value)
method `[]`*(f : formula, i : sf_index_t, j : subformula_item_t) : sf_index_t = sf_index_t sf_get(f.ast[sf_index_nt i], j)
method `[]=`*(f: var formula, i: sf_index_t, j : subformula_item_t,  value: sf_index_nt) : void = sf_set(f.ast[sf_index_nt i], j, value)

proc make_subformula*(vcontent : sf_index_nt, vleft : sf_index_nt = 0, vright : sf_index_nt = 0) : sf_value_t =
  sf_set(result, content, vcontent)
  sf_set(result, left, vleft)
  sf_set(result, right, vright)

method update_gamma*(f : var formula) : void =
  for i, val in f.ast:
    case sf_type(val)
    of rhd:
      f.rhd_sf.incl sf_index_t i
    of box:
      f.boxed_sf.incl sf_index_t i
    of prop:
      f.prop_sf.incl sf_index_t i
    else:
      discard

proc from_prefix*(a : string, index : var int, subformulas : var Table[sf_value_t, sf_index_nt]) : sf_index_nt =
  let s = a[index]
  inc index
  let value : sf_value_t = case s
    of 'a'..'z':
      sf_value_t(ord s)
    of 'B':
      let arg   = from_prefix(a, index, subformulas)
      make_subformula(sf_index_nt(box), arg)
    of 'D':
      let arg   = from_prefix(a, index, subformulas)
      make_subformula(sf_index_nt(diamond), arg)
    of '#':
      make_subformula sf_index_nt(falsum)
    of 'T':
      make_subformula sf_index_nt(verum)
    of '>':
      let vleft  = from_prefix(a, index, subformulas)
      let vright = from_prefix(a, index, subformulas)
      make_subformula(sf_index_nt(rhd), vleft, vright)
    of '~':
      let vleft  = from_prefix(a, index, subformulas)
      make_subformula(sf_index_nt(neg), vleft)
    of '&':
      let vleft  = from_prefix(a, index, subformulas)
      let vright = from_prefix(a, index, subformulas)
      make_subformula(sf_index_nt(land), vleft, vright)
    of '|':
      let vleft  = from_prefix(a, index, subformulas)
      let vright = from_prefix(a, index, subformulas)
      make_subformula(sf_index_nt(lor), vleft, vright)
    of '-':
      let vleft  = from_prefix(a, index, subformulas)
      let vright = from_prefix(a, index, subformulas)
      make_subformula(sf_index_nt(conditional), vleft, vright)
    else:
      0
  result = if value in subformulas:
      subformulas[value]
    else:
    (block:
      subformulas[value] = sf_index_nt(subformulas.len)
      sf_index_nt(subformulas.len - 1)
    )

proc from_prefix*(a : string) : formula =
  let a = replace(replace(a, "D", "~B~"), " ", "")

  var sf : auto = init_table[sf_value_t, sf_index_nt]()
  var i  : int
  result.root = from_prefix(a, i, sf)
  for key, val in sf:
    result.ast[val] = key
  result.update_gamma()

proc `$`*(ft : formula_type) : string =
  case ft
    of falsum:      "#"
    of verum:       "T"
    of rhd:         "|>"
    of conditional: "->"
    of land:        "&"
    of lor:         "|"
    of box:         "[]"
    of diamond:     "<>"
    of neg:         "¬"
    of prop:        "?p?"
    else:           "???"

proc ft_to_chr*(ft : formula_type) : char =
  case ft
    of falsum:      '#'
    of verum:       'T'
    of rhd:         '>'
    of conditional: '-'
    of land:        '&'
    of lor:         '|'
    of box:         'B'
    of diamond:     'D'
    of neg:         '~'
    of prop:        '?'
    else:           '?'

proc sf_to_str*(f : formula, sf : sf_value_t) : string =
  let fcontent : auto = sf_get(sf, content)
  let ft : auto = sf_type sf
  let vl : auto = sf_get(sf, left)
  let vr : auto = sf_get(sf, right)
  result = case ft
    of falsum, verum:               $ft
    of rhd, conditional, land, lor: "(" & sf_to_str(f, f.ast[vl]) & ' ' & $ft & ' ' & sf_to_str(f, f.ast[vr]) & ")"
    of neg, box, diamond:           $ft & sf_to_str(f, f.ast[vl])
    of prop:                        $char(fcontent)
    else:                           $ft

method `$`*(f : formula) : string =
  return sf_to_str(f, f.ast[f.root])


method extend_forcing*(f : formula, i : interpretation_impl_type, sf_ind : sf_index_nt, true_sfs : var set_of_fs, false_sfs : var set_of_fs) : bool =
  if (sf_index_t sf_ind) in true_sfs:  return true
  if (sf_index_t sf_ind) in false_sfs: return false
  let sf = f.ast[sf_ind]
  case sf_type sf
    of falsum:      result = false
    of verum:       result = true
    of prop:        result = (sf_index_t sf_ind) in i
    of conditional:
      let lval = f.extend_forcing(i, sf_get(sf, left), true_sfs, false_sfs)
      let rval = f.extend_forcing(i, sf_get(sf, right), true_sfs, false_sfs)
      result = not lval or rval # avoiding short-circuiting or
    of neg:
      let lval = f.extend_forcing(i, sf_get(sf, left), true_sfs, false_sfs)
      result = not lval
    of land:
      let lval = f.extend_forcing(i, sf_get(sf, left), true_sfs, false_sfs)
      let rval = f.extend_forcing(i, sf_get(sf, right), true_sfs, false_sfs)
      result = lval and rval
    of lor:
      let lval = f.extend_forcing(i, sf_get(sf, left), true_sfs, false_sfs)
      let rval = f.extend_forcing(i, sf_get(sf, right), true_sfs, false_sfs)
      result = lval or rval
    of rhd:
      discard f.extend_forcing(i, sf_get(sf, left), true_sfs, false_sfs)
      discard f.extend_forcing(i, sf_get(sf, right), true_sfs, false_sfs)
      result = (sf_index_t sf_ind) in i
    of box:         (discard f.extend_forcing(i, sf_get(sf, left), true_sfs, false_sfs);  result = (sf_index_t sf_ind) in i)
    else:           raise (ref Exception)(msg: $f & " is not a supported formula")
  if result:
    true_sfs.incl(sf_index_t sf_ind)
  else:
    false_sfs.incl(sf_index_t sf_ind)
method extend_forcing*(f : formula, i : interpretation_impl_type) : set_of_fs =
  # result = {}
  var false_sfs : set_of_fs # = {}
  discard f.extend_forcing(i, f.root, result, false_sfs)