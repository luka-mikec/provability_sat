import helpers
import tables
import strutils
import future
import sequtils

const max_length : int = 256

type
  uint4* = enum
    byte0, byte1, byte2, byte3, byte4, byte5, byte6, byte7,
    byte8, byte9, bytea, byteb, bytec, byted, bytee, bytef
  sf_value_t*  = int32  # pamtimo tip, index lijeve form, index desne f
  sf_index_t*  = int8   # uint4 for length up to 16, uint8 for 256, uint16 for 65k
  sf_index_nt* = int8   # when a proper number is needed (when enum types are used)
  prop_impl_type* = char
  set_of_sfs* = set[sf_index_t]   # ovo moraju biti bas indexi, ne slova, inace se moze dogodit mesanje (jer modalni u istom skupu)
  interpretation_impl_type* = set_of_sfs
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
    notcond
    neg
    box
    diamond
    rhd
    prop
    id
  formula* = object # for formula UP TO 128 subformulas
    ast*      : array[max_length, sf_value_t] # assumption: subformulas have lower indices
    ast_len*  : sf_index_nt # used capacity of ast
    boxed_sf* : set_of_sfs
    rhd_sf*   : set_of_sfs
    prop_sf*  : set_of_sfs
    all_sf*   : set_of_sfs
    #gamma_m*  : set_of_sfs # this should prolly just be all_sf; it won't be a tree
    root*     : sf_index_nt

    boxed_not_root*  : sf_index_nt # m specific
    m_start*  : sf_index_nt # m specific
    boxnot* : Table[sf_index_t, sf_index_t] # m specific

const arity0_operators* = {falsum, verum}
const arity1_operators* = {box, diamond, neg}
const arity2_operators* = {rhd, conditional, land, lor, notcond}
const all_operators* = arity0_operators + arity1_operators + arity2_operators

when sf_value_t is int32:
  proc sf_get*(sf : sf_value_t, j : subformula_item_t) : sf_index_nt =
    result = case j
      of content: sf_index_nt(sf and 0x000000ff)
      of left:    sf_index_nt((sf shr 8)  and 0x000000ff)
      of right:   sf_index_nt((sf shr 16) and 0x000000ff)
when sf_value_t is int16:
  proc sf_get*(sf : sf_value_t, j : subformula_item_t) : sf_index_nt =
    result = case j
      of content: sf and 0x000f
      of left:    (sf shr 4)  and 0x000f
      of right:   (sf shr 8) and 0x000f

proc sf_type*(sf : sf_value_t) : formula_type =
 let fcontent = sf_get(sf, content)
 if fcontent <= ord high formula_type: formula_type(fcontent) else: prop

when sf_value_t is int32:
  proc sf_set*(sf: var sf_value_t, j : subformula_item_t,  value: sf_index_nt) : void = # TODO : sf_index_nt =
    case j
      of content: sf = (sf and (sf_value_t)0xffffff00'i32) or sf_value_t(value)
      of left:    sf = (sf and (sf_value_t)0xffff00ff'i32) or (sf_value_t(value) shl 8)
      of right:   sf = (sf and (sf_value_t)0xff00ffff'i32) or (sf_value_t(value) shl 16)
when sf_value_t is int16:
  proc sf_set*(sf: var sf_value_t, j : subformula_item_t,  value: sf_index_nt) : void = # TODO : sf_index_nt =
    case j
      of content: sf = (sf and (sf_value_t)0xfff0'i16) or value
      of left:    sf = (sf and (sf_value_t)0xff0f'i16) or (sf_value_t(value) shl 4)
      of right:   sf = (sf and (sf_value_t)0xf0ff'i16) or (sf_value_t(value) shl 8)


method `[]`*(f : formula, i : sf_index_nt, j : subformula_item_t) : sf_index_nt = sf_get(f.ast[i], j)
method `[]=`*(f: var formula, i: sf_index_nt, j : subformula_item_t,  value: sf_index_nt) : void = sf_set(f.ast[i], j, value)
when not( sf_index_t is sf_index_nt ):
  method `[]`*(f : formula, i : sf_index_t, j : subformula_item_t) : sf_index_t = sf_index_t sf_get(f.ast[sf_index_nt i], j)
  method `[]=`*(f: var formula, i: sf_index_t, j : subformula_item_t,  value: sf_index_nt) : void = sf_set(f.ast[sf_index_nt i], j, value)

proc make_subformula*(vcontent : sf_index_nt, vleft : sf_index_nt = 0, vright : sf_index_nt = 0) : sf_value_t =
  sf_set(result, content, vcontent)
  sf_set(result, left, vleft)
  sf_set(result, right, vright)

method update_gamma*(f : var formula) : void =
  for i, val in f.ast:
    if sf_type(val) != undefined:
      f.all_sf.incl sf_index_t i
      # f.gamma_m.incl sf_index_t i

      case sf_type(val)
      of rhd:
        f.rhd_sf.incl sf_index_t i
      of box:
        f.boxed_sf.incl sf_index_t i
      of prop:
        f.prop_sf.incl sf_index_t i
      else:
        discard


proc chr_to_ft*(chr : char) : formula_type =
  case chr
    of '#': falsum
    of 'T': verum
    of '>': rhd
    of '-': conditional
    of '&': land
    of '|': lor
    of '%': notcond
    of 'B': box
    of 'D': diamond
    of '~': neg
    of '(': id
    else  : undefined

proc from_prefix*(a : string, index : var int, subformulas : var Table[sf_value_t, sf_index_nt]) : sf_index_nt =
  let s = a[index]
  let ft = chr_to_ft s
  inc index
  let value : sf_value_t = case ft
    of arity0_operators:  # T, #
      make_subformula sf_index_nt ft
    of arity1_operators:  # B, D, ~
      let arg   = from_prefix(a, index, subformulas)
      make_subformula(sf_index_nt(ft), arg)
    of arity2_operators:  # >, &, %, |, -
      let vleft  = from_prefix(a, index, subformulas)
      let vright = from_prefix(a, index, subformulas)
      make_subformula(sf_index_nt(ft), vleft, vright)
    else: # prop variable
      sf_value_t(ord s)
  result = if value in subformulas:
      subformulas[value]
    else:
    (block:
      subformulas[value] = sf_index_nt(subformulas.len)
      sf_index_nt(subformulas.len - 1)
    )

proc from_prefix*(a : string, append_boxes : bool = false) : formula =
  let a = replace(replace(a, "D", "~B~"), " ", "")

  var subformulas : auto = init_table[sf_value_t, sf_index_nt]()
  var i  : int
  result.root = from_prefix(a, i, subformulas)
  result.m_start = sf_index_nt i
  result.ast_len = sf_index_nt i

  if append_boxes:
    let bot_formula = make_subformula sf_index_nt falsum
    var bot_index : sf_index_nt = sf_index_nt i
    if bot_formula in subformulas:
      bot_index = subformulas[bot_formula]
    else:
      subformulas[bot_formula] = bot_index
      i += 1

    var new_subformulas : auto = init_table[sf_value_t, sf_index_nt]()
    for form_value, form_ind in subformulas:
      let f_rhd_bot = make_subformula(sf_index_nt rhd, form_ind, bot_index)
      var f_rhd_bot_index : sf_index_nt = sf_index_nt i
      if f_rhd_bot in subformulas:
        f_rhd_bot_index = subformulas[f_rhd_bot]
      else:
        new_subformulas[f_rhd_bot] = sf_index_nt i
        if form_ind == result.root:
          result.boxed_not_root = sf_index_nt i
        i += 1
      result.boxnot[form_ind] = f_rhd_bot_index
    for form_value, form_ind in new_subformulas:
      subformulas[form_value] = form_ind
      result.ast_len += 1

  for form_value, form_ind in subformulas:
    result.ast[form_ind] = form_value
  result.update_gamma()


proc `$`*(ft : formula_type) : string =
  case ft
    of falsum:      "\u27c2"
    of verum:       "\u22a4"
    of rhd:         "\u22B3"
    of notcond:     "\u219b"
    of conditional: "\u2192"
    of land:        "\u2227"
    of lor:         "\u2228"
    of box:         "\u25fb"
    of diamond:     "\u25ca"
    of neg:         "\uac"
    of prop:        "\u1f001"
    else:           "\u1f631"

proc ft_to_chr*(ft : formula_type) : char =
  case ft
    of falsum:      '#'
    of verum:       'T'
    of rhd:         '>'
    of conditional: '-'
    of land:        '&'
    of lor:         '|'
    of notcond:     '%'
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
    of arity0_operators: $ft
    of arity1_operators: $ft & sf_to_str(f, f.ast[vl])
    of arity2_operators: "(" & sf_to_str(f, f.ast[vl]) & ' ' & $ft & ' ' & sf_to_str(f, f.ast[vr]) & ")"
    of prop:             $char(fcontent)
    else:                $ft

method `$`*(f : formula) : string =
  return sf_to_str(f, f.ast[f.root])

# this is just for infix -> prefix conversion
type exprnode = object
  ftype : formula_type
  data  : char
  lexpr : ref exprnode
  rexpr : ref exprnode

proc toks(str : string, i : int) : tuple[curr: char, peek: char] =
  let c = str[i + 0]
  let p = case (len str) - i
    of 1: '\0'
    else: str[i + 1]
  (c, p)

proc infixp(str : string, i : var int, preferunary : bool = false) : ref exprnode =
  new(result)

  var c, p : char
  (c, p) = toks(str, i)
  var am_unary = preferunary

  var ft = chr_to_ft c
  result.ftype = ft

  case ft
    of id:
      inc i
      result.lexpr = infixp(str, i, false)
      inc i
      (c, p) = toks(str, i)
      assert(c == ')')
    of arity1_operators:
      inc i
      result.lexpr = infixp(str, i, true)
    of arity0_operators:
      result.ftype = ft
    else:
      result.ftype = prop
      result.data  = c
  # do we already know this expr is unary?
  if am_unary:
    return result

  # TODO: shouldn't we check for EOS?

  # expr is allowed to be binary, is it?
  (c, p) = toks(str, i)
  let tn = chr_to_ft p
  if tn notin arity2_operators:
    return result

  # expr is binary
  let lexpr = result
  new(result)
  result.lexpr = lexpr

  inc i
  (c, p) = toks(str, i)
  ft = chr_to_ft c
  result.ftype = ft

  inc i
  (c, p) = toks(str, i)
  ft = chr_to_ft c

  new(result.rexpr)
  result.rexpr.ftype = ft
  case ft
    of id:
      inc i
      result.rexpr.lexpr = infixp(str, i, false)
      inc i
      (c, p) = toks(str, i)
      assert(c == ')')
    of arity1_operators:
      inc i
      result.rexpr.lexpr = infixp(str, i, true)
    of arity0_operators:
      result.rexpr.ftype = ft
    else:
      result.rexpr.ftype = prop
      result.rexpr.data  = c
  result

proc infixp(str : string) : ref exprnode =
  var i = 0
  return infixp(replace(str, " ", ""), i)

proc exprnode_to_prefix(e : ref exprnode) : string =
  case e.ftype
    of prop:
      $e.data
    of arity0_operators:
      $ft_to_chr(e.ftype)
    of arity1_operators:
      if e.ftype == box:
        ft_to_chr(rhd) & ft_to_chr(neg) & exprnode_to_prefix(e.lexpr) &  ft_to_chr(falsum) 
      elif e.ftype == diamond:
        ft_to_chr(neg) & ft_to_chr(rhd) &  exprnode_to_prefix(e.lexpr) &  ft_to_chr(falsum)
      else:
        ft_to_chr(e.ftype) & exprnode_to_prefix(e.lexpr)
    of arity2_operators:
      ft_to_chr(e.ftype) & exprnode_to_prefix(e.lexpr) & exprnode_to_prefix(e.rexpr)
    of id:
      exprnode_to_prefix(e.lexpr)
    else:
      "???"

proc from_infix*(str : string, append_boxes : bool = false) : formula =
  from_prefix(exprnode_to_prefix infixp multi_replace(str, ("->", "-"), ("&&", "&"), ("\\/", "|"), ("||", "|"), ("/\\", "&"),
                                 ("_|_", "#"), ("[]", "B"), ("<>", "D"), ("¬", "~"), ("|>", ">"), ("*", "&"), ("+", "|"),
                                 ("\u27c2", "#"), ("\u22a4", "T"), ("\u22B3", ">"), ("\u219b", "%"), ("\u2192", "-"),
                                 ("\u2227", "&"), ("\u2228", "|"), ("\u25fb", "B"), ("\u25ca", "D"), ("\uac", "~") ),
              append_boxes)

var bla1*, bla2* : int
bla1 = 0
bla2 = 0

method extend_forcing*(f : formula, i : interpretation_impl_type) : set_of_sfs =
  for sf_ind in sf_index_t(0)..<sf_index_t(f.ast_len):
    let sf = f.ast[sf_ind]
    var sf_true : bool
    case sf_type sf
      of falsum:
        sf_true = false
      of verum:
        sf_true = true
      of prop:
        sf_true = sf_ind in i
      of conditional:
        sf_true = sf_get(sf, left) notin result or
          sf_get(sf, right) in result
      of neg:
        sf_true = sf_get(sf, left) notin result
      of land:
        sf_true = sf_get(sf, left) in result and
          sf_get(sf, right) in result
      of lor:
        sf_true = sf_get(sf, left) in result or
          sf_get(sf, right) in result
      of notcond:
        sf_true = sf_get(sf, left) in result and
          sf_get(sf, right) notin result
      of rhd:
        sf_true = sf_ind in i
      of box:
        sf_true = sf_ind in i
      else:
        sf_true = sf_ind in i
        #raise (ref Exception)(msg: "extend_forcing: type '" & $int(sf_type sf) & "' of formula '" & sf_to_str(f, f.ast[sf]) & "' not supported")
    if sf_true:
      result.incl(sf_ind)
  return result
