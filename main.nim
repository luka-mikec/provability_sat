import unsigned
import math
import sets
import tables
import strutils
import typetraits
import sequtils
import options
import future
import lists
import threadpool

# some additional methods for built-in sets
iterator subsets*[T](s : set[T]) : set[T] =
  var subset : set[T]
  for i in 0 .. 2^s.card - 1:
    subset = {}
    var tmpi : auto = i
    for val in s:
      if 1 == tmpi mod 2:
        subset.incl val
      tmpi = tmpi div 2
    yield subset

proc all*[T](s: set[T], pred: proc (x: T): bool {.closure.}): bool =
  for val in s:
    if not pred(val):
      return false
  return true

proc some*[T](s: set[T], pred: proc (x: T): bool {.closure.}): bool =
  for val in s:
    if pred(val):
      return true
  return false

proc map*[T, S](s: set[T], f: proc (x: T): S {.closure.}): set[S] =
  for val in s:
    result.incl f(val)

proc to_list*[T](s : seq[T]) : SinglyLinkedList[T] =
  result = initSinglyLinkedList[T]()
  for val in s:
    result.prepend(val)

const max_length : int = 16

type
  uint4 = enum
    byte0, byte1, byte2, byte3, byte4, byte5, byte6, byte7,
    byte8, byte9, bytea, byteb, bytec, byted, bytee, bytef
  sf_value_t  = uint32  # pamtimo tip, index lijeve form, index desne f
  sf_index_t  = uint4   # uint4 for length up to 16, uint8 for 256, uint16 for 65k
  sf_index_nt = uint8   # when a proper number is needed
  prop_impl_type = char
  set_of_fs = set[sf_index_t]   # ovo moraju biti bas indexi, ne slova, inace se moze dogodit mesanje (jer modalni u istom skupu)
  interpretation_impl_type = set_of_fs
  subformula_item_t = enum
    content,
    left,
    right
  formula_type = enum
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
  formula = object # for formula UP TO 128 subformulas
    ast      : array[max_length, sf_value_t]
    boxed_sf : set_of_fs
    prop_sf  : set_of_fs
    root : sf_index_nt


when sf_value_t is uint32:
  proc sf_get(sf : sf_value_t, j : subformula_item_t) : sf_index_nt =
    result = case j
      of content: sf and 0x000000ff
      of left:    (sf shr 8)  and 0x000000ff
      of right:   (sf shr 16) and 0x000000ff
when sf_value_t is uint16:
  proc sf_get(sf : sf_value_t, j : subformula_item_t) : sf_index_nt =
    result = case j
      of content: sf and 0x000f
      of left:    (sf shr 4)  and 0x000f
      of right:   (sf shr 8) and 0x000f

proc sf_type(sf : sf_value_t) : formula_type =
 let fcontent = sf_get(sf, content)
 if fcontent <= ord high formula_type: formula_type(fcontent) else: prop

when sf_value_t is uint32:
  proc sf_set(sf: var sf_value_t, j : subformula_item_t,  value: sf_index_nt) : void = # TODO : sf_index_nt =
    case j
      of content: sf = (sf and (uint32)0xffffff00) or value
      of left:    sf = (sf and (uint32)0xffff00ff) or (sf_value_t(value) shl 8)
      of right:   sf = (sf and (uint32)0xff00ffff) or (sf_value_t(value) shl 16)
when sf_value_t is uint16:
  proc sf_set(sf: var sf_value_t, j : subformula_item_t,  value: sf_index_nt) : void = # TODO : sf_index_nt =
    case j
      of content: sf = (sf and (uint16)0xfff0) or value
      of left:    sf = (sf and (uint16)0xff0f) or (sf_value_t(value) shl 4)
      of right:   sf = (sf and (uint16)0xf0ff) or (sf_value_t(value) shl 8)


method `[]`(f : formula, i : sf_index_nt, j : subformula_item_t) : sf_index_nt = sf_get(f.ast[i], j)
method `[]=`(f: var formula, i: sf_index_nt, j : subformula_item_t,  value: sf_index_nt) : void = sf_set(f.ast[i], j, value)
method `[]`(f : formula, i : sf_index_t, j : subformula_item_t) : sf_index_nt = sf_get(f.ast[sf_index_nt i], j)
method `[]=`(f: var formula, i: sf_index_t, j : subformula_item_t,  value: sf_index_nt) : void = sf_set(f.ast[sf_index_nt i], j, value)


proc make_subformula(vcontent : sf_index_nt, vleft : sf_index_nt = 0, vright : sf_index_nt = 0) : sf_value_t =
  sf_set(result, content, vcontent)
  sf_set(result, left, vleft)
  sf_set(result, right, vright)

method update_gamma(f : var formula) : void =
  for i, val in f.ast:
    case sf_type(val)
    of box:
      f.boxed_sf.incl sf_index_t i
    of prop:
      f.prop_sf.incl sf_index_t i
    else:
      discard

proc from_prefix(a : string, index : var int, subformulas : var Table[sf_value_t, sf_index_nt]) : sf_index_nt =
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

proc from_prefix(a : string) : formula =
  let a = replace(replace(a, "D", "~B~"), " ", "")

  var sf : auto = init_table[sf_value_t, sf_index_nt]()
  var i  : int
  result.root = from_prefix(a, i, sf)
  for key, val in sf:
    result.ast[val] = key
  result.update_gamma()

proc `$`(ft : formula_type) : string =
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

proc ft_to_chr(ft : formula_type) : char =
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

proc sf_to_str(f : formula, sf : sf_value_t) : string =
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

method `$`(f : formula) : string =
  return sf_to_str(f, f.ast[f.root])


method gl_eval_prop(f : formula, i : interpretation_impl_type, sf_ind : sf_index_nt) : bool =
  let sf = f.ast[sf_ind]
  case sf_type sf
    of falsum:      return false
    of verum:       return true
    of prop:        return (sf_index_t sf_ind) in i # recimo da se mapira ovako
    of conditional: return not f.gl_eval_prop(i, sf_get(sf, left)) or f.gl_eval_prop(i, sf_get(sf, right))
    of neg:         return not f.gl_eval_prop(i, sf_get(sf, left))
    of land:        return f.gl_eval_prop(i, sf_get(sf, left)) and f.gl_eval_prop(i, sf_get(sf, right))
    of lor:         return f.gl_eval_prop(i, sf_get(sf, left)) or f.gl_eval_prop(i, sf_get(sf, right))
    of box:         return (sf_index_t sf_ind) in i
    else:           raise (ref Exception)(msg: "not GL formula")
method gl_eval_prop(f : formula, i : interpretation_impl_type) : bool = f.gl_eval_prop(i, f.root)

method gl_eval_prop_set(f : formula, i : interpretation_impl_type, sf_ind : sf_index_nt, true_sfs : var set_of_fs, false_sfs : var set_of_fs) : bool =
  if (sf_index_t sf_ind) in true_sfs:  return true
  if (sf_index_t sf_ind) in false_sfs: return false
  let sf = f.ast[sf_ind]
  case sf_type sf
    of falsum:      result = false
    of verum:       result = true
    of prop:        result = (sf_index_t sf_ind) in i
    of conditional:
      let lval = f.gl_eval_prop_set(i, sf_get(sf, left), true_sfs, false_sfs)
      let rval = f.gl_eval_prop_set(i, sf_get(sf, right), true_sfs, false_sfs)
      result = not lval or rval # avoiding short-circuiting or
    of neg:
      let lval = f.gl_eval_prop_set(i, sf_get(sf, left), true_sfs, false_sfs)
      result = not lval
    of land:
      let lval = f.gl_eval_prop_set(i, sf_get(sf, left), true_sfs, false_sfs)
      let rval = f.gl_eval_prop_set(i, sf_get(sf, right), true_sfs, false_sfs)
      result = lval and rval
    of lor:
      let lval = f.gl_eval_prop_set(i, sf_get(sf, left), true_sfs, false_sfs)
      let rval = f.gl_eval_prop_set(i, sf_get(sf, right), true_sfs, false_sfs)
      result = lval or rval
    of box:         (discard f.gl_eval_prop_set(i, sf_get(sf, left), true_sfs, false_sfs);  result = (sf_index_t sf_ind) in i)
    else:           raise (ref Exception)(msg: $f & " is not GL formula")
  if result:
    true_sfs.incl (sf_index_t sf_ind)
  else:
    false_sfs.incl (sf_index_t sf_ind)
method gl_eval_prop_set(f : formula, i : interpretation_impl_type) : set_of_fs =
  # result = {}
  var false_sfs : set_of_fs # = {}
  discard f.gl_eval_prop_set(i, f.root, result, false_sfs)
  #[
  assert(false_sfs * result == {})
  for j, val in f.ast:
    if val != 0:
      if not( (sf_index_t j) in result or (sf_index_t j) in false_sfs ):
        echo f
        echo i
        echo j
        echo result
        echo false_sfs
        quit()
  ]#


proc sattreegl(f : formula,
               goal : Option[sf_index_nt],
               neg_goal : Option[sf_index_nt],
               persistent_bans : set_of_fs,
               persistent_truths : set_of_fs,
               lev : int = 0) : bool =
  let gamma0 = f.boxed_sf + f.prop_sf
  #echo repeat("  ", lev), gamma0, " @ ", (if goal.is_some: goal.get else: neg_goal.get), persistent_truths, persistent_bans
  if persistent_bans * persistent_truths != {} or
    (goal.is_some and (sf_index_t goal.get) in persistent_bans) or
    (neg_goal.is_some and (sf_index_t neg_goal.get) in persistent_truths) :
    #echo repeat("  ", lev), "FAILS", persistent_truths, persistent_bans
    return false
  let vargamma0 = gamma0 - persistent_truths - persistent_bans
  for varK in vargamma0.subsets:
    let K = persistent_truths + varK
    let truths = f.gl_eval_prop_set(K)
    #echo repeat("  ", lev), K, varK, " out of ", vargamma0
    let goal_satisfied = goal.is_none or (sf_index_t goal.get) in truths
    let neg_goal_avoided = neg_goal.is_none or (sf_index_t neg_goal.get) notin truths
    let pers_truths_satisfied = persistent_truths <= truths
    let pers_bans_avoided     = persistent_bans * truths == {}
    #echo repeat("  ", lev), goal_satisfied, neg_goal_avoided, pers_truths_satisfied, pers_bans_avoided
    if not( goal_satisfied and neg_goal_avoided and pers_truths_satisfied and pers_bans_avoided ):
       continue
    var N = f.boxed_sf - K
    if N == {}:
      #echo repeat("  ", lev), "SUCC"
      return true
    let all_satisfied = N.all do (boxC : sf_index_t) -> bool:
      let C = f[boxC, left]
      return sattreegl(
        f = f,
        goal = none sf_index_nt,
        neg_goal = some C,
        persistent_bans   = persistent_bans + (if goal.is_some(): {sf_index_t goal.get} else: {}),
        persistent_truths = persistent_truths +
          f.boxed_sf * K +
          ((f.boxed_sf * K).map boxD => sf_index_t(f[ (sf_index_nt boxD), left])) +
          {boxC} +
          (if neg_goal.is_some(): {sf_index_t neg_goal.get} else: {}),
        lev = lev + 1
      )
    if all_satisfied:
      #echo repeat("  ", lev), "sat:", K
      return true
  #echo repeat("  ", lev), "fail:", gamma0, " @ ", (if goal.is_some: goal.get else: neg_goal.get)
  false


proc sattreegl(f : formula) : bool = sattreegl(f, some f.root, none sf_index_nt, {}, {})

# this checks whether the subsequence of the first occurences of letters starts with 'a', is sorted and without holes
# eg superduper --aab, --aba, -----abacba, but not superduper b, -ac, ---abad
# name inspired by robert webb <3
proc superduper(fs : string) : bool =
  var current_max = ord('a')-1
  let ops_syms = lc[(ft_to_chr x) | (x <- [falsum, verum, neg, box, diamond, rhd, conditional, land, lor]), char]
  for i, c in fs:
    let cc = ord c
    if c in ops_syms:
      continue
    if cc <= current_max:
      continue
    if cc == current_max + 1:
      current_max += 1
    elif cc > current_max + 1:
      return false
  return true


iterator prefix_formulas(length : int, ops = {falsum, verum, conditional, box, diamond}, variables : int = -1) : string =
  let op0 = {falsum, verum} * ops
  let op1 = {box, diamond, neg} * ops
  let op2 = {rhd, conditional, land, lor} * ops

  let variables = if variables == -1: if op1.card > 0: length div 2 else: 1 else: variables
  let var_syms  = lc[$char(i + ord('a'))  |  (i <- 0..variables-1), string]
  let ar0_syms  = var_syms & lc[($ ft_to_chr x) | (x <- op0), string]
  let ar1_syms  = lc[($ ft_to_chr x) | (x <- op1), string]
  let ar2_syms  = lc[($ ft_to_chr x) | (x <- op2), string]

  # we will build formulas recursively by complexity, saving the previous stages
  var fcache    = new_seq[ SinglyLinkedList[string] ](length)
  fcache[0] = to_list ar0_syms
  for stage in 2..length:
    fcache[stage - 1] = to_list lc[ (op & f) | (op <- ar1_syms, f <- fcache[stage - 1 - 1]), string ]

    for pstage1 in 1..stage-2:
      let pstage2 = stage - pstage1 - 1
      if pstage2 < pstage1:
        continue
      for op in ar2_syms:
        for f1 in fcache[pstage1 - 1]:
          for f2 in fcache[pstage2 - 1]:
            fcache[stage - 1].prepend (op & f1 & f2)
            if pstage1 != pstage2:  # skip adding (b, a) if we already have (a, b)
              fcache[stage - 1].prepend (op & f2 & f1)

  for stage in fcache:
    for f in stage:
      if superduper f:
        yield f

iterator formulas(length : int, ops = {falsum, verum, conditional, box, diamond}, variables : int = -1) : formula =
  for f in prefix_formulas(length, ops, variables):
    yield from_prefix f


# let fs = @[ "- B-Bpp Bp", "- BDT B#", "- B-pq -BpBq", "p", "Dp", "~- B-Bpp Bp", "~- BDT B#", "~- B-pq -BpBq", "& Bp B~p", "& DT & Bp B~p" ]

#echo sattreegl from_prefix "~BB#"
#quit()

let threads = 4

import os
import parseutils
var length = case param_count():
  of 0: 10
  else: parse_int(param_str(1))
echo "generating formulas up to length ", length

var fstrs = lc[ initSinglyLinkedList[string]()  |  (i <- 1..threads), SinglyLinkedList[string] ]

var choose_goose = 0 # choose some protection from my selection!
for v in prefix_formulas(length, ops = {falsum, conditional, box}, 3):
  fstrs[choose_goose].prepend v
  choose_goose = (choose_goose + 1) mod threads

echo "generated."
proc search_job(me, max, length : int) : int =
  {.gcsafe.}:
    var c = 0
    var t = 0
    for sf in fstrs[me]:
      let f = from_prefix sf
      t += 1
      if sattreegl f:
        #echo "DA"
        c += 1
      else:
        #echo "NE"
        discard 0

    echo c, "/", t
    c



var responses = new_seq[FlowVar[int]](threads)
for t in 0..threads-1:
  responses[t] = spawn search_job(t, threads, length)
echo sum responses.map( x => ^x )
quit()

