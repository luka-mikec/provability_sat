import unsigned
import math
import sets
import tables
import strutils
import typetraits
import sequtils
import options
import future
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


const max_depth : int = 14

type
  sf_value_t = uint32  # pamtimo tip, index lijeve form, index desne f
  sf_index_t = uint8   # zapravo je 8, al da se ne dogode cudne stvari
  prop_impl_type = char
  set_of_fs = set[sf_index_t]   # ovo moraju biti bas indexi, ne slova, inace se moze dogodit mesanje (jer modalni u istom skupu)
  interpretation_impl_type = set_of_fs
  subformula_t = object
    itr : sf_index_t
    val : sf_value_t
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
  fat_formula = object
    case tip: formula_type
    of undefined, falsum, verum:
      nil
    of prop:
      letter: prop_impl_type
    of box, diamond, neg:
      arg: ref fat_formula
    of conditional, rhd, land, lor:
      left, right: ref fat_formula
    cache_str : string
  formula = object # for formula UP TO 128 subformulas
    ast      : array[11, sf_value_t]
    boxed_sf : set[sf_index_t]
    prop_sf  : set[sf_index_t]
    root : sf_index_t


proc sf_get(sf : sf_value_t, j : subformula_item_t) : sf_index_t =
  case j
    of content: sf and 0x000000ff
    of left:    (sf shr 8)  and 0x000000ff
    of right:   (sf shr 16) and 0x000000ff

proc sf_type(sf : sf_value_t) : formula_type =
 let fcontent = sf_get(sf, content)
 if fcontent <= ord high formula_type: formula_type(fcontent) else: prop

proc sf_set(sf: var sf_value_t, j : subformula_item_t,  value: sf_index_t) : void = # TODO : sf_index_t =
  case j
    of content: sf = (sf and (uint32)0xffffff00) or value
    of left:    sf = (sf and (uint32)0xffff00ff) or (sf_value_t(value) shl 8)
    of right:   sf = (sf and (uint32)0xff00ffff) or (sf_value_t(value) shl 16)


method `[]`(f : formula, i : sf_index_t, j : subformula_item_t) : sf_index_t = sf_get(f.ast[i], j)
method `[]=`(f: var formula, i: sf_index_t, j : subformula_item_t,  value: sf_index_t) : void = sf_set(f.ast[i], j, value)


proc make_subformula(vcontent : sf_index_t, vleft : sf_index_t = 0, vright : sf_index_t = 0) : sf_value_t =
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

proc from_prefix(a : string, index : var int, subformulas : var Table[sf_value_t, sf_index_t]) : sf_index_t =
  let s = a[index]
  inc index
  let value : sf_value_t = case s
    of 'a'..'z':
      sf_value_t(ord s)
    of 'B':
      let arg   = from_prefix(a, index, subformulas)
      make_subformula(sf_index_t(box), arg)
    of 'D':
      let arg   = from_prefix(a, index, subformulas)
      make_subformula(sf_index_t(diamond), arg)
    of '#':
      make_subformula sf_index_t(falsum)
    of 'T':
      make_subformula sf_index_t(verum)
    of '>':
      let vleft  = from_prefix(a, index, subformulas)
      let vright = from_prefix(a, index, subformulas)
      make_subformula(sf_index_t(rhd), vleft, vright)
    of '~':
      let vleft  = from_prefix(a, index, subformulas)
      make_subformula(sf_index_t(neg), vleft)
    of '&':
      let vleft  = from_prefix(a, index, subformulas)
      let vright = from_prefix(a, index, subformulas)
      make_subformula(sf_index_t(land), vleft, vright)
    of '|':
      let vleft  = from_prefix(a, index, subformulas)
      let vright = from_prefix(a, index, subformulas)
      make_subformula(sf_index_t(lor), vleft, vright)
    of '-':
      let vleft  = from_prefix(a, index, subformulas)
      let vright = from_prefix(a, index, subformulas)
      make_subformula(sf_index_t(conditional), vleft, vright)
    else:
      0
  result = if value in subformulas:
      subformulas[value]
    else:
    (block:
      subformulas[value] = sf_index_t(subformulas.len)
      sf_index_t(subformulas.len - 1)
    )

proc from_prefix(a : string) : formula =
  let a = replace(replace(a, "D", "~B~"), " ", "")

  var sf : auto = init_table[sf_value_t, sf_index_t]()
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


method gl_eval_prop(f : formula, i : interpretation_impl_type, sf_ind : sf_index_t) : bool =
  let sf = f.ast[sf_ind]
  case sf_type sf
    of falsum:      return false
    of verum:       return true
    of prop:        return sf_ind in i # recimo da se mapira ovako
    of conditional: return not f.gl_eval_prop(i, sf_get(sf, left)) or f.gl_eval_prop(i, sf_get(sf, right))
    of neg:         return not f.gl_eval_prop(i, sf_get(sf, left))
    of land:        return f.gl_eval_prop(i, sf_get(sf, left)) and f.gl_eval_prop(i, sf_get(sf, right))
    of lor:         return f.gl_eval_prop(i, sf_get(sf, left)) or f.gl_eval_prop(i, sf_get(sf, right))
    of box:         return sf_ind in i
    else:           raise (ref Exception)(msg: "not GL formula")

method gl_eval_prop(f : formula, i : interpretation_impl_type) : bool = f.gl_eval_prop(i, f.root)


proc sattreegl(f : formula,
               goal : Option[sf_index_t],
               neg_goal : Option[sf_index_t],
               persistent_bans : set_of_fs,
               persistent_truths : set_of_fs,
               lev : int = 0) : bool =
  let gamma0 = f.boxed_sf + f.prop_sf
  #echo repeat("  ", lev), gamma0, " @ ", (if goal.is_some: goal.get else: neg_goal.get), persistent_truths, persistent_bans
  if persistent_bans * persistent_truths != {}:
    #echo repeat("  ", lev), "FAILS", persistent_truths, persistent_bans
    return false
  let vargamma0 = gamma0 - persistent_truths - persistent_bans
  for varK in vargamma0.subsets:
    let K = persistent_truths + varK
    #echo repeat("  ", lev), K, varK, " out of ", vargamma0
    let goal_satisfied = goal.is_none or f.gl_eval_prop(K, goal.get)
    let neg_goal_avoided = neg_goal.is_none or not f.gl_eval_prop(K, neg_goal.get)
    let pers_truths_satisfied = persistent_truths.all_it f.gl_eval_prop(K, it) # do (frm : sf_index_t) -> bool:
    let pers_bans_avoided     = persistent_bans.all_it (not f.gl_eval_prop(K, it))
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
        goal = none sf_index_t,
        neg_goal = some C,
        persistent_bans   = persistent_bans + (if goal.is_some(): {goal.get} else: {}),
        persistent_truths = persistent_truths +
          f.boxed_sf * K +
          ((f.boxed_sf * K).map boxD => f[boxD, left]) +
          {boxC} +
          (if neg_goal.is_some(): {neg_goal.get} else: {}),
        lev = lev + 1
      )
    if all_satisfied:
      #echo repeat("  ", lev), "sat:", K
      return true
  #echo repeat("  ", lev), "fail:", gamma0, " @ ", (if goal.is_some: goal.get else: neg_goal.get)
  false


proc sattreegl(f : formula) : bool = sattreegl(f, some f.root, none sf_index_t, {}, {})

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


iterator formulas(length : int, ops = {falsum, verum, conditional, box, diamond}, variables : int = -1) : formula =
  let op0 = {falsum, verum} * ops
  let op1 = {box, diamond, neg} * ops
  let op2 = {rhd, conditional, land, lor} * ops

  let variables = if variables == -1: if op1.card > 0: length div 2 else: 1 else: variables
  let var_syms  = lc[$char(i + ord('a'))  |  (i <- 0..variables-1), string]
  let ar0_syms  = var_syms & lc[($ ft_to_chr x) | (x <- op0), string]
  let ar1_syms  = lc[($ ft_to_chr x) | (x <- op1), string]
  let ar2_syms  = lc[($ ft_to_chr x) | (x <- op2), string]

  # we will build formulas recursively by complexity, saving the previous stages
  var fcache    = @[ ar0_syms ]
  for stage in 2..length:
    var stage_formulas = lc[ (op & f) | (op <- ar1_syms, f <- fcache[stage - 1 - 1]), string ]

    for pstage1 in 1..stage-2:
      let pstage2 = stage - pstage1 - 1
      if pstage2 < pstage1:
        continue
      for op in ar2_syms:
        for f1 in fcache[pstage1 - 1]:
          for f2 in fcache[pstage2 - 1]:
            stage_formulas.add (op & f1 & f2)
            if pstage1 != pstage2:  # skip adding (b, a) if we already have (a, b)
              stage_formulas.add (op & f2 & f1)
    fcache.add stage_formulas

  for stage in fcache:
    for f in stage:
      if superduper f:
        #echo f
        yield from_prefix f


# let fs = @[ "- B-Bpp Bp", "- BDT B#", "- B-pq -BpBq", "p", "Dp", "~- B-Bpp Bp", "~- BDT B#", "~- B-pq -BpBq", "& Bp B~p", "& DT & Bp B~p" ]

#echo sattreegl from_prefix "~BB#"
#quit()

let threads = 1

proc search_job(me, max : int) : int =
  {.gcsafe.}:
    var c = 0
    var t = 0
    for f in formulas(11, ops = {falsum, conditional, box}):
      t += 1
      if t mod max == me:
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
  responses[t] = spawn search_job(t, threads)
echo sum responses.map( x => ^x )
quit()

