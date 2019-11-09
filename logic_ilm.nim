import options

import helpers
import math
import sugar
import tables
import formula
import strutils
import sets

import sequtils

type
  quad = tuple[I: set_of_sfs, F: set_of_sfs]
  sattreeilm_args = tuple[goal: sf_index_t,
                          ancestry: seq[quad],
                          avail_witnesses: set_of_sfs,
                          boxes: set_of_sfs]

var debug_print = 0 # 0 none, 1 some, 2 all
var cache_print = 0 # 0 none, 1 all

var m_calls* = 0
var m_calls_i* = 0
var m_calls_n* = 0

include sets
var cache_true : HashSet[sattreeilm_args]
var cache_false : HashSet[sattreeilm_args]
var cache_max_len_data : int = 16777216 # this is ok for native with ~5GB RAM free
const use_cache = true

when defined(js):
  var js_output* : cstring = ""
  proc print(a: varargs[string, `$`]) : void =
    for el in a:
      js_output &= (cstring)($el)

  proc println(a: varargs[string, `$`]) : void =
    for el in a:
      js_output &= (cstring)($el)
    js_output &= (cstring)"\n"

when not defined(js):
  proc print(a: varargs[string, `$`]) : void =
    stdout.write(a)
    flushFile(stdout)

  proc println(a: varargs[string, `$`]) : void =
    stdout.write(a)
    stdout.write("\n")
    flushFile(stdout)


proc sattreeilm*(f : formula,
                 goal : sf_index_t,
                 ancestry : seq[quad],
                 avail_witnesses : set_of_sfs, # available if bans_for_succ remains the same
                 boxes : set_of_sfs,
                 lev : int = 0,
                 is_N_call : bool = true) : bool =
  result = false

  if cache_print > 0 and (m_calls mod 1000000 == 0):
    print(m_calls)
    when use_cache:
      print(len(cache_true.data), ' ', len(cache_false.data), ' ', len(cache_true),' ', len(cache_false))

  m_calls += 1
  if is_N_call:
    m_calls_n += 1
  else:
    m_calls_i += 1

  #if m_calls > 50:
  #  quit(5)

  if debug_print > 0:
    println repeat("  ", lev) & "modelling ", sf_to_str(f, f.ast[goal]), " is N: ", is_N_call, " height: ", len(ancestry)

  let
    what_mcs_should_not_be  : set_of_sfs = ancestry.map(anc => anc.F).foldl(a + b, set_of_sfs({}))
    boxed_not_goal : sf_index_t = f.boxnot.getOrDefault(goal, f.boxed_not_root)

  if goal in what_mcs_should_not_be:
    if debug_print > 1:
      println repeat("  ", lev) & "false, goal in what goal should not be: "
      for sf in what_mcs_should_not_be:
        print repeat("  ", lev) & "mcs: " & sf_to_str(f, f.ast[sf]) &  "   "
      println ""
    when use_cache:
      let cache_args : sattreeilm_args = (goal: goal, ancestry: ancestry, avail_witnesses: avail_witnesses, boxes: boxes)
      if not (len(cache_false.data) >= cache_max_len_data and mustRehash(len(cache_false.data), cache_false.counter)):
        cache_false.incl cache_args
    return false

  when use_cache:
    let cache_args : sattreeilm_args = (goal: goal, ancestry: ancestry, avail_witnesses: avail_witnesses, boxes: boxes)
    if cache_args in cache_false:
      return false
    if cache_args in cache_true:
      return true

  let
    gamma0 = #[ f.boxed_sf + ]# f.rhd_sf + f.prop_sf
    # boxed are rhd's, co can be added later while remaining MBCS
    vargamma0 = gamma0 - what_mcs_should_not_be - boxes - {boxed_not_goal}

  when defined(js):
    var varK_ind : int = 0
  when not defined(js):
    var varK_ind : uint64 = 0

  when use_cache:
    if debug_print > 1: # and lev == 0
      println repeat("  ", lev) & "gamma things to check:" & $vargamma0.card
  for varK in vargamma0.subsets_fast_unsorted(prefer_smaller = false):
    varK_ind += 1
    if debug_print > 0:
      if lev == 0:
        for sf in varK:
            print sf_to_str(f, f.ast[sf]) & "  :  "
        println ""


    when use_cache:
      if lev == 0:
        if len(cache_false.data) >= cache_max_len_data :
          println "clearing cache..."
          cache_false.init()
          println "cleared"
        if len(cache_true.data) >= cache_max_len_data :
          println "clearing cache..."
          cache_true.init()
          println "cleared"
        if cache_print > 0 and varK_ind mod 1000000 == 0:
          println "varK_ind:", varK_ind


    # elim iz igre boxeve, boxeve odmah na početku prije N, i boxevi moraju bit nadskup zabrana
    let K = varK + boxes + { boxed_not_goal }
    let truths = f.extend_forcing(K * gamma0)
    #println repeat("  ", lev), K, varK, " out of ", vargamma0
    let goal_satisfied = goal in truths
    let mcs_is_ok = what_mcs_should_not_be * truths == {} #  and  falsum notin truths
    if debug_print > 0:
      println repeat("  ", lev), "truths: "
      for sf in truths:
        print repeat("  ", lev) & sf_to_str(f, f.ast[sf]) &  "   "
      println ""
    if not( goal_satisfied and mcs_is_ok ):
      if debug_print > 1:
        println repeat("  ", lev) & "false (goal not satisifed or mcs not ok):"
        for sf in what_mcs_should_not_be * truths:
          print repeat("  ", lev) & "intersects: " & sf_to_str(f, f.ast[sf]) &  "   "
          for ind, anc in ancestry:
            if sf in anc.F:
              print("at ", ind)
        println ""

      continue # to next MBCS
    let N_rhd   = f.rhd_sf - K
    let I       = f.rhd_sf * K

    if debug_print > 1:
      println repeat("  ", lev), "N_rhd: "
      for sf in N_rhd:
        print repeat("  ", lev) & sf_to_str(f, f.ast[sf]) &  "   "
      println ""

    if N_rhd == {}:
      discard # with ILM, still have to eliminate deficiencies

    # ovo je samo optimizacija: prvo boxeve (tj. D > #) sredimo (može li se to dodat u F_i? (vj. da) ili elim F_i (vj. ne)?)
    var boxed_of_old_I : set_of_sfs = {}
    var do_break = false
    for i, anc in ancestry:
      for ErhdG in anc.I:
        let
          E = f[ErhdG, left]
          G = f[ErhdG, right]

        if sf_type(f.ast[G]) == falsum:
          if E in truths:
            do_break = true
            break
          if debug_print > 1:
            println "navodno: ", sf_to_str(f, f.ast[ErhdG]), " ", sf_to_str(f, f.ast[G]),  " ", sf_get(f.ast[E], content),
                 " ", sf_get(f.ast[G], content), " ", sf_get(f.ast[G], content), " ",
                 falsum, " ", sf_type(E), " ", sf_type(G)
          boxed_of_old_I.incl E
      if do_break:
        break
    if do_break:
      continue # to next MBCS

    do_break = false # well, obviously it is :D

    var
      boxed_of_new_I : set_of_sfs = {}
      boxes_of_new_I : set_of_sfs = {}

    for ErhdG in I:
      let
        E = f[ErhdG, left]
        G = f[ErhdG, right]

      if sf_type(f.ast[G]) == falsum:
        boxed_of_new_I.incl E
        boxes_of_new_I.incl ErhdG

    let old_call_bound = boxes == boxes_of_new_I
    if old_call_bound:
      # bound call means I can use avail_witnesses, but also my goal should not be available
      # (otherwise we might have a super-polynomial/even infinite loop of bound goals)
      if goal in avail_witnesses:
        # this should be impossible to reach
        println "IMPOSSIB"
        quit(1000)

    let Ns_satisfied = N_rhd.all do (CrhdD : sf_index_t) -> bool:
      let
        C = f[CrhdD, left]
        D = f[CrhdD, right]
      return sattreeilm(f,
        C,
        ancestry.concat @[(I: I, F: boxed_of_new_I + {goal, D})], # boxed_of_new_I redundant, but optimizes
        {},
        boxes_of_new_I,
        lev + 1
      )

    if not Ns_satisfied:
      if debug_print > 1:
        println repeat("  ", lev) & "false (some N not sat)"
      continue

    let
      traditional = old_call_bound
      a_last_i : int = len(ancestry) - 1

    var Is_satisfied = true
    for i, anc in ancestry:
      for ErhdG in anc.I:
        let
          E = f[ErhdG, left]
          G = f[ErhdG, right]
        if E in truths and G notin truths and not(traditional and i == a_last_i and G in avail_witnesses):
          Is_satisfied = Is_satisfied and  sattreeilm(f,
            G,
            if len(ancestry) > 0:
              ancestry[0..i]
            else:
              @[],
            if i == len(ancestry) - 1: avail_witnesses + truths else: {}, # ljepse avail_witnesses + truths (bilo + {goal})
            boxes_of_new_I,
            lev + 1,
            false
          )

    if not Is_satisfied:
      if debug_print > 1:
        println repeat("  ", lev) & "false (some I not sat)"
      continue
    else:
      if debug_print > 1:
        println repeat("  ", lev) & "true (non-trivial)"
      when use_cache:
        if not (len(cache_true.data) >= cache_max_len_data and mustRehash(len(cache_true.data), cache_true.counter)):
          cache_true.incl cache_args
      return true
  when use_cache:
    if not (len(cache_false.data) >= cache_max_len_data and mustRehash(len(cache_false.data), cache_false.counter)):
      cache_false.incl cache_args

proc sattreeilm*(f : formula) : bool =
  when use_cache:
    cache_false.clear()
    cache_true.clear()
  m_calls = 0
  m_calls_i = 0
  m_calls_n = 0
  return sattreeilm(f, sf_index_t f.root, @[], {}, {  #[f.boxed_not_root]#  }, 0)

