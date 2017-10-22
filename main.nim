# usage: <program> n, where n is the length up to which to generate formulas

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

import helpers
import formula
import generator

proc sattreegl(f : formula,
               goal : Option[sf_index_t],
               neg_goal : Option[sf_index_t],
               persistent_bans : set_of_fs,
               persistent_truths : set_of_fs,
               lev : int = 0) : bool =
  let gamma0 = f.boxed_sf + f.prop_sf
  #echo repeat("  ", lev), gamma0, " @ ", (if goal.is_some: goal.get else: neg_goal.get), persistent_truths, persistent_bans
  if persistent_bans * persistent_truths != {} or
    (goal.is_some and goal.get in persistent_bans) or
    (neg_goal.is_some and neg_goal.get in persistent_truths) :
    #echo repeat("  ", lev), "FAILS", persistent_truths, persistent_bans
    return false
  let vargamma0 = gamma0 - persistent_truths - persistent_bans
  for varK in vargamma0.subsets:
    let K = persistent_truths + varK
    let truths = f.extend_forcing(K)
    #echo repeat("  ", lev), K, varK, " out of ", vargamma0
    let goal_satisfied = goal.is_none or goal.get in truths
    let neg_goal_avoided = neg_goal.is_none or neg_goal.get notin truths
    let pers_truths_satisfied = persistent_truths <= truths
    let pers_bans_avoided     = persistent_bans * truths == {}
    #echo repeat("  ", lev), goal_satisfied, neg_goal_avoided, pers_truths_satisfied, pers_bans_avoided
    if not( goal_satisfied and neg_goal_avoided and pers_truths_satisfied and pers_bans_avoided ):
       continue
    let N = f.boxed_sf - K
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
          ((f.boxed_sf * K).map boxD => (f[ ( boxD), left])) +
          {boxC} +
          (if neg_goal.is_some(): {neg_goal.get} else: {}),
        lev = lev + 1
      )
    if all_satisfied:
      #echo repeat("  ", lev), "sat:", K
      return true
  #echo repeat("  ", lev), "fail:", gamma0, " @ ", (if goal.is_some: goal.get else: neg_goal.get)
  false

proc sattreegl(f : formula) : bool = sattreegl(f, some sf_index_t f.root, none sf_index_t, {}, {})







proc sattreeil(f : formula,
               goal : Option[sf_index_t],
               neg_goal : Option[sf_index_t],
               persistent_bans : set_of_fs,
               persistent_truths : set_of_fs,
               lev : int = 0) : bool =
  let gamma0 = f.boxed_sf + f.rhd_sf + f.prop_sf
  #echo repeat("  ", lev), gamma0, " @ ", (if goal.is_some: goal.get else: neg_goal.get), persistent_truths, persistent_bans
  if persistent_bans * persistent_truths != {} or
    (goal.is_some and goal.get in persistent_bans) or
    (neg_goal.is_some and neg_goal.get in persistent_truths) :
    #echo repeat("  ", lev), "FAILS", persistent_truths, persistent_bans
    return false
  let vargamma0 = gamma0 - persistent_truths - persistent_bans
  for varK in vargamma0.subsets:
    let K = persistent_truths + varK
    let truths = f.extend_forcing(K)
    #echo repeat("  ", lev), K, varK, " out of ", vargamma0
    let goal_satisfied = goal.is_none or goal.get in truths
    let neg_goal_avoided = neg_goal.is_none or neg_goal.get notin truths
    let pers_truths_satisfied = persistent_truths <= truths
    let pers_bans_avoided     = persistent_bans * truths == {}
    #echo repeat("  ", lev), goal_satisfied, neg_goal_avoided, pers_truths_satisfied, pers_bans_avoided
    if not( goal_satisfied and neg_goal_avoided and pers_truths_satisfied and pers_bans_avoided ):
       continue
    let N_boxed = f.boxed_sf - K
    let N_rhd   = f.rhd_sf - K
    let I       = f.rhd_sf * K

    if N_boxed == {} and N_rhd == {}:
      #echo repeat("  ", lev), "SUCC"
      return true

    var found_ok_I_for_boxes = false
    for I_witnesses in I.subsets:
      let I_bans = I - I_witnesses
      let pbans = persistent_bans + (if goal.is_some(): { goal.get} else: {}) + I_bans
      let ptruths = persistent_truths +
        f.boxed_sf * K +
        ((f.boxed_sf * K).map boxD => f[boxD, left]) +
        (if neg_goal.is_some(): {neg_goal.get} else: {})
      # TODO: mijenjaj bit oko CrhdD u zabranama
      let ok_negs = N_boxed.all do (boxC : sf_index_t) -> bool:
        let C = f[boxC, left]
        return sattreeil(
          f = f,
          goal = none sf_index_t,
          neg_goal = some C,
          pbans, ptruths + {boxC}, lev + 1)
      let ok_pos = I_witnesses.all do (ErhdG : sf_index_t) -> bool:
        let G = f[ErhdG, right]
        return sattreeil(
          f = f,
          goal = some G,
          neg_goal = none sf_index_t,
          pbans, ptruths, lev + 1)
      if ok_negs and ok_pos:
        found_ok_I_for_boxes = true
        break
    if not found_ok_I_for_boxes:
      continue
    #var created_I_witnesses : set[uint16]  # successful (D, E>G) pairs, neće raditi jer ovisi o drugima EG
    var N_rhd_by_rhs = init_table[sf_index_t, set_of_fs]()
    var Ds : set[sf_index_t]
    for CrhdD in N_rhd:
      let
        C = f[CrhdD, left]
        D = f[CrhdD, right]
      Ds.incl D
      if not N_rhd_by_rhs.hasKeyOrPut(D, {CrhdD}):
        N_rhd_by_rhs[D].incl CrhdD

    let all_satisfied_rhd = Ds.all do (D : sf_index_t) -> bool:
      for I_witnesses in I.subsets:
        let I_bans = I - I_witnesses
        let pbans = persistent_bans + (if goal.is_some(): { goal.get} else: {}) + {D} + I_bans
        let ptruths = persistent_truths +
          f.boxed_sf * K +
          ((f.boxed_sf * K).map boxD => f[boxD, left]) +
          (if neg_goal.is_some(): {neg_goal.get} else: {})
        # TODO: mijenjaj bit oko CrhdD u zabranama
        let ok_negs = N_rhd_by_rhs[D].all do (CrhdD : sf_index_t) -> bool:
          let C = f[CrhdD, left]
          return sattreeil(
            f = f,
            goal = some C,
            neg_goal = none sf_index_t,
            pbans, ptruths + {CrhdD}, lev + 1)
        let ok_pos = I_witnesses.all do (ErhdG : sf_index_t) -> bool:
          let G = f[ErhdG, right]
          return sattreeil(
            f = f,
            goal = some G,
            neg_goal = none sf_index_t,
            pbans, ptruths, lev + 1)
        if ok_negs and ok_pos: return true # this block made it
      false # this block is not satisfiable
    if all_satisfied_rhd:
      #echo repeat("  ", lev), "sat:", K
      return true
  #echo repeat("  ", lev), "fail:", gamma0, " @ ", (if goal.is_some: goal.get else: neg_goal.get)
  false

proc sattreeil(f : formula) : bool = sattreeil(f, some sf_index_t f.root, none sf_index_t, {}, {})


#[
let fs = [  ">pp", "~>pp", ">pq", "~>qp", "- B-pq >pq", "~- B-pq >pq", "~> B-pq >pq", "- >pq - >qr >pr", "~- >pq - >qr >pr",
            "- >ps - >qs >|pq s", "~- >ps - >qs >|pq s", "- >pq -DpDq",
           "&& >Tq DTB~q",
           "-B-TT >TT",
           "~> B>pq >pq"]

for s in fs:
  let f = from_prefix s
  echo f
  #echo repr f
  echo sattreeil f
quit()
]#

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
for v in prefix_formulas(length, ops = {falsum, conditional, rhd, box}):
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
      if sattreeil f:
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

