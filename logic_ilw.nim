import options

import helpers
import math
import future
import tables
import formula
import strutils

# bitset supports up to 8 rhds

# helper procs for working with visibility graphs
proc `[]`(x : int64, i : int) : bool = (x shr i) mod 2 == 1
proc `[]`(x : int64, n : int, i : int, j : int) : bool = (x shr (n*i + j)) mod 2 == 1
proc get_row(x : int64, i : int, n : int) : int64 = (x shr (i*n)) mod (2 ^ n)
proc `[]=`(x : var int64, n : int, i : int, j : int, b : bool) : void =
  if x[n, i, j] and not b   or   not x[n, i, j] and b:
    x = x xor (1 shl (n*i + j))
proc transc(a : var int64, n : int) : void =
  for k in 0..n-1:
    for i in 0..n-1:
      for j in 0..n-1:
        a[n, i, j] = a[n, i, j] or (a[n, i, k] and a[n, k, j])
proc transpose(a : int64, n : int) : int64 =
  for i in 0..n-1:
    for j in 0..n-1:
      result[n, i, j] = a[n, j, i]
proc is_trans(a : int64, n : int) : bool =
  for k in 0..n-1:
    for i in 0..n-1:
      if i == k: continue
      for j in 0..n-1:
        if not a[n, i, j] and a[n, i, k] and a[n, k, j]:
          return false
  return true
iterator loop(a : int64, n : int, i : int) : int =
  for j in 0..n-1:
    if a[n, i, j] and a[n, j, i]:
      yield j
proc unary_bit_mat(n : int) : int64 =
  for i in 0..n-1:
    result[n, i, i] = true
iterator rt_bit_mats(n : int) : int64 =
  for seed in 0..2^((n-1)*n)-1:
    var nmat = unary_bit_mat(n)
    var it = 0
    for i in 0..n-1:
      for j in 0..n-1:
        if i == j: continue
        nmat[n, i, j] = seed[it]
        it += 1
    #transc(nmat, n)
    if is_trans(nmat, n):
      yield nmat


#[
let n = 5
var i = 0
for m in rt_bit_mats(n):
  i += 1
  for i in 0..n-1:
    for j in 0..n-1:
      discard 5
      #stdout.write int m[n, i, j], " "
    #echo ""
  #echo "---"
echo i
]#

proc sattreeilw*(f : formula,
               goal : Option[sf_index_t],
               neg_goal : Option[sf_index_t],
               persistent_bans : set_of_fs,
               persistent_truths : set_of_fs,
               delayed_bans : set_of_fs,
               lev : int = 0) : bool =
  let gamma0 = f.boxed_sf + f.rhd_sf + f.prop_sf
  ###echo repeat("  ", lev), gamma0, " @ ", (if goal.is_some: goal.get else: neg_goal.get), persistent_truths, persistent_bans, delayed_bans
  if persistent_bans * persistent_truths != {} or
    (goal.is_some and goal.get in persistent_bans) or
    (neg_goal.is_some and neg_goal.get in persistent_truths) :
    ###echo repeat("  ", lev), "FAILS", persistent_truths, persistent_bans
    return false
  let vargamma0 = gamma0 - persistent_truths - persistent_bans
  for varK in vargamma0.subsets(prefer_smaller = false):
    let K = persistent_truths + varK
    ##
    #if lev == 0 and (byte2 notin K or byte5 in K or byte9 in K or byte7 in K):
    #  continue

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
    ###echo repeat("  ", lev), "pass variant ", "I=", I, " Nrhd=", N_rhd, " Nb=", N_boxed, " Delayed=", delayed_bans

    if N_boxed == {} and N_rhd == {}:
      ###echo repeat("  ", lev), "SUCC"
      return true

    let base_pbans = persistent_bans + (if goal.is_some(): { goal.get} else: {}) + delayed_bans
    let base_pthruths = persistent_truths +
      f.boxed_sf * K +
      ((f.boxed_sf * K).map boxD => f[boxD, left]) +
      (if neg_goal.is_some(): {neg_goal.get} else: {})
    var found_ok_I_for_boxes = false
    for I_witnesses in I.subsets(prefer_smaller = true):
      ###echo repeat("  ", lev), "variant witnesses: ", I_witnesses
      for visibility in rt_bit_mats(I_witnesses.card):
        let visibility_t = transpose(visibility, I_witnesses.card)
        let bivisibility = visibility and visibility_t
        ###echo repeat("  ", lev), "var visi: ", to_bin(visibility, 16), " ", to_bin(bivisibility, 16)
        let I_bans = I - I_witnesses
        let pbans = base_pbans + (I_bans.map CrhdD => f[CrhdD, left])
        let ptruths = base_pthruths
        # TODO: mijenjaj bit oko CrhdD u zabranama
        let ok_negs = N_boxed.all do (boxC : sf_index_t) -> bool:
          let C = f[boxC, left]
          ###echo repeat("  ", lev), "call[]part, base ", C
          return sattreeilw(f, goal = none sf_index_t, neg_goal = some C, pbans, ptruths + {boxC}, {}, lev + 1)
        var index = 0
        let ok_pos = I_witnesses.all do (ErhdG : sf_index_t) -> bool:
          let G = f[ErhdG, right]
          index += 1
          ###echo index
          var visibility_bans  = (I_witnesses - bitset_to_set(get_row(visibility, index - 1, I_witnesses.card), I_witnesses)).map HrhdJ => f[HrhdJ, left]
          var new_delayed_bans = bitset_to_set(get_row(bivisibility, index - 1, I_witnesses.card), I_witnesses).map HrhdJ => f[HrhdJ, left]
          ###echo repeat("  ", lev), "call[]part, svjedoci ", G, " ", "vb: ", visibility_bans, " new db: ", new_delayed_bans, " bstoset ", bitset_to_set(get_row(visibility, index - 1, I_witnesses.card), I_witnesses), " ", visibility, " ", index - 1, " ", I_witnesses.card, " ", get_row(visibility, index - 1, I_witnesses.card), " "
          return sattreeilw(f, goal = some G, neg_goal = none sf_index_t, pbans + visibility_bans, ptruths, new_delayed_bans, lev + 1)
        if ok_negs and ok_pos:
          ###echo repeat("  ", lev), "calls satisfied"
          found_ok_I_for_boxes = true
          break
      if found_ok_I_for_boxes:
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
      #echo repeat("  ", lev), "za ", D
      let base_D_pbans = base_pbans + {D}
      for I_witnesses in I.subsets(prefer_smaller = false):
        for visibility in rt_bit_mats(I_witnesses.card):
          let visibility_t = transpose(visibility, I_witnesses.card)
          let bivisibility = visibility and visibility_t
          let I_bans = I - I_witnesses
          let pbans = base_D_pbans + (I_bans.map CrhdD => f[CrhdD, left])
          let ptruths = base_pthruths
          #echo repeat("  ", lev), I_witnesses, " pb ", base_D_pbans, I_bans, " pt ", ptruths
          # TODO: mijenjaj bit oko CrhdD u zabranama
          let ok_negs = N_rhd_by_rhs[D].all do (CrhdD : sf_index_t) -> bool:
            let C = f[CrhdD, left]
            return sattreeilw(f, goal = some C, neg_goal = none sf_index_t, pbans, ptruths + {CrhdD}, {}, lev + 1)
          var index = 0
          let ok_pos = I_witnesses.all do (ErhdG : sf_index_t) -> bool:
            let G = f[ErhdG, right]
            index += 1
            var visibility_bans  = (I_witnesses - bitset_to_set(get_row(visibility, index - 1, I_witnesses.card), I_witnesses)).map HrhdJ => f[HrhdJ, left]
            var new_delayed_bans = bitset_to_set(get_row(bivisibility, index - 1, I_witnesses.card), I_witnesses).map HrhdJ => f[HrhdJ, left]
            return sattreeilw(f, goal = some G, neg_goal = none sf_index_t, pbans + visibility_bans, ptruths, new_delayed_bans, lev + 1)
          if ok_negs and ok_pos: return true # this block made it
      false # this block is not satisfiable
    if all_satisfied_rhd:
      #echo repeat("  ", lev), "sat:", K
      return true
  ###echo repeat("  ", lev), "fail:", gamma0, " @ ", (if goal.is_some: goal.get else: neg_goal.get)
  false

proc sattreeilw*(f : formula) : bool = sattreeilw(f, some sf_index_t f.root, none sf_index_t, {}, {}, {})


