import sequtils
import future

import formula
import logic_ilp

include principles


let
  taut = [gl, k4, k, j1, j2, j3, j4, j5, w, f, kw1, kw10, kw2, kw3, kw4, p, wx, p0, r, r1, m0, ipm]
  cont = [m, km1, km2] # TODO: are these really not provable in P?
  should_true  = @taut & @cont & @cont.map (x => "~(" & x & ")")
  should_false = @taut.map (x => "~(" & x & ")")

for f in should_true:
  let frm = from_infix f
  echo frm
  echo sattreeilp frm

for f in should_false:
  let frm = from_infix f
  echo frm
  echo (not sattreeilp frm)

echo "all test ok: ", should_true.all_it (sattreeilp from_infix it) and should_false.all_it(not sattreeilp from_infix it)
