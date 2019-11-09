import sequtils
import future

import formula
import logic_ilm

include principles


let
  taut = [gl, k4, k, j1, j2, j3, j4, j5, w, f, kw1, kw10, kw2, kw3, kw4,
    m, m0, p0, wx, km1, km2, r, ipm # add r1 if you have a few days to spare...
  ]
  cont = [p]
  should_true  = @taut & @cont & @cont.map(x => "~(" & x & ")")
  should_false = @taut.map(x => "~(" & x & ")")

for f in should_true:
  let frm = from_infix(f, true)
  echo f, frm
  echo sattreeilm frm
echo "\n"

for f in should_false:
  let frm = from_infix(f, true)
  echo f, frm
  echo (not sattreeilm frm)
