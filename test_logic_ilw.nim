import sequtils
import future

import formula
import logic_ilw

include principles


let
  taut = [gl, k4, k, j1, j2, j3, j4, j5, w, f, kw1, kw10, kw2, kw3, kw4]
  cont = [m, m0, p, wx, p0, km1, km2, r, ipm] # r1 should be here, but too slow
  should_true  = @taut & @cont & @cont.map(x => "~(" & x & ")")
  should_false = @taut.map(x => "~(" & x & ")")

for f in should_true:
  let frm = from_infix f
  echo f, frm
  echo sattreeilw frm
echo "\n"
for f in should_false:
  let frm = from_infix f
  echo f, frm
  echo (not sattreeilw frm)

echo "all test ok: ", should_true.all_it(sattreeilw from_infix it) and should_false.all_it(not sattreeilw from_infix it)
