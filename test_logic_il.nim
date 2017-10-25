import sequtils
import future

import formula
import logic_il

let # axioms of IL
  gl = "B(Bp -> p) -> Bp"
  k5 = "Bp -> BBp"
  k  = "B(p -> q) -> (Bp -> Bq)"
  j1 = "B(p -> q) -> (p > q)"
  j2 = "(p > q) -> ((q > s) -> (p > s))"
  j3 = "((p > s) & (q > s)) -> ((p | q) > s)"
  j4 = "(p > q) -> (Dp -> Dq)"
  j5 = "Dp > p"

let # extensions
  m  = "(p > q) -> ((p & Bs) > (q & Bs))"
  m0 = "(p > q) -> ((Dp & Bs) > (q & Bs))"
  p  = "(p > q) -> B(p > q)"
  f  = "(p > Dp) -> B~p"
  w  = "(p > q) -> (p > (q & B~p))"
  wx = "(p > q) -> ((p & Bs) > ((q & B~p) & Bs))"
  p0 = "(p > Dq) -> B(p > q)"
  r  = "(p > q) -> (~(p > ~c) > (q & Bc))"
  r1 = "(p > q) -> ((~(p > ~c) & (x > Dy)) > ((q & Bc) & (x > y)))"

let
  taut = [gl, k5, k, j1, j2, j3, j4, j5]
  cont = [m, m0, p, f, w, wx, p0, r, r1]
  should_true  = @taut & @cont & @cont.map (x => "~(" & x & ")")
  should_false = @taut.map (x => "~(" & x & ")")

for f in should_true:
  let frm = from_infix f
  echo frm
  echo sattreeil frm

for f in should_false:
  let frm = from_infix f
  echo frm
  echo (not sattreeil frm)

echo "all test ok: ", should_true.all_it (sattreeil from_infix it) and should_false.all_it(not sattreeil from_infix it)
