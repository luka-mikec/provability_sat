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
  km1 = "(p > Dq) -> B(p -> Dq)"
  km2 = "(p > q) -> (B(q -> Ds) -> B(p -> Ds))"
  kw1 = "(p > DT) -> (T > ~p)"
  kw10 = "((p & q) > Dp) -> (p > (p & ~q))"

  kw2 = "(p > Dq) -> (q > (q & ¬p))"
  kw3 = "(p > (q | Dp)) -> (p > q)"
  kw4 = "(p > q) -> (q > (q & B¬p))"
