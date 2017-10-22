import lists
import times

proc stopwatch*( f : proc  ) : float =
  result = cpu_time()
  f()
  return cpu_time() - result

# some additional methods for the built-in types
iterator subsets*[T](s : set[T], prefer_smaller : bool = true) : set[T] =
  var subset : set[T]
  let m = 2^s.card - 1
  for ii in 0 .. m:
    let i = case prefer_smaller
      of true:  ii
      of false: m - ii
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
