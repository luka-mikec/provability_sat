# javascript frontend
import dom
import helpers
import formula
import sugar
import sequtils
# import generator # nim'js backend doesnt support lc, used extensively there

import logic_il
import logic_ilw
import logic_ilp
import logic_ilm

include principles

proc get_principles*() : seq[cstring] {.exportc.} =
  return all_principles.map(str => (cstring)str)

proc check*(sf : cstring, logic : cstring) {.exportc.} =
  let f = from_infix($sf, $logic == "ilm")
  let result : bool =
    if   $logic == "il":
      sattreeil  f
    elif $logic == "ilw":
      sattreeilw f
    elif $logic == "ilp":
      sattreeilp f
    elif $logic == "ilm":
      sattreeilm f
    else:
      (alert("not implemented!"); false)
  alert(window, cstring ($f & $ (if result: " is satisfiable." else: " is not satisfiable.")  ))




