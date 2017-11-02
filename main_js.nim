# javascript frontend
import dom
import helpers
import formula
# import generator # nim'js backend doesnt support lc, used extensively there

import logic_il
import logic_ilw
import logic_ilp

include principles

proc get_principles*() : type(all_principles) {.exportc.} =
  return all_principles

proc check*(sf : cstring, logic : cstring) {.exportc.} =
  let f = from_infix ($sf)
  let result : bool =
    if   $logic == "il":
      sattreeil  f
    elif $logic == "ilw":
      sattreeilw f
    elif $logic == "ilp":
      sattreeilp f
    else:
      (alert("not implemented!"); false)
  alert(window, cstring ($f & $ (if result: " is satisfiable." else: " is not satisfiable.")  ))




