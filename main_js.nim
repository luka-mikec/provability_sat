# javascript frontend
import dom
import helpers
import formula
# import generator # nim'js backend doesnt support lc, used extensively there

import logic_il
import logic_ilw

proc check*(sf : cstring, logic : cstring) {.exportc.} =
  let f = from_infix ($sf)
  let result : bool =
    if   $logic == "il":
      sattreeil  f
    elif $logic == "ilw":
      sattreeilw f
    else:
      (alert("not implemented!"); false)
  alert(window, cstring ($f & $ (if result: " is satisfiable." else: " is not satisfiable.")  ))




