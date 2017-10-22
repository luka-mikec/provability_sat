# javascript frontend
import dom
import helpers
import formula
# import generator # nim'js backend doesnt support lc, used extensively there

import logic_il

proc check*(sf : cstring) {.exportc.} =
  let f = from_infix ($sf)
  alert(window, cstring ($f & $ (if sattreeil f: " is satisfiable." else: " is not satisfiable.")  ))

  
