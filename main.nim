# usage: <program> n, where n is the length up to which to generate formulas

import unsigned
import math
import sets
import tables
import strutils
import typetraits
import sequtils
import options
import future
import lists
import threadpool
import times
import algorithm
import os
import parseutils

import helpers
import formula
import generator

import logic_il
import logic_ilw


#[
let f = from_infix "(T > DT) & DT"   # "((T > T) > T) & ~[] #"
echo repr f
echo sattreeil f
echo sattreeilw f
quit()
]#


let threads = 4

var length = case param_count():
  of 0: 8
  else: parse_int(param_str(1))
echo "generating formulas up to length ", length

var fstrs = lc[ initSinglyLinkedList[string]()  |  (i <- 1..threads), SinglyLinkedList[string] ]

var choose_goose = 0
for v in prefix_formulas(length, ops = {rhd, box, conditional, neg}, 2):
  fstrs[choose_goose].prepend v
  choose_goose = (choose_goose + 1) mod threads

echo "generated."

#var highscore = init_table[float, string]()
type job_res = tuple[s : int, t : int]

proc search_job(me, max, length : int) : job_res =
  {.gcsafe.}:
    var c = 0
    var t = 0
    for sf in fstrs[me]:
      let f = from_prefix sf
      t += 1
      let duration = stopwatch do:
        c += int sattreeilw f
        #if (sattreeil f) and (not sattreeilw f):
        #  echo f
      # highscore[duration] = sf  # TODO: make thread safe
    echo c, "/", t
    (c, t)


echo "total time: ", stopwatch do:
  var responses = new_seq[FlowVar[job_res]](threads)
  for t in 0..threads-1:
    responses[t] = spawn search_job(t, threads, length)
  echo "satisfiable: ", sum responses.map( x => (^x).s )
  echo "total tested: ", sum responses.map( x => (^x).t )


#[
echo "total time:", stopwatch do:
  let stotal, total = search_job(0, threads, length)

  var i = 0
  var sorted_hs = to_seq highscore.keys()
  sort(sorted_hs, system.cmp[float])
  for sfr in sorted_hs:
    let f = from_prefix highscore[sfr]
    echo sfr, " : ", f
    if i > 10:
      break
  echo total



let frm = from_infix "(p > q) -> (~(p > ~c) > (q & Bc))" #
#let frm = from_infix "~(~(T > p) > #)" # (p > q) &
echo repr frm
echo sattreeil frm

quit()

]#

quit()

