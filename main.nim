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


#[
let fs = [  "- B-Bpp Bp", "- BDT B#", "- B-pq -BpBq", "p", "Dp", "~- B-Bpp Bp", "~- BDT B#", "~- B-pq -BpBq", "& Bp B~p", "& DT & Bp B~p",
            ">pp", "~>pp", ">pq", "~>qp", "- B-pq >pq", "~- B-pq >pq", "~> B-pq >pq", "- >pq - >qr >pr", "~- >pq - >qr >pr",
            "- >ps - >qs >|pq s", "~- >ps - >qs >|pq s", "- >pq -DpDq","&& >Tq DTB~q", "-B-TT >TT", "~> B>pq >pq",
            ]

for s in fs:
  let f = from_prefix s
  echo f
  #echo repr f
  echo sattreeil f
quit()
]#

let frm = from_infix "(p > q) -> (~(p > ~c) > (q & Bc))" #
#let frm = from_infix "~(~(T > p) > #)" # (p > q) &
echo repr frm
echo sattreeil frm

quit()

let threads = 4


var length = case param_count():
  of 0: 5
  else: parse_int(param_str(1))
echo "generating formulas up to length ", length

var fstrs = lc[ initSinglyLinkedList[string]()  |  (i <- 1..threads), SinglyLinkedList[string] ]

var choose_goose = 0
for v in prefix_formulas(length, ops = {falsum, conditional, rhd, box}):
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
        c += int sattreeil f
      # highscore[duration] = sf  # TODO: make thread safe
    echo c, "/", t
    (c, t)


echo "total time: ", stopwatch do:
  var responses = new_seq[FlowVar[job_res]](threads)
  for t in 0..threads-1:
    responses[t] = spawn search_job(t, threads, length)
  echo sum responses.map( x => (^x).s )
  echo sum responses.map( x => (^x).t )


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
]#

quit()

