module Map

import TOrd
import BoundTree

public export
data Map : (k : Type)
        -> {ord : TOrd k}
        -> (v : Type)
        -> {lower, upper : k}
        -> (cts : BoundTree k {ord} lower upper)
        -> Type
  where

    Empty : (ord : TOrd k) => Map k v Leaf

    Insert : (ord : TOrd k)
          => (key : k)
          -> (value : v)

          -> {ltree : BoundTree k {ord} ll ul}
          -> (lmap  : Map k v ltree)
          
          -> {rtree : BoundTree k {ord} lr ur}
          -> (rmap  : Map k v rtree)
          
          -> {auto 0 lok : ul `LE` key}
          -> {auto 0 rok : key `LE` lr}
          
          -> Map k v (Node ltree key rtree)







