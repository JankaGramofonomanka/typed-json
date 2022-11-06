module DMap

import Map
import TOrd
import BoundTree

public export
data DMap : {ord : TOrd k}
         -> (f : a -> Type)
         -> {l, u : k}
         -> {keys : BoundTree k {ord} l u}
         -> (m : Map k {ord} a keys)
         -> Type
  where
    Empty : TOrd a
         => {x : a}
         -> DMap {ord} f {l = x, u = x} {keys = Leaf @{ord}} (Empty @{ord})
    
    Insert : (ord : TOrd k)
          => (key : k)
          -> (value : f a)

          -> {ltree : BoundTree k {ord} ll ul}
          -> {lmap  : Map k {ord} v ltree}
          -> (ldmap : DMap {ord} f lmap)
          
          -> {rtree : BoundTree k {ord} lr ur}
          -> {rmap  : Map k {ord} v rtree}
          -> (rdmap : DMap {ord} f rmap)
          
          -> {auto 0 lok : ul `LE` key}
          -> {auto 0 rok : key `LE` lr}
          
          -> DMap {ord} f (Insert @{ord} key a lmap rmap)




