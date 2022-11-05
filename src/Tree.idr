module Tree

import Data.So


infixr 4 \/
infixr 5 /\
infix 6 `EQ`, `LT`, `GT`, `LE`, `GT`

(/\) : Type -> Type -> Type
p /\ q = (p, q)

(\/) : Type -> Type -> Type
p \/ q = Either p q

namespace TOrd

  public export
  Relation : Type -> Type
  Relation a = a -> a -> Type


  export
  interface TOrd a where
    LT : Relation a
    lt : a -> a -> Bool
    le : a -> a -> Bool
    
    ltLT : {x, y : a} -> So (x `lt` y) -> x `LT` y
    

  export
  GT : TOrd a => Relation a  
  GT x y = LT x y -> Void

  export
  EQ : TOrd a => Relation a
  EQ = Equal

  export
  GE : TOrd a => Relation a

  export
  LE : TOrd a => Relation a
  x `LE` y = x `EQ` y \/ x `LT` y

  export
  eqle : TOrd a => {x, y : a} -> x = y -> x `LE` y
  eqle Refl = Left Refl

  

  public export
  implementation TOrd Integer where
    x `LT` y = So (x < y)
    lt = (<)
    le = (<=)
    ltLT prf = prf




namespace BoundTree
  public export
  data BoundTree : (a : Type) -> {ord : TOrd a} -> (lower : a) -> (upper : a) -> Type where
    Leaf : (ord : TOrd a) => BoundTree a {ord} x x
    Node : (ord : TOrd a) => (left : BoundTree a {ord} ll ul)
                          -> (middle : a)
                          -> (right : BoundTree a {ord} lr ur)
                          -> {auto 0 lok : ul `LE` middle}
                          -> {auto 0 rok : middle `LE` lr}
                          -> BoundTree a {ord} ll ul
  
namespace Map
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

