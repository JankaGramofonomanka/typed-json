module TOrd

import Data.So

import Logic

infix 6 `EQ`, `LT`, `GT`, `LE`, `GT`


public export
Relation : Type -> Type
Relation a = a -> a -> Type

export
interface TOrd a where
  EQ : Relation a
  
  LT : Relation a
  LE : Relation a

  GT : Relation a
  GE : Relation a
  

  eq : (x : a) -> (y : a) -> Decide (x `EQ` y)

  le : (x : a) -> (y : a) -> Decide (x `LE` y)
  lt : (x : a) -> (y : a) -> Decide (x `LT` y)
  ge : (x : a) -> (y : a) -> Decide (x `GE` y)
  gt : (x : a) -> (y : a) -> Decide (x `GT` y)

  
  0 equalEQ : {x : a} -> x `EQ` x

  0 eqle : {x, y : a} -> x `EQ` y -> x `LE` y
  0 ltle : {x, y : a} -> x `LT` y -> x `LE` y
  
  0 eqge : {x, y : a} -> x `EQ` y -> x `GE` y
  0 gtge : {x, y : a} -> x `GT` y -> x `GE` y
  
  
  0 nlegt : {x, y : a} -> Not (x `LE` y) -> x `GT` y
  0 gtnle : {x, y : a} -> x `GT` y -> Not (x `LE` y)

  0 ngelt : {x, y : a} -> Not (x `GE` y) -> x `LT` y
  0 ltnge : {x, y : a} -> x `LT` y -> Not (x `GE` y)

  0 lege : {x, y : a} -> x `LE` y -> y `GE` x
  0 ltgt : {x, y : a} -> x `LT` y -> y `GT` x
  0 gele : {x, y : a} -> y `GE` x -> x `LE` y
  0 gtlt : {x, y : a} -> y `GT` x -> x `LT` y
  




export
0 xlex : (ord : TOrd a) => {x : a} -> x `LE` x
xlex {x = x} = eqle @{ord} {x = x, y = x} equalEQ

export
0 xgex : (ord : TOrd a) => {x : a} -> x `GE` x
xgex {x = x} = eqge @{ord} {x = x, y = x} equalEQ


public export
implementation TOrd Integer where

  x `EQ` y = So (x == y)
  
  x `LT` y = So (x < y)
  x `LE` y = So (x <= y)

  x `GT` y = So (x > y)
  x `GE` y = So (x >= y)
  

  x `eq` y with (x == y)
    x `eq` y | True   = Right Oh
    x `eq` y | False  = Left (\x => case x of {})

  x `le` y with (x <= y)
    x `le` y | True   = Right Oh
    x `le` y | False  = Left (\x => case x of {})
  
  x `lt` y with (x < y)
    x `lt` y | True   = Right Oh
    x `lt` y | False  = Left (\x => case x of {})

  x `ge` y with (x >= y)
    x `ge` y | True   = Right Oh
    x `ge` y | False  = Left (\x => case x of {})
  
  x `gt` y with (x > y)
    x `gt` y | True   = Right Oh
    x `gt` y | False  = Left (\x => case x of {})

  
  -- TODO this should have proofs somewhere
  equalEQ = believe_me ()

  eqle = believe_me ()
  ltle = believe_me ()
  
  eqge = believe_me ()
  gtge = believe_me ()
  
  
  nlegt = believe_me ()
  gtnle = believe_me ()

  ngelt = believe_me ()
  ltnge = believe_me ()

  lege = believe_me ()
  ltgt = believe_me ()
  gele = believe_me ()
  gtlt = believe_me ()
  
