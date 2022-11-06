module BoundTree

import TOrd
import Logic

public export
data BoundTree : (a : Type) -> {ord : TOrd a} -> (lower : a) -> (upper : a) -> Type where
  Leaf : (ord : TOrd a) => BoundTree a {ord} x x
  Node : (ord : TOrd a) 
      
      -- this could be erased with dependent pairs with erased `fst` value
      => {ll, ul : a}
      -> (left : BoundTree a {ord} ll ul)
      -> (middle : a)

      -- this could be erased with dependent pairs with erased `fst` value
      -> {lr, ur : a}
      -> (right : BoundTree a {ord} lr ur)
      
      -> {auto 0 lm : ul `LE` middle}
      -> {auto 0 mr : middle `LE` lr}
      -> BoundTree a {ord} ll ur


trivial : (x = a) \/ (x = x)
trivial = Right Refl

public export
insert : (ord : TOrd a)
      => {0 l, u : a}
      -> (x : a)
      -> BoundTree a {ord} l u
      -> (lower ** upper ** (BoundTree a {ord} lower upper, (upper = x) \/ (upper = u), (lower = x) \/ (lower = l)))

insert x Leaf = (x ** x ** (Node Leaf x Leaf {lm = xlex} {mr = xlex}, Left Refl, Left Refl))

insert {l} {u} x (Node left middle right {lm} {mr}) = case x `cmp` middle of

  Case1 xltm => let (lower ** upperL ** (newLeft, prfU, prfL)) = insert x left
                    
                    0 upperLLEmiddle : upperL `LE` middle
                    upperLLEmiddle = case prfU of
                      Left  Refl {- upperL = x -}   => ltle xltm
                      Right Refl {- upperL = ul -}  => lm

                in (lower ** u ** (Node newLeft middle right {lm = upperLLEmiddle} {mr}, trivial, prfL))
  
  Case2 xeqm => (l ** u ** (Node left middle right {lm} {mr}, trivial, trivial))
  
  Case3 xgtm => let (lowerR ** upper ** (newRight, prfU, prfL)) = insert x right

                    0 middleLElowerR : middle `LE` lowerR
                    middleLElowerR = case prfL of
                      Left  Refl {- lowerR = x -}   => (ltle . gtlt) xgtm
                      Right Refl {- lowerR = lr -}  => mr

                in (l ** upper ** (Node left middle newRight {lm} {mr = middleLElowerR}, prfU, trivial))
  
