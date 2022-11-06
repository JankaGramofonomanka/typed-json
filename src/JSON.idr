module JSON

import Map
import DMap
import TOrd
import BoundTree

data JType
  = TNull
  | TBool
  | TInt
  | TString
  | TArr (List JType)
  | TObj (Map String JType keys)



data DList : (f : a -> Type) -> (l : List a) -> Type where
  Nil : DList f Nil
  (::) : {t : a} -> f t -> DList f ts -> DList f (t :: ts)


data TJson : JType -> Type where
  TJNull    :                      TJson TNull
  TJBool    : Bool              -> TJson TBool
  TJInt     : Int               -> TJson TInt
  TJString  : String            -> TJson TString
  TJArr     : DList TJson ts    -> TJson (TArr ts)
  TJObj     : DMap TJson schema -> TJson (TObj schema)





