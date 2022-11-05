module Logic

infixr 4 \/
infixr 5 /\

public export
(/\) : Type -> Type -> Type
p /\ q = (p, q)

public export
(\/) : Type -> Type -> Type
p \/ q = Either p q

public export
Decide : Type -> Type
Decide p = (Not p) \/ p
