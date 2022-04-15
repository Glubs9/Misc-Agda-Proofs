data forall (A : Set) (B : A -> Set) : Set where
    dfun : ((a : A) -> B a) -> forall A B

data exists (A : Set) (B : A -> Set) : Set where
    [_,_] : (a : A) -> B a -> exists A B

data _==_ {A : Set} : A -> A -> Set where
    refl : (a : A) -> a == a

-- we could postulate univalence, we should in fact! Do some HoTT stuff at some point

-- this is transposrt btw
subst : {A : Set} -> {C : A -> Set} -> {a' a'' : A} -> a' == a'' -> C a' -> C a''
subst (refl a) c = c
