data false : Set where

data _+_ (A : Set) (B : Set) : Set where
    inl : A -> A + B
    inr : B -> A + B

data _x_ (A : Set) (B : Set) : Set where
    <_,_> : A -> B -> A x B

pnotp : {p : Set} -> p x (p -> false) -> false 
pnotp < p , f > = f p

impl
