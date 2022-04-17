open import Agda.Primitive

-- idk i think it would be fun to write and prove HoTT stuff here.

-- chapter 1 (normal dependent type theory stuff)

-- note: this might not be an adequate definition of == as I think Higher inductive types create custom definitions.
-- we will get to this when it becomes a problem I guess
data _==_ {n : Level} {A : Set n} : A -> A -> Set n where
    refl : {a : A} -> a == a

-- the question becomes, do we specify things in this language, or do we try to prove theorems in agda which are equivalent to HoTT theorems
-- I am going with just proving things in agda as rewriting an entire type theory in agda seems like a chore

data _x_ {n : Level} (A B : Set n) : Set n where
    <_,_> : A -> B -> A x B

curry : {n : Level} {A B C : Set n} -> (A -> B -> C) -> (A x B -> C) -- works as pair recursion rule (almost)
curry f < a , b > = f a b

recAxB : {n m : Level} {A B : Set n} (C : Set m) -> (A -> B -> C) -> (A x B -> C)
recAxB C f < a , b > = f a b

-- haha holy shit look at this type signature
indAxB : {n m : Level} {A B : Set n} -> (C : A x B -> Set m) -> ((a : A) -> (b : B) -> C < a , b >) -> (x : A x B) -> C x
indAxB C g < a , b > = g a b

uncurry : {n : Level} {A B C : Set n} -> (A x B -> C) -> (A -> B -> C)
uncurry g a b = g < a , b >

pr1 : {n : Level} {A B : Set n} -> A x B -> A 
pr1 {A = A} = recAxB A (\a -> (\_ -> a))

pr2 : {n : Level} {A B : Set n} -> A x B -> B
pr2 {B = B} = recAxB B (\_ -> (\b -> b))


data unit : Set where -- I'm pretty sure this is set_-2 but idk how to write that in agda (or at least can't be bothered. Probably a theorem)
    * : unit

-- note: we do not define the recursor on unit because it's SUPA! useless
