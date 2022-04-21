open import Agda.Primitive

-- idk i think it would be fun to write and prove HoTT stuff here.

-- chapter 1 (normal dependent type theory stuff)

-- note: this might not be an adequate definition of == as I think Higher inductive types create custom definitions.
-- we will get to this when it becomes a problem I guess
data _==_ {n : Level} {A : Set n} : A -> A -> Set n where
    refl : {a : A} -> a == a

-- used when we want to specify the refl's argument. Not necersarry or clean but whatever, sometimes it's useful
data _===_ {n : Level} {A : Set n} : A -> A -> Set n where
    refl' : (a : A) -> a === a

-- but the two are equivalent so it doesn't matter (we can define this the other way around trivially)
refl-equiv : {n : Level} {A : Set n} {a b : A} -> a === b -> a == b
refl-equiv (refl' a) = refl

-- the question becomes, do we specify things in this language, or do we try to prove theorems in agda which are equivalent to HoTT theorems
-- I am going with just proving things in agda as rewriting an entire type theory in agda seems like a chore

data _x_ {n : Level} (A B : Set n) : Set n where
    <_,_> : A -> B -> A x B

curry : {n : Level} {A B C : Set n} -> (A -> B -> C) -> (A x B -> C) -- works as pair recursion rule (almost)
curry f < a , b > = f a b

rec-AxB : {n m : Level} {A B : Set n} (C : Set m) -> (A -> B -> C) -> (A x B -> C)
rec-AxB C f < a , b > = f a b

-- haha holy shit look at this type signature
ind-AxB : {n m : Level} {A B : Set n} -> (C : A x B -> Set m) -> ((a : A) -> (b : B) -> C < a , b >) -> (x : A x B) -> C x
ind-AxB C g < a , b > = g a b

uncurry : {n : Level} {A B C : Set n} -> (A x B -> C) -> (A -> B -> C)
uncurry g a b = g < a , b >

pr1 : {n : Level} {A B : Set n} -> A x B -> A 
pr1 {A = A} = rec-AxB A (\a -> (\_ -> a))

pr2 : {n : Level} {A B : Set n} -> A x B -> B
pr2 {B = B} = rec-AxB B (\_ -> (\b -> b))

uniq-AxB : {n : Level} {A B : Set n} -> (x : A x B) -> x == < pr1 x , pr2 x > 
uniq-AxB < a , b > = refl


data unit : Set where -- I'm pretty sure this is set_-2 but idk how to write that in agda (or at least can't be bothered. Probably a theorem)
    * : unit

-- note: we do not define the recursor on unit because it's SUPA! useless

-- note: i don't really get what's going on with the extra C x? it doesn't really follow hte pattern of ind a x b
ind-unit : {n : Level} -> (C : unit -> Set n) -> (C *) -> (x : unit) -> C x
ind-unit C c * = c

uniq-unit : (x : unit) -> * == x
uniq-unit * = ind-unit (\{x -> * == x}) refl *



data Sigma (A : Set) (B : A -> Set) : Set where
    _,_ : (a : A) -> B a -> Sigma A B

proj1 : {A : Set} {B : A -> Set} -> Sigma A B -> A
proj1 (a , b) = a

proj2 : {A : Set} {B : A -> Set} -> (p : Sigma A B) -> B (proj1 p)
proj2 (a , b) = b

rec-sigma : {n m : Level} {A : Set n} {B : A -> Set m} -> (C : Set m) -> 
