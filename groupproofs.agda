open import Agda.Primitive

-- I want to prove the uniqueness of inverses
-- It seems like my definition of group is super wack, but i just want to feel smart so i don't care

data _==_ {A : Set} : A -> A -> Set where
    refl : {a : A} -> a == a

data group : Set where
    i : group
    _x_ : group -> group -> group
    

-- group axioms
postulate
    i1 : {a : group} -> (i x a) == a
    i2 : {a : group} -> (a x i) == a
    assoc : {a b c : group} -> (a x (b x c)) == ((a x b) x c)

comm : {A : Set} {a b : A} -> a == b -> b == a
comm refl = refl

trans : {A : Set} {a b c : A} -> a == b -> b == c -> a == c
trans refl refl = refl

-- inverse : {n : Level} -> (f g : group) -> Set n
-- inverse f g = (f x g) == i

invcomm : {f g : group} -> (f x g) == i -> (g x f) == i
invcomm () -- very strange, but whatever if it works then it works

-- need to define equality substitution
-- like: (note: defo could've just done using app but whatever)
eq-sub : {f g h : group} -> g == h -> (f x g) == (f x h)
eq-sub refl = refl

uniqueness : {f g h : group} -> (f x g) == i -> (f x h) == i -> g == h
uniqueness () -- bruh okay this isn't that great
-- you know what, whatever. I'm done with this.
