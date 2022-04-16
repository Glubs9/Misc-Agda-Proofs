data Nat : Set where
    zero : Nat
    succ : Nat -> Nat

-- primitive recursion
natrec : {C : Nat -> Set} -> (C zero) -> ((m : Nat) -> C m -> C (succ m)) -> (n : Nat) -> C n
natrec p h zero     = p
natrec p h (succ n) = h n (natrec p h n)

-- yoo wtf we can use natrec to prove stuff about natural numbers??????????????

data _==_ {A : Set} : A -> A -> Set where
    refl : (a : A) -> a == a

data _===_ {A : Set} : A -> A -> Set where
    refl' : {a : A} -> a === a

cong : {a b : Set} (f : a -> b) {x y : a} -> x == y -> f x == f y
cong f (refl a) = refl (f a)

_+_ : Nat -> Nat -> Nat
zero + m = m
(succ n) + m = succ (n + m)


-- hehe nice :)
eq-succ : {n m : Nat} -> n == m -> (succ n) == (succ m)
eq-succ (refl a) = refl (succ a)

eq-pred : {n m : Nat} -> (succ n) == (succ m) -> n == m
eq-pred (refl (succ n)) = refl n

add-eq : {n m r : Nat} -> n == m -> (n + r) == (m + r)
add-eq {n} {m} {r} (refl a) = refl (a + r)

{-
comm-zero : (m : Nat) -> (zero + m) == (m + zero)
comm-zero zero     = refl (zero)
comm-zero (succ m) = eq-succ (comm-zero m)
-}

com-eq : {A : Set} {a b : A} -> a == b -> b == a
com-eq (refl n) = refl n

-- assoc-refl : (n m : Nat) -> ((succ n) + m) == (m + (succ n))
-- assoc-refl n zero = {!!} (assoc-zero n)
-- assoc-refl (succ m) = refl (succ m)

{-
com : (n m : Nat) -> (n + m) == (m + n)
com zero m     = com-zero m
com (succ n) m = {!!}
  where tmp = com n m
-}

assoc : (a b c : Nat) -> (a + (b + c)) == ((a + b) + c)
assoc zero b c = refl (b + c)
assoc (succ a) b c = cong succ (assoc a b c)
-- how tf does this worK????? but fuck it i'm just gonna keep grooving

comm-zero : (m : Nat) -> (m + zero) == m
comm-zero zero = refl zero
comm-zero (succ m) = eq-succ (comm-zero m)

trans-eq : {A : Set} {a b : A} -> a == b -> b == a
trans-eq (refl a) = refl a

-- using second refl as it makes proofs easier somehow?
refl-equiv : {A : Set} {a b : A} -> a === b -> a == b
refl-equiv {a = a} refl' = refl a

comm-succ : (m n : Nat) -> (m + (succ n)) == (succ (m + n))
comm-succ zero n     = refl-equiv refl'
comm-succ (succ m) n = cong succ (comm-succ m n)

eq-trans : {n m r : Nat} -> n == m -> m == r -> n == r
eq-trans (refl a) (refl b) = refl a

eq-comm : {A : Set} {a b : A} -> a == b -> b == a
eq-comm (refl a) = refl a

-- fuck you agda tutorial!, no need for rewriting rules here baby!
-- probably should learn that stuff later, but not right now! low level or nothing 
comm : (m n : Nat) -> (m + n) == (n + m)
comm m zero     = comm-zero m
comm m (succ n) = eq-trans comm-scall comm-rec-succ
  where comm-rec = comm m n
        comm-rec-succ = cong succ comm-rec
        comm-scall = comm-succ m n

{-
comm : (a b : Nat) -> (a + b) == (b + a)
comm zero b = refl (b)
comm zero (succ a)     = eq-succ (comm zero a) -- same shit here, whats going on?
comm (succ a) zero     = eq-succ (comm a zero)
comm (succ a) (succ b) = cong succ (comm a b)
-- comm (succ a) b = eq-succ (comm a b)
-}

-- fuck. i'm too tired for this shit
