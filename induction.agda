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

comm : (a b : Nat) -> (a + b) == (b + a)
comm zero zero         = refl (zero)
comm zero (succ a)     = eq-succ (comm zero a) -- same shit here, whats going on?
comm (succ a) zero     = eq-succ (comm a zero)
comm (succ a) b = eq-succ (comm a b)

-- fuck. i'm too tired for this shit
