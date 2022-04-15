data Nat : Set where
    zero : Nat
    succ : Nat -> Nat

-- primitive recursion
natrec : {C : Nat -> Set} -> (C zero) -> ((m : Nat) -> C m -> C (succ m)) -> (n : Nat) -> C n
natrec p h zero     = p
natrec p h (succ n) = h n (natrec p h n)

-- yoo wtf we can use natrec to prove stuff about natural numbers??????????????
