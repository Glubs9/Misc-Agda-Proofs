-- haha so easy. i love this :)))))
refl : {p : Set} -> p -> (p -> p)
refl a = \_ -> a


data _&_ (A : Set) (B : Set) : Set where
    <_,_> : A -> B -> A & B

data _+_ (A : Set) (B : Set) : Set where
    inl : A -> A + B
    inr : B -> A + B

data _==>_ (A B : Set) : Set where
    fun : (A -> B) -> A ==> B

data false : Set where

_<==>_ : Set -> Set -> Set
A <==> B = (A ==> B) & (B ==> A)

orreflrhs : {p : Set} -> p + p -> p
orreflrhs (inl p) = p
orreflrhs (inr p) = p

orrefl : {p : Set} -> p <==> (p + p)
orrefl = < fun inl , fun orreflrhs >

pairAssoc : {p q : Set} -> (p & q) <==> (q & p)
pairAssoc = < fun (\{(< x , y >) -> < y , x >}) , fun (\{(< y , x >) -> < x , y >}) > -- ewww syntax overload

-- haha nice :)
modtol : {p q : Set} -> ((p -> q) & (q -> false)) -> (p -> false)
modtol < pq , qf > = \{x -> (qf (pq x))} -- this is just a degenerate case of composition / transitivity

postulate
    LEM : {p : Set} -> p + (p -> false)

disjsylo : {p q : Set} -> ((p + q) & (p -> false)) -> false + q
disjsylo < inl p , f > = inl (f p)
disjsylo < inr q , _ > = inr q

-- haha bruh moment so eeeaaaaasssyyyy omg wtf???? absolute braindead
implif' : {p q : Set} -> (p -> q) -> p + (p -> false) -> q + (p -> false)
implif' f (inl p) = inl (f p)
implif' _ (inr f) = inr f

implif : {p q : Set} -> (p -> q) -> q + (p -> false)
implif f = implif' f LEM

negrec : {p : Set} -> false -> p
negrec ()

--ahhhhhhhh i totally get it :)))))) (hehehe ha)
--this works without LEM, only LEM is needed for if direction
implonlif : {p q : Set} -> q + (p -> false) -> (p -> q)
implonlif (inl q) = \{_ -> q}  
implonlif (inr f) = \{p -> negrec (f p)} -- hehehe ha

-- gotteeeeeemmmmmm
impliesDestruct : {p q : Set} -> (p -> q) <==> (q + (p -> false))
impliesDestruct = < fun implif , fun implonlif >

-- contrapositive is provable in intuitionistic logic?
-- ahhhhh but only in one direction though lol
contraif : {p q : Set} -> (p -> q) -> ((q -> false) -> (p -> false))
contraif f f' p = f' (f p)

-- contraonlyif : {p q : Set} -> ((q -> false) -> (p -> false)) -> (p -> q)
-- contraonlyif f p = 
-- shit i'm too tired. need to add lem probs?
-- why does nobody mention this? like cause everybody says "don't do it" cause it's a consequence, but it's really only one direction.
-- we might be able to prove more if we had both? idk check for unsolved problems or something i guess

-- doubleNeg : p -> ((p -> false) -> false)
-- doubleNeg p = LEM

-- check on the proofs that talk about the consequences and see if they fail under the understanding that we can get it one way.
-- like how funny would that be. i doubt it but either way it's a fun exercise :)

_o_ : {p q r : Set} -> (q -> r) -> (p -> q) -> (p -> r)
f1 o f2 = \{p -> f1 (f2 p)}

-- tihs is so epic :)::):::):))
equivCase : {p q : Set} -> p <==> q -> (p + (p -> false)) -> (p & q) + ((p -> false) & (q -> false))
equivCase < fun f1 , _ > (inl p)    = inl (< p , f1 p >)
equivCase < _ , fun f2 > (inr notp) = inr (< notp , notp o f2 >)

-- haha nice :)
-- got it yesssss lezzzz go babby ybybybybybyb
equiv : {p q : Set} -> p <==> q -> ((p & q) + ((p -> false) & (q -> false)))
equiv f = equivCase f LEM

-- woowwo proving stuff is so fucking easy oh my god :))))
exportation : {p q r : Set} -> ((p & q) -> r) -> (p -> (q -> r))
exportation f1 p q = f1 (< p , q >)

demorgansCase : {p q : Set} -> ((p & q) -> false) -> (p + (p -> false)) -> (q + (q -> false)) -> ((p -> false) + (q -> false))
demorgansCase f (inl p) (inl q) = inl (\{_ -> f < p , q >})
demorgansCase _ (inr pf) _      = inl pf
demorgansCase _ _ (inr qf)      = inr qf

demorgans : {p q : Set} -> ((p & q) -> false) -> ((p -> false) + (q -> false))
demorgans f = {!!} LEM LEM -- demorgansCase LEM LEM
