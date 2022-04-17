-- was thinking, if we remove the enforcement of termination in a type theory, we should be able to prove anything.

data unit : Set where
    * : unit

-- like
{-# TERMINATING #-}
prf : {A : Set} -> unit -> A
prf * = prf *

prf-of-a : {A : Set} -> A
prf-of-a = prf *

-- the agda docs include this, even simpler example
{-# TERMINATING #-}
a : {A : Set} -> A
a = a

-- in other words, we have created the false thing, like false-rec : false -> A. Same deal, we can prove anything really.

-- so if we don't have a termination checker, then this can happen. So we definitely need one

-- i was thinking that this might be a connection between bottom in type theory and domain theory. Like we have bottom in domain theory (non-termination) behaving similarly to bottom in type theory. Except bottom in domain theory is trivial to create. This also implies that domain theory is inconsistent from a proposition as types perspective but either way.

-- i'm pretty happy with this discovery :) (not really a discovery but something fun nonetheless)

-- does it actually type check is the real question?  agda runs forever on this
-- i mean it does type check when you do it by hand, i guess the computational verification doesn't work

-- edit: actually, looking at it again, i'm not sure this type checks by hand? Like I was very tired when I wrote this. It makes sense to some extent. but at the same time it's like, ehhhhhhhhhhhh
