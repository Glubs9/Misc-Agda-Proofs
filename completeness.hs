module Completeness where

-- note: before reading this proof please realize that i'm very tired and
-- sad and this is the stupidest proof i've ever written. it doesn't even
-- make sense? like point-free programming? point-free programming doesn't
-- mean anything. It's haskells prelude pointfree programming. Much less
-- fun

-- I want to prove the completeness of point free programming
-- cause i always felt like point free was too restrictive, but like it's
-- not though? It should be fully complete (i guess i'm doing completeness
-- but whatever)

-- I am going to do this with two proofs.
-- The first that we can generate every combination of functions (ala
-- untyped-lambda calculus)
-- Cause if we can, then we can express everything
--
-- Although we are finished there I wanted to make it more interesting, as
-- although, lambda calculus is turing complete, it is a little impractical
-- to code in literally. I am going to then write up primtive and general
-- recursion ala peano arithmetic completely pointfree to show that we can
-- do non-trivial computation on data-structures.
--


-- first we do lambda calculus, which we do by writing ski calculus

import Data.Bifunctor
import Control.Monad

i :: a -> a
i = head . (: [])

-- not using const cause then theres no challenge
k :: a -> b -> a
k = curry fst

s :: (a -> b -> c) -> (a -> b) -> a -> c
s x y z = undefined
    where fs = (x, y)
          -- f = \f -> f z -- cannot construct the infinite type?
          f = ($ z)
          fs' = bimap f f fs -- something like double or duplicate or something
          --out = foldr1 ($) (x z, y z)
          -- out = fst fs' (snd fs') -- this is the same fucking equation lmao
          xD = uncurry ($) (x z, y z)
          -- something like curry $ join bimap ($z)
          -- wtf does that even mean?
          -- benis = curry $ join bimap ($ z)
          -- benis = join bimap ($ z)
          -- uwu = (uncurry ($)) . join bimap
          -- uwu = uncurry ($) . (curry (join bimap))
          -- uwu = uncurry ($) . _ (join bimap $) fucking hell something
          -- like that or whatever
