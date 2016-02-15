{-
    T R U N C A T I O N   L E V E L S
                 I N
H O M O T O P Y   T Y P E   T H E O R Y

======= ELECTRONIC APPENDIX =======

           NICOLAI KRAUS

           February 2015
-}

{-# OPTIONS --without-K #-}

module INDEX where

-- Chapter 2
open import Preliminaries
-- Parts of Chapter 2 are in a separate file:
open import Pointed

{- Chapter 3,4,5,6 are joint work with
   Martin Escardo, 
   Thierry Coquand, 
   Thorsten Altenkirch -}

-- Chapter 3
open import Truncation_Level_Criteria

-- Chapter 4
open import Anonymous_Existence_CollSplit
open import Anonymous_Existence_Populatedness
open import Anonymous_Existence_Comparison

-- Chapter 5
open import Weakly_Constant_Functions

-- Chapter 6
open import Judgmental_Computation

{- Chapter 7 (joint work with Christian Sattler)
   has two parts. First, we construct homotopically
   complicated types; this development is distributed 
   beween two files. Then, we discuss connectedness,
   which turns out to be very hard to formalise;
   we use in total five files to structure that 
   discussion, see below. -}

{- First, we have an auxiliary file which makes precise 
   that the 'universe of n-types' behaves like an actual
   universe. We formalise operations for it; this is 
   very useful as it allows a more 'principled' development. -}
open import UniverseOfNTypes
{- Now: Sections 1-4 of Chapter 7, where 1,2 are "hidden". 
   They are special cases of the more general theorem that 
   we prove in 7.4; the special cases are written out only
   for pedagogical reasons and are thus omitted in this 
   formalisation. -}
open import HHHUU-ComplicatedTypes

{- Note that Chapter 7.5 is not formalised, even though it 
   could have been; we omit it because it is only an 
   alternative to the above formalisation, and actually 
   leads to a weaker result than the one in 
   'HHHUU-ComplicatedTypes'. 

   Chapter 7.6 is very hard to formalise (mostly done by 
   Christian Sattler). Caveat: The order of the statements
   in the formalisation is different from the order in
   the thesis (it sometimes is more convenient to define
   multiple notions in the same module because they share
   argument to avoid replication of code, without them 
   belonging together logically).

   First, we show (in a separate file) that the non-dependent 
   universal property and the dependent universal
   property are equivalent. 

   Contains: Definition 7.6.2, Lemma 7.6.6 -}
open import Trunc.Universal

-- Definition 7.6.4, Lemma 7.6.7, Corollary 7.6.8
open import Trunc.Basics

-- Lemma 7.6.9, Lemma 7.6.10
-- (actually even a stronger version of Lemma 7.6.10)
open import Trunc.TypeConstructors

{- main part of connectedness:
   (link to 7.6.1,)
   Definition 7.6.13, Definition 7.6.11, 
   Lemma 7.6.14, Lemma 7.6.12, Lemma 7.6.15 
   and
   Theorem 7.7.1 -}
open import Trunc.Connection

-- Remark 7.6.16
open import Trunc.ConnectednessAlt


{- The main result of Chapter 8 is, unfortunately,
   meta-theoretical. It is plausible that in an 
   implementation of a type theory with 'two levels'
   (one semi-internal 'strict' equality and the
   ordinary identity type), the complete Chapter 8
   could be formalised; but at the moment, this is
   merely speculation. -}


-- Chapter 9.2: Semi-Simplicial Types

-- Proposition 9.2.1 (Δ₊ implemented with judgmental categorical laws)
open import Deltaplus
