{- 

This is the Agda formalization of

      NOTIONS OF ANONYMOUS EXISTENCE IN MARTIN-LOF TYPE THEORY

                              by

Nicolai Kraus, Martin Escardo, Thierry Coquand, Thorsten Altenkirch

This file stays very close to the article. Because of this, not all 
proofs are given in the way that is most elegant for a formalization. 
In fact, often re-ordering statements would lead to a shorter 
presentation. The order that we have chosen in the article makes our 
results, as we hope, understandable and gives sufficient motivation.

This file type check with Agda 2.4.2.5.
-}

module INDEX_NotionsOfAnonymousExistence where

-- We use the following library files:

open import library.Basics hiding (Type ; Σ)
open import library.types.Sigma
open import library.types.Pi
open import library.types.Bool
open import library.NType2
open import library.types.Paths

-- OUR FORMALIZATION

-- Section 1: Introduction
-- (no formalization)

-- Section 2: Preliminaries
open import Sec2preliminaries

-- Section 3: Hedberg's Theorem
open import Sec3hedberg

-- Section 4: Collapsibility implies H-Stability
open import Sec4hasConstToSplit

-- Section 5: Factorizing Weakly Constant Functions
open import Sec5factorConst

-- Section 6: Populatedness
open import Sec6populatedness

-- Section 7: Taboos and Counter-Models
open import Sec7taboos

-- Section 8: Propositional Truncation with Judgmental Computation Rule
open import Sec8judgmentalBeta

-- Section 9: Conclusion and Open Problems
-- (no formalization)
