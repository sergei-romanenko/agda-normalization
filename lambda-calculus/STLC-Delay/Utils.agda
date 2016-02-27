module STLC-Delay.Utils where

open import Agda.Primitive public
open import Size public
open import Category.Monad public
  using (RawMonad; module RawMonad)

open import Data.Unit public
  using (⊤; tt)
open import Data.Product as Prod public
  using (_,_; proj₁; proj₂; _×_; Σ; ∃; ∃₂)

open import Function public

open import Relation.Binary.PropositionalEquality as P public
  renaming ([_] to ≡[_])

open import Relation.Binary public
  using (Setoid)

import Relation.Binary.EqReasoning as EqReasoning
