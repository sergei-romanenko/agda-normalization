module STLC-Tait-OPE.Util where

open import Data.Unit public
  using (⊤; tt)
open import Data.Product as Prod public
  using (_,_; proj₁; proj₂; _×_; Σ; ∃; ∃₂)

open import Function public
--import Function.Related as Related public

open import Relation.Binary.PropositionalEquality as P public
  renaming ([_] to ≡[_])

open import Relation.Binary public
  using (Setoid)

import Relation.Binary.EqReasoning as EqReasoning
