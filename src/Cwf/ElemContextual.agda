open import Basics
open import Presheaves
open import Cwf.Elem

-- Any cwf induces a 'contextual' cwf where the contexts are
-- telescopes of types

module Cwf.ElemContextual {lvs lvr lo lh lr : Level}
 (E : eCwF {lvs} {lvr} {lo} {lh} {lr}) where

open eCwF E
open eCwFNotation {Ctx = Ctx} Ty Tm

data Tele : Set lvs
ψ : Tele → obj Ctx              -- collaps telescope

data Tele where
  nil  : Tele
  snoc : (As : Tele) (A : Typ (ψ As )) → Tele

ψ nil = <>
ψ (snoc As A) = ψ As ∙ A


