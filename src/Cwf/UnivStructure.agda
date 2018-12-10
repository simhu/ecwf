-- A universe structure for now is just a dependent type
module Cwf.UnivStructure where

open import Basics
open import Presheaves
open import Cwf.Elem

module _ {lvs lvr lo lh lr : Level} (E : eCwF {lvs} {lvr} {lo} {lh} {lr}) where
  open eCwF E
  open eCwFNotation {Ctx = Ctx} Ty Tm

  record UnivStructure : Set lvs where
    field
      U : Typ <>
      El : Typ (<> ∙ U)

