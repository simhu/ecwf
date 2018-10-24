module Limits where

open import Basics


isTerminal : ∀ {lo lh lr} {C : ECat {lo} {lh} {lr}} (T : obj C) → Set (lo ⊔ lh ⊔ lr)
isTerminal {C = C} T = ∀ A → Σ λ (f : hom C A T) → ∀ g → hom-rel C f g

module ConstantFunctor {ljo ljh ljr lco lch lcr : Level}
                       (J : ECat {ljo} {ljh} {ljr}) (C : ECat {lco} {lch} {lcr}) where

  open ECat C using () renaming (comp to _∘C_ ; hom-rel to _~C_ ; hom-eqr to Ceq)

  -- The constant functor
  Δobj : (c : obj C) → eFunctor J C
  Δobj c = record
    { fun = λ _ → c
    ; mor = λ _ → id C
    ; resp = λ _ → Ceq .refl
    ; id-mor = Ceq .refl
    ; comp-mor = C .id-l
    }

  Δmor : {c0 c1 : obj C} (f : hom C c0 c1) → eNat (Δobj c0) (Δobj c1) 
  Δmor {c0} {c1} f = record { nat = λ _ → f ; nat-eq = Ceq .trans (id-l C) (id-r-inv C) }

  Δ : eFunctor C (EFunctor J C)
  Δ = record
    { fun = Δobj ; mor = Δmor ; resp = λ p _ → p 
    ; id-mor = λ _ → Ceq .refl ; comp-mor = λ _ → Ceq .refl }


module LimitModule {ljo ljh ljr lco lch lcr : Level}
                   {J : ECat {ljo} {ljh} {ljr}} {C : ECat {lco} {lch} {lcr}}
                   (F : eFunctor J C) where

  open ECat J using () renaming (comp to _∘J_ ; hom-rel to _~J_ ; hom-eqr to Jeq)
  open ECat C using () renaming (comp to _∘C_ ; hom-rel to _~C_ ; hom-eqr to Ceq)

  lmax = ljo ⊔ ljh ⊔ ljr ⊔ lco ⊔ lcr ⊔ lch

  open ConstantFunctor J C

  record Cone : Set lmax where
    no-eta-equality
    field
      cone-obj : obj C
      cone-nat : eNat (Δobj cone-obj) F

  -- A different way to represent cones
  record Cone' : Set (ljo ⊔ ljh ⊔ lco ⊔ lcr ⊔ lch) where
    no-eta-equality
    field
      cone-obj  : obj C
      cone-proj : (j : obj J) → hom C cone-obj (fun F j)
      cone-mor  : {i j : obj J} (f : hom J i j) → (mor F f ∘C cone-proj i) ~C cone-proj j

  cone-fwd : Cone → Cone'
  cone-fwd c = let open Cone c in record
    { cone-obj = cone-obj ; cone-proj = cone-nat .nat
    ; cone-mor = λ f → Ceq .trans (cone-nat .nat-eq) (id-r C)
    }

  cone-bwd : Cone' → Cone
  cone-bwd c' = let open Cone' c' in record
    { cone-obj = cone-obj
    ; cone-nat = record { nat = cone-proj ; nat-eq = Ceq .trans (cone-mor _) (id-r-inv C) }
    }

