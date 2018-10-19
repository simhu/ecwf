module Presheaves where

open import Basics

ePSh : ∀ {k lo lh lr} (C : ECat {lo} {lh} {lr}) → Set ((lsuc k) ⊔ lo ⊔ lh ⊔ lr)
ePSh {k} C = eFunctor (C op) (ESet {k})

EPSh : ∀ {k lo lh lr} (C : ECat {lo} {lh} {lr}) → ECat
EPSh {k} C = EFunctor (C op) (ESet {k})

-- Some notation for a presheaf
module ePShNotation {k lo lh lr} {C : ECat {lo} {lh} {lr}} (F : ePSh {k} C) where
  open ECat C public using () renaming ( comp to _∘d_ ; hom-rel to _~d_ )
  setF : obj C → Set k
  setF I = set (fun F I)
  _~_ : {I : obj C} → setF I → setF I → Set k
  _~_ {I} = rel (fun F I)
  infixl 40 _·_
  _·_ : ∀ {I J} → setF I → hom C J I → setF J
  u · h = mor F h .ap u

-- The category of elements of a preasheaf
∫ : ∀ {k lo lh lr} {C : ECat {lo} {lh} {lr}} (F : ePSh {k} C) → ECat
∫ {C = C} F = cat where
  open ePShNotation {C = C} F
  cat : ECat
  obj cat = Σ setF
  hom cat (J , v) (I , u) = Σ λ (f : hom C J I) → v ~ u · f
  hom-rel cat (f , _) (g , _) = f ~d g  -- proof irrelevant in the second argument
  hom-eqr cat = record
    { refl =  C .hom-eqr .refl ; sym =  C .hom-eqr .sym ; trans = C .hom-eqr .trans }
  fst (comp cat (f , _) (g , _)) = f ∘d g
  snd (comp cat {(K , w)} {(J , v)} {(I , u)} (f , p) (g , q)) =
      let gvrelfgu : v · g ~ u · (f ∘d g)
          gvrelfgu  = fun F K .trans (mor F g .ap-cong  p) (F .comp-mor ` (fun F I .refl))
      in fun F K .trans q gvrelfgu
  comp-assoc cat = C .comp-assoc
  comp-cong cat = C .comp-cong
  id cat {(I , u)}=  id C , id-mor F ` (fun F I .refl)
  id-l cat = id-l C
  id-r cat = id-r C
