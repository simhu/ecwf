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
-- TODO: Why do we always have to put the category C when using ∫?
∫ : ∀ {k lo lh lr} {C : ECat {lo} {lh} {lr}} (F : ePSh {k} C) → ECat {k ⊔ lo} {k ⊔ lh} {lr}
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

∫proj : ∀ {k lo lh lr} {C : ECat {lo} {lh} {lr}} (F : ePSh {k} C) → eFunctor (∫ {C = C} F) C
∫proj {C = C} F = record
  { fun = fst 
  ; mor = fst
  ; resp = λ p → p
  ; id-mor = C .hom-eqr .refl
  ; comp-mor = C .hom-eqr .refl
  }

∫fun : ∀ {k lo lh lr} {C : ECat {lo} {lh} {lr}} {F G : ePSh {k} C}
       (α : eNat F G ) → eFunctor (∫ {C = C} F) (∫ {C = C} G)
fun (∫fun {C = C} {F} {G} α) (I , u) = I , nat α I .ap u 
mor (∫fun {C = C} {F} {G} α) {J , v} {I , u} (f , p) =
  f , fun G J .trans (nat α J .ap-cong p) (nat-eq-inv α ` fun F I .refl)
resp (∫fun {C = C} {F} {G} α) p = p
id-mor (∫fun {C = C} {F} {G} α) = C .hom-eqr .refl
comp-mor (∫fun {C = C} {F} {G} α) = C .hom-eqr .refl

