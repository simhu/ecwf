module Presheaves where

open import Basics

ePSh : ∀ {ks kr lo lh lr} (C : ECat {lo} {lh} {lr}) → Set (lsuc ks ⊔ (lsuc kr ⊔ (lo ⊔ (lh ⊔ lr))))
ePSh {ks} {kr} C = eFunctor (C op) (ESet {ks} {kr})

EPSh : ∀ {ks kr lo lh lr} (C : ECat {lo} {lh} {lr}) → ECat
EPSh {ks} {kr} C = EFunctor (C op) (ESet {ks} {kr})

-- Some notation for a presheaf
module ePShNotation {ks kr lo lh lr} {C : ECat {lo} {lh} {lr}} (F : ePSh {ks} {kr} C) where
  open ECat C public using () renaming ( comp to _∘d_ ; hom-rel to _~d_ ; hom-eqr to ~deqr )
  setF : obj C → Set ks
  setF I = set (fun F I)
  _~_ : {I : obj C} → setF I → setF I → Set kr
  _~_ {I} = rel (fun F I)
  ~eqr : {I : obj C} → EqRel (fun F I .rel)
  ~eqr {I} = eqr (fun F I)

  infixl 40 _·_ -- \cdot
  _·_ : ∀ {I J} → setF I → hom C J I → setF J
  u · h = mor F h .ap u

  ·-id : ∀ {I} {u : setF I} → u ~ u · id C
  ·-id {I} =  id-mor F ` (fun F I .refl)

  ·-assoc : ∀ {I J K} {f : hom C J I} {g : hom C K J} {u : setF I} → u · f · g ~ u · (f ∘d g)
  ·-assoc {I} = comp-mor F .map-resp (fun F I .refl)

  ·-cong-l : ∀ {J I} {f : hom C J I} {u v : setF I} → u ~ v → u · f ~ v · f
  ·-cong-l {f = f} uv = mor F f .ap-cong uv


-- The category of elements of a preasheaf
-- (Note that this can also be constructred using comma categories)
-- TODO: Why do we always have to put the category C when using ∫?
∫ : ∀ {ks kr lo lh lr} {C : ECat {lo} {lh} {lr}} (F : ePSh {ks} {kr} C) → ECat {ks ⊔ lo} {kr ⊔ lh} {lr}
∫ {C = C} F = cat where
  open ePShNotation {C = C} F
  cat : ECat
  obj cat = Σ setF
  hom cat (J , v) (I , u) = Σ λ (f : hom C J I) → v ~ u · f
  hom-rel cat (f , _) (g , _) = f ~d g  -- proof irrelevant in the second argument
  hom-eqr cat = record
    { refl =  C .hom-eqr .refl ; sym =  C .hom-eqr .sym ; trans = C .hom-eqr .trans }
  fst (comp cat (f , _) (g , _)) = f ∘d g
  snd (comp cat {(K , w)} {(J , v)} {(I , u)} (f , p) (g , q)) = let open EqRelReason ~eqr in
    begin w ≈⟨ q ⟩ v · g ≈⟨ ·-cong-l p ⟩  (u · f) · g ≈⟨ ·-assoc ⟩  u · (f ∘d g) ∎
  comp-assoc cat = C .comp-assoc
  comp-cong cat = C .comp-cong
  id cat {(I , u)}=  id C , ·-id
  id-l cat = id-l C
  id-r cat = id-r C

∫proj : ∀ {ks kr lo lh lr} {C : ECat {lo} {lh} {lr}} (F : ePSh {ks} {kr} C) → eFunctor (∫ {C = C} F) C
∫proj {C = C} F = record
  { fun = fst
  ; mor = fst
  ; resp = λ p → p
  ; id-mor = C .hom-eqr .refl
  ; comp-mor = C .hom-eqr .refl
  }

∫fun : ∀ {ks kr lo lh lr} {C : ECat {lo} {lh} {lr}} {F G : ePSh {ks} {kr} C}
       (α : eNat F G ) → eFunctor (∫ {C = C} F) (∫ {C = C} G)
fun (∫fun {C = C} {F} {G} α) (I , u) = I , nat α I .ap u
mor (∫fun {C = C} {F} {G} α) {J , v} {I , u} (f , p) =
  f , fun G J .trans (nat α J .ap-cong p) (nat-eq-inv α ` fun F I .refl)
resp (∫fun {C = C} {F} {G} α) p = p
id-mor (∫fun {C = C} {F} {G} α) = C .hom-eqr .refl
comp-mor (∫fun {C = C} {F} {G} α) = C .hom-eqr .refl

∫id : ∀ {ks kr lo lh lr} {C : ECat {lo} {lh} {lr}} {F : ePSh {ks} {kr} C} →
      eNatIso (idFunctor (∫ {C = C} F)) (∫fun (id (EPSh C)))
∫id {C = C} {F} =
  let eta : eNatIso  (idFunctor (∫ {C = C} F)) (idFunctor (∫ {C = C} F))
      eta = iso-natiso iso-refl
  in record  -- no-eta isn't really our friend here
  { to-nat = record
    { nat = eta .to-nat .nat
    ; nat-eq = λ {a} {b} {f} → eta .to-nat .nat-eq {f = f} }
  ; to-is-iso = record { nat-inv = eta .to-is-iso .isNatIso.nat-inv
                       ; nat-inv-sect = λ {a} →
                         eta .to-is-iso .isNatIso.nat-inv-sect {a}
                       ; nat-inv-retract = λ {a} →
                         eta .to-is-iso .isNatIso.nat-inv-retract {a = a}
                       }
  }

∫comp : ∀ {ks kr lo lh lr} {C : ECat {lo} {lh} {lr}} {F G H : ePSh {ks} {kr} C}
        {α : eNat G H} {β : eNat F G} →
        eNatIso (∫fun {C = C} α ∘Func ∫fun β) (∫fun (comp (EPSh {ks} {kr} C) α β))
∫comp {C = C} {α = α} {β = β} =
  let eta : eNatIso (∫fun {C = C} α ∘Func ∫fun β) (∫fun {C = C} α ∘Func ∫fun β)
      eta = iso-natiso iso-refl
  in record  -- no-eta isn't really our friend here
    { to-nat = record
      { nat = eta .to-nat .nat
      ; nat-eq = λ {a} {b} {f} → eta .to-nat .nat-eq {f = f} }
    ; to-is-iso = record { nat-inv = eta .to-is-iso .isNatIso.nat-inv
                         ; nat-inv-sect = λ {a} →
                           eta .to-is-iso .isNatIso.nat-inv-sect {a}
                         ; nat-inv-retract = λ {a} →
                           eta .to-is-iso .isNatIso.nat-inv-retract {a = a}
                         }
    }


∫resp : ∀ {ks kr lo lh lr} {C : ECat {lo} {lh} {lr}} {F G : ePSh {ks} {kr} C}
          {α  β : eNat F G} → hom-rel (EPSh C) α β →
          hom-rel CAT (∫fun {C = C} α) (∫fun β)
∫resp {C = C} {F} {G} {α} {β} αβ = let open ePShNotation {C = C} G in record
  { to-nat = record
      { nat = λ a → id C , ~eqr .trans (αβ (fst a) ` (fun F (fst a) .refl)) ·-id
      ; nat-eq = ~deqr .trans (id-r C) (id-l-inv C)
      }
    ; to-is-iso = record
      { nat-inv = λ a → id C , ~eqr .trans (fun G (fst a) .sym
                                  (αβ (fst a) ` (fun F (fst a) .refl))) ·-id
      ; nat-inv-sect = id-l C
      ; nat-inv-retract = id-l C
      }
  }

∫∫ : ∀ {ks kr lo lh lr} {C : ECat {lo} {lh} {lr}} → eFunctor (EPSh {ks} {kr} C) CAT
∫∫ {C = C} = record { fun = ∫ {C = C} ; mor = ∫fun ; resp = ∫resp ; id-mor = ∫id ; comp-mor = ∫comp }
