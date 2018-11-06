module Presheaves where

open import Basics
open import Opposite public

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


module _ {ks kr lo lh lr : Level} {C : ECat {lo} {lh} {lr}} where
  -- The category of elements of a preasheaf
  -- (Note that this can also be constructred using comma categories)
  -- TODO: Why do we always have to put the category C when using ∫?
  ∫ : (F : ePSh {ks} {kr} C) → ECat {ks ⊔ lo} {kr ⊔ lh} {lr}
  ∫ F = cat where
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

  ∫proj : (F : ePSh {ks} {kr} C) → eFunctor (∫ F) C
  ∫proj F = record
    { fun = fst
    ; mor = fst
    ; resp = λ p → p
    ; id-mor = C .hom-eqr .refl
    ; comp-mor = C .hom-eqr .refl
    }

  ∫fun : {F G : ePSh {ks} {kr} C} (α : eNat F G ) → eFunctor (∫ F) (∫ G)
  fun (∫fun {F} {G} α) (I , u) = I , nat α I .ap u
  mor (∫fun {F} {G} α) {J , v} {I , u} (f , p) =
    f , fun G J .trans (nat α J .ap-cong p) (nat-eq-inv α ` fun F I .refl)
  resp (∫fun {F} {G} α) p = p
  id-mor (∫fun {F} {G} α) = C .hom-eqr .refl
  comp-mor (∫fun {F} {G} α) = C .hom-eqr .refl

  ∫id : {F : ePSh {ks} {kr} C} →
        eNatIso (idFunctor (∫ F)) (∫fun (id (EPSh C)))
  ∫id {F} =
    let eta : eNatIso  (idFunctor (∫ F)) (idFunctor (∫ F))
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

  ∫comp : {F G H : ePSh {ks} {kr} C} {α : eNat G H} {β : eNat F G} →
          eNatIso (∫fun α ∘Func ∫fun β) (∫fun (comp (EPSh {ks} {kr} C) α β))
  ∫comp {α = α} {β = β} =
    let eta : eNatIso (∫fun α ∘Func ∫fun β) (∫fun α ∘Func ∫fun β)
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


  ∫resp : {F G : ePSh {ks} {kr} C} {α  β : eNat F G} →
          hom-rel (EPSh C) α β → hom-rel CAT (∫fun α) (∫fun β)
  ∫resp {F} {G} {α} {β} αβ = let open ePShNotation {C = C} G in record
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

  ∫∫ : eFunctor (EPSh {ks} {kr} C) CAT
  ∫∫ = record { fun = ∫ ; mor = ∫fun ; resp = ∫resp ; id-mor = ∫id ; comp-mor = ∫comp }


module _ {ks kr lco lch lcr ldo ldh ldr : Level}
         {C : ECat {lco} {lch} {lcr}} {D : ECat {ldo} {ldh} {ldr}}
         {P : ePSh {ks} {kr} C} {Q : ePSh {ks} {kr} D}
         (F : eFunctor C D) (α : eNat P (Q ∘Func (F op-fun))) where
  ∫base : eFunctor (∫ {C = C} P) (∫ {C = D} Q)
  fun ∫base (I , u) = fun F I , nat α I .ap u
  mor ∫base {J , v} {I , u} (f , p) = mor F f ,
    let open EqRelReason (eqr (fun Q (fun F J))) in
    begin
      nat α J .ap v
    ≈⟨ nat α J .ap-cong p ⟩
      nat α J .ap (mor P f .ap u)
    ≈⟨ sym (fun Q (fun F J)) (nat-eq α ` refl (fun P I)) ⟩
      mor Q (mor F f) .ap (nat α I .ap u)
    ∎
  resp ∫base = resp F
  id-mor ∫base = id-mor F
  comp-mor ∫base = comp-mor F



module Yoneda {lo lh lr : Level} (C : ECat {lo} {lh} {lr}) where

  yon-obj : obj C → ePSh {lh} {lr} C
  fun (yon-obj x) y = hom-set C y x
  mor (yon-obj x) f = record { ap =  λ g → comp C g f ; ap-cong = comp-cong-l C }
  resp (yon-obj x) p = map-rel λ q → comp-cong C q p
  id-mor (yon-obj x) = map-rel λ p → hom-eqr C .trans p (id-r-inv C)
  comp-mor (yon-obj x) {f = f} {g = g} = map-rel λ {h} {h'} p →
    let open EqRelReason (hom-eqr C) in
    begin
      comp C (comp C h g) f
    ≈⟨ comp-assoc-inv C ⟩
      comp C h (comp C g f)
    ≈⟨ comp-cong-l C p ⟩
      comp C h' (comp C g f)
    ∎

  yon-fun : ∀ {a b} (f : hom C a b) → hom (EPSh C) (yon-obj a) (yon-obj b)
  nat (yon-fun f) c = record { ap = λ g → comp C f g ; ap-cong = comp-cong-r C }
  nat-eq (yon-fun f) {f = g} = map-rel λ {h} {h'} p →
    let open EqRelReason (hom-eqr C) in
    begin
      comp C (comp C f h) g
    ≈⟨ comp-assoc-inv C ⟩
      comp C f (comp C h g)
    ≈⟨ comp-cong-r C (comp-cong-l C p) ⟩
      comp C f (comp C h' g)
    ∎

  yon-resp : ∀ {a b} {f g : hom C a b} (p : hom-rel C f g) →
             hom-rel (EPSh C) (yon-fun f) (yon-fun g)
  yon-resp p q = map-rel (comp-cong C p)

  yon-id : ∀ {a} → hom-rel (EPSh C) (id (EPSh C)) (yon-fun (id C {a}))
  yon-id {a} b = map-rel λ p → hom-eqr C .trans p (id-l-inv C)

  yon-comp : ∀ {a b c} {f : hom C b c} {g : hom C a b} →
             hom-rel (EPSh C) (comp (EPSh C) (yon-fun f) (yon-fun g)) (yon-fun (comp C f g))
  yon-comp {f = f} {g} d = map-rel λ {h} {h'} p →
    let open EqRelReason (hom-eqr C) in
    begin
      comp C f (comp C g h)
    ≈⟨ comp-assoc C ⟩
      comp C (comp C f g) h
    ≈⟨ comp-cong-r C p ⟩
      comp C (comp C f g) h'
    ∎

  yoneda : eFunctor C (EPSh C)
  yoneda = record { fun = yon-obj ; mor = yon-fun ; resp = yon-resp
                  ; id-mor = yon-id ; comp-mor = yon-comp }
