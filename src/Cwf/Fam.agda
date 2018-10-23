-- WIP: A definition of e-categories with families using the e-category
-- EFam of families of setoids

module Cwf.Fam where

open import Basics
open import Discrete
open import Presheaves
open import Comma
open import Limits using (module ConstantFunctor)

-- This looks way too complicated, or?
EFam : {ls lr : Level} → ECat {lsuc ls ⊔ lsuc lr} {lsuc ls ⊔ lsuc lr} {ls ⊔ lr}
EFam {ls} {lr}  = cat where
  S = ESet {ls} {lr}
  _~s_ = S .hom-rel
  _∘s_ = S .comp
  infixl 40 _∘s_
  seq = S .hom-eqr

  cat : ECat
  obj cat = Σ λ (A : S .obj) → eFunctor (#0 A) S
  hom cat (A , B) (A' , B') =
    Σ λ (f : hom S A A') → eNat B (B' ∘Func (#fun0 {ls = ls} {lr = lr} {A} {A'} f))
  hom-rel cat {A , B} {A' , B'} (f , α) (g , β) =
    Σ λ (p : f ~s g) →
    ∀ (a : A .set) → (mor B' (p ` (A .refl))) ∘s (nat α a) ~s (nat β a)

  refl (hom-eqr cat {A , B} {A' , B'}) {f , α} = seq .refl {f} , λ a →
    let open EqRelReason seq in
    begin
      (mor B' (seq .refl {f} ` (A .refl))) ∘s (nat α a)
    ≈⟨ comp-cong-l S {g = nat α a} (resp B' tt) ⟩
      (mor B' (A' .refl)) ∘s (nat α a)
    ≈⟨ comp-cong-l S {g = nat α a} (id-mor-inv B') ⟩
      (id S) ∘s (nat α a)
    ≈⟨ id-l S ⟩
      nat α a
    ∎

  sym (hom-eqr cat {A , B} {A' , B'}) {f , α} {g , β} (p , q) = seq .sym p , λ a →
    let open EqRelReason (seq {fun B a} {fun B' (f .ap a)})
        qai : nat β a ~s mor B' (p ` eqr A .refl) ∘s nat α a
        qai = seq .sym (q a)
        fisf : A' .rel (f .ap a) (f .ap a)
        fisf = A' .trans (p ` (A .refl)) (seq .sym p ` (A .refl))
    in
      begin
        mor B' (seq .sym p ` (A .refl)) ∘s nat β a
      ≈⟨ comp-cong-r S {f = mor B' (seq .sym p ` A .refl)} qai ⟩
        mor B' (seq .sym p ` (A .refl)) ∘s (mor B' (p ` (A .refl)) ∘s nat α a)
      ≈⟨ comp-assoc S {f = mor B' (seq .sym p ` (A .refl))}
           {g = mor B' (p ` (A .refl))} {h = nat α a} ⟩
        (mor B' (seq .sym p ` (A .refl)) ∘s mor B' (p ` (A .refl))) ∘s nat α a
      ≈⟨ comp-cong-l S {g = nat α a} (comp-mor B') ⟩
        mor B' fisf ∘s nat α a
      ≈⟨ comp-cong-l S {g = nat α a} (resp B' tt) ⟩
        mor B' (A' .refl) ∘s nat α a
      ≈⟨ comp-cong-l S {g = nat α a} (seq .sym (id-mor B')) ⟩
        id S ∘s nat α a
      ≈⟨ id-r S ⟩
        nat α a
      ∎

  trans (hom-eqr cat {A , B} {A' , B'}) {f , α} {g , β} {h , γ} (fg , αβ) (gh , βγ) =
    seq .trans fg gh , λ a →
      let open EqRelReason (seq {fun B a} {fun B' (h .ap a)}) in
      begin
        mor B' (seq .trans fg gh ` A .refl) ∘s nat α a
      ≈⟨ comp-cong-l S {g = nat α a} (comp-mor-inv B') ⟩
        (mor B' (gh ` A .refl) ∘s mor B' (fg ` A .refl)) ∘s nat α a
      ≈⟨ comp-assoc S {f = mor B' (gh ` A .refl)}
                    {g = mor B' (fg ` A .refl)} {h = nat α a}⟩
        mor B' (gh ` A .refl) ∘s (mor B' (fg ` A .refl) ∘s nat α a)
      ≈⟨ comp-cong-r S {f = mor B' (gh ` A .refl)} (αβ a) ⟩
        mor B' (gh ` A .refl) ∘s nat β a
      ≈⟨ βγ a ⟩
        (nat γ a)
      ∎

  comp cat {A , B} {A' , B'} {A'' , B''} (f , α) (g , β) = f ∘s g , record
    { nat = λ (a : A .set) → nat α (g .ap a) ∘s nat β a
    ; nat-eq = λ {a b p} → let open EqRelReason seq in
        begin
          ((mor B'' (f .ap-cong (g .ap-cong p))) ∘s (nat α (g .ap a))) ∘s nat β a
        ≈⟨ comp-cong-l S {g = nat β a} (nat-eq α)  ⟩
          (nat α (g .ap b) ∘s mor B' (g .ap-cong p)) ∘s nat β a
        ≈⟨ comp-assoc-inv S
             {f = nat α (g .ap b)} {g = mor B' (g .ap-cong p)} {h = nat β a} ⟩
          nat α (g .ap b) ∘s (mor B' (g .ap-cong p) ∘s nat β a)
        ≈⟨ comp-cong-r S {f = nat α (g .ap b)} (nat-eq β) ⟩
          (nat α (g .ap b) ∘s nat β b) ∘s (mor B p)
        ∎
    }

  comp-assoc cat {A1 , B1} {A2 , B2} {A3 , B3} {A4 , B4} {f , α} {g , β} {h , γ} =
    comp-assoc S {f = f} {g = g} {h = h} , λ a →
      let open EqRelReason seq
          k = nat α ((g ∘s h) .ap a) ∘s (nat β (h .ap a) ∘s nat γ a)
      in
        begin
          mor B4 (comp-assoc S {f = f} {g = g} {h = h} ` A1 .refl {a}) ∘s k
        ≈⟨ comp-cong-l S {g = k} (resp B4 tt) ⟩
          mor B4 (A4 .refl) ∘s k
        ≈⟨ comp-cong-l S {g = k} (id-mor-inv B4) ⟩
          id S ∘s k
        ≈⟨ id-l S ⟩
          k
        ∎

  comp-cong cat {A , B} {A' , B'} {A'' , B''} {f , α} {f' , α'} {g , β} {g' , β'}
    (ff' , αα') (gg' , ββ') = comp-cong S ff' gg' , λ a → -- seq .sym
      let open EqRelReason seq
      in -- NB: start reading at the bottom..
        begin  -- (comp-cong S ff' gg' ` A .refl {a}) is (ff' `(gg' ` A .refl {a}))
          mor B'' (ff' `(gg' ` A .refl {a})) ∘s (nat α (g .ap a) ∘s nat β a)
        ≈⟨ comp-cong-l S {g = nat α (g .ap a) ∘s nat β a} (resp B'' tt) ⟩
          (mor B'' (A'' .trans (f .ap-cong (gg' ` A .refl)) (ff' ` A' .refl)))
            ∘s (nat α (g .ap a) ∘s nat β a)
        ≈⟨ comp-cong-l S {g = nat α (g .ap a) ∘s nat β a} (comp-mor-inv B'') ⟩
          (mor B'' (ff' ` A' .refl) ∘s mor B'' (f .ap-cong (gg' ` A .refl)))
            ∘s (nat α (g .ap a) ∘s nat β a)
        ≈⟨ comp-assoc-inv S
             {f = mor B'' (ff' ` A' .refl)} {g = mor B'' (f .ap-cong (gg' ` A .refl))}
             {h = nat α (g .ap a) ∘s nat β a} ⟩
          mor B'' (ff' ` A' .refl) ∘s (mor B'' (f .ap-cong (gg' ` A .refl))
            ∘s (nat α (g .ap a) ∘s nat β a))
        ≈⟨ comp-cong-r S {f = mor B'' (ff' ` A' .refl)}
           (comp-assoc S {f = mor B'' (f .ap-cong (gg' ` A .refl))}
             {g = nat α (g .ap a)} {h = nat β a}) ⟩
          mor B'' (ff' ` A' .refl) ∘s ((mor B'' (f .ap-cong (gg' ` A .refl))
            ∘s nat α (g .ap a)) ∘s nat β a)
        ≈⟨ comp-cong-r S {f = mor B'' (ff' ` A' .refl)}
           (comp-cong-l S {g = nat β a} (nat-eq α)) ⟩
          mor B'' (ff' ` A' .refl) ∘s ((nat α (g' .ap a) ∘s mor B' (gg' ` A .refl))
            ∘s nat β a)
        ≈⟨ comp-cong-r S {f = mor B'' (ff' ` A' .refl)}
            (comp-assoc S {f = nat α (g' .ap a)} {g = mor B' (gg' ` A .refl)}
               {h = nat β a}) ⟩
          mor B'' (ff' ` A' .refl) ∘s (nat α (g' .ap a) ∘s (mor B' (gg' ` A .refl)
            ∘s nat β a))
        ≈⟨ comp-assoc S {f = mor B'' (ff' ` A' .refl)} {g = nat α (g' .ap a)}
             {h = (mor B' (gg' ` A .refl) ∘s nat β a)} ⟩
          (mor B'' (ff' ` A' .refl) ∘s nat α (g' .ap a)) ∘s (mor B' (gg' ` A .refl)
            ∘s nat β a)
        ≈⟨ comp-cong-l S {g = mor B' (gg' ` A .refl) ∘s nat β a} (αα' (g' .ap a)) ⟩
          nat α' (g' .ap a) ∘s (mor B' (gg' ` A .refl) ∘s nat β a)
        ≈⟨ comp-cong-r S {f = nat α' (g' .ap a)} (ββ' a) ⟩
          nat α' (g' .ap a) ∘s nat β' a
        ∎

  id cat {A , B} = id S , record
    { nat = λ (a : A .set) → id S
    ; nat-eq =  λ {a b p} → seq .trans {b = mor B p} (id-r S) (seq .sym (id-l S))
    }
  id-l cat {A , B} {A' , B'} {f , α} = id-l S , λ a →
    let open EqRelReason seq
    in
      begin
        (mor B' (id-l S {f = f} ` A .refl)) ∘s (id S ∘s nat α a)
      ≈⟨ comp-cong-l S {g = id S ∘s nat α a} (resp B' tt) ⟩
        (mor B' (A' .refl)) ∘s (id S ∘s nat α a)
      ≈⟨ comp-cong-l S {g = id S ∘s nat α a} (id-mor-inv B') ⟩
        id S ∘s (id S ∘s nat α a)
      ≈⟨ id-l S ⟩
        id S ∘s nat α a
      ≈⟨ id-l S ⟩
        (nat α a)
      ∎

  id-r cat {A , B} {A' , B'} {f , α} = id-r S , λ a →
    let open EqRelReason seq
    in
      begin
        mor B' (id-r S {f = f} ` A .refl) ∘s (nat α a ∘s id S)
      ≈⟨ comp-cong-l S {g = nat α a ∘s id S} (resp B' tt) ⟩
        mor B' (A' .refl) ∘s (nat α a ∘s id S)
      ≈⟨ comp-cong-l S {g = nat α a ∘s id S} (id-mor-inv B') ⟩
        id S ∘s (nat α a ∘s id S)
      ≈⟨ id-l S ⟩
        nat α a ∘s id S
      ≈⟨ id-r S ⟩
        nat α a
      ∎

  -- A different attempt at defining composition...
  -- -- TODO: why doesn (comp (EFunctor _ _) (r-whisker α (#fun g)) β)
  -- -- directly work as second component if I enable all eta-equalities
  -- -- for records?
  -- comp cat {A , B} {A' , B'} {A'' , B''} (f , α) (g , β) =
  --   f ∘s g , record
  --            { nat = comp (EFunctor _ _) (r-whisker α (#fun g)) β .nat
  --            ; nat-eq = comp (EFunctor _ _) (r-whisker α (#fun g)) β .nat-eq }

  -- comp-assoc cat {A1 , B1} {A2 , B2} {A3 , B3} {A4 , B4} {f , α} {g , β} {h , γ} =
  --   comp-assoc S {f = f} {g = g} {h = h} , λ a →
  --     let open EqRelReason seq
  --         lhs' = nat (snd (comp cat (f , α) (comp cat (g , β) (h , γ)))) a
  --         rhs  = nat (snd (comp cat (comp cat (f , α) (g , β)) (h , γ))) a
  --     in
  --       map-rel λ {a b} p → {!!}
  --       -- begin
  --       --   mor B4 (comp-assoc S {f = f} {g = g} {h = h} ` refl (eqr A1)) ∘s lhs'
  --       -- ≈⟨ comp-cong-l S {g = lhs'} (resp B4 tt) ⟩
  --       --   mor B4 (A4 .refl) ∘s lhs'
  --       -- ≈⟨ comp-cong-l S {g = lhs'} (seq .sym (id-mor B4)) ⟩
  --       --   id S ∘s lhs'
  --       -- ≈⟨ id-l S ⟩
  --       --   lhs'
  --       -- ≈⟨ map-rel (λ {a b} p →
  --       --     {!mor-resp B4!}) ⟩

  --       --   rhs
  --       -- ∎

  -- comp-cong cat {A , B} {A' , B'} {A'' , B''} {f , α} {f' , α'} {g , β} {g' , β'}
  --    (ff' , αα') (gg' , ββ') = {!!}

π : {ls lr : Level} → eFunctor (EFam {ls} {lr}) (ESet {ls} {lr})
π = record
  { fun = fst ; mor = fst ; resp = fst
  ; id-mor = map-rel λ p → p
  ; comp-mor = λ { {f = f , _} {g = g , _} →
                   map-rel λ p → f .ap-cong (g .ap-cong p) }
  }


-- -- Another definition of EFam using the comma construction

-- test : ∀ {l} → Set l → Set (lsuc l)
-- test A = {!lift!}

-- EFam' : {ls : Level} → ECat
-- EFam' {ls} = let open ConstantFunctor 1cat0 (CAT {ls} {ls} {{!lzero!}})
--                  !set : eFunctor 1cat CAT
--                  !set = Δobj (ESet {ls})
--              in  (## {ls}) ↓ {!!set!}


-- The Fam variant of an E-CwF
record eCwf {lvs lvr lo lh lr : Level} : Set (lsuc (lvs ⊔ lvr ⊔ lo ⊔ lh ⊔ lr)) where
  field
    Ctx : ECat {lo} {lh} {lr}
    F   : eFunctor (Ctx op) (EFam {lvs} {lvr})

  -- Some notation
  Subst = Ctx .hom
  _~s_ = Ctx .hom-rel
  _∘s_ = Ctx .comp
  infixl 40 _∘s_

  Ty : ePSh Ctx
  Ty = π ∘Func F

  TyS : obj Ctx → eSet
  TyS Γ = fun Ty Γ
  Typ : obj Ctx → Set _
  Typ Γ = set (fun Ty Γ)
  _~_ : {Γ : obj Ctx} → Typ Γ → Typ Γ → Set lvr
  _~_ {Γ} = rel (fun Ty Γ)
  ~eq : {Γ : obj Ctx} → EqRel (fun Ty Γ .rel)
  ~eq {Γ} = eqr (fun Ty Γ)

  _[_] : ∀ {Δ Γ} → Typ Γ → Subst Δ Γ → Typ Δ
  A [ σ ] = mor Ty σ .ap A
  infix 40 _[_]

  Ter : (Γ : obj Ctx) (A : Typ Γ) → Set _
  Ter Γ A = (fun F Γ) .snd .fun A .set

  TerS : (Γ : obj Ctx) → eFunctor (# (TyS Γ)) ESet
  TerS Γ = fun F Γ .snd

  _~t_ : ∀ {Γ A} → Ter Γ A → Ter Γ A → Set _
  _~t_ {Γ} {A} = (fun F Γ) .snd .fun A .rel
  teq : {Γ : obj Ctx} {A : Typ Γ} → _
  teq {Γ} {A} = (fun F Γ) .snd .fun A .eqr

  _[_]t : ∀ {Γ Δ A} (t : Ter Γ A) (σ : Subst Δ Γ) → Ter Δ (A [ σ ])
  u [ σ ]t = F .mor σ .snd .nat _ .ap u
  infix 50 _[_]t

  ι : ∀ {Γ} {A B : Typ Γ} → A ~ B → Ter Γ A → Ter Γ B
  ι {Γ} p = fun F Γ .snd .mor p .ap

  ιirr : ∀ {Γ} {A B : Typ Γ} {p q : A ~ B} {u v : Ter Γ A} → u ~t v → ι p u ~t ι q v
  ιirr {Γ} = fun F Γ .snd .resp tt .map-resp

  ιrefl : ∀ {Γ} {A : Typ Γ} {u : Ter Γ A} → u ~t ι (~eq .refl) u
  ιrefl {Γ} = fun F Γ .snd .id-mor .map-resp (teq .refl)

  ιtrans : ∀ {Γ} {A B C : Typ Γ} {p : B ~ C} {q : A ~ B} {u : Ter Γ A} →
           ι p (ι q u) ~t ι (~eq .trans q p) u
  ιtrans {Γ} = fun F Γ .snd .comp-mor .map-resp (teq .refl)

  field
    -- terminal object
    <> : obj Ctx
    ! :  ∀ {A} → hom Ctx A <>
    !-unique : ∀ {A} {g : hom Ctx A <>} → g ~s !

    -- context extension
    _∙_ : (Γ : obj Ctx) (A : Typ Γ) → obj Ctx
    pp : ∀ {Γ A} → Subst (Γ ∙ A) Γ
    qq : ∀ {Γ A} → Ter (Γ ∙ A) (A [ pp ])
    <_,_> : ∀ {Δ Γ} → (σ : Subst Δ Γ) {A : Typ Γ} (t : Ter Δ (A [ σ ])) → Subst Δ (Γ ∙ A)

    pp<> : ∀ {Δ Γ} {σ : Subst Δ Γ} {A : Typ Γ} {t : Ter Δ (A [ σ ])} →
             pp ∘s < σ , t > ~s σ

    -- TODO: missing laws etc


-- -}
