module ECwfFam where

open import Agda.Primitive
open import EBasics

--------------------------------------------------------------------------------

-- We can restrict a category to the category which only contains its
-- isos (a groupoid)
-- (Not sure if this is actually useful.)
toIsoCat : ∀ {lo lh lr} → ECat {lo} {lh} {lr} → ECat {lo} {lh ⊔ lr} {lr}
toIsoCat {lo} {lh} {lr} C = cat where
  _~_ : ∀ {a b} → hom C a b → hom C a b → Set lr
  _~_ = C ._∼_
  _∘c_ = C ._∘_
  infixl 40 _∘c_

  idc : {a : C .obj} → hom C a a
  idc = C .id

  Ceq = C .∼-eq

  cat : ECat
  obj cat = C .obj
  hom cat a b =  Σ λ (f : hom C a b) →
                 Σ λ (fi : hom C b a) → 
                    (f ∘c fi ~ idc) × (fi ∘c f ~ idc)
  _∼_ cat (f , fi) (g , gi) = f ~ g
  refl (∼-eq cat) = C .∼-eq .refl
  sym (∼-eq cat) = C .∼-eq .sym
  trans (∼-eq cat) = C .∼-eq .trans
  _∘_ cat {a} {b} {c} (f , fi , fr , fl) (g , gi , gr , gl) = 
    let
      fgr =  let open EqRelReason Ceq in
        begin
          ((f ∘c g) ∘c (gi ∘c fi)) 
        ≈⟨ Ceq .sym (C .∘-assoc) ⟩
          (f ∘c (g ∘c (gi ∘c fi))) 
        ≈⟨ ∘-cong-r C (C .∘-assoc) ⟩
          (f ∘c ((g ∘c gi) ∘c fi))
        ≈⟨ ∘-cong-r C (∘-cong-l C gr) ⟩
          (f ∘c (idc ∘c fi))
        ≈⟨ ∘-cong-r C (C .id-l) ⟩
          (f ∘c fi)
        ≈⟨ fr ⟩
          idc
        ∎ 
      fgl =  let open EqRelReason Ceq in
        begin
          ((gi ∘c fi) ∘c (f ∘c g)) 
        ≈⟨ Ceq .sym (C .∘-assoc) ⟩
          (gi ∘c (fi ∘c (f ∘c g)))
        ≈⟨ ∘-cong-r C (C .∘-assoc) ⟩
          (gi ∘c ((fi ∘c f) ∘c g))
        ≈⟨ ∘-cong-r C (∘-cong-l C fl) ⟩
          (gi ∘c (idc ∘c g))
        ≈⟨ ∘-cong-r C (C .id-l) ⟩
          (gi ∘c g)
        ≈⟨ gl ⟩
          idc
        ∎ 
    in
      f ∘c g , gi ∘c fi , fgr , fgl
  ∘-assoc cat =  C .∘-assoc
  ∘-cong cat = C .∘-cong
  id cat =  idc ,  idc ,  C .id-l ,  C .id-l
  id-l cat = C .id-l
  id-r cat = C .id-r


ESetIso : {l : Level} → ECat
ESetIso {l} = toIsoCat (ESet {l})


--------------------------------------------------------------------------------

-- Question: One way to define EFam could be as the category of
-- elements of the functor (probably misses an op somewhere?)
--   Cat(-, ESet) ∘ #

EFam : {ls : Level} → ECat
EFam {ls}  = cat where
  cat : ECat
  obj cat = Σ λ (A : eSet {ls} {ls}) → eFunctor {ls} {ls} {lzero} (# A) (ESet {ls}) 
  hom cat (A , B) (A' , B') = Σ λ (f : hom (ESet {ls}) A A') → eNat B (B' ∘Func (#fun {ls} {A} {A'} f))
  _∼_ cat {(A , B)} {(A' , B')} (f , α) (g , β) =
    Σ λ (p : ESet ._∼_ f g) →
    ∀ (a : A .set)
    -- ∀ {x y : A .set} (q : A .rel x y) → 
    let -- foo : A' .rel (f .fst x) (g .fst y)
        -- foo = p q 
        -- bla : {a b : fun B x .set} →
        --         fun B x .rel a b →
        --         fun (B' ∘Func #fun f) x .rel (nat α x .fst a) (nat α x .fst b)
        -- bla = nat α x .snd
        -- bla2 : fun B x .set → fun (B' ∘Func #fun f) x .set
        -- bla2 = mor B' () (nat α x .fst) 
        -- bla3 : fun B x .set → fun (B' ∘Func #fun g) x .set
        -- bla3 = nat β x .fst

    in {!!}
  --               {! ∀ !} -- ( ∀ a → ESet ._∼_ (nat α a) {! nat β a!} )
  ∼-eq cat = {!!}
  _∘_ cat = {!!}
  ∘-assoc cat = {!!}
  ∘-cong cat = {!!}
  id cat = {!!}
  id-l cat = {!!}
  id-r cat = {!!}
-- obj EFam = {! !}
-- hom EFam = {!!}
-- _∼_ EFam = {!!}
-- ∼-eq EFam = {!!}
-- _∘_ EFam = {!!}
-- ∘-assoc EFam = {!!}
-- ∘-cong EFam = {!!}
-- id EFam = {!!}
-- id-l EFam = {!!}
-- id-r EFam = {!!}



