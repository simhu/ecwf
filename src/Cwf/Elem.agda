-- A formalization of e-category with families based on two presheaves
-- Ty : ePsh C and Ter : ePsh (∫ Ty) where ∫ Ty denotes the categories
-- of elements of Ty.  Note, this is *not* the same as the
-- Fiore/Awodey definition

-- TODO: clean up and refactor using EqRelReason

module Cwf.Elem where

open import Basics
open import Presheaves
open import Opposite
--open import Limits
open import Products

-- Some derived notions to define and use eCwFs
module eCwFNotation {lvs lvr lo lh lr} {Ctx : ECat {lo} {lh} {lr}}
    (Ty : ePSh {lvs} {lvr} Ctx) (Tm : ePSh {lvs} {lvr} (∫ {C = Ctx} Ty)) where
  Subst = hom Ctx
  _∘s_ = Ctx .comp
  infixl 40 _∘s_
  ids = Ctx .id
  _~s_ : ∀ {Γ Δ} (σ τ : Subst Δ Γ) → Set lr
  _~s_ = Ctx .hom-rel

  ~seq : {Δ Γ : obj Ctx} → EqRel {A = Subst Δ Γ} _~s_
  ~seq = Ctx .hom-eqr
  ∘s-assoc = Ctx .comp-assoc
  ∘s-cong = Ctx .comp-cong

  _~el_ : {A B : ∫ {C = Ctx} Ty .obj} → ∫ {C = Ctx} Ty .hom A B → ∫ {C = Ctx} Ty .hom A B → Set lr
  _~el_ = ∫ {C = Ctx} Ty .hom-rel
  _∘el_ = ∫ {C = Ctx} Ty .comp
  infixl 40 _∘el_

  idel = ∫ {C = Ctx} Ty .id

  Typ : (Γ : obj Ctx) → Set lvs
  Typ = λ Γ → set (fun Ty Γ)
  _~_ : {Γ : obj Ctx} → Typ Γ → Typ Γ → Set lvr
  _~_ {Γ} = rel (fun Ty Γ)
  ~eq : {Γ : obj Ctx} → _
  ~eq {Γ} = eqr (fun Ty Γ)

  _[_] : ∀ {Γ Δ} → Typ Γ → Subst Δ Γ → Typ Δ
  A [ σ ] = mor Ty σ .ap A
  infix 40 _[_]

  []-id' : ∀ {Γ} {A B : Typ Γ} → A ~ B → A ~ B [ ids ]
  []-id' = id-mor Ty .map-resp

  []-id : ∀ {Γ} {A : Typ Γ} → A ~ A [ ids ]
  []-id = []-id' (~eq .refl)

  []-assoc' : ∀ {Θ Δ Γ} {τ : Subst Θ Δ} {σ : Subst Δ Γ} {A B : Typ Γ} →
             A ~ B → A [ σ ] [ τ ] ~ B [ σ ∘s τ ]
  []-assoc' = comp-mor Ty .map-resp

  []-assoc : ∀ {Θ Δ Γ} {τ : Subst Θ Δ} {σ : Subst Δ Γ} {A : Typ Γ} →
             A [ σ ] [ τ ] ~ A [ σ ∘s τ ]
  []-assoc = []-assoc' (~eq .refl)

  []-assoc-inv : ∀ {Θ Δ Γ} {τ : Subst Θ Δ} {σ : Subst Δ Γ} {A : Typ Γ} →
             A [ σ ∘s τ ] ~ A [ σ ] [ τ ]
  []-assoc-inv = ~eq .sym []-assoc

  []-resp' : ∀ {Δ Γ} {σ τ : Subst Δ Γ} {A B : Typ Γ} →
               A ~ B → σ ~s τ → A [ σ ] ~ B [ τ ]
  []-resp' q p = resp Ty p ` q

  []-resp-r : ∀ {Δ Γ} {σ τ : Subst Δ Γ} {A : Typ Γ} →
               σ ~s τ → A [ σ ] ~ A [ τ ]
  []-resp-r = []-resp' (~eq .refl)

  []-resp-l : ∀ {Δ Γ} {σ : Subst Δ Γ} {A B : Typ Γ} →
               A ~ B → A [ σ ] ~ B [ σ ]
  []-resp-l q = []-resp' q (~seq .refl)

  Ter = λ Γ A → set (fun Tm (Γ , A))
  _~t_ = λ {Γ A} → rel (fun Tm (Γ , A))
  ~teq : {Γ : obj Ctx} {A : Typ Γ} → _
  ~teq {Γ} {A} = eqr (fun Tm (Γ , A))

  _[_]t : ∀ {Γ Δ A} (t : Ter Γ A) (σ : Subst Δ Γ) → Ter Δ (A [ σ ])
  u [ σ ]t = mor Tm (σ , ~eq .refl) .ap u
  infix 50 _[_]t

  []t-resp-l : ∀ {Δ Γ} {σ : Subst Δ Γ} {A : Typ Γ} {u v : Ter Γ A} →
                u ~t v → u [ σ ]t ~t v [ σ ]t
  []t-resp-l = Tm .resp (~seq .refl) .map-resp


  ι : ∀ {Γ} {A B : Typ Γ} → B ~ A → Ter Γ A → Ter Γ B
  ι {Γ} {A} {B} p u = Tm .mor (ids , trans ~eq p []-id) .ap u

  ιirr' : ∀ {Γ} {A B : Typ Γ} {p q : B ~ A} {u v : Ter Γ A} → u ~t v → ι p u ~t ι q v
  ιirr' {p = p} {q = q} r =
    let lem : (ids , trans ~eq p []-id) ~el (ids , trans ~eq q []-id)
        lem = ~seq .refl
    in Tm .resp lem .map-resp r

  ιirr : ∀ {Γ} {A B : Typ Γ} {p q : B ~ A} {u : Ter Γ A} → ι p u ~t ι q u
  ιirr = ιirr' (~teq .refl)

  -- A special case..
  ιresp : ∀ {Γ A B} {p : B ~ A} {u v : Ter Γ A} → u ~t v → ι p u ~t ι p v
  ιresp = Tm .resp (~seq .refl) .map-resp

  ιrefl : ∀ {Γ} {A : Typ Γ} {u : Ter Γ A} → u ~t ι (~eq .refl) u
  ιrefl {Γ} {A} {u} =
    let lem : u ~t Tm .mor (∫ {C = Ctx} Ty .id) .ap u
        lem = Tm .id-mor ` (~teq .refl)
    in ~teq .trans lem (Tm .resp (~seq .refl) ` (~teq .refl))

  ιtrans : ∀ {Γ} {A B C : Typ Γ} (p : C ~ B) (q : B ~ A) {u : Ter Γ A} →
           ι p (ι q u) ~t ι (~eq .trans p q) u
  ιtrans p q = ~teq .trans (Tm .comp-mor ` (~teq .refl)) (Tm .resp (Ctx .id-l) ` (~teq .refl))

  ιsubst : ∀ {Δ Γ} (σ : Subst Δ Γ) {A B : Typ Γ} (p : B ~ A) (u : Ter Γ A) →
           (ι p u) [ σ ]t ~t ι ([]-resp' p (~seq .refl)) (u [ σ ]t)
  ιsubst σ p u =
    let open EqRelReason ~teq
        lem : (ids , trans ~eq p []-id) ∘el (σ ,  eqr (fun Ty _) .refl)
                ~el (σ ,  eqr (fun Ty _) .refl) ∘el
                      (ids , trans ~eq ([]-resp' p (~seq .refl)) []-id)
        lem = ~seq .trans (Ctx .id-l) (~seq .sym (Ctx .id-r))
    in begin
      (ι p u) [ σ ]t
    ≈⟨ Tm .comp-mor ` (~teq .refl) ⟩
      Tm .mor ((ids , trans ~eq p []-id) ∘el (σ ,  eqr (fun Ty _) .refl)) .ap u
    ≈⟨ Tm .resp lem ` ~teq .refl ⟩
      Tm .mor ((σ ,  eqr (fun Ty _) .refl) ∘el
        (ids , trans ~eq ([]-resp' p (~seq .refl)) []-id)) .ap u
    ≈⟨ ~teq .sym (Tm .comp-mor ` ~teq .refl) ⟩
       ι ([]-resp' p (~seq .refl)) (u [ σ ]t)
    ∎

  ι' : ∀ {Γ} {A B : Typ Γ} → A ~ B → Ter Γ A → Ter Γ B
  ι' p = ι (~eq .sym p)

  []t-assoc : ∀ {Θ Δ Γ} {τ : Subst Θ Δ} {σ : Subst Δ Γ} {A : Typ Γ} {u : Ter Γ A} →
                u [ σ ]t [ τ ]t ~t ι []-assoc (u [ σ ∘s τ ]t)
  []t-assoc {τ = τ} {σ = σ} {u = u} = let open EqRelReason ~teq in
    begin
      u [ σ ]t [ τ ]t
    ≈⟨ Tm .comp-mor ` ~teq .refl ⟩
      Tm .mor ((σ , ~eq .refl) ∘el (τ , ~eq .refl)) .ap u
    ≈⟨ Tm .resp (~seq .sym (Ctx .id-r)) ` ~teq .refl ⟩
      Tm .mor ((σ ∘s τ , ~eq .refl) ∘el (ids , ~eq .trans []-assoc []-id)) .ap u
    ≈⟨ ~teq .sym (Tm .comp-mor ` (~teq .refl)) ⟩
      ι []-assoc (u [ σ ∘s τ ]t)
    ∎

  []t-id : ∀ {Γ} {A} {u : Ter Γ A} → u ~t ι []-id (u [ ids ]t)
  []t-id {u = u} = ~teq .trans (Tm .id-mor ` (~teq .refl))
                     (~teq .sym (~teq .trans (Tm .comp-mor ` (~teq .refl))
                                  (Tm .resp (Ctx .id-l) ` (~teq .refl))))

  -- In an eCwf we will require all of the following categories to
  -- have terminal objects, witnessing the structure of context
  -- extension.  Probably it would make more sense to formalize slices
  -- first..

  -- TODO: we really should have a more abstract definition, so that
  -- it is apparent the functor and natural transformation data of a
  -- cwf morphism induce a functor on the respective cprInp's
  cprInp : (Γ : obj Ctx) (A : Typ Γ) → ECat
  cprInp Γ A = cat where
    cat : ECat
    obj cat = Σ λ Δ → Σ λ (σ : Subst Δ Γ) → Ter Δ (A [ σ ])
    hom cat (Δ , σ , v ) (Δ' , σ' , v' ) =
      Σ λ (τ : Subst Δ Δ') → Σ λ (q : σ ~s σ' ∘s τ) →
        v ~t ι (~eq .trans ([]-resp-r q) (~eq .sym []-assoc)) (v' [ τ ]t)
        -- Alternative definition (?):
        -- ι (~eq .trans []-assoc (~eq .sym ([]-resp-r q))) v ~t v' [ τ ]t
    hom-rel cat (τ , _ , _) (τ' , _ , _) = τ ~s τ'
    refl (hom-eqr cat) = ~seq .refl
    sym (hom-eqr cat) = ~seq .sym
    trans (hom-eqr cat) = ~seq .trans
    comp cat {(Δ , σ , v )} {(Δ' , σ' , v')} {(Δ'' , σ'' , v'')}
        (τ , q , α) (τ' , q' , α') =  -- TODO: clean up
          τ ∘s τ'
          , (let open EqRelReason ~seq in
             begin
               σ
             ≈⟨ q' ⟩
               σ' ∘s τ'
             ≈⟨ comp-cong-l Ctx q ⟩
               (σ'' ∘s τ) ∘s τ'
             ≈⟨ comp-assoc-inv Ctx ⟩
               σ'' ∘s (τ ∘s τ')
             ∎)
          , ~teq .trans α' (~teq .trans (ιresp ([]t-resp-l α))
            (~teq .trans (ιresp (ιsubst _ _ _))
            (~teq .trans (ιtrans _ _)
            (~teq .trans (ιresp []t-assoc)
            (~teq .trans (ιtrans _ _) ιirr)))))

    comp-assoc cat = Ctx .comp-assoc
    comp-cong cat = Ctx .comp-cong
    id cat =  ids , ~seq .sym (Ctx .id-r) , ~teq .trans []t-id ιirr
    id-l cat = Ctx .id-l
    id-r cat = Ctx .id-r

  -- ιswap : ∀ {Γ A B} {u : Ter Γ B} {v : Ter Γ A} (p : B ~ A) (e : u ~t ι p v) → ι (~eq .sym p) u ~t v
  -- ιswap p e = ~teq .trans {!!} {!!}

record eCwF {lvs lvr lo lh lr : Level} : Set (lsuc (lvs ⊔ lvr ⊔ lo ⊔ lh ⊔ lr)) where
  no-eta-equality
  field
    Ctx : ECat {lo} {lh} {lr}
    Ty : ePSh {lvs} {lvr} Ctx
    Tm : ePSh {lvs} {lvr} (∫ {C = Ctx} Ty)
  open eCwFNotation {Ctx = Ctx} Ty Tm
  field
    -- terminal object
    <> : obj Ctx
    ! :  ∀ {A} → hom Ctx A <>
    !-unique : ∀ {A} {g : hom Ctx A <>} → g ~s !
    -- context extension
    _∙_ : (Γ : obj Ctx) (A : Typ Γ) → obj Ctx
    pp : ∀ {Γ A} → Subst (Γ ∙ A) Γ
    qq : ∀ {Γ A} → Ter (Γ ∙ A) (A [ pp ])
    compr : ∀ {Γ A} → isTerminal (cprInp Γ A) (Γ ∙ A , pp , qq)

  <_,_> : ∀ {Δ Γ} → (σ : Subst Δ Γ) {A : Typ Γ} (t : Ter Δ (A [ σ ])) → Subst Δ (Γ ∙ A)
  < σ , t > = compr .isTerminal.! {_ , σ , t}  .fst

  pp<>-inv : ∀ {Δ Γ} {σ : Subst Δ Γ} {A : Typ Γ} {t : Ter Δ (A [ σ ])} →
           σ ~s pp ∘s < σ , t >
  pp<>-inv {σ = σ} {t = t} = (compr .isTerminal.! {_ , σ , t} .snd .fst)

  pp<> : ∀ {Δ Γ} {σ : Subst Δ Γ} {A : Typ Γ} {t : Ter Δ (A [ σ ])} →
           pp ∘s < σ , t > ~s σ
  pp<> = ~seq .sym pp<>-inv

  qq<> : ∀ {Δ Γ} {σ : Subst Δ Γ} {A : Typ Γ} {t : Ter Δ (A [ σ ])} →
            t ~t ι (~eq .trans ([]-resp-r (compr .isTerminal.! {Δ , σ , t} .snd .fst))
                    (~eq .sym []-assoc))
                   (qq [ < σ , t > ]t)
  qq<> {σ = σ} {t = t} = compr .isTerminal.! {_ , σ , t} .snd .snd

  -- TODO: double-check this definition!
  <>-η-id : ∀ {Γ} {A : Typ Γ} → ids {Γ ∙ A} ~s < pp , qq >
  <>-η-id {Γ} {A} = compr .isTerminal.!-η {_ , pp , qq} {id (cprInp Γ A)}

  <>-comp : ∀ {Ξ Δ Γ σ} {A : Typ Γ} {t : Ter Δ (A [ σ ])} {τ : Subst Ξ Δ} →
            < σ , t > ∘s τ ~s < σ ∘s τ , ι' []-assoc (t [ τ ]t) >
  <>-comp {Ξ} {Δ} {Γ} {σ} {A} {t} {τ} =
    compr .isTerminal.!-η {_ , σ ∘s τ , ι' []-assoc (t [ τ ]t)}
      { < σ , t > ∘s τ
      , (let open EqRelReason ~seq in
         begin
          σ ∘s τ
         ≈⟨ comp-cong-l Ctx pp<>-inv ⟩
          (pp ∘s < σ , t >) ∘s τ
         ≈⟨ comp-assoc-inv Ctx ⟩
          pp ∘s (< σ , t > ∘s τ)
         ∎)
      , (let open EqRelReason ~teq in
         begin
           ι _ (t [ τ ]t)
         ≈⟨ ιresp ([]t-resp-l qq<>) ⟩
           ι _ (ι _ (qq [ < σ , t > ]t) [ τ ]t)
         -- ≈⟨ ιresp ([]t-resp-l ιirr) ⟩
         --   ι _ (ι _ (qq [ < σ , t > ]t) [ τ ]t)
         ≈⟨ ιresp (ιsubst _ _ _) ⟩
           ι _ (ι _ (qq [ < σ , t > ]t [ τ ]t))
         ≈⟨ ιtrans _ _ ⟩
           ι _ (qq [ < σ , t > ]t [ τ ]t)
         ≈⟨ ιresp []t-assoc ⟩
           ι _ (ι _ (qq [ < σ , t > ∘s τ ]t))
         ≈⟨ ιtrans _ _ ⟩
           ι _ (qq [ < σ , t > ∘s τ ]t)
         ≈⟨ ιirr ⟩
           ι _ (qq [ < σ , t > ∘s τ ]t)
         ∎)
      }

  <>-η : ∀ {Δ Γ} {A : Typ Γ} {σ : Subst Δ (Γ ∙ A)} →
         σ ~s < pp ∘s σ , ι' []-assoc (qq [ σ ]t) >
  <>-η {Δ} {Γ} {A} {σ} = let open EqRelReason ~seq in
    begin
      σ
    ≈⟨ id-l-inv Ctx ⟩
      ids ∘s σ
    ≈⟨ comp-cong-l Ctx <>-η-id ⟩
      < pp , qq > ∘s σ
    ≈⟨ <>-comp ⟩
      < pp ∘s σ , ι' []-assoc (qq [ σ ]t) >
    ∎


-- -}

record Mor {ks kr : Level}
           {lao lah lar : Level}
           {lbo lbh lbr : Level}
           (A : eCwF {ks} {kr} {lao} {lah} {lar})
           (B : eCwF {ks} {kr} {lbo} {lbh} {lbr}) :
       Set (lao ⊔ lah ⊔ lar ⊔ lbo ⊔ lbh ⊔ lbr ⊔ lsuc (ks ⊔ kr)) where
  no-eta-equality
  open eCwF A using () renaming (Ctx to CtxA ; Ty to TyA ; Tm to TmA)
  open eCwF B using () renaming (Ctx to CtxB ; Ty to TyB ; Tm to TmB)
  field
    ctx : eFunctor CtxA CtxB
    ty : eNat TyA (TyB ∘Func (ctx op-fun))
    tm : eNat TmA (TmB ∘Func ((∫base ctx ty) op-fun))
  -- TODO: preserving terminal objects and comprehension
