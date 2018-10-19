-- A formalization of e-category with families based on two presheaves
-- Ty : ePsh C and Ter : ePsh (∫ Ty) where ∫ Ty denotes the categories
-- of elements of Ty.  Note, this is *not* the same as the
-- Fiore/Awodey definition

module Cwf.Elem where

open import Basics
open import Presheaves

-- Some derived notions to define and use eCwFs
module eCwFNotation {lv lo lh lr} {Ctx : ECat {lo} {lh} {lr}} 
    (Ty : ePSh {lv} Ctx) (Tm : ePSh {lv} (∫ {C = Ctx} Ty)) where 
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

  Typ : (Γ : obj Ctx) → Set lv
  Typ = λ Γ → set (fun Ty Γ)
  _~_ : {Γ : obj Ctx} → Typ Γ → Typ Γ → Set lv
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

  []-resp' : ∀ {Δ Γ} {σ τ : Subst Δ Γ} {A B : Typ Γ} →
               A ~ B → σ ~s τ → A [ σ ] ~ B [ τ ]
  []-resp' q p = resp Ty p ` q

  []-resp : ∀ {Δ Γ} {σ τ : Subst Δ Γ} {A : Typ Γ} →
               σ ~s τ → A [ σ ] ~ A [ τ ]
  []-resp = []-resp' (~eq .refl)

  Ter = λ Γ A → set (fun Tm (Γ , A))
  _~t_ = λ {Γ A} → rel (fun Tm (Γ , A))
  ~teq : {Γ : obj Ctx} {A : Typ Γ} → _
  ~teq {Γ} {A} = eqr (fun Tm (Γ , A))

  _[_]t : ∀ {Γ Δ A} (t : Ter Γ A) (σ : Subst Δ Γ) → Ter Δ (A [ σ ])
  u [ σ ]t = mor Tm (σ , eqr (fun Ty _) .refl) .ap u
  infix 50 _[_]t

  []t-resp-l : ∀ {Δ Γ} {σ : Subst Δ Γ} {A : Typ Γ} {u v : Ter Γ A} →
                u ~t v → u [ σ ]t ~t v [ σ ]t
  []t-resp-l = Tm .resp (~seq .refl) .map-resp


  ι : ∀ {Γ} {A B : Typ Γ} → B ~ A → Ter Γ A → Ter Γ B
  ι {Γ} {A} {B} p u = Tm .mor (ids , trans ~eq p []-id) .ap u

  ιirr : ∀ {Γ} {A B : Typ Γ} {p q : B ~ A} {u v : Ter Γ A} → u ~t v → ι p u ~t ι q v
  ιirr {p = p} {q = q} r =
    let lem : (ids , trans ~eq p []-id) ~el (ids , trans ~eq q []-id)
        lem = ~seq .refl
    in Tm .resp lem .map-resp r

  -- A special case..
  ιresp : ∀ {Γ A B} {p : B ~ A} {u v : Ter Γ A} → u ~t v → ι p u ~t ι p v
  ιresp = Tm .resp (~seq .refl) .map-resp

  ιrefl : ∀ {Γ} {A : Typ Γ} {u : Ter Γ A} → u ~t ι (~eq .refl) u
  ιrefl {Γ} {A} {u} = 
    let lem : u ~t Tm .mor (∫ {C = Ctx} Ty .id) .ap u
        lem = Tm .id-mor ` (~teq .refl)
    in ~teq .trans lem (Tm .resp (~seq .refl) ` (~teq .refl))

  ιtrans : ∀ {Γ} {A B C : Typ Γ} (p : C ~ B) (q : B ~ A) {u : Ter Γ A} → ι p (ι q u) ~t ι (~eq .trans p q) u
  ιtrans p q = ~teq .trans (Tm .comp-mor ` (~teq .refl)) (Tm .resp (Ctx .id-l) ` (~teq .refl))

  ιsubst : ∀ {Δ Γ} (σ : Subst Δ Γ) {A B : Typ Γ} (p : B ~ A) (u : Ter Γ A) →
             (ι p u) [ σ ]t ~t ι ([]-resp' p (~seq .refl)) (u [ σ ]t)
  ιsubst σ p u =
    let -- TODO: clean using EqRel reasoning?
        lem : (ids , trans ~eq p []-id) ∘el (σ ,  eqr (fun Ty _) .refl)
                ~el (σ ,  eqr (fun Ty _) .refl) ∘el (ids , trans ~eq ([]-resp' p (~seq .refl)) []-id)
        lem = ~seq .trans (Ctx .id-l) (~seq .sym (Ctx .id-r))
        mid = Tm .mor ((ids , trans ~eq p []-id) ∘el (σ ,  eqr (fun Ty _) .refl)) .ap u
        lhsmid : (ι p u) [ σ ]t ~t mid
        lhsmid = Tm .comp-mor ` (~teq .refl)
        mid' = Tm .mor ((σ ,  eqr (fun Ty _) .refl) ∘el (ids , trans ~eq ([]-resp' p (~seq .refl)) []-id)) .ap u
        midmid' : mid ~t mid'
        midmid' = Tm .resp lem ` (~teq .refl)
        mid'rhs : mid' ~t ι ([]-resp' p (~seq .refl)) (u [ σ ]t)
        mid'rhs = ~teq .sym (Tm .comp-mor ` (~teq .refl))
    in ~teq .trans lhsmid (~teq .trans midmid' mid'rhs)

  ι' : ∀ {Γ} {A B : Typ Γ} → A ~ B → Ter Γ A → Ter Γ B
  ι' p = ι (~eq .sym p)

  []t-assoc : ∀ {Θ Δ Γ} {τ : Subst Θ Δ} {σ : Subst Δ Γ} {A : Typ Γ} {u : Ter Γ A} →
                u [ σ ]t [ τ ]t ~t ι []-assoc (u [ σ ∘s τ ]t)
  []t-assoc {τ = τ} {σ = σ} {A = A} {u = u} =
    let mid = Tm .mor ((σ , ~eq .refl) ∘el (τ , ~eq .refl)) .ap u 
        lhsmid :  u [ σ ]t [ τ ]t  ~t mid
        lhsmid = Tm .comp-mor ` (~teq .refl)
        -- eq : ((σ , ~eq .refl) ∘el (τ , ~eq .refl)) ~el ((σ ∘s τ , ~eq .refl) ∘el (ids , []-id' []-assoc))
        -- eq =  ~seq .sym (Ctx .id-r)
        midrhs : mid ~t ι []-assoc (u [ σ ∘s τ ]t)
        midrhs = ~teq .trans (Tm .resp (~seq .sym (Ctx .id-r)) ` (~teq .refl))
                   (~teq .sym (Tm .comp-mor ` (~teq .refl)))
    in ~teq .trans lhsmid midrhs

  []t-id : ∀ {Γ} {A} {u : Ter Γ A} → u ~t ι []-id (u [ ids ]t)
  []t-id {u = u} = ~teq .trans (Tm .id-mor ` (~teq .refl))
                     (~teq .sym (~teq .trans (Tm .comp-mor ` (~teq .refl)) 
                                  (Tm .resp (Ctx .id-l) ` (~teq .refl))))

  -- In an eCwf we will require all of the following categories to
  -- have terminal objects, witnessing the structure of context
  -- extension.  Probably it would make more sense to formalize slices
  -- first..
  cprInp : (Γ : obj Ctx) (A : Typ Γ) → ECat
  cprInp Γ A = cat where
    cat : ECat
    obj cat = Σ λ Δ → Σ λ (σ : Subst Δ Γ) → Ter Δ (A [ σ ])
    hom cat (Δ , σ , v ) (Δ' , σ' , v' ) =
      Σ λ (τ : Subst Δ Δ') → Σ λ (q : σ ~s σ' ∘s τ) →
        v ~t ι (~eq .trans ([]-resp q) (~eq .sym []-assoc)) (v' [ τ ]t)
        -- Alternative definition (?):
        -- ι (~eq .trans []-assoc (~eq .sym ([]-resp q))) v ~t v' [ τ ]t
    hom-rel cat (τ , _ , _) (τ' , _ , _) = τ ~s τ'
    refl (hom-eqr cat) = ~seq .refl
    sym (hom-eqr cat) = ~seq .sym
    trans (hom-eqr cat) = ~seq .trans
    comp cat {(Δ , σ , v )} {(Δ' , σ' , v')} {(Δ'' , σ'' , v'')}
        (τ , q , α) (τ' , q' , α') =  -- TODO: clean up
          τ ∘s τ'
          , (let lem : σ ~s ((σ'' ∘s τ) ∘s τ')
                 lem = ~seq .trans q' (Ctx .comp-cong q (~seq .refl))
                 lem2 : (σ'' ∘s τ) ∘s τ' ~s σ'' ∘s (τ ∘s τ')
                 lem2 = ~seq .sym (Ctx .comp-assoc) 
             in ~seq .trans lem lem2)
          , ~teq .trans α' (~teq .trans (ιresp ([]t-resp-l α))
            (~teq .trans (ιresp (ιsubst _ _ _))
            (~teq .trans (ιtrans _ _)
            (~teq .trans (ιresp []t-assoc)
            (~teq .trans (ιtrans _ _) (ιirr (~teq .refl)))))))
    comp-assoc cat = Ctx .comp-assoc 
    comp-cong cat = Ctx .comp-cong
    id cat =  ids , ~seq .sym (Ctx .id-r) , ~teq .trans []t-id (ιirr (~teq .refl))
    id-l cat = Ctx .id-l
    id-r cat = Ctx .id-r    
  
  -- ιswap : ∀ {Γ A B} {u : Ter Γ B} {v : Ter Γ A} (p : B ~ A) (e : u ~t ι p v) → ι (~eq .sym p) u ~t v
  -- ιswap p e = ~teq .trans {!!} {!!}

record eCwF {lv lo lh lr : Level} : Set (lsuc (lv ⊔ lo ⊔ lh ⊔ lr)) where
  field
    Ctx : ECat {lo} {lh} {lr}
    Ty : ePSh {lv} Ctx
    Tm : ePSh {lv} (∫ {C = Ctx} Ty)
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
    compr : ∀ {Γ A} → isTerminal {C = cprInp Γ A} (Γ ∙ A , pp , qq)

  <_,_> : ∀ {Δ Γ} → (σ : Subst Δ Γ) {A : Typ Γ} (t : Ter Δ (A [ σ ])) → Subst Δ (Γ ∙ A)
  < σ , t > = compr (_ , σ , t) .fst .fst

  pp<> : ∀ {Δ Γ} {σ : Subst Δ Γ} {A : Typ Γ} {t : Ter Δ (A [ σ ])} →
           pp ∘s < σ , t > ~s σ
  pp<> {σ = σ} {t = t} = ~seq .sym (compr (_ , σ , t)  .fst .snd .fst)

  qq<>' : ∀ {Δ Γ} {σ : Subst Δ Γ} {A : Typ Γ} {t : Ter Δ (A [ σ ])} →
            t ~t ι (~eq .trans ([]-resp (compr (Δ , σ , t) .fst .snd .fst))
                    (~eq .sym []-assoc))
                   (qq [ < σ , t > ]t)
  qq<>' {σ = σ} {t = t} = compr (_ , σ , t) .fst .snd .snd


-- -}
