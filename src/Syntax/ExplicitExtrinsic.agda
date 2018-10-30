-- Type theory presented with an extrinsic explicit syntax
module Syntax.ExplicitExtrinsic where

open import Agda.Primitive
open import Basics
open import Presheaves

module _ {l : Level} where
  data Raw : Set l where
    -- raw contexts
    ε : Raw
    _∙_ : Raw → Raw → Raw
    -- raw term
    qq : Raw                      -- variables
    _[_] : Raw → Raw → Raw         -- substitution in terms
    -- raw substitutions
    comps : Raw → Raw → Raw       -- TODO: Ctx? for mediating object
    ids : Raw
    ! : Raw
    pp : Raw
    <_,_> : Raw → Raw → Raw

  infixl 30 _∙_
  infixl 60 _[_]

  data _⊢ : (Γ : Raw) → Set l
  data _⊢_ : (Γ A : Raw) → Set l
  data _⊢_~_ : (Γ A B : Raw) → Set l
  data _⊢_∈_ : (Γ t A : Raw) → Set l
  data _⊢_~_∈_ : (Γ u v A : Raw) → Set l
  data _∈_⇒_ : (σ Δ Γ : Raw) → Set l
  data _~_∈_⇒_ : (σ τ Δ Γ : Raw) → Set l

  -- data Ctx where
  --   ctx-nil : Ctx
  --   ctx-cons : (Γ : Ctx) {A : Raw} (p : Γ ⊢ A) → Ctx

  data _⊢ where
    ctx-nil :
      -----
      ε ⊢

    ctx-cons :
      ∀ {Γ A} →
      Γ ⊢ → Γ ⊢ A →
      --------------
      Γ ∙ A ⊢

  data _⊢_ where
    ty-subst :
      ∀ {σ Δ Γ A} →
      Γ ⊢ A → σ ∈ Δ ⇒ Γ →
      ---------------------
      Δ ⊢ A [ σ ]

  data _⊢_~_ where
    ty-eq-subst :
      ∀ {σ σ' Δ Γ A A'} →
      Γ ⊢ A ~ A' → σ ~ σ' ∈ Δ ⇒ Γ →
      -------------------------------
      Δ ⊢ A [ σ ] ~ A' [ σ' ]

    ty-eq-id :
      ∀ {Γ A} →
      Γ ⊢ A →
      -----------------
      Γ ⊢ A ~ A [ ids ]

    ty-eq-assoc :
      ∀ {Ξ Δ Γ σ τ A} →
      Γ ⊢ A →
      σ ∈ Δ ⇒ Γ → τ ∈ Ξ ⇒ Δ →
      ------------------------------------
      Ξ ⊢ A [ σ ] [ τ ] ~ A [ comps σ τ ]

    ty-eq-refl :
      ∀ {Γ A} →
      Γ ⊢ A →
      ---------
      Γ ⊢ A ~ A
    ty-eq-sym :
      ∀ {Γ A B} →
      Γ ⊢ A ~ B →
      ------------
      Γ ⊢ B ~ A
    ty-eq-trans :
      ∀ {Γ A B C} →
      Γ ⊢ A ~ B → Γ ⊢ B ~ C →
      ------------------------
      Γ ⊢ A ~ C

  data _⊢_∈_ where
    ter-qq :
      ∀ {Γ A} →
      Γ ⊢ A →
      ----------------------
      Γ ∙ A ⊢ qq ∈ A [ pp ]

    ter-subst :
      ∀ {σ Δ Γ A t} →
      Γ ⊢ t ∈ A → σ ∈ Δ ⇒ Γ →
      -------------------------
      Δ ⊢ t [ σ ] ∈ A [ σ ]

    ter-ty-eq :
      ∀ {Γ A B t} →
      Γ ⊢ t ∈ A → Γ ⊢ A ~ B →
      ------------------------
      Γ ⊢ t ∈ B

  data _⊢_~_∈_ where
    ter-eq-qq<> :
      ∀ {Δ Γ σ t A } →
      σ ∈ Δ ⇒ Γ → Γ ⊢ A → Δ ⊢ t ∈ A [ σ ] →
      ---------------------------------------
      Δ ⊢ qq [ < σ , t > ] ~ t ∈ A [ σ ] -- use lhs for type?

    ter-eq-subst :
      ∀ {σ σ' Δ Γ A t t'} →
      Γ ⊢ t ~ t' ∈ A → σ ~ σ' ∈ Δ ⇒ Γ →
      -----------------------------------
      Δ ⊢ t [ σ ] ~ t' [ σ' ] ∈ A [ σ ]

    ter-eq-id :
      ∀ {Γ A t} →
      Γ ⊢ t ∈ A →
      ----------------------
      Γ ⊢ t ~ t [ ids ] ∈ A

    ter-eq-assoc :
      ∀ {Ξ Δ Γ σ τ A t} →
      Γ ⊢ t ∈ A →
      σ ∈ Δ ⇒ Γ → τ ∈ Ξ ⇒ Δ →
      -----------------------------------------------------
      Ξ ⊢ t [ σ ] [ τ ] ~ t [ comps σ τ ] ∈ A [ σ ] [ τ ]

    ter-eq-refl :
      ∀ {Γ A t} →
      Γ ⊢ t ∈ A →
      --------------
      Γ ⊢ t ~ t ∈ A
    ter-eq-sym :
      ∀ {Γ A u v} →
      Γ ⊢ u ~ v ∈ A →
      ----------------
      Γ ⊢ v ~ u ∈ A
    ter-eq-trans :
      ∀ {Γ A u v w} →
      Γ ⊢ u ~ v ∈ A → Γ ⊢ v ~ w ∈ A →
      ---------------------------------
      Γ ⊢ u ~ w ∈ A

  data _∈_⇒_ where
    subst-pp :
      ∀ {Γ A} →
      Γ ⊢ A →
      ---------------
      pp ∈ Γ ∙ A ⇒ Γ

    subst-! :
      ∀ {Γ} →
      Γ ⊢ →
      ----------
      ! ∈ ε ⇒ Γ

    subst-<> :
      ∀ {Δ Γ σ t A} →
      σ ∈ Δ ⇒ Γ → Γ ⊢ A → Δ ⊢ t ∈ A [ σ ] →
      ----------------------------------------
      < σ , t > ∈ Δ ⇒ Γ ∙ A

    subst-id :
      ∀ {Γ} →
      Γ ⊢ →
      ------------
      ids ∈ Γ ⇒ Γ

    subst-comp :
      ∀ {Ξ Δ Γ σ τ} →
      σ ∈ Δ ⇒ Γ → τ ∈ Ξ ⇒ Δ →
      -------------------------
      comps σ τ ∈ Ξ ⇒ Γ

  data _~_∈_⇒_ where
    subst-eq-!-η :
      ∀ {Γ σ} →
      σ ∈ ε ⇒ Γ →
      ---------------
      ! ~ σ ∈ ε ⇒ Γ

    subst-eq-<>-η :
      ∀ {Δ Γ σ A} →
      σ ∈ Δ ⇒ Γ ∙ A →
      -------------------------------------------
      < comps pp σ , qq [ σ ] > ~ σ ∈ Δ ⇒ Γ ∙ A

    subst-eq-pp<> :
      ∀ {Δ Γ σ t A} →
      σ ∈ Γ ⇒ Δ → Γ ⊢ A → Δ ⊢ t ∈ A [ σ ] →
      ---------------------------------------
      comps pp < σ , t > ~ σ ∈ Δ ⇒ Γ

    subst-eq-assoc :
      ∀ {Θ Ξ Δ Γ σ τ ξ} →
      σ ∈ Δ ⇒ Γ → τ ∈ Ξ ⇒ Δ → ξ ∈ Θ ⇒ Ξ →
      ---------------------------------------------------
      comps σ (comps τ ξ) ~ comps (comps σ τ) ξ ∈ Θ ⇒ Γ

    subst-eq-id-l :
      ∀ {Δ Γ σ} →
      σ ∈ Δ ⇒ Γ →
      ------------------------
      comps ids σ ~ σ ∈ Δ ⇒ Γ

    subst-eq-id-r :
      ∀ {Δ Γ σ} →
      σ ∈ Δ ⇒ Γ →
      ------------------------
      comps σ ids ~ σ ∈ Δ ⇒ Γ

    subst-eq-comp :
      ∀ {Ξ Δ Γ σ σ' τ τ'} →
      σ ~ σ' ∈ Δ ⇒ Γ → τ ~ τ' ∈ Ξ ⇒ Δ →
      ------------------------------------
      comps σ τ ~ comps σ' τ' ∈ Ξ ⇒ Γ

    subst-eq-<> :
      ∀ {Δ Γ σ σ' A t t'} →
      Γ ⊢ A → σ ~ σ ∈ Δ ⇒ Γ → Δ ⊢ t ~ t' ∈ A [ σ ] →
      -------------------------------------------------
      < σ , t > ~ < σ' , t' > ∈ Δ ⇒ Γ ∙ A

    subst-eq-refl :
      ∀ {Δ Γ σ} →
      σ ∈ Δ ⇒ Γ →
      --------------
      σ ~ σ ∈ Δ ⇒ Γ
    subst-eq-sym :
      ∀ {Δ Γ σ τ} →
      σ ~ τ ∈ Δ ⇒ Γ →
      ----------------
      τ ~ σ ∈ Δ ⇒ Γ
    subst-eq-trans :
      ∀ {Δ Γ σ τ ξ} →
      σ ~ τ ∈ Δ ⇒ Γ → τ ~ ξ ∈ Δ ⇒ Γ →
      ---------------------------------
      σ ~ ξ ∈ Δ ⇒ Γ


  ------------------------------------------------------------------------------
  ctx-cat : ECat
  obj ctx-cat = Σ _⊢
  hom ctx-cat Δ Γ = Σ (_∈ fst Δ ⇒ fst Γ)
  hom-rel ctx-cat {Δ} {Γ} σ τ = fst σ ~ fst τ ∈ fst Δ ⇒ fst Γ
  hom-eqr ctx-cat = record
    { refl =  λ {σ} → subst-eq-refl (snd σ)
    ; sym = subst-eq-sym
    ; trans = subst-eq-trans
    }
  comp ctx-cat (σ , pσ) (τ , pτ) = comps σ τ , subst-comp pσ pτ
  comp-assoc ctx-cat {f = σ , pσ} {τ , pτ} {ξ , pξ} = subst-eq-assoc pσ pτ pξ
  comp-cong ctx-cat = subst-eq-comp
  id ctx-cat {Γ , pΓ} = ids , subst-id pΓ
  id-l ctx-cat {f = σ , pσ} = subst-eq-id-l pσ
  id-r ctx-cat {f = σ , pσ} = subst-eq-id-r pσ

  ty-set : (Γ : Raw) → eSet
  set (ty-set Γ) = Σ (Γ ⊢_)
  rel (ty-set Γ) (A , pA) (B , pB) = Γ ⊢ A ~ B
  eqr (ty-set Γ) = record { refl = λ {ApA} → ty-eq-refl (snd ApA)
                          ; sym = ty-eq-sym
                          ; trans = ty-eq-trans }

  ty-map : ∀ {Δ Γ σ} (pσ : σ ∈ Δ ⇒ Γ) → eMap (ty-set Γ) (ty-set Δ)
  ty-map {Δ} {Γ} {σ} pσ = record
    { ap = λ ApA → fst ApA [ σ ] , ty-subst (snd ApA) pσ
    ; ap-cong = λ AB → ty-eq-subst AB (subst-eq-refl pσ)
    }

  ty-resp : ∀ {Δ Γ σ τ} {pσ : σ ∈ Δ ⇒ Γ} {pτ : τ ∈ Δ ⇒ Γ} (p : σ ~ τ ∈ Δ ⇒ Γ) →
            eMapRel (ty-map pσ) (ty-map pτ)
  ty-resp {Δ} {Γ} {σ} {τ} {pσ} {pτ} p = map-rel λ x → ty-eq-subst x p

  ty-psh : ePSh ctx-cat
  ty-psh = record
    { fun =  λ { (Γ , pΓ) → ty-set Γ }
    ; mor =  λ { (σ , pσ) → ty-map pσ }
    ; resp = ty-resp
    ; id-mor = map-rel λ { {b = B , pB} AB → ty-eq-trans AB (ty-eq-id pB) }
    ; comp-mor = λ { {f = σ , pσ} {g = τ , pτ} → map-rel
                     λ { {A , pA} {B , pB} AB →
                         ty-eq-trans (ty-eq-assoc pA pτ pσ)
                           (ty-eq-subst AB (subst-eq-refl (subst-comp pτ pσ)))
                       }
                   }
    }
