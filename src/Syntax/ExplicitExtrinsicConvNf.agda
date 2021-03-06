{-# OPTIONS --without-K #-}
open import Basics
open import Presheaves
open import Cwf.Elem
open import Products using (isTerminal)

-- Type theory presented with an extrinsic explicit syntax, where the
-- application of the conversion rule is only allowed directly when
-- introducing a term.  This makes the derivations of terms
-- syntax-directed.

-- For now fix the level to not have the annoying constructor name
-- issue when using C-c C-c.
module Syntax.ExplicitExtrinsicConvNf where

l = lzero

data Raw : Set l where
  -- raw contexts
  ε : Raw
  _∙_ : Raw → Raw → Raw
  -- raw term
  qq : Raw                        -- variables
  _[_to_] : Raw → Raw → Raw → Raw -- type substitution
  _[_to_at_] : Raw → Raw → Raw → Raw → Raw -- term substitution
  -- raw substitutions
  comps : Raw → Raw → Raw → Raw
  ids : Raw
  ! : Raw
  pp : Raw
  <_,_> : Raw → Raw → Raw

infixl 30 _∙_
infixl 60 _[_to_]
infixl 60 _[_to_at_]

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
    Γ ⊢ →
    Γ ⊢ A →
    --------------
    Γ ∙ A ⊢

data _⊢_ where
  ty-subst :
    ∀ {σ Δ Γ A} →
    Γ ⊢ →
    Γ ⊢ A → σ ∈ Δ ⇒ Γ →
    ---------------------
    Δ ⊢ A [ σ to Γ ]

data _⊢_~_ where
  ty-eq-subst :
    ∀ {σ σ' Δ Γ A A'} →
    Γ ⊢ A ~ A' → σ ~ σ' ∈ Δ ⇒ Γ →
    -------------------------------
    Δ ⊢ A [ σ to Γ ] ~ A' [ σ' to Γ ]

  ty-eq-id :
    ∀ {Γ A} →
    Γ ⊢ A →
    -----------------
    Γ ⊢ A ~ A [ ids to Γ ]

  ty-eq-assoc :
    ∀ {Ξ Δ Γ σ τ A} →
    Γ ⊢ A →
    σ ∈ Δ ⇒ Γ → τ ∈ Ξ ⇒ Δ →
    ------------------------------------
    Ξ ⊢ A [ σ to Γ ] [ τ to Δ ] ~ A [ comps Δ σ τ to Γ ]

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
    Γ ⊢ B →
    Γ ⊢ A ~ B → Γ ⊢ B ~ C →
    ------------------------
    Γ ⊢ A ~ C

data _⊢_∈_ where
  ter-qq-conv :
    ∀ {Γ A B} →
    Γ ⊢ A →
    Γ ∙ A ⊢ A [ pp to Γ ] ~ B →
    -----------------------------
    Γ ∙ A ⊢ qq ∈ B

  ter-subst-conv :
    ∀ {σ Δ Γ A B t} →
    Γ ⊢ →
    Γ ⊢ t ∈ A → σ ∈ Δ ⇒ Γ →
    Γ ⊢ A →
    Δ ⊢ A [ σ to Γ ] ~ B →
    ----------------------------------
    Δ ⊢ t [ σ to Γ at A ] ∈ B


data _⊢_~_∈_ where
  ter-eq-qq<> :
    ∀ {Δ Γ σ t A } →
    σ ∈ Δ ⇒ Γ → Γ ⊢ A → Δ ⊢ t ∈ A [ σ to Γ ] →
    ---------------------------------------
    Δ ⊢ qq [ < σ , t > to Γ ∙ A at A [ pp to Γ ] ] ~ t ∈ A [ σ to Γ ] -- use lhs for type?

  ter-eq-subst :
    ∀ {σ σ' Δ Γ A B t t'} →
    Γ ⊢ t ~ t' ∈ A → σ ~ σ' ∈ Δ ⇒ Γ →
    Γ ⊢ A ~ B → -- ??
    Γ ⊢ t' ∈ A → -- ?? helps in ty-cong
    -----------------------------------
    Δ ⊢ t [ σ to Γ at A ] ~ t' [ σ' to Γ at B ] ∈ A [ σ to Γ ]

  ter-eq-id :
    ∀ {Γ A t} →
    Γ ⊢ t ∈ A →
    ----------------------
    Γ ⊢ t ~ t [ ids to Γ at A ] ∈ A

  ter-eq-assoc :
    ∀ {Ξ Δ Γ σ τ A t} →
    Γ ⊢ t ∈ A →
    σ ∈ Δ ⇒ Γ → τ ∈ Ξ ⇒ Δ →
    -----------------------------------------------------
    Ξ ⊢ t [ σ to Γ at A ] [ τ to Δ at A [ σ to Γ ] ] ~ t [ comps Δ σ τ to Γ at A ] ∈ A [ σ to Γ ] [ τ to Δ ]

  ter-eq-ty-eq :
    ∀ {Γ A B t s} →
    Γ ⊢ A → Γ ⊢ t ∈ A → Γ ⊢ s ∈ A →
    Γ ⊢ t ~ s ∈ A → Γ ⊢ A ~ B →
    -------------------------------
    Γ ⊢ t ~ s ∈ B

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
    Γ ⊢ v ∈ A →
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
    ! ∈ Γ ⇒ ε

  subst-<> :
    ∀ {Δ Γ σ t A} →
    σ ∈ Δ ⇒ Γ → Γ ⊢ A → Δ ⊢ t ∈ A [ σ to Γ ] →
    ----------------------------------------
    < σ , t > ∈ Δ ⇒ Γ ∙ A

  subst-id :
    ∀ {Γ} →
    Γ ⊢ →
    ------------
    ids ∈ Γ ⇒ Γ

  subst-comp :
    ∀ {Ξ Δ Γ σ τ} →
    Δ ⊢ → σ ∈ Δ ⇒ Γ → τ ∈ Ξ ⇒ Δ →
    --------------------------------
    comps Δ σ τ ∈ Ξ ⇒ Γ

data _~_∈_⇒_ where
  subst-eq-!-η :
    ∀ {Γ σ} →
    σ ∈ Γ ⇒ ε →
    ---------------
    σ ~ ! ∈ Γ ⇒ ε

  subst-eq-<>-η :
    ∀ {Δ Γ σ A} →
    σ ∈ Δ ⇒ Γ ∙ A →
    -------------------------------------------
    σ ~ < comps (Γ ∙ A) pp σ , qq [ σ to Γ ∙ A at A [ pp to Γ ] ] > ∈ Δ ⇒ Γ ∙ A

  subst-eq-pp<> :
    ∀ {Δ Γ σ t A} →
    σ ∈ Δ ⇒ Γ → Γ ⊢ A → Δ ⊢ t ∈ A [ σ to Γ ] →
    ---------------------------------------
    comps (Γ ∙ A) pp < σ , t > ~ σ ∈ Δ ⇒ Γ

  subst-eq-assoc :
    ∀ {Θ Ξ Δ Γ σ τ ξ} →
    σ ∈ Δ ⇒ Γ → τ ∈ Ξ ⇒ Δ → ξ ∈ Θ ⇒ Ξ →
    ---------------------------------------------------
    comps Δ σ (comps Ξ τ ξ) ~ comps Ξ (comps Δ σ τ) ξ ∈ Θ ⇒ Γ

  subst-eq-id-l :
    ∀ {Δ Γ σ} →
    σ ∈ Δ ⇒ Γ →
    ------------------------
    comps Γ ids σ ~ σ ∈ Δ ⇒ Γ

  subst-eq-id-r :
    ∀ {Δ Γ σ} →
    σ ∈ Δ ⇒ Γ →
    ------------------------
    comps Δ σ ids ~ σ ∈ Δ ⇒ Γ

  subst-eq-comp :
    ∀ {Ξ Δ Γ σ σ' τ τ'} →
    Δ ⊢ → σ ~ σ' ∈ Δ ⇒ Γ → τ ~ τ' ∈ Ξ ⇒ Δ →
    ------------------------------------------
    comps Δ σ τ ~ comps Δ σ' τ' ∈ Ξ ⇒ Γ

  -- TODO: use subst-eq-<> again and refactor m-resp
  -- subst-eq-<> :
  --   ∀ {Δ Γ σ σ' A t t'} →
  --   Γ ⊢ A → σ ~ σ' ∈ Δ ⇒ Γ → Δ ⊢ t ~ t' ∈ A [ σ to Γ ] →
  --   -----------------------------------------------------------
  --   < σ , t > ~ < σ' , t' > ∈ Δ ⇒ Γ ∙ A

  subst-eq-<>-l :
    ∀ {Δ Γ σ A t t'} →
    Γ ⊢ A → σ ∈ Δ ⇒ Γ → Δ ⊢ t ~ t' ∈ A [ σ to Γ ] →
    -------------------------------------------------------
    < σ , t > ~ < σ , t' > ∈ Δ ⇒ Γ ∙ A

  subst-eq-<>-r :
    ∀ {Δ Γ σ σ' A t} →
    Γ ⊢ A → σ ~ σ' ∈ Δ ⇒ Γ → Δ ⊢ t ∈ A [ σ to Γ ] →
    -------------------------------------------------------
    < σ , t > ~ < σ' , t > ∈ Δ ⇒ Γ ∙ A


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
    τ ∈ Δ ⇒ Γ → -- ???
    σ ~ τ ∈ Δ ⇒ Γ → τ ~ ξ ∈ Δ ⇒ Γ →
    ---------------------------------
    σ ~ ξ ∈ Δ ⇒ Γ

------------------------------------------------------------------------------

ter-eq-subst' :
    ∀ {σ Δ Γ A t t'} →
    Γ ⊢ t ~ t' ∈ A → σ ∈ Δ ⇒ Γ →
    Γ ⊢ A → -- ??
    Γ ⊢ t' ∈ A → -- ?????
    -----------------------------------
    Δ ⊢ t [ σ to Γ at A ] ~ t' [ σ to Γ at A ] ∈ A [ σ to Γ ]
ter-eq-subst' ptt' pσ pA pt' = ter-eq-subst ptt' (subst-eq-refl pσ) (ty-eq-refl pA) pt'

ty-eq-subst' :
  ∀ {σ Δ Γ A A'} →
  Γ ⊢ A ~ A' → σ ∈ Δ ⇒ Γ →
  -------------------------------
  Δ ⊢ A [ σ to Γ ] ~ A' [ σ to Γ ]
ty-eq-subst' aa' pσ = ty-eq-subst aa' (subst-eq-refl pσ)

ter-qq :
  ∀ {Γ A} →
  Γ ⊢ →
  Γ ⊢ A →
  ----------------------
  Γ ∙ A ⊢ qq ∈ A [ pp to Γ ]
ter-qq pΓ pA = ter-qq-conv pA (ty-eq-refl (ty-subst pΓ pA (subst-pp pA)))

ter-subst :
  ∀ {σ Δ Γ A t} →
  Γ ⊢ →
  Γ ⊢ A →
  Γ ⊢ t ∈ A → σ ∈ Δ ⇒ Γ →
  -------------------------
  Δ ⊢ t [ σ to Γ at A ] ∈ A [ σ to Γ ]
ter-subst pΓ pA pt pσ = ter-subst-conv pΓ pt pσ pA (ty-eq-refl (ty-subst pΓ pA pσ))

ter-ty-eq :
  ∀ {Γ A B t} →
  Γ ⊢ A → -- ??
  Γ ⊢ B →
  Γ ⊢ t ∈ A → Γ ⊢ A ~ B →
  ------------------------
  Γ ⊢ t ∈ B
ter-ty-eq pA pB (ter-qq-conv pC pCpA) pAB = ter-qq-conv pC (ty-eq-trans pA pCpA pAB)
ter-ty-eq pA pB (ter-subst-conv pΔ pt pσ pC pCσB) pAB =
  ter-subst-conv pΔ pt pσ pC (ty-eq-trans pA pCσB pAB)


subst-eq-<> :
  ∀ {Δ Γ σ σ' A t t'} →
  Γ ⊢ → -- ???
  Γ ⊢ A →
  σ ∈ Δ ⇒ Γ → σ' ∈ Δ ⇒ Γ →
  Δ ⊢ t ∈ A [ σ to Γ ] →  Δ ⊢ t' ∈ A [ σ to Γ ] → -- ???
  σ ~ σ' ∈ Δ ⇒ Γ → Δ ⊢ t ~ t' ∈ A [ σ to Γ ] →
  -------------------------------------------------
  < σ , t > ~ < σ' , t' > ∈ Δ ⇒ Γ ∙ A
subst-eq-<> pΓ pA pσ pσ' pt pt' pσσ' ptt' =
  subst-eq-trans
    (subst-<> pσ' pA
      (ter-ty-eq (ty-subst pΓ pA pσ) (ty-subst pΓ pA pσ') pt
        (ty-eq-subst (ty-eq-refl pA) pσσ')))
    (subst-eq-<>-r pA pσσ' pt)
    (subst-eq-<>-l pA pσ' (ter-eq-ty-eq (ty-subst pΓ pA pσ) pt pt' ptt' (ty-eq-subst (ty-eq-refl pA) pσσ')))



------------------------------------------------------------------------------

ctx-cat : ECat
obj ctx-cat = Σ _⊢
hom ctx-cat Δ Γ = Σ (_∈ fst Δ ⇒ fst Γ)
hom-rel ctx-cat {Δ} {Γ} σ τ = fst σ ~ fst τ ∈ fst Δ ⇒ fst Γ
hom-eqr ctx-cat = record
  { refl =  λ {σ} → subst-eq-refl (snd σ)
  ; sym = subst-eq-sym
  ; trans = λ {_} {τpτ} {_} → subst-eq-trans (snd τpτ)
  }
comp ctx-cat {B = Δ , pΔ} (σ , pσ) (τ , pτ) = comps Δ σ τ , subst-comp pΔ pσ pτ
comp-assoc ctx-cat {f = σ , pσ} {τ , pτ} {ξ , pξ} = subst-eq-assoc pσ pτ pξ
comp-cong ctx-cat {B = _ , pΔ} = subst-eq-comp pΔ
id ctx-cat {Γ , pΓ} = ids , subst-id pΓ
id-l ctx-cat {f = σ , pσ} = subst-eq-id-l pσ
id-r ctx-cat {f = σ , pσ} = subst-eq-id-r pσ

ty-set : (Γ : Raw) → eSet
set (ty-set Γ) = Σ (Γ ⊢_)
rel (ty-set Γ) (A , pA) (B , pB) = Γ ⊢ A ~ B
eqr (ty-set Γ) = record { refl = λ {ApA} → ty-eq-refl (snd ApA)
                        ; sym = ty-eq-sym
                        ; trans = λ {_} {BpB} {_} → ty-eq-trans (snd BpB) }

ty-map : ∀ {Δ Γ σ} (pΓ : Γ ⊢) (pσ : σ ∈ Δ ⇒ Γ) → eMap (ty-set Γ) (ty-set Δ)
ty-map {Δ} {Γ} {σ} pΓ pσ = record
  { ap = λ ApA → fst ApA [ σ to _ ] , ty-subst pΓ (snd ApA) pσ
  ; ap-cong = λ AB → ty-eq-subst AB (subst-eq-refl pσ)
  }


ty-resp : ∀ {Δ Γ σ τ} {pσ : σ ∈ Δ ⇒ Γ} {pτ : τ ∈ Δ ⇒ Γ} (pΓ : Γ ⊢) (p : σ ~ τ ∈ Δ ⇒ Γ) →
          eMapRel (ty-map pΓ pσ) (ty-map pΓ pτ)
ty-resp {Δ} {Γ} {σ} {τ} {pσ} {pτ} pΓ p = map-rel λ x → ty-eq-subst x p


ty-psh : ePSh ctx-cat
ty-psh = record
  { fun =  λ { (Γ , pΓ) → ty-set Γ }
  ; mor =  λ { {Δ , pΔ} {Γ , pΓ} (σ , pσ) → ty-map pΔ pσ }
  ; resp =  λ { {a = _ , pΓ} → ty-resp pΓ }
  ; id-mor = map-rel λ { {b = B , pB} AB → ty-eq-trans pB AB (ty-eq-id pB) }
  ; comp-mor = λ { {a = _ , pΓ} {b = _ , pΔ} {f = σ , pσ} {g = τ , pτ} → map-rel
                   λ { {A , pA} {B , pB} AB →
                       ty-eq-trans (ty-subst pΓ pA (subst-comp pΔ pτ pσ))
                         (ty-eq-assoc pA pτ pσ)
                         (ty-eq-subst AB (subst-eq-refl (subst-comp pΔ pτ pσ)))
                     }
                 }
  }




ter-set : (Γ A : Raw) → eSet
ter-set Γ A = record
  { set = Σ (Γ ⊢_∈ A)
  ; rel = λ { (u , pu) (v , pv) → Γ ⊢ u ~ v ∈ A }
  ; eqr = record { refl = λ {tpt} → ter-eq-refl (snd tpt)
                 ; sym = ter-eq-sym
                 ; trans = λ { { b = b} → ter-eq-trans (snd b) }
                 }
  }


ter-map : ∀ {Γ Δ σ A B} (pΓ : Γ ⊢) (pA : Γ ⊢ A) (pB : Δ ⊢ B)
          (pσ : σ ∈ Δ ⇒ Γ) (q : Δ ⊢ B ~ A [ σ to Γ ]) →
          eMap (ter-set Γ A) (ter-set Δ B)
ter-map {Γ} {Δ} {σ} {A} {B} pΓ pA pB pσ q = record
  { ap = λ { (t , pt) →
      t [ σ to _ at _ ] , ter-ty-eq (ty-subst pΓ pA pσ) pB (ter-subst pΓ pA pt pσ) (ty-eq-sym q) }
  ; ap-cong = λ { {_ , pt} {_ , ps} ts →
      ter-eq-ty-eq (ty-subst pΓ pA pσ)
        (ter-subst-conv pΓ pt pσ pA (ty-eq-refl (ty-subst pΓ pA pσ)))
        (ter-subst-conv pΓ ps pσ pA (ty-eq-refl (ty-subst pΓ pA pσ)))
        (ter-eq-subst ts (subst-eq-refl pσ) (ty-eq-refl pA) ps) (ty-eq-sym q) }
  }

ter-psh : ePSh (∫ {C = ctx-cat} ty-psh)
ter-psh = record
  { fun = λ { ((Γ , pΓ) , (A , pA)) → ter-set Γ A }
  ; mor = λ { {a = (Γ , pΓ) , (A , pA)} {b = _ , (B , pB)} ((σ , pσ) , p) →
              ter-map pΓ pA pB pσ p }
  ; resp =
    λ { {(Γ , pΓ) , A , pA} {(Δ , pΔ) , B , pB} {(σ , pσ) , p} {(τ , pτ) , q} στ →
        map-rel λ { {t , pt} {s , ps} ts →
                    ter-eq-ty-eq (ty-subst pΓ pA pσ)
                      (ter-subst-conv pΓ pt pσ pA (ty-eq-refl (ty-subst pΓ pA pσ)))
                      (ter-subst-conv pΓ ps pτ pA (ty-eq-trans pB (ty-eq-sym q) p))
                      (ter-eq-subst ts στ (ty-eq-refl pA) ps) (ty-eq-sym p) }
      }
  ; id-mor = map-rel λ { {t , pt} {s , ps} ts → ter-eq-trans ps ts (ter-eq-id ps) }
  ; comp-mor = λ
    { {(Γ , pΓ) , A , pA} {(Δ , pΔ) , B , pB} {(Ξ , pΞ) , C , pC}
      {(σ , pσ) , p} {(τ , pτ) , q} →
        map-rel λ
        { {t , pt} {s , ps} ts →
          ter-eq-ty-eq (ty-subst pΔ pB pσ)
            (ter-subst-conv pΔ (ter-subst-conv pΓ pt pτ pA (ty-eq-sym q)) pσ pB
               (ty-eq-refl (ty-subst pΔ pB pσ))) (ter-subst-conv pΓ ps (subst-comp pΔ pτ pσ) pA
                 (ty-eq-sym (ty-eq-trans (ty-subst pΔ (ty-subst pΓ pA pτ) pσ)
                   (ty-eq-subst q (subst-eq-refl pσ)) (ty-eq-assoc pA pτ pσ))))
            (ter-eq-trans
              (ter-subst-conv pΔ (ter-subst-conv pΓ ps pτ pA (ty-eq-sym q)) pσ pB
                                        (ty-eq-refl (ty-subst pΔ pB pσ)))
              (ter-eq-subst' (ter-eq-ty-eq (ty-subst pΓ pA pτ)
                (ter-subst-conv pΓ pt pτ pA (ty-eq-refl (ty-subst pΓ pA pτ)))
                (ter-subst-conv pΓ ps pτ pA (ty-eq-refl (ty-subst pΓ pA pτ)))
                (ter-eq-subst' ts pτ pA ps) (ty-eq-sym q)) pσ pB
                  (ter-subst-conv pΓ ps pτ pA (ty-eq-sym q)))
              (ter-eq-trans
                (ter-subst-conv pΔ
                  (ter-subst-conv pΓ ps pτ pA (ty-eq-refl (ty-subst pΓ pA pτ))) pσ
                     (ty-subst pΓ pA pτ) (ty-eq-subst (ty-eq-sym q) (subst-eq-refl pσ)))
                     (ter-eq-subst (ter-eq-refl (ter-subst-conv pΓ ps pτ pA (ty-eq-sym q)))
                       (subst-eq-refl pσ) q (ter-subst-conv pΓ ps pτ pA (ty-eq-sym q)))
                     (ter-eq-ty-eq (ty-subst pΔ (ty-subst pΓ pA pτ) pσ)
                       (ter-subst-conv pΔ
                         (ter-subst-conv pΓ ps pτ pA (ty-eq-refl (ty-subst pΓ pA pτ))) pσ
                         (ty-subst pΓ pA pτ)
                         (ty-eq-refl (ty-subst pΔ (ty-subst pΓ pA pτ) pσ)))
                       (ter-subst-conv pΓ ps (subst-comp pΔ pτ pσ) pA
                         (ty-eq-sym (ty-eq-assoc pA pτ pσ))) (ter-eq-assoc ps pτ pσ)
                  (ty-eq-subst (ty-eq-sym q) (subst-eq-refl pσ)))))
              (ty-eq-sym p)
        }
    }
  }

open eCwFNotation {Ctx = ctx-cat} ty-psh ter-psh
  renaming (ids to idSubst ; _[_] to _[_]S)

-- context extension
_◂_ : (Γ : obj ctx-cat) → Typ Γ → obj ctx-cat
(Γ , pΓ) ◂ (A , pA) = Γ ∙ A , ctx-cons pΓ pA


εS : obj ctx-cat
εS = ε , ctx-nil

!S : ∀ {Γ} → Subst Γ εS
!S {Γ , pΓ} = ! , subst-! pΓ

-- TODO: Why do we have to put all the implicits? :-(
!S-unique : ∀ {Γ : obj ctx-cat } {σ : Subst Γ εS} → _~s_ {εS} {Γ} σ (!S {Γ})
!S-unique {Γ , pΓ} {σ , pσ}= subst-eq-!-η pσ


ppS : ∀ {Γ A} → Subst (Γ ◂ A) Γ
ppS {A = A , pA} = pp , subst-pp pA

qqS : ∀ {Γ A} → Ter (Γ ◂ A) (_[_]S {Γ} {Γ ◂ A} A (ppS {Γ} {A})) -- (A [ ppS {Γ} {A} ]S)
qqS {Γ , pΓ} {A , pA} = qq , ter-qq {Γ} {A} pΓ pA

-- TODO: refactor equational reasoning?
compr : ∀ {Γ A} → isTerminal (cprInp Γ A) (Γ ◂ A , ppS {Γ} {A}, qqS {Γ} {A})
compr {Γ , pΓ} {A , pA} = record {
  !-explicit = λ { ((Δ , pΔ) , (σ , pσ) , (t , pt)) →
    (< σ , t > , (subst-<> pσ pA pt)) ,
    subst-eq-sym (subst-eq-pp<> pσ pA pt) ,
    let bla = ty-eq-trans
                (ty-subst pΓ pA (subst-comp (ctx-cons pΓ pA) (subst-pp pA) (subst-<> pσ pA pt)))
                (ty-eq-assoc pA (subst-pp pA) (subst-<> pσ pA pt))
                (ty-eq-subst (ty-eq-refl pA) (subst-eq-pp<> pσ pA pt))
        pAσ = ty-subst pΓ pA pσ
        pAσid = ty-subst pΔ pAσ (subst-id pΔ)
        p0 = ter-ty-eq (ty-subst (ctx-cons pΓ pA) (ty-subst pΓ pA (subst-pp pA))
              (subst-<> pσ pA pt))
              pAσ (ter-subst (ctx-cons pΓ pA) (ty-subst pΓ pA (subst-pp pA))
                (ter-qq-conv pA (ty-eq-refl (ty-subst pΓ pA (subst-pp pA))))
                (subst-<> pσ pA pt)) bla
        p1 = ter-subst pΔ pAσ p0 (subst-id pΔ)
    in
    ter-eq-trans
      (ter-subst-conv pΔ pt (subst-id pΔ) pAσ
        (ty-eq-sym (ty-eq-id pAσ)))
      (ter-eq-id pt)
      (ter-eq-trans (ter-ty-eq (ty-subst pΔ pAσ (subst-id pΔ)) pAσ
        (ter-subst pΔ pAσ
          (ter-subst-conv (ctx-cons pΓ pA) (ter-qq pΓ pA) (subst-<> pσ pA pt)
          (ty-subst pΓ pA (subst-pp pA)) bla)
          (subst-id pΔ))
        (ty-eq-sym (ty-eq-id pAσ)))
        (ter-eq-ty-eq pAσid (ter-subst pΔ pAσ pt (subst-id pΔ))
          p1
          (ter-eq-subst' (ter-eq-sym (ter-eq-qq<> pσ pA pt)) (subst-id pΔ) pAσ
            p0)
          (ty-eq-sym (ty-eq-id pAσ)))
          (ter-eq-ty-eq pAσid p1 (ter-subst-conv pΔ
              (ter-subst (ctx-cons pΓ pA) (ty-subst pΓ pA (subst-pp pA))
                (ter-qq-conv pA (ty-eq-refl (ty-subst pΓ pA (subst-pp pA))))
                (subst-<> pσ pA pt))
              (subst-id pΔ)
              (ty-subst (ctx-cons pΓ pA) (ty-subst pΓ pA (subst-pp pA)) (subst-<> pσ pA pt))
              (ty-eq-subst bla (subst-eq-refl (subst-id pΔ))))
            (ter-eq-subst (ter-eq-refl
              (ter-subst-conv (ctx-cons pΓ pA) (ter-qq pΓ pA) (subst-<> pσ pA pt)
                (ty-subst pΓ pA (subst-pp pA))
                bla))
              (subst-eq-refl (subst-id pΔ)) (ty-eq-sym bla) p0)
            (ty-eq-sym (ty-eq-id pAσ))))
    }
  ;
  !-η = λ { {(Δ , pΔ) , (σ , pσ) , t , pt} {(τ , pτ) , eq , q} →
    let pΓA = ctx-cons pΓ pA
        ppτ = subst-comp pΓA (subst-pp pA) pτ
        pApτ = ty-subst pΓA (ty-subst pΓ pA (subst-pp pA)) pτ
        pqτ = (ter-subst-conv pΓA (ter-qq-conv pA (ty-eq-refl (ty-subst pΓ pA (subst-pp pA))))
                pτ (ty-subst pΓ pA (subst-pp pA)) (ty-eq-assoc pA (subst-pp pA) pτ))
        pqτid = ter-subst-conv pΔ
                 (ter-ty-eq (ty-subst pΓ pA ppτ) pApτ pqτ
                   (ty-eq-sym (ty-eq-assoc pA (subst-pp pA) pτ)))
                 (subst-id pΔ) pApτ
                 (ty-eq-trans pApτ (ty-eq-sym (ty-eq-id pApτ))
                   (ty-eq-assoc pA (subst-pp pA) pτ))
    in -- TODO: unreadable..
    subst-eq-trans
      (subst-<> ppτ pA
        (ter-subst-conv pΓA (ter-qq pΓ pA) pτ (ty-subst pΓ pA (subst-pp pA))
          (ty-eq-assoc pA (subst-pp pA) pτ)))
      (subst-eq-<>-η pτ)
      (subst-eq-<> pΓ pA ppτ pσ
        pqτ (ter-ty-eq (ty-subst pΓ pA pσ)
          (ty-subst pΓ pA (subst-comp (ctx-cons pΓ pA) (subst-pp pA) pτ))
          pt (ty-eq-subst (ty-eq-refl pA) eq))
        (subst-eq-sym eq)
        (ter-eq-sym
          (ter-eq-trans pqτid (ter-eq-ty-eq (ty-subst pΓ pA pσ) pt
              (ter-ty-eq (ty-subst pΓ pA (subst-comp (ctx-cons pΓ pA) (subst-pp pA) pτ))
                (ty-subst pΓ pA pσ) pqτid (ty-eq-subst (ty-eq-refl pA) (subst-eq-sym eq)))
              q (ty-eq-subst (ty-eq-refl pA) eq))
            (ter-eq-ty-eq pApτ (ter-ty-eq (ty-subst pΓ pA
                  (subst-comp (ctx-cons pΓ pA) (subst-pp pA) pτ))
                (ty-subst (ctx-cons pΓ pA) (ty-subst pΓ pA (subst-pp pA)) pτ) pqτid
                (ty-eq-sym (ty-eq-assoc pA (subst-pp pA) pτ)))
              (ter-subst (ctx-cons pΓ pA) (ty-subst pΓ pA (subst-pp pA))
                (ter-qq-conv pA (ty-eq-refl (ty-subst pΓ pA (subst-pp pA)))) pτ)
              (ter-eq-sym (ter-eq-id (ter-subst-conv pΓA (ter-qq pΓ pA) pτ
                (ty-subst pΓ pA (subst-pp pA)) (ty-eq-refl pApτ))))
              (ty-eq-assoc pA (subst-pp pA) pτ)))))
  } }

SynCwf : eCwF
SynCwf = record
           { Ctx = ctx-cat
           ; Ty = ty-psh
           ; Tm = ter-psh
           ; <> = εS
           ; ! = λ {Γ} → !S {Γ} -- yellow?!?!?!
           ; !-unique = λ {Γ σ} → !S-unique {Γ} {σ}
           ; _∙_ = _◂_
           ; pp = λ {Γ A} → ppS {Γ} {A}
           ; qq = λ {Γ A} → qqS {Γ} {A}
           ; compr = compr
           }

-- -}
-- -}
