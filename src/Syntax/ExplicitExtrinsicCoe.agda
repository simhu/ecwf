{-# OPTIONS --without-K #-}
open import Basics
open import Presheaves
open import Cwf.Elem
open import Products using (isTerminal)

-- Type theory presented with an extrinsic explicit syntax
-- module Syntax.ExplicitExtrinsic {l : Level} where

-- For now fix the level to don't have the annoying constructor name
-- issue when using C-c C-c.
module Syntax.ExplicitExtrinsicCoe where

l = lzero

data Raw : Set l where
  -- raw contexts
  ε : Raw
  _∙_ : Raw → Raw → Raw
  -- raw term
  qq : Raw                      -- variables
  _[_to_] : Raw → Raw → Raw → Raw         -- substitution in terms
  coe : Raw → Raw → Raw → Raw             -- coercions
  -- raw substitutions
  comps : Raw → Raw → Raw → Raw
  ids : Raw
  ! : Raw
  pp : Raw
  <_,_> : Raw → Raw → Raw

infixl 30 _∙_
infixl 60 _[_to_]

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
  ter-qq :
    ∀ {Γ A} →
    Γ ⊢ A →
    ----------------------
    Γ ∙ A ⊢ qq ∈ A [ pp to Γ ]

  ter-subst :
    ∀ {σ Δ Γ A t} →
    Γ ⊢ t ∈ A → σ ∈ Δ ⇒ Γ →
    -------------------------
    Δ ⊢ t [ σ to Γ ] ∈ A [ σ to Γ ]

  ter-coe :
    ∀ {Γ A B t} →
    Γ ⊢ A → -- ??
    Γ ⊢ t ∈ A → Γ ⊢ A ~ B →
    ------------------------
    Γ ⊢ coe A B t ∈ B

data _⊢_~_∈_ where
  ter-eq-qq<> :
    ∀ {Δ Γ σ t A } →
    σ ∈ Δ ⇒ Γ → Γ ⊢ A → Δ ⊢ t ∈ A [ σ to Γ ] →
    ---------------------------------------
    Δ ⊢ qq [ < σ , t > to Γ ∙ A ] ~ t ∈ A [ σ to Γ ] -- use lhs for type?

  ter-eq-subst :
    ∀ {σ σ' Δ Γ A t t'} →
    Γ ⊢ t ~ t' ∈ A → σ ~ σ' ∈ Δ ⇒ Γ →
    -----------------------------------
    Δ ⊢ t [ σ to Γ ] ~ t' [ σ' to Γ ] ∈ A [ σ to Γ ]

  ter-eq-id :
    ∀ {Γ A t} →
    Γ ⊢ t ∈ A →
    ----------------------
    Γ ⊢ t ~ t [ ids to Γ ] ∈ A

  ter-eq-assoc :
    ∀ {Ξ Δ Γ σ τ A t} →
    Γ ⊢ t ∈ A →
    σ ∈ Δ ⇒ Γ → τ ∈ Ξ ⇒ Δ →
    -----------------------------------------------------
    Ξ ⊢ t [ σ to Γ ] [ τ to Δ ] ~ t [ comps Δ σ τ to Γ ] ∈ A [ σ to Γ ] [ τ to Δ ]

  ter-eq-coe :
    ∀ {Γ A B t s} →
    Γ ⊢ t ~ s ∈ A → Γ ⊢ A ~ B →
    ------------------------
    Γ ⊢ coe A B t ~ coe A B s ∈ B

  -- ter-eq-coe-trans :
  --   ∀ {Γ A B C t} →



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
    σ ~ < comps (Γ ∙ A) pp σ , qq [ σ to Γ ∙ A ] > ∈ Δ ⇒ Γ ∙ A

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

  subst-eq-<> :
    ∀ {Δ Γ σ σ' A t t'} →
    Γ ⊢ A → σ ~ σ' ∈ Δ ⇒ Γ → Δ ⊢ t ~ t' ∈ A [ σ to Γ ] →
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
    τ ∈ Δ ⇒ Γ → -- ???
    σ ~ τ ∈ Δ ⇒ Γ → τ ~ ξ ∈ Δ ⇒ Γ →
    ---------------------------------
    σ ~ ξ ∈ Δ ⇒ Γ

------------------------------------------------------------------------------

ter-eq-subst' :
    ∀ {σ Δ Γ A t t'} →
    Γ ⊢ t ~ t' ∈ A → σ ∈ Δ ⇒ Γ →
    -----------------------------------
    Δ ⊢ t [ σ to Γ ] ~ t' [ σ to Γ ] ∈ A [ σ to Γ ]
ter-eq-subst' tt' pσ = ter-eq-subst tt' (subst-eq-refl pσ)

ty-eq-subst' :
  ∀ {σ Δ Γ A A'} →
  Γ ⊢ A ~ A' → σ ∈ Δ ⇒ Γ →
  -------------------------------
  Δ ⊢ A [ σ to Γ ] ~ A' [ σ to Γ ]
ty-eq-subst' aa' pσ = ty-eq-subst aa' (subst-eq-refl pσ)

-- -- Some admissible rules.

-- -- Inversion (fragile concerning possible extensions)

-- ty-ctx : ∀ {Γ A} → Γ ⊢ A → Γ ⊢
-- subst-dom : ∀ {Δ Γ σ} → σ ∈ Δ ⇒ Γ → Δ ⊢
-- subst-cod : ∀ {Δ Γ σ} → σ ∈ Δ ⇒ Γ → Γ ⊢

-- ty-ctx {Γ} {.(_ [ _ ])} (ty-subst  pA pσ) = subst-dom pσ

-- subst-dom (subst-pp pA) = ctx-cons (ty-ctx pA) pA
-- subst-dom (subst-! pΔ) = pΔ
-- subst-dom (subst-<> pσ _ _) = subst-dom pσ
-- subst-dom (subst-id pΔ) = pΔ
-- subst-dom (subst-comp pΔ pσ pτ) = subst-dom pτ

-- subst-cod (subst-pp pA) = ty-ctx pA
-- subst-cod (subst-! pΔ) = ctx-nil
-- subst-cod (subst-<> pσ pA x₁) = ctx-cons (ty-ctx pA) pA
-- subst-cod (subst-id pΔ) = pΔ
-- subst-cod (subst-comp pΔ pσ pτ) = subst-cod pσ

-- -- These also need the corresponding inversions for judgmental
-- -- equality on terms, which might be problematic once we add Pi-types.
-- -- Alternatively, we could try adding term derivations in the
-- -- subst-eq-<> rule.

-- -- subst-eq-lhs : ∀ {Δ Γ σ τ} → σ ~ τ ∈ Δ ⇒ Γ → σ ∈ Δ ⇒ Γ
-- -- subst-eq-rhs : ∀ {Δ Γ σ τ} → σ ~ τ ∈ Δ ⇒ Γ → τ ∈ Δ ⇒ Γ
-- -- subst-eq-lhs (subst-eq-!-η pσ) = pσ
-- -- subst-eq-lhs (subst-eq-<>-η pσ) = pσ
-- -- subst-eq-lhs (subst-eq-pp<> pσ pA pt) =
-- --   subst-comp (ctx-cons (ty-ctx pA) pA) (subst-pp pA) (subst-<> pσ pA pt)
-- -- subst-eq-lhs (subst-eq-assoc pσ pτ pξ) =
-- --   subst-comp (subst-dom pσ) pσ (subst-comp (subst-dom pτ) pτ pξ)
-- -- subst-eq-lhs (subst-eq-id-l pσ) =
-- --   subst-comp (subst-cod pσ) (subst-id (subst-cod pσ)) pσ
-- -- subst-eq-lhs (subst-eq-id-r pσ) =
-- --   subst-comp (subst-dom pσ) pσ (subst-id (subst-dom pσ))
-- -- subst-eq-lhs (subst-eq-comp pΔ pστ pστ') =
-- --   subst-comp pΔ (subst-eq-lhs pστ) (subst-eq-lhs pστ')
-- -- subst-eq-lhs (subst-eq-<> pA pστ x₁) = {!!}
-- -- subst-eq-lhs (subst-eq-refl x) = {!!}
-- -- subst-eq-lhs (subst-eq-sym pστ) = {!!}
-- -- subst-eq-lhs (subst-eq-trans pστ pστ₁) = {!!}

-- -- subst-eq-rhs pστ = {!!}

------------------------------------------------------------------------------
{-
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
                 ; trans = ter-eq-trans
                 }
  }


ter-map : ∀ {Γ Δ σ A B} (pΓ : Γ ⊢) (pA : Γ ⊢ A) (pσ : σ ∈ Δ ⇒ Γ) (q : Δ ⊢ B ~ A [ σ to Γ ]) →
          eMap (ter-set Γ A) (ter-set Δ B)
ter-map {Γ} {Δ} {σ} {A} {B} pΓ pA pσ q = record
  { ap = λ { (t , pt) → coe (A [ σ to Γ ]) B (t [ σ to Γ ]) , ter-coe (ty-subst pΓ pA pσ) (ter-subst pt pσ) (ty-eq-sym q) }
  ; ap-cong = λ ts →
      ter-eq-coe (ter-eq-subst ts (subst-eq-refl pσ)) (ty-eq-sym q)
  }

ter-psh : ePSh (∫ {C = ctx-cat} ty-psh)
ter-psh = record
  { fun = λ { ((Γ , pΓ) , (A , pA)) → ter-set Γ A }
  ; mor = λ { {a = (Γ , pΓ) , (A , pA)} ((σ , pσ) , p) → ter-map pΓ pA pσ p }
  ; resp =
    λ { {(Γ , pΓ) , A , pA} {(Δ , pΔ) , B , pB} {(σ , pσ) , p} {(τ , pτ) , q} στ →
        map-rel λ { {t , pt} {s , ps} ts → {!!}
                    -- ter-eq-ty-eq (ter-eq-subst ts στ) (ty-eq-sym p) 
                  }
      }
  ; id-mor = map-rel λ { {t , pt} {s , ps} ts → {!!} }-- ter-eq-trans ts (ter-eq-id ps) }
  ; comp-mor = λ
    { {(Γ , pΓ) , A , pA} {(Δ , pΔ) , B , pB} {(Ξ , pΞ) , C , pC}
      {(σ , pσ) , p} {(τ , pτ) , q} →
        map-rel λ
        { {t , pt} {s , ps} ts → {!!}
          -- ter-eq-ty-eq (ter-eq-trans (ter-eq-subst' (ter-eq-subst' ts pτ) pσ)
          --                (ter-eq-assoc ps pτ pσ))
          -- (ty-eq-trans (ty-subst pΔ pB pσ) (ty-eq-subst' (ty-eq-sym q) pσ) (ty-eq-sym p))
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
qqS {Γ , pΓ} {A , pA} = qq , ter-qq {Γ} {A} pA

-- TODO: refactor equational reasoning?
compr : ∀ {Γ A} → isTerminal (cprInp Γ A) (Γ ◂ A , ppS {Γ} {A}, qqS {Γ} {A})
isTerminal.!-explicit (compr {Γ , pΓ} {A , pA}) ((Δ , pΔ) , (σ , pσ) , (t , pt)) = {!!}
  -- (< σ , t > , (subst-<> pσ pA pt)) ,
  -- subst-eq-sym (subst-eq-pp<> pσ pA pt) ,
  -- ter-eq-trans (ter-eq-id pt) (ter-eq-ty-eq (ter-eq-subst'
  --   (ter-eq-sym (ter-eq-qq<> pσ pA pt)) (subst-id pΔ))
  --     (ty-eq-sym (ty-eq-id (ty-subst pΓ pA pσ))))
isTerminal.!-η (compr {Γ , pΓ} {A , pA}) {(Δ , pΔ) , (σ , pσ) , t , pt}
  {(τ , pτ) , eq , q} = let pΓA = ctx-cons pΓ pA in {!!}
  -- subst-eq-trans
  --   (subst-<> (subst-comp pΓA (subst-pp pA) pτ) pA
  --     (ter-ty-eq (ty-subst pΓA (ty-subst pΓ pA (subst-pp pA)) pτ)
  --     (ter-subst (ter-qq pA) pτ) (ty-eq-assoc pA (subst-pp pA) pτ)))
  --   (subst-eq-<>-η pτ)
  --   (subst-eq-<> pA
  --     (subst-eq-sym eq)
  --     (ter-eq-trans
  --       (ter-eq-id (ter-ty-eq (ty-subst pΓA (ty-subst pΓ pA (subst-pp pA)) pτ)
  --       (ter-subst (ter-qq pA) pτ)
  --         (ty-eq-assoc pA (subst-pp pA) pτ)))
  --       (ter-eq-ty-eq (ter-eq-sym q) (ty-eq-subst (ty-eq-refl pA) eq))))


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
