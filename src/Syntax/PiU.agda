{-# OPTIONS --without-K #-}

module Syntax.PiU where

open import Basics
open import Data.Nat
open import Data.Fin
open import Relation.Binary.PropositionalEquality hiding ([_])

l = lzero

-- Raw expressions

data Exp : (n : ℕ) → Set l where
  var : {n : ℕ} (i : Fin n) → Exp n
  pi  : {n : ℕ} (a : Exp n) (b : Exp (suc n)) → Exp n
  app : {n : ℕ} (r s : Exp n) → Exp n
  lam : {n : ℕ} (t : Exp (suc n)) → Exp n
  uni : {n : ℕ} → Exp n
  el  : {n : ℕ} → Exp n → Exp n

data Ren : (n m : ℕ) → Set l where
   idR : {n : ℕ} → Ren n n
   wkR : {n m : ℕ} → Ren n m → Ren (suc n) m
   upR : {n m : ℕ} → Ren n m → Ren (suc n) (suc m)

pR : {n : ℕ} → Ren (suc n) n
pR = wkR idR

lookR : {m n : ℕ} → Fin n → Ren m n → Fin m
lookR i       idR     = i
lookR i       (wkR ρ) = suc (lookR i ρ)
lookR zero    (upR ρ) = zero
lookR (suc i) (upR ρ) = suc (lookR i ρ)

infixl 60 _[_]R

_[_]R : {m n : ℕ} → Exp n → Ren m n → Exp m
var i   [ ρ ]R = var (lookR i ρ)
pi a b  [ ρ ]R = pi (a [ ρ ]R) (b [ upR ρ ]R)
app r s [ ρ ]R = app (r [ ρ ]R) (s [ ρ ]R)
lam t   [ ρ ]R = lam (t [ upR ρ ]R)
uni     [ ρ ]R = uni
el t    [ ρ ]R = el (t [ ρ ]R)

_r⋆r_ : {k m n : ℕ} → Ren m n → Ren k m → Ren k n
ρ     r⋆r idR   = ρ
ρ     r⋆r wkR η = wkR (ρ r⋆r η)
idR   r⋆r upR η = upR η
wkR ρ r⋆r upR η = wkR (ρ r⋆r η)
upR ρ r⋆r upR η = upR (ρ r⋆r η)

data Subst : (m n : ℕ) → Set l where
  !     : {m : ℕ} → Subst m zero
  <_,_> : {m n : ℕ} → Subst m n → Exp m → Subst m (suc n)

_⋆r_ : {k m n : ℕ} → Subst m n → Ren k m → Subst k n
!         ⋆r ρ = !
< σ , t > ⋆r ρ = < σ ⋆r ρ , t [ ρ ]R >

upS : {m n : ℕ} → Subst m n → Subst (suc m) (suc n)
upS σ = < σ ⋆r pR , var zero >

-- pS^ : {n : ℕ} (i : Fin n) → Subst n (toℕ i)
-- pS^ zero    = !
-- pS^ (suc i) = upS (pS^ i)

wkS : {m n : ℕ} → Subst m n → Subst (suc m) n
wkS σ = σ ⋆r pR

idS : {n : ℕ} → Subst n n
idS {zero}  = !
idS {suc n} = < wkS idS , var zero >

ren-to-subst : {m n : ℕ} → Ren m n → Subst m n
ren-to-subst idR     = idS
ren-to-subst (wkR ρ) = wkS (ren-to-subst ρ)
ren-to-subst (upR ρ) = upS (ren-to-subst ρ)

lookS : {m n : ℕ} → Fin n → Subst m n → Exp m
lookS () !
lookS zero    < σ , t > = t
lookS (suc i) < σ , t > = lookS i σ

infixl 60 _[_]

_[_] : {m n : ℕ} → Exp n → Subst m n → Exp m
var i   [ σ ] = lookS i σ
pi a b  [ σ ] = pi (a [ σ ]) (b [ upS σ ])
app r s [ σ ] = app (r [ σ ]) (s [ σ ])
lam t   [ σ ] = lam (t [ upS σ ])
uni     [ σ ] = uni
el t    [ σ ] = el (t [ σ ])

_⋆_ : {k m n : ℕ} → Subst m n → Subst k m → Subst k n
!         ⋆ τ = !
< σ , t > ⋆ τ = < σ ⋆ τ , t [ τ ] >



--------------------------------------------------------------------------------
-- Typing

data Ctx : ℕ → Set l where
  ε   : Ctx zero
  _∙_ : {n : ℕ} (Γ : Ctx n) (A : Exp n) → Ctx (suc n)

infix 30 _∙_

qq : {n : ℕ} → Exp (suc n)
qq = var zero

pp : {n : ℕ} → Subst (suc n) n
pp = ren-to-subst pR


data _⊢_ : {n : ℕ} (Γ : Ctx n) (A : Exp n) → Set l
data _⊢_~_ : {n : ℕ} (Γ : Ctx n) (A B : Exp n) → Set l
data _⊢_∈_ : {n : ℕ} (Γ : Ctx n) (u A : Exp n) → Set l
data _⊢_~_∈_ : {n : ℕ} (Γ : Ctx n) (u v A : Exp n) → Set l


data _⊢_ where

  ty-univ :
    ∀ {n} {Γ : Ctx n} →
    --------------------
    Γ ⊢ uni

  ty-el :
    ∀ {n} {Γ : Ctx n} {a} →
    Γ ⊢ a ∈ uni →
    -------------
    Γ ⊢ el a

  ty-pi :
    ∀ {n} {Γ : Ctx n} {A B} →
    Γ ⊢ A → Γ ∙ A ⊢ B →
    --------------------
    Γ ⊢ pi A B

data _⊢_~_ where

  ty-eq-univ :
    ∀ {n} {Γ : Ctx n} →
    --------------------
    Γ ⊢ uni ~ uni

  ty-eq-el :
    ∀ {n} {Γ : Ctx n} {a b} →
    Γ ⊢ a ~ b ∈ uni →
    ------------------
    Γ ⊢ el a ~ el b

  ty-eq-pi :
    ∀ {n} {Γ : Ctx n} {A B C D} →
    Γ ⊢ A ~ C → Γ ∙ A ⊢ B ~ D →
    ----------------------------
    Γ ⊢ pi A B ~ pi C D


  ty-eq-sym :
    ∀ {n} {Γ : Ctx n} {A B} →
    Γ ⊢ A ~ B →
    ------------
    Γ ⊢ B ~ A
  ty-eq-trans :
    ∀ {n} {Γ : Ctx n} {A B C} →
    Γ ⊢ A ~ B → Γ ⊢ B ~ C →
    ------------------------
    Γ ⊢ A ~ C


data _⊢_∈_ where

  ter-ty-eq :
    ∀ {n} {Γ : Ctx n} {A B t} →
    Γ ⊢ t ∈ A → Γ ⊢ A ~ B →
    ------------------------
    Γ ⊢ t ∈ B

  ter-var-zero :
    ∀ {n} {Γ : Ctx n} {A} →
    Γ ⊢ A →
    -----------------------------
    Γ ∙ A ⊢ var zero ∈ A [ pR ]R

  ter-var-suc :
    ∀ {n} {Γ : Ctx n} {A B i} →
    Γ ⊢ var i ∈ A →
    ---------------------------------
    Γ ∙ B ⊢ var (suc i)  ∈ A [ pR ]R


  ter-lam :
    ∀ {n} {Γ : Ctx n} {A B t} →
    Γ ∙ A ⊢ t ∈ B →
    ----------------
    Γ ⊢ lam t ∈ pi A B

  ter-app :
    ∀ {n} {Γ : Ctx n} {A B r s} →
    Γ ⊢ r ∈ pi A B → Γ ⊢ s ∈ A →
    ------------------------------
    Γ ⊢ app r s ∈ B [ < idS , s > ]


data _⊢_~_∈_ where

  ter-eq-ty-eq :
    ∀ {n} {Γ : Ctx n} {A B t s} →
    Γ ⊢ t ~ s ∈ A → Γ ⊢ A ~ B →
    ----------------------------
    Γ ⊢ t ~ s ∈ B

  ter-eq-beta :
    ∀ {n} {Γ : Ctx n} {A B t s} →
    Γ ∙ A ⊢ t ∈ B → Γ ⊢ s ∈ A →
    ----------------------------------------------------------
    Γ ⊢ app (lam t) s ~ t [ < idS , s > ] ∈ B [ < idS , s > ]

  ter-eq-eta :
    ∀ {n} {Γ : Ctx n} {A B t} →
    Γ ⊢ t ∈ pi A B →
    ------------------
    Γ ⊢ t ~ lam (app (t [ pR ]R) qq) ∈ pi A B


  ter-eq-var-zero :
    ∀ {n} {Γ : Ctx n} {A} →
    Γ ⊢ A →
    ----------------------------------------
    Γ ∙ A ⊢ var zero ~ var zero ∈ A [ pR ]R

  ter-eq-var-suc :
    ∀ {n} {Γ : Ctx n} {A B i j} →
    Γ ⊢ var i ~ var j ∈ A →
    ----------------------------------------------
    Γ ∙ B ⊢ var (suc i) ~ var (suc j) ∈ A [ pR ]R

  ter-eq-lam :
    ∀ {n} {Γ : Ctx n} {A B  u v} →
    Γ ∙ A ⊢ u ~ v ∈ B →
    ---------------------------
    Γ ⊢ lam u ~ lam v ∈ pi A B

  ter-eq-app :
    ∀ {n} {Γ : Ctx n} {A B r s u v} →
    Γ ⊢ r ~ u ∈ pi A B → Γ ⊢ s ~ v ∈ A →
    --------------------------------------
    Γ ⊢ app r s ~ app u v ∈ B [ < idS , s > ]


  ter-eq-sym :
    ∀ {n} {Γ : Ctx n} {A u v} →
    Γ ⊢ u ~ v ∈ A →
    ----------------
    Γ ⊢ v ~ u ∈ A

  ter-eq-trans :
    ∀ {n} {Γ : Ctx n} {A u v w} →
    Γ ⊢ u ~ v ∈ A → Γ ⊢ v ~ w ∈ A →
    ---------------------------------
    Γ ⊢ u ~ w ∈ A


--------------------------------------------------------------------------------
-- Some admissible rules

ty-eq-refl :
  ∀ {n} {Γ : Ctx n} {A} →
  Γ ⊢ A →
  ----------
  Γ ⊢ A ~ A

ter-eq-refl :
  ∀ {n} {Γ : Ctx n} {A u} →
  Γ ⊢ u ∈ A →
  ------------
  Γ ⊢ u ~ u ∈ A

ty-eq-refl ty-univ       = ty-eq-univ
ty-eq-refl (ty-el pa)    = ty-eq-el (ter-eq-refl pa)
ty-eq-refl (ty-pi pA pB) = ty-eq-pi (ty-eq-refl pA) (ty-eq-refl pB)

ter-eq-refl (ter-ty-eq pu pAB) = ter-eq-ty-eq (ter-eq-refl pu) pAB
ter-eq-refl (ter-var-zero pA)  = ter-eq-var-zero pA
ter-eq-refl (ter-var-suc pu)   = ter-eq-var-suc (ter-eq-refl pu)
ter-eq-refl (ter-lam pu)       = ter-eq-lam (ter-eq-refl pu)
ter-eq-refl (ter-app pu pv)    = ter-eq-app (ter-eq-refl pu) (ter-eq-refl pv)

--------------------------------------------------------------------------------
-- Derived jugdments: contexts and substitutions

data _⊢ : {n : ℕ} (Γ : Ctx n) → Set l where

  ctx-nil :
    -----
    ε ⊢

  ctx-cons :
    ∀ {n} {Γ : Ctx n} {A} →
    Γ ⊢ →
    Γ ⊢ A →
    ----------
    Γ ∙ A ⊢


data _∈_⇒_ : {m n : ℕ} (σ : Subst m n) (Δ : Ctx m) (Γ : Ctx n) → Set l where

  subst-! :
    ∀ {n} {Γ : Ctx n} →
    --------------------
    ! ∈ Γ ⇒ ε

  subst-<> :
    ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} {A σ t} →
    σ ∈ Δ ⇒ Γ → Γ ⊢ A → Δ ⊢ t ∈ A [ σ ] →
    ----------------------------------------
    < σ , t > ∈ Δ ⇒ Γ ∙ A


data _~_∈_⇒_ : {m n : ℕ} (σ τ : Subst m n) (Δ : Ctx m) (Γ : Ctx n) → Set l where

  subst-eq-! :
    ∀ {n} {Γ : Ctx n} →
    --------------------
    ! ~ ! ∈ Γ ⇒ ε

  subst-eq-<> :
    ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} {A σ τ u v} →
    σ ~ τ ∈ Δ ⇒ Γ → Γ ⊢ A → Δ ⊢ u ~ v ∈ A [ σ ] →
    ------------------------------------------------
    < σ , u > ~ < τ , v > ∈ Δ ⇒ Γ ∙ A


--------------------------------------------------------------------------------
-- Derived judgment: renamings

data _∈_≤_ : {m n : ℕ} (ρ : Ren m n) (Δ : Ctx m) (Γ : Ctx n) → Set l where

  ren-id :
    ∀ {n} {Γ : Ctx n} →
    Γ ⊢ →
    ------------
    idR ∈ Γ ≤ Γ

  ren-wk :
    ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} {A ρ} →
    ρ ∈ Δ ≤ Γ →
    ------------------
    wkR ρ ∈ Δ ∙ A ≤ Γ

  ren-upr :
    ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} {A ρ} →
    ρ ∈ Δ ≤ Γ → Γ ⊢ A →
    ------------------------------
    upR ρ ∈ Δ ∙ A [ ρ ]R ≤ Γ ∙ A


-- subst-pp : ∀ {n} {Γ : Ctx n} {A} → Γ ⊢ → pp ∈ Γ ∙ A ⇒ Γ
-- subst-pp ctx-nil = subst-!
-- subst-pp (ctx-cons pΓ x) = subst-<> {!!} {!!} {!!}


