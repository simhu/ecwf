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

-- TODO: rename into something like 'weakenings' (Wk)
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

r⋆r-id-l : {m n : ℕ} {ρ : Ren m n} → ρ ≡ idR r⋆r ρ
r⋆r-id-l {ρ = idR}   = _≡_.refl
r⋆r-id-l {ρ = wkR ρ} = cong wkR r⋆r-id-l
r⋆r-id-l {ρ = upR ρ} = _≡_.refl

lookR-assoc : {k m n : ℕ} {ρ : Ren m n} {η : Ren k m} {i : Fin n} →
              lookR (lookR i ρ) η ≡ lookR i (ρ r⋆r η)
lookR-assoc {ρ = ρ}     {idR}   {i}     = _≡_.refl
lookR-assoc {ρ = ρ}     {wkR η} {i}     = cong suc (lookR-assoc {ρ = ρ} {η})
lookR-assoc {ρ = idR}   {upR η} {i}     = _≡_.refl
lookR-assoc {ρ = wkR ρ} {upR η} {i}     = cong suc (lookR-assoc {ρ = ρ} {η})
lookR-assoc {ρ = upR ρ} {upR η} {zero}  = _≡_.refl
lookR-assoc {ρ = upR ρ} {upR η} {suc i} = cong suc (lookR-assoc {ρ = ρ} {η})

[]R-assoc : {k m n : ℕ} {ρ : Ren m n} {η : Ren k m} {t : Exp n} →
            t [ ρ ]R [ η ]R ≡ t [ ρ r⋆r η ]R
[]R-assoc {ρ = ρ} {η} {var i}   = cong var (lookR-assoc {ρ = ρ} {η})
[]R-assoc {ρ = ρ} {η} {pi a b}  = cong₂ pi []R-assoc []R-assoc
[]R-assoc {ρ = ρ} {η} {app r s} = cong₂ app []R-assoc []R-assoc
[]R-assoc {ρ = ρ} {η} {lam t}   = cong lam []R-assoc
[]R-assoc {ρ = ρ} {η} {uni}     = _≡_.refl
[]R-assoc {ρ = ρ} {η} {el t}    = cong el []R-assoc

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

[][]R-assoc : {k m n : ℕ} {σ : Subst m n} { ρ : Ren k m} {t : Exp n} →
              t [ σ ] [ ρ ]R ≡ t [ σ ⋆r ρ ]
[][]R-assoc {σ = σ} {ρ} {var i} = {!!}
[][]R-assoc {σ = σ} {ρ} {pi a b} = cong₂ pi [][]R-assoc [][]R-assoc
[][]R-assoc {σ = σ} {ρ} {app r s} = cong₂ app [][]R-assoc [][]R-assoc
[][]R-assoc {σ = σ} {ρ} {lam t} = cong lam {!([][]R-assoc  {σ = upS σ} {ρ = upR ρ} {t = t})!} -- ([][]R-assoc  {σ = upS σ} {ρ = upR ρ} {t = t})
[][]R-assoc {σ = σ} {ρ} {uni} = _≡_.refl
[][]R-assoc {σ = σ} {ρ} {el t} = cong el [][]R-assoc


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
    Γ ⊢ A → -- similar as in Abel, Öhmann, Vezzosi (POPL2018)
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
    Γ ⊢ A →
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
    Γ ⊢ A →
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
-- Reflexivity is admissible

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
ty-eq-refl (ty-pi pA pB) = ty-eq-pi pA (ty-eq-refl pA) (ty-eq-refl pB)

ter-eq-refl (ter-ty-eq pu pAB) = ter-eq-ty-eq (ter-eq-refl pu) pAB
ter-eq-refl (ter-var-zero pA)  = ter-eq-var-zero pA
ter-eq-refl (ter-var-suc pu)   = ter-eq-var-suc (ter-eq-refl pu)
ter-eq-refl (ter-lam pA pu)    = ter-eq-lam pA (ter-eq-refl pu)
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

subst-eq-refl :
  ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} {σ} →
  σ ∈ Δ ⇒ Γ →
  --------------
  σ ~ σ ∈ Δ ⇒ Γ

subst-eq-refl subst-! = subst-eq-!
subst-eq-refl (subst-<> pσ pA pt) = subst-eq-<> (subst-eq-refl pσ) pA (ter-eq-refl pt)

-- TODO: this relies on ter-eq-subst
-- subst-eq-sym :
--   ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} {σ τ} →
--   σ ~ τ ∈ Δ ⇒ Γ →
--   --------------
--   τ ~ σ ∈ Δ ⇒ Γ

-- subst-eq-sym subst-eq-! = subst-eq-!
-- subst-eq-sym (subst-eq-<> pστ pA pst) = subst-eq-<> (subst-eq-sym pστ) pA (ter-eq-sym {!pst!})

-- ter-eq-subst :
--   ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} {σ σ' A t t'} →
--   Γ ⊢ t ~ t' ∈ A → σ ~ σ' ∈ Δ ⇒ Γ →
--   ------------------------------------
--   Δ ⊢ t [ σ ] ~ t' [ σ' ] ∈ A [ σ ]

-- ter-subst :
--   ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} {σ A t} →
--   Γ ⊢ t ∈ A → σ ∈ Δ ⇒ Γ →
--   -------------------------
--   Δ ⊢ t [ σ ] ∈ A [ σ ]



-- subst-pp : ∀ {n} {Γ : Ctx n} {A} → Γ ⊢ → pp ∈ Γ ∙ A ⇒ Γ
-- subst-pp ctx-nil = subst-!
-- subst-pp (ctx-cons pΓ x) = subst-<> {!!} {!!} {!!}


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

-- {-

ty-ren :
  ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} {ρ A} →
  Γ ⊢ A → ρ ∈ Δ ≤ Γ →
  ---------------------
  Δ ⊢ A [ ρ ]R

ty-eq-ren :
  ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} {ρ A B} →
  Γ ⊢ A ~ B → ρ ∈ Δ ≤ Γ →
  -------------------------
  Δ ⊢ A [ ρ ]R ~ B [ ρ ]R

ter-ren :
  ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} {ρ A t} →
  Γ ⊢ t ∈ A → ρ ∈ Δ ≤ Γ →
  -------------------------
  Δ ⊢ t [ ρ ]R ∈ A [ ρ ]R

ter-eq-ren :
  ∀ {m n} {Δ : Ctx m} {Γ : Ctx n} {ρ A t s} →
  Γ ⊢ t ~ s ∈ A → ρ ∈ Δ ≤ Γ →
  -----------------------------------
  Δ ⊢ t [ ρ ]R ~ s [ ρ ]R ∈ A [ ρ ]R

ty-ren ty-univ pρ       = ty-univ
ty-ren (ty-el pa) pρ    = ty-el (ter-ren pa pρ)
ty-ren (ty-pi pA pB) pρ = ty-pi (ty-ren pA pρ) (ty-ren pB (ren-upr pρ pA))

ty-eq-ren ty-eq-univ pρ            = ty-eq-univ
ty-eq-ren (ty-eq-el pab) pρ        = ty-eq-el (ter-eq-ren pab pρ)
ty-eq-ren (ty-eq-pi pA pAC pBD) pρ =
  ty-eq-pi (ty-ren pA pρ) (ty-eq-ren pAC pρ) (ty-eq-ren pBD (ren-upr pρ pA))
ty-eq-ren (ty-eq-sym pAB) pρ       = ty-eq-sym (ty-eq-ren pAB pρ)
ty-eq-ren (ty-eq-trans pAB pBC) pρ =
  ty-eq-trans (ty-eq-ren pAB pρ) (ty-eq-ren pBC pρ)

ter-ren (ter-ty-eq pt pAB) pρ = ter-ty-eq (ter-ren pt pρ) (ty-eq-ren pAB pρ)
ter-ren (ter-var-zero {A = A} pA) (ren-id pΓ)
  rewrite []R-assoc {ρ = pR} {η = idR}{t = A} = ter-var-zero pA
ter-ren (ter-var-zero {A = A} pA) (ren-wk {ρ = ρ} pρ) = {!!}
--  rewrite []R-assoc {ρ = pR} {η = wkR ρ} {t = A} = {!ter-var-suc!}
ter-ren (ter-var-zero x) (ren-upr pρ pA) = {!!}
ter-ren (ter-var-suc pt) pρ = {!!}
ter-ren (ter-lam pA pt) pρ = ter-lam (ty-ren pA pρ) (ter-ren pt (ren-upr pρ pA))
ter-ren (ter-app pr ps) pρ = {!!} -- ter-app {!ter-ren pr pρ!} {!!}

ter-eq-ren (ter-eq-ty-eq pts pAB) pρ = ter-eq-ty-eq (ter-eq-ren pts pρ) (ty-eq-ren pAB pρ)
ter-eq-ren (ter-eq-beta x x₁) pρ = {!!}
ter-eq-ren (ter-eq-eta x) pρ = {!!}
ter-eq-ren (ter-eq-var-zero x) pρ = {!!}
ter-eq-ren (ter-eq-var-suc pts) pρ = {!!}
ter-eq-ren (ter-eq-lam pA pts) pρ = ter-eq-lam (ty-ren pA pρ) (ter-eq-ren pts (ren-upr pρ pA))
ter-eq-ren (ter-eq-app pru psv) pρ = ter-eq-app (ter-eq-ren {!!} pρ) (ter-eq-ren psv pρ)
ter-eq-ren (ter-eq-sym pts) pρ = ter-eq-sym (ter-eq-ren pts pρ)
ter-eq-ren (ter-eq-trans pts psr) pρ = ter-eq-trans (ter-eq-ren pts pρ) (ter-eq-ren psr pρ)

-- -}
