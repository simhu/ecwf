{-# OPTIONS --without-K #-}
module Syntax.ExplicitExtrinsic.Initial where

open import Basics
open import Presheaves
open import Cwf.Elem
open import Products using (isTerminal)

open import Equality renaming (refl to ≡-refl)

-- TODO: is there any way to not require lzero?  (The syntax has to be
-- generalized.)
module Elim {ks kr lo lh lr : Level}
  (E : eCwF {lzero} {lzero} {lo} {lh} {lr}) where

  open import Syntax.ExplicitExtrinsic {lzero}

  open eCwF
  module Notation {ks kr lo lh lr} (H : eCwF {ks} {kr} {lo} {lh} {lr}) = eCwFNotation {Ctx = Ctx H} (Ty H) (Tm H)

  open Notation E renaming
    ( _~_ to _~E_ ; ~eq to ~Eeq ; _~s_ to _~sE_ ; _~t_ to _~tE_ ; Typ to TypE ; ~teq to ~tEeq
    ; Ter to TerE ; _[_] to _[_]E
    ; ids to idsE ; _[_]t to _[_]tE
    )
  open Notation SynCwf using () renaming (_~_ to _~S_ ; _~s_ to _~sS_ ; Typ to TypS ; _[_] to _[_]S)

  module _ where -- the interpretation
    abstract
      mutual
        o : ∀ {Γ} → Γ ⊢ → obj (Ctx E)
        o {Γ} pΓ = {!!}

        -- ??
        -- o# : ∀ {Γ} (pΓ pΓ' :  Γ ⊢) → o pΓ ≡ o pΓ'
        -- o# {Γ} pΓ pΓ' = {!!}

        m : ∀ {Δ Γ σ} (pΔ : Δ ⊢) (pΓ : Γ ⊢) (pσ : σ ∈ Δ ⇒ Γ) →
            hom (Ctx E) (o pΔ) (o pΓ)
        m = {!!}

        m# : ∀ {Δ Γ σ} (pΔ : Δ ⊢) (pΓ : Γ ⊢)
             (pσ pσ' : σ ∈ Δ ⇒ Γ) → m pΔ pΓ pσ ~sE m pΔ pΓ pσ'
        m# = {!!}

        m-resp : ∀ {Δ Γ σ τ} (pΔ : Δ ⊢) (pΓ : Γ ⊢) (pσ : σ ∈ Δ ⇒ Γ) (pτ : τ ∈ Δ ⇒ Γ)
               (pστ : σ ~ τ ∈ Δ ⇒ Γ) → m pΔ pΓ pσ ~sE m pΔ pΓ pτ
        m-resp {Δ} {Γ} {σ} {τ} pΔ pΓ pσ pτ pστ = {!!}

        ty : ∀ {Γ A} (pΓ : Γ ⊢) (pA : Γ ⊢ A) → TypE (o pΓ)
        ty = {!!}

        -- ??
        -- ty# : ∀ {Γ A} (pΓ : Γ ⊢) (pA pA' : Γ ⊢ A) → ty pΓ pA ~E ty pΓ pA'
        -- ty# = {!!}

        ty-cong : ∀ {Γ A B} (pΓ : Γ ⊢) (pA : Γ ⊢ A) (pB : Γ ⊢ B)
                  (pAB : Γ ⊢ A ~ B) → ty pΓ pA ~E ty pΓ pB
        ty-cong = {!!}

        subst-ty : ∀ {Γ Δ σ A} (pΔ : Δ ⊢) (pΓ : Γ ⊢)
                          (pσ : σ ∈ Δ ⇒ Γ) (pA : Γ ⊢ A) →
                          (ty pΓ pA [ m pΔ pΓ pσ ]E) ~E ty pΔ (ap (ty-map pσ) (A , pA) .snd)
        subst-ty = {!!}

        ter : ∀ {Γ A t} (pΓ : Γ ⊢) (pA : Γ ⊢ A) (pt : Γ ⊢ t ∈ A) → TerE (o pΓ) (ty pΓ pA)
        ter = {!!}

        ter-cong : ∀ {Γ A t s} (pΓ : Γ ⊢) (pA : Γ ⊢ A) (pt : Γ ⊢ t ∈ A) (ps : Γ ⊢ s ∈ A)
                   (pts : Γ ⊢ t ~ s ∈ A) → ter pΓ pA pt ~tE ter pΓ pA ps
        ter-cong = {!!}

        subst-ter : ∀ {Γ Δ A σ t} (pΔ : Δ ⊢) (pΓ : Γ ⊢) (pσ : σ ∈ Δ ⇒ Γ)
                    (pA : Γ ⊢ A) (pt : Γ ⊢ t ∈ A) →
                    let pAσ = ty-subst pA pσ  -- aka: ap (ty-map pσ) (A , pA) .snd
                        ptσ = ter-subst pt pσ
                        eq : (ty pΓ pA [ m pΔ pΓ pσ ]E) ~E ty pΔ pAσ
                        eq = subst-ty pΔ pΓ pσ pA
                    in ter pΓ pA pt [ m pΔ pΓ pσ ]tE ~tE ι eq (ter pΔ pAσ ptσ)
        subst-ter {Γ} {Δ} {A} {σ} {t} pΔ pΓ pσ pA pt = {!!}

        -- does this make sense?
        ι-ter : ∀ {Γ A B t} (pΓ : Γ ⊢) (pA : Γ ⊢ A) (pB : Γ ⊢ B)
                  (pAB : Γ ⊢ A ~ B) (pt : Γ ⊢ t ∈ B) →
                  ι (ty-cong pΓ pA pB pAB) (ter pΓ pB pt)
                  ~tE ter pΓ pA (ter-ty-eq pt (ty-eq-sym pAB))
        ι-ter = {!!}


--------------------------------------------------------------------------------

    subst-ty-cong : ∀ {Γ Δ σ A B} (pΔ : Δ ⊢) (pΓ : Γ ⊢) (pσ : σ ∈ Δ ⇒ Γ)
            (pA : Γ ⊢ A) (pB : Γ ⊢ B) (pAB : Γ ⊢ A ~ B)
            → (ty pΓ pA [ m pΔ pΓ pσ ]E) ~E ty pΔ (ap (ty-map pσ) (B , pB) .snd)
                                            --  (snd ((B , pB) [ σ , pσ ]S))
    subst-ty-cong {Δ} {Γ} {σ} {A} {B} pΔ pΓ pσ pA pB pAB =
      let open EqRelReason ~Eeq in
      begin
        ty pΓ pA [ m pΔ pΓ pσ ]E
      ≈⟨ []-resp' (ty-cong pΓ pA pB pAB) (~seq .refl) ⟩
        ty pΓ pB [ m pΔ pΓ pσ ]E
      ≈⟨ subst-ty pΔ pΓ pσ pB ⟩
        ty pΔ (ap (ty-map pσ) (B , pB) .snd)
      ∎

    subst-ter-cong : ∀ {Γ Δ A B σ t s}
      (pΓ : Γ ⊢) (pΔ : Δ ⊢) (pA : Γ ⊢ A) (pB : Δ ⊢ B) (pσ : σ ∈ Δ ⇒ Γ)
      (q : Δ ⊢ B ~ A [ σ ]) (pt : Γ ⊢ t ∈ A) (ps : Γ ⊢ s ∈ A) (pts : Γ ⊢ t ~ s ∈ A) →
      _~tE_  -- fun (Tm E) (o pΔ , ty pΔ pB) .rel
        (mor (Tm E)
          (m pΔ pΓ pσ ,
            eqr (fun (Ty E) (o pΔ)) .trans (ty-cong pΔ pB (ty-subst pA pσ) q)
             (eqr (fun (Ty E) (o pΔ)) .trans
              (sym (eqr (fun (Ty E) (o pΔ)))
                (subst-ty-cong pΔ pΓ pσ pA pA (ty-eq-refl pA)))
              (eqr (fun (Ty E) (o pΔ)) .EqRel.refl)))
            .ap (ter pΓ pA pt))
        (ter pΔ pB (ter-ty-eq (ter-subst ps pσ) (ty-eq-sym q)))
    subst-ter-cong {Γ} {Δ} {A} {B} {σ} {t} {s} pΓ pΔ pA pB pσ q pt ps pts =
      let open EqRelReason (~tEeq {o pΔ} {ty pΔ pB})
          pAσ = ap (ty-map pσ) (A , pA) .snd -- aka: ty-subst pA pσ
          psσ = ter-subst ps pσ

          tyeq : ty pΔ pB ~E ty pΓ pA [ m pΔ pΓ pσ ]E
          tyeq = ~Eeq .trans (ty-cong pΔ pB (ty-subst pA pσ) q)
                    (~Eeq .trans (sym (eqr (fun (Ty E) (o pΔ)))
                      (subst-ty-cong pΔ pΓ pσ pA pA (ty-eq-refl pA)))
                    (~Eeq .refl))

          mσel : hom (∫ {C = Ctx E} (Ty E)) (o pΔ , ty pΓ pA [ m pΔ pΓ pσ ]E) (o pΓ , ty pΓ pA)
          mσel = m pΔ pΓ pσ , ~Eeq .refl

          ιtyeqel : hom (∫ {C = Ctx E} (Ty E)) (o pΔ , ty pΔ pB) (o pΔ , ty pΓ pA [ m pΔ pΓ pσ ]E)
          ιtyeqel = idsE , ~Eeq .trans tyeq (id-mor (Ty E) .map-resp (~Eeq .refl))
      in
      begin
        mor (Tm E)
          (m pΔ pΓ pσ , tyeq) .ap (ter pΓ pA pt)
      ≈⟨ mor (Tm E) _ .ap-cong (ter-cong pΓ pA pt ps pts) ⟩
        mor (Tm E)
          (m pΔ pΓ pσ , tyeq) .ap (ter pΓ pA ps)
      ≈⟨ resp (Tm E) (id-r-inv (Ctx E)) .map-resp (~tEeq .refl) ⟩
        mor (Tm E)
          (mσel ∘el ιtyeqel) .ap (ter pΓ pA ps)
      ≈⟨ comp-mor-inv (Tm E) .map-resp (~tEeq .refl) ⟩
        mor (Tm E) ιtyeqel .ap (mor (Tm E) mσel .ap (ter pΓ pA ps))
      ≈⟨⟩
        ι tyeq ((ter pΓ pA ps) [ m pΔ pΓ pσ ]tE)
      ≈⟨ ιresp (subst-ter pΔ pΓ pσ pA ps) ⟩
        ι tyeq (ι (subst-ty pΔ pΓ pσ pA) (ter pΔ pAσ psσ))
      ≈⟨ ιtrans _ _ ⟩
        ι (~Eeq .trans tyeq (subst-ty pΔ pΓ pσ pA)) (ter pΔ pAσ psσ)
      ≈⟨ ιirr (~tEeq .refl) ⟩
        ι (ty-cong pΔ pB pAσ q) (ter pΔ pAσ psσ)
      ≈⟨ ι-ter pΔ pB (ty-subst pA pσ) q (ter-subst ps pσ) ⟩
        ter pΔ pB (ter-map pσ q .ap (s , ps) .snd)
      ∎

  elim-ctx : eFunctor (eCwF.Ctx SynCwf) (eCwF.Ctx E)
  elim-ctx = record
    { fun = λ { (Γ , pΓ) → o pΓ }
    ; mor = λ { {Δ , pΔ} {Γ , pΓ} (σ , pσ) → m pΔ pΓ pσ }
    ; resp = λ { {Δ , pΔ} {Γ , pΓ} {σ , pσ} {τ , pτ} pστ → m-resp pΔ pΓ pσ pτ pστ}
    ; id-mor = {!!}
 ; comp-mor = {!!} }

  elim-ty-nat : (Γ : obj (Ctx SynCwf op)) →
                eMap (fun (Ty SynCwf) Γ) (fun (Ty E ∘Func (elim-ctx op-fun)) Γ)
  elim-ty-nat (Γ , pΓ) = record
    { ap = λ {(A , pA) → ty pΓ pA}
    ; ap-cong = λ { {A , pA} {B , pB} pAB → ty-cong pΓ pA pB pAB}
    }

  elim-ty : eNat (Ty SynCwf) (Ty E ∘Func (elim-ctx op-fun))
  elim-ty = record
    { nat = elim-ty-nat
    ; nat-eq = λ
      { {Γ , pΓ} {Δ , pΔ} {σ , pσ} → map-rel λ
        { {A , pA} {B , pB} pAB → subst-ty-cong pΔ pΓ pσ pA pB pAB
        }
      }
    }

  elim-ter-nat : (ΓA : obj (∫ {C = Ctx SynCwf} (Ty SynCwf) op)) →
                 eMap (fun (Tm SynCwf) ΓA) (fun (Tm E ∘Func (∫base elim-ctx elim-ty op-fun)) ΓA)
  elim-ter-nat ((Γ , pΓ), (A , pA)) = record
    { ap =  λ { (t , pt) → ter pΓ pA pt }
    ; ap-cong =  λ { {t , pt} {s , ps} pts → ter-cong pΓ pA pt ps pts}
    }

  elim-ter : eNat (Tm SynCwf) (Tm E ∘Func (∫base elim-ctx elim-ty op-fun))
  elim-ter = record
    { nat = elim-ter-nat
    ; nat-eq = λ
      { {(Γ , pΓ) , A , pA} {(Δ , pΔ) , B , pB} {(σ , pσ) , q} → map-rel λ
        { {t , pt} {s , ps} pts → subst-ter-cong pΓ pΔ pA pB pσ q pt ps pts
        }
      }
    }

  elim : Mor SynCwf E
  elim = record { ctx = elim-ctx ; ty = elim-ty ; tm = elim-ter }
