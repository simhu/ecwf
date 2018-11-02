module Syntax.ExplicitExtrinsic.Initial where

open import Basics
open import Presheaves
open import Cwf.Elem
open import Products using (isTerminal)

open import Equality

-- TODO: is there any way to not require lzero?  (The syntax has to be
-- generalized.)
module Elim {ks kr lo lh lr : Level}
  (E : eCwF {lzero} {lzero} {lo} {lh} {lr}) where

  open import Syntax.ExplicitExtrinsic {lzero}

  open eCwF
  module Notation {ks kr lo lh lr} (H : eCwF {ks} {kr} {lo} {lh} {lr}) = eCwFNotation {Ctx = Ctx H} (Ty H) (Tm H)

  open Notation E renaming
    ( _~_ to _~E_ ; _~s_ to _~sE_ ; _~t_ to _~tE_ ; Typ to TypE ; Ter to TerE ; _[_] to _[_]E
    ; _[_]t to _[_]tE     
    )
  open Notation SynCwf renaming (_~_ to _~S_ ; _~s_ to _~sS_ ; Typ to TypS ; _[_] to _[_]S)

  module _ where
    abstract
      mutual
        o : ∀ {Γ} → Γ ⊢ → obj (Ctx E)
        o {Γ} pΓ = {!!}

        o# : ∀ {Γ} (pΓ pΓ' :  Γ ⊢) → o pΓ ≡ o pΓ'
        o# {Γ} pΓ pΓ' = {!!}

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

        ty-cong : ∀ {Γ A B} (pΓ : Γ ⊢) (pA : Γ ⊢ A) (pB : Γ ⊢ B)
                  (pAB : Γ ⊢ A ~ B) → ty pΓ pA ~E ty pΓ pB
        ty-cong = {!!}

        -- probably easier w/o the B and use trans etc
        sty-cong : ∀ {Γ Δ σ A B} (pΔ : Δ ⊢) (pΓ : Γ ⊢) (pσ : σ ∈ Δ ⇒ Γ)
                (pA : Γ ⊢ A) (pB : Γ ⊢ B) (pAB : Γ ⊢ A ~ B)
                → (ty pΓ pA [ m pΔ pΓ pσ ]E) ~E ty pΔ (ap (ty-map pσ) (B , pB) .snd) --  (snd ((B , pB) [ σ , pσ ]S))
        sty-cong = {!!}

        ter : ∀ {Γ A t} (pΓ : Γ ⊢) (pA : Γ ⊢ A) (pt : Γ ⊢ t ∈ A) → TerE (o pΓ) (ty pΓ pA)
        ter = {!!}

        ter-cong : ∀ {Γ A t s} (pΓ : Γ ⊢) (pA : Γ ⊢ A) (pt : Γ ⊢ t ∈ A) (ps : Γ ⊢ s ∈ A)
                   (pts : Γ ⊢ t ~ s ∈ A) → ter pΓ pA pt ~tE ter pΓ pA ps
        ter-cong = {!!}
      
        foo : ∀ {Γ Δ A B σ t s} 
              (pΓ : Γ ⊢) (pΔ : Δ ⊢) (pA : Γ ⊢ A) (pB : Δ ⊢ B) (pσ : σ ∈ Δ ⇒ Γ)
              (q : Δ ⊢ B ~ A [ σ ]) (pt : Γ ⊢ t ∈ A) (ps : Γ ⊢ s ∈ A) (pts : Γ ⊢ t ~ s ∈ A) →
              _~tE_  -- fun (Tm E) (o pΔ , ty pΔ pB) .rel
                (mor (Tm E)
                  (m pΔ pΓ pσ ,
                    eqr (fun (Ty E) (o pΔ)) .trans (ty-cong pΔ pB (ty-subst pA pσ) q)
                    (eqr (fun (Ty E) (o pΔ)) .trans
                      (sym (eqr (fun (Ty E) (o pΔ)))
                        (sty-cong pΔ pΓ pσ pA pA (ty-eq-refl pA)))
                      (eqr (fun (Ty E) (o pΔ)) .EqRel.refl)))
                    .ap (ter pΓ pA pt))
                (ter pΔ pB (ter-ty-eq (ter-subst ps pσ) (ty-eq-sym q)))
        foo = {!!}





  elim-ctx : eFunctor (eCwF.Ctx SynCwf) (eCwF.Ctx E)
  elim-ctx = record
    { fun = λ { (Γ , pΓ) → o pΓ }
    ; mor = λ { {Δ , pΔ} {Γ , pΓ} (σ , pσ) → m pΔ pΓ pσ }  
    ; resp = λ { {Δ , pΔ} {Γ , pΓ} {σ , pσ} {τ , pτ} pστ → m-resp pΔ pΓ pσ pτ pστ} 
    ; id-mor = {!!} ; comp-mor = {!!} }

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
        { {A , pA} {B , pB} pAB → sty-cong pΔ pΓ pσ pA pB pAB
        } 
      }
    }

  elim-ter-nat : (ΓA : obj (∫ {C = Ctx SynCwf} (Ty SynCwf) op)) →
                 eMap (fun (Tm SynCwf) ΓA) (fun (Tm E ∘Func (∫base elim-ctx elim-ty op-fun)) ΓA)
  elim-ter-nat ((Γ , pΓ), (A , pA)) = record
    { ap =  λ { (t , pt) → ter pΓ pA pt }
    ; ap-cong =  λ { {t , pt} {s , ps} pts → ter-cong pΓ pA pt ps pts}
    }

  -- elim-ter-nat-eq : {ΓA ΔB : obj (∫ {C = Ctx SynCwf} (Ty SynCwf) op)}
  --                   {f : hom (∫ {C = Ctx SynCwf} (Ty SynCwf) op) ΓA ΔB} →
  --                   eMapRel
  --                     (comp ESet (mor (Tm E ∘Func (∫base {C = Ctx SynCwf} {D = Ctx E} elim-ctx elim-ty op-fun)) f)
  --                       (elim-ter-nat ΓA))
  --                     (comp ESet (elim-ter-nat ΔB) (mor (Tm SynCwf) f))
  -- elim-ter-nat-eq = {!!}                  



  elim-ter : eNat (Tm SynCwf) (Tm E ∘Func (∫base elim-ctx elim-ty op-fun))
  elim-ter = record
    { nat = elim-ter-nat 
    ; nat-eq = λ 
      { {(Γ , pΓ) , A , pA} {(Δ , pΔ) , B , pB} {(σ , pσ) , q} → map-rel λ
        { {t , pt} {s , ps} pts → {!!} -- foo pΓ pΔ pA pB pσ q pt ps pts
        }
      }
    }

  elim : Mor SynCwf E
  elim = record { ctx = elim-ctx ; ty = elim-ty ; tm = elim-ter }

