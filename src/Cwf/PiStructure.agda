module Cwf.PiStructure where

open import Basics
open import Presheaves
open import Cwf.Elem

module _ {lvs lvr lo lh lr : Level} (E : eCwF {lvs} {lvr} {lo} {lh} {lr}) where
  open eCwF E
  open eCwFNotation {Ctx = Ctx} Ty Tm

  record PiStructure : Set (lo ⊔ lh ⊔ lr ⊔ lvr ⊔ lvs) where
    field
      Pi : ∀ {Γ} (A : Typ Γ) (B : Typ (Γ ∙ A)) → Typ Γ
      lam : ∀ {Γ} {A : Typ Γ} {B : Typ (Γ ∙ A)} (t : Ter (Γ ∙ A) B) → Ter Γ (Pi A B)
      app : ∀ {Γ} {A : Typ Γ} {B : Typ (Γ ∙ A)} (r : Ter Γ (Pi A B)) (s : Ter Γ A) →
            Ter Γ (B [ [[ s ]] ])

      -- TODO: congruence rules for Pi, lam, and app

      subst-Pi : ∀ {Δ Γ} {σ : Subst Δ Γ} {A : Typ Γ} {B : Typ (Γ ∙ A)} →
                 (Pi A B) [ σ ] ~ Pi (A [ σ ]) (B [ σ ⁺ ])

      subst-lam : ∀ {Δ Γ} {σ : Subst Δ Γ} {A : Typ Γ} {B : Typ (Γ ∙ A)} {t : Ter (Γ ∙ A) B} →
                  (lam t) [ σ ]t ~t ι subst-Pi (lam (t [ σ ⁺ ]t))

      subst-app : ∀ {Δ Γ} {σ : Subst Δ Γ} {A : Typ Γ} {B : Typ (Γ ∙ A)}
                  {r : Ter Γ (Pi A B)} {s : Ter Γ A} →
                  let open EqRelReason ~eq
                      eq = begin
                             B [ [[ s ]] ] [ σ ]
                           ≈⟨ []-assoc ⟩
                             B [ [[ s ]] ∘s σ ]
                           ≈⟨ []-resp-r [[]]-subst ⟩
                             B [ σ ⁺ ∘s [[ s [ σ ]t ]] ]
                           ≈⟨ []-assoc-inv ⟩
                             B [ σ ⁺ ] [ [[ s [ σ ]t ]] ]
                           ∎
                  in
                    (app r s) [ σ ]t ~t ι eq (app (ι' subst-Pi (r [ σ ]t)) (s [ σ ]t))

      beta : ∀ {Γ} {A : Typ Γ} {B : Typ (Γ ∙ A)} (t : Ter (Γ ∙ A) B) (s : Ter Γ A) →
             app (lam t) s ~t t [ [[ s ]] ]t
      eta : ∀ {Γ} {A : Typ Γ} {B : Typ (Γ ∙ A)} {t : Ter Γ (Pi A B)} →
            let eq : B ~ ((B [ pp ⁺ ]) [ [[ qq ]] ])
                eq = ~eq .trans []-id (~eq .trans ([]-resp-r lift-id) []-assoc-inv)
            in
              t ~t lam (ι eq (app (ι (~eq .sym subst-Pi) (t [ pp ]t)) qq))
