module Comma where

open import Basics

-- Comma categories
comma : {lco lch lcr ldo ldh ldr leo leh ler : Level}
  {C : ECat {lco} {lch} {lcr}} {D : ECat {ldo} {ldh} {ldr}} {E : ECat {leo} {leh} {ler}}
  (F : eFunctor C D) (G : eFunctor E D) →
  ECat {lco ⊔ ldh ⊔ leo} {lch ⊔ (ldr ⊔ leh)} {lcr ⊔ ler}
comma {C = C} {D} {E} F G = record
  { obj = Σ λ (c : obj C) → Σ λ (e : obj E) → hom D (fun F c) (fun G e)
  ; hom = λ { (c , e , h) (c' , e' , h') →  Σ λ (f : hom C c c') → Σ λ (g : hom E e e') →
           h' ∘d (mor F f) ~d  (mor G g) ∘d h}
  ; hom-rel = λ { (f , g , _) (f' , g' , _) → (f ~c f') × (g ~e g')}
  ; hom-eqr =  record { refl = C .hom-eqr .refl , E .hom-eqr .refl
                      ; sym =  λ p → C .hom-eqr .sym (fst p) , E .hom-eqr .sym (snd p)
                      ; trans = λ p q → C .hom-eqr .trans (fst p) (fst q) ,
                                        E .hom-eqr .trans (snd p) (snd q)
                      }
  ; comp = λ { {_ , _ , h} {_ , _ , h'} {_ , _ , h'' } (f , g , p) (f' , g' , p') →
      f ∘c f' , g ∘e g' ,
      let open EqRelReason (D .hom-eqr) in
        begin
           h'' ∘d mor F (f ∘c f')
         ≈⟨ comp-cong-r D (comp-mor-inv F) ⟩
           h'' ∘d (mor F f ∘d mor F f')
         ≈⟨ comp-assoc D ⟩
           (h'' ∘d mor F f) ∘d mor F f'
         ≈⟨ comp-cong-l D p ⟩
           (mor G g ∘d h') ∘d mor F f'
         ≈⟨ comp-assoc-inv D ⟩
           mor G g ∘d (h' ∘d mor F f')
         ≈⟨ comp-cong-r D p' ⟩
           mor G g ∘d (mor G g' ∘d h)
         ≈⟨ comp-assoc D ⟩
           (mor G g ∘d mor G g') ∘d h
         ≈⟨ comp-cong-l D (comp-mor G) ⟩
           mor G (g ∘e g') ∘d h
         ∎ }
  ; comp-assoc = comp-assoc C , comp-assoc E
  ; comp-cong = λ p q → comp-cong C (fst p) (fst q) , comp-cong E (snd p) (snd q)
  ; id =  λ { {c , e , h} → id C , id E , let open EqRelReason (D .hom-eqr) in
                            begin
                              h ∘d mor F (id C)
                            ≈⟨ comp-cong-r D (id-mor-inv F) ⟩
                              h ∘d id D
                            ≈⟨ id-r D ⟩
                              h
                            ≈⟨ id-l-inv D ⟩
                              id D ∘d h
                            ≈⟨ comp-cong-l D (id-mor G) ⟩
                              mor G (id E) ∘d h
                            ∎}
  ; id-l = id-l C , id-l E
  ; id-r = id-r C , id-r E
  }
  where _~d_ = hom-rel D ; _∘d_ = comp D ; infixl 40 _∘d_
        _~c_ = hom-rel C ; _∘c_ = comp C ; infixl 40 _∘c_
        _~e_ = hom-rel E ; _∘e_ = comp E ; infixl 40 _∘e_


_↓_ = comma

comma-fst : {lco lch lcr ldo ldh ldr leo leh ler : Level}
            {C : ECat {lco} {lch} {lcr}} {D : ECat {ldo} {ldh} {ldr}} {E : ECat {leo} {leh} {ler}}
            (F : eFunctor C D) (G : eFunctor E D) →
            eFunctor (F ↓ G) C
comma-fst {C = C} F G = record
  { fun = fst ; mor = fst ; resp = fst
  ; id-mor = C .hom-eqr .refl ; comp-mor = C .hom-eqr .refl
  }

comma-snd : {lco lch lcr ldo ldh ldr leo leh ler : Level}
            {C : ECat {lco} {lch} {lcr}} {D : ECat {ldo} {ldh} {ldr}} {E : ECat {leo} {leh} {ler}}
            (F : eFunctor C D) (G : eFunctor E D) →
            eFunctor (F ↓ G) E
comma-snd {E = E} F G = record
  { fun = λ x → x .snd .fst ; mor = λ x → x .snd .fst ; resp = snd
  ; id-mor = E .hom-eqr .refl ; comp-mor = E .hom-eqr .refl
  }
