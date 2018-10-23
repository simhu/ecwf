module Discrete where

open import Basics



-- Any setoid is a discrete category (which is also a groupoid)
# : ∀ {ls lr} (A : eSet {ls} {lr}) → ECat {ls} {lr} {lzero}
obj (# A) = A .set
hom (# A) a b = A .rel a b
hom-rel (# A) p q = Unit {lzero}
refl (hom-eqr (# A)) = tt
sym (hom-eqr (# A)) =  λ _ → tt
trans (hom-eqr (# A)) = λ _ _ → tt
comp (# A) p q = A .trans q p
comp-assoc (# A) = tt
comp-cong (# A) = λ _ _ → tt
id (# A) = A .refl
id-l (# A) = tt
id-r (# A) = tt


#fun : ∀ {l} {A B} (f : hom (ESet {l}) A B) → eFunctor (# A) (# B)
fun (#fun f) = f .ap
mor (#fun f) = f .ap-cong
resp (#fun f) =  λ _ → tt
id-mor (#fun f) = tt
comp-mor (#fun f) = tt

#id : ∀ {l} {A : eSet {l}}  → eNatIso (idFunctor (# A)) (#fun (id (ESet {l})))
#id {A = A} = record 
  { to-nat = record { nat = λ _ → A .refl ; nat-eq = tt }
  ; to-is-iso = record { nat-inv =  λ _ → A .refl ; nat-inv-sect = tt ; nat-inv-retract = tt }
  }

#comp : ∀ {l} {A B C : eSet {l}} {f : hom (ESet {l}) B C} {g : hom (ESet {l}) A B} →
        eNatIso ((#fun f) ∘Func (#fun g)) (#fun (comp (ESet {l}) f g))
#comp {C = C} = record
  { to-nat = record { nat = λ _ → C .refl ; nat-eq = tt }
  ; to-is-iso = record { nat-inv = λ _ → C .refl ; nat-inv-sect = tt ; nat-inv-retract = tt }
  }

#resp : ∀ {l} {A B : eSet {l}} {f g : eMap A B} → eMapRel f g → hom-rel CAT (#fun f) (#fun g)
#resp {A = A} {B} p = record
  { to-nat = record { nat = λ a → p ` A .refl {a} ; nat-eq = tt }
  ; to-is-iso = record { nat-inv = λ a → B .sym (p ` A .refl {a})
                       ; nat-inv-sect = tt
                       ; nat-inv-retract = tt }
  }

## : ∀ {lo} → eFunctor (ESet {lo}) (CAT {lo} {lo} {lzero})
##  = record { fun =  # ; mor = #fun ; resp = #resp ; id-mor = #id ; comp-mor = #comp }
