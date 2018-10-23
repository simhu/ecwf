module Discrete where

open import Basics



-- Any setoid is a discrete category (which is also a groupoid)
# : ∀ {k ls lr} (A : eSet {ls} {lr}) → ECat {ls} {lr} {k}
obj (# A) = A .set
hom (# A) a b = A .rel a b
hom-rel (# A) p q = Unit
refl (hom-eqr (# A)) = tt
sym (hom-eqr (# A)) =  λ _ → tt
trans (hom-eqr (# A)) = λ _ _ → tt
comp (# A) p q = A .trans q p
comp-assoc (# A) = tt
comp-cong (# A) = λ _ _ → tt
id (# A) = A .refl
id-l (# A) = tt
id-r (# A) = tt

#0 : ∀ {ls lr} (A : eSet {ls} {lr}) → ECat {ls} {lr} {lzero}
#0 = #

#fun : ∀ {k ls lr} {A B} (f : hom (ESet {ls} {lr}) A B) → eFunctor (# {k} A) (# {k} B)
fun (#fun f) = f .ap
mor (#fun f) = f .ap-cong
resp (#fun f) =  λ _ → tt
id-mor (#fun f) = tt
comp-mor (#fun f) = tt

#fun0 : ∀ {ls lr} {A B} (f : hom (ESet {ls} {lr}) A B) → eFunctor (#0 A) (#0 B)
#fun0 = #fun

#id : ∀ {k ls lr} {A : eSet {ls} {lr}} → eNatIso (idFunctor (# {k} A)) (#fun (id (ESet {ls} {lr})))
#id {A = A} = record 
  { to-nat = record { nat = λ _ → A .refl ; nat-eq = tt }
  ; to-is-iso = record { nat-inv =  λ _ → A .refl ; nat-inv-sect = tt ; nat-inv-retract = tt }
  }

#comp : ∀ {k ls lr} {A B C : eSet {ls} {lr}} {f : hom (ESet {ls} {lr}) B C} {g : hom (ESet {ls} {lr}) A B} →
        eNatIso ((#fun {k} f) ∘Func (#fun g)) (#fun (comp (ESet {ls} {lr}) f g))
#comp {C = C} = record
  { to-nat = record { nat = λ _ → C .refl ; nat-eq = tt }
  ; to-is-iso = record { nat-inv = λ _ → C .refl ; nat-inv-sect = tt ; nat-inv-retract = tt }
  }

#resp : ∀ {k ls lr} {A B : eSet {ls} {lr}} {f g : eMap A B} → eMapRel f g → hom-rel (CAT {lr = k}) (#fun f) (#fun g)
#resp {A = A} {B} p = record
  { to-nat = record { nat = λ a → p ` A .refl {a} ; nat-eq = tt }
  ; to-is-iso = record { nat-inv = λ a → B .sym (p ` A .refl {a})
                       ; nat-inv-sect = tt
                       ; nat-inv-retract = tt }
  }

## : ∀ {k ls lr} → eFunctor (ESet {ls} {lr}) (CAT {ls} {lr} {k})
##  = record { fun =  # ; mor = #fun ; resp = #resp ; id-mor = #id ; comp-mor = #comp }
