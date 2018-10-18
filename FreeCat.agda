-- The free e-category on a graph.
module FreeCat {ls lr} (A : Set ls) (R : A → A → Set lr) where

open import Agda.Primitive
open import Basics


-- The free category on a graph.

data Raw : Set (ls ⊔ lr) where
  -- Objects
  in-obj : A → Raw

  -- Morphisms
  in-hom : {a b : A} (r : R a b) → Raw
  idr : Raw
  _∘r_ : Raw → Raw → Raw

infixl 40 _∘r_

data Obj : (a : Raw) → Set ls
data _∈_⇒_ : (f : Raw) → Raw → Raw → Set (ls ⊔ lr)
data _~_ : (f g : Raw) → Set (ls ⊔ lr)

data Obj where
  t-in-obj : (a : A) → Obj (in-obj a)

data _∈_⇒_ where
  t-in-hom : {a b : A} (r : R a b) → (in-hom r) ∈ (in-obj a) ⇒ (in-obj b)
  t-id : ∀ {x} (_ : Obj x) → idr ∈ x ⇒ x
  t-∘r : {x y z f g : Raw} → f ∈ y ⇒ z → g ∈ x ⇒ y → (f ∘r g) ∈ x ⇒ z

data _~_ where
  t-∘r-assoc : ∀ {a b c d f g h} {p : f ∈ c ⇒ d} {q : g ∈ b ⇒ c } {r : h ∈ a ⇒ b} →
    f ∘r (g ∘r h) ~ (f ∘r g) ∘r h
  t-∘r-cong : ∀ {a b c f f' g g'} 
                {p : f ∈ b ⇒ c} {q : f' ∈ b ⇒ c} {r : g ∈ a ⇒ b} {s : g' ∈ a ⇒ b} →
                f ~ f' → g ~ g' → f ∘r g ~ f' ∘r g'
  t-idr-l : ∀ {a b f} → f ∈ a ⇒ b → idr ∘r f ~ f
  t-idr-r : ∀ {a b f} → f ∈ a ⇒ b → f ∘r idr ~ f

  t-~-refl : ∀ {a b f} → {p : f ∈ a ⇒ b} → f ~ f
  t-~-sym  : ∀ {f g} → f ~ g  → g ~ f
  t-~-trans  : ∀ {f g h} → f ~ g  → g ~ h → f ~ h
  

freeCat : ECat
obj freeCat = Σ λ (a : Raw) → Obj a
hom freeCat (a , _) (b , _) = Σ λ (f : Raw) → f ∈ a ⇒ b 
hom-rel freeCat (f , _) (g , _) = f ~ g
hom-eqr freeCat = record
  { refl = λ {a} → t-~-refl {p = snd a} ; sym = t-~-sym ; trans = t-~-trans }
comp freeCat (f , p) (g , q) = f ∘r g , t-∘r p q
comp-assoc freeCat {f = f} {g} {h} = t-∘r-assoc {p = snd f} {snd g} {snd h}
comp-cong freeCat {f = f} {f'} {g} {g'} = t-∘r-cong {p = snd f} {snd f'} {snd g} {snd g'}
id freeCat {_ , p} = idr , t-id p
id-l freeCat {f = f} = t-idr-l (snd f)
id-r freeCat {f = f} = t-idr-r (snd f)


-- Some inversion lemmas.
inv-mor-s : ∀ {a b f} → f ∈ a ⇒ b → Obj a
inv-mor-s (t-in-hom {a} {b} r) = t-in-obj a
inv-mor-s (t-id x) = x
inv-mor-s (t-∘r pf pg) = inv-mor-s pg

inv-mor-t : ∀ {a b f} → f ∈ a ⇒ b → Obj b
inv-mor-t (t-in-hom {a} {b} r) = t-in-obj b
inv-mor-t (t-id x) = x
inv-mor-t (t-∘r pf pg) = inv-mor-t pf

inv-~-s : ∀ {f g} → f ~ g → obj freeCat
inv-~-s (t-∘r-assoc {a = a} {r = r}) = a , inv-mor-s r
inv-~-s (t-∘r-cong {a = a} {r = r} ff' gg') = a , inv-mor-s r
inv-~-s (t-idr-l {a = a} pf) = a , inv-mor-s pf
inv-~-s (t-idr-r {a = a} pf) = a , inv-mor-s pf
inv-~-s (t-~-refl {a = a} {p = p}) = a , inv-mor-s p
inv-~-s (t-~-sym fg) = inv-~-s fg
inv-~-s (t-~-trans fg gh) = inv-~-s fg

inv-~-t : ∀ {f g} → f ~ g → obj freeCat
inv-~-t (t-∘r-assoc {d = d} {p = p}) = d , inv-mor-t p
inv-~-t (t-∘r-cong {c = c} {p = p} ff' gg') = c , inv-mor-t p
inv-~-t (t-idr-l {b = b} pf) = b , inv-mor-t pf
inv-~-t (t-idr-r {b = b} pf) = b , inv-mor-t pf
inv-~-t (t-~-refl {b = b} {p = p}) = b , inv-mor-t p
inv-~-t (t-~-sym fg) = inv-~-t fg
inv-~-t (t-~-trans fg gh) = inv-~-t fg

inv-~-l : ∀ {f g} (fg : f ~ g) →
          let (a , _) = inv-~-s fg
              (b , _) = inv-~-t fg
          in f ∈ a ⇒ b
inv-~-l (t-∘r-assoc {p = p} {q} {r})= 
  t-∘r p (t-∘r q r)
inv-~-l (t-∘r-cong {a} {b} {c} {f} {f'} {g} {g'} ff' gg') = 
  {!!}
inv-~-l (t-idr-l x) = {!!}
inv-~-l (t-idr-r x) = {!!}
inv-~-l t-~-refl = {!!}
inv-~-l (t-~-sym fg) = {!!}
inv-~-l (t-~-trans fg gh) = {!!}



-- module FreeElim {lo lh lr} (C : ECat {lo} {lh} {lr})
--            (iA : A → obj C) (iR : {a b : A} → R a b → hom C (iA a) (iA b)) where
--   open ECat C using () renaming (comp to _∘c_ ; hom-rel to _~c_)
--   infix 10 _~c_

--   objMap : {a : Raw} (p : Obj a) → obj C
--   objMap (t-in-obj a) = iA a

--   homMap : {a b f : Raw} (pa : Obj a) (pb : Obj b) → 
--            f ∈ a ⇒ b → hom C (objMap pa) (objMap pb)
--   homMap (t-in-obj a) (t-in-obj b) (t-in-hom r) = iR r
--   homMap pa pb (t-id x) = {!!}
--   homMap pa pb (t-∘r pf pf₁) = {!!}
  
--   ~Map   : {a b f g : Raw} {pa : Obj a} {pb : Obj b}
--            {pf : f ∈ a ⇒ b} {pg : g ∈ a ⇒ b} →
--            f ~ g → (homMap pa pb pf) ~c (homMap pa pb pg)
--   ~Map = {!!}
