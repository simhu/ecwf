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
data _~_∈_⇒_ : (f g a b : Raw) → Set (ls ⊔ lr)

data Obj where
  t-in-obj : (a : A) → Obj (in-obj a)

data _∈_⇒_ where
  t-in-hom : {a b : A} (r : R a b) → (in-hom r) ∈ (in-obj a) ⇒ (in-obj b)
  t-id : ∀ {x} → Obj x → idr ∈ x ⇒ x
  t-∘r : {x y z f g : Raw} → f ∈ y ⇒ z → g ∈ x ⇒ y → (f ∘r g) ∈ x ⇒ z

data _~_∈_⇒_ where
  t-∘r-assoc : ∀ {a b c d f g h} {p : f ∈ c ⇒ d} {q : g ∈ b ⇒ c} {r : h ∈ a ⇒ b} →
    f ∘r (g ∘r h) ~ (f ∘r g) ∘r h ∈ a ⇒ d
  t-∘r-cong : ∀ {a b c f f' g g'} 
                {p : f ∈ b ⇒ c} {q : f' ∈ b ⇒ c} {r : g ∈ a ⇒ b} {s : g' ∈ a ⇒ b} →
                f ~ f' ∈ b ⇒ c → g ~ g' ∈ a ⇒ b → f ∘r g ~ f' ∘r g' ∈ a ⇒ c
  t-idr-l : ∀ {a b f} → f ∈ a ⇒ b → idr ∘r f ~ f ∈ a ⇒ b
  t-idr-r : ∀ {a b f} → f ∈ a ⇒ b → f ∘r idr ~ f ∈ a ⇒ b

  t-~-refl : ∀ {a b f} → {p : f ∈ a ⇒ b} → f ~ f ∈ a ⇒ b
  t-~-sym  : ∀ {a b f g} → f ~ g ∈ a ⇒ b  → g ~ f ∈ a ⇒ b
  t-~-trans  : ∀ {a b f g h} → f ~ g ∈ a ⇒ b → g ~ h ∈ a ⇒ b → f ~ h ∈ a ⇒ b
  

freeCat : ECat
obj freeCat = Σ λ (a : Raw) → Obj a
hom freeCat (a , _) (b , _) = Σ λ (f : Raw) → f ∈ a ⇒ b 
hom-rel freeCat {a , _} {b , _} (f , _) (g , _) = f ~ g ∈ a ⇒ b
hom-eqr freeCat = record
  { refl = λ {a} → t-~-refl {p = snd a} ; sym = t-~-sym ; trans = t-~-trans }
comp freeCat (f , p) (g , q) = f ∘r g , t-∘r p q
comp-assoc freeCat {f = f} {g} {h} = t-∘r-assoc {p = snd f} {snd g} {snd h}
comp-cong freeCat {f = f} {f'} {g} {g'} = t-∘r-cong {p = snd f} {snd f'} {snd g} {snd g'}
id freeCat {_ , p} = idr , t-id p
id-l freeCat {f = f} = t-idr-l (snd f)
id-r freeCat {f = f} = t-idr-r (snd f)

-- -- Some inversion lemmas.
mor-s : ∀ {a b f} → f ∈ a ⇒ b → Obj a
mor-s (t-in-hom {a} {b} r) = t-in-obj a
mor-s (t-id x) = x
mor-s (t-∘r pf pg) = mor-s pg

mor-t : ∀ {a b f} → f ∈ a ⇒ b → Obj b
mor-t (t-in-hom {a} {b} r) = t-in-obj b
mor-t (t-id x) = x
mor-t (t-∘r pf pg) = mor-t pf


~-l : ∀ {a b f g} → f ~ g ∈ a ⇒ b → f ∈ a ⇒ b
~-r : ∀ {a b f g} → f ~ g ∈ a ⇒ b → g ∈ a ⇒ b

~-l (t-∘r-assoc {p = p} {q} {r}) = t-∘r p (t-∘r q r)
~-l (t-∘r-cong ff' gg') = t-∘r (~-l ff') (~-l gg')
~-l (t-idr-l pf) = t-∘r (t-id (mor-t pf)) pf
~-l (t-idr-r pf) = t-∘r pf (t-id (mor-s pf))
~-l (t-~-refl {p = p})= p
~-l (t-~-sym p) = ~-r p
~-l (t-~-trans p q) = ~-l p

~-r (t-∘r-assoc {p = p} {q} {r}) = t-∘r (t-∘r p q) r
~-r (t-∘r-cong ff' gg') = t-∘r (~-r ff') (~-r gg')
~-r (t-idr-l pf) = pf
~-r (t-idr-r pf) = pf
~-r (t-~-refl {p = p}) = p
~-r (t-~-sym p) = ~-l p
~-r (t-~-trans p q) = ~-r q



module FreeElim {lo lh lr} (C : ECat {lo} {lh} {lr})
           (iA : A → obj C) (iR : {a b : A} → R a b → hom C (iA a) (iA b)) where
  open ECat C using () renaming (comp to _∘c_ ; hom-rel to _~c_)

  objMap : {a : Raw} (p : Obj a) → obj C
  objMap {.(in-obj a)} (t-in-obj a) = iA a

  homMap' : {a b f : Raw} →
           (pf : f ∈ a ⇒ b) → hom C (objMap (mor-s pf)) (objMap (mor-t pf))
  homMap' (t-in-hom r) = iR r
  homMap' (t-id x) = id C
  homMap' (t-∘r {a} {b} {c} {f} {g} pf pg) = comp C (homMap' pf) {!homMap' pg!}



  homMap : {a b f : Raw} (pa : Obj a) (pb : Obj b) → 
           f ∈ a ⇒ b → hom C (objMap pa) (objMap pb)
  -- If this is the last equation, we don't get the right definitional equalities.
  homMap pa pb (t-∘r pf pg) = comp C (homMap (mor-s pf) pb pf) (homMap pa (mor-s pf) pg)
  homMap (t-in-obj a) (t-in-obj b) (t-in-hom r) = iR r
  -- Does this generalize?
  homMap {.(in-obj a)} {.(in-obj a)} (t-in-obj a) (t-in-obj .a) (t-id x) = id C

  -- NB: matching here on pa and pb instead of the withs will generate
  -- case-trees where the last case will not be a definitional
  -- equality?  (Is this a bug in Agda?)
  -- homMap pa pb (t-∘r pf pg) = comp C (homMap (mor-s pf) pb pf) (homMap pa (mor-s pf) pg)
  -- homMap (t-in-obj a) (t-in-obj b) (t-in-hom r) = iR r
  -- -- Does this generalize?

  -- homMap {.(in-obj a)} {.(in-obj a)} (t-in-obj a) (t-in-obj .a) (t-id x) = id C


  -- homMap pa pb (t-in-hom r) with pa | pb
  -- homMap pa pb (t-in-hom r) | t-in-obj a | t-in-obj b = iR r
  -- homMap pa pb (t-id x) with pa | pb 
  -- homMap pa pb (t-id x) | t-in-obj a | t-in-obj .a = id C
  -- homMap pa pb (t-∘r pf pg) = comp C (homMap (mor-s pf) pb pf) (homMap pa (mor-s pf) pg)



  ~Map   : {a b f g : Raw} {pa : Obj a} {pb : Obj b}
           {pf : f ∈ a ⇒ b} {pg : g ∈ a ⇒ b} →
           f ~ g ∈ a ⇒ b → (homMap pa pb pf) ~c (homMap pa pb pg)
  ~Map {pa = pa} {pb} {t-∘r pf1 (t-∘r pg1 ph1)} {t-∘r (t-∘r pf2 pg2) ph2} (t-∘r-assoc {a} {b} {c} {d} {f} {g} {h}) = {!!}
  ~Map {pa = pa} {pb} {pf} {pg} (t-∘r-cong pfg pfg₁) = {!!}
  ~Map {pa = pa} {pb} {pf} {pg} (t-idr-l x) = {!!}
  ~Map {pa = pa} {pb} {pf} {pg} (t-idr-r x) = {!!}
  ~Map {pa = pa} {pb} {pf} {pg} t-~-refl = {!!}
  ~Map {pa = pa} {pb} {pf} {pg} (t-~-sym pfg) = {!!}
  ~Map {pa = pa} {pb} {pf} {pg} (t-~-trans pfg pfg₁) = {!!}
