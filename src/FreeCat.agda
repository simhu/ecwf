-- The free e-category on a graph.
module FreeCat {ls lr} (A : Set ls) (R : A → A → Set lr) where

open import Basics


-- The free category on a graph.

data Obj : Set ls where
  in-obj : A → Obj

data Raw : Set (ls ⊔ lr) where
  -- Morphisms
  in-hom : {a b : A} (r : R a b) → Raw
  idr : Raw
  compr : Obj → Raw → Raw → Raw

data _∈_⇒_ : (f : Raw) → Obj → Obj → Set (ls ⊔ lr)
data _~_∈_⇒_ : (f g : Raw) → Obj → Obj → Set (ls ⊔ lr)

data _∈_⇒_ where
  t-in-hom : {a b : A} (r : R a b) → (in-hom r) ∈ (in-obj a) ⇒ (in-obj b)
  t-id : ∀ (a : Obj) → idr ∈ a ⇒ a
  t-compr : ∀ {f g a b c} → f ∈ b ⇒ c → g ∈ a ⇒ b → (compr b f g) ∈ a ⇒ c

data _~_∈_⇒_ where
  t-compr-assoc : ∀ {a b c d f g h} {p : f ∈ c ⇒ d} {q : g ∈ b ⇒ c} {r : h ∈ a ⇒ b} →
    compr c f (compr b g h) ~ compr b (compr c f g) h ∈ a ⇒ d
  t-compr-cong : ∀ {a b c f f' g g'}
                {p : f ∈ b ⇒ c} {q : f' ∈ b ⇒ c} {r : g ∈ a ⇒ b} {s : g' ∈ a ⇒ b} →
                f ~ f' ∈ b ⇒ c → g ~ g' ∈ a ⇒ b → compr b f g ~ compr b f' g' ∈ a ⇒ c
  t-idr-l : ∀ {a b f} → f ∈ a ⇒ b → compr b idr f ~ f ∈ a ⇒ b
  t-idr-r : ∀ {a b f} → f ∈ a ⇒ b → compr a f idr ~ f ∈ a ⇒ b

  t-~-refl : ∀ {a b f} → {p : f ∈ a ⇒ b} → f ~ f ∈ a ⇒ b
  t-~-sym  : ∀ {a b f g} → f ~ g ∈ a ⇒ b  → g ~ f ∈ a ⇒ b
  t-~-trans  : ∀ {a b f g h} → f ~ g ∈ a ⇒ b → g ~ h ∈ a ⇒ b → f ~ h ∈ a ⇒ b

freeCat : ECat
obj freeCat = Obj
hom freeCat a b = Σ λ (f : Raw) → f ∈ a ⇒ b
hom-rel freeCat {a} {b} (f , _) (g , _) = f ~ g ∈ a ⇒ b
hom-eqr freeCat = record
  { refl = λ {a} → t-~-refl {p = snd a} ; sym = t-~-sym ; trans = t-~-trans }
comp freeCat (f , p) (g , q) = compr _ f g , t-compr p q
comp-assoc freeCat {f = f} {g} {h} = t-compr-assoc {p = snd f} {snd g} {snd h}
comp-cong freeCat {f = f} {f'} {g} {g'} = t-compr-cong {p = snd f} {snd f'} {snd g} {snd g'}
id freeCat {p} = idr , t-id p
id-l freeCat {f = f} = t-idr-l (snd f)
id-r freeCat {f = f} = t-idr-r (snd f)

~-l : ∀ {a b f g} → f ~ g ∈ a ⇒ b → f ∈ a ⇒ b
~-r : ∀ {a b f g} → f ~ g ∈ a ⇒ b → g ∈ a ⇒ b

~-l (t-compr-assoc {p = p} {q} {r}) = t-compr p (t-compr q r)
~-l (t-compr-cong ff' gg') = t-compr (~-l ff') (~-l gg')
~-l (t-idr-l pf) = t-compr (t-id _) pf
~-l (t-idr-r pf) = t-compr pf (t-id _)
~-l (t-~-refl {p = p})= p
~-l (t-~-sym p) = ~-r p
~-l (t-~-trans p q) = ~-l p

~-r (t-compr-assoc {p = p} {q} {r}) = t-compr (t-compr p q) r
~-r (t-compr-cong ff' gg') = t-compr (~-r ff') (~-r gg')
~-r (t-idr-l pf) = pf
~-r (t-idr-r pf) = pf
~-r (t-~-refl {p = p}) = p
~-r (t-~-sym p) = ~-l p
~-r (t-~-trans p q) = ~-r q


module FreeElim {lo lh lr} (C : ECat {lo} {lh} {lr})
           (iA : A → obj C) (iR : {a b : A} → R a b → hom C (iA a) (iA b)) where
  open ECat C using () renaming (comp to _∘c_ ; hom-rel to _~c_ ; hom-eqr to ceq )
  -- TODO: How do we get this fixity declaration to work?
  -- infixl 40 _∘c_

  objMap : Obj → obj C
  objMap (in-obj a) = iA a

  homMap : {a b : Obj} {f : Raw}
           (pf : f ∈ a ⇒ b) → hom C (objMap a) (objMap b)
  homMap (t-in-hom r) = iR r
  homMap (t-id a) = id C
  homMap (t-compr pf pg) = homMap pf ∘c homMap pg

  homMapIrr : {a b : Obj} {f : Raw} (pf0 pf1 : f ∈ a ⇒ b) →
              homMap pf0 ~c homMap pf1
  homMapIrr (t-in-hom r) (t-in-hom .r) = ceq .refl
  homMapIrr (t-id a) (t-id .a) = ceq .refl
  homMapIrr (t-compr pf0 pg0) (t-compr pf1 pg1) = comp-cong C (homMapIrr pf0 pf1) (homMapIrr pg0 pg1)

  -- NB: reordeing the cases gives a better case-tree; this is really
  -- weird and it seems to me Agda should look for the "best"
  -- case-tree from the beginning (if there is an optimal one)?
  ~Map : {a b : Obj} {f g : Raw} (pf : f ∈ a ⇒ b) (pg : g ∈ a ⇒ b) →
           f ~ g ∈ a ⇒ b → homMap pf ~c homMap pg
  ~Map pf pg t-~-refl = homMapIrr pf pg
  ~Map pf pg (t-~-sym pfg) = ceq .sym (~Map pg pf pfg)
  ~Map pf ph (t-~-trans {a} {b} {f} {g} {h} pfg pgh) =
    let pg0 : g ∈ a ⇒ b
        pg0 = ~-r pfg
        pg1 : g ∈ a ⇒ b
        pg1 = ~-l pgh
        open EqRelReason ceq
    in begin
       homMap pf
     ≈⟨ ~Map pf pg0 pfg ⟩
       homMap pg0
     ≈⟨ homMapIrr pg0 pg1 ⟩
       homMap pg1
     ≈⟨ ~Map pg1 ph pgh ⟩
       homMap ph
     ∎
  ~Map (t-compr pf0 (t-compr pg0 ph0)) (t-compr (t-compr pf1 pg1) ph1) t-compr-assoc =
    let open EqRelReason ceq in
      begin
        homMap pf0 ∘c (homMap pg0 ∘c homMap ph0)
      ≈⟨ comp-assoc C ⟩
        (homMap pf0 ∘c homMap pg0) ∘c homMap ph0
      ≈⟨ comp-cong C (comp-cong C (homMapIrr pf0 pf1) (homMapIrr pg0 pg1)) (homMapIrr ph0 ph1) ⟩
        (homMap pf1 ∘c homMap pg1) ∘c homMap ph1
      ∎
  ~Map (t-compr pf0 pg0) (t-compr pf1 pg1) (t-compr-cong pf01 pg01) =
    comp-cong C (~Map pf0 pf1 pf01) (~Map pg0 pg1 pg01)
  ~Map (t-compr (t-id a) pf0) pf1 (t-idr-l x) =
    let open EqRelReason ceq in
      begin
        id C ∘c homMap pf0
      ≈⟨ id-l C ⟩
        homMap pf0
      ≈⟨ homMapIrr pf0 pf1 ⟩
        homMap pf1
      ∎

  ~Map (t-compr pf0 (t-id a)) pf1 (t-idr-r x) =
    let open EqRelReason ceq in
      begin
        homMap pf0 ∘c id C
      ≈⟨ id-r C ⟩
        homMap pf0
      ≈⟨ homMapIrr pf0 pf1 ⟩
        homMap pf1
      ∎

  free-elim : eFunctor freeCat C
  free-elim = record
    { fun = objMap
    ; mor = λ {(f , pf) → homMap pf}
    ; resp = λ {a} {b} {f} {g} p → ~Map (snd f) (snd g) p
    ; id-mor = ceq .refl
    ; comp-mor = ceq .refl
    }


  -- This is formulated rather cumbersome, due to the fact that we
  -- formulated functors not general enough; the problem is that
  -- graphs (gadgets (A,R) as above) don't naturally form a category
  -- as there is no natural way to formulate equality of morphisms.
  module FreeElimUnique
           (F : eFunctor freeCat C)
           (eA : (a : A) → Iso {C = C} (iA a) (fun F (in-obj a)))
           (eA-to-nat : ∀ {a b} (r : R a b) → (mor F (in-hom r , t-in-hom r) ∘c eA a .to-mor)
                                              ~c (eA b .to-mor ∘c iR r))
    where

    fwd-nat : (a : Obj) → hom C (fun free-elim a) (fun F a)
    fwd-nat (in-obj a) = eA a .to-mor

    fwd-nat-eq : {a b : Obj} {f : Raw} (pf : f ∈ a ⇒ b) →
                 (mor F (f , pf) ∘c fwd-nat a) ~c (fwd-nat b ∘c (homMap pf))
    fwd-nat-eq (t-in-hom {a} {b} r) = eA-to-nat r
    fwd-nat-eq (t-id a) = let open EqRelReason ceq in
      begin
        mor F (id freeCat) ∘c fwd-nat a
      ≈⟨ comp-cong-l C (id-mor-inv F) ⟩
        id C ∘c fwd-nat a
      ≈⟨ id-l C ⟩
        fwd-nat a
      ≈⟨ id-r-inv C ⟩
        fwd-nat a ∘c id C
      ∎
    fwd-nat-eq (t-compr {f} {g} {a} {b} {c} pf pg) = let open EqRelReason ceq in
      begin
        mor F (compr _ f g , t-compr pf pg) ∘c fwd-nat a
      ≈⟨ comp-cong-l C (comp-mor-inv F) ⟩
        (mor F (f , pf) ∘c mor F (g , pg))∘c fwd-nat a
      ≈⟨ comp-assoc-inv C ⟩
        mor F (f , pf) ∘c (mor F (g , pg)∘c fwd-nat a)
      ≈⟨ comp-cong-r C (fwd-nat-eq pg) ⟩ -- IH g
        mor F (f , pf) ∘c (fwd-nat b ∘c homMap pg)
      ≈⟨ comp-assoc C ⟩
        (mor F (f , pf) ∘c fwd-nat b) ∘c homMap pg
      ≈⟨ comp-cong-l C (fwd-nat-eq pf) ⟩ -- IH f
        (fwd-nat c ∘c homMap pf) ∘c homMap pg
      ≈⟨ comp-assoc-inv C ⟩
        fwd-nat c ∘c (homMap pf ∘c homMap pg)
      ∎

    bwd-nat : (a : Obj) → hom C (fun F a) (objMap a)
    bwd-nat (in-obj a) = eA a .from-mor

    fwd-bwd-id : (a : Obj) → (fwd-nat a ∘c bwd-nat a) ~c id C
    fwd-bwd-id (in-obj a) = eA a .to-from-id

    bwd-fwd-id : (a : Obj) → (bwd-nat a ∘c fwd-nat a) ~c id C
    bwd-fwd-id (in-obj a) = eA a .from-to-id

    -- This should not be neccessary if we'd used more general
    -- definitions of functors and natural transformations.  This is
    -- copy-paste from isnatiso-inv from Basics.
    bwd-nat-eq : {a b : Obj} {f : Raw} (pf : f ∈ a ⇒ b) →
                 (homMap pf ∘c bwd-nat a) ~c (bwd-nat b ∘c mor F (f , pf))
    bwd-nat-eq {a} {b} {f} pf = let open EqRelReason ceq in
      begin
        homMap pf ∘c bwd-nat a
      ≈⟨ comp-cong-l C (id-l-inv C) ⟩
        (id C ∘c homMap pf) ∘c bwd-nat a
      ≈⟨ comp-cong-l C (comp-cong-l C (ceq .sym (bwd-fwd-id b))) ⟩
        ((bwd-nat b ∘c fwd-nat b) ∘c homMap pf) ∘c bwd-nat a
      ≈⟨ comp-cong-l C (comp-assoc-inv C) ⟩
        (bwd-nat b ∘c (fwd-nat b ∘c homMap pf)) ∘c bwd-nat a
      ≈⟨ comp-cong-l C (comp-cong-r C (ceq .sym (fwd-nat-eq pf))) ⟩
        (bwd-nat b ∘c (mor F (f , pf) ∘c fwd-nat a)) ∘c bwd-nat a
      ≈⟨ comp-assoc-inv C ⟩
        bwd-nat b ∘c ((mor F (f , pf) ∘c fwd-nat a) ∘c bwd-nat a)
      ≈⟨ comp-cong-r C (comp-assoc-inv C) ⟩
        bwd-nat b ∘c (mor F (f , pf) ∘c (fwd-nat a ∘c bwd-nat a))
      ≈⟨ comp-cong-r C (comp-cong-r C (fwd-bwd-id a)) ⟩
        bwd-nat b ∘c (mor F (f , pf) ∘c id C)
      ≈⟨ comp-cong-r C (id-r C) ⟩
        bwd-nat b ∘c mor F (f , pf)
      ∎

    free-elim-unique : eNatIso free-elim F
    free-elim-unique = record
      { to-nat = record { nat = fwd-nat
                        ; nat-eq = λ {a} {b} {fpf} → fwd-nat-eq (snd fpf) }
      ; to-is-iso = record
        { nat-inv = bwd-nat
        ; nat-inv-sect = λ {a} → fwd-bwd-id a
        ; nat-inv-retract = λ {a} → bwd-fwd-id a
        }
      }
  open FreeElimUnique public using ( free-elim-unique )

open FreeElim public
