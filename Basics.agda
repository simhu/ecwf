module Basics where

open import Agda.Primitive

--------------------------------------------------------------------------------

data Unit : Set where
  tt : Unit

record Σ {l k} {A : Set l} (B : A → Set k) : Set (l ⊔ k) where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ public

infixr 10 _,_

_×_ : {l k : Level} (A : Set l) (B : Set k) → Set (l ⊔ k)
A × B = Σ {A = A} (λ _ → B)

--------------------------------------------------------------------------------

-- Equivalence Relations
record EqRel {ls lr : Level} {A : Set ls} (R : A → A → Set lr) : Set (ls ⊔ lr) where
  field
    refl  : {a : A} → R a a
    sym   : {a b : A} → R a b → R b a
    trans : {a b c : A} → R a b → R b c → R a c

open EqRel public

module EqRelReason {l l' : Level} {A : Set l} {_==_ : A → A → Set l'} (eqr : EqRel _==_) where
  infix  3 _∎
  infixr 2 _≈⟨⟩_ _≈⟨_⟩_
  infix  1 begin_

  begin_ : ∀{x y : A} → x == y → x == y
  begin_ p = p

  _≈⟨⟩_ : ∀ (x {y} : A) → x == y → x == y
  _ ≈⟨⟩ p = p

  _≈⟨_⟩_ : ∀ (x {y z} : A) → x == y → y == z → x == z
  _ ≈⟨ p ⟩ q = eqr .trans p q

  _∎ : ∀ (x : A) → x == x
  _∎ _ = eqr .refl

-- Setoids
record eSet {ls lr : Level} : Set (lsuc (ls ⊔ lr)) where
  no-eta-equality
  field
    set : Set ls
    rel : set → set → Set lr
    eqr : EqRel rel
  open EqRel eqr public

open eSet public

-- E-Categories
record ECat {lo lh lr : Level} : Set (lsuc (lo ⊔ lh ⊔ lr)) where
  no-eta-equality
  field
    obj : Set lo
    hom : obj → obj → Set lh
    hom-rel : ∀ {A B} (f g : hom A B) → Set lr
    hom-eqr : ∀ {A B} → EqRel {lh} {lr} {hom A B} hom-rel
    comp : ∀ {A B C} → hom B C → hom A B → hom A C
    comp-assoc : ∀ {A B C D} {f : hom C D} {g : hom B C} {h : hom A B} →
      hom-rel (comp f (comp g h)) (comp (comp f g) h)
    comp-cong : ∀ {A B C} {f f' : hom B C} {g g' : hom A B} → 
      hom-rel f f' → hom-rel g g' → hom-rel (comp f g) (comp f' g')
    id : ∀ {A} → hom A A
    id-l : ∀ {A B} {f : hom A B} → hom-rel (comp id f) f
    id-r : ∀ {A B} {f : hom A B} → hom-rel (comp f id) f
  comp-cong-l : ∀ {A B C} {f f' : hom B C} {g : hom A B} → 
    hom-rel f f' → hom-rel (comp f g) (comp f' g)
  comp-cong-l p = comp-cong p (hom-eqr .refl)

  comp-cong-r : ∀ {A B C} {f : hom B C} {g g' : hom A B} →
    hom-rel g g' → hom-rel (comp f g) (comp f g')
  comp-cong-r = comp-cong (hom-eqr .refl)


open ECat public

_op : ∀ {lo lh lr} → ECat {lo} {lh} {lr} → ECat
C op = record C
     { hom = λ A B → hom C B A
     ; comp = λ f g → comp C g f
     ; comp-assoc =  C .hom-eqr .sym (C .comp-assoc) 
     ; comp-cong =  λ p q → C .comp-cong q p
     ; id-l = id-r C
     ; id-r = id-l C
     }

record eMap {lao lar lbo lbr} (A : eSet {lao} {lar}) (B : eSet {lbo} {lbr}) : Set (lao ⊔ lar ⊔ lbo ⊔ lbr) where
  no-eta-equality
  field
    ap : A .set → B .set
    ap-cong : ∀ {a b} → A .rel a b → B .rel (ap a) (ap b)

open eMap public

record eMapRel {lao lar lbo lbr} {A : eSet {lao} {lar}} {B : eSet {lbo} {lbr}}
  (f g : eMap A B) : Set (lao ⊔ lar ⊔ lbo ⊔ lbr) where
  no-eta-equality
  constructor map-rel
  field
    map-resp : ∀ {a b} → A .rel a b → B .rel (f .ap a) (g .ap b)
  _`_ = map-resp
open eMapRel public

eMapEqR : {lao lar lbo lbr : Level} {A : eSet {lao} {lar}} {B : eSet {lbo} {lbr}} →
  EqRel (eMapRel {A = A} {B = B})
refl (eMapEqR {A = A} {B}) {f} = map-rel (f .ap-cong)
sym (eMapEqR {A = A} {B}) p = map-rel λ ab → B .sym (p ` (A .sym ab))
trans (eMapEqR {A = A} {B}) p q = map-rel λ r → B .trans (p ` r) (q ` (A .refl))



-- The E-Cat of E-Sets
ESet : {l : Level} → ECat {lsuc l} {l} {l}
obj (ESet {l}) = eSet {l} {l}
--hom ESet A B = Σ λ (f : A .set → B .set) → ∀ {a b} → A .rel a b → B .rel (f a) (f b)
hom ESet A B = eMap A B
-- This should really be pointwise equality instead?
--hom-rel ESet {A} {B} f g =  ∀ {a b} → A .rel a b → B .rel (f .ap a) (g .ap b)
hom-rel ESet f g = eMapRel f g
-- hom-rel ESet {A} {B} (f , _) (g , _) = ∀ (a : A .set) → B .rel (f a) (g b)
-- refl (hom-eqr ESet {A} {B}) {f} = (f .ap-cong)
-- sym (hom-eqr ESet {A} {B}) ptw pa = B .sym (ptw .map-resp (A .sym pa))
-- trans (hom-eqr ESet {A} {B}) ptw ptw' pa = B .trans (ptw pa) (ptw' (A .refl))
hom-eqr ESet = eMapEqR
comp ESet f g =  record { ap = λ x → f .ap (g .ap x) ; ap-cong = λ p →  f .ap-cong (g .ap-cong p) }
comp-assoc ESet {A} {B} {C} {D} {f} {g} {h} = map-rel λ pa → f .ap-cong (g .ap-cong (h .ap-cong pa))
comp-cong ESet p q = map-rel λ ab → p ` (q ` ab)
id ESet {A} = record { ap = λ x → x ; ap-cong = λ {_} {_} x → x }
id-l ESet {f = f} = map-rel λ ab → f .ap-cong ab
id-r ESet {f = f} = map-rel λ ab → f .ap-cong ab

ESet0 : ECat
ESet0 = ESet {lzero}


-- E-Functors
record eFunctor {lco lch lcr ldo ldh ldr : Level}
    (C : ECat {lco} {lch} {lcr}) (D : ECat {ldo} {ldh} {ldr}) : 
      Set (lco ⊔ lch ⊔ lcr ⊔ ldo ⊔ ldh ⊔ ldr) where
  no-eta-equality
  field
    fun : obj C → obj D
    mor : ∀ {a b} (f : hom C a b) → hom D (fun a) (fun b)
    resp : ∀ {a b} {f g : hom C a b} →
           hom-rel C f g → hom-rel D (mor f) (mor g)
    id-mor : ∀ {a} → hom-rel D (D .id) (mor {a} {a} (C .id))
    comp-mor : ∀ {a b c} {f : hom C b c} {g : hom C a b} → 
                 hom-rel D (comp D (mor f) (mor g)) (mor (comp C f g))

open eFunctor public



_∘Func_ : {lco lch lcr ldo ldh ldr leo leh ler : Level}
  {C : ECat {lco} {lch} {lcr}} {D : ECat {ldo} {ldh} {ldr}} {E : ECat {leo} {leh} {ler}}
  (F : eFunctor D E) (G : eFunctor C D) → eFunctor C E
_∘Func_ {C = C} {D = D} {E = E} F G = FG where
  FG : eFunctor C E
  fun FG =  λ c → fun F (fun G c)
  mor FG =  λ p → mor F (mor G p)
  resp FG = λ p → resp F (resp G p)
  id-mor FG = E .hom-eqr .trans (id-mor F) (resp F (id-mor G))
  comp-mor FG = E .hom-eqr .trans (comp-mor F) (resp F (comp-mor G))

-- E-Natural Transformations
record eNat {lco lch lcr ldo ldh ldr : Level}
    {C : ECat {lco} {lch} {lcr}} {D : ECat {ldo} {ldh} {ldr}}
    (F G : eFunctor C D) : Set (lco ⊔ lch ⊔ lcr ⊔ ldo ⊔ ldh ⊔ ldr) where
  no-eta-equality
  open ECat D using() renaming (comp to _∘D_ ; hom-rel to _~D_)
  field
    nat : (a : obj C) → hom D (fun F a) (fun G a)
    nat-eq : ∀ {a b} {f : hom C a b} →
               ((mor G f) ∘D (nat a)) ~D ((nat b) ∘D (mor F f))

open eNat public


EFunctor : {lco lch lcr ldo ldh ldr : Level}
  (C : ECat {lco} {lch} {lcr}) (D : ECat {ldo} {ldh} {ldr}) →
  ECat
EFunctor C D = cat where
  open ECat D using () renaming (comp to _∘D_ ; hom-rel to _~D_ ; hom-eqr to Deq)
  cat : ECat
  obj cat = eFunctor C D
  hom cat F G = eNat F G
  hom-rel cat α β =  ∀ a → nat α a ~D nat β a
  refl (hom-eqr cat) =  λ _ → Deq .refl
  sym (hom-eqr cat) p =  λ a → Deq .sym (p a) 
  trans (hom-eqr cat) p q =  λ a → Deq .trans (p a) (q a)
  nat (cat .comp α β) = λ a → nat α a ∘D nat β a
  nat-eq (cat .comp {F} {G} {H} α β) {a} {b} {f} = let open EqRelReason Deq in
    begin
      ((mor H f) ∘D (nat (cat .comp α β) a))
    ≈⟨  D .comp-assoc ⟩ 
      ((mor H f) ∘D (nat α a)) ∘D (nat β a)
    ≈⟨ comp-cong-l D (nat-eq α) ⟩ 
      ((nat α b) ∘D (mor G f)) ∘D (nat β a)
    ≈⟨ Deq .sym (D .comp-assoc) ⟩ 
      (nat α b) ∘D ((mor G f) ∘D (nat β a))
    ≈⟨ comp-cong-r D (nat-eq β) ⟩ 
      (nat α b) ∘D ((nat β b) ∘D (mor F f))
    ≈⟨ D .comp-assoc ⟩ 
      ((nat (cat .comp α β) b) ∘D (mor F f))
    ∎
  comp-assoc cat = λ _ → D .comp-assoc
  comp-cong cat =  λ p q a → D .comp-cong (p a) (q a)
  nat (id cat) = λ a → D .id
  nat-eq (id cat) = Deq .trans (D .id-r) (Deq .sym (D .id-l))
  id-l cat = λ _ → D .id-l
  id-r cat = λ _ → D .id-r


-- Presheaves
ePSh : ∀ {k lo lh lr} (C : ECat {lo} {lh} {lr}) → Set ((lsuc k) ⊔ lo ⊔ lh ⊔ lr)
ePSh {k} C = eFunctor (C op) (ESet {k})

EPSh : ∀ {k lo lh lr} (C : ECat {lo} {lh} {lr}) → ECat
EPSh {k} C = EFunctor (C op) (ESet {k})


-- Some notation for a presheaf
module ePShNotation {k lo lh lr} {C : ECat {lo} {lh} {lr}} (F : ePSh {k} C) where
  open ECat C public using () renaming ( comp to _∘d_ ; hom-rel to _~d_ )
  setF : obj C → Set k
  setF I = set (fun F I)
  _~_ : {I : obj C} → setF I → setF I → Set k 
  _~_ {I} = rel (fun F I)
  infixl 40 _·_
  _·_ : ∀ {I J} → setF I → hom C J I → setF J
  u · h = mor F h .ap u

-- infixl 40 _∘d_

-- The category of elements of a preasheaf
∫ : ∀ {k lo lh lr} {C : ECat {lo} {lh} {lr}} (F : ePSh {k} C) → ECat
∫ {C = C} F = cat where
  open ePShNotation {C = C} F
  cat : ECat
  obj cat = Σ setF
  hom cat (J , v) (I , u) = Σ λ (f : hom C J I) → v ~ u · f
  hom-rel cat (f , _) (g , _) = f ~d g  -- proof irrelevant in the second argument
  hom-eqr cat = record { refl =  C .hom-eqr .refl ; sym =  C .hom-eqr .sym ; trans = C .hom-eqr .trans }
  fst (comp cat (f , _) (g , _)) = f ∘d g
  snd (comp cat {(K , w)} {(J , v)} {(I , u)} (f , p) (g , q)) = 
      let gvrelfgu : v · g ~ u · (f ∘d g)
          gvrelfgu  = fun F K .trans (mor F g .ap-cong  p) (F .comp-mor ` (fun F I .refl))
      in fun F K .trans q gvrelfgu
  comp-assoc cat = C .comp-assoc
  comp-cong cat = C .comp-cong
  id cat {(I , u)}=  id C , id-mor F ` (fun F I .refl) 
  id-l cat = id-l C
  id-r cat = id-r C

-- Any setoid is a discrete category (which is also a groupoid)
# : ∀ {ls lr} (A : eSet {ls} {lr}) → ECat
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


#fun : ∀ {l} {A B} (f : hom (ESet {l}) A B) → eFunctor (# A) (# B)
fun (#fun f) = f .ap
mor (#fun f) = f .ap-cong
resp (#fun f) =  λ _ → tt
id-mor (#fun f) = tt
comp-mor (#fun f) = tt


-- #comp : ∀ {l} {A B C} (f : hom (ESet {l}) A B) (g : hom (ESet {l}) B C) →
  



--------------------------------------------------------------------------------

module eFamNotation {ls lt : Level} {A : obj (ESet {ls})} (B : eFunctor (# A) (ESet {lt})) where
  *_ : (a : A .set) → Set lt
  * a = fun B a .set 

  -- _~t_ = hom-rel (ESet {lt})
  -- _~s_ = hom-rel _

  ι : {a b : A .set} (p : A .rel a b) → * a → * b
  ι p = mor B p .ap

  -- ιirr : {a b : A .set} {p q : A .rel a b} {u v : * a} → u ~s v → ι p u ~t ι q v
  -- ιirr 

-- isInvertible : {lo lh lr : Level} (C : ECat {lo} {lh} {lr}) → Set _

-- module SomeCatLaws {lo lh lr : Level} (C : ECat {lo} {lh} {lr}) where
--   open ECat C using () renaming ( hom-rel to _~_ ; comp to _∘_ ; hom-eqr to ceq )
--   trivial-left : ∀ {a b} {f : hom C b b} {g : hom C a b} → f ~ id C → (f ∘ g) ~ g
--   trivial-left p = ceq .trans (comp-cong-l C p) (id-l C)

  
EFam : {ls : Level} → ECat
EFam {ls}  = cat where
  S = ESet {ls}
  _~s_ = S .hom-rel
  _∘s_ = S .comp
  infixl 40 _∘s_
  seq = S .hom-eqr
  cat : ECat
  obj cat = Σ λ (A : S .obj) → eFunctor (# A) S
  hom cat (A , B) (A' , B') =
    Σ λ (f : hom S A A') → eNat B (B' ∘Func (#fun {ls} {A} {A'} f))
  hom-rel cat {A , B} {A' , B'} (f , α) (g , β) =
    Σ λ (p : f ~s g) → 
    ∀ (a : A .set) → (mor B' (p ` (A .refl))) ∘s (nat α a) ~s (nat β a)

  refl (hom-eqr cat {A , B} {A' , B'}) {f , α} = seq .refl {f} , λ a → 
    let open EqRelReason seq in
    begin
      (mor B' (seq .refl {f} ` (A .refl))) ∘s (nat α a)
    ≈⟨ comp-cong-l S {g = nat α a} (resp B' tt) ⟩
      (mor B' (A' .refl)) ∘s (nat α a)
    ≈⟨ comp-cong-l S {g = nat α a} (seq .sym (id-mor B')) ⟩
      (id S) ∘s (nat α a)
    ≈⟨ id-l S ⟩
      nat α a
    ∎

  sym (hom-eqr cat {A , B} {A' , B'}) {f , α} {g , β} (p , q) = seq .sym p , λ a → 
    let open EqRelReason (seq {fun B a} {fun B' (f .ap a)})
        qai : nat β a ~s mor B' (p ` eqr A .refl) ∘s nat α a
        qai = seq .sym (q a)
        fisf : A' .rel (f .ap a) (f .ap a)
        fisf = A' .trans (p ` (A .refl)) (seq .sym p ` (A .refl))
    in 
      begin
        mor B' (seq .sym p ` (A .refl)) ∘s nat β a
      ≈⟨ comp-cong-r S {f = mor B' (seq .sym p ` A .refl)} qai ⟩
        mor B' (seq .sym p ` (A .refl)) ∘s (mor B' (p ` (A .refl)) ∘s nat α a)
      ≈⟨ comp-assoc S {f = mor B' (seq .sym p ` (A .refl))} {g = mor B' (p ` (A .refl))} {h = nat α a} ⟩ 
        (mor B' (seq .sym p ` (A .refl)) ∘s mor B' (p ` (A .refl))) ∘s nat α a
      ≈⟨ comp-cong-l S {g = nat α a} (comp-mor B') ⟩ 
        mor B' fisf ∘s nat α a
      ≈⟨ comp-cong-l S {g = nat α a} (resp B' tt) ⟩ 
        mor B' (A' .refl) ∘s nat α a
      ≈⟨ comp-cong-l S {g = nat α a} (seq .sym (id-mor B')) ⟩ 
        id S ∘s nat α a
      ≈⟨ id-r S ⟩ 
        (nat α a)
      ∎

  trans (hom-eqr cat {A , B} {A' , B'}) {f , α} {g , β} {h , γ} (fg , αβ) (gh , βγ) =
    seq .trans fg gh , λ a → 
      let open EqRelReason (seq {fun B a} {fun B' (h .ap a)}) in
      begin
        mor B' (seq .trans fg gh ` A .refl) ∘s nat α a
      ≈⟨ comp-cong-l S {g = nat α a} (seq .sym (comp-mor B')) ⟩
        (mor B' (gh ` A .refl) ∘s mor B' (fg ` A .refl)) ∘s nat α a
      ≈⟨ comp-assoc S {f = mor B' (gh ` A .refl)} {g = mor B' (fg ` A .refl)} {h = nat α a}⟩
        mor B' (gh ` A .refl) ∘s (mor B' (fg ` A .refl) ∘s nat α a)
      ≈⟨ comp-cong-r S {f = mor B' (gh ` A .refl)} (αβ a) ⟩
        mor B' (gh ` A .refl) ∘s nat β a
      ≈⟨ βγ a ⟩
        (nat γ a)
      ∎

  comp cat {A , B} {A' , B'} {A'' , B''} (f , α) (g , β) = f ∘s g , {! λ a → !}
  comp-assoc cat = {!!}
  comp-cong cat = {!!}
  id cat = {!!}
  id-l cat = {!!}
  id-r cat = {!!}

-- -}
