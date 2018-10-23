module Basics where

open import Agda.Primitive public

--------------------------------------------------------------------------------

data ⊥ {l : Level} : Set l where

data Unit {l : Level} : Set l where
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

infixr 10 _×_


--------------------------------------------------------------------------------

-- Equivalence Relations
record EqRel {ls lr : Level} {A : Set ls} (R : A → A → Set lr) : Set (ls ⊔ lr) where
  field
    refl  : {a : A} → R a a
    sym   : {a b : A} → R a b → R b a
    trans : {a b c : A} → R a b → R b c → R a c

open EqRel public

module EqRelReason {l l' : Level} {A : Set l} {_==_ : A → A → Set l'}
                   (eqr : EqRel _==_) where
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

  comp-assoc-inv : ∀ {A B C D} {f : hom C D} {g : hom B C} {h : hom A B} →
    hom-rel (comp (comp f g) h) (comp f (comp g h))
  comp-assoc-inv = hom-eqr .sym comp-assoc
  id-l-inv : ∀ {A B} {f : hom A B} → hom-rel f (comp id f)
  id-l-inv = hom-eqr .sym id-l
  id-r-inv : ∀ {A B} {f : hom A B} → hom-rel f (comp f id)
  id-r-inv = hom-eqr .sym id-r



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

-- We have to pack E-Maps into a record instead of just a Σ-type;
-- otherwise, the definition of EFam below needs too many (all)
-- implicit arguments.
record eMap {lao lar lbo lbr} (A : eSet {lao} {lar}) (B : eSet {lbo} {lbr}) :
  Set (lao ⊔ lar ⊔ lbo ⊔ lbr) where
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
ESet : {ls lr : Level} → ECat
obj (ESet {ls} {lr}) = eSet {ls} {lr}
hom ESet A B = eMap A B
hom-rel ESet f g = eMapRel f g
hom-eqr ESet = eMapEqR
comp ESet f g = record
  { ap = λ x → f .ap (g .ap x) ; ap-cong = λ p →  f .ap-cong (g .ap-cong p) }
comp-assoc ESet {f = f} {g} {h} = map-rel λ pa → f .ap-cong (g .ap-cong (h .ap-cong pa))
comp-cong ESet p q = map-rel λ ab → p ` (q ` ab)
id ESet {A} = record { ap = λ x → x ; ap-cong = λ {_} {_} x → x }
id-l ESet {f = f} = map-rel λ ab → f .ap-cong ab
id-r ESet {f = f} = map-rel λ ab → f .ap-cong ab

ESet0 : ECat
ESet0 = ESet {lzero} {lzero}


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

  comp-mor-inv : ∀ {a b c} {f : hom C b c} {g : hom C a b} →
                 hom-rel D (mor (comp C f g)) (comp D (mor f) (mor g))
  comp-mor-inv = D .hom-eqr .sym comp-mor
  id-mor-inv : ∀ {a} → hom-rel D (mor {a} {a} (C .id)) (D .id)
  id-mor-inv = D .hom-eqr .sym id-mor


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
  nat-eq-inv : ∀ {a b} {f : hom C a b} →
                 ((nat b) ∘D (mor F f)) ~D ((mor G f) ∘D (nat a))
  nat-eq-inv = D .hom-eqr .sym nat-eq

open eNat public

-- TODO: we can also consider "functors" where C is not a category,
-- but merely given by obj, hom, id, comp (but no equations)
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
    ≈⟨  comp-assoc D ⟩
      ((mor H f) ∘D (nat α a)) ∘D (nat β a)
    ≈⟨ comp-cong-l D (nat-eq α) ⟩
      ((nat α b) ∘D (mor G f)) ∘D (nat β a)
    ≈⟨ comp-assoc-inv D ⟩
      (nat α b) ∘D ((mor G f) ∘D (nat β a))
    ≈⟨ comp-cong-r D (nat-eq β) ⟩
      (nat α b) ∘D ((nat β b) ∘D (mor F f))
    ≈⟨ comp-assoc D ⟩
      ((nat (cat .comp α β) b) ∘D (mor F f))
    ∎
  comp-assoc cat = λ _ → D .comp-assoc
  comp-cong cat =  λ p q a → D .comp-cong (p a) (q a)
  nat (id cat) = λ a → D .id
  nat-eq (id cat) = Deq .trans (D .id-r) (Deq .sym (D .id-l))
  id-l cat = λ _ → D .id-l
  id-r cat = λ _ → D .id-r

idFunctor : ∀ {lco lch lcr} (C : ECat {lco} {lch} {lcr}) → eFunctor C C
fun (idFunctor C) = λ a → a
mor (idFunctor C) = λ f → f
resp (idFunctor C) = λ p → p
id-mor (idFunctor C) = C .hom-eqr .refl
comp-mor (idFunctor C) = C .hom-eqr .refl


--------------------------------------------------------------------------------
-- The initial category

𝟘 : ∀ {lo lh lr} → ECat {lo} {lh} {lr}
𝟘 = record
  { obj = ⊥
  ; hom = λ _ _ → ⊥
  ; hom-rel = λ _ _ → ⊥
  ; hom-eqr = record { refl = λ {} ; sym = λ z → z ; trans = λ _ z → z }
  ; comp = λ _ z → z
  ; comp-assoc = λ {}
  ; comp-cong = λ _ z → z
  ; id = λ {}
  ; id-l = λ {}
  ; id-r = λ {}
  }

𝟘-elim : ∀ {lo lh lr lco lch lcr} {C : ECat {lco} {lch} {lcr}} → eFunctor (𝟘 {lo} {lh} {lr}) C
𝟘-elim = record { fun = λ () ; mor = λ () ; resp = λ () ; id-mor = λ {} ; comp-mor = λ {} }

--------------------------------------------------------------------------------
-- Horizontal composition
hcomp :
  {lco lch lcr ldo ldh ldr leo leh ler : Level}
  {C : ECat {lco} {lch} {lcr}} {D : ECat {ldo} {ldh} {ldr}} {E : ECat {leo} {leh} {ler}}
  {F G : eFunctor D E} {K L : eFunctor C D}
  (α : eNat F G) (β : eNat K L) → eNat (F ∘Func K) (G ∘Func L)
hcomp {C = C} {D} {E} {F} {G} {K} {L} α β = record
  { nat = λ (a : obj C) → comp E (mor G (nat β a)) (nat α (fun K a))
  ; nat-eq =  λ {a b f} →
    let eeq = hom-eqr E
        _∘E_ = comp E
        _∘D_ = comp D
        open EqRelReason eeq
    in
      begin
        (mor G (mor L f)) ∘E ((mor G (nat β a)) ∘E (nat α (fun K a)))
      ≈⟨ comp-assoc E ⟩
        ((mor G (mor L f)) ∘E (mor G (nat β a))) ∘E (nat α (fun K a))
      ≈⟨ comp-cong-l E (comp-mor G) ⟩
        (mor G (mor L f ∘D nat β a)) ∘E (nat α (fun K a))
      ≈⟨ comp-cong-l E (resp G (nat-eq β)) ⟩
        (mor G (nat β b ∘D mor K f)) ∘E (nat α (fun K a))
      ≈⟨ comp-cong-l E (eeq .sym (comp-mor G)) ⟩
        (mor G (nat β b) ∘E mor G (mor K f)) ∘E (nat α (fun K a))
      ≈⟨ comp-assoc-inv E ⟩
        mor G (nat β b) ∘E (mor G (mor K f) ∘E (nat α (fun K a)))
      ≈⟨ comp-cong-r E (nat-eq α) ⟩
        mor G (nat β b) ∘E (nat α (fun K b) ∘E mor F (mor K f))
      ≈⟨ comp-assoc E ⟩
         ((mor G (nat β b)) ∘E (nat α (fun K b))) ∘E (mor F (mor K f))
      ∎
  }

_*_ = hcomp

r-whisker :
  {lco lch lcr ldo ldh ldr leo leh ler : Level}
  {C : ECat {lco} {lch} {lcr}} {D : ECat {ldo} {ldh} {ldr}} {E : ECat {leo} {leh} {ler}}
  {F G : eFunctor D E}
  (α : eNat F G) (H : eFunctor C D) → eNat (F ∘Func H) (G ∘Func H)
r-whisker α H = α * (id (EFunctor _ _) {H})

l-whisker :
  {lco lch lcr ldo ldh ldr leo leh ler : Level}
  {C : ECat {lco} {lch} {lcr}} {D : ECat {ldo} {ldh} {ldr}} {E : ECat {leo} {leh} {ler}}
  {G H : eFunctor C D}
  (F : eFunctor D E) (α : eNat G H) → eNat (F ∘Func G) (F ∘Func H)
l-whisker F α = hcomp (id (EFunctor _ _) {F}) α






--------------------------------------------------------------------------------

-- Isomorphisms in a given category
module IsoModule {lo lh lr : Level} {C : ECat {lo} {lh} {lr}} where
  open ECat C using () renaming (comp to _∘C_ ; hom-rel to _~C_ ; hom-eqr to Ceq)

  record isIso {a b : obj C}
    (f : hom C a b) : Set (lh ⊔ lr) where
    no-eta-equality
    field
      inverse : hom C b a
      inverse-section : (f ∘C inverse) ~C id C
      inverse-retract : (inverse ∘C f) ~C id C

  open isIso public

  record Iso (a b : obj C) : Set (lh ⊔ lr) where
    no-eta-equality
    field
      to-mor : hom C a b
      to-mor-iso : isIso to-mor
    open isIso to-mor-iso public renaming
      ( inverse to from-mor
      ; inverse-section to to-from-id
      ; inverse-retract to from-to-id
      )
  open Iso public

  isiso-id : {a : obj C} → isIso (id C {a})
  isiso-id = record { inverse =  id C ; inverse-section = id-r C ; inverse-retract = id-r C }


  isiso-inv : {a b : obj C} {f : hom C a b} (pf : isIso f) → isIso (pf .inverse)
  isiso-inv {f = f} pf = record
    { inverse = f
    ; inverse-section = inverse-retract pf
    ; inverse-retract = inverse-section pf
    }

  isiso-comp : {a b c : obj C} {f : hom C b c} {g : hom C a b} → isIso f → isIso g → isIso (f ∘C g)
  isiso-comp {f = f} {g = g} pf pg = record
    { inverse =  pg .inverse ∘C  pf .inverse
    ; inverse-section = let open EqRelReason Ceq in
      begin
        (f ∘C g) ∘C (pg .inverse ∘C pf .inverse)
      ≈⟨ comp-assoc-inv C ⟩
        f ∘C (g ∘C (pg .inverse ∘C pf .inverse))
      ≈⟨ comp-cong-r C (comp-assoc C) ⟩
        f ∘C ((g ∘C pg .inverse) ∘C pf .inverse)
      ≈⟨ comp-cong-r C (comp-cong-l C (pg .inverse-section)) ⟩
        f ∘C (id C ∘C pf .inverse)
      ≈⟨ comp-cong-r C (id-l C) ⟩
        f ∘C pf .inverse
      ≈⟨ pf .inverse-section ⟩
        id C
      ∎
    ; inverse-retract = let open EqRelReason Ceq in
      begin
        (pg .inverse ∘C pf .inverse) ∘C (f ∘C g)
      ≈⟨ comp-assoc-inv C ⟩
        pg .inverse ∘C (pf .inverse ∘C (f ∘C g))
      ≈⟨ comp-cong-r C (comp-assoc C) ⟩
        pg .inverse ∘C ((pf .inverse ∘C f) ∘C g)
      ≈⟨ comp-cong-r C (comp-cong-l C (pf .inverse-retract)) ⟩
        pg .inverse ∘C (id C ∘C g)
      ≈⟨ comp-cong-r C (id-l C) ⟩
        pg .inverse ∘C g
      ≈⟨ pg .inverse-retract ⟩
        id C
      ∎
    }

  iso-refl : {a : obj C} → Iso a a
  iso-refl = record { to-mor = id C  ; to-mor-iso = isiso-id}

  iso-sym : {a b : obj C} → Iso a b → Iso b a
  iso-sym iso = record { to-mor = from-mor iso ; to-mor-iso = isiso-inv (to-mor-iso iso) }

  iso-trans : {a b c : obj C} → Iso a b → Iso b c → Iso a c
  iso-trans pf pg = record
    { to-mor = to-mor pg ∘C to-mor pf
    ; to-mor-iso = isiso-comp (to-mor-iso pg) (to-mor-iso pf)
    }

  --  iso-comp : {lo lh lr : Level} {C : ECat {lo} {lh} {lr}} {a b c: obj C} {f : }
open IsoModule public

-- Natural isomorphism
module eNatIsoModule
         {lco lch lcr ldo ldh ldr : Level}
         {C : ECat {lco} {lch} {lcr}} {D : ECat {ldo} {ldh} {ldr}}
         {F G : eFunctor C D} where

  open ECat C using() renaming (comp to _∘C_ ; hom-rel to _~C_)
  open ECat D using() renaming (comp to _∘D_ ; hom-rel to _~D_ ; hom-eqr to deq)

  record isNatIso (α : eNat F G) : Set (lco ⊔ lch ⊔ lcr ⊔ ldo ⊔ ldh ⊔ ldr) where
    no-eta-equality
    field
      nat-inv : (a : obj C) → hom D (fun G a) (fun F a)
      nat-inv-sect : ∀ {a} → (nat α a ∘D nat-inv a) ~D id D
      nat-inv-retract : ∀ {a} → (nat-inv a ∘D nat α a) ~D id D

  isnatiso-inv : ∀ {α} → isNatIso α → eNat G F
  isnatiso-inv {α} p = let open isNatIso p in record
    { nat = nat-inv
    ; nat-eq = λ {a b f} → let open EqRelReason deq in
      begin
        mor F f ∘D nat-inv a
      ≈⟨ comp-cong-l D (id-l-inv D) ⟩
        (id D ∘D mor F f) ∘D nat-inv a
      ≈⟨ comp-cong-l D (comp-cong-l D (deq .sym nat-inv-retract)) ⟩
        ((nat-inv b ∘D nat α b) ∘D mor F f) ∘D nat-inv a
      ≈⟨ comp-cong-l D (comp-assoc-inv D) ⟩
        (nat-inv b ∘D (nat α b ∘D mor F f)) ∘D nat-inv a
      ≈⟨ comp-cong-l D (comp-cong-r D (deq .sym (nat-eq α))) ⟩
        (nat-inv b ∘D (mor G f ∘D nat α a)) ∘D nat-inv a
      ≈⟨ comp-assoc-inv D ⟩
        nat-inv b ∘D ((mor G f ∘D nat α a) ∘D nat-inv a)
      ≈⟨ comp-cong-r D (comp-assoc-inv D) ⟩
        nat-inv b ∘D (mor G f ∘D (nat α a ∘D nat-inv a))
      ≈⟨ comp-cong-r D (comp-cong-r D (nat-inv-sect)) ⟩
        nat-inv b ∘D (mor G f ∘D id D)
      ≈⟨ comp-cong-r D (id-r D) ⟩
        nat-inv b ∘D mor G f
      ∎
    }

  isnatiso-iso : ∀ {α} → isNatIso α → isIso {C = EFunctor C D} α
  isnatiso-iso {α} p = let open isNatIso p in record
    { inverse = isnatiso-inv p
    ; inverse-section = λ a → nat-inv-sect {a}
    ; inverse-retract = λ a → nat-inv-retract {a}
    }

  iso-isnatiso : ∀ {α} → isIso {C = EFunctor C D} α → isNatIso α
  iso-isnatiso p = record { nat-inv =  λ a → nat (inverse p) a
                          ; nat-inv-sect = p .inverse-section _
                          ; nat-inv-retract = p .inverse-retract _
                          }
  record eNatIso : Set (lco ⊔ lch ⊔ lcr ⊔ ldo ⊔ ldh ⊔ ldr) where
    no-eta-equality
    field
      to-nat : eNat F G
      to-is-iso : isNatIso to-nat
    open isNatIso to-is-iso public renaming
      ( nat-inv to from-nat
      ; nat-inv-sect to ptw-to-from-id
      ; nat-inv-retract to ptw-from-to-id
      )
  open eNatIso public

  iso-natiso : Iso {C = EFunctor C D} F G → eNatIso
  iso-natiso p = record { to-nat = to-mor p ; to-is-iso = iso-isnatiso (to-mor-iso p) }

  natiso-iso : eNatIso → Iso {C = EFunctor C D} F G
  natiso-iso p = record { to-mor = to-nat p ; to-mor-iso = isnatiso-iso (to-is-iso p) }


eNatIso : {lco lch lcr ldo ldh ldr : Level}
          {C : ECat {lco} {lch} {lcr}} {D : ECat {ldo} {ldh} {ldr}}
          (F G : eFunctor C D) → Set _
eNatIso F G = eNatIsoModule.eNatIso {F = F} {G = G}


open eNatIsoModule public hiding ( eNatIso )


∘Func-assoc : {lbo lbh lbr lco lch lcr ldo ldh ldr leo leh ler : Level}
  {B : ECat {lbo} {lbh} {lbr}} {C : ECat {lco} {lch} {lcr}}
  {D : ECat {ldo} {ldh} {ldr}} {E : ECat {leo} {leh} {ler}}
  (F : eFunctor D E) (G : eFunctor C D) (H : eFunctor B C) →
  eNatIso (F ∘Func (G ∘Func H)) ((F ∘Func G) ∘Func H)
∘Func-assoc {B = B} {C} {D} {E} F G H =
  let eta : eNatIso ((F ∘Func G) ∘Func H) ((F ∘Func G) ∘Func H)
      eta = iso-natiso iso-refl
  in record  -- no-eta isn't really our friend here
  { to-nat = record
    { nat = eta .to-nat .nat
    ; nat-eq = eta .to-nat .nat-eq }
  ; to-is-iso = record { nat-inv = eta .to-is-iso .isNatIso.nat-inv
                       ; nat-inv-sect = eta .to-is-iso .isNatIso.nat-inv-sect
                       ; nat-inv-retract = eta .to-is-iso .isNatIso.nat-inv-retract
                       }
  }

idFunctor-l : ∀ {lco lch lcr ldo ldh ldr} {C : ECat {lco} {lch} {lcr}} {D : ECat {ldo} {ldh} {ldr}}
              {F : eFunctor C D} → eNatIso (idFunctor D ∘Func F) F
idFunctor-l {C = C} {D} {F} =
  let eta : eNatIso F F
      eta = iso-natiso iso-refl
  in record  -- no-eta isn't really our friend here
  { to-nat = record
    { nat = eta .to-nat .nat
    ; nat-eq = eta .to-nat .nat-eq }
  ; to-is-iso = record { nat-inv = eta .to-is-iso .isNatIso.nat-inv
                       ; nat-inv-sect = eta .to-is-iso .isNatIso.nat-inv-sect
                       ; nat-inv-retract = eta .to-is-iso .isNatIso.nat-inv-retract
                       }
  }

idFunctor-r : ∀ {lco lch lcr ldo ldh ldr} {C : ECat {lco} {lch} {lcr}} {D : ECat {ldo} {ldh} {ldr}}
              {F : eFunctor C D} → eNatIso (F ∘Func idFunctor C) F
idFunctor-r {C = C} {D} {F} =
  let eta : eNatIso F F
      eta = iso-natiso iso-refl
  in record  -- no-eta isn't really our friend here
  { to-nat = record
    { nat = eta .to-nat .nat
    ; nat-eq = eta .to-nat .nat-eq }
  ; to-is-iso = record { nat-inv = eta .to-is-iso .isNatIso.nat-inv
                       ; nat-inv-sect = eta .to-is-iso .isNatIso.nat-inv-sect
                       ; nat-inv-retract = eta .to-is-iso .isNatIso.nat-inv-retract
                       }
  }

∘Func-cong : {lco lch lcr ldo ldh ldr leo leh ler : Level}
  {C : ECat {lco} {lch} {lcr}} {D : ECat {ldo} {ldh} {ldr}} {E : ECat {leo} {leh} {ler}}
  {F F' : eFunctor D E} {G G' : eFunctor C D} {α : eNat F F'} {β : eNat G G'} →
  isNatIso α → isNatIso β → isNatIso (hcomp α β)
∘Func-cong {C = C} {D} {E} {F} {F'} {G} {G'} {α} {β} isoα isoβ =
  let open ECat E using() renaming (comp to _∘E_ ; hom-rel to _~E_ ; hom-eqr to Eqr )
      open isNatIso isoα using () renaming
        (nat-inv to invα ; nat-inv-sect to αinvα ; nat-inv-retract to invαα)
      open isNatIso isoβ using () renaming
        (nat-inv to invβ ; nat-inv-sect to βinvβ ; nat-inv-retract to invββ)
  in record
  { nat-inv = λ a → mor F (invβ a) ∘E invα (fun G' a)
  ; nat-inv-sect =
    λ {a} → let open EqRelReason Eqr in
    begin
      (mor F' (nat β a) ∘E nat α (fun G a)) ∘E (mor F (invβ a) ∘E invα (fun G' a))
    ≈⟨ comp-assoc E ⟩
      ((mor F' (nat β a) ∘E nat α (fun G a)) ∘E mor F (invβ a)) ∘E invα (fun G' a)
    ≈⟨ comp-cong-l E (comp-assoc-inv E) ⟩
      (mor F' (nat β a) ∘E (nat α (fun G a) ∘E (mor F (invβ a)))) ∘E invα (fun G' a)
    ≈⟨ comp-cong-l E (comp-cong-r E (nat-eq-inv α)) ⟩
      (mor F' (nat β a) ∘E (mor F' (invβ a) ∘E nat α (fun G' a))) ∘E invα (fun G' a)
    ≈⟨ comp-cong-l E (comp-assoc E) ⟩
      ((mor F' (nat β a) ∘E mor F' (invβ a)) ∘E nat α (fun G' a)) ∘E invα (fun G' a)
    ≈⟨ comp-assoc-inv E ⟩
      (mor F' (nat β a) ∘E mor F' (invβ a)) ∘E ((nat α (fun G' a)) ∘E invα (fun G' a))
    ≈⟨ comp-cong E (comp-mor F') αinvα ⟩
      mor F' (comp D (nat β a) (invβ a)) ∘E id E
    ≈⟨ id-r E ⟩
      mor F' (comp D (nat β a) (invβ a))
    ≈⟨ resp F' βinvβ ⟩
      mor F' (id D)
    ≈⟨ id-mor-inv F' ⟩
      id E
    ∎
  ; nat-inv-retract =
    λ {a} → let open EqRelReason Eqr in
    begin
      (mor F (invβ a) ∘E invα (fun G' a)) ∘E (mor F' (nat β a) ∘E nat α (fun G a))
    ≈⟨ comp-assoc E ⟩
      ((mor F (invβ a) ∘E invα (fun G' a)) ∘E mor F' (nat β a)) ∘E nat α (fun G a)
    ≈⟨ comp-cong-l E (comp-assoc-inv E) ⟩
      (mor F (invβ a) ∘E (invα (fun G' a) ∘E (mor F' (nat β a)))) ∘E nat α (fun G a)
    ≈⟨ comp-cong-l E (comp-cong-r E (nat-eq-inv (isnatiso-inv isoα))) ⟩
      (mor F (invβ a) ∘E (mor F (nat β a) ∘E invα (fun G a))) ∘E nat α (fun G a)
    ≈⟨ comp-cong-l E (comp-assoc E) ⟩
      ((mor F (invβ a) ∘E mor F (nat β a)) ∘E invα (fun G a)) ∘E nat α (fun G a)
    ≈⟨ comp-assoc-inv E ⟩
      (mor F (invβ a) ∘E mor F (nat β a)) ∘E ((invα (fun G a)) ∘E nat α (fun G a))
    ≈⟨ comp-cong E (comp-mor F) invαα ⟩
      mor F (comp D (invβ a) (nat β a)) ∘E id E
    ≈⟨ id-r E ⟩
      mor F (comp D (invβ a) (nat β a))
    ≈⟨ resp F invββ ⟩
      mor F (id D)
    ≈⟨ id-mor-inv F ⟩
      id E
    ∎
  }



-- The categories of categories with equality of functors being
-- natural isomorphism
CAT : {lo lh lr : Level} → ECat
CAT {lo} {lh} {lr} = record
  { obj = ECat {lo} {lh} {lr}
  ; hom = eFunctor
  ; hom-rel = eNatIso
  ; hom-eqr = record { refl = iso-natiso iso-refl
                     ; sym = λ α → iso-natiso (iso-sym (natiso-iso α))
                     ; trans = λ α β →
                       iso-natiso (iso-trans (natiso-iso α) (natiso-iso β))
                     }
  ; comp = _∘Func_
  ; comp-assoc = λ { {f = F} {G} {H} → ∘Func-assoc F G H }
  ; comp-cong = λ pα pβ → record { to-nat = hcomp (to-nat pα) (to-nat pβ)
                                  ; to-is-iso = ∘Func-cong (to-is-iso pα) (to-is-iso pβ) }
  ; id = idFunctor _
  ; id-l = idFunctor-l
  ; id-r = idFunctor-r
  }


--------------------------------------------------------------------------------

-- The terminal category

1cat : {lo lh lr : Level} → ECat {lo} {lh} {lr}
1cat = record
     { obj = Unit
     ; hom = λ { _ _ → Unit }
     ; hom-rel =  λ { _ _ → Unit }
     ; hom-eqr = record { refl = tt ; sym = λ _ → tt ; trans = λ _ _ → tt }
     ; comp = λ _ _ → tt
     ; comp-assoc = tt
     ; comp-cong = λ _ _ → tt
     ; id = tt
     ; id-l = tt
     ; id-r = tt
     }

1cat0 = 1cat {lzero} {lzero} {lzero}

!cat : {lo lh lr lco lch lcr : Level} (C : ECat {lco} {lch} {lcr}) → eFunctor C (1cat {lo} {lh} {lr})
!cat C = record { fun = λ _ → tt ; mor = λ _ → tt ; resp = λ _ → tt ; id-mor = tt ; comp-mor = tt }

!cat0 = !cat {lzero} {lzero} {lzero}

-- Uniqueness of !cat up to unique natural isomorphism
!cat-unique : {lo lh lr lco lch lcr : Level} {C : ECat {lco} {lch} {lcr}}
              {F G : eFunctor C (1cat {lo} {lh} {lr})} → eNatIso F G
!cat-unique = record
                { to-nat = record { nat = λ _ → tt ; nat-eq = tt }
                ; to-is-iso =
                    record
                    { nat-inv = λ _ → tt
                    ; nat-inv-sect = tt
                    ; nat-inv-retract = tt
                    }
                }

!cat-unique-nat : {lo lh lr lco lch lcr : Level} {C : ECat {lco} {lch} {lcr}}
                  {F G : eFunctor C (1cat {lo} {lh} {lr})} {α β : eNatIso F G} →
                  hom-rel (EFunctor C 1cat) (to-nat α) (to-nat β)
!cat-unique-nat a = tt




-- -}
