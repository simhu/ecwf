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
-- TODO: this should really take two universe levels...
ESet : {l : Level} → ECat {lsuc l} {l} {l}
obj (ESet {l}) = eSet {l} {l}
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


-- Horizontal composition (not used at the moment)
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


-- Any setoid is a discrete category (which is also a groupoid)
# : ∀ {ls lr} (A : eSet {ls} {lr}) → ECat
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



--------------------------------------------------------------------------------

isTerminal : ∀ {l l' l''} {C : ECat {l} {l'} {l''}} (T : obj C) → Set (l ⊔ (l' ⊔ l''))
isTerminal {C = C} T = ∀ A → Σ λ (f : hom C A T) → ∀ g → hom-rel C f g


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

  record eNatIso : Set (lco ⊔ lch ⊔ lcr ⊔ ldo ⊔ ldh ⊔ ldr) where
    no-eta-equality
    field
      to-nat : eNat F G
      to-is-iso : isNatIso to-nat

  open eNatIso public

open eNatIsoModule public



-- -}
