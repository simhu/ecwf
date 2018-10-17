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

-- The category of elements of a preasheaf
∫ : ∀ {k lo lh lr} {C : ECat {lo} {lh} {lr}} (F : ePSh {k} C) → ECat
∫ {C = C} F = cat where
  open ePShNotation {C = C} F
  cat : ECat
  obj cat = Σ setF
  hom cat (J , v) (I , u) = Σ λ (f : hom C J I) → v ~ u · f
  hom-rel cat (f , _) (g , _) = f ~d g  -- proof irrelevant in the second argument
  hom-eqr cat = record
    { refl =  C .hom-eqr .refl ; sym =  C .hom-eqr .sym ; trans = C .hom-eqr .trans }
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


--------------------------------------------------------------------------------


-- This looks way too complicated, or?
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
    ≈⟨ comp-cong-l S {g = nat α a} (id-mor-inv B') ⟩
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
      ≈⟨ comp-assoc S {f = mor B' (seq .sym p ` (A .refl))}
           {g = mor B' (p ` (A .refl))} {h = nat α a} ⟩
        (mor B' (seq .sym p ` (A .refl)) ∘s mor B' (p ` (A .refl))) ∘s nat α a
      ≈⟨ comp-cong-l S {g = nat α a} (comp-mor B') ⟩
        mor B' fisf ∘s nat α a
      ≈⟨ comp-cong-l S {g = nat α a} (resp B' tt) ⟩
        mor B' (A' .refl) ∘s nat α a
      ≈⟨ comp-cong-l S {g = nat α a} (seq .sym (id-mor B')) ⟩
        id S ∘s nat α a
      ≈⟨ id-r S ⟩
        nat α a
      ∎

  trans (hom-eqr cat {A , B} {A' , B'}) {f , α} {g , β} {h , γ} (fg , αβ) (gh , βγ) =
    seq .trans fg gh , λ a →
      let open EqRelReason (seq {fun B a} {fun B' (h .ap a)}) in
      begin
        mor B' (seq .trans fg gh ` A .refl) ∘s nat α a
      ≈⟨ comp-cong-l S {g = nat α a} (comp-mor-inv B') ⟩
        (mor B' (gh ` A .refl) ∘s mor B' (fg ` A .refl)) ∘s nat α a
      ≈⟨ comp-assoc S {f = mor B' (gh ` A .refl)}
                    {g = mor B' (fg ` A .refl)} {h = nat α a}⟩
        mor B' (gh ` A .refl) ∘s (mor B' (fg ` A .refl) ∘s nat α a)
      ≈⟨ comp-cong-r S {f = mor B' (gh ` A .refl)} (αβ a) ⟩
        mor B' (gh ` A .refl) ∘s nat β a
      ≈⟨ βγ a ⟩
        (nat γ a)
      ∎

  comp cat {A , B} {A' , B'} {A'' , B''} (f , α) (g , β) = f ∘s g , record
    { nat = λ (a : A .set) → nat α (g .ap a) ∘s nat β a
    ; nat-eq = λ {a b p} → let open EqRelReason seq in
        begin
          ((mor B'' (f .ap-cong (g .ap-cong p))) ∘s (nat α (g .ap a))) ∘s nat β a
        ≈⟨ comp-cong-l S {g = nat β a} (nat-eq α)  ⟩
          (nat α (g .ap b) ∘s mor B' (g .ap-cong p)) ∘s nat β a
        ≈⟨ comp-assoc-inv S
             {f = nat α (g .ap b)} {g = mor B' (g .ap-cong p)} {h = nat β a} ⟩
          nat α (g .ap b) ∘s (mor B' (g .ap-cong p) ∘s nat β a)
        ≈⟨ comp-cong-r S {f = nat α (g .ap b)} (nat-eq β) ⟩
          (nat α (g .ap b) ∘s nat β b) ∘s (mor B p)
        ∎
    }

  comp-assoc cat {A1 , B1} {A2 , B2} {A3 , B3} {A4 , B4} {f , α} {g , β} {h , γ} =
    comp-assoc S {f = f} {g = g} {h = h} , λ a →
      let open EqRelReason seq
          k = nat α ((g ∘s h) .ap a) ∘s (nat β (h .ap a) ∘s nat γ a)
      in
        begin
          mor B4 (comp-assoc S {f = f} {g = g} {h = h} ` A1 .refl {a}) ∘s k
        ≈⟨ comp-cong-l S {g = k} (resp B4 tt) ⟩
          mor B4 (A4 .refl) ∘s k
        ≈⟨ comp-cong-l S {g = k} (id-mor-inv B4) ⟩
          id S ∘s k
        ≈⟨ id-l S ⟩
          k
        ∎

  comp-cong cat {A , B} {A' , B'} {A'' , B''} {f , α} {f' , α'} {g , β} {g' , β'}
    (ff' , αα') (gg' , ββ') = comp-cong S ff' gg' , λ a → -- seq .sym
      let open EqRelReason seq
      in -- NB: start reading at the bottom..
        begin  -- (comp-cong S ff' gg' ` A .refl {a}) is (ff' `(gg' ` A .refl {a}))
          mor B'' (ff' `(gg' ` A .refl {a})) ∘s (nat α (g .ap a) ∘s nat β a)
        ≈⟨ comp-cong-l S {g = nat α (g .ap a) ∘s nat β a} (resp B'' tt) ⟩
          (mor B'' (A'' .trans (f .ap-cong (gg' ` A .refl)) (ff' ` A' .refl)))
            ∘s (nat α (g .ap a) ∘s nat β a)
        ≈⟨ comp-cong-l S {g = nat α (g .ap a) ∘s nat β a} (comp-mor-inv B'') ⟩
          (mor B'' (ff' ` A' .refl) ∘s mor B'' (f .ap-cong (gg' ` A .refl)))
            ∘s (nat α (g .ap a) ∘s nat β a)
        ≈⟨ comp-assoc-inv S
             {f = mor B'' (ff' ` A' .refl)} {g = mor B'' (f .ap-cong (gg' ` A .refl))}
             {h = nat α (g .ap a) ∘s nat β a} ⟩
          mor B'' (ff' ` A' .refl) ∘s (mor B'' (f .ap-cong (gg' ` A .refl))
            ∘s (nat α (g .ap a) ∘s nat β a))
        ≈⟨ comp-cong-r S {f = mor B'' (ff' ` A' .refl)}
           (comp-assoc S {f = mor B'' (f .ap-cong (gg' ` A .refl))}
             {g = nat α (g .ap a)} {h = nat β a}) ⟩
          mor B'' (ff' ` A' .refl) ∘s ((mor B'' (f .ap-cong (gg' ` A .refl))
            ∘s nat α (g .ap a)) ∘s nat β a)
        ≈⟨ comp-cong-r S {f = mor B'' (ff' ` A' .refl)}
           (comp-cong-l S {g = nat β a} (nat-eq α)) ⟩
          mor B'' (ff' ` A' .refl) ∘s ((nat α (g' .ap a) ∘s mor B' (gg' ` A .refl))
            ∘s nat β a)
        ≈⟨ comp-cong-r S {f = mor B'' (ff' ` A' .refl)}
            (comp-assoc S {f = nat α (g' .ap a)} {g = mor B' (gg' ` A .refl)}
               {h = nat β a}) ⟩
          mor B'' (ff' ` A' .refl) ∘s (nat α (g' .ap a) ∘s (mor B' (gg' ` A .refl)
            ∘s nat β a))
        ≈⟨ comp-assoc S {f = mor B'' (ff' ` A' .refl)} {g = nat α (g' .ap a)}
             {h = (mor B' (gg' ` A .refl) ∘s nat β a)} ⟩
          (mor B'' (ff' ` A' .refl) ∘s nat α (g' .ap a)) ∘s (mor B' (gg' ` A .refl)
            ∘s nat β a)
        ≈⟨ comp-cong-l S {g = mor B' (gg' ` A .refl) ∘s nat β a} (αα' (g' .ap a)) ⟩
          nat α' (g' .ap a) ∘s (mor B' (gg' ` A .refl) ∘s nat β a)
        ≈⟨ comp-cong-r S {f = nat α' (g' .ap a)} (ββ' a) ⟩
          nat α' (g' .ap a) ∘s nat β' a
        ∎

  id cat {A , B} = id S , record
    { nat = λ (a : A .set) → id S
    ; nat-eq =  λ {a b p} → seq .trans {b = mor B p} (id-r S) (seq .sym (id-l S))
    }
  id-l cat {A , B} {A' , B'} {f , α} = id-l S , λ a →
    let open EqRelReason seq
    in
      begin
        (mor B' (id-l S {f = f} ` A .refl)) ∘s (id S ∘s nat α a)
      ≈⟨ comp-cong-l S {g = id S ∘s nat α a} (resp B' tt) ⟩
        (mor B' (A' .refl)) ∘s (id S ∘s nat α a)
      ≈⟨ comp-cong-l S {g = id S ∘s nat α a} (id-mor-inv B') ⟩
        id S ∘s (id S ∘s nat α a)
      ≈⟨ id-l S ⟩
        id S ∘s nat α a
      ≈⟨ id-l S ⟩
        (nat α a)
      ∎

  id-r cat {A , B} {A' , B'} {f , α} = id-r S , λ a →
    let open EqRelReason seq
    in
      begin
        mor B' (id-r S {f = f} ` A .refl) ∘s (nat α a ∘s id S)
      ≈⟨ comp-cong-l S {g = nat α a ∘s id S} (resp B' tt) ⟩
        mor B' (A' .refl) ∘s (nat α a ∘s id S)
      ≈⟨ comp-cong-l S {g = nat α a ∘s id S} (id-mor-inv B') ⟩
        id S ∘s (nat α a ∘s id S)
      ≈⟨ id-l S ⟩
        nat α a ∘s id S
      ≈⟨ id-r S ⟩
        nat α a
      ∎

  -- A different attempt at defining composition...
  -- -- TODO: why doesn (comp (EFunctor _ _) (r-whisker α (#fun g)) β)
  -- -- directly work as second component if I enable all eta-equalities
  -- -- for records?
  -- comp cat {A , B} {A' , B'} {A'' , B''} (f , α) (g , β) =
  --   f ∘s g , record
  --            { nat = comp (EFunctor _ _) (r-whisker α (#fun g)) β .nat
  --            ; nat-eq = comp (EFunctor _ _) (r-whisker α (#fun g)) β .nat-eq }

  -- comp-assoc cat {A1 , B1} {A2 , B2} {A3 , B3} {A4 , B4} {f , α} {g , β} {h , γ} =
  --   comp-assoc S {f = f} {g = g} {h = h} , λ a →
  --     let open EqRelReason seq
  --         lhs' = nat (snd (comp cat (f , α) (comp cat (g , β) (h , γ)))) a
  --         rhs  = nat (snd (comp cat (comp cat (f , α) (g , β)) (h , γ))) a
  --     in
  --       map-rel λ {a b} p → {!!}
  --       -- begin
  --       --   mor B4 (comp-assoc S {f = f} {g = g} {h = h} ` refl (eqr A1)) ∘s lhs'
  --       -- ≈⟨ comp-cong-l S {g = lhs'} (resp B4 tt) ⟩
  --       --   mor B4 (A4 .refl) ∘s lhs'
  --       -- ≈⟨ comp-cong-l S {g = lhs'} (seq .sym (id-mor B4)) ⟩
  --       --   id S ∘s lhs'
  --       -- ≈⟨ id-l S ⟩
  --       --   lhs'
  --       -- ≈⟨ map-rel (λ {a b} p →
  --       --     {!mor-resp B4!}) ⟩

  --       --   rhs
  --       -- ∎

  -- comp-cong cat {A , B} {A' , B'} {A'' , B''} {f , α} {f' , α'} {g , β} {g' , β'}
  --    (ff' , αα') (gg' , ββ') = {!!}

π : {l : Level} → eFunctor (EFam {l}) (ESet {l})
π = record
  { fun = fst ; mor = fst ; resp = fst
  ; id-mor = map-rel λ p → p
  ; comp-mor = λ { {f = f , _} {g = g , _} →
                   map-rel λ p → f .ap-cong (g .ap-cong p) }
  }


-- The Fam variant of an E-CwF
record eCwf {lv lo lh lr : Level} : Set (lsuc (lv ⊔ lo ⊔ lh ⊔ lr)) where
  field
    Ctx : ECat {lo} {lh} {lr}
    F   : eFunctor (Ctx op) (EFam {lv})

  -- Some notation
  Subst = Ctx .hom
  _~s_ = Ctx .hom-rel
  _∘s_ = Ctx .comp
  infixl 40 _∘s_

  Ty : ePSh Ctx
  Ty = π ∘Func F

  TyS : obj Ctx → eSet
  TyS Γ = fun Ty Γ
  Typ : obj Ctx → Set _
  Typ Γ = set (fun Ty Γ)
  _~_ : {Γ : obj Ctx} → Typ Γ → Typ Γ → Set lv
  _~_ {Γ} = rel (fun Ty Γ)
  ~eq : {Γ : obj Ctx} → _
  ~eq {Γ} = eqr (fun Ty Γ)


  _[_] : ∀ {Δ Γ} → Typ Γ → Subst Δ Γ → Typ Δ
  A [ σ ] = mor Ty σ .ap A
  infix 40 _[_]

  Ter : (Γ : obj Ctx) (A : Typ Γ) → Set _
  Ter Γ A = (fun F Γ) .snd .fun A .set

  TerS : (Γ : obj Ctx) → eFunctor (# (TyS Γ)) ESet
  TerS Γ = fun F Γ .snd

  _~t_ : ∀ {Γ A} → Ter Γ A → Ter Γ A → Set _
  _~t_ {Γ} {A} = (fun F Γ) .snd .fun A .rel
  teq : {Γ : obj Ctx} {A : Typ Γ} → _
  teq {Γ} {A} = (fun F Γ) .snd .fun A .eqr

  _[_]t : ∀ {Γ Δ A} (t : Ter Γ A) (σ : Subst Δ Γ) → Ter Δ (A [ σ ])
  u [ σ ]t = F .mor σ .snd .nat _ .ap u
  infix 50 _[_]t

  ι : ∀ {Γ} {A B : Typ Γ} → A ~ B → Ter Γ A → Ter Γ B
  ι {Γ} p = fun F Γ .snd .mor p .ap

  ιirr : ∀ {Γ} {A B : Typ Γ} {p q : A ~ B} {u v : Ter Γ A} → u ~t v → ι p u ~t ι q v
  ιirr {Γ} = fun F Γ .snd .resp tt .map-resp

  ιrefl : ∀ {Γ} {A : Typ Γ} {u : Ter Γ A} → u ~t ι (~eq .refl) u
  ιrefl {Γ} = fun F Γ .snd .id-mor .map-resp (teq .refl)

  ιtrans : ∀ {Γ} {A B C : Typ Γ} {p : B ~ C} {q : A ~ B} {u : Ter Γ A} →
           ι p (ι q u) ~t ι (~eq .trans q p) u
  ιtrans {Γ} = fun F Γ .snd .comp-mor .map-resp (teq .refl)

  field
    -- terminal object
    <> : obj Ctx
    ! :  ∀ {A} → hom Ctx A <>
    !-unique : ∀ {A} {g : hom Ctx A <>} → g ~s !

    -- context extension
    _∙_ : (Γ : obj Ctx) (A : Typ Γ) → obj Ctx
    pp : ∀ {Γ A} → Subst (Γ ∙ A) Γ
    qq : ∀ {Γ A} → Ter (Γ ∙ A) (A [ pp ])
    <_,_> : ∀ {Δ Γ} → (σ : Subst Δ Γ) {A : Typ Γ} (t : Ter Δ (A [ σ ])) → Subst Δ (Γ ∙ A)

    pp<> : ∀ {Δ Γ} {σ : Subst Δ Γ} {A : Typ Γ} {t : Ter Δ (A [ σ ])} →
             pp ∘s < σ , t > ~s σ

    -- TODO: missing laws etc


-- -}
