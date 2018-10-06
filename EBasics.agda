module EBasics where

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
  field
    set : Set ls
    rel : set → set → Set lr
    eqr : EqRel rel
  open EqRel eqr public

open eSet public

-- E-Categories
record ECat {lo lh lr : Level} : Set (lsuc (lo ⊔ lh ⊔ lr)) where
  field
    obj : Set lo
    hom : obj → obj → Set lh
    _∼_ : ∀ {A B} (f g : hom A B) → Set lr
    ∼-eq : ∀ {A B} → EqRel {lh} {lr} {hom A B} _∼_
    _∘_ : ∀ {A B C} → hom B C → hom A B → hom A C
    ∘-assoc : ∀ {A B C D} {f : hom C D} {g : hom B C} {h : hom A B} → (f ∘ (g ∘ h)) ∼ ((f ∘ g) ∘ h)
    ∘-cong : ∀ {A B C} {f f' : hom B C} {g g' : hom A B} → f ∼ f' → g ∼ g' → (f ∘ g) ∼ (f' ∘ g')
    id : ∀ {A} → hom A A
    id-l : ∀ {A B} {f : hom A B} → (id ∘ f) ∼ f
    id-r : ∀ {A B} {f : hom A B} → (f ∘ id) ∼ f
  ∘-cong-l : ∀ {A B C} {f f' : hom B C} {g : hom A B} → f ∼ f' →(f ∘ g) ∼ (f' ∘ g)
  ∘-cong-l p = ∘-cong p (∼-eq .refl)

  ∘-cong-r : ∀ {A B C} {f : hom B C} {g g' : hom A B} → g ∼ g' →(f ∘ g) ∼ (f ∘ g')
  ∘-cong-r = ∘-cong (∼-eq .refl)

  

open ECat public

-- The opposite of an E-Cat
_op : ∀ {lo lh lr} → ECat {lo} {lh} {lr} → ECat {lo} {lh} {lr}
obj (C op) = obj C
hom (C op) A B = hom C B A
_∼_ (C op) f g = _∼_ C f g 
refl (∼-eq (C op)) = C .∼-eq .refl 
sym (∼-eq (C op)) = C .∼-eq .sym
trans (∼-eq (C op)) = C .∼-eq .trans
_∘_ (C op) f g = C ._∘_ g f 
∘-assoc (C op) = C .∼-eq .sym (C .∘-assoc)
∘-cong (C op) p q = C .∘-cong q p 
id (C op) = id C
id-l (C op) = id-r C
id-r (C op) = id-l C

-- The E-Cat of E-Sets
ESet : {l : Level} → ECat {lsuc l} {l} {l}
obj (ESet {l}) = eSet {l} {l}
hom ESet A B =  Σ λ (f : A .set → B .set) → ∀ {a b} → A .rel a b → B .rel (f a) (f b)
-- This should really be pointwise equality instead:
_∼_ ESet {A} {B} (f , _) (g , _) =  ∀ {a b} → A .rel a b → B .rel (f a) (g b)
-- _∼_ ESet {A} {B} (f , _) (g , _) = ∀ (a : A .set) → B .rel (f a) (g b)
refl (∼-eq ESet {A} {B}) {(f , fe)} = fe
sym (∼-eq ESet {A} {B}) ptw pa = B .sym (ptw (A .sym pa))
trans (∼-eq ESet {A} {B}) ptw ptw' pa = B .trans (ptw pa) (ptw' (A .refl))
_∘_ ESet (f , fe) (g , ge) =  (λ x → f (g x)) ,  λ p →  fe (ge p)
∘-assoc ESet {A} {B} {C} {D} {(f , fe)} {(g , ge)} {(h , he)} pa =  fe (ge (he pa))
∘-cong ESet p q ab = p (q ab)
id ESet {A} = (λ x → x) , (λ {_} {_} x → x)
id-l ESet {f = (f , fe)} ab = fe ab
id-r ESet {f = (f , fe)} ab = fe ab

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
    resp : ∀ {a b} {f g : hom C a b} → _∼_ C f g → _∼_ D (mor f) (mor g)
    id-mor : ∀ {a} → _∼_ D (D .id) (mor {a} {a} (C .id))
    ∘-mor : ∀ {a b c} {f : hom C b c} {g : hom C a b} → 
              _∼_ D (D ._∘_ (mor f) (mor g)) (mor (C ._∘_ f g))

open eFunctor public

_∘Func_ : {lco lch lcr ldo ldh ldr leo leh ler : Level}
  {C : ECat {lco} {lch} {lcr}} {D : ECat {ldo} {ldh} {ldr}} {E : ECat {leo} {leh} {ler}}
  (F : eFunctor D E) (G : eFunctor C D) → eFunctor C E
_∘Func_ {C = C} {D = D} {E = E} F G = FG where
  FG : eFunctor C E
  fun FG =  λ c → fun F (fun G c)
  mor FG =  λ p → mor F (mor G p)
  resp FG = λ p → resp F (resp G p)
  id-mor FG = E .∼-eq .trans (id-mor F) (resp F (id-mor G))
  ∘-mor FG = E .∼-eq .trans (∘-mor F) (resp F (∘-mor G))


-- E-Natural Transformations
record eNat {lco lch lcr ldo ldh ldr : Level}
    {C : ECat {lco} {lch} {lcr}} {D : ECat {ldo} {ldh} {ldr}}
    (F G : eFunctor C D) : Set (lco ⊔ lch ⊔ lcr ⊔ ldo ⊔ ldh ⊔ ldr) where
  no-eta-equality    
  field
    nat : (a : obj C) → hom D (fun F a) (fun G a)
    nat-eq : ∀ {a b} {f : hom C a b} →
             let _∘D_ = D ._∘_ 
                 _~D_ = D ._∼_
             in ((mor G f) ∘D (nat a)) ~D ((nat b) ∘D (mor F f))
open eNat public

EFunctor : {lco lch lcr ldo ldh ldr : Level}
  (C : ECat {lco} {lch} {lcr}) (D : ECat {ldo} {ldh} {ldr}) →
  ECat
EFunctor C D = cat where
  _~D_ = D ._∼_
  _∘D_ = D ._∘_ 
  infixl 40 _∘D_
  Deq = D .∼-eq
  cat : ECat
  obj cat = eFunctor C D
  hom cat F G = eNat F G
  _∼_ cat α β =  ∀ a → nat α a ~D nat β a
  refl (∼-eq cat) =  λ _ → Deq .refl
  sym (∼-eq cat) p =  λ a → Deq .sym (p a) 
  trans (∼-eq cat) p q =  λ a → Deq .trans (p a) (q a)
  nat (cat ._∘_ α β) = λ a → nat α a ∘D nat β a
  nat-eq (cat ._∘_ {F} {G} {H} α β) {a} {b} {f} = let open EqRelReason Deq in
    begin
      ((mor H f) ∘D (nat (cat ._∘_ α β) a))
    ≈⟨  D .∘-assoc ⟩ 
      ((mor H f) ∘D (nat α a)) ∘D (nat β a)
    ≈⟨ ∘-cong-l D (nat-eq α) ⟩ 
      ((nat α b) ∘D (mor G f)) ∘D (nat β a)
    ≈⟨ Deq .sym (D .∘-assoc) ⟩ 
      (nat α b) ∘D ((mor G f) ∘D (nat β a))
    ≈⟨ ∘-cong-r D (nat-eq β) ⟩ 
      (nat α b) ∘D ((nat β b) ∘D (mor F f))
    ≈⟨ D .∘-assoc ⟩ 
      ((nat (cat ._∘_ α β) b) ∘D (mor F f))
    ∎
  ∘-assoc cat = λ _ → D .∘-assoc
  ∘-cong cat =  λ p q a → D .∘-cong (p a) (q a)
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
module ePShNotation {k l l' l''} {C : ECat {l} {l'} {l''}} (F : ePSh {k} C) where
  _∘d_ = C ._∘_
  _∼d_ = C ._∼_
  setF : obj C → Set k
  setF I = set (fun F I)
  _~_ : {I : obj C} → setF I → setF I → Set k 
  _~_ {I} = rel (fun F I)
  infixl 40 _·_
  _·_ : ∀ {I J} → setF I → hom C J I → setF J
  u · h = fst (mor F h) u

-- The category of elements of a preasheaf
∫ : ∀ {k lo lh lr} {C : ECat {lo} {lh} {lr}} (F : ePSh {k} C) → ECat
∫ {C = C} F = cat where
  open ePShNotation F
  cat : ECat
  obj cat = Σ setF
  hom cat (J , v) (I , u) = Σ λ (f : hom C J I) → v ~ u · f
  _∼_ cat (f , _) (g , _) = f ∼d g  -- proof irrelevant in the second argument
  ∼-eq cat = record { refl =  C .∼-eq .refl ; sym =  C .∼-eq .sym ; trans = C .∼-eq .trans }
  fst (_∘_ cat (f , _) (g , _)) = f ∘d g
  snd (_∘_ cat {(K , w)} {(J , v)} {(I , u)} (f , p) (g , q)) = 
      let gvrelfgu : v · g ~ u · (f ∘d g)
          gvrelfgu  = fun F K .trans (snd (mor F g) p) (F .∘-mor (fun F I .refl))
      in fun F K .trans q gvrelfgu
  ∘-assoc cat = C .∘-assoc
  ∘-cong cat = C .∘-cong
  id cat {(I , u)}=  id C , id-mor F (fun F I .refl) 
  id-l cat = id-l C
  id-r cat = id-r C

-- Any setoid is a discrete category (which is also a groupoid)
# : ∀ {ls lr} (A : eSet {ls} {lr}) → ECat
obj (# A) = A .set
hom (# A) a b = A .rel a b
_∼_ (# A) p q = Unit
refl (∼-eq (# A)) = tt
sym (∼-eq (# A)) =  λ _ → tt
trans (∼-eq (# A)) = λ _ _ → tt
_∘_ (# A) p q = A .trans q p
∘-assoc (# A) = tt
∘-cong (# A) = λ _ _ → tt
id (# A) = A .refl
id-l (# A) = tt
id-r (# A) = tt

#fun : ∀ {l} {A B} (f : hom (ESet {l}) A B) → eFunctor (# A) (# B)
fun (#fun (f , fr)) = f
mor (#fun (f , fr)) = fr
resp (#fun (f , fr)) =  λ _ → tt
id-mor (#fun (f , fr)) = tt
∘-mor (#fun (f , fr)) = tt

