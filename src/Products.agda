module Products where

open import Basics

module _ {lo lh lr : Level} (C : ECat {lo} {lh} {lr}) where
  private
    lmax = lo ⊔ lh ⊔ lr
  open ECat C using () renaming (comp to _∘c_ ; hom-rel to _~c_ ; hom-eqr to ceq )

  record isTerminal (a : obj C) : Set lmax where
    no-eta-equality
    field
      ! : {b : obj C} → hom C b a
      !-η : {b : obj C} {f : hom C b a} → f ~c !
    !-η' : {b : obj C} {f g : hom C b a} → f ~c g
    !-η' {f = f} {g} = ceq .trans !-η (ceq .sym !-η)

  is-terminal-unique : ∀ {a b : obj C} → isTerminal a → isTerminal b → Iso {C = C} a b
  is-terminal-unique {a} {b} at bt = 
    let open isTerminal at renaming (! to !a ; !-η' to !a-η')
        open isTerminal bt renaming (! to !b ; !-η' to !b-η')
    in record
    { to-mor = !b ; to-mor-iso = record
      { inverse = !a ; inverse-section =  !b-η' ; inverse-retract = !a-η' } }

  record hasTerminal : Set lmax where
    no-eta-equality
    field
      terminal-obj : obj C
      is-terminal  : isTerminal terminal-obj
    open isTerminal is-terminal public

  record isProduct {a b} (ab) (p : hom C ab a) (q : hom C ab b) : Set lmax where
    no-eta-equality
    field
      ⟨_,_⟩ : ∀ {x} (f : hom C x a) (g : hom C x b) → hom C x ab
      ⟨⟩-η  : ∀ {x} (f : hom C x ab) → f ~c ⟨ p ∘c f , q ∘c f ⟩

  record hasProducts : Set lmax where
    no-eta-equality
    field
       prod : (a b : obj C) → obj C
       pp   : ∀ {a b} → hom C (prod a b) a
       qq   : ∀ {a b} → hom C (prod a b) b
       is-product : ∀ {a b} → isProduct (prod a b) pp qq
    open isProduct public -- TODO: is this really how one should do
                          -- it?  All the pairing now has explicit
                          -- arguments...

module _ {lco lch lcr ldo ldh ldr : Level}
         {C : ECat {lco} {lch} {lcr}} {D : ECat {ldo} {ldh} {ldr}}
         (F : eFunctor C D) where
  private
    lmax = lco ⊔ lch ⊔ lcr ⊔  ldo ⊔ ldh ⊔ ldr 

  preserves-terminal : Set lmax
  preserves-terminal = ∀ {a} → isTerminal C a → isTerminal D (fun F a)

  preserves-products : Set lmax
  preserves-products = ∀ {a b ab : obj C} {p : hom C ab a} {q : hom C ab b} →
    isProduct C ab p q → isProduct D (fun F ab) (mor F p) (mor F q)

-- TODO: formalize CAT with product preserving functors

-- Freely add finite products to a category
module FreeProd {lo lh lr : Level} (C : ECat {lo} {lh} {lr}) where
  private
    lmax = lo ⊔ lh ⊔ lr
  open ECat C using () renaming (comp to _∘c_ ; hom-rel to _~c_ ; hom-eqr to ceq )

  data Obj : Set lo where
    in-obj : obj C → Obj

  data Raw : Set (lo ⊔ lh) where
    -- Morphisms
    in-hom : {a b : obj C} (f : hom C a b) → Raw
    idr : Raw
    compr : Obj → Raw → Raw → Raw

  data _∈_⇒_ : (f : Raw) → Obj → Obj → Set (lo ⊔ lh)
  data _~_∈_⇒_ : (f g : Raw) → Obj → Obj → Set (lo ⊔ lh)

  data _∈_⇒_ where
    t-in-hom : {a b : obj C} (f : hom C a b) → (in-hom f) ∈ (in-obj a) ⇒ (in-obj b)
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

