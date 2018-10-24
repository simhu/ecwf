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
      ⟨⟩-cong : ∀ {x} {f f' : hom C x a} {g g' : hom C x b} → f ~c f' → g ~c g' →
                ⟨ f , g ⟩ ~c ⟨ f' , g' ⟩
      ⟨⟩-β-fst : ∀ {x} {f : hom C x a} {g : hom C x b} → (p ∘c ⟨ f , g ⟩) ~c f
      ⟨⟩-β-snd : ∀ {x} {f : hom C x a} {g : hom C x b} → (q ∘c ⟨ f , g ⟩) ~c g
      ⟨⟩-η  : ∀ {x} (f : hom C x ab) → f ~c ⟨ p ∘c f , q ∘c f ⟩

    ⟨⟩-η'  : ∀ {x} {f g : hom C x ab} → (p ∘c f) ~c (p ∘c g) → (q ∘c f) ~c (q ∘c g) → f ~c g
    ⟨⟩-η' {f = f} {g} pfg qfg =  let open EqRelReason ceq in
      begin
        f
      ≈⟨ ⟨⟩-η f ⟩
        ⟨ p ∘c f , q ∘c f ⟩
      ≈⟨ ⟨⟩-cong pfg qfg ⟩
        ⟨ p ∘c g , q ∘c g ⟩
      ≈⟨ ceq .sym (⟨⟩-η g) ⟩
        g
      ∎

    ⟨⟩-η-id : ⟨ p , q ⟩ ~c id C
    ⟨⟩-η-id = ⟨⟩-η' (ceq .trans ⟨⟩-β-fst (id-r-inv C)) (ceq .trans ⟨⟩-β-snd (id-r-inv C))

  products-unique : ∀ {x y a b pa qa pb qb} →
                    isProduct {x} {y} a pa qa → isProduct {x} {y} b pb qb →
                    Iso {C = C} a b
  products-unique {pa = pa} {qa} {pb} {qb} aprod bprod = record
    { to-mor = B.⟨ pa , qa ⟩
    ; to-mor-iso = record
      { inverse = A.⟨ pb , qb ⟩
      ; inverse-section =
        let open EqRelReason ceq
            lhs = B.⟨ pa , qa ⟩ ∘c A.⟨ pb , qb ⟩
        in begin
             B.⟨ pa , qa ⟩ ∘c A.⟨ pb , qb ⟩
           ≈⟨ B.⟨⟩-η lhs ⟩
             B.⟨ pb ∘c lhs , qb ∘c lhs ⟩
           ≈⟨ B.⟨⟩-cong (comp-assoc C) (comp-assoc C) ⟩
             B.⟨ (pb ∘c B.⟨ pa , qa ⟩) ∘c A.⟨ pb , qb ⟩ , (qb ∘c B.⟨ pa , qa ⟩) ∘c A.⟨ pb , qb ⟩ ⟩
           ≈⟨ B.⟨⟩-cong (comp-cong-l C B.⟨⟩-β-fst) (comp-cong-l C B.⟨⟩-β-snd) ⟩
             B.⟨ pa ∘c A.⟨ pb , qb ⟩ , qa ∘c A.⟨ pb , qb ⟩ ⟩
           ≈⟨ B.⟨⟩-cong A.⟨⟩-β-fst A.⟨⟩-β-snd ⟩
             B.⟨ pb , qb ⟩
           ≈⟨ B.⟨⟩-η-id ⟩
             id C
           ∎
      ; inverse-retract =
        let open EqRelReason ceq
            lhs = A.⟨ pb , qb ⟩ ∘c B.⟨ pa , qa ⟩
        in begin
             A.⟨ pb , qb ⟩ ∘c B.⟨ pa , qa ⟩
           ≈⟨ A.⟨⟩-η lhs ⟩
             A.⟨ pa ∘c lhs , qa ∘c lhs ⟩
           ≈⟨ A.⟨⟩-cong (comp-assoc C) (comp-assoc C) ⟩
             A.⟨ (pa ∘c A.⟨ pb , qb ⟩) ∘c B.⟨ pa , qa ⟩ , (qa ∘c A.⟨ pb , qb ⟩) ∘c B.⟨ pa , qa ⟩ ⟩
           ≈⟨ A.⟨⟩-cong (comp-cong-l C A.⟨⟩-β-fst) (comp-cong-l C A.⟨⟩-β-snd) ⟩
             A.⟨ pb ∘c B.⟨ pa , qa ⟩ , qb ∘c B.⟨ pa , qa ⟩ ⟩
           ≈⟨ A.⟨⟩-cong B.⟨⟩-β-fst B.⟨⟩-β-snd ⟩
             A.⟨ pa , qa ⟩
           ≈⟨ A.⟨⟩-η-id ⟩
             id C
           ∎
        }
    }
    where open module A = isProduct aprod
          open module B = isProduct bprod

  record hasProducts : Set lmax where
    no-eta-equality
    field
       prod : (a b : obj C) → obj C
       pp   : ∀ {a b} → hom C (prod a b) a
       qq   : ∀ {a b} → hom C (prod a b) b
       is-product : ∀ {a b} → isProduct (prod a b) pp qq

    open module isProd {a b : obj C} = isProduct (is-product {a} {b}) public



-- As an example, we show who ESet has products.
_×S_ : ∀ {las lar lbs lbr} → eSet {las} {lar} → eSet {lbs} {lbr} → eSet
A ×S B = record
  { set = A .set × B .set
  ; rel =  λ { (a , b) (a' , b' ) → A .rel a a' × B .rel b b'}
  ; eqr = record { refl =  A .refl , B .refl
                 ; sym = λ p → A .sym (fst p) , B .sym (snd p)
                 ; trans = λ p q → A .trans (fst p) (fst q) , B .trans (snd p) (snd q)
                 }
  }

eset-has-products : ∀ {ls lr} → hasProducts (ESet {ls} {lr})
eset-has-products = record
  { prod = _×S_
  ; pp = record { ap = fst ; ap-cong = fst }
  ; qq = record { ap = snd ; ap-cong = snd }
  ; is-product = record
    { ⟨_,_⟩ = λ f g → record { ap = λ x → f .ap x , g .ap x
                             ; ap-cong = λ x → f .ap-cong x , g .ap-cong x
                             }
    ; ⟨⟩-cong = λ ff' gg' → map-rel (λ x → (ff' ` x) , (gg' ` x))
    ; ⟨⟩-β-fst = λ { {f = f} → map-rel (f .ap-cong) }
    ; ⟨⟩-β-snd = λ { {g = g} → map-rel (g .ap-cong) }
    ; ⟨⟩-η = λ f → map-rel (f .ap-cong)
    }
  }


module _ {lco lch lcr ldo ldh ldr : Level}
         {C : ECat {lco} {lch} {lcr}} {D : ECat {ldo} {ldh} {ldr}}
         (F : eFunctor C D) where
  private
    lmax = lco ⊔ lch ⊔ lcr ⊔  ldo ⊔ ldh ⊔ ldr

  -- Note that strict preservation of a structure would refer to
  -- equality of objects.

  preserves-terminal : Set lmax
  preserves-terminal = ∀ {a} → isTerminal C a → isTerminal D (fun F a)

  preserves-products : Set lmax
  preserves-products = ∀ {a b ab : obj C} {p : hom C ab a} {q : hom C ab b} →
    isProduct C ab p q → isProduct D (fun F ab) (mor F p) (mor F q)

-- TODO: formalize CAT with product preserving functors

-- Freely add binary products to a category
module FreeProd {lo lh lr : Level} (C : ECat {lo} {lh} {lr}) where
  private
    lmax = lo ⊔ lh ⊔ lr
  open ECat C using () renaming (comp to _∘c_ ; hom-rel to _~c_ ; hom-eqr to ceq )

  data Obj : Set lo where
    [_] : obj C → Obj
    _×r_ : Obj → Obj → Obj

  infix 30 _×r_

  data Raw : Set (lo ⊔ lh) where
    -- Morphisms
    [_] : {a b : obj C} (f : hom C a b) → Raw
    idr : Raw
    compr : Obj → Raw → Raw → Raw
    ppr : Obj → Obj → Raw
    qqr : Obj → Obj → Raw
    ⟨_,_⟩r : Raw → Raw → Raw

  data _∈_⇒_ : (f : Raw) → Obj → Obj → Set (lo ⊔ lh)
  data _~_∈_⇒_ : (f g : Raw) → Obj → Obj → Set (lo ⊔ lh ⊔ lr)

  data _∈_⇒_ where
    t-[] : {a b : obj C} (f : hom C a b) → [ f ] ∈ [ a ] ⇒ [ b ]
    t-id : ∀ (a : Obj) → idr ∈ a ⇒ a
    t-compr : ∀ {f g a b c} → f ∈ b ⇒ c → g ∈ a ⇒ b → (compr b f g) ∈ a ⇒ c

    t-ppr : ∀ { a b : Obj} → ppr a b ∈ a ×r b ⇒ a
    t-qqr : ∀ { a b : Obj} → qqr a b ∈ a ×r b ⇒ b
    t-⟨⟩r : ∀ {a b c : Obj} {f g} → f ∈ c ⇒ a → g ∈ c ⇒ b → ⟨ f , g ⟩r ∈ c ⇒ a ×r b

  data _~_∈_⇒_ where
    -- extend the given structure
    t-[]-cong : ∀ {a b} {f g : hom C a b} → f ~c g → [ f ] ~ [ g ] ∈ [ a ] ⇒ [ b ]
    t-[]-comp : ∀ {a b c} {f : hom C b c} {g : hom C a b} →
                [ comp C f g ] ~ compr [ b ] [ f ] [ g ] ∈ [ a ] ⇒ [ c ]
    t-[]-id :  ∀ {a} → [ id C {a} ] ~ idr ∈ [ a ] ⇒ [ a ]

    -- rules for products
    t-⟨⟩-cong : ∀ {a b c : Obj} {f f' g g' : Raw} → f ~ f' ∈ c ⇒ a → g ~ g' ∈ c ⇒ b →
                ⟨ f , g ⟩r ~ ⟨ f' , g' ⟩r ∈ c ⇒ a ×r b
    t-⟨⟩-β-fst : ∀ {a b c f g} → {p : f ∈ c ⇒ a} {q : g ∈ c ⇒ b} →
                 compr (a ×r b) (ppr a b) ⟨ f , g ⟩r ~ f ∈ c ⇒ a
    t-⟨⟩-β-snd : ∀ {a b c f g} → {p : f ∈ c ⇒ a} {q : g ∈ c ⇒ b} →
                 compr (a ×r b) (qqr a b) ⟨ f , g ⟩r ~ g ∈ c ⇒ b
    t-⟨⟩-η  : ∀ {a b c f} {p : f ∈ c ⇒ a ×r b} →
              f ~ ⟨ compr (a ×r b) (ppr a b) f , compr (a ×r b) (qqr a b) f ⟩r ∈ c ⇒ a ×r b

    -- rules for composition and identity
    t-compr-assoc : ∀ {a b c d f g h} {p : f ∈ c ⇒ d} {q : g ∈ b ⇒ c} {r : h ∈ a ⇒ b} →
      compr c f (compr b g h) ~ compr b (compr c f g) h ∈ a ⇒ d
    t-compr-cong : ∀ {a b c f f' g g'}
                  {p : f ∈ b ⇒ c} {q : f' ∈ b ⇒ c} {r : g ∈ a ⇒ b} {s : g' ∈ a ⇒ b} →
                  f ~ f' ∈ b ⇒ c → g ~ g' ∈ a ⇒ b → compr b f g ~ compr b f' g' ∈ a ⇒ c
    t-idr-l : ∀ {a b f} → f ∈ a ⇒ b → compr b idr f ~ f ∈ a ⇒ b
    t-idr-r : ∀ {a b f} → f ∈ a ⇒ b → compr a f idr ~ f ∈ a ⇒ b

    -- rules for setoids
    t-~-refl : ∀ {a b f} → {p : f ∈ a ⇒ b} → f ~ f ∈ a ⇒ b
    t-~-sym  : ∀ {a b f g} → f ~ g ∈ a ⇒ b  → g ~ f ∈ a ⇒ b
    t-~-trans  : ∀ {a b f g h} → f ~ g ∈ a ⇒ b → g ~ h ∈ a ⇒ b → f ~ h ∈ a ⇒ b

  freeProd : ECat
  freeProd = record
    { obj = Obj
    ; hom = λ a b → Σ λ (f : Raw) → f ∈ a ⇒ b
    ; hom-rel = λ { {a} {b} (f , _) (g , _) → f ~ g ∈ a ⇒ b }
    ; hom-eqr =  record
      { refl = λ {a} → t-~-refl {p = snd a} ; sym = t-~-sym ; trans = t-~-trans }
    ; comp = λ { (f , p) (g , q) → compr _ f g , t-compr p q }
    ; comp-assoc = λ { {f = f} {g} {h} → t-compr-assoc {p = snd f} {snd g} {snd h}}
    ; comp-cong = λ { {f = f} {f'} {g} {g'} →
      t-compr-cong {p = snd f} {snd f'} {snd g} {snd g'} }
    ; id = λ { {a} → idr , t-id a }
    ; id-l = λ { {f = f} → t-idr-l (snd f) }
    ; id-r = λ { {f = f} → t-idr-r (snd f) }
    }

  freeprod-has-products : hasProducts freeProd
  freeprod-has-products = record { prod = _×r_ ; pp = ppr _ _ , t-ppr ; qq = qqr _ _ , t-qqr ;
    is-product = record
       { ⟨_,_⟩ = λ f g → ⟨ fst f , fst g ⟩r , t-⟨⟩r (snd f) (snd g)
       ; ⟨⟩-cong = λ ff' gg' → t-⟨⟩-cong ff' gg'
       ; ⟨⟩-β-fst = λ { {f = f} {g} → t-⟨⟩-β-fst {p = snd f} {q = snd g} }
       ; ⟨⟩-β-snd =  λ { {f = f} {g} → t-⟨⟩-β-snd {p = snd f} {q = snd g} }
       ; ⟨⟩-η = λ f → t-⟨⟩-η {p = snd f}
       } }

  ~-l : ∀ {a b f g} → f ~ g ∈ a ⇒ b → f ∈ a ⇒ b
  ~-r : ∀ {a b f g} → f ~ g ∈ a ⇒ b → g ∈ a ⇒ b

  ~-l (t-compr-assoc {p = p} {q} {r}) = t-compr p (t-compr q r)
  ~-l (t-compr-cong ff' gg') = t-compr (~-l ff') (~-l gg')
  ~-l (t-idr-l pf) = t-compr (t-id _) pf
  ~-l (t-idr-r pf) = t-compr pf (t-id _)
  ~-l (t-~-refl {p = p})= p
  ~-l (t-~-sym p) = ~-r p
  ~-l (t-~-trans p q) = ~-l p
  ~-l (t-[]-cong {f = f} _) = t-[] f
  ~-l (t-[]-comp {f = f} {g}) = t-[] (comp C f g)
  ~-l t-[]-id = t-[] (id C)
  ~-l (t-⟨⟩-cong ff' gg') = t-⟨⟩r (~-l ff') (~-l gg')
  ~-l (t-⟨⟩-β-fst {p = p} {q}) = t-compr t-ppr (t-⟨⟩r p q)
  ~-l (t-⟨⟩-β-snd {p = p} {q}) = t-compr t-qqr (t-⟨⟩r p q)
  ~-l (t-⟨⟩-η {p = p}) = p

  ~-r (t-compr-assoc {p = p} {q} {r}) = t-compr (t-compr p q) r
  ~-r (t-compr-cong ff' gg') = t-compr (~-r ff') (~-r gg')
  ~-r (t-idr-l pf) = pf
  ~-r (t-idr-r pf) = pf
  ~-r (t-~-refl {p = p}) = p
  ~-r (t-~-sym p) = ~-l p
  ~-r (t-~-trans p q) = ~-r q
  ~-r (t-[]-cong {g = g} _) = t-[] g
  ~-r (t-[]-comp {f = f} {g}) = t-compr (t-[] f) (t-[] g)
  ~-r t-[]-id = t-id _
  ~-r (t-⟨⟩-cong ff' gg') = t-⟨⟩r (~-r ff') (~-r gg')
  ~-r (t-⟨⟩-β-fst {p = p} {q}) = p
  ~-r (t-⟨⟩-β-snd {p = p} {q}) = q
  ~-r (t-⟨⟩-η {p = p}) = t-⟨⟩r (t-compr t-ppr p) (t-compr t-qqr p)

  module _ {ldo ldh ldr} (D : ECat {ldo} {ldh} {ldr}) (d-products : hasProducts D)
           (F : eFunctor C D) where

    open ECat D using () renaming (comp to _∘d_ ; hom-rel to _~d_ ; hom-eqr to deq )
    open hasProducts d-products

    objMap : Obj → obj D
    objMap [ x ] = fun F x
    objMap (a ×r b) = prod (objMap a) (objMap b)

    homMap : {a b : Obj} {f : Raw}
             (pf : f ∈ a ⇒ b) → hom D (objMap a) (objMap b)
    homMap (t-[] f) = mor F f
    homMap (t-id a) = id D
    homMap (t-compr pf pg) = homMap pf ∘d homMap pg
    homMap t-ppr = pp
    homMap t-qqr = qq
    homMap (t-⟨⟩r pf pg) = ⟨ homMap pf , homMap pg ⟩

    homMapIrr : {a b : Obj} {f : Raw} (pf0 pf1 : f ∈ a ⇒ b) →
                homMap pf0 ~d homMap pf1
    homMapIrr (t-[] f) (t-[] .f) = deq .refl
    homMapIrr (t-id a) (t-id .a) = deq .refl
    homMapIrr (t-compr pf0 pg0) (t-compr pf1 pg1) =
      comp-cong D (homMapIrr pf0 pf1) (homMapIrr pg0 pg1)
    homMapIrr t-ppr t-ppr = deq .refl
    homMapIrr t-qqr t-qqr = deq .refl
    homMapIrr (t-⟨⟩r pf0 pg0) (t-⟨⟩r pf1 pg1) =
      ⟨⟩-cong (homMapIrr pf0 pf1) (homMapIrr pg0 pg1)

    ~Map : {a b : Obj} {f g : Raw} (pf : f ∈ a ⇒ b) (pg : g ∈ a ⇒ b) →
           f ~ g ∈ a ⇒ b → homMap pf ~d homMap pg
    ~Map pf pg t-~-refl = homMapIrr pf pg
    ~Map pf pg (t-~-sym pfg) = deq .sym (~Map pg pf pfg)
    ~Map pf ph (t-~-trans {a} {b} {f} {g} {h} pfg pgh) =
      let pg0 : g ∈ a ⇒ b
          pg0 = ~-r pfg
          pg1 : g ∈ a ⇒ b
          pg1 = ~-l pgh
          open EqRelReason deq
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
      let open EqRelReason deq in
        begin
          homMap pf0 ∘d (homMap pg0 ∘d homMap ph0)
        ≈⟨ comp-assoc D ⟩
          (homMap pf0 ∘d homMap pg0) ∘d homMap ph0
        ≈⟨ comp-cong D (comp-cong D (homMapIrr pf0 pf1) (homMapIrr pg0 pg1)) (homMapIrr ph0 ph1) ⟩
          (homMap pf1 ∘d homMap pg1) ∘d homMap ph1
        ∎
    ~Map (t-compr pf0 pg0) (t-compr pf1 pg1) (t-compr-cong pf01 pg01) =
      comp-cong D (~Map pf0 pf1 pf01) (~Map pg0 pg1 pg01)
    ~Map (t-compr (t-id a) pf0) pf1 (t-idr-l x) =
      let open EqRelReason deq in
        begin
          id D ∘d homMap pf0
        ≈⟨ id-l D ⟩
          homMap pf0
        ≈⟨ homMapIrr pf0 pf1 ⟩
          homMap pf1
        ∎

    ~Map (t-compr pf0 (t-id a)) pf1 (t-idr-r x) =
      let open EqRelReason deq in
        begin
          homMap pf0 ∘d id D
        ≈⟨ id-r D ⟩
          homMap pf0
        ≈⟨ homMapIrr pf0 pf1 ⟩
          homMap pf1
        ∎
    ~Map (t-[] f) (t-[] g) (t-[]-cong x) = resp F x
    ~Map (t-[] .(comp C f g)) (t-compr (t-[] f) (t-[] g)) (t-[]-comp {a} {_} {_} {f} {.g}) =
      deq .sym (comp-mor F)
    ~Map (t-[] .(id C)) (t-id .([ _ ])) t-[]-id = deq .sym (id-mor F)
    ~Map (t-⟨⟩r pf pg) (t-⟨⟩r pf' pg') (t-⟨⟩-cong pff' pgg') =
      ⟨⟩-cong (~Map pf pf' pff') (~Map pg pg' pgg')
    ~Map (t-compr t-ppr (t-⟨⟩r pf0 pg0)) pf1 t-⟨⟩-β-fst =
      let open EqRelReason deq in
        begin
          pp ∘d ⟨ homMap pf0 , homMap pg0 ⟩
        ≈⟨ ⟨⟩-β-fst ⟩
          homMap pf0
        ≈⟨ homMapIrr pf0 pf1 ⟩
          homMap pf1
        ∎
    ~Map (t-compr t-qqr (t-⟨⟩r pf0 pg0)) pg1 t-⟨⟩-β-snd =
      let open EqRelReason deq in
        begin
          qq ∘d ⟨ homMap pf0 , homMap pg0 ⟩
        ≈⟨ ⟨⟩-β-snd ⟩
          homMap pg0
        ≈⟨ homMapIrr pg0 pg1 ⟩
          homMap pg1
        ∎
    ~Map pf0 (t-⟨⟩r (t-compr t-ppr pf1) (t-compr t-qqr pf2)) t-⟨⟩-η =
      let open EqRelReason deq in
        begin
          homMap pf0
        ≈⟨ ⟨⟩-η _ ⟩
          ⟨ pp ∘d homMap pf0 , qq ∘d homMap pf0 ⟩
        ≈⟨ ⟨⟩-cong (comp-cong-r D (homMapIrr pf0 pf1)) (comp-cong-r D (homMapIrr pf0 pf2)) ⟩
          ⟨ pp ∘d homMap pf1 , qq ∘d homMap pf2 ⟩
        ∎

    free-elim : eFunctor freeProd D
    free-elim = record
      { fun = objMap
      ; mor = λ {(f , pf) → homMap pf}
      ; resp = λ {a} {b} {f} {g} p → ~Map (snd f) (snd g) p
      ; id-mor = deq .refl
      ; comp-mor = deq .refl
      }

    -- The chosen products are preserved definitionally:
    free-elim-preserves-product-str :
      ∀ {a b : Obj} → let open module F = hasProducts freeprod-has-products
                      in isProduct D (fun free-elim (F.prod a b))
                           (mor free-elim (F.pp {a} {b}))
                           (mor free-elim (F.qq {a} {b}))
    free-elim-preserves-product-str = is-product
