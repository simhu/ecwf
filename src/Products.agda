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
    ⟨⟩-η' {f = f} {g} pfg qfg = let open EqRelReason ceq in
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

    ⟨⟩-comp : ∀ {c d} {f : hom C c a} {g : hom C c b} {h : hom C d c} →
              (⟨ f , g ⟩ ∘c h) ~c ⟨ f ∘c h , g ∘c h ⟩
    ⟨⟩-comp {f = f} {g} {h} = ⟨⟩-η' eq1 eq2
      where open module M {x} {y} = EqRelReason (ceq {x} {y}) public
            eq1 = begin
                    p ∘c (⟨ f , g ⟩ ∘c h)
                  ≈⟨ comp-assoc C ⟩
                    (p ∘c ⟨ f , g ⟩) ∘c h
                  ≈⟨ comp-cong-l C ⟨⟩-β-fst ⟩
                    f ∘c h
                  ≈⟨ ceq .sym ⟨⟩-β-fst ⟩
                    p ∘c ⟨ f ∘c h , g ∘c h ⟩
                  ∎
            eq2 = begin
                    q ∘c (⟨ f , g ⟩ ∘c h)
                  ≈⟨ comp-assoc C ⟩
                    (q ∘c ⟨ f , g ⟩) ∘c h
                  ≈⟨ comp-cong-l C ⟨⟩-β-snd ⟩
                    g ∘c h
                  ≈⟨ ceq .sym ⟨⟩-β-snd ⟩
                    q ∘c ⟨ f ∘c h , g ∘c h ⟩
                  ∎


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
             B.⟨ (pb ∘c B.⟨ pa , qa ⟩) ∘c A.⟨ pb , qb ⟩
               , (qb ∘c B.⟨ pa , qa ⟩) ∘c A.⟨ pb , qb ⟩ ⟩
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
             A.⟨ (pa ∘c A.⟨ pb , qb ⟩) ∘c B.⟨ pa , qa ⟩
               , (qa ∘c A.⟨ pb , qb ⟩) ∘c B.⟨ pa , qa ⟩ ⟩
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

-- TODO: formalize CATs with products and product preserving functors

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

    t-ppr : ∀ {a b : Obj} → ppr a b ∈ a ×r b ⇒ a
    t-qqr : ∀ {a b : Obj} → qqr a b ∈ a ×r b ⇒ b
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

  η : eFunctor C freeProd
  fun η a = [ a ]
  mor η f = [ f ] , t-[] f
  resp η p = t-[]-cong p
  id-mor η = t-~-sym (t-[]-id)
  comp-mor η = t-~-sym t-[]-comp

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
    open module EqR {a b} = EqRelReason (deq {a} {b})

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
      begin
        id D ∘d homMap pf0
      ≈⟨ id-l D ⟩
        homMap pf0
      ≈⟨ homMapIrr pf0 pf1 ⟩
        homMap pf1
      ∎
    ~Map (t-compr pf0 (t-id a)) pf1 (t-idr-r x) =
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
      begin
        pp ∘d ⟨ homMap pf0 , homMap pg0 ⟩
      ≈⟨ ⟨⟩-β-fst ⟩
        homMap pf0
      ≈⟨ homMapIrr pf0 pf1 ⟩
        homMap pf1
      ∎
    ~Map (t-compr t-qqr (t-⟨⟩r pf0 pg0)) pg1 t-⟨⟩-β-snd =
      begin
        qq ∘d ⟨ homMap pf0 , homMap pg0 ⟩
      ≈⟨ ⟨⟩-β-snd ⟩
        homMap pg0
      ≈⟨ homMapIrr pg0 pg1 ⟩
        homMap pg1
      ∎
    ~Map pf0 (t-⟨⟩r (t-compr t-ppr pf1) (t-compr t-qqr pf2)) t-⟨⟩-η =
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
      ∀ {a b : Obj} → let open module M = hasProducts freeprod-has-products
                      in isProduct D (fun free-elim (M.prod a b))
                           (mor free-elim (M.pp {a} {b}))
                           (mor free-elim (M.qq {a} {b}))
    free-elim-preserves-product-str = is-product

    elim-commute : eNatIso (free-elim ∘Func η) F
    elim-commute = let eta : eNatIso F F
                       eta = iso-natiso iso-refl
      in record
      { to-nat = record
        { nat = eta .to-nat .nat
        ; nat-eq = λ {a} {b} {f} → eta .to-nat .nat-eq {f = f} }
      ; to-is-iso = record { nat-inv = eta .to-is-iso .isNatIso.nat-inv
                           ; nat-inv-sect = λ {a} →
                             eta .to-is-iso .isNatIso.nat-inv-sect {a}
                           ; nat-inv-retract = λ {a} →
                             eta .to-is-iso .isNatIso.nat-inv-retract {a = a}
                           }
      }

    module _ (G : eFunctor freeProd D) (G-prod : preserves-products G)
             (α : eNatIso (G ∘Func η) F) where

      -- TODO: clean this mess
      fwd-nat : (a : Obj) → hom D (fun free-elim a) (fun G a)
      fwd-nat [ x ] = α .from-nat x
      fwd-nat (a ×r b) =
        let open module M = hasProducts freeprod-has-products
              renaming ( pp to pp' ; qq to qq' )
            gab : isProduct D (fun G (a ×r b)) (mor G pp') (mor G qq')
            gab = G-prod M.is-product
            open isProduct gab using () renaming ( ⟨_,_⟩ to g⟨_,_⟩ )
        in g⟨ fwd-nat a ∘d pp , fwd-nat b ∘d qq ⟩

      fwd-nat-eq : ∀ {a b f} (pf : f ∈ a ⇒ b) →
                     (mor G (f , pf) ∘d fwd-nat a) ~d (fwd-nat b ∘d (homMap pf))
      fwd-nat-eq (t-[] {a} {b} r) = let αiso = natiso-iso α in αiso .from-mor .nat-eq
      fwd-nat-eq (t-id a) =
        begin
          mor G (id freeProd) ∘d fwd-nat a
        ≈⟨ comp-cong-l D (id-mor-inv G) ⟩
          id D ∘d fwd-nat a
        ≈⟨ id-l D ⟩
          fwd-nat a
        ≈⟨ id-r-inv D ⟩
          fwd-nat a ∘d id D
        ∎
      fwd-nat-eq (t-compr {f} {g} {a} {b} {c} pf pg) =
        begin
          mor G (compr _ f g , t-compr pf pg) ∘d fwd-nat a
        ≈⟨ comp-cong-l D (comp-mor-inv G) ⟩
          (mor G (f , pf) ∘d mor G (g , pg))∘d fwd-nat a
        ≈⟨ comp-assoc-inv D ⟩
          mor G (f , pf) ∘d (mor G (g , pg)∘d fwd-nat a)
        ≈⟨ comp-cong-r D (fwd-nat-eq pg) ⟩ -- IH g
          mor G (f , pf) ∘d (fwd-nat b ∘d homMap pg)
        ≈⟨ comp-assoc D ⟩
          (mor G (f , pf) ∘d fwd-nat b) ∘d homMap pg
        ≈⟨ comp-cong-l D (fwd-nat-eq pf) ⟩ -- IH f
          (fwd-nat c ∘d homMap pf) ∘d homMap pg
        ≈⟨ comp-assoc-inv D ⟩
          fwd-nat c ∘d (homMap pf ∘d homMap pg)
        ∎
      fwd-nat-eq (t-ppr {a} {b}) =
        let open isProduct (G-prod (hasProducts.is-product freeprod-has-products))
              renaming (⟨_,_⟩ to g⟨_,_⟩ ; ⟨⟩-β-fst to g-fst)
        in begin
          mor G (ppr a b , t-ppr {a} {b}) ∘d fwd-nat (a ×r b)
        ≈⟨⟩
          mor G (ppr a b , t-ppr) ∘d g⟨ fwd-nat a ∘d pp , fwd-nat b ∘d qq ⟩
        ≈⟨ g-fst ⟩
          fwd-nat a ∘d pp
        ∎
      fwd-nat-eq t-qqr = -- likewise
        let open isProduct (G-prod (hasProducts.is-product freeprod-has-products))
              renaming (⟨⟩-β-snd to g-snd)
        in g-snd

      fwd-nat-eq (t-⟨⟩r {a} {b} {c} {f} {g} pf pg) =
        let open isProduct (G-prod (hasProducts.is-product freeprod-has-products))
              renaming (⟨_,_⟩ to g⟨_,_⟩ ; ⟨⟩-comp to g⟨⟩-comp ; ⟨⟩-cong to g⟨⟩-cong
                       ; ⟨⟩-β-fst to g-fst ; ⟨⟩-β-snd to g-snd ; ⟨⟩-η' to g-η)
            open hasProducts freeprod-has-products using ()
              renaming (pp to pp' ; qq to qq' ; ⟨⟩-β-fst to fp-fst ; ⟨⟩-β-snd to fp-snd)
            open ECat freeProd using () renaming (comp to _∘fp_)
            lem1 = begin
                     mor G pp' ∘d mor G (⟨ f , g ⟩r , t-⟨⟩r pf pg)
                   ≈⟨ comp-mor G ⟩
                     mor G (pp' ∘fp (⟨ f , g ⟩r , t-⟨⟩r pf pg))
                   ≈⟨ resp G (fp-fst {f = f , pf} {g = g , pg}) ⟩
                     mor G (f , pf)
                   ≈⟨ deq .sym g-fst ⟩
                     mor G pp' ∘d g⟨ mor G (f , pf) , mor G (g ,  pg) ⟩
                   ∎
            lem2 = begin
                     mor G qq' ∘d mor G (⟨ f , g ⟩r , t-⟨⟩r pf pg)
                   ≈⟨ comp-mor G ⟩
                     mor G (qq' ∘fp (⟨ f , g ⟩r , t-⟨⟩r pf pg))
                   ≈⟨ resp G (fp-snd {f = f , pf} {g = g , pg}) ⟩
                     mor G (g , pg)
                   ≈⟨ deq .sym g-snd ⟩
                     mor G qq' ∘d g⟨ mor G (f , pf) , mor G (g ,  pg) ⟩
                   ∎
        in begin
          mor G (⟨ f , g ⟩r , t-⟨⟩r pf pg) ∘d fwd-nat c
        ≈⟨ comp-cong-l D (g-η lem1 lem2) ⟩
          g⟨ mor G (f , pf) , mor G (g ,  pg) ⟩ ∘d fwd-nat c
        ≈⟨ g⟨⟩-comp ⟩
          g⟨ mor G (f , pf) ∘d fwd-nat c , mor G (g ,  pg) ∘d fwd-nat c ⟩
        ≈⟨ g⟨⟩-cong (fwd-nat-eq pf) (fwd-nat-eq pg) ⟩
          g⟨ fwd-nat a ∘d homMap pf , fwd-nat b ∘d homMap pg ⟩
        ≈⟨ deq .sym (g⟨⟩-cong (comp-cong-r D ⟨⟩-β-fst) (comp-cong-r D ⟨⟩-β-snd)) ⟩
          g⟨ fwd-nat a ∘d (pp ∘d ⟨ homMap pf , homMap pg ⟩)
           , fwd-nat b ∘d (qq ∘d ⟨ homMap pf , homMap pg ⟩) ⟩
        ≈⟨ g⟨⟩-cong (comp-assoc D) (comp-assoc D) ⟩
          g⟨ (fwd-nat a ∘d pp) ∘d ⟨ homMap pf , homMap pg ⟩
           , (fwd-nat b ∘d qq) ∘d ⟨ homMap pf , homMap pg ⟩ ⟩
        ≈⟨ deq .sym g⟨⟩-comp ⟩
          g⟨ fwd-nat a ∘d pp , fwd-nat b ∘d qq ⟩ ∘d ⟨ homMap pf , homMap pg ⟩
        ∎


      bwd-nat : (a : Obj) → hom D (fun G a) (fun free-elim a)
      bwd-nat [ x ] = α .to-nat .nat x
      bwd-nat (a ×r b) = ⟨ bwd-nat a ∘d mor G pp' , bwd-nat b ∘d mor G qq' ⟩
        where open module M = hasProducts freeprod-has-products
                                using () renaming (  pp to pp' ; qq to qq' )

      fwd-bwd-id : (a : Obj) → (fwd-nat a ∘d bwd-nat a) ~d id D
      fwd-bwd-id [ _ ] = α .ptw-from-to-id
      fwd-bwd-id (a ×r b) =
        begin  -- TODO: can we somehow use products-unique?
          g⟨ fwd-nat a ∘d pp , fwd-nat b ∘d qq ⟩ ∘d
            ⟨ bwd-nat a ∘d mor G pp' , bwd-nat b ∘d mor G qq' ⟩
        ≈⟨ g-comp ⟩
          g⟨ (fwd-nat a ∘d pp) ∘d ⟨ bwd-nat a ∘d mor G pp' , bwd-nat b ∘d mor G qq' ⟩
           , (fwd-nat b ∘d qq) ∘d ⟨ bwd-nat a ∘d mor G pp' , bwd-nat b ∘d mor G qq' ⟩ ⟩
        ≈⟨ g-cong (comp-assoc-inv D) (comp-assoc-inv D) ⟩
          g⟨ fwd-nat a ∘d (pp ∘d ⟨ bwd-nat a ∘d mor G pp' , bwd-nat b ∘d mor G qq' ⟩)
           , fwd-nat b ∘d (qq ∘d ⟨ bwd-nat a ∘d mor G pp' , bwd-nat b ∘d mor G qq' ⟩) ⟩
        ≈⟨ g-cong (comp-cong-r D ⟨⟩-β-fst) (comp-cong-r D ⟨⟩-β-snd) ⟩
          g⟨ fwd-nat a ∘d (bwd-nat a ∘d mor G pp')
           , fwd-nat b ∘d (bwd-nat b ∘d mor G qq') ⟩
        ≈⟨ g-cong (comp-assoc D) (comp-assoc D) ⟩
          g⟨ (fwd-nat a ∘d bwd-nat a) ∘d mor G pp'
           , (fwd-nat b ∘d bwd-nat b) ∘d mor G qq' ⟩
        ≈⟨ g-cong (comp-cong-l D (fwd-bwd-id a)) (comp-cong-l D (fwd-bwd-id b)) ⟩
          g⟨ id D ∘d mor G pp' , id D ∘d mor G qq' ⟩
        ≈⟨ g-cong (id-l D) (id-l D) ⟩
          g⟨ mor G pp' , mor G qq' ⟩
        ≈⟨ g-η-id ⟩
          id D
        ∎
        where open module M = hasProducts freeprod-has-products
                                using () renaming (  pp to pp' ; qq to qq' )
              gab : isProduct D (fun G (a ×r b)) (mor G pp') (mor G qq')
              gab = G-prod M.is-product
              open isProduct gab using () renaming
                (⟨_,_⟩ to g⟨_,_⟩ ; ⟨⟩-comp to g-comp ; ⟨⟩-cong to g-cong
                ; ⟨⟩-η-id to g-η-id)

      bwd-fwd-id : (a : Obj) → (bwd-nat a ∘d fwd-nat a) ~d id D
      bwd-fwd-id [ _ ] = α .ptw-to-from-id
      bwd-fwd-id (a ×r b) =
        begin  -- TODO: can we somehow use products-unique?
           ⟨ bwd-nat a ∘d mor G pp' , bwd-nat b ∘d mor G qq' ⟩ ∘d
            g⟨ fwd-nat a ∘d pp , fwd-nat b ∘d qq ⟩
        ≈⟨ ⟨⟩-comp ⟩
           ⟨ (bwd-nat a ∘d mor G pp') ∘d g⟨ fwd-nat a ∘d pp , fwd-nat b ∘d qq ⟩
           , (bwd-nat b ∘d mor G qq') ∘d g⟨ fwd-nat a ∘d pp , fwd-nat b ∘d qq ⟩ ⟩
        ≈⟨ ⟨⟩-cong (comp-assoc-inv D) (comp-assoc-inv D) ⟩
           ⟨ bwd-nat a ∘d (mor G pp' ∘d g⟨ fwd-nat a ∘d pp , fwd-nat b ∘d qq ⟩)
           , bwd-nat b ∘d (mor G qq' ∘d g⟨ fwd-nat a ∘d pp , fwd-nat b ∘d qq ⟩)⟩
        ≈⟨ ⟨⟩-cong (comp-cong-r D g-fst) (comp-cong-r D g-snd) ⟩
           ⟨ bwd-nat a ∘d (fwd-nat a ∘d pp) , bwd-nat b ∘d (fwd-nat b ∘d qq)⟩
        ≈⟨ ⟨⟩-cong (comp-assoc D) (comp-assoc D) ⟩
           ⟨ (bwd-nat a ∘d fwd-nat a) ∘d pp , (bwd-nat b ∘d fwd-nat b) ∘d qq ⟩
        ≈⟨ ⟨⟩-cong (comp-cong-l D (bwd-fwd-id a)) (comp-cong-l D (bwd-fwd-id b)) ⟩
           ⟨ id D ∘d pp , id D ∘d qq ⟩
        ≈⟨ ⟨⟩-cong (id-l D) (id-l D) ⟩
           ⟨ pp , qq ⟩
        ≈⟨ ⟨⟩-η-id ⟩
          id D
        ∎
        where open module M = hasProducts freeprod-has-products
                                using () renaming (  pp to pp' ; qq to qq' )
              gab : isProduct D (fun G (a ×r b)) (mor G pp') (mor G qq')
              gab = G-prod M.is-product
              open isProduct gab using () renaming
                (⟨_,_⟩ to g⟨_,_⟩ ; ⟨⟩-β-fst to g-fst ; ⟨⟩-β-snd to g-snd)


      free-elim-unique : eNatIso free-elim G
      free-elim-unique = record
        { to-nat = record { nat = fwd-nat ; nat-eq = fwd-nat-eq _ }
        ; to-is-iso = record
          { nat-inv = bwd-nat
          ; nat-inv-sect = fwd-bwd-id _
          ; nat-inv-retract = bwd-fwd-id _
          }
        }
