{-# OPTIONS --with-K #-}
-- TODO: can we typecheck this w/o K?
-- {-# OPTIONS --without-K #-}
module Syntax.ExplicitExtrinsic.Initial where

open import Basics
open import Presheaves
open import Cwf.Elem
open import Products using (isTerminal)

-- open import Equality renaming (refl to ≡-refl)

-- to make type-checking faster
postulate
  BLOCK : ∀ {l} {A : Set l} → A

-- TODO: is there any way to not require lzero?  (The syntax has to be
-- generalized.)
module Elim {ks kr lo lh lr : Level}
  (E : eCwF {lzero} {lzero} {lo} {lh} {lr}) where

  -- --open import Syntax.ExplicitExtrinsic {lzero}
  -- import Syntax.ExplicitExtrinsic
  -- open Syntax.ExplicitExtrinsic {lzero}
  open import Syntax.ExplicitExtrinsic


  open eCwF

  module Notation {ks kr lo lh lr} (H : eCwF {ks} {kr} {lo} {lh} {lr}) =
    eCwFNotation {Ctx = Ctx H} (Ty H) (Tm H)

  open Notation E renaming
    ( _~_ to _~E_ ; Typ to TypE
    ; _∘s_ to _∘E_
    ; Ter to TerE ; _[_] to _[_]E
    ; ids to idsE ; _[_]t to _[_]tE
    )
  open Notation SynCwf using () renaming (_~_ to _~S_ ; _~s_ to _~sS_ ; Typ to TypS ; _[_] to _[_]S)

  open eCwF E using () renaming (_∙_ to _∙E_ ; <_,_> to <_,_>E ; pp to ppE ; qq to qqE ; ! to !E)

  -- TODO This doesn't really work :-( (probably because of the 'eCwF.compr E')
  -- {-# DISPLAY eCwF.compr E .isTerminal.! {_ , σ , t} .fst = < σ , t >E #-}
  -- {-# DISPLAY eCwF.compr E .isTerminal.! {x} .fst = < snd (fst x) , snd (snd x) >E #-}
  -- {-# DISPLAY isTerminal.!-explicit (eCwF.compr E) (x , σ , t) .fst = < σ , t >E #-}


  mutual -- the interpretation
    -- NEEDED
    o : ∀ {Γ} → Γ ⊢ → obj (Ctx E)
    -- Ind(Γ ⊢).
    o ctx-nil = <> E
    o (ctx-cons pΓ pA) = o pΓ ∙E ty pΓ pA
    -- I wonder if the termination checker would accept: (o (ty-ctx pA)) ∙E ..

    -- ??
    -- o# : ∀ {Γ} (pΓ pΓ' :  Γ ⊢) → o pΓ ≡ o pΓ'
    -- o# ctx-nil ctx-nil = ≡-refl
    -- o# (ctx-cons pΓ pA) (ctx-cons pΓ' pA') = {!!}
    -- the problem with this is that type equality (~E) isn't
    -- necessarily equality

    -- Maybe it is still feasible to formulate o# as an iso?
    -- But this has to be in a way compatible with ty# etc.
    o# : ∀ {Γ} (pΓ pΓ' :  Γ ⊢) → hom (Ctx E) (o pΓ) (o pΓ')
    -- Ind(pΓ : Γ ⊢ , pΓ' : Γ ⊢).
    o# ctx-nil ctx-nil = id (Ctx E)
    o# (ctx-cons pΓ pA) (ctx-cons pΓ' pA') =
      < o# pΓ pΓ' ∘E ppE
      , (let open EqRelReason ~eq
             eq = begin
                    ty pΓ pA [ ppE ]E
                  ≈⟨ []-resp-l (ty# pΓ pΓ' pA pA') ⟩
                    ty pΓ' pA' [ o# pΓ pΓ' ]E [ ppE ]E
                  ≈⟨ []-assoc ⟩
                    ty pΓ' pA' [ o# pΓ pΓ' ∘E ppE ]E
                  ∎
         in ι' eq qqE)
      >E

    -- NEEDED (depending on what to do with independence of context derivations)
    o#id : ∀ {Γ} (pΓ : Γ ⊢) → idsE ~s o# pΓ pΓ
    -- Ind(pΓ : Γ ⊢).
    o#id = BLOCK
    -- o#id ctx-nil = ~seq .refl
    -- o#id (ctx-cons pΓ pA) =
    --   let IH : idsE ~s o# pΓ pΓ
    --       IH = o#id pΓ
    --       left = let open EqRelReason ~seq in
    --              begin
    --                ppE
    --              ≈⟨ id-l-inv (Ctx E) ⟩
    --                idsE ∘E ppE
    --              ≈⟨ comp-cong-l (Ctx E) IH ⟩
    --                o# pΓ pΓ ∘E ppE
    --              ∎
    --       right = let open EqRelReason ~teq in
    --               begin
    --                 qqE
    --               ≈⟨ ιrefl ⟩
    --                 ι _ qqE
    --               ≈⟨ ιirr ⟩
    --                 ι _ qqE
    --               ≈⟨ ~teq .sym ιtrans ⟩
    --                 ι _ (ι' _ qqE)
    --               ∎
    --   in ~seq .trans (<>-η-id E) (<>-cong E left right)

    -- we most likely also need:
    o#comp : ∀ {Γ} (pΓ pΓ' pΓ'' : Γ ⊢) → o# pΓ' pΓ'' ∘E o# pΓ pΓ' ~s o# pΓ pΓ''
    -- Ind(pΓ pΓ' pΓ'' : Γ ⊢).
    o#comp = BLOCK
    -- o#comp ctx-nil ctx-nil ctx-nil = id-l (Ctx E)
    -- o#comp (ctx-cons pΓ pA) (ctx-cons pΓ' pA') (ctx-cons pΓ'' pA'') =
    --   let o#ΓAΓA' = o# (ctx-cons pΓ pA) (ctx-cons pΓ' pA')
    --       lefteq = let open EqRelReason ~seq in
    --                begin
    --                  (o# pΓ' pΓ'' ∘E ppE) ∘E o#ΓAΓA'
    --                ≈⟨ comp-assoc-inv (Ctx E) ⟩
    --                  o# pΓ' pΓ'' ∘E (ppE ∘E o#ΓAΓA')
    --                ≈⟨ comp-cong-r (Ctx E) (pp<> E) ⟩
    --                  o# pΓ' pΓ'' ∘E (o# pΓ pΓ' ∘E ppE)
    --                ≈⟨ comp-assoc (Ctx E) ⟩
    --                  (o# pΓ' pΓ'' ∘E o# pΓ pΓ') ∘E ppE
    --                ≈⟨ comp-cong-l (Ctx E) (o#comp pΓ pΓ' pΓ'') ⟩ -- IH
    --                  o# pΓ pΓ'' ∘E ppE
    --                ∎
    --       righteq = let open EqRelReason ~teq in
    --                 begin
    --                   ι' []-assoc ((ι _ qqE) [ o#ΓAΓA' ]tE)
    --                 ≈⟨ ιresp ιsubst ⟩
    --                   ι' []-assoc (ι _ (qqE [ o#ΓAΓA' ]tE))
    --                 ≈⟨ ιresp (ιresp (qq<> E)) ⟩
    --                   ι' []-assoc (ι _ (ι _ (ι _ qqE)))
    --                 ≈⟨ ~teq .trans ιtrans (~teq .trans ιtrans ιtrans) ⟩
    --                   ι _ qqE
    --                 ≈⟨ ιirr ⟩
    --                   ι _ qqE
    --                 ≈⟨ ιtrans-inv ⟩
    --                   ι ([]-resp-r lefteq) (ι _ qqE)
    --                 ∎
    --       open EqRelReason ~seq
    --   in begin
    --     < o# pΓ' pΓ'' ∘E ppE , ι' _ qqE >E ∘E o#ΓAΓA'
    --   ≈⟨ <>-comp E ⟩
    --     < (o# pΓ' pΓ'' ∘E ppE) ∘E o#ΓAΓA' , ι' []-assoc ((ι' _ qqE) [ o#ΓAΓA' ]tE) >E
    --   ≈⟨ <>-cong E lefteq righteq ⟩
    --     < o# pΓ pΓ'' ∘E ppE , ι _ qqE >E
    --   ∎

    -- NEEDED
    m : ∀ {Δ Γ σ} (pΔ : Δ ⊢) (pΓ : Γ ⊢) (pσ : σ ∈ Δ ⇒ Γ) →
        hom (Ctx E) (o pΔ) (o pΓ)
    -- for id, have  pΓ pΓ' : Γ ⊢, want morphism o pΓ to  pΓ'
    -- Ind(pσ : σ ∈ Δ ⇒ Γ).
    m pΔ pΓ (subst-pp pA) = ppE ∘E o# pΔ (ctx-cons pΓ pA)
    m pΔ pΓ (subst-! pΔ') = o# ctx-nil pΓ ∘E !E
    m pΔ (ctx-cons pΓ pA') (subst-<> pσ pA pt) =
       < m pΔ pΓ pσ , ι (subst-ty pΔ pΓ pσ pA') (ter pΔ (ty-subst pΓ pA' pσ) pt) >E
    m pΔ pΓ (subst-id pΔ') = o# pΔ pΓ -- hmm
    m pΔ pΓ (subst-comp pΞ pσ pτ) = m pΞ pΓ pσ ∘E m pΔ pΞ pτ


    -- Combine with m#?  This is needed there, but m-o# looks at least
    -- as painful?  It feels like treating o# as isomorphisms is
    -- *really* cumbersome, but this probably was to be expected..
    m-o# : ∀ {Δ Γ σ} (pΔ pΔ' : Δ ⊢) (pΓ pΓ' : Γ ⊢) (pσ : σ ∈ Δ ⇒ Γ) →
           m pΔ pΓ pσ ∘E o# pΔ' pΔ ~s o# pΓ' pΓ ∘E m pΔ' pΓ' pσ
    -- Ind(pσ : σ ∈ Δ ⇒ Γ).  Maybe doing an induction on Δ might
    -- actually be more direct, and maybe split it up in two?
    m-o# = BLOCK
    -- m-o# pΔ pΔ' pΓ pΓ' (subst-! x) =
    --   let open EqRelReason ~seq in
    --   begin
    --     o# ctx-nil pΓ ∘E !E ∘E o# pΔ' pΔ
    --   ≈⟨ comp-assoc-inv (Ctx E) ⟩
    --     o# ctx-nil pΓ ∘E (!E ∘E o# pΔ' pΔ)
    --   ≈⟨ comp-cong-r (Ctx E) (!-unique E) ⟩
    --     o# ctx-nil pΓ ∘E !E
    --   ≈⟨ comp-cong-l (Ctx E) (~seq .sym (o#comp ctx-nil pΓ' pΓ)) ⟩
    --     (o# pΓ' pΓ ∘E o# ctx-nil pΓ') ∘E !E
    --   ≈⟨ comp-assoc-inv (Ctx E) ⟩
    --     o# pΓ' pΓ ∘E (o# ctx-nil pΓ' ∘E !E)
    --   ∎
    -- m-o# pΔ pΔ' (ctx-cons pΓ pA) (ctx-cons pΓ' pA') (subst-<> pσ pA'' pt) =
    --   let open EqRelReason ~seq in
    --   begin
    --     < m pΔ pΓ pσ
    --     , ι (subst-ty pΔ pΓ pσ pA) (ter pΔ (ty-subst pΓ pA pσ) pt) >E ∘E o# pΔ' pΔ
    --   ≈⟨ <>-comp E ⟩
    --     < m pΔ pΓ pσ ∘E o# pΔ' pΔ
    --     , ι' []-assoc ((ι (subst-ty pΔ pΓ pσ pA) (ter pΔ (ty-subst pΓ pA pσ) pt))
    --                       [ o# pΔ' pΔ ]tE) >E
    --   ≈⟨ <>-cong E  (m-o# pΔ pΔ' pΓ pΓ' pσ)
    --        (~teq .trans (ιresp ιsubst)
    --          (~teq .trans ιtrans (~teq .sym (~teq .trans ιtrans ιirr)))) ⟩
    --     < o# pΓ' pΓ ∘E m pΔ' pΓ' pσ
    --     , ι _ (ter pΔ (ty-subst pΓ pA pσ) pt [ o# pΔ' pΔ ]tE) >E
    --   ≈⟨ <>-cong-r E (~teq .sym (~teq .trans
    --        (ιresp (ter# pΔ' pΔ (ty-subst pΓ' pA' pσ) (ty-subst pΓ pA pσ) pt pt))
    --        ιtrans)) ⟩
    --     < o# pΓ' pΓ ∘E m pΔ' pΓ' pσ
    --     , ι _ (ter pΔ' (ty-subst pΓ' pA' pσ) pt)
    --     >E
    --   ≈⟨ <>-cong E (comp-cong-r (Ctx E) (pp<>-inv E))
    --        (~teq .sym (~teq .trans (ιresp (ιresp (qq<> E)))
    --          (~teq .trans ιtrans (~teq .trans ιtrans ιtrans)))) ⟩
    --     < o# pΓ' pΓ ∘E (ppE ∘E
    --         < m pΔ' pΓ' pσ , ι (subst-ty pΔ' pΓ' pσ pA')
    --                             (ter pΔ' (ty-subst pΓ' pA' pσ) pt) >E)
    --     , ι _ (qqE [ < m pΔ' pΓ' pσ
    --                  , ι (subst-ty pΔ' pΓ' pσ pA')
    --                      (ter pΔ' (ty-subst pΓ' pA' pσ) pt) >E ]tE)
    --     >E
    --   ≈⟨ <>-cong E (comp-assoc (Ctx E))
    --      (~teq .trans (~teq .trans ιtrans-inv
    --        (~teq .sym (ιresp ιsubst))) ιtrans-inv) ⟩
    --     < o# pΓ' pΓ ∘E ppE ∘E
    --         < m pΔ' pΓ' pσ
    --         , ι (subst-ty pΔ' pΓ' pσ pA') (ter pΔ' (ty-subst pΓ' pA' pσ) pt) >E
    --     , ι' []-assoc ((ι' _ qqE)
    --         [ < m pΔ' pΓ' pσ
    --           , ι (subst-ty pΔ' pΓ' pσ pA') (ter pΔ' (ty-subst pΓ' pA' pσ) pt) >E ]tE)
    --     >E
    --   ≈⟨ ~seq .sym (<>-comp E) ⟩
    --     < o# pΓ' pΓ ∘E ppE , ι' _ qqE >E ∘E
    --      < m pΔ' pΓ' pσ , ι _ (ter pΔ' (ty-subst pΓ' pA' pσ) pt) >E
    --   ∎
    -- m-o# pΔ pΔ' pΓ pΓ' (subst-id x) =
    --   let open EqRelReason ~seq in
    --   begin
    --     o# pΔ pΓ ∘E o# pΔ' pΔ
    --   ≈⟨ o#comp  pΔ' pΔ pΓ ⟩
    --     o# pΔ' pΓ
    --   ≈⟨ ~seq .sym (o#comp pΔ' pΓ' pΓ) ⟩
    --     o# pΓ' pΓ ∘E o# pΔ' pΓ'
    --   ∎
    -- m-o# pΔ pΔ' pΓ pΓ' (subst-comp pΞ pσ pτ) =
    --   let open EqRelReason ~seq in
    --   begin
    --     m pΞ pΓ pσ ∘E m pΔ pΞ pτ ∘E o# pΔ' pΔ
    --   ≈⟨ comp-assoc-inv (Ctx E) ⟩
    --     m pΞ pΓ pσ ∘E (m pΔ pΞ pτ ∘E o# pΔ' pΔ)
    --   ≈⟨ comp-cong-r (Ctx E) (m-o# pΔ pΔ' pΞ pΞ pτ) ⟩
    --     m pΞ pΓ pσ ∘E (o# pΞ pΞ ∘E m pΔ' pΞ pτ)
    --   ≈⟨ comp-assoc (Ctx E) ⟩
    --     (m pΞ pΓ pσ ∘E o# pΞ pΞ) ∘E m pΔ' pΞ pτ
    --   ≈⟨ comp-cong-l (Ctx E) (m-o# pΞ pΞ pΓ pΓ' pσ) ⟩
    --     (o# pΓ' pΓ ∘E m pΞ pΓ' pσ) ∘E m pΔ' pΞ pτ
    --   ≈⟨ comp-assoc-inv (Ctx E) ⟩
    --     o# pΓ' pΓ ∘E (m pΞ pΓ' pσ ∘E m pΔ' pΞ pτ)
    --   ∎
    -- m-o# (ctx-cons pΔ pA) (ctx-cons pΔ' pA') pΓ pΓ' (subst-pp pA'') =
    --   let open EqRelReason ~seq in
    --   begin
    --     ppE ∘E < o# pΔ pΓ ∘E ppE , _ >E ∘E < o# pΔ' pΔ ∘E ppE , _ >E
    --   ≈⟨ comp-cong-l (Ctx E) (pp<> E) ⟩
    --     o# pΔ pΓ ∘E ppE ∘E < o# pΔ' pΔ ∘E ppE , _ >E
    --   ≈⟨ comp-assoc-inv (Ctx E) ⟩
    --     o# pΔ pΓ ∘E (ppE ∘E < o# pΔ' pΔ ∘E ppE , _ >E)
    --   ≈⟨ comp-cong-r (Ctx E) (pp<> E) ⟩
    --     o# pΔ pΓ ∘E (o# pΔ' pΔ ∘E ppE)
    --   ≈⟨ comp-assoc (Ctx E) ⟩
    --     (o# pΔ pΓ ∘E o# pΔ' pΔ) ∘E ppE
    --   ≈⟨ comp-cong-l (Ctx E) (o#comp pΔ' pΔ pΓ) ⟩
    --     o# pΔ' pΓ ∘E ppE
    --   ≈⟨ comp-cong-l (Ctx E) (~seq .sym (o#comp pΔ' pΓ' pΓ)) ⟩
    --     (o# pΓ' pΓ ∘E o# pΔ' pΓ') ∘E ppE
    --   ≈⟨ comp-assoc-inv (Ctx E) ⟩
    --     o# pΓ' pΓ ∘E (o# pΔ' pΓ' ∘E ppE)
    --   ≈⟨ comp-cong-r (Ctx E) (pp<>-inv E) ⟩
    --     o# pΓ' pΓ ∘E (ppE ∘E < o# pΔ' pΓ' ∘E ppE , _ >E)
    --   ∎

    -- Some consequences..
    m-o#-l : ∀ {Δ Γ σ} (pΔ : Δ ⊢) (pΓ pΓ' : Γ ⊢) (pσ : σ ∈ Δ ⇒ Γ) →
             m pΔ pΓ pσ ~s o# pΓ' pΓ ∘E m pΔ pΓ' pσ
    m-o#-l = BLOCK

    m-o#-r : ∀ {Δ Γ σ} (pΔ pΔ' : Δ ⊢) (pΓ : Γ ⊢) (pσ : σ ∈ Δ ⇒ Γ) →
             m pΔ pΓ pσ ~s m pΔ' pΓ pσ ∘E o# pΔ pΔ'
    m-o#-r = BLOCK

    m-o#-lr : ∀ {Δ Γ σ} (pΔ pΔ' : Δ ⊢) (pΓ pΓ' : Γ ⊢) (pσ : σ ∈ Δ ⇒ Γ) →
            m pΔ pΓ pσ ~s o# pΓ' pΓ ∘E m pΔ' pΓ' pσ ∘E o# pΔ pΔ'
    m-o#-lr = BLOCK


    -- note that this is also needed in the refl case of m-resp
    m# : ∀ {Δ Γ σ} (pΔ : Δ ⊢) (pΓ : Γ ⊢)
         (pσ pσ' : σ ∈ Δ ⇒ Γ) → m pΔ pΓ pσ ~s m pΔ pΓ pσ'
    -- Ind(pσ pσ': σ ∈ Δ ⇒ Γ).
    m# = BLOCK
    -- m# pΔ pΓ (subst-! pΔ') (subst-! pΔ'') = ~seq .refl
    -- m# pΔ (ctx-cons pΓ pA) (subst-<> pσ pA'' pt'') (subst-<> pσ' pA' pt') =
    --   let right = let open EqRelReason ~teq in
    --               begin
    --                 ι (subst-ty pΔ pΓ pσ pA) (ter pΔ (ty-subst pΓ pA pσ) pt'')
    --               ≈⟨ ιresp (ter#r pΔ (ty-subst pΓ pA pσ) pt'' pt') ⟩
    --                 ι (subst-ty pΔ pΓ pσ pA) (ter pΔ (ty-subst pΓ pA pσ) pt')
    --               ≈⟨ ιresp (ter#m pΔ (ty-subst pΓ pA pσ) (ty-subst pΓ pA pσ') pt') ⟩
    --                 ι (subst-ty pΔ pΓ pσ pA) (ι _ (ter pΔ (ty-subst pΓ pA pσ') pt'))
    --               ≈⟨ ιtrans ⟩
    --                 ι _ (ter pΔ (ty-subst pΓ pA pσ') pt')
    --               ≈⟨ ιirr ⟩
    --                 ι _ (ter pΔ (ty-subst pΓ pA pσ') pt')
    --               ≈⟨ ιtrans-inv ⟩
    --                 ι ([]-resp-r (m# pΔ pΓ pσ pσ'))
    --                   (ι (subst-ty pΔ pΓ pσ' pA) (ter pΔ (ty-subst pΓ pA pσ') pt'))
    --               ∎
    --   in <>-cong E (m# pΔ pΓ pσ pσ') right
    -- m# pΔ pΓ (subst-id _) (subst-id _) = ~seq .refl
    -- m# {Δ} {Γ} {comps Ξ σ τ} pΔ pΓ (subst-comp pΞ pσ pτ) (subst-comp pΞ' pσ' pτ') =
    --   -- here we need the comps annotation with the mediating object
    --   let open EqRelReason ~seq
    --   in begin
    --     m pΞ pΓ pσ ∘E m pΔ pΞ pτ
    --   ≈⟨ comp-cong (Ctx E) (id-l-inv (Ctx E)) (id-r-inv (Ctx E)) ⟩
    --     (idsE ∘E m pΞ pΓ pσ) ∘E (m pΔ pΞ pτ ∘E idsE)
    --   ≈⟨ comp-cong (Ctx E) (comp-cong-l (Ctx E) (o#id pΓ)) (comp-cong-r (Ctx E) (o#id pΔ)) ⟩
    --     (o# pΓ pΓ ∘E m pΞ pΓ pσ) ∘E (m pΔ pΞ pτ ∘E o# pΔ pΔ)
    --   ≈⟨ comp-cong (Ctx E) (~seq .sym (m-o# pΞ' pΞ pΓ pΓ pσ)) (m-o# pΔ pΔ pΞ pΞ' pτ) ⟩
    --     (m pΞ' pΓ pσ ∘E o# pΞ pΞ') ∘E (o# pΞ' pΞ ∘E m pΔ pΞ' pτ)
    --   ≈⟨ comp-assoc-inv (Ctx E) ⟩
    --     m pΞ' pΓ pσ ∘E (o# pΞ pΞ' ∘E (o# pΞ' pΞ ∘E m pΔ pΞ' pτ))
    --   ≈⟨ comp-cong-r (Ctx E) (comp-assoc (Ctx E)) ⟩
    --     m pΞ' pΓ pσ ∘E ((o# pΞ pΞ' ∘E o# pΞ' pΞ) ∘E m pΔ pΞ' pτ)
    --   ≈⟨ comp-cong-r (Ctx E) (comp-cong-l (Ctx E) (o#comp pΞ' pΞ pΞ')) ⟩
    --     m pΞ' pΓ pσ ∘E (o# pΞ' pΞ' ∘E m pΔ pΞ' pτ)
    --   ≈⟨ comp-cong-r (Ctx E) (comp-cong-l (Ctx E) (~seq .sym (o#id pΞ'))) ⟩
    --     m pΞ' pΓ pσ ∘E (idsE ∘E m pΔ pΞ' pτ)
    --   ≈⟨ comp-cong-r (Ctx E) (id-l (Ctx E)) ⟩
    --     m pΞ' pΓ pσ ∘E m pΔ pΞ' pτ
    --   ≈⟨ comp-cong (Ctx E) (m# pΞ' pΓ pσ pσ') (m# pΔ pΞ' pτ pτ') ⟩
    --     m pΞ' pΓ pσ' ∘E m pΔ pΞ' pτ'
    --   ∎
    -- m# (ctx-cons pΓ' pA'') pΓ (subst-pp pA) (subst-pp pA') = -- TODO: needs K?
    --   let open EqRelReason ~seq in
    --   begin
    --     ppE ∘E < o# pΓ' pΓ ∘E ppE , _ >E
    --   ≈⟨ pp<> E ⟩
    --     o# pΓ' pΓ ∘E ppE
    --   ≈⟨ pp<>-inv E ⟩
    --     ppE ∘E < o# pΓ' pΓ ∘E eCwF.pp E , _ >E
    --   ∎


    -- NEEDED
    m-resp : ∀ {Δ Γ σ τ} (pΔ : Δ ⊢) (pΓ : Γ ⊢) (pσ : σ ∈ Δ ⇒ Γ) (pτ : τ ∈ Δ ⇒ Γ)
           (pστ : σ ~ τ ∈ Δ ⇒ Γ) → m pΔ pΓ pσ ~s m pΔ pΓ pτ
    -- Ind(pστ : σ ~ τ ∈ Δ ⇒ Γ)
    m-resp pΔ pΓ
      (subst-comp (ctx-cons pΓ' pA) (subst-pp pA') (subst-<> pσ pA'' pt))
      pσ' (subst-eq-pp<> pσ'' pA''' pt') =
      BLOCK
      -- let open EqRelReason ~seq in
      -- begin
      --   ppE ∘E < o# pΓ' pΓ ∘E ppE , _ >E ∘E  < m pΔ pΓ' pσ , _ >E
      -- ≈⟨ comp-cong-l (Ctx E) (pp<> E) ⟩
      --   o# pΓ' pΓ ∘E ppE ∘E  < m pΔ pΓ' pσ , _ >E
      -- ≈⟨ comp-assoc-inv (Ctx E) ⟩
      --   o# pΓ' pΓ ∘E (ppE ∘E  < m pΔ pΓ' pσ , _ >E)
      -- ≈⟨ comp-cong-r (Ctx E) (pp<> E) ⟩
      --   o# pΓ' pΓ ∘E  m pΔ pΓ' pσ
      -- ≈⟨ ~seq .sym (m-o#-l pΔ pΓ pΓ' pσ) ⟩
      --   m pΔ pΓ pσ
      -- ≈⟨ m# pΔ pΓ pσ pσ' ⟩
      --   m pΔ pΓ pσ'
      -- ∎
    m-resp pΔ pΓ (subst-comp pΞ pσ (subst-comp pΘ pτ pξ))
                 (subst-comp pΘ' (subst-comp pΞ' pσ' pτ') pξ')
                 (subst-eq-assoc pσ'' pτ'' pξ'') = BLOCK
      -- let open EqRelReason ~seq in
      -- begin
      --   m pΞ pΓ pσ ∘E (m pΘ pΞ pτ ∘E m pΔ pΘ pξ)
      -- ≈⟨ comp-cong (Ctx E) (m# pΞ pΓ pσ pσ')
      --      (comp-cong (Ctx E) (m# pΘ pΞ pτ pτ') (m# pΔ pΘ pξ pξ')) ⟩
      --   m pΞ pΓ pσ' ∘E (m pΘ pΞ pτ' ∘E m pΔ pΘ pξ')
      -- ≈⟨ comp-cong (Ctx E) (m-o#-r pΞ pΞ' pΓ pσ')
      --      (comp-cong-r (Ctx E) (m-o#-l pΔ pΘ pΘ' pξ')) ⟩
      --   (m pΞ' pΓ pσ' ∘E o# pΞ pΞ') ∘E (m pΘ pΞ pτ' ∘E (o# pΘ' pΘ ∘E m pΔ pΘ' pξ'))
      -- ≈⟨ comp-cong-r (Ctx E) (comp-assoc (Ctx E)) ⟩
      --   (m pΞ' pΓ pσ' ∘E o# pΞ pΞ') ∘E ((m pΘ pΞ pτ' ∘E o# pΘ' pΘ) ∘E m pΔ pΘ' pξ')
      -- ≈⟨ comp-assoc-inv (Ctx E) ⟩
      --   m pΞ' pΓ pσ' ∘E (o# pΞ pΞ' ∘E ((m pΘ pΞ pτ' ∘E o# pΘ' pΘ) ∘E m pΔ pΘ' pξ'))
      -- ≈⟨ comp-cong-r (Ctx E) (comp-assoc (Ctx E)) ⟩
      --   m pΞ' pΓ pσ' ∘E ((o# pΞ pΞ' ∘E (m pΘ pΞ pτ' ∘E o# pΘ' pΘ)) ∘E m pΔ pΘ' pξ')
      -- ≈⟨ comp-assoc (Ctx E) ⟩
      --   (m pΞ' pΓ pσ' ∘E (o# pΞ pΞ' ∘E (m pΘ pΞ pτ' ∘E o# pΘ' pΘ))) ∘E m pΔ pΘ' pξ'
      -- ≈⟨ comp-cong-l (Ctx E) (comp-cong-r (Ctx E) (comp-assoc (Ctx E))) ⟩
      --   m pΞ' pΓ pσ' ∘E (o# pΞ pΞ' ∘E m pΘ pΞ pτ' ∘E o# pΘ' pΘ) ∘E m pΔ pΘ' pξ'
      -- ≈⟨ comp-cong-l (Ctx E) (comp-cong-r (Ctx E)
      --      (~seq .sym (m-o#-lr pΘ' pΘ pΞ' pΞ pτ'))) ⟩
      --   m pΞ' pΓ pσ' ∘E m pΘ' pΞ' pτ' ∘E m pΔ pΘ' pξ'
      -- ∎
    m-resp pΔ pΓ (subst-comp pΓ' (subst-id pΓ'') pτ) pτ' (subst-eq-id-l pτ'') = BLOCK
      -- let open EqRelReason ~seq in
      -- begin
      --   o# pΓ' pΓ ∘E m pΔ pΓ' pτ
      -- ≈⟨ comp-cong-r (Ctx E) (m# pΔ pΓ' pτ pτ') ⟩
      --   o# pΓ' pΓ ∘E m pΔ pΓ' pτ'
      -- ≈⟨ ~seq .sym (m-o#-l pΔ pΓ pΓ' pτ') ⟩
      --   m pΔ pΓ pτ'
      -- ∎
    m-resp pΔ pΓ (subst-comp pΔ' pσ (subst-id pΔ'')) pσ' (subst-eq-id-r pσ'') = BLOCK
      -- let open EqRelReason ~seq in
      -- begin
      --   m pΔ' pΓ pσ ∘E o# pΔ pΔ'
      -- ≈⟨ ~seq .sym (m-o#-r pΔ pΔ' pΓ pσ) ⟩
      --   m pΔ pΓ pσ
      -- ≈⟨ m# pΔ pΓ pσ pσ' ⟩
      --   m pΔ pΓ pσ'
      -- ∎
    m-resp pΔ pΓ (subst-comp pΞ pσ pτ) (subst-comp pΞ' pσ' pτ') (subst-eq-comp pΞ'' pσσ' pττ') =
      BLOCK
      -- let open EqRelReason ~seq in
      -- begin
      --   m pΞ pΓ pσ ∘E m pΔ pΞ pτ
      -- ≈⟨ comp-cong (Ctx E) (m-o#-r pΞ pΞ' pΓ pσ) (m-o#-l pΔ pΞ pΞ' pτ) ⟩
      --   (m pΞ' pΓ pσ ∘E o# pΞ pΞ')∘E (o# pΞ' pΞ ∘E m pΔ pΞ' pτ)
      -- ≈⟨ comp-assoc (Ctx E) ⟩
      --   ((m pΞ' pΓ pσ ∘E o# pΞ pΞ')∘E o# pΞ' pΞ) ∘E m pΔ pΞ' pτ
      -- ≈⟨ comp-cong-l (Ctx E) (comp-assoc-inv (Ctx E)) ⟩
      --   m pΞ' pΓ pσ ∘E (o# pΞ pΞ' ∘E o# pΞ' pΞ) ∘E m pΔ pΞ' pτ
      -- ≈⟨ comp-cong-l (Ctx E) (comp-cong-r (Ctx E) (o#comp pΞ' pΞ pΞ')) ⟩
      --   m pΞ' pΓ pσ ∘E o# pΞ' pΞ' ∘E m pΔ pΞ' pτ
      -- ≈⟨ comp-cong-l (Ctx E) (comp-cong-r (Ctx E) (~seq .sym (o#id pΞ'))) ⟩
      --   m pΞ' pΓ pσ ∘E idsE ∘E m pΔ pΞ' pτ
      -- ≈⟨ comp-cong-l (Ctx E) (id-r (Ctx E)) ⟩
      --   m pΞ' pΓ pσ ∘E m pΔ pΞ' pτ
      -- ≈⟨ comp-cong (Ctx E) (m-resp pΞ' pΓ pσ pσ' pσσ') (m-resp pΔ pΞ' pτ pτ' pττ') ⟩
      --   m pΞ' pΓ pσ' ∘E m pΔ pΞ' pτ'
      -- ∎
    m-resp pΔ (ctx-cons pΓ pA) (subst-<> pσ pA' pt) (subst-<> pτ pA'' ps) (subst-eq-<> pA''' pστ pst) = <>-cong E {!m-resp pΔ pΓ pσ pτ pστ!} {!!}
    m-resp pΔ pΓ pσ pτ (subst-eq-refl _) = m# pΔ pΓ pσ pτ
    m-resp pΔ pΓ pσ pτ (subst-eq-sym pστ) = ~seq .sym (m-resp pΔ pΓ pτ pσ pστ)
    m-resp pΔ pΓ pσ pτ (subst-eq-trans pξ pσξ pξτ) =
      ~seq .trans (m-resp pΔ pΓ pσ pξ pσξ) (m-resp pΔ pΓ pξ pτ pξτ)
    m-resp pΔ ctx-nil pσ pτ (subst-eq-!-η _) = !-η' E
    m-resp pΔ (ctx-cons pΓ pA) pσ (subst-<> (subst-comp x₃ pτ pτ₁) x₁ x₂) (subst-eq-<>-η x) = {!!}

    -- NEEDED
    ty : ∀ {Γ A} (pΓ : Γ ⊢) (pA : Γ ⊢ A) → TypE (o pΓ)
    -- Ind(pA : Γ ⊢ A).
    {-# TERMINATING #-}  -- Hello, Agda, my old friend???
    ty pΔ (ty-subst pΓ pA pσ) = ty pΓ pA [ m pΔ pΓ pσ ]E
    -- INFO: here we need the pΓ argument to ty-subst


    -- maybe better to define ty#l and ty#r instead to prove ty#
    ty# : ∀ {Γ A} (pΓ pΓ' : Γ ⊢) (pA pA' : Γ ⊢ A) → ty pΓ pA ~E ty pΓ' pA' [ o# pΓ pΓ' ]E
    -- Ind(pA pA' : Γ ⊢ A)?

    -- Hmm, this is actually not at all clear how to do as Δ and Δ'
    -- might be different; where do we need ty#?  One way to be able
    -- to proof is to fix Δ and Δ' by adding it to the substitution
    -- syntax as an additional argument to _[_] in the raw syntax.

    ty# pΓ pΓ' (ty-subst pΔ pA pσ) (ty-subst pΔ' pA' pσ') = BLOCK
      -- let open EqRelReason ~eq in
      -- begin
      --   ty pΔ pA [ m pΓ pΔ pσ ]E
      -- ≈⟨ []-resp-l (ty# pΔ pΔ' pA pA') ⟩
      --   ty pΔ' pA' [ o# pΔ pΔ' ]E [ m pΓ pΔ pσ ]E
      -- ≈⟨ []-assoc ⟩
      --   ty pΔ' pA' [ o# pΔ pΔ' ∘E m pΓ pΔ pσ ]E
      -- ≈⟨ []-resp-r (comp-cong-r (Ctx E) (m# pΓ pΔ pσ pσ')) ⟩
      --   ty pΔ' pA' [ o# pΔ pΔ' ∘E m pΓ pΔ pσ' ]E
      -- ≈⟨ []-resp-r (~seq .sym (m-o# pΓ' pΓ pΔ' pΔ pσ')) ⟩
      --   ty pΔ' pA' [ m pΓ' pΔ' pσ' ∘E o# pΓ pΓ' ]E
      -- ≈⟨ []-assoc-inv ⟩
      --   ty pΔ' pA' [ m pΓ' pΔ' pσ' ]E [ o# pΓ pΓ' ]E
      -- ∎

    -- special case of ty#, using m#id (not sure if termination
    -- checker will grasp this)
    -- TODO: really necessary?
    ty#r : ∀ {Γ A} (pΓ : Γ ⊢) (pA pA' : Γ ⊢ A) → ty pΓ pA ~E ty pΓ pA'
    -- Ind(pA pA' : Γ ⊢ A)?
    ty#r pΓ pA pA' = BLOCK
      -- let open EqRelReason ~eq in
      -- begin
      --   ty pΓ pA
      -- ≈⟨ ty# pΓ pΓ pA pA' ⟩
      --   ty pΓ pA' [ o# pΓ pΓ ]E
      -- ≈⟨ []-resp-r (~seq .sym (o#id pΓ)) ⟩
      --   ty pΓ pA' [ idsE ]E
      -- ≈⟨ []-id-inv ⟩
      --   ty pΓ pA'
      -- ∎

    -- ditto
    -- ty#l : ∀ {Γ A} (pΓ pΓ' : Γ ⊢) (pA : Γ ⊢ A) → ty pΓ pA ~E ty pΓ' pA [ o# pΓ pΓ' ]E
    -- -- Ind(pA : Γ ⊢ A)?
    -- ty#l pΓ pΓ' (ty-subst pΓ'' pA pσ) = {!!}

    -- NEEDED
    ty-cong : ∀ {Γ A B} (pΓ : Γ ⊢) (pA : Γ ⊢ A) (pB : Γ ⊢ B)
              (pAB : Γ ⊢ A ~ B) → ty pΓ pA ~E ty pΓ pB
    -- Ind(pAB : Γ ⊢ A ~ B).
    ty-cong = BLOCK
    -- ty-cong pΓ pA pB (ty-eq-refl _) = ty#r pΓ pA pB
    -- ty-cong pΓ pA pB (ty-eq-sym pBA) = ~eq .sym (ty-cong pΓ pB pA pBA)
    -- ty-cong pΓ pA pB (ty-eq-trans pC pAC pCB) =
    --   ~eq .trans (ty-cong pΓ pA pC pAC) (ty-cong pΓ pC pB pCB)
    -- ty-cong pΓ pA (ty-subst pΔ pB (subst-id x₁)) (ty-eq-id x) = ty# pΓ pΔ pA pB
    -- ty-cong pΓ
    --   (ty-subst pΔ (ty-subst pΞ pA pσ) pτ) (ty-subst pΞ' pA' (subst-comp pΔ' pσ' pτ'))
    --   (ty-eq-assoc pA'' pσ'' pτ'') =
    --   let open EqRelReason ~eq in
    --   begin
    --     ty pΞ pA [ m pΔ pΞ pσ ]E [ m pΓ pΔ pτ ]E
    --   ≈⟨ []-resp-l ([]-resp-r (m-o#-lr pΔ pΔ' pΞ pΞ' pσ)) ⟩
    --     ty pΞ pA [ o# pΞ' pΞ ∘E m pΔ' pΞ' pσ ∘E o# pΔ pΔ' ]E [ m pΓ pΔ pτ ]E
    --   ≈⟨ []-resp-l []-assoc-inv ⟩
    --     ty pΞ pA [ o# pΞ' pΞ ∘E m pΔ' pΞ' pσ ]E [ o# pΔ pΔ' ]E [ m pΓ pΔ pτ ]E
    --   ≈⟨ []-assoc ⟩
    --     ty pΞ pA [ o# pΞ' pΞ ∘E m pΔ' pΞ' pσ ]E [ o# pΔ pΔ' ∘E m pΓ pΔ pτ ]E
    --   ≈⟨ []-resp-l []-assoc-inv ⟩
    --     ty pΞ pA [ o# pΞ' pΞ ]E [ m pΔ' pΞ' pσ ]E [ o# pΔ pΔ' ∘E m pΓ pΔ pτ ]E
    --   ≈⟨ []-resp' ([]-resp-l (~eq .sym (ty# pΞ' pΞ pA' pA))) (~seq .sym (m-o#-l pΓ pΔ' pΔ pτ)) ⟩
    --     ty pΞ' pA' [ m pΔ' pΞ' pσ ]E [ m pΓ pΔ' pτ ]E
    --   ≈⟨ []-resp' ([]-resp-r (m# pΔ' pΞ' pσ pσ')) (m# pΓ pΔ' pτ pτ') ⟩
    --     ty pΞ' pA' [ m pΔ' pΞ' pσ' ]E [ m pΓ pΔ' pτ' ]E
    --   ≈⟨ []-assoc ⟩
    --     ty pΞ' pA' [ m pΔ' pΞ' pσ' ∘E m pΓ pΔ' pτ' ]E
    --   ∎
    -- ty-cong pΓ (ty-subst pΔ pA pσ) (ty-subst pΔ' pB pτ) (ty-eq-subst pAB pστ) =
    --   let open EqRelReason ~eq in
    --   begin
    --     ty pΔ pA [ m pΓ pΔ pσ ]E
    --   ≈⟨ []-resp' (ty-cong pΔ pA pB pAB) (m-o#-l pΓ pΔ pΔ' pσ) ⟩
    --     ty pΔ pB [ o# pΔ' pΔ ∘E m pΓ pΔ' pσ ]E
    --   ≈⟨ []-assoc-inv ⟩
    --     ty pΔ pB [ o# pΔ' pΔ ]E [ m pΓ pΔ' pσ ]E
    --   ≈⟨ []-resp' (~eq .sym (ty# pΔ' pΔ pB pB)) (m-resp pΓ pΔ' pσ pτ pστ) ⟩
    --     ty pΔ' pB [ m pΓ pΔ' pτ ]E
    --   ∎

    -- NEEDED
    subst-ty : ∀ {Γ Δ σ A} (pΔ : Δ ⊢) (pΓ : Γ ⊢)
               (pσ : σ ∈ Δ ⇒ Γ) (pA : Γ ⊢ A) →
               (ty pΓ pA [ m pΔ pΓ pσ ]E) ~E ty pΔ (ap (ty-map pΓ pσ) (A , pA) .snd)
    -- Ind(pA : Γ ⊢ A)?
    subst-ty = {!!}

    -- NEEDED
    ter : ∀ {Γ A t} (pΓ : Γ ⊢) (pA : Γ ⊢ A) (pt : Γ ⊢ t ∈ A) → TerE (o pΓ) (ty pΓ pA)
    -- Ind(pt : Γ ⊢ t ∈ A).
    ter = BLOCK
    -- ter pΓ pA (ter-ty-eq pB pt pBA) = ι' (ty-cong pΓ pB pA pBA) (ter pΓ pB pt)
    -- ter pΓ (ty-subst pΔ pA pσ) (ter-subst pt pσ') = ter pΔ pA pt [ m pΓ pΔ pσ ]tE
    -- ter (ctx-cons pΓ pA) (ty-subst pΓ' pA' (subst-pp pA'')) (ter-qq pA''') =
    --   let open EqRelReason ~eq
    --       eq = begin
    --            ty pΓ' pA' [ ppE ∘E < o# pΓ pΓ' ∘E ppE , ι _ qqE >E ]E
    --          ≈⟨ []-resp-r (pp<> E) ⟩
    --            ty pΓ' pA' [ o# pΓ pΓ' ∘E ppE ]E
    --          ≈⟨ []-assoc-inv ⟩
    --            ty pΓ' pA' [ o# pΓ pΓ' ]E [ ppE ]E
    --          ≈⟨ []-resp-l (~eq .sym (ty# pΓ pΓ' pA pA')) ⟩
    --            ty pΓ pA [ ppE ]E
    --          ∎
    --   in ι eq qqE


    -- ??? we should really generalize to a more general equality...
    ter# : ∀ {Γ A t} (pΓ pΓ' : Γ ⊢) (pA pA' : Γ ⊢ A) (pt pt' : Γ ⊢ t ∈ A) →
           ter pΓ pA pt ~t ι (ty# pΓ pΓ' pA pA') (ter pΓ' pA' pt' [ o# pΓ pΓ' ]tE)
    ter# = BLOCK
    -- ter# pΓA pΓA' pA pA' (ter-qq pA'') (ter-qq pA''') = {!!}
    -- ter# pΓ pΓ' pA pA' (ter-qq x) (ter-ty-eq x₁ pt' x₂) = {!!}
    -- ter# pΓ pΓ' pA pA' (ter-subst pt x) pt' = {!!}
    -- ter# pΓ pΓ' pA pA' (ter-ty-eq x pt x₁) pt' = {!!}

    ter#r : ∀ {Γ A t} (pΓ : Γ ⊢) (pA : Γ ⊢ A) (pt pt' : Γ ⊢ t ∈ A) →
            ter pΓ pA pt ~t ter pΓ pA pt'
    -- Ind(pt pt' : Γ ⊢ t ∈ A).
    ter#r = {!!}

    -- Maybe parametrize by an equality instead of using ty#r
    ter#m : ∀ {Γ A t} (pΓ : Γ ⊢) (pA pA' : Γ ⊢ A) (pt : Γ ⊢ t ∈ A) →
            ter pΓ pA pt ~t ι (ty#r pΓ pA pA') (ter pΓ pA' pt)
    ter#m = {!!}


    -- NEEDED
    ter-cong : ∀ {Γ A t s} (pΓ : Γ ⊢) (pA : Γ ⊢ A) (pt : Γ ⊢ t ∈ A) (ps : Γ ⊢ s ∈ A)
               (pts : Γ ⊢ t ~ s ∈ A) → ter pΓ pA pt ~t ter pΓ pA ps
    -- Ind(pts : Γ ⊢ t ~ s ∈ A).
    ter-cong = {!!}
    -- ter-cong pΓ pA pt ps (ter-eq-qq<> x x₁ x₂) = {!!}
    -- ter-cong pΓ pA pt ps (ter-eq-subst pts x) = {!!}
    -- ter-cong pΓ pA pt ps (ter-eq-id x) = {!!}
    -- ter-cong pΓ pA pt ps (ter-eq-assoc x x₁ x₂) = {!!}
    -- ter-cong pΓ pA pt ps (ter-eq-ty-eq pts x) = {!!}
    -- ter-cong pΓ pA pt ps (ter-eq-refl _) = ter#r pΓ pA pt ps
    -- ter-cong pΓ pA pt ps (ter-eq-sym pst) = ~teq .sym (ter-cong pΓ pA ps pt pst)
    -- ter-cong pΓ pA pt ps (ter-eq-trans pts pts₁) = {!!}

    -- NEEDED
    subst-ter : ∀ {Γ Δ A σ t} (pΔ : Δ ⊢) (pΓ : Γ ⊢) (pσ : σ ∈ Δ ⇒ Γ)
                (pA : Γ ⊢ A) (pt : Γ ⊢ t ∈ A) →
                let pAσ = ty-subst pΓ pA pσ  -- aka: ap (ty-map pσ) (A , pA) .snd
                    ptσ = ter-subst pt pσ
                    eq : (ty pΓ pA [ m pΔ pΓ pσ ]E) ~E ty pΔ pAσ
                    eq = subst-ty pΔ pΓ pσ pA
                in ter pΓ pA pt [ m pΔ pΓ pσ ]tE ~t ι eq (ter pΔ pAσ ptσ)
    -- Ind(pt : Γ ⊢ t ∈ A)?
    subst-ter {Γ} {Δ} {A} {σ} {t} pΔ pΓ pσ pA pt = {!!}

    -- NEEDED
    -- does this make sense?
    ι-ter : ∀ {Γ A B t} (pΓ : Γ ⊢) (pA : Γ ⊢ A) (pB : Γ ⊢ B)
              (pAB : Γ ⊢ A ~ B) (pt : Γ ⊢ t ∈ B) →
              ι (ty-cong pΓ pA pB pAB) (ter pΓ pB pt)
              ~t ter pΓ pA (ter-ty-eq pB pt (ty-eq-sym pAB))
    -- Ind(pt : Γ ⊢ t ∈ B)?  On pAB?
    ι-ter = {!!}


-------------------------------------------------------------------------------

{-


  subst-ty-cong : ∀ {Γ Δ σ A B} (pΔ : Δ ⊢) (pΓ : Γ ⊢) (pσ : σ ∈ Δ ⇒ Γ)
          (pA : Γ ⊢ A) (pB : Γ ⊢ B) (pAB : Γ ⊢ A ~ B)
          → (ty pΓ pA [ m pΔ pΓ pσ ]E) ~E ty pΔ (ap (ty-map pσ) (B , pB) .snd)
                                          --  (snd ((B , pB) [ σ , pσ ]S))
  subst-ty-cong {Δ} {Γ} {σ} {A} {B} pΔ pΓ pσ pA pB pAB =
    let open EqRelReason ~eq in
    begin
      ty pΓ pA [ m pΔ pΓ pσ ]E
    ≈⟨ []-resp' (ty-cong pΓ pA pB pAB) (~seq .refl) ⟩
      ty pΓ pB [ m pΔ pΓ pσ ]E
    ≈⟨ subst-ty pΔ pΓ pσ pB ⟩
      ty pΔ (ap (ty-map pσ) (B , pB) .snd)
    ∎

  subst-ter-cong : ∀ {Γ Δ A B σ t s}
    (pΓ : Γ ⊢) (pΔ : Δ ⊢) (pA : Γ ⊢ A) (pB : Δ ⊢ B) (pσ : σ ∈ Δ ⇒ Γ)
    (q : Δ ⊢ B ~ A [ σ ]) (pt : Γ ⊢ t ∈ A) (ps : Γ ⊢ s ∈ A) (pts : Γ ⊢ t ~ s ∈ A) →
    _~t_  -- fun (Tm E) (o pΔ , ty pΔ pB) .rel
      (mor (Tm E)
        (m pΔ pΓ pσ ,
          eqr (fun (Ty E) (o pΔ)) .trans (ty-cong pΔ pB (ty-subst pA pσ) q)
           (eqr (fun (Ty E) (o pΔ)) .trans
            (sym (eqr (fun (Ty E) (o pΔ)))
              (subst-ty-cong pΔ pΓ pσ pA pA (ty-eq-refl pA)))
            (eqr (fun (Ty E) (o pΔ)) .EqRel.refl)))
          .ap (ter pΓ pA pt))
      (ter pΔ pB (ter-ty-eq (ter-subst ps pσ) (ty-eq-sym q)))
  subst-ter-cong {Γ} {Δ} {A} {B} {σ} {t} {s} pΓ pΔ pA pB pσ q pt ps pts =
    let open EqRelReason (~teq {o pΔ} {ty pΔ pB})
        pAσ = ap (ty-map pσ) (A , pA) .snd -- aka: ty-subst pA pσ
        psσ = ter-subst ps pσ

        tyeq : ty pΔ pB ~E ty pΓ pA [ m pΔ pΓ pσ ]E
        tyeq = ~eq .trans (ty-cong pΔ pB (ty-subst pA pσ) q)
                  (~eq .trans (sym (eqr (fun (Ty E) (o pΔ)))
                    (subst-ty-cong pΔ pΓ pσ pA pA (ty-eq-refl pA)))
                  (~eq .refl))

        mσel : hom (∫ {C = Ctx E} (Ty E)) (o pΔ , ty pΓ pA [ m pΔ pΓ pσ ]E) (o pΓ , ty pΓ pA)
        mσel = m pΔ pΓ pσ , ~eq .refl

        ιtyeqel : hom (∫ {C = Ctx E} (Ty E)) (o pΔ , ty pΔ pB) (o pΔ , ty pΓ pA [ m pΔ pΓ pσ ]E)
        ιtyeqel = idsE , ~eq .trans tyeq (id-mor (Ty E) .map-resp (~eq .refl))
    in
    begin
      mor (Tm E)
        (m pΔ pΓ pσ , tyeq) .ap (ter pΓ pA pt)
    ≈⟨ mor (Tm E) _ .ap-cong (ter-cong pΓ pA pt ps pts) ⟩
      mor (Tm E)
        (m pΔ pΓ pσ , tyeq) .ap (ter pΓ pA ps)
    ≈⟨ resp (Tm E) (id-r-inv (Ctx E)) .map-resp (~teq .refl) ⟩
      mor (Tm E)
        (mσel ∘el ιtyeqel) .ap (ter pΓ pA ps)
    ≈⟨ comp-mor-inv (Tm E) .map-resp (~teq .refl) ⟩
      mor (Tm E) ιtyeqel .ap (mor (Tm E) mσel .ap (ter pΓ pA ps))
    ≈⟨⟩
      ι tyeq ((ter pΓ pA ps) [ m pΔ pΓ pσ ]tE)
    ≈⟨ ιresp (subst-ter pΔ pΓ pσ pA ps) ⟩
      ι tyeq (ι (subst-ty pΔ pΓ pσ pA) (ter pΔ pAσ psσ))
    ≈⟨ ιtrans ⟩
      ι (~eq .trans tyeq (subst-ty pΔ pΓ pσ pA)) (ter pΔ pAσ psσ)
    ≈⟨ ιirr ⟩
      ι (ty-cong pΔ pB pAσ q) (ter pΔ pAσ psσ)
    ≈⟨ ι-ter pΔ pB (ty-subst pA pσ) q (ter-subst ps pσ) ⟩
      ter pΔ pB (ter-map pσ q .ap (s , ps) .snd)
    ∎

  elim-ctx : eFunctor (eCwF.Ctx SynCwf) (eCwF.Ctx E)
  elim-ctx = record
    { fun = λ { (Γ , pΓ) → o pΓ }
    ; mor = λ { {Δ , pΔ} {Γ , pΓ} (σ , pσ) → m pΔ pΓ pσ }
    ; resp = λ { {Δ , pΔ} {Γ , pΓ} {σ , pσ} {τ , pτ} pστ → m-resp pΔ pΓ pσ pτ pστ}
    ; id-mor = λ { {Γ , pΓ} → o#id pΓ }
    ; comp-mor = ~seq .refl     -- a definitional equality!
    }

  elim-ty-nat : (Γ : obj (Ctx SynCwf op)) →
                eMap (fun (Ty SynCwf) Γ) (fun (Ty E ∘Func (elim-ctx op-fun)) Γ)
  elim-ty-nat (Γ , pΓ) = record
    { ap = λ {(A , pA) → ty pΓ pA}
    ; ap-cong = λ { {A , pA} {B , pB} pAB → ty-cong pΓ pA pB pAB}
    }

  elim-ty : eNat (Ty SynCwf) (Ty E ∘Func (elim-ctx op-fun))
  elim-ty = record
    { nat = elim-ty-nat
    ; nat-eq = λ
      { {Γ , pΓ} {Δ , pΔ} {σ , pσ} → map-rel λ
        { {A , pA} {B , pB} pAB → subst-ty-cong pΔ pΓ pσ pA pB pAB
        }
      }
    }

  elim-ter-nat : (ΓA : obj (∫ {C = Ctx SynCwf} (Ty SynCwf) op)) →
                 eMap (fun (Tm SynCwf) ΓA) (fun (Tm E ∘Func (∫base elim-ctx elim-ty op-fun)) ΓA)
  elim-ter-nat ((Γ , pΓ), (A , pA)) = record
    { ap =  λ { (t , pt) → ter pΓ pA pt }
    ; ap-cong =  λ { {t , pt} {s , ps} pts → ter-cong pΓ pA pt ps pts}
    }

  elim-ter : eNat (Tm SynCwf) (Tm E ∘Func (∫base elim-ctx elim-ty op-fun))
  elim-ter = record
    { nat = elim-ter-nat
    ; nat-eq = λ
      { {(Γ , pΓ) , A , pA} {(Δ , pΔ) , B , pB} {(σ , pσ) , q} → map-rel λ
        { {t , pt} {s , ps} pts → subst-ter-cong pΓ pΔ pA pB pσ q pt ps pts
        }
      }
    }

  -- TODO: Still misses that structure is preserved
  elim : Mor SynCwf E
  elim = record { ctx = elim-ctx ; ty = elim-ty ; tm = elim-ter ; <>-pres = {!!} ; pair-pres = {!!} }

-- -}
-- -}
