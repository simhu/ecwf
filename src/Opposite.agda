module Opposite where

open import Basics

_op : ∀ {lo lh lr} → ECat {lo} {lh} {lr} → ECat
C op = record C
     { hom = λ A B → hom C B A
     ; comp = λ f g → comp C g f
     ; comp-assoc =  C .hom-eqr .sym (C .comp-assoc)
     ; comp-cong =  λ p q → C .comp-cong q p
     ; id-l = id-r C
     ; id-r = id-l C
     }

_op-fun : ∀ {lco lch lcr ldo ldh ldr}
          {C : ECat {lco} {lch} {lcr}} {D : ECat {ldo} {ldh} {ldr}}
          (F : eFunctor C D) → eFunctor (C op) (D op)
F op-fun = record -- hmm, no eta :-(
 { fun = fun F ; mor = mor F ; resp = resp F
 ; id-mor = id-mor F ; comp-mor = comp-mor F }
