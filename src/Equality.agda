module Equality where

open import Agda.Primitive

data _≡_ {l : Level} {A : Set l} (a : A) : A → Set l where
  refl : a ≡ a

