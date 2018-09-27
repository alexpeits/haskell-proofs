{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module Equality where

import Data.Type.Equality

-- Transitive property of propositional equality
(==>) :: a :~: b -> b :~: c -> a :~: c
Refl ==> Refl = Refl

-- Symmetric property of propositional equality
symm :: a :~: b -> b :~: a
symm Refl = Refl

-- Congruence of propositional equality
cong :: a :~: b -> f a :~: f b
cong Refl = Refl
