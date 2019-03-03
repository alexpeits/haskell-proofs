{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
module Nat where

import Data.Kind
import GHC.TypeLits (TypeError, ErrorMessage(..))

data Nat = Z | S Nat

data SNat :: Nat -> Type where
  SZ :: SNat Z
  SS :: SNat n -> SNat (S n)

sNatToInt :: SNat n -> Int
sNatToInt SZ     = 0
sNatToInt (SS n) = 1 + sNatToInt n

instance Show (SNat n) where
  show SZ = "0"
  show n  = show $ sNatToInt n

type I = S Z
type II = S I

class               IsNat (n :: Nat) where nat :: SNat n
instance            IsNat Z          where nat =  SZ
instance IsNat n => IsNat (S n)      where nat =  SS nat

-- get predecessor SNat given a nonzero SNat
spred :: SNat (S n) -> SNat n
spred (SS n) = n

type family P n where
  P Z     = Z
  P (S n) = n

type family NonZero n where
  NonZero Z     = TypeError (Text "`Z` is not non-zero, m8")
  NonZero (S n) = True ~ True

--
-- Addition
--
type family a + b where
  a + Z   = a         -- (1)
  a + S b = S (a + b) -- (2)

(!+) :: SNat n -> SNat m -> SNat (n + m)
n !+ SZ     = n
n !+ (SS m) = SS (n !+ m)

--
-- Subtraction
--

type family a - b where
  a - Z   = a
  a - S b = P (a - b)

--
-- Multiplication
--
type family a * b where
  a * Z   = Z           -- (3)
  a * S b = (a * b) + a -- (4)

(!*) :: SNat n -> SNat m -> SNat (n * m)
n !* SZ     = SZ
n !* (SS m) = (n !* m) !+ n


--
-- Comparison
--

type family Min n m where
  Min Z Z = Z
  Min (S n) Z = Z
  Min Z (S n) = Z
  Min (S n) (S m) = S (Min n m)

type family Max n m where
  Max Z Z = Z
  Max (S n) Z = S n
  Max Z (S n) = S n
  Max (S n) (S m) = S (Max n m)


--
-- Finite set
--

data Fin :: Nat -> Type where
  FZ :: Fin (S n)
  FS :: Fin n -> Fin (S n)
