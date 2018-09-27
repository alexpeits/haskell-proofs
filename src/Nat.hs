{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
module Nat where

data Nat = Z | S Nat

data SNat :: Nat -> * where
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
-- Multiplication
--
type family a * b where
  a * Z   = Z           -- (3)
  a * S b = (a * b) + a -- (4)

(!*) :: SNat n -> SNat m -> SNat (n * m)
n !* SZ     = SZ
n !* (SS m) = (n !* m) !+ n
