{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
module Vec where

import Data.Type.Equality

import Nat
import Equality

import Proofs.Addition

data Vec :: Nat -> * -> * where
  V0   :: Vec Z a
  (:>) :: a -> Vec n a -> Vec (S n) a

infixr 5 :>

instance (Show a) => Show (Vec n a) where
  show v = "[" ++ go v
    where go :: (Show a') => Vec n' a' -> String
          go v = case v of
            V0        -> "]"
            (x :> xs) -> show x ++ sep ++ go xs
              where sep = case xs of
                      V0   -> ""
                      _    -> ", "

x = 1 :> 2 :> 3 :> 4 :> V0
y = 5 :> 6 :> 7 :> 8 :> 9 :> V0

vlength :: IsNat n => Vec n a -> SNat n
vlength _ = nat

append :: SNat n -> SNat m -> Vec n a -> Vec m a -> Vec (n + m) a
append SZ m V0 ys = gcastWith (plusIdenL m) ys
append n m (x:>xs) ys = gcastWith (proof n' m) $ x :> append n' m xs ys
  where proof :: SNat n -> SNat m -> (S n + m) :~: S (n + m)
        proof n SZ     = Refl
        proof n (SS m) = gcastWith (proof n m) Refl

        n' = spred n  -- we know that n !~ SZ from the (x:>xs) pattern match

append' :: SNat n -> SNat m -> Vec n a -> Vec m a -> Vec (n + m) a
append' SZ m V0 ys = gcastWith (plusIdenL m) ys
append' n m (x:>xs) ys = gcastWith (proof pn m) $ x :> append' (spred n) m xs ys
  where
    pn = spred n
    proof :: forall x y. SNat x -> SNat y -> (S x + y) :~: S (x + y)
    proof x y = step1 ==> step2 ==> step3
      where
        step1 :: (S x + y) :~: (y + S x)
        step1 = gcastWith (plusComm (SS x) y) Refl

        step2 :: (y + S x) :~: S (y + x)
        step2 = gcastWith (given2 y (SS x)) Refl

        step3 :: S (y + x) :~: S (x + y)
        step3 = gcastWith (plusComm y x) Refl

-- Implicit version of `append`, thanks to typeclasses
(+++) :: forall n m a. (IsNat n, IsNat m) => Vec n a -> Vec m a -> Vec (n + m) a
(+++) = append (nat @n) (nat @m)
