{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeOperators        #-}
module Proofs.Addition where

import Data.Type.Equality

import Nat
import Equality

-- Value-level proof of (1)
given1 :: SNat a -> (a + Z) :~: a
given1 _ = Refl

-- Value-level proof of (2)
given2 :: SNat a -> SNat b -> (a + S b) :~: S (a + b)
given2 _ _ = Refl

-- Right identity
plusIdenR :: SNat a -> (a + Z) :~: a
plusIdenR = given1

-- Left identity
plusIdenL :: SNat a -> (Z + a) :~: a
plusIdenL SZ     = Refl
plusIdenL (SS a) = gcastWith (plusIdenL a) Refl

-- Plus Associativity
plusAssoc :: SNat a -> SNat b -> SNat c -> ((a + b) + c) :~: (a + (b + c))
plusAssoc a b SZ     = Refl
plusAssoc a b (SS c) = gcastWith (plusAssoc a b c) Refl

plusAssoc' :: SNat a -> SNat b -> SNat c -> ((a + b) + c) :~: (a + (b + c))
plusAssoc' a b SZ =
  let proof :: forall x y. SNat x -> SNat y -> ((x + y) + Z) :~: (x + (y + Z))
      proof x y = step1 ==> step2
        where
          step1 :: ((x + y) + Z) :~: (x + y)
          step1  = gcastWith (given1 (x !+ y)) Refl

          step2 :: (x + y) :~: (x + (y + Z))
          step2 = gcastWith (given1 y) Refl
  in proof a b
plusAssoc' a b (SS c) =
  let proof ::
        forall x y z.
        SNat x -> SNat y -> SNat z ->
        ((x + y) + S z) :~: (x + (y + S z))
      proof x y z = step1 ==> step2 ==> step3 ==> step4
        where
          step1 :: ((x + y) + S z) :~: S ((x + y) + z)
          step1 = gcastWith (given2 (x !+ y) (SS z)) Refl

          step2 :: S ((x + y) + z) :~: S (x + (y + z))
          step2 = gcastWith (plusAssoc' x y z) Refl

          step3 :: S (x + (y + z)) :~: (x + S (y + z))
          step3 = gcastWith (given2 x (y !+ z)) Refl

          step4 :: (x + S (y + z)) :~: (x + (y + S z))
          step4 = gcastWith (given2 y z) Refl
  in proof a b c

-- Plus Commutativity
plusComm :: SNat a -> SNat b -> (a + b) :~: (b + a)
plusComm SZ     SZ      = Refl
plusComm a      SZ      = gcastWith (plusIdenL a) Refl
plusComm SZ     (SS SZ) = Refl
plusComm (SS a) (SS SZ) = gcastWith (plusComm a (SS SZ)) Refl
plusComm a      k@(SS b)  =
  let proof :: forall a b. SNat a -> SNat b -> (a + S b) :~: (S b + a)
      proof x y = p1 ==> p2 ==> p3 ==> p4 ==> p5 ==> p6 ==> p7
        where
          p1 :: (a + S b) :~: (a + (b + I))
          p1 = gcastWith (given2 y (SS SZ)) Refl

          p2 :: (a + (b + I)) :~: ((a + b) + I)
          p2 = gcastWith (plusAssoc x y (SS SZ)) Refl

          p3 :: ((a + b) + I) :~: ((b + a) + I)
          p3 = gcastWith (plusComm x y) Refl

          p4 :: ((b + a) + I) :~: (b + (a + I))
          p4 = gcastWith (plusAssoc y x (SS SZ)) Refl

          p5 :: (b + (a + I)) :~: (b + (I + a))
          p5 = gcastWith (plusComm x (SS SZ)) Refl

          p6 :: (b + (I + a)) :~: ((b + I) + a)
          p6 = gcastWith (plusAssoc y (SS SZ) x) Refl

          p7 :: ((b + I) + a) :~: (S b + a)
          p7 = gcastWith (given2 y (SS SZ)) Refl

  in proof a b
