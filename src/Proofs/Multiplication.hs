{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeOperators        #-}
module Proofs.Multiplication where

import Data.Type.Equality

import Nat
import Equality

import Proofs.Addition

-- Value-level proof of (3)
given3 :: SNat a -> (a * Z) :~: Z
given3 _ = Refl

-- Value-level proof of (4)
given4 :: SNat a -> SNat b -> (a * S b) :~: ((a * b) + a)
given4 _ _ = Refl

-- Right zero property
mulZeroPropR :: SNat a -> (a * Z) :~: Z
mulZeroPropR = given3

-- Left zero property
mulZeroPropL :: SNat a -> (Z * a) :~: Z
mulZeroPropL SZ     = Refl
mulZeroPropL (SS a) = gcastWith (mulZeroPropL a) Refl

-- Right identity
mulIdenR :: SNat a -> (a * I) :~: a
mulIdenR SZ     = Refl
mulIdenR (SS a) = gcastWith (mulIdenR a) Refl

-- Left identity
mulIdenL :: SNat a -> (I * a) :~: a
mulIdenL SZ     = Refl
mulIdenL (SS a) = gcastWith (mulIdenL a) Refl

-- Proof that multiplication distributes over addition
mulPlusDist :: SNat a -> SNat b -> SNat c -> ((a + b) * c) :~: ((a * c) + (b * c))
mulPlusDist a b SZ       = Refl
mulPlusDist a b k@(SS c) =
  let proof :: forall a b c. SNat a -> SNat b -> SNat c -> ((a + b) * S c) :~: ((a * S c) + (b * S c))
      proof x y z = p1 ==> p2 ==> p3 ==> p4 ==> p5 ==> p6 ==> p7 ==> p8 ==> p9
        where
          p1 :: ((a + b) * S c) :~: (((a + b) * c) + (a + b))
          p1 = Refl -- from (4)

          p2 :: (((a + b) * c) + (a + b)) :~: (((a * c) + (b * c)) + (a + b))
          p2 = gcastWith (mulPlusDist x y z) Refl

          p3 :: (((a * c) + (b * c)) + (a + b)) :~: ((a * c) + ((b * c) + (a + b)))
          p3 = gcastWith (plusAssoc (x !* z) (y !* z) (x !+ y)) Refl

          p4 :: ((a * c) + ((b * c) + (a + b))) :~: ((a * c) + ((a + b) + (b * c)))
          p4 = gcastWith (plusComm (y !* z) (x !+ y)) Refl

          p5 :: ((a * c) + ((a + b) + (b * c))) :~: (((a * c) + (a + b)) + (b * c))
          p5 = gcastWith (plusAssoc (x !* z) (x !+ y) (y !* z)) Refl

          p6 :: (((a * c) + (a + b)) + (b * c)) :~: ((((a * c) + a) + b) + (b * c))
          p6 = gcastWith (plusAssoc (x !* z) x y) Refl

          p7 :: ((((a * c) + a) + b) + (b * c)) :~: (((a * c) + a) + (b + (b * c)))
          p7 = gcastWith (plusAssoc ((x !* z) !+ x) y (y !* z)) Refl

          p8 :: (((a * c) + a) + (b + (b * c))) :~: (((a * c) + a) + ((b * c) + b))
          p8 = gcastWith (plusComm y (y !* z)) Refl

          p9 :: (((a * c) + a) + ((b * c) + b)) :~: ((a * S c) + (b * S c))
          p9 = Refl

  in proof a b c


mulComm :: SNat a -> SNat b -> (a * b) :~: (b * a)
mulComm a SZ       = gcastWith (mulZeroPropL a) Refl
mulComm a k@(SS b) =
  let
    proof :: forall a b c. SNat a -> SNat b -> (a * S b) :~: (S b * a)
    proof x y = p1 ==> p2 ==> p3 ==> p4 ==> p5
      where
        p1 :: (a * S b) :~: ((a * b) + a)
        p1 = Refl

        p2 :: ((a * b) + a) :~: ((b * a) + a)
        p2 = gcastWith (mulComm x y) Refl

        p3 :: ((b * a) + a) :~: ((b * a) + (I * a))
        p3 = gcastWith (mulIdenL x) Refl

        p4 :: ((b * a) + (I * a)) :~: ((b + I) * a)
        p4 = gcastWith (mulPlusDist y (SS SZ) x) Refl

        p5 :: ((b + I) * a) :~: (S b * a)
        p5 = Refl

  in proof a b


mulAssoc :: SNat a -> SNat b -> SNat c -> ((a * b) * c) :~: (a * (b * c))
mulAssoc a b SZ       = Refl
mulAssoc a b k@(SS c) =
  let proof :: forall a b c. SNat a -> SNat b -> SNat c -> ((a * b) * S c) :~: (a * (b * S c))
      proof x y z = p1 ==> p2 ==> p3 ==> p4 ==> p5 ==> p6 ==> p7 ==> p8 ==> p9
        where
          p1 :: ((a * b) * S c) :~: (((a * b) * c) + (a * b))
          p1 = Refl -- from (4)

          p2 :: (((a * b) * c) + (a * b)) :~: ((a * (b * c)) + (a * b))
          p2 = gcastWith (mulAssoc x y z) Refl

          p3 :: ((a * (b * c)) + (a * b)) :~: ((a * b) + (a * (b * c)))
          p3 = gcastWith (plusComm (x !* (y !* z)) (x !* y)) Refl

          p4 :: ((a * b) + (a * (b * c))) :~: ((b * a) + (a * (b * c)))
          p4 = gcastWith (mulComm x y) Refl

          p5 :: ((b * a) + (a * (b * c))) :~: ((b * a) + ((b * c) * a))
          p5 = gcastWith (mulComm x (y !* z)) Refl

          p6 :: ((b * a) + ((b * c) * a)) :~: ((b + (b * c)) * a)
          p6 = gcastWith (mulPlusDist y (y !* z) x) Refl

          p7 :: ((b + (b * c)) * a) :~: (a * (b + (b * c)))
          p7 = gcastWith (mulComm x (y !+ (y !* z))) Refl

          p8 :: (a * (b + (b * c))) :~: (a * ((b * c) + b))
          p8 = gcastWith (plusComm y (y !* z)) Refl

          p9 :: (a * ((b * c) + b)) :~: (a * (b * S c))
          p9 = Refl

  in proof a b c
