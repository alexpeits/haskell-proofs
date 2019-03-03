{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE EmptyCase            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE InstanceSigs         #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
module Vec where

import Data.Void
import Data.Kind
import Data.Type.Equality

import Prelude hiding
  ( length
  , (++)
  , head
  , last
  , tail
  , init
  , map
  , reverse
  , intersperse
  , concat
  , intercalate
  , transpose
  , subsequences
  , permutations
  )
import qualified Data.List as L

import Nat
import Equality

import Proofs.Addition
import Proofs.Multiplication

data Vec :: Type -> Nat -> Type where
  V0   :: Vec a Z
  (:>) :: a -> Vec a n -> Vec a (S n)

infixr 5 :>

instance (Show a) => Show (Vec a n) where
  show v = "[" L.++ go v
    where go :: (Show a') => Vec a' n' -> String
          go v = case v of
            V0        -> "]"
            (x :> xs) -> show x L.++ sep L.++ go xs
              where sep = case xs of
                      V0   -> ""
                      _    -> ", "

x = 1 :> 2 :> 3 :> 4 :> V0
y = 5 :> 6 :> 7 :> 8 :> 9 :> V0

sumSuccProof :: forall x y. SNat x -> SNat y -> (S x + y) :~: S (x + y)
sumSuccProof x SZ = Refl
sumSuccProof x (SS y) = gcastWith (sumSuccProof x y) Refl
-- ... also:
-- sumSuccProof x y = step1 ==> step2 ==> step3
--   where
--     step1 :: (S x + y) :~: (y + S x)
--     step1 = gcastWith (plusComm (SS x) y) Refl

--     step2 :: (y + S x) :~: S (y + x)
--     step2 = gcastWith (given2 y (SS x)) Refl

--     step3 :: S (y + x) :~: S (x + y)
--     step3 = gcastWith (plusComm y x) Refl

append :: SNat n -> SNat m -> Vec a n -> Vec a m -> Vec a (n + m)
append SZ m V0 ys = gcastWith (plusIdenL m) ys
append n m (x:>xs) ys = gcastWith (sumSuccProof pn m) $ x :> append pn m xs ys
  where
    pn = spred n  -- we know that n !~ SZ from the (x:>xs) pattern match

-- Implicit version of `append`, thanks to typeclasses
(++) :: forall a n m. (IsNat n, IsNat m) => Vec a n -> Vec a m -> Vec a (n + m)
(++) = append (nat @n) (nat @m)

head :: Vec a (S n) -> a
head (x:>_) = x

last :: Vec a (S n) -> a
last (x:>V0) = x
last (_:>xs) = case xs of r@(_:>_) -> last r

tail :: Vec a (S n) -> Vec a n
tail (_:>V0) = V0
tail (_:>xs) = xs

init :: Vec a (S n) -> Vec a n
init (x:>xs) = init' x xs
  where init' :: a -> Vec a n -> Vec a n
        init' _ V0 = V0
        init' y (z :> zs) = y :> init' z zs

uncons :: Vec a (S n) -> (a, Vec a n)
uncons v = (head v, tail v)

null :: Vec a n -> Bool
null V0 = True
null _  = False

length :: Vec a n -> Int
length V0 = 0
length (_:>xs) = 1 + length xs

lengthS :: IsNat n => Vec a n -> SNat n
lengthS _ = nat

-- instance Foldable (Vec n) where
--   foldr :: (a -> b -> b) -> b -> Vec n a -> b
--   foldr _ a V0 = a
--   foldr f a (x:>xs) = foldr f (f x a) xs

--   foldMap :: Monoid m => (a -> m) -> Vec n a -> m
--   foldMap _ V0 = mempty
--   foldMap f (x:>xs) = mappend (f x) (foldMap f xs)

map :: (a -> b) -> Vec a n -> Vec b n
map _ V0 = V0
map f (x:>xs) = f x :> map f xs

-- reverse :: IsNat n => Vec n a -> Vec n a
-- reverse V0 = V0
-- reverse xs = go xs V0
  -- where
    -- go :: forall n m a. (IsNat n, IsNat m) => Vec n a -> Vec m a -> Vec (n + m) a
    -- go V0 acc = gcastWith (plusIdenL (nat @m)) acc
    -- go (y:>ys) acc = gcastWith (sumSuccProof pn (nat @m)) $ go ys (y:>acc)
      -- where
        -- pn = spred (nat @n)

reverse' :: SNat n -> Vec a n -> Vec a n
reverse' _ V0 = V0
reverse' n (x:>xs) = go n SZ (x:>xs) V0
  where
    --               length of n , length of acc
    go :: forall n m a. SNat n -> SNat m -> Vec a n -> Vec a m -> Vec a (n + m)
    go _ lm V0 acc = gcastWith (plusIdenL lm) acc
    go ln lm (y:>ys) acc = gcastWith (sumSuccProof pln lm) $ go pln (SS lm) ys (y:>acc)
      where pln = spred ln

reverse :: forall n a. IsNat n => Vec a n -> Vec a n
reverse = reverse' (nat @n)

-- succCong :: n :~: m -> S n :~: S m
-- succCong Refl = Refl

-- predProof :: SNat n -> SNat m -> (m :~: Z -> Void) -> S n :~: m -> n :~: P m
-- predProof n m nonZero eq
--   = case m of
--       SZ    -> absurd $ nonZero Refl
--       SS m' -> gcastWith eq Refl

succPredCancelProof :: SNat n -> (n :~: Z -> Void) -> S (P n) :~: n
succPredCancelProof n nonZero
  = case n of
      SZ    -> absurd $ nonZero Refl
      SS n' -> Refl

natNonZero :: NonZero n => n :~: Z -> Void
natNonZero nonZero = case nonZero of {}

natNonZero' :: NonZero n => SNat n -> n :~: Z -> Void
natNonZero' _ nonZero = case nonZero of {}

-- length after intersperse is double minus one: n ~~> 2 * n - 1
intersperse' :: forall n a. SNat n -> a -> Vec a n -> Vec a (P (II * n))
intersperse' _ _ V0 = V0
intersperse' _ _ l@(_:>V0) = l
intersperse' n a (x:>xs@(_:>_))  -- prove that tail is not V0, in order to know that P n ~ S m
  -- = gcastWith (succPredCancelProof pn (natNonZero' pn)) $ x :> a :> intersperse' pn a xs
  = gcastWith (succPredCancelProof pn (natNonZero @(P n))) $ x :> a :> intersperse' pn a xs
  where pn = spred n

intersperse :: forall n a. IsNat n => a -> Vec a n -> Vec a (P (II * n))
intersperse = intersperse' (nat @n)

-- pr :: a -> ((a, b) -> Void) -> (b -> Void)
-- pr a f b = f (a, b)

-- doubleNeg :: a -> (a -> Void) -> Void
-- doubleNeg a f = f a

data Ex :: (k -> Type) -> Type where
  Ex :: a i -> Ex a

concat' :: SNat n -> SNat m -> Vec (Vec a n) m -> Vec a (n * m)
concat' _ _ V0 = V0
concat' n m (x:>xs) = gcastWith (plusComm n len') $ append n len' x $ concat' n pm xs
  where pm = spred m
        len' = n !* pm

concat :: forall n m a. (IsNat n, IsNat m) => Vec (Vec a n) m -> Vec a (n * m)
concat = concat' (nat @n) (nat @m)

intercProof :: SNat n -> (S n + n) :~: S (II * n)
intercProof n
  = gcastWith (plusIdenL n)
  $ gcastWith (mulComm (SS (SS SZ)) n)
  $ gcastWith (plusComm (SS n) n) Refl

-- let's assume for now the vector of vectors h
intercalate' :: SNat n -> SNat m -> Vec a n -> Vec (Vec a n) m -> Vec a ((n * m) + (n * P m))
intercalate' _ _ _ V0 = V0
intercalate' n _ _ (x:>V0) = gcastWith (plusIdenL n) x
intercalate' n m V0 v@(_:>_)  -- again, we need to tell ghc that mm ~ S x
  = gcastWith (mulComm SZ (spred m)) $ concat' n m v
-- *** TODO
-- intercalate' n m l@(x:>xs) r@(y:>ys)
--   = gcastWith (intercProof (spred m))
--   $ concat' n (m !+ spred m) $ intersperse' m l r
