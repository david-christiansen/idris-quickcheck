module Play

-- Playing with quickcheck over a universe

import QuickCheck
import Debug.Trace

%default total

using (c : Type -> Type, c' : Type -> Type, t : Type)
  getInst : c t => c t
  getInst = %instance

  getInst2 : (c t, c' t) => (c t, c' t)
  getInst2 = (%instance, %instance)

nums : List (t ** (Num t, Eq t))
nums = [ (Int     ** getInst2)
       , (Integer ** getInst2)
       , (Float   ** getInst2)
       , (Nat     ** getInst2)
       ]

data NumEq = INT | INTEGER | FLOAT | NAT

instance Show NumEq where
  show INT = "INT"
  show INTEGER = "INTEGER"
  show FLOAT = "FLOAT"
  show NAT = "NAT"

interpNumEq : NumEq -> Type
interpNumEq INT     = Int
interpNumEq INTEGER = Integer
interpNumEq FLOAT   = Float
interpNumEq NAT     = Nat

insts : (t : NumEq) -> (Num (interpNumEq t), Eq (interpNumEq t))
insts INT     = getInst2
insts INTEGER = getInst2
insts FLOAT   = getInst2
insts NAT     = getInst2

instance RandomGen r => Arbitrary r NumEq where
  arbitrary = elements [INT, INTEGER, FLOAT, NAT]
  coarbitrary INT = variant 0
  coarbitrary INTEGER = variant 1
  coarbitrary FLOAT = variant 2
  coarbitrary NAT = variant 3

instance RandomGen r => Arbitrary r (t ** (Num t, Eq t)) where
  arbitrary = elements nums
  coarbitrary _ = variant 0

instance Eq (interpNumEq t) where
  (==) = let inst = snd (insts _) in (==) @{inst}

instance Num (interpNumEq t) where
  fromInteger = let inst = fst (insts _) in fromInteger @{inst}
  (+) = let inst = fst (insts _) in (+) @{inst}
  (-) = let inst = fst (insts _) in (-) @{inst}
  (*) = let inst = fst (insts _) in (*) @{inst}
  abs = let inst = fst (insts _) in abs @{inst}

instance Show (interpNumEq t) where
  show = show @{getShow _}
    where getShow : (t : NumEq) -> Show (interpNumEq t)
          getShow INT = %instance
          getShow INTEGER = %instance
          getShow FLOAT = %instance
          getShow NAT = %instance

getGen : RandomGen r => Gen r (interpNumEq t)
getGen {t=INT} = arbitrary
getGen {t=INTEGER} = arbitrary
getGen {t=FLOAT} = arbitrary
getGen {t=NAT} = arbitrary

coGetGen : RandomGen r => (interpNumEq t) -> Gen r b -> Gen r b
coGetGen {t=INT} = coarbitrary
coGetGen {t=INTEGER} = coarbitrary
coGetGen {t=FLOAT} = coarbitrary
coGetGen {t=NAT} = coarbitrary

instance RandomGen r => Arbitrary r (interpNumEq t) where
  arbitrary = getGen
  coarbitrary = coGetGen

sumList : Num t => List t -> t
sumList [] = 0
sumList (x::xs) = x + sumList xs

instance [ok] (RandomGen r, Testable r b) => Testable r ((t : NumEq) -> List (interpNumEq t) -> b) where
  property f = Prop $ do ty <- arbitrary {a=NumEq}
                         xs <- arbitrary {a=List (interpNumEq ty)}
                         res <- evaluate (f ty xs)
                         pure (arg ty xs res)
  where arg : (t : NumEq) -> (xs : List (interpNumEq t)) -> Result -> Result
        arg t xs res = record { arguments = show t :: show xs :: arguments res } res


total
rearrange : List a -> List a -> List a -> List a
rearrange (x::y::xs) acc1 acc2 = rearrange xs (x::acc1) (y::acc2)
rearrange [x]        acc1 acc2 = acc1 ++ [x] ++ acc2
rearrange []         acc1 acc2 = acc1 ++ acc2


checkSumList : (t : NumEq) -> List (interpNumEq t) -> Bool
checkSumList t xs = sumList xs == sumList (rearrange xs [] [])


myprop : Property StdGen
myprop = Prop $ evaluate (checkSumList INT [1,2,3])


namespace Main
  partial
  main : IO ()
  main = verboseCheck @{ok} checkSumList
