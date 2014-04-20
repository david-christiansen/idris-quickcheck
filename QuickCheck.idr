module QuickCheck

import System
import Debug.Trace
import System.Random.TF.Random --Random
import System.Random.TF.Gen

-- Direct port from the first QuickCheck paper.

%include C "time.h"

%default total

doMsg : String -> IO ()
doMsg message = do t <- mkForeign (FFun "time" [FPtr] FInt) prim__null
                   putStrLn $ show t ++ "\t" ++ message

repeatN : Nat -> a -> List a
repeatN n x = go n x []
  where go : Nat -> a -> List a -> List a
        go Z     x xs = xs
        go (S n) x xs = go n x (x::xs)



data Gen r a = MkGen (Int -> r -> a)

instance Show (Gen r a) where
  show _ = "<gen>"

instance RandomGen r => Functor (Gen r) where
  map f (MkGen g) = MkGen $ \i, r => f (g i (snd (next r)))

instance RandomGen r => Applicative (Gen r) where
  pure x = MkGen (\i, r => x)
  (MkGen f) <$> (MkGen x) =
    MkGen $ \i, r =>
            let (r1, r2) = split r in
            f i (snd (next r1)) (x i (snd (next r2)))


instance RandomGen r => Monad (Gen r) where
  (MkGen m1) >>= k =
    MkGen $ \i, r => let (r1, r2) = split r in
                     let (MkGen m2) = k (m1 i (snd (next r1))) in
                     m2 i (snd (next r2))

rand : (RandomGen r) => Gen r r
rand = MkGen (\n, r => r)

choose : (RandomGen r, Random a) => (a, a) -> Gen r a
choose bounds = map (fst . randomR bounds) rand

variant : RandomGen r => Nat -> Gen r a -> Gen r a
variant v (MkGen m) = MkGen (\ n, r => m n (getV (S v) r))
  where
    getV : RandomGen r => Nat -> r -> r
    getV Z r = r
    getV (S n) r = getV n (snd (split r))

generate : RandomGen r => Int -> r -> Gen r a -> a
generate n rnd (MkGen m) = let (size, rnd') = randomR (0, n) rnd in
                           m size rnd'

promote : RandomGen r => (a -> Gen r b) -> Gen r (a -> b)
promote f = MkGen (\n, r, x => let MkGen m = f x in m n r )

sized : RandomGen r => (Int -> Gen r a) -> Gen r a
sized fgen = MkGen (\n, r => let MkGen m = fgen n in m n r)

partial
unsafe_get : List a -> Int -> a
unsafe_get (x :: xs) 0 = x
unsafe_get (x :: xs) n = unsafe_get xs (n-1)

total
elements : RandomGen r => List a -> Gen r a
elements {r=r} xs = do i <- choose (the Int 0, (cast $ length xs) - 1)
                       pure $ assert_total (unsafe_get xs i)


oneof : RandomGen r => List (Gen r a) -> Gen r a
oneof gens = elements gens >>= id

frequency : RandomGen r => List (Int, Gen r a) -> Gen r a
frequency xs = choose (1, sum (map fst xs)) >>= (assert_total $ flip pick xs)
  where
    partial
    pick : Int -> List (Int, b) -> b
    pick n ((k,x)::xs) = if n <= k then x else pick (n-k) xs

-- Arbitrary

class RandomGen r => Arbitrary r a where
  arbitrary : Gen r a
  partial coarbitrary : a -> Gen r b -> Gen r b

instance RandomGen r => Arbitrary r () where
  arbitrary = pure ()
  coarbitrary () = variant 0

instance RandomGen r => Arbitrary r Bool where
  arbitrary = elements [True, False]
  coarbitrary True = variant 0
  coarbitrary False = variant 1

instance RandomGen r => Arbitrary r Int where
  arbitrary = sized (\n => choose (-n,n))
  coarbitrary n = variant (cast $ if n >= 0 then 2*n else 2*(-n) + 1)

instance RandomGen r => Arbitrary r Integer where
  arbitrary = sized (\n => map {f=Gen _} cast $ choose (-n, n))
  coarbitrary n = variant (cast $ if n >= 0 then 2*n else 2*(-n) + 1)

instance RandomGen r => Arbitrary r Float where
  arbitrary = sized (\n => do a <- choose (-n*1000000, n*1000000)
                              b <- choose (1, 1000000)
                              return (prim__toFloatInt a / prim__toFloatInt b))
  coarbitrary n = variant (cast $ prim__fromFloatInt (n * 10000.0))

instance RandomGen r => Arbitrary r Nat where
  arbitrary = sized (\n => map {f=Gen _} cast $ choose (0,n))
  coarbitrary = variant

instance (RandomGen r, Arbitrary r t1, Arbitrary r t2) => Arbitrary r (t1, t2) where
  arbitrary = liftA2 (\n,m => (n, m)) arbitrary arbitrary
  coarbitrary (x, y) g = coarbitrary x (coarbitrary y g)

instance (RandomGen r, Arbitrary r a) => Arbitrary r (List a) where
  arbitrary = sized (\n => do i <- choose (0, n)
                              sequence (repeatN (cast i) arbitrary))
  coarbitrary [] = variant 0
  coarbitrary (x::xs) = variant 1 . coarbitrary x . coarbitrary xs


--NB doesnt follow paper
instance (RandomGen r, Arbitrary r t1, Arbitrary r t2) => Arbitrary r (t1 -> t2) where
  arbitrary = promote (flip coarbitrary arbitrary)
  coarbitrary f gen = arbitrary  >>= ((flip coarbitrary gen) . f)

-- Properties
record Result : Type where
  Res : (ok : Maybe Bool) ->  (stamp : List String) -> (arguments : List String) -> Result

instance Show Result where
  show (Res o s a) = "Result {" ++ show o ++ " " ++ show s ++ " " ++ show a ++ "}"

data Property : Type -> Type where
  Prop : Gen r Result -> Property r

nothing : Result
nothing = Res Nothing [] []

result : (RandomGen r) => Result -> Property r
result = Prop . pure

class RandomGen r => Testable r a where
  partial property : a -> Property r

instance RandomGen r => Testable r Bool where
  property b = result (record {ok = Just b} nothing)

instance RandomGen r => Testable r (Property r) where
  property prop = prop

evaluate : (RandomGen r, Testable r a) => a -> Gen r Result
evaluate {r=r} x = case property {r=r} x of
               Prop gen => gen

forAll : (RandomGen r, Show a, Testable r b) => Gen r a -> (a -> b) -> Property r
forAll gen body = Prop $ do a <- gen
                            res <- evaluate (body a)
                            return (arg a res)
  where arg a res = record { arguments = show a :: arguments res } res


instance (RandomGen r, Arbitrary r a, Show a, Testable r b) => Testable r (a -> b) where
  property f = forAll arbitrary f

infix 4 |==>

(|==>) : Testable r a => Bool -> a -> Property r
True  |==> a = property a
False |==> a = result nothing

label : Testable r a => String -> a -> Property r
label s a = Prop (add `map` evaluate a)
  where add res = record { stamp = s :: stamp res } res

classify : Testable r a => Bool -> String -> a -> Property r
classify True name = label name
classify False _ = property

collect : (Show a, Testable r b) => a -> b -> Property r
collect v = label (show v)


-- Running tests


record Config : Type where
  MkConfig : (maxTest : Int) ->
             (maxFail : Int) ->
             (size : Int -> Int) ->
             (every : Int -> List String -> String) ->
             Config

partial
quick : Config
quick = MkConfig 10 --100
          10 -- 1000
          ((+ 3) . (flip div 2))
          (\n, args =>
             let s = show n in
             Strings.(++) s (pack $ repeatN (length s) '\b'))

partial
verbose : Config
verbose = record {
            every = \n, args => show n ++ ":\n" ++ concat (intersperse "\n" args)
          } quick

partial
group : Eq a => List a -> List (List a)
group [] = []
group (x :: xs) = let next = span (==x) xs in
                  let ys = fst next in
                  let zs = snd next in
                  (x::ys) :: group zs



partial
done : String -> Int -> List (List String) -> IO ()
done mesg ntest stamps =
  do putStr ( mesg ++ " " ++ show ntest ++ " tests" ++ table )
 where
  table = display
        . map entry
        . reverse
        . sort
        . map pairLength
        . group
        . sort
        . filter isCons
        $ stamps

  display : List String -> String
  display []  = ".\n"
  display [x] = " (" ++ x ++ ").\n"
  display xs  = ".\n" ++ (concat (intersperse "\n" (map (++ ".") xs)))

  partial
  percentage : Int -> Int -> String
  percentage n m = show ((100 * n) `div` m) ++ "%"

  partial
  pairLength : List a -> (Int, a)
  pairLength (xs::xss) = (cast (length (xs::xss)), xs)

  partial
  entry : (Int, List String) -> String
  entry (n, xs) = percentage n ntest ++ " " ++ concat (intersperse ", " xs)

printTime : String -> IO ()
printTime lbl = do t <- mkForeign (FFun "time" [FPtr] FInt) prim__null
                   putStrLn (lbl ++ " --- " ++ show t)



partial
tests : RandomGen g => Config -> Gen g Result -> g -> Int -> Int -> List (List String) -> IO ()
tests config gen rnd0 ntest nfail stamps =
  let s = split rnd0 in
  let rnd1 = fst s in
  let rnd2 = snd s in
  if ntest == maxTest config
    then done "OK, passed" ntest stamps
    else do let ssss = size config ntest
            putStrLn "fnords"
            let result = generate ssss rnd2 gen
            putStrLn "got a result"
            putStrLn (every config ntest (arguments result))
            putStrLn "did some stuff"
            case ok result of
              Nothing    =>
                do putStrLn "nothing"
                   tests config gen (snd (next rnd1)) ntest (nfail+1) stamps
              Just True  =>
                do putStrLn "Just T"
                   tests config gen (snd (next rnd1)) (ntest+1) nfail (stamp result::stamps)
              Just False =>
                putStrLn $ "Falsifiable, after "
                           ++ show ntest
                           ++ " tests:\n"
                           ++ concat (intersperse "\n" (arguments result))


partial
check' : Testable TFGen a => TFGen -> Config -> a -> IO ()
check' rnd config x = tests config (evaluate x) rnd 0 0 []

partial
check : Testable TFGen a => Config -> a -> IO ()
check config x =
  do putStrLn "getting seed"
     seed <- mkSeed
     putStrLn "seed gotten"
     let rnd = seedTFGen seed
     putStrLn "seeded generator"
     tests config (evaluate x) rnd 0 0 []


partial
test : Testable TFGen a => a -> IO ()
test = check quick

partial
quickCheck : Testable TFGen a => a -> IO ()
quickCheck = check quick

partial
verboseCheck : Testable TFGen a => a -> IO ()
verboseCheck = check verbose

----

prop_RevRev : Eq a => List a -> Bool
prop_RevRev xs = reverse (reverse xs) == xs

prop_listTriv : Eq a => List a -> Bool
prop_listTriv xs = True

stupid : List a -> List a
stupid [] = []
stupid [w,x,y,z] = []
stupid (x::xs) = reverse xs ++ [x]

prop_stupid : Eq a => List a -> Bool
prop_stupid xs = stupid (stupid xs) == xs

triv : () -> Bool
triv () = True

atoi : String -> Maybe Int
atoi "" = Nothing
atoi xs = let xs' = sequence (map getI (unpack xs))
          in map {f=Maybe} mkInt xs'
    where getI : Char -> Maybe Int
          getI c = if c >= '0' && c <= '9'
                     then Just $ prim__charToInt c - prim__charToInt '0'
                     else Nothing
          mkInt : List (Int) -> Int
          mkInt = foldl (\a => \b => 10 * a + b) 0



namespace Main

  %default partial

  testTest : IO ()
  testTest =
    do args <- getArgs
       let numtests : (Int, Maybe Int) =
          case args of
            []                      => (10, Nothing)
            [progname]              => (10, Nothing)
            [progname, howmany]     => let t = maybe 10 id (atoi howmany) in (t, Nothing)
            (progname::howmany::batchsize::_) => let t = maybe 10 id (atoi howmany) in
                                                 let b = maybe t id (atoi batchsize) in
                                                 (t, Just b)
       case numtests of
         (m, Nothing) => check (record {maxTest = m} verbose) triv
         (m, Just b) =>
           let config = record { maxTest = min m b } verbose in
           test 0 m config

    where test : Int -> Int -> Config -> IO ()
          test n  max config = do check config (prop_RevRev {a=Int})
                                  if n >= max
                                    then pure ()
                                    else test (n+(maxTest config)) max config

  main : IO ()
  main = do
     putStrLn "starting"
     testTest
     let gen : Gen TFGen (List Int) = sequence (repeatN 30 arbitrary)
     case gen of
        MkGen f => let xs = f 100 (seedTFGen (MkBlock256 0 1 2 3))
                   in putStrLn (show xs)


-- Local Variables:
-- idris-packages: ("neweffects" "tfrandom")
-- End:

-- -}
