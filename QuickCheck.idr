module QuickCheck

import System
import Debug.Trace
-- Direct port from the first QuickCheck paper.

%include C "time.h"

--%default total

doMsg : String -> IO ()
doMsg message = do t <- mkForeign (FFun "time" [FPtr] FInt) prim__null
                   putStrLn $ show t ++ "\t" ++ message

repeatN : Nat -> a -> List a
repeatN n x = go n x []
  where go : Nat -> a -> List a -> List a
        go Z     x xs = xs
        go (S n) x xs = go n x (x::xs)

class RandomGen g where
  next : g -> (Int, g)
  genRange : g -> (Int,Int)
  split : g -> (g, g)

data StdGen = MkStdGen Int Int

instance Show StdGen where
  show (MkStdGen i j) = "MkStdGen " ++ show i ++ " " ++ show j

-- Blatantly stolen from Haskell
instance RandomGen StdGen where
  next (MkStdGen s1 s2) =
    let k : Int = assert_total $ s1 `prim__sdivInt` 53668 in
    let s1' : Int  = 40014 * (s1 - k * 53668) - k * 12211 in
    let s1'' : Int = if s1' < 0 then s1' + 2147483563 else s1' in
    let k' : Int = assert_total $ s2 `prim__sdivInt` 52774 in
    let s2' : Int = 40692 * (s2 - k' * 52774) - k' * 3791 in
    let s2'' : Int = if s2' <= 0 then s2' + 2147483399 else s2' in
    let z : Int = s1'' - s2'' in
    let z' : Int = if z < 1 then z + 2147483562 else z in
    (z', MkStdGen s1'' s2'')

  genRange _ = (0, 2147483562)
  split (MkStdGen s1 s2) =
    let gen' : StdGen = snd (next (MkStdGen s1 s2)) in
    let t1 : Int = case gen' of { MkStdGen a b => a } in
    let t2 : Int = case gen' of { MkStdGen a b => b } in
    let new_s1 : Int = if s1 >= 2147483562 || s1 < 1
                         then 1
                         else s1 + 1 in
    let new_s2 : Int = if s2 <= 1 || s2 >= 2147483398
                         then 2147483398
                         else s2 - 1 in
    let left : StdGen = MkStdGen (new_s1 - 1) t2 in
    let right : StdGen = MkStdGen t1 (new_s2 + 1) in
    (left, right)



class Random a where
  randomR : RandomGen g => (a, a) -> g -> (a, g)
  random : RandomGen g => g -> (a, g)

instance Random Int where
  randomR (lo, hi) gen = assert_total $ myRandomR lo hi gen
    where
          myRandomR : RandomGen g => Int -> Int -> g -> (Int, g)
          myRandomR {g=g} lo hi gen = assert_total $
                         if lo > hi
                           then myRandomR hi lo gen
                           else case (f n 1 gen) of
                                  (v, gen') => ((lo + v `mod` k), gen')
            where
              k : Int
              k = hi - lo + 1
              -- ERROR: b here (2^31-87) represents a baked-in assumption about genRange:
              b : Int
              b = 2147483561

              iLogBase : Int -> Int
              iLogBase i = if i < b then 1 else 1 + iLogBase (i `div` b)

              n : Int
              n = iLogBase k

              -- Here we loop until we've generated enough randomness to cover the range:
              f : RandomGen g => Int -> Int -> g -> (Int, g)
              f 0 acc g = (acc, g)
              f n' acc g =
                let (x,g') = next g in
                -- We shift over the random bits generated thusfar (* b) and add in the new ones.
                f (n' - 1) (x + acc * b) g'
  random gen = next gen

--instance Random Nat where
--  randomR (lo, hi) gen = (randomR (cast {to=Int} lo, cast {to=Int} hi) gen)
--  random gen = let gen' = next gen in
--               (cast (fst gen'), snd gen')

instance Random () where
  randomR ((), ()) gen = ((), gen)
  random gen = ((), gen)

data Gen r a = MkGen (Int -> r -> a)

instance Show (Gen r a) where
  show _ = "<gen>"

instance Functor (Gen r) where
  map f (MkGen g) = MkGen $ \i, r => f (g i r)

instance RandomGen r => Applicative (Gen r) where
  pure x = MkGen (\i, r => x)
  (MkGen f) <$> (MkGen x) = MkGen (\i, gen =>
    let new = split gen in
    f i (fst new) (x i (snd new)))

instance RandomGen r => Monad (Gen r) where
  (MkGen m1) >>= k =
    MkGen $ \i, r => let (r1, r2) = split r in
                     let (MkGen m2) = k (m1 i r1) in
                     m2 i r2

choose : (RandomGen r, Random a) => (a, a) -> Gen r a
choose bounds = MkGen (\n, r => fst (randomR bounds r))

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

partial
oneof : RandomGen r => List (Gen r a) -> Gen r a
oneof gens = elements gens >>= id

frequency : RandomGen r => List (Int, Gen r a) -> Gen r a
frequency xs = choose (1, sum (map fst xs)) >>= (flip pick xs)
  where
    pick n ((k,x)::xs) = if n <= k then x else pick (n-k) xs

-- Arbitrary

class RandomGen r => Arbitrary r a where
  arbitrary : Gen r a

instance RandomGen r => Arbitrary r Bool where
  arbitrary = elements [True, False]

instance RandomGen r => Arbitrary r Int where
  arbitrary = sized (\n => choose (-n,n))

instance RandomGen r => Arbitrary r () where
  arbitrary = pure ()

instance (RandomGen r, Arbitrary r a, Arbitrary r b) => Arbitrary r (a, b) where
  arbitrary = liftA2 (\n,m => (n, m)) arbitrary arbitrary

instance (RandomGen r, Arbitrary r a) => Arbitrary r (List a) where
  arbitrary = sized (\n => do i <- choose (0, n)
                              sequence (repeatN (cast i) arbitrary))

class RandomGen r => Coarbitrary r a where
  coarbitrary : a -> Gen r b -> Gen r b

instance RandomGen r => Coarbitrary r Bool where
  coarbitrary b = variant (if b then 0 else 1)

instance RandomGen r => Coarbitrary r Int where
  coarbitrary n =
    if n == 0
      then variant 0
      else if n < 0
             then variant 2 . coarbitrary (-n)
             else variant 1 . coarbitrary (n `div` 2)

instance (RandomGen r, Arbitrary r arg, Coarbitrary r ret )=> Coarbitrary r (arg -> ret) where
  coarbitrary f gen = arbitrary >>= ((flip coarbitrary gen) . f)


--NB doesnt follow paper
instance (RandomGen r, Coarbitrary r a, Arbitrary r b) => Arbitrary r (a -> b) where
  arbitrary = promote (flip coarbitrary arbitrary)

instance (RandomGen r, Coarbitrary r t1, Coarbitrary r t2) => Coarbitrary r (t1, t2) where
  coarbitrary (a, b) = coarbitrary a . coarbitrary b

instance (RandomGen r, Coarbitrary r a) => Coarbitrary r (List a) where
  coarbitrary [] = variant 0
  coarbitrary (x::xs) = variant 1 . coarbitrary x . coarbitrary xs


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
  property : a -> Property r

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

quick : Config
quick = MkConfig 10 --100
          10 -- 1000
          ((+ 3) . (flip div 2))
          (\n, args =>
             let s = show n in
             Strings.(++) s (pack $ repeatN (length s) '\b'))

verbose : Config
verbose = record {
            every = \n, args => show n ++ ":\n" ++ concat (intersperse "\n" args)
          } quick

group : Eq a => List a -> List (List a)
group [] = []
group (x :: xs) = let next = span (==x) xs in
                  let ys = fst next in
                  let zs = snd next in
                  (x::ys) :: group zs




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

  percentage : Int -> Int -> String
  percentage n m = show ((100 * n) `div` m) ++ "%"

  pairLength : List a -> (Int, a)
  pairLength (xs::xss) = (cast (length (xs::xss)), xs)

  entry : (Int, List String) -> String
  entry (n, xs) = percentage n ntest ++ " " ++ concat (intersperse ", " xs)

printTime : String -> IO ()
printTime lbl = do t <- mkForeign (FFun "time" [FPtr] FInt) prim__null
                   putStrLn (lbl ++ " --- " ++ show t)




tests : Config -> Gen StdGen Result -> StdGen -> Int -> Int -> List (List String) -> IO ()
tests config gen rnd0 ntest nfail stamps =
  let s = split rnd0 in
  let rnd1 = fst s in
  let rnd2 = snd s in
  if ntest == maxTest config
    then done "OK, passed" ntest stamps
    else do let ssss = size config ntest
            let result = generate ssss rnd2 gen
            putStrLn (every config ntest (arguments result))
            case ok result of
              Nothing    =>
                tests config gen rnd1 ntest (nfail+1) stamps
              Just True  =>
                tests config gen rnd1 (ntest+1) nfail (stamp result::stamps)
              Just False =>
                putStrLn $ "Falsifiable, after "
                           ++ show ntest
                           ++ " tests:\n"
                           ++ concat (intersperse "\n" (arguments result))



stringNum : String -> Int -> Int
stringNum s acc with (strM s)
  stringNum ""             acc | StrNil = acc
  stringNum (strCons x xs) acc | (StrCons x xs) = stringNum xs (acc + cast x)

newStdGen : IO StdGen
newStdGen = do t <- mkForeign (FFun "time" [FPtr] FInt) prim__null
               t' <- mkForeign (FFun "clock" [] FInt)
               urandom <- openFile "/dev/urandom" Read
               stuff <- fread urandom
               closeFile urandom
               pure $ MkStdGen (stringNum stuff t) (stringNum stuff t')
--newStdGen = pure (MkStdGen 23462 254334222987)

check' : Testable StdGen a => StdGen -> Config -> a -> IO ()
check' rnd config x = tests config (evaluate x) rnd 0 0 []

check : Testable StdGen a => Config -> a -> IO ()
check config x =
  do rnd <- newStdGen
     tests config (evaluate x) rnd 0 0 []



test : Testable StdGen a => a -> IO ()
test = check quick

quickCheck : Testable StdGen a => a -> IO ()
quickCheck = check quick

verboseCheck : Testable StdGen a => a -> IO ()
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
          test n  max config = do check config prop_stupid --prop_RevRev
                                  if n >= max
                                    then pure ()
                                    else test (n+(maxTest config)) max config

  lotsaNumbers : IO ()
  lotsaNumbers = do go !newStdGen 15
                    go !newStdGen 15
                    go !newStdGen 15
    where go : StdGen -> Int -> IO ()
          go _   0 = pure ()
          go gen n = do putStr (show n ++ "  ")
                        let x = next gen
                        putStrLn (show (fst x))
                        go (snd x) (n - 1)

  main : IO ()
  main = testTest


-- Local Variables:
-- idris-packages: ("neweffects")
-- End:

-- -}
