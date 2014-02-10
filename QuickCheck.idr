module QuickCheck

-- Direct port from the first QuickCheck paper. Slow; needs work.

%include C "time.h"

--%default total

repeatN : Nat -> a -> List a
repeatN Z x = []
repeatN (S n) x = x :: repeatN n x

class RandomGen g where
  next : g -> (Int, g)
  genRange : g -> (Int,Int)
  split : g -> (g, g)

data StdGen = MkStdGen Int Int

-- Blatantly stolen from Haskell
instance RandomGen StdGen where
  next (MkStdGen s1 s2) = (z', MkStdGen s1'' s2'')
    where
          %assert_total k : Int
          k    = s1 `prim__sdivInt` 53668
          s1' : Int
          s1'  = 40014 * (s1 - k * 53668) - k * 12211
          s1'' : Int
          s1'' = if s1' < 0 then s1' + 2147483563 else s1'
          %assert_total k' : Int
          k'   = s2 `prim__sdivInt` 52774
          s2' : Int
          s2'  = 40692 * (s2 - k' * 52774) - k' * 3791
          s2'' : Int
          s2'' = if s2' < 0 then s2' + 2147483399 else s2'
          z : Int
          z  = s1'' - s2''
          z' : Int
          z' = if z < 1 then z + 2147483562 else z

  genRange _ = (0, 2147483562)
  split (MkStdGen s1 s2) = (left, right)
    where gen' : StdGen
          gen' = snd (next (MkStdGen s1 s2))
          t1 : Int
          t1 = case gen' of { MkStdGen a b => a}
          t2 : Int
          t2 = case gen' of { MkStdGen a b => b}
          new_s1 : Int
          new_s1 = if s1 == 2147483562
                     then 1
                     else s1 + 1
          new_s2 : Int
          new_s2 = if s2 == 1
                     then 2147483398
                     else s2 - 1
          left : StdGen
          left = MkStdGen new_s1 t2
          right : StdGen
          right = MkStdGen t1 new_s2



class Random a where
  randomR : RandomGen g => (a, a) -> g -> (a, g)
  random : RandomGen g => g -> (a, g)

instance Random Int where
  randomR (lo, hi) gen = if hi <= lo
                           then (lo, (snd (next gen)))
                           else let (x, gen') = next gen in
                                let d = (hi - lo) in
                                (lo + (mod x d), gen')
  random gen = next gen

instance Random Nat where
  randomR (lo, hi) gen = if hi <= lo
                           then (lo, snd (next gen))
                           else let (x, gen') = next gen in
                                let d = (hi - lo) in
                                (lo + ((cast {to=Nat} x) `mod` d), gen')
  random gen = let gen' = next gen in
               (cast (fst gen'), snd gen')

instance Random () where
  randomR ((), ()) gen = ((), gen)
  random gen = ((), gen)

data Gen r a = MkGen (Int -> r -> a)

instance Functor (Gen r) where
  map f (MkGen g) = MkGen $ \i, r => f (g i r)

instance Applicative (Gen r) where
  pure x = MkGen (\i, r => x)
  (MkGen f) <$> (MkGen x) = MkGen (\i, r => f i r (x i r))

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
sized fgen = MkGen (\n, r =>
                   let MkGen m = fgen n in m n r)


%assert_total
get : Vect (S n) a -> Int -> a
get {n=n} {a=a} xs i = go (S n) xs i
  where go : (m : Nat) -> Vect m a -> Int -> a
        go Z [] i = go (S n) xs i
        go (S m) (y :: ys) i = if i < 0
                                 then go (S m) (y :: ys) (i + (cast (S n)))
                                 else if i == 0 then y else go m ys (i-1)



elements : RandomGen r => Vect (S n) a -> Gen r a
elements {r=r} {n=n} xs = do i <- choose (the Int 0, cast (S n))
                             pure $ get xs i

oneof : RandomGen r => Vect (S n) (Gen r a) -> Gen r a
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


tests : Config -> Gen StdGen Result -> StdGen -> Int -> Int -> List (List String) -> IO ()
tests config gen rnd0 ntest nfail stamps =
  let (rnd1, rnd2) = split rnd0 in
  let result = generate (size config ntest) rnd2 gen in
  if ntest == maxTest config
    then done "OK, passed" ntest stamps
    else do putStr (every config ntest (arguments result))
            case ok result of
              Nothing    =>
                tests config gen rnd1 ntest (nfail+1) stamps
              Just True  =>
                tests config gen rnd1 (ntest+1) nfail (stamp result::stamps)
              Just False =>
                putStr ( "Falsifiable, after "
                      ++ show ntest
                      ++ " tests:\n"
                      ++ concat (intersperse "\n" (arguments result))
                       )





newStdGen : IO StdGen
--newStdGen = do t <- mkForeign (FFun "time" [FPtr] FInt) prim__null
--               pure $ MkStdGen t t
newStdGen = pure (MkStdGen 23462 254334222987)

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


triv : () -> Bool
triv () = True

namespace Main
  main : IO ()
  main = quickCheck prop_RevRev --prop_RevRev



-- Local Variables:
-- idris-packages: ("neweffects")
-- End:

-- -}
