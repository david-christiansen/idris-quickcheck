module Random

import System

class RandomGen g where
  next : g -> (Int, g)
  genRange : g -> (Int,Int)
  split : g -> (g, g)

data StdGen = MkStdGen Int Int


stringNum : String -> Int -> Int
stringNum s acc with (strM s)
  stringNum ""             acc | StrNil = acc
  stringNum (strCons x xs) acc | (StrCons x xs) =
    stringNum (assert_smaller (strCons x xs) xs)
              (prim__shlInt 1 acc + cast x)

partial
newStdGen : IO StdGen
newStdGen = do t <- mkForeign (FFun "time" [FPtr] FInt) prim__null
               t' <- mkForeign (FFun "clock" [] FInt)
               urandom <- openFile "/dev/urandom" Read
               stuff <- fread urandom
               closeFile urandom
               urandom <- openFile "/dev/urandom" Read
               stuff' <- fread urandom
               closeFile urandom
               pure $ MkStdGen (stringNum stuff t) (stringNum stuff' t')
--newStdGen = pure (MkStdGen 23462 254334222987)


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
    let left : StdGen = snd (next (MkStdGen new_s1 t2)) in
    let right : StdGen = snd (next (MkStdGen t1 new_s2)) in
    (left, right)



class Random a where
  randomR : RandomGen g => (a, a) -> g -> (a, g)
  random : RandomGen g => g -> (a, g)

instance Random Int where
  randomR (lo, hi) gen = assert_total $ myRandomR lo hi gen
    where
          myRandomR : RandomGen g => Int -> Int -> g -> (Int, g)
          myRandomR lo hi gen = assert_total $
                         if lo > hi
                           then myRandomR hi lo gen
                           else case (f n 1 gen) of
                                  (v, gen') => ((lo + (abs v) `mod` k), gen')
            where
              k : Int
              k = hi - lo + 1
              -- ERROR: b here (2^31-87) represents a baked-in assumption about genRange:
              b : Int
              b = 2147483561

              iLogBase : Int -> Int
              iLogBase i = if b <= 1
                              then 1
                              else if i < b
                                     then 1
                                     else 1 + iLogBase (assert_smaller i (assert_total $ i `div` b))

              n : Int
              n = iLogBase k

              -- Here we loop until we've generated enough randomness to cover the range:
              f : RandomGen g => Int -> Int -> g -> (Int, g)
              f n' acc g =
                if n' <= 0
                   then (acc, g)
                   else let (x,g') = next g in
                        -- We shift over the random bits generated thusfar (* b) and add in the new ones.
                        f (assert_smaller n' $ n' - 1) (x + acc * b) g'
  random gen = next gen

--instance Random Nat where
--  randomR (lo, hi) gen = (randomR (cast {to=Int} lo, cast {to=Int} hi) gen)
--  random gen = let gen' = next gen in
--               (cast (fst gen'), snd gen')

instance Random () where
  randomR ((), ()) gen = ((), gen)
  random gen = ((), gen)
