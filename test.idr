import Data.Vect

main : IO ()
main = putStrLn "hello world"

foo : Int -> Int
foo a = a + 4

lens : List String -> List Nat
lens [] = []
lens (x :: xs) = (length x) :: lens xs

lensv : Vect n String -> Vect n Nat
lensv [] = []
lensv (x :: xs) = length x :: lensv xs


insert : Ord elem => (n : elem) -> (xsSorted: Vect len elem) -> Vect (S len) elem
insert n [] = [n]
insert n l@(x :: xs) = case n < x of
  True  => n :: l
  False => x :: insert n xs

mySort : Ord elem =>  Vect n elem -> Vect n elem
mySort [] = []
mySort (x :: xs) = let xs' = mySort xs in insert x xs'

zeroes : Vect n Nat
-- zeroes {n} =
zeroes {n = Z}     = []
zeroes {n = (S _)} = 0 :: zeroes

v : Vect 10 Nat
v = zeroes

-- zeroes {n=6}


-- data KekType : Type where
--   Kek : KekType
--   Puk : KekType

-- data KekType = Kek | Puk

-- data KekType : Type where
--   Kek : Nat -> KekType
--   Puk : KekType

-- data PukType = Pukt Nat Nat

-- data MyPair : Type -> Type -> Type where
--   MyMkPair : a -> b -> MyPair a b

-- implement one function from another
mutual
  even' : Nat -> Bool
  even' Z = True
  even' (S n) = odd' n

  odd' : Nat -> Bool
  odd' Z = False
  odd' (S n) = even' n

-- rotate : Vect n a -> Vect n a
-- rotate (x :: xs) = xs ++ [x]
--
-- Type mismatch between
--         Vect (len + 1) a (Type of xs ++ [x])
-- and
--         Vect (S len) a (Expected type)
--
-- (len + 1) =/= (S len)     WHYYY???
-- We need to prove it


rotate : Vect n a -> Vect n a
rotate (x :: xs) = insertLast x xs where
  insertLast : a -> Vect k a -> Vect (S k) a
  insertLast a [] = [a]
  insertLast a (x :: xs) = x :: insertLast a xs

tryIndex : Integer -> Vect n a -> Maybe a
tryIndex {n} ind vect = case integerToFin ind n of
  Nothing => Nothing
  (Just i) => Just (index i vect)



record Person where
  constructor MkPerson
  firstName : String
  age : Int

fred : Person
fred = MkPerson "Fred" 18

john : Person
john = record {firstName = "Jonh"} fred


record SizedClass (size : Nat) where
  constructor SizedClassInfo
  students : Vect size Person
  className : String

-- You cant just return value of dep type
readVecFromSomewhere : (len : Nat) -> Vect len String
readVecFromSomewhere Z = []
readVecFromSomewhere (S n) = "qwe" :: readVecFromSomewhere n

-- Dependent pair,
--  we dont know actual vector size in compile time,
--  so we need to return dep pair with size
readVect : IO (len ** Vect len String)
readVect = do
  s <- getLine
  if s == "" then pure (_ ** []) else do -- compiller deduct value of _
    (_ ** ss) <- readVect
    pure (_ ** s :: ss)


flt : (a -> Bool) -> Vect n a -> (p ** Vect p a)
flt _ [] = (_ ** [])
flt p (x :: xs) = let (_ ** xs') = flt p xs in
  if p x then (_ ** x :: xs') else (_ ** xs')

-- zipVects : Vect m a -> Vect n a -> Vest ? a

testZip : IO ()
testZip = do
  (l1 ** v1) <- readVect
  (l2 ** v2) <- readVect
  if l1 /= l2 then ?err else ?kek

Position : Type
Position = (Double, Double)

Polygon : Nat -> Type
Polygon n = Vect n Position

-- the (Fin 5) 3
-- the Nat (cast "42")




boolToType : Bool -> Type
boolToType True = Int
boolToType _    = Bool

boolToTypeVal : (b : Bool) -> (boolToType b)
boolToTypeVal True  = 55
boolToTypeVal False = False
