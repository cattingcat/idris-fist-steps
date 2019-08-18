import Data.Fin
import Data.Vect

data MyType = Kek | Puk Int

-- You can omit instance keyword
implementation Show MyType where
  show Kek = "k"
  show Puk = "p"

r1 : String
r1 = show Kek

-- named implementation
implementation [namedShow] Show MyType where
  show Kek = "k-"
  show Puk = "p-"

r2 : String
r2 = show @{namedShow} Kek

f : Show a => a -> String
f = show

r22 : String
r22 = f @{namedShow} (Puk 5)

finTest : Fin 50
finTest = FS (FS (FS (FS (FS (FS FZ)))))



-- interface Functor (f : Type -> Type) where
--   map : (m : a -> b) -> f a -> f b

-- [| f a1 a2 a3 ... |]    <=>    f <*> a1 <*> a2 <*> ...

-- !a + !b    -   for applicatives, unwrap m a to a if possible


-- We cant build term with type EqNat for not equal Nats
data EqNat : (a : Nat) -> (b : Nat) -> Type where
  Same : (n : Nat) -> EqNat n n

checkEqNat : (n1 : Nat) -> (n2 : Nat) -> Maybe (EqNat n1 n2)
checkEqNat Z Z = Just (Same 0)
checkEqNat (S n) (S m) = case checkEqNat n m of
  Nothing => Nothing
  Just (Same n) => Just (Same (S n))
checkEqNat _ _ = Nothing


exactLen : (len : Nat) -> (Vect m a) -> Maybe (Vect len a)
exactLen {m} len vect = case checkEqNat m len of
  Nothing => Nothing
  Just (Same n) => Just vect




{-
data (=) : a -> b -> Type
  Refl : x = x              -- x=x - is type
-}

checkEqNat' : (n1 : Nat) -> (n2 : Nat) -> Maybe (n1 = n2)
checkEqNat' Z Z = Just Refl
checkEqNat' (S n) (S m) = case checkEqNat' n m of
  Nothing => Nothing
  Just Refl => Just Refl -- Just proof => Just (cong proof)
checkEqNat' _ _ = Nothing


-- {f : a -> b} - implicit parameter
cong : {f : a -> b} -> (x = y) -> (f x = f y)
cong Refl = Refl


-- rotate : Vect n a -> Vect n a
-- rotate [] = []
-- rotate (x :: xs) = xs ++ [x] -- There are type mismatch
-- -- plus len 1 =/= S len



rotate : Vect n a -> Vect n a
rotate [] = []
rotate (x :: xs) = rotProof (xs ++ [x]) where
  rotProof : Vect (len + 1) a -> Vect (S len) a
  rotProof {len} vs = rewrite plusCommutative 1 len in vs
