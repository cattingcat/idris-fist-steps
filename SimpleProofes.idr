%default total

plus_commutes_Z : (n : Nat) -> (0 + n = n + 0)
plus_commutes_Z Z = Refl
-- plus_commutes_Z (S k) = cong (plus_commutes_Z k)
plus_commutes_Z (S k) = rewrite plus_commutes_Z k in Refl

plus_commutes_S : (m : Nat) -> (n : Nat) -> S (m + n) = m + S n
plus_commutes_S Z n     = Refl
plus_commutes_S (S k) n = rewrite plus_commutes_S k n in Refl

plus_commutes : (m, n : Nat) -> (m + n = n + m)
plus_commutes Z n = plus_commutes_Z n
plus_commutes (S k) n = rewrite plus_commutes k n in  plus_commutes_S n k


not2eq3 : (2 = 3) -> Void
not2eq3 Refl impossible


{-
data Dec : Type -> Type where
  Yes : (prf : prop) -> Dec prop
  No  : (contra : prop -> Void) -> Dec prop
-}

notEqZS : (Z = S k) -> Void
notEqZS Refl impossible

notEqSZ : (S k = Z) -> Void
notEqSZ Refl impossible

notSS : (contra : m = n -> Void) -> S m = S n -> Void
notSS contra Refl = contra Refl


checkEqNatStrong : (m : Nat) -> (n : Nat) -> Dec (m = n)
checkEqNatStrong Z Z = Yes Refl
checkEqNatStrong Z (S n') = No notEqZS
checkEqNatStrong (S m') Z = No notEqSZ
checkEqNatStrong (S m') (S n') = case checkEqNatStrong m' n' of
  Yes Refl => Yes Refl
  No contra => No (notSS contra)
