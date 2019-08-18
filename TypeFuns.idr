data Ty = TyNat | TyString | TyBool

evalType : Ty -> Type
evalType TyNat = Nat
evalType TyString = String
evalType TyBool = Bool


initVal : (ty : Ty) -> evalType ty
initVal TyNat = 0
initVal TyString = ""
initVal TyBool = False


AdderType : Nat -> Type
AdderType Z = Int
AdderType (S k) = Int -> AdderType k

adder : (nArgs : Nat) -> (acc : Int) -> AdderType nArgs
adder Z acc = acc
adder (S k) acc = \i => adder k (acc + i)

tstAdder : Int
tstAdder = adder 3 0 1 2 3


data Format = Number Format
  | Str Format
  | Lit String Format
  | End

FormatFunc : Format -> Type
FormatFunc End          = String
FormatFunc (Number fmt) = Int    -> FormatFunc fmt
FormatFunc (Str fmt)    = String -> FormatFunc fmt
FormatFunc (Lit s fmt)  = FormatFunc fmt

myFormat : (fmt : Format) -> FormatFunc fmt
myFormat fmt = runFmt "" fmt where
  runFmt acc End          = acc
  runFmt acc (Number fmt) = \n => runFmt (acc ++ show n) fmt
  runFmt acc (Str fmt)    = \s => runFmt (acc ++ s) fmt
  runFmt acc (Lit s fmt)  = runFmt (acc ++ s) fmt

||| Looks like compiller bug
-- toFormat : String -> Format
-- toFormat s = toFormatInt (unpack s) where
--   toFormatInt [] = End
--   toFormatInt ('%' :: ss) = case ss of
--     'n' :: ss' => Number (toFormatInt ss')
--     's' :: ss' => Str    (toFormatInt ss')
--     ss'        => Lit "%" (toFormatInt ss')
--   toFormatInt (c :: ss) = Lit (singleton c) (toFormatInt ss)

||| Simple solution for prev bug
-- toFormat : String -> Format
-- toFormat s = toFormatInt (unpack s) where
--   toFormatInt [] = End
--   toFormatInt ('%' :: ss) = foo ss where
--     foo ('n' :: ss') = Number (toFormatInt ss')
--     foo ('s' :: ss') = Str    (toFormatInt ss')
--     foo ss'        = Lit "%" (toFormatInt ss')
--   toFormatInt (c :: ss) = Lit (singleton c) (toFormatInt ss)

toFormat : String -> Format
toFormat s = toFormatInt (unpack s) where
  toFormatInt [] = End
  toFormatInt ('%' :: 'n' :: ss) = Number (toFormatInt ss)
  toFormatInt ('%' :: 's' :: ss) = Str    (toFormatInt ss)
  toFormatInt (c :: ss) = Lit (singleton c) (toFormatInt ss)

sprintf : (s : String) -> FormatFunc (toFormat s)
sprintf s = myFormat (toFormat s)


testFormat : Format
testFormat = Lit "Hello, number is: " (Number End)

testRunFmt : String
testRunFmt = myFormat testFormat 55

testRunFmt2 : String
testRunFmt2 = myFormat (Lit "Kek: " (Number (Lit " Puk: " (Number End)))) 1 2

testToFormat : Format
testToFormat = toFormat "Kek %s ; Puk %n"

testRunFmt3 : String
testRunFmt3 = sprintf "Kek %s ; Puk %n" "kek" 55
