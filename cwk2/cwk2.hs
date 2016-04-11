---------------------------------------------------------------
-- Language Engineering: COMS22201
-- Assessed Coursework 2: CWK2
-- Question 1: Denotational Semantics of While with read/write
---------------------------------------------------------------
-- This stub file provides a set of Haskell type definitions
-- you should use to implement various functions and examples
-- associated with the denotational semantics of While with
-- read and write statements as previously used in CWK1.
--
-- To answer this question, upload one file "cwk2.hs" to the
-- "CWK2" unit component in SAFE by midnight on 01/05/2016.
--
-- You should ensure your file loads in GHCI with no errors
-- and it does not import any modules (other than Prelude).
--
-- Please note that you will loose marks if your submission
-- is late, incorrectly named, generates load errors,
-- or if you modify any of the type definitions below.
--
-- For further information see the brief at the following URL:
-- https://www.cs.bris.ac.uk/Teaching/Resources/COMS22201/cwk2.pdf
---------------------------------------------------------------

import Prelude hiding (Num)
import qualified Prelude (Num)

type Num = Integer
type Var = String
type Z = Integer
type T = Bool
type State = Var -> Z
type Input  = [Integer]  -- to denote the values read by a program
type Output = [String]   -- to denote the strings written by a program
type IOState = (Input,Output,State)  -- to denote the combined inputs, outputs and state of a program

data Aexp = N Num | V Var | Add Aexp Aexp | Mult Aexp Aexp | Sub Aexp Aexp deriving (Show, Eq, Read)
data Bexp = TRUE | FALSE | Eq Aexp Aexp | Le Aexp Aexp | Neg Bexp | And Bexp Bexp deriving (Show, Eq, Read)
data Stm  = Ass Var Aexp | Skip | Comp Stm Stm | If Bexp Stm Stm | While Bexp Stm
          | Read Var       -- for reading in the value of a variable
          | WriteA Aexp    -- for writing out the value of an arithmetic expression
          | WriteB Bexp    -- for writing out the value of a Boolean expression
          | WriteS String  -- for writing out a given string
          | WriteLn        -- for writing out a string consisting of a newline character
          deriving (Show, Eq, Read)

---------------------------------------------------------------
-- Part A)
--
-- Begin by adding your definitions of the following functions
-- that you previously wrote as part of CWK2p1 and CWk2p2:
---------------------------------------------------------------

fv_aexp :: Aexp -> [Var]
fv_aexp (N a)      = []
fv_aexp (V x)      = [x]
fv_aexp (Add a b)  = union (fv_aexp a) (fv_aexp b)
fv_aexp (Mult a b) = union (fv_aexp a) (fv_aexp b)
fv_aexp (Sub a b)  = union (fv_aexp a) (fv_aexp b)

fv_bexp :: Bexp -> [Var]
fv_bexp (TRUE)    = []
fv_bexp (FALSE)   = []
fv_bexp (Eq a b)  = union (fv_aexp a) (fv_aexp b)
fv_bexp (Le a b)  = union (fv_aexp a) (fv_aexp b)
fv_bexp (Neg a)   = (fv_bexp a)
fv_bexp (And a b) = union (fv_bexp a) (fv_bexp b)

union :: Eq a => [a] -> [a] -> [a]
union [] y = y
union (x:xs) y
             | elem x y == True  = union xs y
             | elem x y == False = union xs (x:y)

a_val :: Aexp -> State -> Z
a_val      (N a) s = a
a_val      (V a) s = s a
a_val (Add x y)  s = (a_val x s) + (a_val y s)
a_val (Mult x y) s = (a_val x s) * (a_val y s)
a_val (Sub x y)  s = (a_val x s) - (a_val y s)

b_val :: Bexp -> State -> T
b_val     TRUE  s = True
b_val     FALSE s = False
b_val (Eq a b)  s = (a_val a s) == (a_val b s)
b_val (Le a b)  s = (a_val a s) <= (a_val b s)
b_val (Neg a)   s =  not (b_val a s)
b_val (And a b) s = (b_val a s)  && (b_val b s)

cond :: (a->T, a->a, a->a) -> (a->a)
cond (b,p,q) s = if (b s) == True then (p s) else (q s)

fix :: (a -> a) -> a
fix f = f (fix f)

update :: State -> Z -> Var -> State
update s i v = x
    where x b
            | b==v = i
            | otherwise = s b

---------------------------------------------------------------
-- Part B))
--
-- Write a function fv_stm with the following signature such that
-- fv_stm p returns the set of (free) variables appearing in p:
---------------------------------------------------------------
fv_stm :: Stm -> [Var]
fv_stm (Ass x y)   = union (fv_aexp y) [x]
fv_stm  Skip       = []
fv_stm (Comp x y)  = union (fv_stm x) (fv_stm y)
fv_stm (If a x y)  = union (union (fv_stm x) (fv_bexp a)) (fv_stm y)
fv_stm (While a x) = union (fv_bexp a) (fv_stm x)
fv_stm (Read x)    = [x]
fv_stm (WriteA x)  = fv_aexp x
fv_stm (WriteB x)  = fv_bexp x
fv_stm (WriteS x)  = []
fv_stm  WriteLn    = []

---------------------------------------------------------------
-- Part C)
--
-- Define a constant fac representing the following program
-- (which you may recall from the file test7.w used in CWK1):
{--------------------------------------------------------------
write('Factorial calculator'); writeln;
write('Enter number: ');
read(x);
write('Factorial of '); write(x); write(' is ');
y := 1;
while !(x=1) do (
  y := y * x;
  x := x - 1
);
write(y);
writeln;
writeln;
---------------------------------------------------------------}
fac   :: Stm
fac   = Comp stm1 (Comp stm2 (Comp stm3 (Comp stm4 (Comp stm5 (Comp stm6 (Comp stm7 (Comp stm8 (Comp stm9 (Comp stm12 (Comp stm2 stm2) ) ) ) ) ) ) ) ) )


stm1  :: Stm
stm1  = WriteS "Factorial calculator"

stm2  :: Stm
stm2  = WriteLn

stm3  :: Stm
stm3  = WriteS "Enter number: "

stm4  :: Stm
stm4  = Read "x"

stm5  :: Stm
stm5  = WriteS "Factorial of "

stm6  :: Stm
stm6  = WriteA (V "x")

stm7  :: Stm
stm7  = WriteS " is "

stm8  :: Stm
stm8  = Ass "y" (N 1)

stm9  :: Stm
stm9  = While (Neg (Eq (V "x") (N 1) ) ) (Comp stm10 stm11)

stm10 :: Stm
stm10 = Ass "y" (Mult (V "y") (V "x"))

stm11 :: Stm
stm11 = Ass "x" (Sub (V "x") (N 1))

stm12 :: Stm
stm12 = WriteA (V "y")
---------------------------------------------------------------
-- Part D)
--
-- Define a constant pow representing the following program
-- (which you may recall from the file test7.w used in CWK1):
{--------------------------------------------------------------
write('Exponential calculator'); writeln;
write('Enter base: ');
read(base);
if 1 <= base then (
  write('Enter exponent: ');
  read(exponent);
  num := 1;
  count := exponent;
  while 1 <= count do (
    num := num * base;
    count := count - 1
  );
  write(base); write(' raised to the power of '); write(exponent); write(' is ');
  write(num)
) else (
  write('Invalid base '); write(base)
);
writeln
---------------------------------------------------------------}
pow :: Stm
pow = Comp ln1 (Comp ln2 (Comp ln3 (Comp ln4 WriteLn)))

ln1 :: Stm
ln1 = Comp (WriteS "Exponential calculator") (WriteLn)

ln2 :: Stm
ln2 = WriteS "Enter base: "

ln3 :: Stm
ln3 = Read "base"

ln4 :: Stm
ln4 = If (Le (N 1) (V "base")) (ln5) (Comp (WriteS "Invalid base ") (WriteA (V "base")))

ln5 :: Stm
ln5 = Comp ln6 (Comp ln7 ln8)

ln6 :: Stm
ln6 = Comp (WriteS "Enter exponent: ") (Comp (Read "exponent") (Comp (Ass "num" (N 1)) (Ass "count" (V "exponent")) ))

ln7 :: Stm
ln7 = While (Le (N 1) (V "count")) (Comp (Ass "num" (Mult (V "num") (V "base") )) (Ass "count"  (Sub (V "count") (N 1) )))

ln8 :: Stm
ln8 = Comp (WriteA (V "base")) (Comp (WriteS " raised to the power of ") (Comp (WriteA (V "exponent")) (Comp (WriteS " is ")  (WriteA (V "num") ) ) ) )

---------------------------------------------------------------
-- Part E)
--
-- Write a function s_ds with the following signature such that
-- s_ds p (i,o,s) returns the result of semantically evaluating
-- program p in state s with input list i and output list o.
---------------------------------------------------------------
cond' :: (c->T, (a,b,c)->(a,b,c), (a,b,c)->(a,b,c))-> (a,b,c)->(a,b,c)
cond' (b,p,q) (i,o,s) = if (b s) == True then (p (i,o,s)) else (q (i,o,s))

s_ds :: Stm -> IOState -> IOState
s_ds (Ass v a)  (i,o,s)  = (i,o,(update s (a_val a s) v))
s_ds (Skip) (i,o,s)      = (i,o,s)
s_ds (Comp a b) (i,o,s)  = x
             where x = s_ds b y
                   y = s_ds a (i,o,s)
s_ds (If x a b)  (i,o,s) = cond' ((b_val x),(s_ds a),(s_ds b)) (i,o,s)
s_ds (While x a) (i,o,s) = fix f (i,o,s) where f g = cond'( (b_val x), g. (s_ds a), id )

s_ds (Read x)   (i,o,s)  = (xs,o ++ ["<"++(show y)++">"],update s y x)
                        where (y:xs) = i

s_ds (WriteA x) (i,o,s)  = (i, o ++ [show (a_val x s)], s)
s_ds (WriteB x) (i,o,s)  = (i, o ++ [show (b_val x s)], s)
s_ds (WriteS x) (i,o,s)  = (i, o ++ [x], s)
s_ds  WriteLn   (i,o,s)  = (i, o ++ ["\n"],s)

stm::Stm
stm=Comp (Comp (Comp (Comp (Comp (Comp (Comp (Comp (Comp (Comp (Comp (Ass "i" (N 10023))(WriteA (V "i")))(WriteLn))(Ass "a" (V "i")))(WriteA (V "a")))(WriteLn))(Ass "j" (N 76)))(WriteA (V "j")))(WriteLn))(Ass "a" (V "j")))(WriteA (V "a")))(WriteLn)

(x,y,z) = s_ds stm ([27,39],[],undefined)

---------------------------------------------------------------
-- Part F)
--
-- Write a function eval with the following signature such that
-- eval p (i,o,s) computes the result of semantically evaluating
-- program p in state s with input list i and output list o; and
-- then returns the final input list and output list together
-- with a list of the variables appearing in the program and
-- their respective values in the final state.
---------------------------------------------------------------

eval :: Stm -> IOState -> (Input, Output, [Var], [Num])
eval a (i,o,s) = (x,y,vars,vals)
    where (x,y,z) = s_ds a (i,o,s)
          vars = fv_stm a
          vals = [z x| x <- vars]
