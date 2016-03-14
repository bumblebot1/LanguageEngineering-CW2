---------------------------------------------------------------
-- Language Engineering: COMS22201
-- CWK2p1: Denotational Semantics of Arithmetics and Booleans
-- Due: Sunday 6th March (for formative feedback only)
---------------------------------------------------------------
-- This stub file provides a set of Haskell type definitions
-- that you should use to implement six functions associated 
-- with the denotational semantics of arithmetic and Boolean 
-- expressions in the While programming language as described 
-- in the course text book by Nielson and Nielson.
--
-- These six functions are defined in the lecture notes and 
-- in Chapter 1 of the book. Hints on their implementation 
-- can be found in the lab exercises and the Miranda code 
-- in Appendix B of the book.
--
-- You should submit one file "cwk2p1.hs" into the "CWK2p1"
-- unit component in SAFE by midnight on Sunday 6th March.
--
-- You should ensure your file loads in GHCI with no errors 
-- and it does not import any modules (other than Prelude).
--
-- Please note that your submission will NOT be marked if 
-- it is late, incorrectly named, generates load errors, 
-- or if you modify any of the type definitions below.
---------------------------------------------------------------
  
import Prelude hiding (Num)
import qualified Prelude (Num)

type Num = Integer
type Var = String
type Z = Integer
type T = Bool
type State = Var -> Z

data Aexp = N Num | V Var | Add Aexp Aexp | Mult Aexp Aexp | Sub Aexp Aexp deriving (Show, Eq, Read)
data Bexp = TRUE | FALSE | Eq Aexp Aexp | Le Aexp Aexp | Neg Bexp | And Bexp Bexp deriving (Show, Eq, Read)
data Stm  = Ass Var Aexp | Skip | Comp Stm Stm | If Bexp Stm Stm | While Bexp Stm deriving (Show, Eq, Read)

---------------------------------------------------------------
-- QUESTION 1)
-- Write a function fv_aexp with the following signature such that 
-- fv_aexp a returns the set of (free) variables in a:  
---------------------------------------------------------------

fv_aexp :: Aexp -> [Var]
fv_aexp (N a)      = []
fv_aexp (V x)      = [x]
fv_aexp (Add a b)  = union (fv_aexp a) (fv_aexp b)
fv_aexp (Mult a b) = union (fv_aexp a) (fv_aexp b)
fv_aexp (Sub a b)  = union (fv_aexp a) (fv_aexp b)

---------------------------------------------------------------
-- QUESTION 2)
-- Write a function fv_bexp with the following signature such that 
-- fv_bexp b returns the set of (free) variables in b:  
---------------------------------------------------------------

fv_bexp :: Bexp -> [Var]
fv_bexp (TRUE)    = []
fv_bexp (FALSE)   = []
fv_bexp (Eq a b)  = union (fv_aexp a) (fv_aexp b)
fv_bexp (Le a b)  = union (fv_aexp a) (fv_aexp b)
fv_bexp (Neg a)   = (fv_bexp a)
fv_bexp (And a b) = union (fv_bexp a) (fv_bexp b)
---------------------------------------------------------------
-- QUESTION 3)
-- Write a function subst_aexp with the following signature such that 
-- subst_aexp a1 v a2 returns the result of replacing all occurences of v in a1 by a2:
---------------------------------------------------------------

subst_aexp :: Aexp -> Var -> Aexp -> Aexp
subst_aexp (N a) y c  = N a
subst_aexp (V a) y c
           | a==y = c
           | otherwise = V a 
subst_aexp (Add a b) y c  = Add (subst_aexp a y c)  (subst_aexp b y c)
subst_aexp (Mult a b) y c = Mult (subst_aexp a y c) (subst_aexp b y c)
subst_aexp (Sub a b) y c  = Sub (subst_aexp a y c)  (subst_aexp b y c)
---------------------------------------------------------------
-- QUESTION 4)
-- Write a function subst_bexp with the following signature such that 
-- subst_aexp b v a returns the result of replacing all occurences of v in b by a:
---------------------------------------------------------------

subst_bexp :: Bexp -> Var -> Aexp -> Bexp 
subst_bexp TRUE y c      = TRUE
subst_bexp FALSE y c     = FALSE
subst_bexp (Eq a b) y c  = Eq (subst_aexp a y c) (subst_aexp b y c)
subst_bexp (Le a b) y c  = Le (subst_aexp a y c) (subst_aexp b y c)
subst_bexp (Neg a) y c   = Neg (subst_bexp a y c)
subst_bexp (And a b) y c = And (subst_bexp a y c) (subst_bexp b y c)
---------------------------------------------------------------
-- QUESTION 5)
-- Write a function a_val with the following signature such that
-- a_val a s returns the result of semantically evaluating expression a in state s:
---------------------------------------------------------------

a_val :: Aexp -> State -> Z
a_val      (N a) s = a
a_val      (V a) s = s a
a_val (Add x y)  s = (a_val x s) + (a_val y s)
a_val (Mult x y) s = (a_val x s) * (a_val y s)
a_val (Sub x y)  s = (a_val x s) - (a_val y s)
---------------------------------------------------------------
-- QUESTION 6)
-- Write a function b_val with the following signature such that
-- b_val b s returns the result of semantically evaluating expression b in state s:
---------------------------------------------------------------

b_val :: Bexp -> State -> T
b_val     TRUE  s = True
b_val     FALSE s = False
b_val (Eq a b)  s = (a_val a s) == (a_val b s)
b_val (Le a b)  s = (a_val a s) <= (a_val b s)
b_val (Neg a)   s =  not (b_val a s)
b_val (And a b) s = (b_val a s)  && (b_val b s)

union :: Eq a => [a] -> [a] -> [a]
union [] y = y
union (x:xs) y
             | elem x y == True  = union xs y
             | elem x y == False = union xs (x:y)