---------------------------------------------------------------
-- Language Engineering: COMS22201
-- CWK2p2: Denotational Semantics of statements
-- Due: Sunday 20th March (for formative feedback only)
---------------------------------------------------------------
-- This stub file provides a set of Haskell type definitions
-- you should use to implement some functions and examples
-- associated with the denotational semantics of program
-- statements in the While programming language as described
-- in the course text book by Nielson and Nielson.
--
-- These functions are defined in the lecture notes and
-- in Chapter 4 of the book. Hints on their implementation
-- can be found in the lab exercises and the Miranda code
-- in Appendix D of the book.
--
-- You should submit one file "cwk2p2.hs" into the "CWK2p2"
-- unit component in SAFE by midnight on Sunday 20th March.
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
-- QUESTION 0)
-- First include your definitions of a_val and b_val from CWK2p1
---------------------------------------------------------------

a_val :: Aexp -> State -> Z
a_val      (N a) s = a
a_val      (V a) s = s a
a_val (Add x y)  s = (a_val x s) + (a_val y s)
a_val (Mult x y) s = (a_val x s) * (a_val y s)
a_val (Sub x y)  s = (a_val x s) - (a_val y s)

b_val :: Bexp -> State -> T
b_val     TRUE  s  = True
b_val     FALSE s  = False
b_val (Eq a b)  s  = (a_val a s) == (a_val b s)
b_val (Le a b)  s  = (a_val a s) <= (a_val b s)
b_val (Neg a)   s  =  not (b_val a s)
b_val (And a b) s  = (b_val a s)  && (b_val b s)

---------------------------------------------------------------
-- QUESTION 1)
-- Write a function cond with the following signature such that
-- cond (b,p,q) s returns p s if b s is true and q s otherwise
---------------------------------------------------------------

cond :: (a->T, a->a, a->a) -> (a->a)
cond (b,p,q) s
            | b s == True         = p s
            | otherwise           = q s

---------------------------------------------------------------
-- QUESTION 2)
-- Write a function fix with the following signature such that
-- fix f simply returns f (fix f)
---------------------------------------------------------------

fix :: (a -> a) -> a
fix f = f (fix f)

---------------------------------------------------------------
-- QUESTION 3)
-- Write a function update with the following signature such that
-- update s i v returns the state update s[v |-> i]
-- i.e. state obtained from s by updating the value of v to i
---------------------------------------------------------------

update :: State -> Z -> Var -> State
update s i v = x
    where x b
            | b==v = i
            | otherwise = s b

---------------------------------------------------------------
-- QUESTION 4)
-- Write a function s_ds with the following signature such that
-- s_ds p s returns the result of semantically evaluating program p in state s:
---------------------------------------------------------------

s_ds :: Stm -> State -> State
s_ds (Ass v a)   s = update s (a_val a s) v
s_ds (Skip) s      = s
s_ds (Comp a b)  s = x
             where x = s_ds b y
                   y = s_ds a s
s_ds (If x a b)  s = cond ((b_val x),(s_ds a),(s_ds b)) s
s_ds (While x a) s = fix f s where f g = cond( (b_val x), g. (s_ds a), (s_ds Skip) )


---------------------------------------------------------------
-- QUESTION 5)
-- Define a constant p that represents the following program
-- y:=1 ; while Â¬(x=1) do (y:=y*x; x:=x-1)
---------------------------------------------------------------

p :: Stm
p = Comp (Ass "y" (N 1)) (While (Neg (Eq (V "x") (N 1))) (Comp (Ass "y" (Mult (V "y") (V "x"))) (Ass "x" (Sub (V "x") (N 1) ))))

---------------------------------------------------------------
-- QUESTION 6)
-- Define a constant s that represents the state that maps
-- x to 5, y to 2, and every other variable to 0
---------------------------------------------------------------

s :: State
s "x" = 5
s "y" = 2
s  a  = 0

---------------------------------------------------------------
-- QUESTION 7)
-- Verify using your denotational semantics that p computes 5!
-- when it is applied to the state s
---------------------------------------------------------------
q = s_ds p s
