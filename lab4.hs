import Prelude hiding (Num)
import qualified Prelude (Num)

type Z = Integer
type T = Bool
type Num = Integer
type Var = String
type State = Var->Z

data Aexp = N Num | V Var
            | Add Aexp Aexp | Mult Aexp Aexp | Sub Aexp Aexp
            deriving (Show, Eq, Read)

data Bexp = TRUE | FALSE
            | Eq Aexp Aexp | Le Aexp Aexp
            | Neg Bexp | And Bexp Bexp
            | Im Bexp Bexp
            deriving (Show, Eq, Read)
            
n_val::Num->Z
n_val n = n

s::State
s "x" = 1
s "y" = 2
s "z" = 3
s a   = 0


a_val::Aexp->State->Z
a_val (N a) s = a
a_val (V a) s = s a
a_val (Add x y) s = (a_val x s) + (a_val y s)
a_val (Mult x y) s = (a_val x s) * (a_val y s)
a_val (Sub x y) s = (a_val x s) - (a_val y s)


b::Bexp
b = Neg ( Eq (Add (V "x") (V "y")) (N 4))

b_val::Bexp->State->T
b_val TRUE s = True
b_val FALSE s = False
b_val (Eq a b) s  = (a_val a s) == (a_val b s)
b_val (Le a b) s  = (a_val a s) <= (a_val b s)
b_val (Neg a) s   =  not (b_val a s)
b_val (And a b) s = (b_val a s)  && (b_val b s)
b_val (Im a b) s  = (b_val (Neg a) s) || (b_val b s) 
