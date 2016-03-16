import Prelude
import Control.Monad.Fix

fac = fix (\f n -> if n==0 then 1 else n*f(n-1))