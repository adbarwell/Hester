module SumStg4 where
  
import Prelude hiding (sum)

fold c n []    = n
fold c n (h:t) = c h (fold n t)

main = sum [1..4]

sum = fold (+) 0
