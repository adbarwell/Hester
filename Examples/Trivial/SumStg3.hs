module SumStg3 where
  
import Prelude hiding (sum)

fold c n []    = n
fold c n (h:t) = c h (fold n t)

main = fold (+) 0 [1..4]