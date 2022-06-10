module Sum where
  
import Prelude hiding (sum)

sum []    = 0
sum (h:t) = (+) h (sum t)

main = sum [1..4]