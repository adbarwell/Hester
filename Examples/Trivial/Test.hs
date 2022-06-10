<<<<<<< HEAD
module Test where

-- f c x =
--   case x == c of
--     True -> x
--     False -> c

-- main = putStrLn (show (f undefined 42))

-- f (C1 x y (C2 True (C3 z))) = 42

-- f x = x

-- f x y = x

-- f True x = x
-- f False x = 42

-- f x = y where y = 42

{-
f x = g x 2

g x y = y
-}

-- f x = x where x = 42

{-
f x = g x z
  where
    g x y = h y where h x = x

    z = 42
-}

{-
f x = g x z where
  g a b = b
  z = 42
-}

mkList4 = undefined
plus = (+)

sum n [] = n
sum n (h:t) = plus h rest 
  where rest = (sumRest n t) where sumRest n t = sum n t

main = sum 0 (mkList4 1 2 3 4)
=======
module Test where

-- f c x =
--   case x == c of
--     True -> x
--     False -> c

-- main = putStrLn (show (f undefined 42))

-- f (C1 x y (C2 True (C3 z))) = 42

-- f x = x

-- f x y = x

-- f True x = x
-- f False x = 42

-- f x = y where y = 42

{-
f x = g x 2

g x y = y
-}

-- f x = x where x = 42

{-
f x = g x z
  where
    g x y = h y where h x = x

    z = 42
-}

{-
f x = g x z where
  g a b = b
  z = 42
-}

-- mkList4 = undefined
-- plus = (+)

sum n [] = n
sum n (h:t) = plus h (sum n t)
  where
    sumRest n t = sum n t

main = sum 0 (enumFromTo 1 4)
>>>>>>> 73854e529a1527d2e0542a23225888af7bd66b13
