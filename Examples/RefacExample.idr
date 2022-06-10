module RefacExample

%default total
%access public export

namespace Init
  sum : List Nat -> Nat
  sum []       = 0
  sum (h :: t) = (+) h (sum t)

  main : Nat
  main = sum [1..4]

namespace GeneraliseDef1
  sum : Nat -> List Nat -> Nat
  sum n []       = n
  sum n (h :: t) = (+) h (sum t)

  main : Nat
  main = sum 0 [1..4]

namespace GeneraliseDef2
  sum : (c : Nat -> Nat -> Nat) -> Nat -> List Nat -> Nat
  sum c n []       = n
  sum c n (h :: t) = c h (sum c n t)

  main : Nat
  main = sum (+) 0 [1..4]

namespace Rename1
  fold : (c : Nat -> Nat -> Nat) -> Nat -> List Nat -> Nat
  fold c n []       = n
  fold c n (h :: t) = c h (fold c n t)

  main : Nat
  main = fold (+) 0 [1..4]

namespace IntroNewDef1
  fold : (c : Nat -> Nat -> Nat) -> Nat -> List Nat -> Nat
  fold c n []       = n
  fold c n (h :: t) = c h (fold c n t)

  main : Nat
  main = sum [1..4]
    where
      sum = fold (+) 0

namespace LiftToTopLevel1
  fold : (c : Nat -> Nat -> Nat) -> Nat -> List Nat -> Nat
  fold c n []       = n
  fold c n (h :: t) = c h (fold c n t)

  sum : List Nat -> Nat
  sum = fold (+) 0

  main : Nat
  main = sum [1..4]
      