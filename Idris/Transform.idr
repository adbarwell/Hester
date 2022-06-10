module Transform

import public Hs98

import Transform.Rename

%default total
%access public export

{-
  Transformation definition that defines what that transformation changes (but not how those 
  changes occur). No guarantees of equivalence; equivalence will be an additional layer and defined
  for all refactorings. Each refactoring will have a specific transformation.
-}
