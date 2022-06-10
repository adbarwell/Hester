module IdrisUtils.Subset

%default total
%access public export

fst : Subset a p -> a
fst = getWitness

snd : (x : Subset a p) -> (p (fst x))
snd = getProof

uncurry : (q : (x : a) -> p x -> Type) -> (y : Subset a p) -> Type
uncurry q (Element x pf) = q x pf
