--Patrky Wegrzyn
--Logika 2017
--Zadanie 3
--Proving props with Haskell type checker

--Bez tego Haskell rzuca bledami na prawo i lewo
{-# LANGUAGE ScopedTypeVariables #-}
--Cytujac wiki HS'a: "Scoped Type Variables are an extension to Haskell's 
--type system that allow free type variables to be re-used in the scope of a function."

--Traktuje moja propozycje jako pewien typ. Jesli uda mi sie
--znalezc wartosc o takim wlasnie typie (czyli mieszkanca danego
--typu, to automatycznie dowodzi slusznosci mojej propozycji.

--Na przyklad tutaj:
--Moja propozycja do udowodnienia:
--Theorem impl_rozdz : (A -> B) -> (A -> C) -> A -> B -> C
--typ odpowiadajacy mojej propozycji to:
impl_rozdz :: (a -> b) -> (a -> c) -> a -> b -> c
--przykladowa wartosc o takim typie:
impl_rozdz = \(f::a -> b) -> \(g::a -> c) -> \(h::a) -> \(i::b) -> g h
--fakt, ze type-checker Haskella nie zgosil bledu oznacza, ze
--powyzsza wartosc faktycznie jest takiego wlasnie typu, co implikuje, ze
--powyzszy typ jest zamieszkany (przez conajmniej jedna wartosc, potencjalnie wiecej),
--czyli propozycja jest prawdziwa.

--Theorem impl_komp : (A -> B) -> (B -> C) -> A -> C
impl_komp :: (a -> b) -> (b -> c) -> a -> c
impl_komp = \(f::a -> b) -> \(g::b -> c) -> \(h::a) -> g (f h)

--Theorem impl_perm : (A -> B -> C) -> B -> A -> C
impl_perm :: (a -> b -> c) -> b -> a -> c
impl_perm = \(f::a -> b -> c) -> \(g::b) -> \(h::a) -> f h g

--Theorem impl_conj : A -> B -> A /\ B
impl_conj :: a -> b -> (a, b)
impl_conj = \(f::a) -> \(g::b) -> (f, g)

--Theorem conj_elim_l : A /\ B -> A
conj_elim_l :: (a, b) -> a
conj_elim_l = \(f@(first,second)::(a,b)) -> first

--Potrzebne dalej do repreztowania "disjoint union"
data Albo a b = Lewy a | Prawy b

--Theorem disj_intro_l : A -> A \/ B
disj_into_l :: a -> (Albo a b)
disj_into_l = \(f::a) -> Lewy f

--Theorem rozl_elim : A \/ B -> (A -> C) -> (B -> C) -> C
rozl_elim :: (Albo a b) -> (a -> c) -> (b -> c) -> c
rozl_elim (Lewy f::(Albo a b)) (g::(a->c)) (h::(b->c)) = g f
rozl_elim (Prawy f::(Albo a b)) (g::(a->c)) (h::(b->c)) = h f

--Theorem diamencik : (A -> B) -> (A -> C) -> (B -> C -> D) -> A -> D
diamencik :: (a -> b) -> (a -> c) -> (b -> c -> d) -> a -> d
diamencik = \(f::a -> b) -> \(g::a -> c) -> \(h::b -> c -> d) -> \(i::a) -> (h (f i)) (g i)

--Theorem slaby_peirce : ((((A -> B) -> A) -> A) -> B) -> B
slaby_peirce :: ((((a -> b) -> a) -> a) -> b) -> b
slaby_peirce = \(f::(((a -> b) -> a) -> a) -> b) -> f (\g -> g (\h -> f (\i -> h)))

--Theorem rozl_impl_rozdz : (A \/ B -> C) -> (A -> C) /\ (B -> C)
rozl_impl_rozdz :: ((Albo a b) -> c) -> ((a -> c), (b -> c))
rozl_impl_rozdz = \(f::Albo a b -> c) -> (\(g::a) -> f (Lewy g), \(g::b) -> f (Prawy g))

--Theorem rozl_impl_rozdz_odw : (A -> C) /\ (B -> C) -> A \/ B -> C
rozl_impl_rozdz_odw :: ((a -> c), (b -> c)) -> (Albo a b) -> c
rozl_impl_rozdz_odw (f@(first,second)::((a -> c), (b -> c))) (Lewy h::(Albo a b)) = first h
rozl_impl_rozdz_odw (f@(first,second)::((a -> c), (b -> c))) (Prawy h::(Albo a b)) = second h

--Funkcja pomocnicza:
pair a b = (a, b)

--Theorem curry : (A /\ B -> C) -> A -> B -> C
curry' :: ((a, b) -> c) -> a -> b -> c
curry' = \(f::(a, b) -> c) -> \(g::a) -> \(h::b) -> f (pair g h)

--Theorem uncurry : (A -> B -> C) -> A /\ B -> C
uncurry' :: (a -> b -> c) -> (a, b) -> c
uncurry' = \(f::a -> b -> c) -> \(g@(first,second)::(a,b)) -> f first second