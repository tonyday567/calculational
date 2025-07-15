{-# LANGUAGE RebindableSyntax #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Eta reduce" #-}
{-# HLINT ignore "Use foldr" #-}
{-# HLINT ignore "Use foldl" #-}

-- from https://x.com/defnotbeka/status/1898441268159750204

module Prod
  (fac, fac', fac'', faco, faco', facx) where

import Data.Bool
import NumHask.Prelude

fac :: (Multiplicative t, Additive t, Eq t) => t -> t
fac x = prod (range one x)

-- use foldr
prod :: (Multiplicative t) => [t] -> t
prod [] = one
prod (x:xs) = x * prod xs

range :: (Multiplicative a, Additive a, Eq a) => a -> a -> [a]
range x y = bool (x:range (x+one) y) [x] (x==y)

-- problem: prod is not tail-recursive
-- solve: fuse
-- prod_ x xs ~ x * prod xs

-- prod_ x []
-- x * prod [] ~{ spec }
-- x * one ~{def prod}
-- x ~{multiplicative unit}
-- prod_x [] ~ x

-- prod_ x (y:ys)
-- x * prod (y:ys) ~{spec}
-- x * (y * prod ys) ~{def prod}
-- (x * y) * prod ys ~{multiplicative associativity}
-- prod_ (x * y) ys ~{spec}
-- prod_ x (y:ys) ~ prod_ (x*y) ys

-- use foldl
-- tail-recursive: the final calculation inc=volves only values; x,y & ys
prod_ :: Multiplicative t => t -> [t] -> t
prod_ x [] = x
prod_ x (y:ys) = prod_ (x*y) ys

prod' :: (Multiplicative t, FromInteger t) => [t] -> t
prod' xs = prod_ 1 xs

fac' :: (Ring t, FromInteger t, Eq t) => t -> t
fac' x = prod' (range 1 x)

-- Getting stuck on range
-- fac' x
-- prod' (range 1 x) ~ {def fac'}
-- prod_ 1 (range 1 x) ~ {def of prod'}
-- prod_ 1 (bool (1:range 2 x) [1] (1==x)) ~ {def of range}
-- bool (prod_ one (one:range two x)) (prod_ one (pure one)) (1==x) {distributive bool}
-- prod_ one [one] => prod_ (one * one) [] => one {def prod_}
-- bool (prod_ one (one:range two x)) one (one == x)
-- bool (prod_ (one * one) (range two x)) one (one==x) ~{prod_ def}
-- bool (prod_ one (range two x)) one (one==x) ~{multiplicative unit}
-- bool (prod_ one (bool (2:range 3 x) [2] (2==x))) one (one==x) ~{def range}
-- bool (bool (prod_ one (2:range 3 x)) (prod_ one [2]) (2==x)) one (one==x) {distributive bool}
-- bool (bool (prod_ one (2:range 3 x)) 2 (2==x)) one (one==x)


-- if 1==x then 1 else 1 * starProd 1 (numsFromTo 2 x)
-- if 1==x then 1 else starProd 1 (numsFromTo 2 x) ~{unit *}
-- if 1==x then 1 else starProd 1 (if x==2 [2] (2:numsFromTo 3 x)) ~{def numsFromTo}
-- if 1==x then 1 else if 2==x then (starProd 1 [2]) else starProd 1 (2:numsFromTo 3 x) -{if distribution}
-- if 1==x then 1 else if 2==x then (1*2) else starProd (1*2) (numsFromTo 3 x) ~{starProd def}

-- if (1==x) then 1 else if (2==x) 2 else prodStar 2 (range 3 x) [2] (2==x)
-- bool (bool (prod_ one (2:range 3 x)) (prod_ one [2]) (2==x)) one (one==x) {distributive bool}
-- bool (bool (prod_ one (2:range 3 x)) 2 (2==x)) one (one==x)


-- fac' x
-- prod' (range one x) ~{spec}
-- prod_ one (range one x) ~{prod' def}

-- max abstracted fusion
-- fac_ x y z ~ prod_ x (range y z)
-- prod_ x (bool (y:range (y+one) z) [y] (y==z)) ~ {def range}
-- bool (prod_ x (y:range (y+one) z)) (prod_ x [y]) (y==z) ~{bool distribution}
-- prod_ x [y] is prod_ (x*y) [] is x*y
-- bool (prod_ x (y:range (y+one) z)) (x*y) (y==z)
-- bool (prod_ (x*y) (range (y+one) z)) (x*y) (y==z)
-- (x*y) * bool (prod_ one (range (y+one) z)) one (y==z) ~{multiplicative bool distribution}
-- (x*y) * bool (fac_ one (y+one) z) (y==z)

fac_ :: (Multiplicative t, Additive t, Ord t) => t -> t -> t -> t
fac_ x y z = x * y * bool one (fac_ one (y+one) z) (y>z)

fac'' :: (Multiplicative t, Additive t, Ord t) => t -> t
fac'' x = fac_ one one x

-- 1. identifying compound syntax to fuse, based on the syntax that gives rise to non-tail recursion
-- 2. preferring maximally abstracted fusion candidates
-- 3. picking case analysis based on which variables are the root cause of stuckness

faco :: (Multiplicative a, Eq a, Subtractive a) => a -> a
faco n = bool (n*faco(n - one)) one (n==zero)

-- fuse *faco
-- faco_ x y ~ x * faco y

-- faco n = faco_ 1 n

-- faco_ x y
-- x * faco y ~{spec}
-- x * bool (y*faco(y - one)) one (y==zero) ~{def faco}
-- bool (x*y*faco(y-one)) x (y==zero) ~{distributibe * bool}
-- bool (faco_ (x*y) (y-one)) x (y==zero) ~{def faco_}

faco_ :: (Multiplicative a, Subtractive a, Eq a) => a -> a -> a
faco_ x y = bool (faco_ (x*y) (y-one)) x (y==zero)

faco' :: (Multiplicative a, Subtractive a, Eq a) => a -> a
faco' x = faco_ one x


-- https://x.com/defnotbeka/status/1898847444500357537
-- https://x.com/locallycompact/status/1943767542536769969

facx :: (Eq t, FromInteger t, Multiplicative t, Subtractive t) => t -> t
facx n = if n == 1 then 1 else n * facx (n - 1)

-- there exists f and g such that facx = f . g
-- f :: t -> A t
-- g :: A t -> t

-- f (g n) ~ if n==1 then 1 else n * f (g (n-1))

-- the if came from g

-- g n ~ if M then N else P
-- if (n==1) then 1 else n* f(g(n-1))
-- f (g n) ~ f (bool P N M) ~ bool (f P) (f N) M ~ bool (1) (n * f (g (n-1))) (n==1)

-- M ~ n==1
-- f N ~ 1
-- f P ~ n * f(g(n-1)) ~ n * if (M n) then (P n) else (N n)
-- f P ~ if (M n) then (n * P n) else (n * N n)
--

-- N :: a -> t
-- C0 v0 ... vn
--
-- f N = 1 ~ f (C0 v0 ... vn) = 1
-- f P = f (C1 v0 ... vm) ~ n * f(g(n-1))

-- where is the n coming from?
-- f (C1 n v0 ... vm) ~ n * f(g(n-1))

-- g n ~ if n==1 C0 v0 ... vn else C1 n v0 ... vm
-- f (C0 v0 .. vn) ~ 1
-- f (C1 n v0 ... vm) ~ n * f(g(n-1))
--
-- choose the least arguments:

-- g n = if n==1 then C0 else C1 n
-- f C0 = 1
-- f (C1 n) = n * f(g(n-1))

-- Minimal def of A
-- data A t = C0 | C1 t

-- g is the problem in
-- f (C1 n v0 ... vm) ~ n * f(g(n-1))
-- f (C1 n r v0 ... vm) ~ n * f r
-- P ~ C1 n (g(n-1)) u0 ... um
-- g n = if n==1 then C0 else C1 n (g(n-1))

-- data A = C0 | C1 t A
--
-- f C0 = 1
-- f (C1 n r) = n * f r
--


-- let's say the if came from F ...

-- there exists f and g such that facx = f . g
-- f :: t -> A t
-- g :: A t -> t

-- f (g n) ~ if n==1 then 1 else n * f (g (n-1))

-- f ~ if M then N else P
--
-- f (g n) ~ f (bool P N M) ~ bool (f P) (f N) M ~ bool (1) (n * f (g (n-1))) (n==1)
-- f (g n) ~ if (M n) then (N n) else (P n) ~ if (n==1) then (n * f (g(n-1))) else 1
