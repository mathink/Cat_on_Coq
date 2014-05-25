{-# OPTIONS_GHC -cpp -fglasgow-exts #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Yoneda where

import qualified Prelude


import qualified GHC.Base
unsafeCoerce :: a -> b
unsafeCoerce = GHC.Base.unsafeCoerce#

__ :: any
__ = Prelude.error "Logical or arity value used"

data Type =
   Builder

type Carrier = ()

type Type0 =
  Carrier -> Carrier
  -- singleton inductive, whose constructor was builder
  
function :: Type -> Type -> Type0 -> Carrier -> Carrier
function x y t =
  t

setoid :: Type -> Type -> Type
setoid x y =
  Builder

compose :: Type -> Type -> Type -> Type0 -> Type0 -> Type0
compose x y z f g x0 =
  function y z g (function x y f x0)

id :: Type -> Type0
id x x0 =
  x0

data Type1 =
   Builder0 (() -> () -> Type) (() -> () -> () -> Carrier -> Carrier ->
                               Carrier) (() -> Carrier)

type Obj = ()

arr :: Type1 -> Obj -> Obj -> Type
arr t =
  case t of {
   Builder0 arr0 compose2 id3 -> arr0}

compose0 :: Type1 -> Obj -> Obj -> Obj -> Carrier -> Carrier -> Carrier
compose0 t =
  case t of {
   Builder0 arr0 compose2 id3 -> compose2}

id0 :: Type1 -> Obj -> Carrier
id0 t =
  case t of {
   Builder0 arr0 compose2 id3 -> id3}

data Morphism =
   Morphism_triple Obj Obj Carrier

morphism_rect :: Type1 -> (Obj -> Obj -> Carrier -> a1) -> Morphism -> a1
morphism_rect c f m =
  case m of {
   Morphism_triple x x0 x1 -> f x x0 x1}

morphism_rec :: Type1 -> (Obj -> Obj -> Carrier -> a1) -> Morphism -> a1
morphism_rec c =
  morphism_rect c

setoids :: Type1
setoids =
  Builder0 (unsafeCoerce setoid) (unsafeCoerce compose) (unsafeCoerce id)

data Type2 =
   Make_Functor (Obj -> Obj) (Obj -> Obj -> Carrier)

fobj :: Type1 -> Type1 -> Type2 -> Obj -> Obj
fobj c d t =
  case t of {
   Make_Functor fobj0 fmap0 -> fobj0}

fmap :: Type1 -> Type1 -> Type2 -> Obj -> Obj -> Carrier
fmap c d t =
  case t of {
   Make_Functor fobj0 fmap0 -> fmap0}

setoid0 :: Type1 -> Type1 -> Type
setoid0 c d =
  Builder

compose1 :: Type1 -> Type1 -> Type1 -> Type2 -> Type2 -> Type2
compose1 c d e f g =
  Make_Functor (\x -> fobj d e g (fobj c d f x)) (\x y ->
    unsafeCoerce
      (compose (arr c x y) (arr d (fobj c d f x) (fobj c d f y))
        (arr e (fobj d e g (fobj c d f x)) (fobj d e g (fobj c d f y)))
        (unsafeCoerce (fmap c d f x y))
        (unsafeCoerce (fmap d e g (fobj c d f x) (fobj c d f y)))))

id1 :: Type1 -> Type2
id1 c =
  Make_Functor (\x -> x) (\x y -> unsafeCoerce (id (arr c x y)))

type Type3 =
  Obj -> Carrier
  -- singleton inductive, whose constructor was Build_type
  
natrans :: Obj -> Obj -> Carrier -> Carrier -> Type3 -> Obj -> Carrier
natrans c d f g t =
  t

setoid1 :: Obj -> Obj -> Carrier -> Carrier -> Type
setoid1 c d f g =
  Builder

v_compose :: Obj -> Obj -> Carrier -> Carrier -> Carrier -> Type3 -> Type3 ->
             Type3
v_compose c d f g h s t x =
  compose0 (unsafeCoerce d)
    (fobj (unsafeCoerce c) (unsafeCoerce d) (unsafeCoerce f) x)
    (fobj (unsafeCoerce c) (unsafeCoerce d) (unsafeCoerce g) x)
    (fobj (unsafeCoerce c) (unsafeCoerce d) (unsafeCoerce h) x)
    (natrans c d f g s x) (natrans c d g h t x)

h_compose :: Obj -> Obj -> Obj -> Carrier -> Carrier -> Carrier -> Carrier ->
             Type3 -> Type3 -> Type3
h_compose c d e f g f' g' s t x =
  compose0 (unsafeCoerce e)
    (fobj (unsafeCoerce d) (unsafeCoerce e) (unsafeCoerce f')
      (fobj (unsafeCoerce c) (unsafeCoerce d) (unsafeCoerce f) x))
    (fobj (unsafeCoerce d) (unsafeCoerce e) (unsafeCoerce g')
      (fobj (unsafeCoerce c) (unsafeCoerce d) (unsafeCoerce f) x))
    (fobj (unsafeCoerce d) (unsafeCoerce e) (unsafeCoerce g')
      (fobj (unsafeCoerce c) (unsafeCoerce d) (unsafeCoerce g) x))
    (natrans d e f' g' t
      (fobj (unsafeCoerce c) (unsafeCoerce d) (unsafeCoerce f) x))
    (function
      (arr (unsafeCoerce d)
        (fobj (unsafeCoerce c) (unsafeCoerce d) (unsafeCoerce f) x)
        (fobj (unsafeCoerce c) (unsafeCoerce d) (unsafeCoerce g) x))
      (arr (unsafeCoerce e)
        (fobj (unsafeCoerce d) (unsafeCoerce e) (unsafeCoerce g')
          (fobj (unsafeCoerce c) (unsafeCoerce d) (unsafeCoerce f) x))
        (fobj (unsafeCoerce d) (unsafeCoerce e) (unsafeCoerce g')
          (fobj (unsafeCoerce c) (unsafeCoerce d) (unsafeCoerce g) x)))
      (unsafeCoerce
        (fmap (unsafeCoerce d) (unsafeCoerce e) (unsafeCoerce g')
          (fobj (unsafeCoerce c) (unsafeCoerce d) (unsafeCoerce f) x)
          (fobj (unsafeCoerce c) (unsafeCoerce d) (unsafeCoerce g) x)))
      (natrans c d f g s x))

dom_compose :: Obj -> Obj -> Obj -> Carrier -> Carrier -> Carrier -> Type3 ->
               Type3
dom_compose b c d f g e s x =
  natrans c d f g s
    (fobj (unsafeCoerce b) (unsafeCoerce c) (unsafeCoerce e) x)

cod_compose :: Obj -> Obj -> Obj -> Carrier -> Carrier -> Type3 -> Carrier ->
               Type3
cod_compose c d e f g s h x =
  function
    (arr (unsafeCoerce d)
      (fobj (unsafeCoerce c) (unsafeCoerce d) (unsafeCoerce f) x)
      (fobj (unsafeCoerce c) (unsafeCoerce d) (unsafeCoerce g) x))
    (arr (unsafeCoerce e)
      (fobj (unsafeCoerce d) (unsafeCoerce e) (unsafeCoerce h)
        (fobj (unsafeCoerce c) (unsafeCoerce d) (unsafeCoerce f) x))
      (fobj (unsafeCoerce d) (unsafeCoerce e) (unsafeCoerce h)
        (fobj (unsafeCoerce c) (unsafeCoerce d) (unsafeCoerce g) x)))
    (unsafeCoerce
      (fmap (unsafeCoerce d) (unsafeCoerce e) (unsafeCoerce h)
        (fobj (unsafeCoerce c) (unsafeCoerce d) (unsafeCoerce f) x)
        (fobj (unsafeCoerce c) (unsafeCoerce d) (unsafeCoerce g) x)))
    (natrans c d f g s x)

id2 :: Obj -> Obj -> Carrier -> Type3
id2 c d f x =
  id0 (unsafeCoerce d)
    (fobj (unsafeCoerce c) (unsafeCoerce d) (unsafeCoerce f) x)

fun :: Obj -> Obj -> Type1
fun c d =
  Builder0 (setoid1 c d) (unsafeCoerce (v_compose c d))
    (unsafeCoerce (id2 c d))

function0 :: Type
function0 =
  Builder

sets :: Type1
sets =
  Builder0 (\_ _ -> function0) (\_ _ _ f g ->
    unsafeCoerce (\x -> unsafeCoerce g (unsafeCoerce f x))) (\_ ->
    unsafeCoerce (\x -> x))

op_Category :: Type1 -> Type1
op_Category c =
  Builder0 (\x y -> arr c y x) (\x y z f g -> compose0 c z y x g f) (\x ->
    id0 c x)

fmap_HomFunctor :: Obj -> Obj -> Obj -> Obj -> Carrier -> Carrier
fmap_HomFunctor c x y z g =
  unsafeCoerce (\f -> compose0 (unsafeCoerce c) x y z f g)

homFunctor :: Obj -> Obj -> Carrier
homFunctor c x =
  unsafeCoerce (Make_Functor (\y -> unsafeCoerce (arr (unsafeCoerce c) x y))
    (\y z -> unsafeCoerce (\g -> fmap_HomFunctor c x y z g)))

fmap_CoHomFunctor :: Obj -> Obj -> Obj -> Obj -> Carrier -> Carrier
fmap_CoHomFunctor c x y z f =
  unsafeCoerce (\g -> compose0 (unsafeCoerce c) x y z f g)

coHomFunctor :: Obj -> Obj -> Carrier
coHomFunctor c z =
  unsafeCoerce (Make_Functor (\x -> unsafeCoerce (arr (unsafeCoerce c) x z))
    (\y x -> unsafeCoerce (\f -> fmap_CoHomFunctor c x y z f)))

yoneda :: Obj -> Obj -> Obj -> Carrier
yoneda c f x =
  unsafeCoerce (\alpha ->
    function
      (unsafeCoerce
        (fobj (unsafeCoerce c) setoids (unsafeCoerce (homFunctor c x)) x))
      (unsafeCoerce (fobj (unsafeCoerce c) setoids (unsafeCoerce f) x))
      (unsafeCoerce
        (natrans c (unsafeCoerce setoids) (homFunctor c x) f
          (unsafeCoerce alpha) x)) (id0 (unsafeCoerce c) x))

inv_yoneda :: Obj -> Obj -> Obj -> Carrier
inv_yoneda c f x =
  unsafeCoerce (\x0 ->
    unsafeCoerce (\a ->
      unsafeCoerce (\f0 ->
        function
          (unsafeCoerce (fobj (unsafeCoerce c) setoids (unsafeCoerce f) x))
          (unsafeCoerce (fobj (unsafeCoerce c) setoids (unsafeCoerce f) a))
          (unsafeCoerce
            (function (arr (unsafeCoerce c) x a)
              (arr setoids (fobj (unsafeCoerce c) setoids (unsafeCoerce f) x)
                (fobj (unsafeCoerce c) setoids (unsafeCoerce f) a))
              (unsafeCoerce
                (fmap (unsafeCoerce c) setoids (unsafeCoerce f) x a)) f0)) x0)))

map_natrans_fmap_YonedaFunctor :: Obj -> Obj -> Obj -> Obj -> Carrier ->
                                  Carrier
map_natrans_fmap_YonedaFunctor c z y x f =
  unsafeCoerce (\g -> compose0 (unsafeCoerce c) x y z f g)

natrans_fmap_YonedaFunctor :: Obj -> Obj -> Obj -> Carrier -> Carrier
natrans_fmap_YonedaFunctor c y x f =
  unsafeCoerce (\z -> map_natrans_fmap_YonedaFunctor c z y x f)

fmap_YonedaFunctor :: Obj -> Obj -> Obj -> Carrier
fmap_YonedaFunctor c y x =
  unsafeCoerce (\f -> natrans_fmap_YonedaFunctor c y x f)

yonedaFunctor :: Obj -> Type2
yonedaFunctor c =
  Make_Functor (homFunctor c) (\y x -> fmap_YonedaFunctor c y x)

fmap_CoYonedaFunctor :: Obj -> Obj -> Obj -> Carrier -> Type3
fmap_CoYonedaFunctor c x y f z =
  unsafeCoerce (\g -> compose0 (unsafeCoerce c) z x y g f)

coYonedaFunctor :: Obj -> Type2
coYonedaFunctor c =
  Make_Functor (coHomFunctor c) (\x y ->
    unsafeCoerce (\f -> unsafeCoerce (fmap_CoYonedaFunctor c x y f)))

function_compose :: (a1 -> a2) -> (a2 -> a3) -> a1 -> a3
function_compose f g =
  unsafeCoerce
    (function
      (unsafeCoerce
        (fobj sets setoids
          (unsafeCoerce
            (fobj (op_Category sets)
              (fun (unsafeCoerce sets) (unsafeCoerce setoids))
              (yonedaFunctor (unsafeCoerce sets)) __)) __))
      (unsafeCoerce
        (fobj sets setoids
          (unsafeCoerce
            (fobj (op_Category sets)
              (fun (unsafeCoerce sets) (unsafeCoerce setoids))
              (yonedaFunctor (unsafeCoerce sets)) __)) __))
      (unsafeCoerce
        (function (arr sets __ __)
          (arr setoids
            (fobj sets setoids
              (unsafeCoerce
                (fobj (op_Category sets)
                  (fun (unsafeCoerce sets) (unsafeCoerce setoids))
                  (yonedaFunctor (unsafeCoerce sets)) __)) __)
            (fobj sets setoids
              (unsafeCoerce
                (fobj (op_Category sets)
                  (fun (unsafeCoerce sets) (unsafeCoerce setoids))
                  (yonedaFunctor (unsafeCoerce sets)) __)) __))
          (unsafeCoerce
            (fmap sets setoids
              (unsafeCoerce
                (fobj (op_Category sets)
                  (fun (unsafeCoerce sets) (unsafeCoerce setoids))
                  (yonedaFunctor (unsafeCoerce sets)) __)) __ __))
          (unsafeCoerce g))) (unsafeCoerce f))

