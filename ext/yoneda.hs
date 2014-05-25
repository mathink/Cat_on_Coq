{-# OPTIONS_GHC -cpp -fglasgow-exts #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Yoneda where

import qualified Prelude


unsafeCoerce :: a -> b
#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
import qualified IOExts
unsafeCoerce = IOExts.unsafeCoerce
#endif

__ :: any
__ = Prelude.error "Logical or arity value used"

data Prod a b =
   Pair a b

fst :: (Prod a1 a2) -> a1
fst p =
  case p of {
   Pair x y -> x}

snd :: (Prod a1 a2) -> a2
snd p =
  case p of {
   Pair x y -> y}

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
  
natrans :: Type1 -> Type1 -> Type2 -> Type2 -> Type3 -> Obj -> Carrier
natrans c d f g t =
  t

setoid1 :: Type1 -> Type1 -> Type2 -> Type2 -> Type
setoid1 c d f g =
  Builder

v_compose :: Type1 -> Type1 -> Type2 -> Type2 -> Type2 -> Type3 -> Type3 ->
             Type3
v_compose c d f g h s t x =
  compose0 d (fobj c d f x) (fobj c d g x) (fobj c d h x)
    (natrans c d f g s x) (natrans c d g h t x)

h_compose :: Type1 -> Type1 -> Type1 -> Type2 -> Type2 -> Type2 -> Type2 ->
             Type3 -> Type3 -> Type3
h_compose c d e f g f' g' s t x =
  compose0 e (fobj d e f' (fobj c d f x)) (fobj d e g' (fobj c d f x))
    (fobj d e g' (fobj c d g x)) (natrans d e f' g' t (fobj c d f x))
    (function (arr d (fobj c d f x) (fobj c d g x))
      (arr e (fobj d e g' (fobj c d f x)) (fobj d e g' (fobj c d g x)))
      (unsafeCoerce (fmap d e g' (fobj c d f x) (fobj c d g x)))
      (natrans c d f g s x))

dom_compose :: Type1 -> Type1 -> Type1 -> Type2 -> Type2 -> Type2 -> Type3 ->
               Type3
dom_compose b c d f g e s x =
  natrans c d f g s (fobj b c e x)

cod_compose :: Type1 -> Type1 -> Type1 -> Type2 -> Type2 -> Type3 -> Type2 ->
               Type3
cod_compose c d e f g s h x =
  function (arr d (fobj c d f x) (fobj c d g x))
    (arr e (fobj d e h (fobj c d f x)) (fobj d e h (fobj c d g x)))
    (unsafeCoerce (fmap d e h (fobj c d f x) (fobj c d g x)))
    (natrans c d f g s x)

id2 :: Type1 -> Type1 -> Type2 -> Type3
id2 c d f x =
  id0 d (fobj c d f x)

fun :: Type1 -> Type1 -> Type1
fun c d =
  Builder0 (unsafeCoerce (setoid1 c d)) (unsafeCoerce (v_compose c d))
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

fmap_HomFunctor :: Type1 -> Obj -> Obj -> Obj -> Carrier -> Carrier
fmap_HomFunctor c x y z g =
  unsafeCoerce (\f -> compose0 c x y z f g)

homFunctor :: Type1 -> Obj -> Type2
homFunctor c x =
  Make_Functor (\y -> unsafeCoerce (arr c x y)) (\y z ->
    unsafeCoerce (\g -> fmap_HomFunctor c x y z g))

fmap_CoHomFunctor :: Type1 -> Obj -> Obj -> Obj -> Carrier -> Carrier
fmap_CoHomFunctor c x y z f =
  unsafeCoerce (\g -> compose0 c x y z f g)

coHomFunctor :: Type1 -> Obj -> Type2
coHomFunctor c z =
  Make_Functor (\x -> unsafeCoerce (arr c x z)) (\y x ->
    unsafeCoerce (\f -> fmap_CoHomFunctor c x y z f))

fobj_NF :: Type1 -> Obj -> Obj
fobj_NF c fX =
  unsafeCoerce
    (setoid1 c setoids (homFunctor c (snd (unsafeCoerce fX)))
      (fst (unsafeCoerce fX)))

map_natrans_fmap_NF :: Type1 -> Obj -> Obj -> Carrier -> Carrier -> Obj ->
                       Carrier
map_natrans_fmap_NF c fX gY sf alpha x =
  unsafeCoerce (\g ->
    function
      (unsafeCoerce
        (fobj (op_Category c) setoids (coHomFunctor c x)
          (snd (unsafeCoerce gY))))
      (unsafeCoerce (fobj c setoids (fst (unsafeCoerce gY)) x))
      (unsafeCoerce
        (compose0 setoids
          (fobj (op_Category c) setoids (coHomFunctor c x)
            (snd (unsafeCoerce gY)))
          (fobj c setoids (fst (unsafeCoerce fX)) x)
          (fobj c setoids (fst (unsafeCoerce gY)) x)
          (compose0 setoids
            (fobj (op_Category c) setoids (coHomFunctor c x)
              (snd (unsafeCoerce gY)))
            (fobj (op_Category c) setoids (coHomFunctor c x)
              (snd (unsafeCoerce fX)))
            (fobj c setoids (fst (unsafeCoerce fX)) x)
            (function
              (arr (op_Category c) (snd (unsafeCoerce gY))
                (snd (unsafeCoerce fX)))
              (arr setoids
                (fobj (op_Category c) setoids (coHomFunctor c x)
                  (snd (unsafeCoerce gY)))
                (fobj (op_Category c) setoids (coHomFunctor c x)
                  (snd (unsafeCoerce fX))))
              (unsafeCoerce
                (fmap (op_Category c) setoids (coHomFunctor c x)
                  (snd (unsafeCoerce gY)) (snd (unsafeCoerce fX))))
              (snd (unsafeCoerce sf)))
            (natrans c setoids (homFunctor c (snd (unsafeCoerce fX)))
              (fst (unsafeCoerce fX)) (unsafeCoerce alpha) x))
          (natrans c setoids (fst (unsafeCoerce fX)) (fst (unsafeCoerce gY))
            (fst (unsafeCoerce sf)) x))) g)

natrans_fmap_NF :: Type1 -> Obj -> Obj -> Carrier -> Carrier -> Type3
natrans_fmap_NF c fX gY sf alpha x =
  map_natrans_fmap_NF c fX gY sf alpha x

map_fmap_NF :: Type1 -> Obj -> Obj -> Carrier -> Carrier
map_fmap_NF c fX gY sf =
  unsafeCoerce (\alpha -> unsafeCoerce (natrans_fmap_NF c fX gY sf alpha))

nFunctor :: Type1 -> Type2
nFunctor c =
  Make_Functor (\fX ->
    unsafeCoerce
      (setoid1 c setoids (homFunctor c (snd (unsafeCoerce fX)))
        (fst (unsafeCoerce fX)))) (\fX gY ->
    unsafeCoerce (\sf -> map_fmap_NF c fX gY sf))

yoneda :: Obj -> Obj -> Obj -> Carrier
yoneda c f x =
  unsafeCoerce (\alpha ->
    function
      (unsafeCoerce
        (fobj (unsafeCoerce c) setoids
          (homFunctor (unsafeCoerce c) (snd (Pair f x))) x))
      (unsafeCoerce
        (fobj (unsafeCoerce c) setoids (fst (Pair (unsafeCoerce f) x)) x))
      (unsafeCoerce
        (natrans (unsafeCoerce c) setoids
          (homFunctor (unsafeCoerce c) (snd (Pair f x)))
          (fst (Pair (unsafeCoerce f) x)) (unsafeCoerce alpha) x))
      (id0 (unsafeCoerce c) x))

inv_yoneda :: Obj -> Obj -> Obj -> Carrier
inv_yoneda c f x =
  unsafeCoerce (\x0 ->
    unsafeCoerce (\a ->
      unsafeCoerce (\f0 ->
        function
          (unsafeCoerce
            (fobj (unsafeCoerce c) setoids (unsafeCoerce f) (snd (Pair f x))))
          (unsafeCoerce (fobj (unsafeCoerce c) setoids (unsafeCoerce f) a))
          (unsafeCoerce
            (function (arr (unsafeCoerce c) (snd (Pair f x)) a)
              (arr setoids
                (fobj (unsafeCoerce c) setoids (unsafeCoerce f)
                  (snd (Pair f x)))
                (fobj (unsafeCoerce c) setoids (unsafeCoerce f) a))
              (unsafeCoerce
                (fmap (unsafeCoerce c) setoids (unsafeCoerce f)
                  (snd (Pair f x)) a)) f0)) x0)))

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
  Make_Functor (unsafeCoerce (homFunctor (unsafeCoerce c)))
    (fmap_YonedaFunctor c)

fmap_CoYonedaFunctor :: Obj -> Obj -> Obj -> Carrier -> Type3
fmap_CoYonedaFunctor c x y f z =
  unsafeCoerce (\g -> compose0 (unsafeCoerce c) z x y g f)

coYonedaFunctor :: Obj -> Type2
coYonedaFunctor c =
  Make_Functor (unsafeCoerce (coHomFunctor (unsafeCoerce c))) (\x y ->
    unsafeCoerce (\f -> unsafeCoerce (fmap_CoYonedaFunctor c x y f)))

function_compose :: (a1 -> a2) -> (a2 -> a3) -> Carrier
function_compose f g =
  function
    (unsafeCoerce
      (fobj sets setoids
        (unsafeCoerce
          (fobj (op_Category sets) (fun sets setoids)
            (yonedaFunctor (unsafeCoerce sets)) __)) __))
    (unsafeCoerce
      (fobj sets setoids
        (unsafeCoerce
          (fobj (op_Category sets) (fun sets setoids)
            (yonedaFunctor (unsafeCoerce sets)) __)) __))
    (unsafeCoerce
      (function (arr sets __ __)
        (arr setoids
          (fobj sets setoids
            (unsafeCoerce
              (fobj (op_Category sets) (fun sets setoids)
                (yonedaFunctor (unsafeCoerce sets)) __)) __)
          (fobj sets setoids
            (unsafeCoerce
              (fobj (op_Category sets) (fun sets setoids)
                (yonedaFunctor (unsafeCoerce sets)) __)) __))
        (unsafeCoerce
          (fmap sets setoids
            (unsafeCoerce
              (fobj (op_Category sets) (fun sets setoids)
                (yonedaFunctor (unsafeCoerce sets)) __)) __ __))
        (unsafeCoerce g))) (unsafeCoerce f)

