{-# OPTIONS_GHC -cpp -fglasgow-exts #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Cata_foldr where

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

data Unit =
   Tt

data Sum a b =
   Inl a
 | Inr b

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

data Setoid_Spec t =
   Build_Setoid_Spec

type Setoid =
  Setoid_Spec ()
  -- singleton inductive, whose constructor was make_Setoid
  
type Carrier = ()

data Category =
   Make_Category (() -> () -> Setoid) (() -> () -> () -> Carrier -> Carrier
                                      -> Carrier) (() -> Carrier)

type Obj = ()

compose :: Category -> Obj -> Obj -> Obj -> Carrier -> Carrier -> Carrier
compose c =
  case c of {
   Make_Category arr compose0 id0 -> compose0}

id :: Category -> Obj -> Carrier
id c =
  case c of {
   Make_Category arr compose0 id0 -> id0}

id_ :: Category -> Obj -> Carrier
id_ c x =
  id c x

type Initial_Spec =
  Obj -> Carrier
  -- singleton inductive, whose constructor was Build_Initial_Spec
  
initial_arr :: Category -> Obj -> Initial_Spec -> Obj -> Carrier
initial_arr c i initial_Spec =
  initial_Spec

type Terminal_Spec =
  Obj -> Carrier
  -- singleton inductive, whose constructor was Build_Terminal_Spec
  
data Initial =
   Make_Initial Obj Initial_Spec

initial_obj :: Category -> Initial -> Obj
initial_obj c i =
  case i of {
   Make_Initial initial_obj0 initial_spec0 -> initial_obj0}

initial_spec :: Category -> Initial -> Initial_Spec
initial_spec c i =
  case i of {
   Make_Initial initial_obj0 initial_spec0 -> initial_spec0}

data Terminal =
   Make_Terminal Obj Terminal_Spec

terminal_obj :: Category -> Terminal -> Obj
terminal_obj c t =
  case t of {
   Make_Terminal terminal_obj0 terminal_spec -> terminal_obj0}

data Product_Spec =
   Build_Product_Spec Carrier Carrier (Obj -> Carrier -> Carrier -> Carrier)

proj_X :: Category -> Obj -> Obj -> Obj -> Product_Spec -> Carrier
proj_X c x y prod0 product_Spec =
  case product_Spec of {
   Build_Product_Spec proj_X0 proj_Y0 product_arr0 -> proj_X0}

proj_Y :: Category -> Obj -> Obj -> Obj -> Product_Spec -> Carrier
proj_Y c x y prod0 product_Spec =
  case product_Spec of {
   Build_Product_Spec proj_X0 proj_Y0 product_arr0 -> proj_Y0}

product_arr :: Category -> Obj -> Obj -> Obj -> Product_Spec -> Obj ->
               Carrier -> Carrier -> Carrier
product_arr c x y prod0 product_Spec =
  case product_Spec of {
   Build_Product_Spec proj_X0 proj_Y0 product_arr0 -> product_arr0}

data Product =
   Make_Product Obj Product_Spec

product :: Category -> Obj -> Obj -> Product -> Obj
product c x y p =
  case p of {
   Make_Product product0 product_spec0 -> product0}

product_spec :: Category -> Obj -> Obj -> Product -> Product_Spec
product_spec c x y p =
  case p of {
   Make_Product product0 product_spec0 -> product_spec0}

data CoProduct_Spec =
   Build_CoProduct_Spec Carrier Carrier (Obj -> Carrier -> Carrier ->
                                        Carrier)

in_X :: Category -> Obj -> Obj -> Obj -> CoProduct_Spec -> Carrier
in_X c x y coprod0 coProduct_Spec =
  case coProduct_Spec of {
   Build_CoProduct_Spec in_X0 in_Y0 coproduct_arr0 -> in_X0}

in_Y :: Category -> Obj -> Obj -> Obj -> CoProduct_Spec -> Carrier
in_Y c x y coprod0 coProduct_Spec =
  case coProduct_Spec of {
   Build_CoProduct_Spec in_X0 in_Y0 coproduct_arr0 -> in_Y0}

coproduct_arr :: Category -> Obj -> Obj -> Obj -> CoProduct_Spec -> Obj ->
                 Carrier -> Carrier -> Carrier
coproduct_arr c x y coprod0 coProduct_Spec =
  case coProduct_Spec of {
   Build_CoProduct_Spec in_X0 in_Y0 coproduct_arr0 -> coproduct_arr0}

data CoProduct =
   Make_CoProduct Obj CoProduct_Spec

coproduct :: Category -> Obj -> Obj -> CoProduct -> Obj
coproduct c x y c0 =
  case c0 of {
   Make_CoProduct coproduct0 coproduct_spec0 -> coproduct0}

coproduct_spec :: Category -> Obj -> Obj -> CoProduct -> CoProduct_Spec
coproduct_spec c x y c0 =
  case c0 of {
   Make_CoProduct coproduct0 coproduct_spec0 -> coproduct_spec0}

type HasProduct =
  Obj -> Obj -> Product
  -- singleton inductive, whose constructor was Build_hasProduct
  
prod :: Category -> HasProduct -> Obj -> Obj -> Product
prod c hasProduct =
  hasProduct

prod_arr :: Category -> HasProduct -> Obj -> Obj -> Obj -> Obj -> Carrier ->
            Carrier -> Carrier
prod_arr c h x y z w f g =
  product_arr c z w (product c z w (prod c h z w))
    (product_spec c z w (prod c h z w)) (product c x y (prod c h x y))
    (compose c (product c x y (prod c h x y)) x z
      (proj_X c x y (product c x y (prod c h x y))
        (product_spec c x y (prod c h x y))) f)
    (compose c (product c x y (prod c h x y)) y w
      (proj_Y c x y (product c x y (prod c h x y))
        (product_spec c x y (prod c h x y))) g)

type HasCoProduct =
  Obj -> Obj -> CoProduct
  -- singleton inductive, whose constructor was Build_hasCoProduct
  
coprod :: Category -> HasCoProduct -> Obj -> Obj -> CoProduct
coprod c hasCoProduct =
  hasCoProduct

coprod_arr :: Category -> HasCoProduct -> Obj -> Obj -> Obj -> Obj -> Carrier
              -> Carrier -> Carrier
coprod_arr c h x y z w f g =
  coproduct_arr c x y (coproduct c x y (coprod c h x y))
    (coproduct_spec c x y (coprod c h x y))
    (coproduct c z w (coprod c h z w))
    (compose c x z (coproduct c z w (coprod c h z w)) f
      (in_X c z w (coproduct c z w (coprod c h z w))
        (coproduct_spec c z w (coprod c h z w))))
    (compose c y w (coproduct c z w (coprod c h z w)) g
      (in_Y c z w (coproduct c z w (coprod c h z w))
        (coproduct_spec c z w (coprod c h z w))))

data Functor =
   Make_Functor (Obj -> Obj) (Obj -> Obj -> Carrier)

data Algebra =
   Build_Algebra Obj Carrier

alg_obj :: Category -> Functor -> Algebra -> Obj
alg_obj c f a =
  case a of {
   Build_Algebra alg_obj0 alg_arr0 -> alg_obj0}

alg_arr :: Category -> Functor -> Algebra -> Carrier
alg_arr c f a =
  case a of {
   Build_Algebra alg_obj0 alg_arr0 -> alg_arr0}

type Algebra_Map_base =
  Carrier
  -- singleton inductive, whose constructor was make_Algebra_Map_base
  
alg_map :: Category -> Functor -> Algebra -> Algebra -> Algebra_Map_base ->
           Carrier
alg_map c f x y a =
  a

algebra_Map :: Category -> Functor -> Algebra -> Algebra -> Setoid
algebra_Map c f x y =
  Build_Setoid_Spec

compose_Algebra_Map :: Category -> Functor -> Algebra -> Algebra -> Algebra
                       -> Carrier -> Carrier -> Carrier
compose_Algebra_Map c f x y z f0 g =
  unsafeCoerce
    (compose c (alg_obj c f x) (alg_obj c f y) (alg_obj c f z)
      (alg_map c f x y (unsafeCoerce f0)) (alg_map c f y z (unsafeCoerce g)))

id_Algebra_Map :: Category -> Functor -> Algebra -> Carrier
id_Algebra_Map c f x =
  unsafeCoerce (id c (alg_obj c f x))

aLG :: Category -> Functor -> Category
aLG c f =
  Make_Category (unsafeCoerce (algebra_Map c f))
    (unsafeCoerce (compose_Algebra_Map c f))
    (unsafeCoerce (id_Algebra_Map c f))

catamorphism :: Category -> Functor -> Initial -> Algebra -> Carrier
catamorphism c f i x =
  alg_map c f (unsafeCoerce (initial_obj (aLG c f) i)) x
    (unsafeCoerce
      (initial_arr (aLG c f) (initial_obj (aLG c f) i)
        (initial_spec (aLG c f) i) (unsafeCoerce x)))

listF_obj :: Category -> HasProduct -> HasCoProduct -> Terminal -> Obj -> Obj
             -> Obj
listF_obj c hprod hcoprod t a x =
  coproduct c (terminal_obj c t) (product c a x (prod c hprod a x))
    (coprod c hcoprod (terminal_obj c t) (product c a x (prod c hprod a x)))

listF_arr :: Category -> HasProduct -> HasCoProduct -> Terminal -> Obj -> Obj
             -> Obj -> Carrier
listF_arr c hprod hcoprod t a x y =
  unsafeCoerce (\f ->
    coprod_arr c hcoprod (terminal_obj c t)
      (product c a x (prod c hprod a x)) (terminal_obj c t)
      (product c a y (prod c hprod a y)) (id_ c (terminal_obj c t))
      (prod_arr c hprod a x a y (id c a) f))

listF :: Category -> HasProduct -> HasCoProduct -> Terminal -> Obj -> Functor
listF c hprod hcoprod t a =
  Make_Functor (listF_obj c hprod hcoprod t a) (\x y ->
    listF_arr c hprod hcoprod t a x y)

listF_alg_gen :: Category -> HasProduct -> HasCoProduct -> Terminal -> Obj ->
                 Obj -> Carrier -> Carrier -> Algebra
listF_alg_gen c hprod hcoprod t a x fnil fcons =
  Build_Algebra x
    (coproduct_arr c (terminal_obj c t) (product c a x (prod c hprod a x))
      (coproduct c (terminal_obj c t) (product c a x (prod c hprod a x))
        (coprod c hcoprod (terminal_obj c t)
          (product c a x (prod c hprod a x))))
      (coproduct_spec c (terminal_obj c t) (product c a x (prod c hprod a x))
        (coprod c hcoprod (terminal_obj c t)
          (product c a x (prod c hprod a x)))) x fnil fcons)

function :: Setoid
function =
  Build_Setoid_Spec

compose_function :: Carrier -> Carrier -> Carrier
compose_function f g =
  unsafeCoerce (\x -> unsafeCoerce g (unsafeCoerce f x))

id_function :: Carrier
id_function =
  unsafeCoerce (\x -> x)

sets :: Category
sets =
  Make_Category (\_ _ -> function) (\_ _ _ -> compose_function) (\_ ->
    id_function)

sets_Product :: Product
sets_Product =
  Make_Product __ (Build_Product_Spec (unsafeCoerce fst) (unsafeCoerce snd)
    (\_ f g ->
    unsafeCoerce (\x -> Pair (unsafeCoerce f x) (unsafeCoerce g x))))

sets_hasProduct :: HasProduct
sets_hasProduct _ _ =
  sets_Product

sets_CoProduct :: CoProduct
sets_CoProduct =
  Make_CoProduct __ (Build_CoProduct_Spec (unsafeCoerce (\x -> Inl x))
    (unsafeCoerce (\x -> Inr x)) (\_ f g ->
    unsafeCoerce (\x ->
      case x of {
       Inl a -> unsafeCoerce f a;
       Inr b -> unsafeCoerce g b})))

sets_hasCoProduct :: HasCoProduct
sets_hasCoProduct _ _ =
  sets_CoProduct

sets_Terminal :: Terminal
sets_Terminal =
  Make_Terminal __ (\_ -> unsafeCoerce (\x -> Tt))

listF_Sets :: Functor
listF_Sets =
  listF sets sets_hasProduct sets_hasCoProduct sets_Terminal __

list_Algebra :: Algebra
list_Algebra =
  Build_Algebra __
    (unsafeCoerce (\x ->
      case x of {
       Inl wildcard' -> [];
       Inr p ->
        case p of {
         Pair h t -> (:) h t}}))

listF_init_map_function :: Algebra -> (([]) a1) -> ()
listF_init_map_function x l =
  case l of {
   [] -> unsafeCoerce alg_arr sets listF_Sets x (Inl Tt);
   (:) h t ->
    unsafeCoerce alg_arr sets listF_Sets x (Inr (Pair h
      (listF_init_map_function x t)))}

listF_init_map :: Algebra -> Carrier
listF_init_map x =
  unsafeCoerce (unsafeCoerce (listF_init_map_function x))

listF_init :: Initial
listF_init =
  Make_Initial (unsafeCoerce list_Algebra) (\x ->
    listF_init_map (unsafeCoerce x))

cata_foldr :: a2 -> (a1 -> a2 -> a2) -> (([]) a1) -> a2
cata_foldr e f =
  unsafeCoerce
    (catamorphism sets
      (listF sets sets_hasProduct sets_hasCoProduct sets_Terminal __)
      listF_init
      (listF_alg_gen sets sets_hasProduct sets_hasCoProduct sets_Terminal __
        __ (unsafeCoerce (\x -> e)) (unsafeCoerce (\p -> f (fst p) (snd p)))))

