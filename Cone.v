(* Cone:
   
   函手 D:J->C とCの対象 c に対して

   1. Cone to F 
   c から F への錐とは
   射の族 (f__i: c -> D__i),{i∈J} で
   forall i,j ∈ J. alpha: i -> j. D alpha ◦ f__i = f__j を満たすもの

   2. Cone from F
   F から c への錐とは
   射の族 (f__i: D__i -> c),{i∈J} で
   forall i,j ∈ J. alpha: i -> j. f__j ◦ D alpha = f__i を満たすもの

   (J は小さい圏と仮定する．CoqならTypeで問題ないかしら)
 *)


Require Import 
Ssreflect.ssreflect
Ssreflect.eqtype
Ssreflect.ssrbool
Setoid Category Functor.

Set Implicit Arguments.
Unset Strict Implicit.
Section ConeDef.
  Context {J C: Category}(D: Functor J C).

  (* 1. D への錐について *)
  Structure ConeTo :=
    { apex_to:> C;
      generatrix_to (i: J): apex_to --> (D i);

      generatrix_to_commute:
        forall (i j: J)(alpha: i --> j),
          fmap D alpha • generatrix_to i === generatrix_to j }.

  Structure ConeTo_Map (c d: ConeTo) :=
    { cone_to_map:> @apex_to c --> @apex_to d;
      
      cone_to_map_commute:
        forall (i: J),
          generatrix_to c i === generatrix_to d i • cone_to_map }.
 
  Definition eq_ConeTo_Map {c d: ConeTo}(f g: ConeTo_Map c d) :=
    cone_to_map f === cone_to_map g.

  Program Definition ConeTo_Map_Setoid (c d: ConeTo): Setoid :=
    {| equal := @eq_ConeTo_Map c d |}.
  Next Obligation.
    split; rewrite /eq_ConeTo_Map.
    move=> x //=; equiv_refl.
    move=> x y //=; equiv_symm.
    move=> x y z //=; equiv_trns.
  Qed.

  Program Definition compose_ConeTo_Map 
          {c d e: ConeTo}(f: ConeTo_Map_Setoid c d)(g: ConeTo_Map_Setoid d e): ConeTo_Map c e :=
    {| cone_to_map := g • f |}.
  Next Obligation.
    eapply transitivity;
    [ apply cone_to_map_commute |].
    eapply transitivity;
      [| apply compose_assoc ].
    apply compose_subst_snd, cone_to_map_commute.
  Qed.

  Program Definition id_ConeTo_Map (c: ConeTo): ConeTo_Map_Setoid c c :=
    {| cone_to_map := id |}.
  Next Obligation.
    by equiv_symm; apply id_dom.
  Qed.

  (* Category of ConeTo *)
  Program Definition ConeTos: Category :=
    {| compose X Y Z f g :=
         compose_ConeTo_Map f g;
       id X := id_ConeTo_Map X |}.
  Next Obligation.
    by apply compose_assoc.
  Qed.
  Next Obligation.
    by apply compose_subst; auto.
  Qed.
  Next Obligation.
    by apply id_dom.
  Qed.
  Next Obligation.
    by apply id_cod.
  Qed.

  (* 函手 D の極限とは D への錐全体の圏の終対象です *)
  Structure Limit :=
    { limit:> Terminal ConeTos }.

  Structure hasLimit :=
    { limit_obj:> Limit }.

  (* 2. D からの錐について *)
  Structure ConeFrom :=
    { apex_from:> C;
      generatrix_from (i: J): apex_from --> (D i);

      generatrix_from_commute:
        forall (i j: J)(alpha: i --> j),
          fmap D alpha • generatrix_from i === generatrix_from j }.

  Structure ConeFrom_Map (c d: ConeFrom) :=
    { cone_from_map:> @apex_from c --> @apex_from d;
      
      cone_from_map_commute:
        forall (i: J),
          generatrix_from c i === generatrix_from d i • cone_from_map }.

  Definition eq_ConeFrom_Map {c d: ConeFrom}(f g: ConeFrom_Map c d) :=
    cone_from_map f === cone_from_map g.

  Program Definition ConeFrom_Map_Setoid (c d: ConeFrom): Setoid :=
    {| equal := @eq_ConeFrom_Map c d |}.
  Next Obligation.
    split; rewrite /eq_ConeFrom_Map.
    move=> x //=; equiv_refl.
    move=> x y //=; equiv_symm.
    move=> x y z //=; equiv_trns.
  Qed.

  Program Definition compose_ConeFrom_Map 
          {c d e: ConeFrom}(f: ConeFrom_Map_Setoid c d)(g: ConeFrom_Map_Setoid d e): ConeFrom_Map c e :=
    {| cone_from_map := g • f |}.
  Next Obligation.
    eapply transitivity;
    [ eapply transitivity; [apply cone_from_map_commute |] |
      apply compose_assoc ].
    apply compose_subst_snd, cone_from_map_commute.
  Qed.

  Program Definition id_ConeFrom_Map (c: ConeFrom): ConeFrom_Map_Setoid c c :=
    {| cone_from_map := id |}.
  Next Obligation.
    equiv_symm; apply id_dom.
  Qed.

  (* Category of ConeFrom *)
  Program Definition ConeFroms: Category :=
    {| compose X Y Z f g := compose_ConeFrom_Map f g;
       id X := id_ConeFrom_Map X |}.
  Next Obligation.
    by apply compose_assoc.
  Qed.
  Next Obligation.
    by apply compose_subst.
  Qed.
  Next Obligation.
    by apply id_dom.
  Qed.
  Next Obligation.
    by apply id_cod.
  Qed.

  (* 函手Dの余極限とはDからの錐全体の圏の始対象です *)
  Structure CoLimit :=
    { colimit :> Initial ConeFroms }.

  Structure hasCoLimit :=
    { colimit_obj:> CoLimit }.


End ConeDef.