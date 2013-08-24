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

Set Implicit Arguments.
Require Import Setoid Category Functor.


Section ConeDef.
  Context {J C: Category}(D: Functor J C).

  (* 1. D への錐について *)
  Class ConeTo :=
    { apex_to:> C;
      generatrix_to (i: J): apex_to ⟶ (D i);

      generatrix_to_commute:
        forall (i j: J)(alpha: i ⟶ j),
          fmap alpha ◦ generatrix_to i == generatrix_to j }.
  Coercion apex_to: ConeTo >-> obj.

  Class ConeTo_Hom (c d: ConeTo) :=
    { cone_to_hom:> @apex_to c ⟶ @apex_to d;
      
      cone_to_hom_commute:
        forall (i: J),
          generatrix_to i == generatrix_to i ◦ cone_to_hom }.
  Coercion cone_to_hom: ConeTo_Hom >-> carrier.

  Program Instance Compose_ConeTo_Hom 
          {c d e: ConeTo}(f: ConeTo_Hom c d)(g: ConeTo_Hom d e): ConeTo_Hom c e :=
    { cone_to_hom := g ◦ f }.
  Next Obligation.
    apply transitivity with (generatrix_to (ConeTo:=d) i ◦ f);
    [ apply cone_to_hom_commute | ].
    apply transitivity with ((generatrix_to i ◦ g) ◦ f);
      [ apply compose_subst_snd; apply cone_to_hom_commute
      | apply compose_assoc ].
  Qed.

  Program Instance Id_ConeTo_Hom (c: ConeTo): ConeTo_Hom c c :=
    { cone_to_hom := id }.
  Next Obligation.
    equiv_symm; apply id_dom.
  Qed.

  Program Instance ConeTo_Hom_Setoid (c d: ConeTo): Setoid :=
    { carrier := ConeTo_Hom c d ; equal f g := f == g }.
  Next Obligation.
    start.
    - intros x; equiv_refl.
    - intros x y; equiv_symm.
    - intros x y z; equiv_trns.
  Qed.


  (* Category of ConeTo *)
  Program Instance ConeTos: Category :=
    { obj := ConeTo;
      arr X Y := ConeTo_Hom_Setoid X Y;
      compose X Y Z f g := Compose_ConeTo_Hom f g;
      id X := Id_ConeTo_Hom X }.
  Next Obligation.
    apply compose_assoc.
  Qed.
  Next Obligation.
    apply compose_subst; auto.
  Qed.
  Next Obligation.
    apply id_dom.
  Qed.
  Next Obligation.
    apply id_cod.
  Qed.

  (* 函手 D の極限とは D への錐全体の圏の終対象です *)
  Class Limit :=
    { limit :> ConeTo;
      limit_terminal :> Terminal ConeTos limit }.

  (* 2. D からの錐について *)
  Class ConeFrom :=
    { apex_from:> C;
      generatrix_from (i: J): apex_from ⟶ (D i);

      generatrix_from_commute:
        forall (i j: J)(alpha: i ⟶ j),
          fmap alpha ◦ generatrix_from i == generatrix_from j }.
  Coercion apex_from: ConeFrom >-> obj.

  Class ConeFrom_Hom (c d: ConeFrom) :=
    { cone_from_hom:> @apex_from c ⟶ @apex_from d;
      
      cone_from_hom_commute:
        forall (i: J),
          generatrix_from i == generatrix_from i ◦ cone_from_hom }.
  Coercion cone_from_hom: ConeFrom_Hom >-> carrier.

  Program Instance Compose_ConeFrom_Hom 
          {c d e: ConeFrom}(f: ConeFrom_Hom c d)(g: ConeFrom_Hom d e): ConeFrom_Hom c e :=
    { cone_from_hom := g ◦ f }.
  Next Obligation.
    apply transitivity with (generatrix_from (ConeFrom:=d) i ◦ f);
    [ apply cone_from_hom_commute | ].
    apply transitivity with ((generatrix_from i ◦ g) ◦ f);
      [ apply compose_subst_snd; apply cone_from_hom_commute
      | apply compose_assoc ].
  Qed.

  Program Instance Id_ConeFrom_Hom (c: ConeFrom): ConeFrom_Hom c c :=
    { cone_from_hom := id }.
  Next Obligation.
    equiv_symm; apply id_dom.
  Qed.

  Program Instance ConeFrom_Hom_Setoid (c d: ConeFrom): Setoid :=
    { carrier := ConeFrom_Hom c d ; equal f g := f == g }.
  Next Obligation.
    start.
    - intros x; equiv_refl.
    - intros x y; equiv_symm.
    - intros x y z; equiv_trns.
  Qed.


  (* Category of ConeFrom *)
  Program Instance ConeFroms: Category :=
    { obj := ConeFrom;
      arr X Y := ConeFrom_Hom_Setoid X Y;
      compose X Y Z f g := Compose_ConeFrom_Hom f g;
      id X := Id_ConeFrom_Hom X }.
  Next Obligation.
    apply compose_assoc.
  Qed.
  Next Obligation.
    apply compose_subst; auto.
  Qed.
  Next Obligation.
    apply id_dom.
  Qed.
  Next Obligation.
    apply id_cod.
  Qed.

  (* 函手Dの余極限とはDからの錐全体の圏の始対象です *)
  Class CoLimit :=
    { colimit :> ConeFrom;
      colimit_initial :> Initial ConeFroms colimit }.

End ConeDef.