(* BICO_Formalization.v *)
Require Import Stdlib.Sets.Ensembles.
Require Import Stdlib.Setoids.Setoid.
From Stdlib Require Import Reals.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Init.Logic.
From Stdlib Require Import ssreflect ssrfun ssrbool.
Require Import Stdlib.Logic.Classical_Prop.
From Stdlib Require Import Psatz.

Import Ensembles.

(*===========================================================================*)
(* Section: Setup                                                   *)
(*===========================================================================*)

Module Type SETTING.

  (* --- Outcome Space (X, <=_X) --- *)
  Parameter X : Type.
  Parameter le_X : X -> X -> Prop.
  Axiom le_X_refl : forall x : X, le_X x x.
  Axiom le_X_antisym : forall x y : X, le_X x y -> le_X y x -> x = y.
  Axiom le_X_trans : forall x y z : X, le_X x y -> le_X y z -> le_X x z.
  Notation "x <=_X y" := (le_X x y) (at level 70).
  Notation "x <_X y" := (le_X x y /\ x <> y) (at level 70).

  (* --- Budget Scale (Lambda, <=) --- *)
  Parameter Lambda : Type.
  Parameter le_Lambda : Lambda -> Lambda -> Prop.
  Axiom Lambda_non_empty : inhabited Lambda.
  Axiom le_Lambda_refl : forall l : Lambda, le_Lambda l l.
  Axiom le_Lambda_antisym : forall l1 l2 : Lambda, le_Lambda l1 l2 -> le_Lambda l2 l1 -> l1 = l2.
  Axiom le_Lambda_trans : forall l1 l2 l3 : Lambda, le_Lambda l1 l2 -> le_Lambda l2 l3 -> le_Lambda l1 l3.
  Notation "l1 <= l2" := (le_Lambda l1 l2) (at level 70).

  (* Complete lattice: sup/inf for ALL subsets *)
  Parameter sup : Ensemble Lambda -> Lambda.
  Parameter inf : Ensemble Lambda -> Lambda.
  Axiom sup_is_lub :
    forall (S : Ensemble Lambda),
      (forall l, S l -> l <= sup S) /\
      (forall ub, (forall l, S l -> l <= ub) -> sup S <= ub).
  Axiom inf_is_glb :
    forall (S : Ensemble Lambda),
      (forall l, S l -> inf S <= l) /\
      (forall lb, (forall l, S l -> lb <= l) -> lb <= inf S).

  (* binary join/meet from sup/inf *)
  Definition join (l1 l2 : Lambda) : Lambda := sup (fun l => l = l1 \/ l = l2).
  Definition meet (l1 l2 : Lambda) : Lambda := inf (fun l => l = l1 \/ l = l2).

  (* Global pairwise upper bound (useful convenience) *)
  Lemma Lambda_is_directed : forall l1 l2, exists u, l1 <= u /\ l2 <= u.
  Proof.
    intros l1 l2.
    set (D := fun l => l = l1 \/ l = l2).
    destruct (sup_is_lub D) as [Hub _].
    exists (join l1 l2). split; [apply Hub; now left | apply Hub; now right].
  Qed.

  Definition IsDirected (D : Ensemble Lambda) : Prop :=
    (Inhabited Lambda D) /\
    (forall l1 l2, D l1 -> D l2 -> exists l_ub, D l_ub /\ l1 <= l_ub /\ l2 <= l_ub).

  Lemma supremum_is_least_upper_bound :
    forall (D : Ensemble Lambda), IsDirected D ->
      ((forall l_in_D, D l_in_D -> l_in_D <= sup D) /\
       (forall upper_b, (forall l_in_D, D l_in_D -> l_in_D <= upper_b) -> sup D <= upper_b)).
  Proof.
    intros D _. apply sup_is_lub.
  Qed.

  Definition Powerset (P : Type) : Type := Ensemble P.
End SETTING.

Module LatticeFacts (S : SETTING).
  Import S.

  Definition join (l1 l2 : Lambda) : Lambda :=
    sup (fun l => l = l1 \/ l = l2).

  Lemma join_in_plateau :
    forall l0 la lb, l0 <= la -> l0 <= lb -> l0 <= join la lb.
  Proof.
    intros l0 la lb H0a _.
    destruct (sup_is_lub (fun l => l = la \/ l = lb)) as [Hub _].
    eapply le_Lambda_trans; [exact H0a|].
    apply Hub; now left.
  Qed.

  Lemma plateau_directed : forall l0 : Lambda,
    IsDirected (fun l => l0 <= l).
  Proof.
    intros l0; split.
    - exists l0. apply le_Lambda_refl.
    - intros l1 l2 Hl1 Hl2.
      exists (join l1 l2). split.
      + 
        eapply le_Lambda_trans; [exact Hl1|].
        destruct (sup_is_lub (fun l => l = l1 \/ l = l2)) as [Hub _].
        apply Hub; now left.
      + split.
        * destruct (sup_is_lub (fun l => l = l1 \/ l = l2)) as [Hub _].
          apply Hub; now left.
        * destruct (sup_is_lub (fun l => l = l1 \/ l = l2)) as [Hub _].
          apply Hub; now right.
  Qed.
End LatticeFacts.

(*===========================================================================*)
(* Section: Budget-Indexed Closure Operators                                 *)
(*===========================================================================*)

Module BICO (S : SETTING).

  Import S.

  Parameter K_op : Lambda -> (Powerset X -> Powerset X).
  Notation K_lambda l := (K_op l).

  Definition InformationObject := Powerset X.

  Axiom A1_Extensivity : forall l (A : InformationObject),
    Included X A (K_lambda l A).
  Axiom A2_Idempotence : forall l (A : InformationObject),
    Same_set X (K_lambda l (K_lambda l A)) (K_lambda l A).
  Axiom A3_Monotonicity_in_A : forall l (A B : InformationObject),
    Included X A B -> Included X (K_lambda l A) (K_lambda l B).

  Definition Union_indexed_lambda (D : Ensemble Lambda) (fam : Lambda -> Powerset X) : Powerset X :=
    fun x_val : X => exists l_idx : Lambda, D l_idx /\ (fam l_idx x_val).
    
  Axiom A4_Scott_Continuity_in_lambda :
    forall (A : InformationObject) (D : Ensemble Lambda),
    IsDirected D ->
    Same_set X (K_lambda (sup D) A)
               (Union_indexed_lambda D (fun l' => K_lambda l' A)).

  Definition IsDirectedFamily {I : Type} (le_I : I -> I -> Prop) (fam : I -> Powerset X) : Prop :=
    (forall i j, exists k, le_I i k /\ le_I j k) /\
    (forall i j, le_I i j -> Included X (fam i) (fam j)).
  Definition Union_indexed_family {I : Type} (fam : I -> Powerset X) : Powerset X :=
    fun x => exists i : I, fam i x.
  
  (* Note: In the paper I assume X is finite, which makes Scott-continuity in A
   automatic for monotone maps on P(X). Here I keep A5 as an explicit axiom
   to allow infinite X as well. *)
  Axiom A5_Scott_Continuity_in_A :
     forall l (I : Type) (H_inhabited : inhabited I) (le_I : I -> I -> Prop) (fam : I -> Powerset X),
      IsDirectedFamily le_I fam ->
      Same_set X (K_lambda l (Union_indexed_family fam))
                 (Union_indexed_family (fun i => K_lambda l (fam i))).

  (* Proposition "Monotone improvement" *)
  Theorem Monotone_Improvement :
    forall (A : InformationObject) (l1 l2 : Lambda),
      l1 <= l2 -> Included X (K_lambda l1 A) (K_lambda l2 A).
  Proof.
    intros A l1 l2 Hle x Hx.
    set (D := fun l : Lambda => l = l1 \/ l = l2).
    assert (HD : IsDirected D).
    { split.
      - exists l1. left; reflexivity.
      - intros a b Ha Hb.
        exists l2. split.
        + right; reflexivity.
        + 
          destruct Ha as [Ha|Ha]; destruct Hb as [Hb|Hb]; subst; split;
            try apply le_Lambda_refl; try assumption.
    }
    destruct (supremum_is_least_upper_bound D HD) as [Hub Hleast].
    assert (Hs : sup D = l2).
    { apply le_Lambda_antisym.
      - apply Hleast. intros l Hl. destruct Hl as [Hl|Hl]; subst; [assumption|apply le_Lambda_refl].
      - apply Hub. right; reflexivity.
    }
    destruct (A4_Scott_Continuity_in_lambda A D HD) as [Hsup_to_union Hunion_to_sup].
    rewrite Hs in Hsup_to_union, Hunion_to_sup.
    apply Hunion_to_sup. exists l1. split; [left; reflexivity|assumption].
  Qed.

  Axiom Lambda_is_directed : forall l1 l2, exists u, l1 <= u /\ l2 <= u.

  (* Proposition "General plateau criterion" *)
  Theorem General_Plateau_Criterion
      (A : InformationObject) (lambda0 : Lambda) :
    (forall l : Lambda, lambda0 <= l ->
      Same_set X (K_lambda l A) (K_lambda lambda0 A)) ->
      Same_set X (K_lambda (sup (fun l => lambda0 <= l)) A) (K_lambda lambda0 A).
  Proof.
    intros H_plateau.
    set D := fun l : Lambda => lambda0 <= l.
    have HD : IsDirected D.
    {
      split.
      - exists lambda0; apply le_Lambda_refl.
      - intros l1 l2 Hl1 Hl2.
        destruct (Lambda_is_directed l1 l2) as [u [Hu1 Hu2]].
        exists u; split; [apply le_Lambda_trans with l1; assumption | split; assumption].
    }
    have H_scott := A4_Scott_Continuity_in_lambda A D HD.
    assert (H_union_eq : Same_set X (Union_indexed_lambda D (fun l' => K_lambda l' A)) (K_lambda lambda0 A)).
    {
      split.
      - intros x [l [Hl_in_D Hx_in_KlA]].
        apply (proj1 (H_plateau l Hl_in_D)); assumption.
      - intros x Hx_in_Kl0A.
        exists lambda0; split; [apply le_Lambda_refl | assumption].
    }
    
    unfold Same_set in H_scott, H_union_eq.
    destruct H_scott as [H_sup_incl_union H_union_incl_sup].
    destruct H_union_eq as [H_union_incl_l0 H_l0_incl_union].

    unfold Same_set.
    {
    split.
    - (* Goal 1: K_lambda (supremum D) A subsets K_lambda lambda0 A *)
      intros x Hx.
      apply H_union_incl_l0.
      apply H_sup_incl_union.
      exact Hx.

    - (* Goal 2: K_lambda lambda0 A subsets K_lambda (supremum D) A *)
      intros x Hx.
      apply H_union_incl_sup.
      apply H_l0_incl_union.
      exact Hx.
  }
  Qed.

  (* --- Contexts and Information Objects --- *)
  Definition Contexts (l : Lambda) : Ensemble InformationObject :=
    fun (C : InformationObject) => Same_set X (K_lambda l C) C.


  Theorem contexts_are_a_complete_lattice :
    forall l (Coll_Ctx : Ensemble InformationObject),
      (forall C, Coll_Ctx C -> Contexts l C) ->
      (* Infimum exists *)
      (exists inf, Contexts l inf /\
          (forall C, Coll_Ctx C -> Included X inf C) /\
          (forall T, Contexts l T -> (forall C, Coll_Ctx C -> Included X T C) -> Included X T inf)) /\
      (* Supremum exists *)
      (exists sup, Contexts l sup /\
          (forall C, Coll_Ctx C -> Included X C sup) /\
          (forall T, Contexts l T -> (forall C, Coll_Ctx C -> Included X C T) -> Included X sup T)).
  Proof.
    intros l Coll_Ctx H_Coll_are_contexts.
    split.
    -  set (inf := fun x : X => forall C : InformationObject, Coll_Ctx C -> C x).
      exists inf.
      assert (H_inf_is_context : Contexts l inf).
      {
        unfold Contexts, inf, Same_set. split.
        + (* K(inf) included in inf *)
          intros x Hx_Kinf C H_C_in_coll.
          destruct (H_Coll_are_contexts C H_C_in_coll) as [H_KC_incl_C _].
          apply H_KC_incl_C.
          apply (A3_Monotonicity_in_A l inf C).
          {
            intros y Hy_inf.
            unfold inf in Hy_inf.
            apply Hy_inf; assumption.
          }
          {
            exact Hx_Kinf.
          }
        + (* inf included in K(inf) *)
          apply (A1_Extensivity l inf).
      }
      split; [exact H_inf_is_context|].
      split.
      + (* inf is a lower bound *)
        intros C HC x Hx_inf.
        unfold inf in Hx_inf.
        apply Hx_inf; assumption.
      + (* inf is the greatest lower bound *)
        intros T HT_ctx HT_lb.
        intros x Hx_T C HC.
        apply (HT_lb C HC x Hx_T).
    (* Supremum: K(Union of contexts) *)
    - set (BigUnion := fun x : X => exists C : InformationObject, Coll_Ctx C /\ C x).
      set (sup := K_lambda l BigUnion).
      exists sup.
      assert (H_sup_is_context : Contexts l sup).
      {
        unfold Contexts, sup.
        apply (A2_Idempotence l BigUnion).
      }
      split; [exact H_sup_is_context|].
      split.
      + (* sup is an upper bound *)
        intros C HC x HxC.
        unfold sup.
        apply (A1_Extensivity l BigUnion).
        exists C; split; assumption.
      + (* sup is the least upper bound *)
        intros T HT_ctx HT_ub.
        assert (Incl_BigUnion_T : Included X BigUnion T).
        {
          intros y [C [HC_C Hy_C]].
          apply (HT_ub C HC_C y Hy_C).
        }
        unfold sup.
        assert (H_K_incl : Included X (K_lambda l BigUnion) (K_lambda l T)).
        { apply (A3_Monotonicity_in_A l BigUnion T); assumption. }
        destruct HT_ctx as [H_KT_incl_T _].
        intros x Hx_in_sup.
        apply H_KT_incl_T.
        apply H_K_incl.
        exact Hx_in_sup.
  Qed.
End BICO.

(*===========================================================================*)
(* Section: Canonical Construction                                           *)
(*===========================================================================*)

Module CANONICAL_CONSTRUCTION (S : SETTING).
  Import S.
  Module BICO_Theory := BICO S.
  Import BICO_Theory.
  
  (* --- Probabilistic Raw Achievable Outcomes --- *)
  Parameter Pr : Lambda -> X -> R. 

  (* Axiom S1 (Pointwise Monotonicity in Budget) *)
  Axiom S1_Pointwise_Monotonicity : forall x l1 l2,
    l1 <= l2 -> (Pr l1 x <= Pr l2 x)%R.

  (* Axiom S2 (Pointwise Scott continuity) *)
  Axiom S2_Pointwise_Scott_Continuity : forall x (D : Ensemble Lambda),
    IsDirected D ->
    let sup_val := sup D in
    (forall l, D l -> (Pr l x <= Pr sup_val x)%R) /\
    (forall ub : R, (forall l, D l -> (Pr l x <= ub)%R) -> (Pr sup_val x <= ub)%R).

  (* --- Lower Closures and Guaranteed Regions --- *)

  (* Definition "Lower Closure" *)
  Definition lower_closure (A : Powerset X) : Powerset X :=
    fun p_elem : X => exists a_elem : X, A a_elem /\ p_elem <=_X a_elem.
  Notation "'lc' A" := (lower_closure A) (at level 40).

  (* Lemma "Monotonicity of Lower Closure" *)
  Lemma lc_monotone : forall (A B : Powerset X),
    Included X A B -> Included X (lc A) (lc B).
  Proof.
    intros A B H_incl x [a [Ha Hx_le_a]].
    exists a; split; [apply H_incl; assumption | assumption].
  Qed.

  (* Lemma "Lower Closure Distributes over Unions" *)
  Lemma lc_distributes_over_Union_indexed_lambda :
    forall (D : Ensemble Lambda) (fam : Lambda -> Powerset X),
      Same_set X (lc (Union_indexed_lambda D fam))
                 (Union_indexed_lambda D (fun l => lc (fam l))).
  Proof.
    intros D fam.
    unfold Same_set.
    split.

    - (* lc (Union) subset Union (lc) *)
      intros x Hx.
      unfold lower_closure in Hx.
      destruct Hx as [a [Ha Hxlea]].
      unfold Union_indexed_lambda in Ha.
      destruct Ha as [l [Hld Hfamla]].
      unfold Union_indexed_lambda.
      exists l.
      split; [assumption| ].
      unfold lower_closure.
      exists a.
      split; assumption.

    - (* Union (lc) subset lc (Union) *)
      intros x Hx.
      unfold Union_indexed_lambda in Hx.
      destruct Hx as [l [Hld Hxlc]].
      unfold lower_closure in Hxlc.
      destruct Hxlc as [a [Hfama Hxlea]].
      unfold lower_closure.
      exists a.
      split; [ | assumption].
      unfold Union_indexed_lambda.
      exists l.
      split; assumption.
  Qed.

  (* Definition "p-Guaranteed Region" *)
  Definition GuaranteedRegion (p : R) (l : Lambda) : Powerset X :=
  lc (fun x => (Pr l x > p)%R).

  Lemma Same_set_trans : forall A B C,
    Same_set X A B -> Same_set X B C -> Same_set X A C.
  Proof.
    intros A B C HAB HBC.
    unfold Same_set in *.
    destruct HAB as [HAB_fwd HAB_bwd].
    destruct HBC as [HBC_fwd HBC_bwd].
    split.
    - intros x Hx. apply HBC_fwd. apply HAB_fwd. exact Hx.
    - intros x Hx. apply HAB_bwd. apply HBC_bwd. exact Hx.
  Qed.
  
  Lemma lc_is_congruent_wrt_Same_set : forall A B,
    Same_set X A B -> Same_set X (lc A) (lc B).
  Proof.
    intros A B H_same.
    unfold Same_set in *.
    destruct H_same as [H_A_incl_B H_B_incl_A].
    split; apply lc_monotone; assumption.
  Qed.
  
  Lemma Rgt_sup_gt : forall p (D : Ensemble Lambda) x,
    IsDirected D ->
    (Pr (sup D) x > p)%R ->
    exists l, D l /\ (Pr l x > p)%R.
  Proof.
    intros p D x HD Hsup_gt.
    destruct (classic (exists l : Lambda, D l /\ (Pr l x > p)%R)) as [Hex|Hnex].
    - exact Hex. 
    - assert (Hupper : forall l : Lambda, D l -> (Pr l x <= p)%R).
      { 
        intros l Hl.
        destruct (Rlt_le_dec p (Pr l x)) as [Hgt|Hle].
        - exfalso. apply Hnex. exists l; split; assumption.
        - exact Hle. 
      }
      destruct (S2_Pointwise_Scott_Continuity x D HD) as [_ Hleast].
      specialize (Hleast p Hupper).
      exfalso. eapply Rlt_irrefl.
      eapply Rlt_le_trans; [exact Hsup_gt | exact Hleast].
  Qed.
  
  Lemma GR_is_monotone_and_scott_continuous :
    forall (p : R),
    (forall l1 l2, l1 <= l2 -> Included X (GuaranteedRegion p l1) (GuaranteedRegion p l2)) /\
    (forall (D : Ensemble Lambda), IsDirected D ->
      Same_set X (GuaranteedRegion p (sup D)) (Union_indexed_lambda D (GuaranteedRegion p))).
  Proof.
    intros p.
    split.
    - 
      intros l1 l2 Hle.
      apply lc_monotone.
      intros x Hx_pr_l1.
      apply Rlt_le_trans with (Pr l1 x).
      +
        unfold Rgt in Hx_pr_l1.
        exact Hx_pr_l1.
      + apply (S1_Pointwise_Monotonicity x l1 l2); assumption.
    - 
      intros D HD.
      unfold GuaranteedRegion.
      apply Same_set_trans with (lc (Union_indexed_lambda D (fun l => fun x => (Pr l x > p)%R))).
      +
        apply lc_is_congruent_wrt_Same_set.
        unfold Same_set, Union_indexed_lambda. split; intros x Hx_pr.
        * apply Rgt_sup_gt; [exact HD | exact Hx_pr].
        * 
          destruct Hx_pr as [l [HlD Hpr_l]].
          unfold Rgt in Hpr_l; unfold Rgt.
          apply Rlt_le_trans with (Pr l x); [assumption|].
          apply (proj1 (S2_Pointwise_Scott_Continuity x D HD)); assumption.
      + apply lc_distributes_over_Union_indexed_lambda.
  Qed.

  (* --- The Canonical Operator --- *)

  (* Definition "Canonical Operator" *)
  Definition K_can (p : R) (l : Lambda) (A : Powerset X) : Powerset X :=
    fun x : X => A x \/ (GuaranteedRegion p l x).

  (* Theorem "Canonical Construction Yields Budget-Indexed Closure Operators" *)

  Lemma K_can_extensivity : forall (p : R) (l : Lambda) (A : Powerset X),
    Included X A (K_can p l A).
  Proof.
    intros p l A x HAx.
    unfold K_can.
    left; exact HAx.
  Qed.

  Lemma K_can_idempotence : forall (p : R) (l : Lambda) (A : Powerset X),
    Same_set X (K_can p l (K_can p l A)) (K_can p l A).
  Proof.
    intros p l_lambda A.
    unfold Same_set.
    split.
    - intros x Hx; unfold K_can in Hx; destruct Hx as [Hx_in_KA | HxGR].
      + exact Hx_in_KA.
      + unfold K_can; right; exact HxGR.
    - apply: (K_can_extensivity p l_lambda (K_can p l_lambda A)).
  Qed.

  Lemma K_can_monotonicity_A : forall (p : R) (l : Lambda) (A B : Powerset X),
    Included X A B -> Included X (K_can p l A) (K_can p l B).
  Proof.
    intros p l A B H_incl x Hx.
    unfold K_can in Hx.
    destruct Hx as [HxA | HxGR].
    - unfold K_can.
      left; apply H_incl; exact HxA.
    - unfold K_can.
      right; exact HxGR.
  Qed.

  Lemma K_can_scott_continuity_lambda : forall (p : R) (A : Powerset X) (D : Ensemble Lambda),
    IsDirected D ->
    Same_set X (K_can p (sup D) A)
               (Union_indexed_lambda D (fun l' => K_can p l' A)).
  Proof.
    intros p A D HD.
    unfold Same_set.
    split.
    -
      intros x Hx.
      unfold K_can in Hx.
      destruct Hx as [HxA | HxGRsup].
      + unfold Union_indexed_lambda.
        destruct HD as [[l_ex HlD] _].
        exists l_ex.
        split; [exact HlD | ].
        unfold K_can.
        left; exact HxA.
      +
        destruct (GR_is_monotone_and_scott_continuous p) as [_ H_scott_GR].
        specialize (H_scott_GR D HD).
        unfold Same_set in H_scott_GR.
        destruct H_scott_GR as [H_GRsup_subset_union H_union_subset_GRsup].
        apply H_GRsup_subset_union in HxGRsup.
        destruct HxGRsup as [l [HlD HxGRl]].
        unfold Union_indexed_lambda.
        exists l.
        split; [exact HlD | ].
        unfold K_can.
        right; exact HxGRl.
    -
      intros x Hx.
      unfold Union_indexed_lambda in Hx.
      destruct Hx as [l [HlD Hx_KlA]].
      unfold K_can in Hx_KlA.
      destruct Hx_KlA as [HxA | HxGRl].
      + unfold K_can; left; exact HxA.
      + unfold K_can.
        right.
        destruct (GR_is_monotone_and_scott_continuous p) as [_ H_scott_GR].
        specialize (H_scott_GR D HD).
        unfold Same_set in H_scott_GR.
        destruct H_scott_GR as [H_GRsup_subset_union H_union_subset_GRsup].
        apply H_union_subset_GRsup.
        unfold Union_indexed_lambda.
        exists l.
        split; [exact HlD | exact HxGRl].
  Qed.

  Lemma K_can_scott_continuity_A : forall (p : R) (l : Lambda) (I : Type) (H_inhabited : inhabited I)
         (le_I : I -> I -> Prop) (fam : I -> Powerset X),
        IsDirectedFamily le_I fam ->
        Same_set X (K_can p l (Union_indexed_family fam))
                   (Union_indexed_family (fun i => K_can p l (fam i))).
  Proof.
    intros p l I Hinhab le_I fam _.
    unfold Same_set; split; intros x Hx.
    - unfold K_can in Hx. destruct Hx as [Hunion | HGR].
      + destruct Hunion as [i Hi]. exists i. unfold K_can; left; exact Hi.
      + destruct Hinhab as [i0].  exists i0. unfold K_can; right; exact HGR.
    - destruct Hx as [i HK]. unfold K_can in HK.
      destruct HK as [Hi | HGR]; unfold K_can.
      + left. exists i; exact Hi.
      + right; exact HGR.
  Qed.
  
  Theorem K_can_is_BICO : forall (p : R),
    (forall l A, Included X A (K_can p l A)) /\
    (forall l A, Same_set X (K_can p l (K_can p l A)) (K_can p l A)) /\
    (forall l A B, Included X A B ->
                   Included X (K_can p l A) (K_can p l B)) /\
    (forall A D, IsDirected D ->
                 Same_set X (K_can p (sup D) A)
                            (Union_indexed_lambda D (fun l => K_can p l A))) /\
    (forall l (I : Type) (H_inhabited : inhabited I)
            (le_I : I -> I -> Prop) (fam : I -> Powerset X),
       IsDirectedFamily le_I fam ->
       Same_set X (K_can p l (Union_indexed_family fam))
                  (Union_indexed_family (fun i => K_can p l (fam i)))).
  Proof.
    intros p; split.
    - intros l A; apply K_can_extensivity.
    - split.
      + intros l A; apply K_can_idempotence.
      + split.
        * intros l A B H; apply K_can_monotonicity_A; exact H.
        * split.
          -- intros A D HD; apply K_can_scott_continuity_lambda; exact HD.
          -- intros l I Hinh leI fam Hdir; 
             apply (K_can_scott_continuity_A p l I Hinh leI fam Hdir).
  Qed.

  (* --- Properties of the Canonical Construction --- *)

  (* Lemma "Fixed Point Characterisation for Canonical K" *)
  Lemma Fixed_Point_Characterisation : forall p l C,
    Same_set X (K_can p l C) C <-> Included X (GuaranteedRegion p l) C.
  Proof.
    intros p l C. split.
    - intros Hsame.
      destruct Hsame as [H_KC_subset_C _].
      intros x Hx_GR.
      apply H_KC_subset_C.
      unfold K_can. right; exact Hx_GR.
    - intros H_GR_subset_C.
      split.
      + intros x Hx_KC; unfold K_can in Hx_KC. 
        destruct Hx_KC as [Hx_C | Hx_GR]; [assumption |].
        apply H_GR_subset_C; exact Hx_GR.
      + apply K_can_extensivity.
  Qed.

  (* Definition "Lower Set" *)
  Definition Is_Lower_Set (A : Powerset X) : Prop :=
    forall x y, A y -> x <=_X y -> A x.

  (* Lemma: The lower closure of any set is a lower set. *)
  Lemma lc_is_lower_set : forall S, Is_Lower_Set (lc S).
  Proof.
    intros S x y Hy_lc Hx_le_y.
    destruct Hy_lc as [s [Hs H_y_le_s]].
    exists s; split; [assumption | apply le_X_trans with y; assumption].
  Qed.

  (* Proposition "Canonical Operator Preserves Lower Sets" *)
  Proposition K_can_preserves_lower_sets : forall p l A,
    Is_Lower_Set A -> Is_Lower_Set (K_can p l A).
  Proof.
    intros p l A H_lower_A x y H_Ky H_x_le_y.
    unfold K_can in H_Ky.
    destruct H_Ky as [H_Ay | H_GRy].
    - unfold K_can. left. apply H_lower_A with y; assumption.
    - unfold K_can. right. unfold GuaranteedRegion in H_GRy. unfold lower_closure in H_GRy.
      destruct H_GRy as [a [H_Pra_gt_p H_y_le_a]].
      unfold GuaranteedRegion. unfold lower_closure.
      exists a. split; [assumption | apply le_X_trans with y; assumption].
  Qed.

  (* --- Behaviour at a Minimal Budget --- *)

  Parameter zero : Lambda.
  Axiom zero_minimal : forall l : Lambda, zero <= l.
  Axiom Pr_nonneg : forall l x, (0 <= Pr l x)%R.
  Axiom Pr_le_one : forall l x, (Pr l x <= 1)%R.
  
  Lemma K_identity_at_zero_implies_GR_empty : forall p,
    (0 < p < 1)%R ->
    (forall A : Powerset X, Same_set X (K_can p zero A) A) ->
    Same_set X (GuaranteedRegion p zero) (Empty_set X).
  Proof.
    intros p Hp_range Hidentity.
    pose proof (Hidentity (Empty_set X)) as HId_empty.
    apply (proj1 (Fixed_Point_Characterisation p zero (Empty_set X))) in HId_empty.
    unfold Same_set; split.
    - intros x Hx_GR. exact (HId_empty _ Hx_GR).
    - intros x Hx_empty. inversion Hx_empty.
  Qed.
  
  Lemma le_all_small_pos_implies_le_zero : forall r : R,
    (0 <= r)%R ->
    (forall p, (0 < p < 1)%R -> (r <= p)%R) ->
    (r <= 0)%R.
  Proof.
    intros r Hnonneg Hall.
    apply Rnot_gt_le; intro Hpos.
    destruct (Rle_dec 1 r) as [Hge1 | Hlt1].
    - 
      specialize (Hall (1 / 2)%R).
      assert (Hhalf : (0 < 1 / 2 < 1)%R) by lra.
      specialize (Hall Hhalf).
      lra.
    - 
      assert (Hmid : (0 < r / 2 < 1)%R) by lra.
      specialize (Hall _ Hmid).
      assert (Hr_gt_r2 : (r / 2 < r)%R) by lra.
      lra.
  Qed.
  
  Lemma GR_empty_implies_Pr_le :
    forall p x,
      Same_set X (GuaranteedRegion p zero) (Empty_set X) ->
      (Pr zero x <= p)%R.
  Proof.
    intros p x Hempty.
    destruct Hempty as [HGR_subset_empty _].
    apply Rnot_gt_le; intro Hgt.
    assert (H_in_GR : GuaranteedRegion p zero x).
    { unfold GuaranteedRegion, lower_closure; exists x; split; [exact Hgt | apply le_X_refl].  }
    specialize (HGR_subset_empty _ H_in_GR). inversion HGR_subset_empty.
  Qed.

  (* Proposition "Behaviour at a Minimal Budget" *)
  Proposition zero_budget_canonical :
    ( (forall p : R, (0 < p < 1)%R -> forall A : Powerset X, Same_set X (K_can p zero A) A) <->
      (forall x : X, Pr zero x = 0%R) ).
  Proof.
    split.
    - intros H_identity x.
      assert (H_nonneg : (0 <= Pr zero x)%R) by apply Pr_nonneg.
      assert (H_le_small :
              forall p, (0 < p < 1)%R -> (Pr zero x <= p)%R).
      {
        intros p Hp.
        specialize (H_identity p Hp) as HallA. 
        pose proof (K_identity_at_zero_implies_GR_empty
                      p Hp HallA) as H_GR_empty.
        exact (GR_empty_implies_Pr_le p x H_GR_empty).
      }
      pose proof (le_all_small_pos_implies_le_zero (Pr zero x) H_nonneg H_le_small) as H_le_zero.
      apply Rle_antisym; assumption.
    - intros H_Pr_zero p Hp A.
      unfold Same_set; split.
      + 
        intros x HxK.
        unfold K_can in HxK.
        destruct HxK as [HxA | HxGR]; [assumption|].
        unfold GuaranteedRegion, lower_closure in HxGR.
        destruct HxGR as [a [Hgt Hle]].
        rewrite (H_Pr_zero a) in Hgt; lra. 
      + apply K_can_extensivity.
  Qed.

End CANONICAL_CONSTRUCTION.

(*===========================================================================*)
(* Section: Category Perspective Formalization                               *)
(*===========================================================================*)

Module BICO_Category_Perspective (S : SETTING).
  Import S.
  Module BICO_Theory := BICO S.
  Import BICO_Theory.

  (* --- The Operator Algebra --- *)
  
  Definition Operator := Powerset X -> Powerset X.

  Record CLSCOperator := MkCLSCOperator {
    op :> Operator;
    is_extensive : forall A, Included X A (op A);
    is_idempotent : forall A, Same_set X (op (op A)) (op A);
    is_monotone_A : forall A B, Included X A B -> Included X (op A) (op B);
    is_scott_continuous_A : forall (I : Type) (H_inhabited : inhabited I)
                                 (le_I : I -> I -> Prop) (fam : I -> Powerset X),
                              IsDirectedFamily le_I fam ->
                              Same_set X (op (Union_indexed_family fam))
                                         (Union_indexed_family (fun i => op (fam i)))
  }.

  Definition sqsubseteq (K1 K2 : Operator) : Prop :=
    forall A, Included X (K1 A) (K2 A).
  Definition sup_op_family {D: Type} (fam_op : D -> Operator) (A : Powerset X) : Powerset X :=
    Union_indexed_family (fun i => fam_op i A).

  Section SupOperator.
    Context
      {D            : Type}
      (H_inhabited  : inhabited D)
      (le_D         : D -> D -> Prop)
      (K_fam        : D -> CLSCOperator)
      (H_directed   : forall i j, exists k, le_D i k /\ le_D j k)
      (H_mono_fam   : forall i j, le_D i j -> sqsubseteq (K_fam i) (K_fam j)).

    Definition sup_op (A : Powerset X) : Powerset X :=
      fun x => exists i : D, op (K_fam i) A x.

    Lemma sup_op_extensive :
      forall A, Included X A (sup_op A).
    Proof.
      intros A x HxA. destruct H_inhabited as [i0].
      exists i0. apply (is_extensive (K_fam i0) A x). exact HxA.
    Qed.

    Lemma sup_op_monotone :
      forall A B, Included X A B -> Included X (sup_op A) (sup_op B).
    Proof.
      intros A B HAB x [i Hi]. exists i. apply (is_monotone_A (K_fam i) A B HAB). exact Hi.
    Qed.

    Lemma K_sets_directed (A : Powerset X) :
      IsDirectedFamily le_D (fun i => op (K_fam i) A).
    Proof.
      split.
      - 
        intros i j. destruct (H_directed i j) as [k [Hik Hjk]].
        exists k; split; assumption.
      - 
        intros i j Hij x Hxi.
        specialize (H_mono_fam i j Hij A) as Hinc.
        exact (Hinc _ Hxi).
    Qed.

    Lemma sup_op_idempotent :
      forall A, Same_set X (sup_op (sup_op A)) (sup_op A).
    Proof.
      intros A; split.
      - intros x [i Hxi]. 
        set (F := fun j : D => op (K_fam j) A).
        assert (Hsc :
          Same_set X
            (op (K_fam i) (Union_indexed_family F))
            (Union_indexed_family (fun j => op (K_fam i) (F j))))
          by (apply (is_scott_continuous_A (K_fam i)
                   D H_inhabited le_D F (K_sets_directed A))).
        destruct Hsc as [H_subset _]; specialize (H_subset _ Hxi).
        destruct H_subset as [j Hxij]. 
        destruct (H_directed i j) as [k [Hik Hjk]].
        pose proof (H_mono_fam i k Hik (op (K_fam j) A) _ Hxij) as Hxk1.
        assert (H_arg_incl : Included X (op (K_fam j) A) (op (K_fam k) A))
          by (apply (H_mono_fam j k Hjk A)).
        pose proof (is_monotone_A (K_fam k)
                    (op (K_fam j) A) (op (K_fam k) A) H_arg_incl _ Hxk1)
           as Hxk2.
        destruct (is_idempotent (K_fam k) A) as [Hinc_idem _].
        specialize (Hinc_idem _ Hxk2); exists k; exact Hinc_idem.
      - intros x [i Hxi]; exists i; apply (is_monotone_A (K_fam i) A (sup_op A)).
        + apply sup_op_extensive.
        + exact Hxi.
    Qed.

    Lemma sup_op_scott :
      forall (I : Type) (Hinh  : inhabited I) (le_I : I -> I -> Prop)
             (fam : I -> Powerset X),
        IsDirectedFamily le_I fam ->
        Same_set X (sup_op (Union_indexed_family fam))
                   (Union_indexed_family (fun i => sup_op (fam i))).
    Proof.
      intros I Hinh le_I fam HdirFam; split.
      - 
        intros x [i Hxi]. 
        pose proof (is_scott_continuous_A (K_fam i) I Hinh le_I fam HdirFam) as Hsc.
        destruct Hsc as [Hincl _]. 
        specialize (Hincl _ Hxi).
        destruct Hincl as [j Hxij]. 
        unfold Union_indexed_family; exists j. 
        unfold sup_op. exists i. exact Hxij.
      - intros x [j [i Hxij]]; unfold sup_op; exists i.
        apply (is_monotone_A (K_fam i) (fam j) (Union_indexed_family fam)).
        + intros y Hy; unfold Union_indexed_family; exists j; exact Hy.
        + exact Hxij.
    Qed.

    Definition K_sup : CLSCOperator :=
      MkCLSCOperator
        sup_op
        sup_op_extensive
        sup_op_idempotent
        (fun A B HAB => sup_op_monotone A B HAB)
        (fun I hI leI fam Hdir => sup_op_scott I hI leI fam Hdir).

    Lemma sup_is_upper_bound :
      forall i, sqsubseteq (K_fam i) K_sup.
    Proof.
      intros i A x Hxi. exists i; exact Hxi.
    Qed.

    Lemma sup_is_least_upper_bound :
      forall K_ub : Operator,
        (forall i, sqsubseteq (K_fam i) K_ub) ->
        sqsubseteq K_sup K_ub.
    Proof.
      intros K_ub Hub A x [i Hxi]. now apply (Hub i A x).
    Qed.

  End SupOperator.

  (* Proposition `clsc_is_dcpo`: The space of operators is a dcpo *)
  Theorem clsc_is_dcpo :
    forall (D : Type) (H_inhabited: inhabited D) (le_D: D -> D -> Prop) (K_fam : D -> CLSCOperator),
      (forall i j, exists k, le_D i k /\ le_D j k) -> (* D is directed *)
      (forall i j, le_D i j -> sqsubseteq (K_fam i) (K_fam j)) -> (* family is monotone *)
      exists (K_sup : CLSCOperator),
        (forall i, sqsubseteq (K_fam i) K_sup) /\
        (forall K_ub : Operator, (forall i, sqsubseteq (K_fam i) K_ub) -> sqsubseteq K_sup K_ub).
  Proof.
    intros D Hinh le_D K_fam Hdir Hmono.
    pose (K_sup := K_sup Hinh le_D K_fam Hdir Hmono).
    exists K_sup. split.
    - apply sup_is_upper_bound.
    - apply sup_is_least_upper_bound.
  Qed.

  (* --- Composition of Budgeted Systems --- *)
  Module OperatorComposition.
    Section Composition.
      Context {K1 K2 : Operator}.
      Context (H1_ext : forall A, Included X A (K1 A))
              (H1_mono : forall A B, Included X A B -> Included X (K1 A) (K1 B))
              (H2_ext : forall A, Included X A (K2 A))
              (H2_mono : forall A B, Included X A B -> Included X (K2 A) (K2 B)).

      Definition F (A : Powerset X) : Powerset X := K2 (K1 A).

      Lemma F_is_extensive : forall A, Included X A (F A).
      Proof. intros A x HxA; apply (H2_ext (K1 A) x); apply (H1_ext A x); exact HxA. Qed.

      Lemma F_is_monotone : forall A B, Included X A B -> Included X (F A) (F B).
      Proof. 
        intros A B HAB x Hx. 
        apply (H2_mono (K1 A) (K1 B)).
        - apply (H1_mono A B); exact HAB.
        - exact Hx.
      Qed.

      Definition Is_F_closed (C : Powerset X) : Prop := Included X (F C) C.
      Definition K_comp (A : Powerset X) : Powerset X :=
        fun x => forall C, Included X A C -> Is_F_closed C -> C x.
      
      Lemma Is_F_closed_Kcomp :
        forall A, Is_F_closed (K_comp A).
      Proof.
        intros A x HxF; unfold K_comp; intros C HA_C HC_closed.
        assert (Hincl : Included X (K_comp A) C).
        { intros y Hy; apply (Hy C); [assumption|exact HC_closed]. }
        assert (HF_incl : In X (F C) x).
        { apply (F_is_monotone _ _ Hincl); exact HxF. }
        apply HC_closed in HF_incl; exact HF_incl.
      Qed.
    
    Lemma Kcomp_idempotent :
      forall A, Same_set X (K_comp (K_comp A)) (K_comp A).
    Proof.
      intros A; unfold Same_set, Included; split.
      - intros x Hx.
        unfold K_comp in *.
        specialize (Hx (K_comp A)).
        apply Hx.
        + intros y Hy; exact Hy. 
        + apply Is_F_closed_Kcomp. 
      - intros x Hx.
        unfold K_comp in *.
        intros C HKcompA_C HC_closed.
        assert (HA_C : Included X A C).
        { intros y HyA. 
          apply HKcompA_C.
          unfold K_comp.
          intros D HA_D HD_closed.
          apply HA_D; exact HyA.
        }
        apply Hx; [exact HA_C | exact HC_closed].
    Qed.

      (* Theorem `Kcomp_is_closure` *)
      Theorem Kcomp_is_closure_operator :
        (forall A, Included X A (K_comp A)) /\
        (forall A B, Included X A B -> Included X (K_comp A) (K_comp B)) /\
        (forall A, Same_set X (K_comp (K_comp A)) (K_comp A)).
      Proof.
        split.
        - intros A x HA. unfold K_comp. firstorder.
        - split.
          + intros A B HAB x Hx. unfold K_comp in *. firstorder.
          + apply Kcomp_idempotent.
      Qed.

    End Composition.
  End OperatorComposition.

  (* --- Canonical Case --- *)
  Module CC := CANONICAL_CONSTRUCTION S. 
  Module CanonicalPerspective.
    Import CC BICO_Theory.
    Section Canonical.
      Context {p : R} (Hp_range: (0 < p < 1)%R).
      Let K l := K_can p l.

      Definition Contexts_can (l : Lambda) : Ensemble (Powerset X) := Contexts l.
      
      Variable D : Ensemble Lambda.
      Hypothesis HD : IsDirected D.
    
      Proposition contexts_form_a_presheaf :
        forall l1 l2, l1 <= l2 ->
          Included (Powerset X) (Contexts_can l2) (Contexts_can l1).
      Proof.
        intros l1 l2 Hle C HC.
        unfold Contexts_can, Contexts in *.
        destruct HC as [HKl2C_subset_C HC_subset_Kl2C].
        split.
        - intros x Hx; have Hmon := Monotone_Improvement C l1 l2 Hle.
          apply HKl2C_subset_C; apply Hmon; exact Hx.
        - intros x Hx; apply A1_Extensivity; exact Hx.
      Qed.
      
      Lemma contexts_sup_implies_each :
        forall C,
          Contexts_can (sup D) C ->
          (forall l, D l -> Contexts_can l C).
      Proof.
        intros C Hsup_ctx l HlD.
        unfold Contexts_can, Contexts in *.
        destruct Hsup_ctx as [Hsup_sub_C H_C_sub_sup].
        split.
        - intros x Hx_KlC.
          destruct (supremum_is_least_upper_bound D HD) as [Hub _].
          specialize (Hub l HlD) as Hle. 
          pose proof (Monotone_Improvement C l (sup D) Hle) as HKl_sub_Ksup.
          apply Hsup_sub_C; apply HKl_sub_Ksup; exact Hx_KlC.
        - intros x HxC; apply A1_Extensivity; exact HxC.
      Qed.
      
      Lemma contexts_each_implies_sup :
        forall C,
          (forall l, D l -> Contexts_can l C) ->
          Contexts_can (sup D) C.
      Proof.
        intros C Hctx_each; unfold Contexts_can, Contexts in *.
        destruct (A4_Scott_Continuity_in_lambda C D HD) as [Hsup_subset_union Hunion_subset_sup].
        destruct HD as [[l0 Hl0D] Hdir].
        assert (Hunion_subset_C : Included X (Union_indexed_lambda D (fun l => K_lambda l C)) C).
        { intros x [l [HlD HxKlC]]; destruct (Hctx_each l HlD) as [HKlC_subset_C _]; apply (HKlC_subset_C _ HxKlC). }
        assert (HC_subset_union : Included X C (Union_indexed_lambda D (fun l => K_lambda l C))).
        { intros x HxC; exists l0; split; [exact Hl0D|]; destruct (Hctx_each l0 Hl0D) as [_ HC_subset_Kl0C]; apply (HC_subset_Kl0C _ HxC). }
        split.
          - intros x Hx_sup; apply Hunion_subset_C; apply Hsup_subset_union; exact Hx_sup.
          - intros x HxC; apply Hunion_subset_sup; apply HC_subset_union; exact HxC.
      Qed.
      
      (* Proposition `continuity_of_context_presheaf` *)
      Proposition continuity_of_context_presheaf :
        forall (D : Ensemble Lambda), IsDirected D ->
          Same_set (Powerset X)
                   (Contexts_can (sup D))
                   (fun C => forall l, D l -> Contexts_can l C).
      Proof.
        intros D0 HD0.
        unfold Same_set; split.
        -
          intros C Hsup_ctx l HlD0.
          unfold Contexts_can, Contexts in *.
          destruct Hsup_ctx as [Hsup_sub_C HC_sub_sup]. 
          destruct (supremum_is_least_upper_bound D0 HD0) as [Hub _].
          pose proof (Hub l HlD0) as Hle.
          pose proof (Monotone_Improvement C l (sup D0) Hle) as Hmono.
          split.
          + intros x HxKlC; apply Hsup_sub_C; apply Hmono; exact HxKlC.
          + intros x HxC; apply A1_Extensivity; exact HxC.
        -
          intros C Hctx_each.
          unfold Contexts_can, Contexts in *.
          destruct (A4_Scott_Continuity_in_lambda C D0 HD0) as [Hsup_subset_union Hunion_subset_sup].
          assert (Hunion_sub_C : Included X (Union_indexed_lambda D0 (fun l => K_lambda l C)) C).
          { intros x [l [HlD0 HxKlC]]; destruct (Hctx_each l HlD0) as [HKlC_sub_C _]; apply HKlC_sub_C; exact HxKlC. }
          destruct HD0 as [[l0 Hl0D0] Hdir].
          assert (HC_sub_union : Included X C (Union_indexed_lambda D0 (fun l => K_lambda l C))).
          { 
            intros x HxC; destruct (Hctx_each l0 Hl0D0) as [_ HC_sub_Kl0C].
            specialize (HC_sub_Kl0C _ HxC); exists l0; split; [exact Hl0D0 | exact HC_sub_Kl0C]. 
          }
          split.
          + intros x Hx_sup; apply Hunion_sub_C; apply Hsup_subset_union; exact Hx_sup.
          + intros x HxC; apply Hunion_subset_sup; apply HC_sub_union; exact HxC.
      Qed.
    End Canonical.

    (* --- Composition of Canonical Operators --- *)
    Section CanonicalComposition.
      Context {p1 p2 : R}.
      Let K1 l := K_can p1 l.
      Let K2 l := K_can p2 l.
      Let GR1 l := GuaranteedRegion p1 l.
      Let GR2 l := GuaranteedRegion p2 l.

      Let F l1 l2 A := K2 l2 (K1 l1 A).

      Proposition composition_of_canonical_operators_is_simple_alt :
        forall l1 l2 (A : Powerset X),
          Same_set X (F l1 l2 A)
                    (fun x => A x \/ GR1 l1 x \/ GR2 l2 x).
      Proof.
        intros l1 l2 A.
        unfold F, K1, K2, K_can.
        unfold Same_set; split; intros x H; firstorder.
      Qed.
      
      Corollary composition_of_canonical_is_idempotent :
        forall l1 l2 A, Same_set X (F l1 l2 (F l1 l2 A)) (F l1 l2 A).
      Proof.
        intros l1 l2 A.
        pose proof (composition_of_canonical_operators_is_simple_alt l1 l2 A) as [FA_to_S  S_to_FA].
        pose proof (composition_of_canonical_operators_is_simple_alt l1 l2 (F l1 l2 A)) as [FFA_to_B B_to_FFA].
        unfold Same_set; split; intros x Hx.
        -
          apply FFA_to_B in Hx. 
          destruct Hx as [HFax | [HGR1x | HGR2x]].
          + exact HFax. 
          + apply S_to_FA. right;  left.  exact HGR1x.
          + apply S_to_FA. right;  right. exact HGR2x.
        - apply B_to_FFA. left. exact Hx. 
      Qed.
    End CanonicalComposition.
  End CanonicalPerspective.
End BICO_Category_Perspective.

Module Type DECOMPOSITION_SETTING.
  Parameter X : Type.
  Parameter le_X : X -> X -> Prop.
  Axiom le_X_refl : forall x : X, le_X x x.
  Axiom le_X_antisym : forall x y : X, le_X x y -> le_X y x -> x = y.
  Axiom le_X_trans : forall x y z : X, le_X x y -> le_X y z -> le_X x z.
  Notation "x <=_X y" := (le_X x y) (at level 70).
  Definition Powerset (P : Type) : Type := Ensemble P.
  
  Definition Union_indexed_family {P I : Type} (fam : I -> Powerset P) : Powerset P :=
    fun (x : P) => exists (i : I), fam i x.
  Arguments Union_indexed_family {P I} fam.

  Definition IsDirectedFamily {P I : Type} (le_I : I -> I -> Prop) (fam : I -> Powerset P) : Prop :=
    (forall i j, exists k, le_I i k /\ le_I j k) /\
    (forall i j, le_I i j -> Included P (fam i) (fam j)).
  Arguments IsDirectedFamily {P I} le_I fam.
  
  
  Parameter Z : Type.
  Parameter le_Z : Z -> Z -> Prop.
  Axiom le_Z_refl : forall z : Z, le_Z z z.
  Axiom le_Z_antisym : forall z1 z2 : Z, le_Z z1 z2 -> le_Z z2 z1 -> z1 = z2.
  Axiom le_Z_trans : forall z1 z2 z3 : Z, le_Z z1 z2 -> le_Z z2 z3 -> le_Z z1 z3.
  Notation "z1 <=_Z z2" := (le_Z z1 z2) (at level 70).

  Parameter Lambda_s : Type.
  Axiom Lambda_s_non_empty : inhabited Lambda_s.
  Parameter le_s : Lambda_s -> Lambda_s -> Prop.
  Axiom le_s_refl : forall b : Lambda_s, le_s b b.
  Axiom le_s_antisym : forall b1 b2, le_s b1 b2 -> le_s b2 b1 -> b1 = b2.
  Axiom le_s_trans : forall b1 b2 b3, le_s b1 b2 -> le_s b2 b3 -> le_s b1 b3.
  Definition IsDirected_s (D : Ensemble Lambda_s) : Prop :=
    (Inhabited Lambda_s D) /\
    (forall l1 l2, D l1 -> D l2 -> exists l_ub, D l_ub /\ le_s l1 l_ub /\ le_s l2 l_ub).
  Parameter supremum_s : Ensemble Lambda_s -> Lambda_s.
  Axiom supremum_s_is_lub :
    forall (D : Ensemble Lambda_s), IsDirected_s D ->
      ((forall l, D l -> le_s l (supremum_s D)) /\
       (forall ub, (forall l, D l -> le_s l ub) -> le_s (supremum_s D) ub)).
       
  Parameter Lambda_r : Type.
  Axiom Lambda_r_non_empty : inhabited Lambda_r.
  Parameter le_r : Lambda_r -> Lambda_r -> Prop.
  Axiom le_r_refl : forall g : Lambda_r, le_r g g.
  Axiom le_r_antisym : forall g1 g2, le_r g1 g2 -> le_r g2 g1 -> g1 = g2.
  Axiom le_r_trans : forall g1 g2 g3, le_r g1 g2 -> le_r g2 g3 -> le_r g1 g3.
  Definition IsDirected_r (D : Ensemble Lambda_r) : Prop :=
    (Inhabited Lambda_r D) /\
    (forall l1 l2, D l1 -> D l2 -> exists l_ub, D l_ub /\ le_r l1 l_ub /\ le_r l2 l_ub).
  Parameter supremum_r : Ensemble Lambda_r -> Lambda_r.
  Axiom supremum_r_is_lub :
    forall (D : Ensemble Lambda_r), IsDirected_r D ->
      ((forall l, D l -> le_r l (supremum_r D)) /\
       (forall ub, (forall l, D l -> le_r l ub) -> le_r (supremum_r D) ub)).
End DECOMPOSITION_SETTING.

Module DECOMPOSITION_OF_LOSS (DS : DECOMPOSITION_SETTING).
  Import DS.
  
  Definition Budget : Type := (Lambda_s * Lambda_r)%type.
  Definition le_B (b1 b2 : Budget) : Prop :=
    le_s (fst b1) (fst b2) /\ le_r (snd b1) (snd b2).
  Notation "b1 <=B b2" := (le_B b1 b2) (at level 70).
  
  Lemma le_B_refl  : forall b, b <=B b.
  Proof. intros [beta gamma]; split; [apply le_s_refl | apply le_r_refl]. Qed.
  
  Lemma le_B_trans : forall b1 b2 b3,
    b1 <=B b2 -> b2 <=B b3 -> b1 <=B b3.
  Proof.
    intros [beta1 gamma1] [beta2 gamma2] [beta3 gamma3] [H12s H12r] [H23s H23r]; split.
    - eapply le_s_trans; eauto.
    - eapply le_r_trans; eauto.
  Qed.

  Lemma le_B_antisym : forall b1 b2,
    b1 <=B b2 -> b2 <=B b1 -> b1 = b2.
  Proof.
    intros [beta1 gamma1] [beta2 gamma2] [H12s H12r] [H21s H21r].
    f_equal; [apply le_s_antisym | apply le_r_antisym]; auto.
  Qed.
  
  Definition IsDirected_B (D : Ensemble Budget) : Prop :=
    (Inhabited Budget D) /\
    (forall b1 b2, D b1 -> D b2 -> exists b_ub, D b_ub /\ b1 <=B b_ub /\ b2 <=B b_ub).
    
  Definition supremum_B (D : Ensemble Budget) : Budget :=
    (supremum_s (fun bs => exists br, D (bs, br)),
     supremum_r (fun br => exists bs, D (bs, br))).
  Axiom supremum_B_is_lub :
    forall (D : Ensemble Budget), IsDirected_B D ->
      ((forall b, D b -> b <=B (supremum_B D)) /\
       (forall ub, (forall b, D b -> b <=B ub) -> (supremum_B D) <=B ub)).
       
  Parameter C_op : Lambda_s -> (Powerset X -> Powerset Z).
  Notation C_beta beta := (C_op beta).
  Parameter R_op : Lambda_r -> (Powerset Z -> Powerset X).
  Notation R_gamma gamma := (R_op gamma).
  
  Axiom C_monotone_A : forall beta A B,
    Included X A B -> Included Z (C_beta beta A) (C_beta beta B).
  Axiom C_scott_A : forall beta (I:Type) (hI:inhabited I) (leI:I->I->Prop) (fam:I->Powerset X),
    IsDirectedFamily leI fam ->
    Same_set Z (C_beta beta (Union_indexed_family fam))
               (Union_indexed_family (fun i => C_beta beta (fam i))).
  Axiom R_monotone_A : forall gamma S T,
    Included Z S T -> Included X (R_gamma gamma S) (R_gamma gamma T).
  Axiom R_scott_A : forall gamma (I:Type) (hI:inhabited I) (leI:I->I->Prop) (fam:I->Powerset Z),
    IsDirectedFamily leI fam ->
    Same_set X (R_gamma gamma (Union_indexed_family fam))
               (Union_indexed_family (fun i => R_gamma gamma (fam i))).

  Definition Union_indexed_lambda_s (D : Ensemble Lambda_s) (fam : Lambda_s -> Powerset Z) : Powerset Z :=
    fun z_val => exists b_idx, D b_idx /\ (fam b_idx z_val).
  Definition Union_indexed_lambda_r (D : Ensemble Lambda_r) (fam : Lambda_r -> Powerset X) : Powerset X :=
    fun x_val => exists g_idx, D g_idx /\ (fam g_idx x_val).

  Axiom C_scott_beta : forall A (D_s : Ensemble Lambda_s),
    IsDirected_s D_s ->
    Same_set Z (C_beta (supremum_s D_s) A)
               (Union_indexed_lambda_s D_s (fun beta => C_beta beta A)).
  Axiom R_scott_gamma : forall S (D_r : Ensemble Lambda_r),
    IsDirected_r D_r ->
    Same_set X (R_gamma (supremum_r D_r) S)
               (Union_indexed_lambda_r D_r (fun gamma => R_gamma gamma S)).

  Lemma C_monotone_beta : forall A b1 b2,
    le_s b1 b2 -> Included Z (C_beta b1 A) (C_beta b2 A).
  Proof.
    intros A b1 b2 Hle.
    set (D := fun b : Lambda_s => b = b1 \/ b = b2).
    assert (HD : IsDirected_s D).
    { split.
      - exists b1; left; reflexivity.
      - 
        intros l1 l2 Hl1 Hl2; exists b2; split.
        + right; reflexivity.
        + split.
          * case: Hl1 => [-> | ->]; [ exact Hle | apply le_s_refl ].
          * case: Hl2 => [-> | ->]; [ exact Hle | apply le_s_refl ].
    }
    assert (Hsup_eq : supremum_s D = b2).
    { apply le_s_antisym.
      - 
        destruct (supremum_s_is_lub D HD) as [_ Hleast].
        apply Hleast; intros l Hl.
        destruct Hl as [<- | <-]; [ exact Hle | apply le_s_refl ].
      - destruct (supremum_s_is_lub D HD) as [Hub _]; apply Hub. right; reflexivity.
    }

    destruct (C_scott_beta A D HD) as [_ Hunion_sub_sup].
    rewrite Hsup_eq in Hunion_sub_sup.
    intros z Hz; apply Hunion_sub_sup; exists b1; split.
    - left. reflexivity.
    - exact Hz.
  Qed.
  
  Lemma R_monotone_gamma : forall S g1 g2,
    le_r g1 g2 -> Included X (R_gamma g1 S) (R_gamma g2 S).
  Proof.
    intros S g1 g2 Hle x Hx. 
    set (D := fun g : Lambda_r => g = g1 \/ g = g2).
    assert (HD : IsDirected_r D).
    { split.
      - exists g1; left; reflexivity.
      - 
        intros h1 h2 Hh1 Hh2; exists g2; split.
        + right; reflexivity.
        + split.
          * destruct Hh1 as [H|H]; subst; [ exact Hle | apply le_r_refl ].
          * destruct Hh2 as [H|H]; subst; [ exact Hle | apply le_r_refl ]. 
    }
    assert (Hsup : supremum_r D = g2).
    { apply le_r_antisym.
      - destruct (supremum_r_is_lub D HD) as [_ Hleast]; apply Hleast; intros g Hg.
        destruct Hg as [<- | <-]; [ exact Hle | apply le_r_refl ].
      - destruct (supremum_r_is_lub D HD) as [Hub _]; apply Hub; right; reflexivity. 
    }
    destruct (R_scott_gamma S D HD) as [Hsup_subset_union Hunion_subset_sup].
    rewrite Hsup in Hunion_subset_sup; apply Hunion_subset_sup.
    exists g1; split.
    - left; reflexivity. 
    - exact Hx.
  Qed.
  
  Definition K_raw (b : Budget) (A : Powerset X) : Powerset X :=
    R_gamma (snd b) (C_beta (fst b) A).
  Definition Is_K_raw_closed (b: Budget) (C : Powerset X) : Prop :=
    Included X (K_raw b C) C.
  Definition K_bar (b : Budget) (A : Powerset X) : Powerset X :=
    fun x => forall C, Included X A C -> Is_K_raw_closed b C -> C x.
  
  Lemma K_raw_monotone_A (b : Budget) : forall A B,
    Included X A B -> Included X (K_raw b A) (K_raw b B).
  Proof.
    intros A B H_incl.
    unfold K_raw.
    apply R_monotone_A.
    apply C_monotone_A; assumption.
  Qed.
  
  Lemma K_raw_monotone_b A b1 b2 : b1 <=B b2 -> Included X (K_raw b1 A) (K_raw b2 A).
  Proof.
    intros Hle x Hx. 
    destruct b1 as [beta1 gamma1].
    destruct b2 as [beta2 gamma2].
    simpl in *. 
    destruct Hle as [Hbeta Hgamma].
    assert (HC_incl :Included Z (C_beta beta1 A) (C_beta beta2 A))
      by (apply C_monotone_beta; exact Hbeta).
    assert (Hx1 :In X (R_gamma gamma1 (C_beta beta2 A)) x)
      by (apply (R_monotone_A gamma1 (C_beta beta1 A) (C_beta beta2 A)
                             HC_incl); exact Hx).
    apply (R_monotone_gamma (C_beta beta2 A) gamma1 gamma2  Hgamma); exact Hx1.
  Qed.
  
  Proposition K_raw_scott_A (b : Budget) (I:Type) (hI:inhabited I) (leI:I->I->Prop) (fam:I->Powerset X) :
    IsDirectedFamily leI fam ->
    Same_set X (K_raw b (Union_indexed_family fam)) (Union_indexed_family (fun i => K_raw b (fam i))).
  Proof.
    intros Hdir.
    destruct b as [beta gamma].
    assert (HC :
              Same_set Z
                       (C_beta beta (Union_indexed_family fam))
                       (Union_indexed_family
                          (fun i : I => C_beta beta (fam i))))
      by (apply (C_scott_A beta I hI leI fam Hdir)).
    set (S := fun i : I => C_beta beta (fam i)).
    assert (HdirS : IsDirectedFamily leI S).
    { destruct Hdir as [Hup Hincl]; split.
      - exact Hup.
      - intros i j Hij; apply C_monotone_A; apply Hincl; exact Hij. 
    }
    assert (HR :
              Same_set X
                       (R_gamma gamma (Union_indexed_family S))
                       (Union_indexed_family
                          (fun i : I => R_gamma gamma (S i))))
      by (apply (R_scott_A gamma I hI leI S HdirS)).

    destruct HC as [HC1 HC2]. 
    assert (H_R_same :
              Same_set X
                       (R_gamma gamma
                                 (C_beta beta (Union_indexed_family fam)))
                       (R_gamma gamma (Union_indexed_family S))).
    { split.
      - intros x Hx.
        apply (R_monotone_A gamma
                             (C_beta beta (Union_indexed_family fam))
                             (Union_indexed_family S)
                             HC1); exact Hx.
      - intros x Hx.
        apply (R_monotone_A gamma
                             (Union_indexed_family S)
                             (C_beta beta (Union_indexed_family fam))
                             HC2); exact Hx. 
    }
    unfold K_raw, Same_set in *; split.
    - intros x Hx; apply HR; apply H_R_same; exact Hx.
    - intros x Hx; apply H_R_same; apply HR; exact Hx.
  Qed.
  
  Section RawScottBudget.
    Variable A : Powerset X.
    Variable D : Ensemble Budget.
    Hypothesis HD : IsDirected_B D.

    Definition D_s (b : Lambda_s) : Prop := exists g, D (b, g).
    Definition D_r (g : Lambda_r) : Prop := exists b, D (b, g).

    Lemma D_s_directed : IsDirected_s D_s.
    Proof.
      destruct HD as [[b0 Hb0] Hdir].
      destruct b0 as [beta0 gamma0].
      split.
      - exists beta0. exists gamma0. exact Hb0.
      - intros beta1 beta2 Hbeta1 Hbeta2.
        destruct Hbeta1 as [gamma1 Hb1].
        destruct Hbeta2 as [gamma2 Hb2].
        destruct (Hdir _ _ Hb1 Hb2)
            as [[beta3 gamma3] [Hb3 [H13 H23]]].
        destruct H13 as [Hbeta13 _].
        destruct H23 as [Hbeta23 _].
        exists beta3.
        split.
        + exists gamma3. exact Hb3.
        + split; assumption.
    Qed.

    Lemma D_r_directed : IsDirected_r D_r.
    Proof.
      destruct HD as [[b0 Hb0] Hdir].
      destruct b0 as [beta0 gamma0].
      split.
      - exists gamma0. exists beta0. exact Hb0.
      - intros gamma1 gamma2 Hgamma1 Hgamma2.
        destruct Hgamma1 as [beta1 Hb1].
        destruct Hgamma2 as [beta2 Hb2].
        destruct (Hdir _ _ Hb1 Hb2)
            as [[beta3 gamma3] [Hb3 [H13 H23]]].
        destruct H13 as [_ Hgamma13].
        destruct H23 as [_ Hgamma23].
        exists gamma3.
        split.
        + exists beta3. exact Hb3.
        + split; assumption.
    Qed.

    Lemma upper_bound_in_D :
      forall beta gamma,
        D_s beta -> D_r gamma ->
        exists b,
          D b /\
          le_s beta (fst b) /\
          le_r gamma (snd b).
    Proof.
      intros beta gamma Hbeta Hgamma.
      destruct Hbeta  as [gamma1 Hb_beta].
      destruct Hgamma as [beta1 Hb_gamma].
      destruct HD as [_ Hdir].
      specialize (Hdir _ _ Hb_beta Hb_gamma)
        as [[beta2 gamma2] [Hb2 [Hbeta12 Hgamma12]]].
      destruct Hbeta12  as [Hbeta_le  _].
      destruct Hgamma12 as [_ Hgamma_le].
      exists (beta2, gamma2). split.
      - exact Hb2.
      - split; [exact Hbeta_le | exact Hgamma_le].
    Qed.

    Definition beta_sup  : Lambda_s := supremum_s (fun beta  => exists gamma, D (beta,  gamma)).
    Definition gamma_sup : Lambda_r := supremum_r (fun gamma => exists beta , D (beta , gamma)).
    Lemma C_sup_equiv :
      Same_set Z (C_beta beta_sup A)
               (Union_indexed_lambda_s D_s (fun beta => C_beta beta A)).
    Proof. apply C_scott_beta; apply D_s_directed. Qed.

    Lemma R_sup_equiv :
      forall S,
        Same_set X (R_gamma gamma_sup S)
                 (Union_indexed_lambda_r D_r (fun gamma => R_gamma gamma S)).
    Proof. intros S; apply R_scott_gamma; apply D_r_directed. Qed.

    Lemma union_subset_sup :
      Included X
               (fun x => exists b, D b /\ K_raw b A x)
               (K_raw (supremum_B D) A).
    Proof.
      intros x [[beta gamma] [HbD Hx]].
      assert (Hle : (beta, gamma) <=B (supremum_B D))
        by (apply (proj1 (supremum_B_is_lub D HD)); exact HbD).
      apply (K_raw_monotone_b A (beta, gamma) (supremum_B D) Hle) in Hx.
      exact Hx.
    Qed.
    
    Lemma R_sup_elim :
      forall (S : Powerset Z) x,
        In _ (R_gamma gamma_sup S) x ->
        exists gamma, D_r gamma /\ In _ (R_gamma gamma S) x.
      Proof.
        intros S x Hx_sup.
        destruct (R_sup_equiv S) as [Hsup_subset_union _].
        specialize (Hsup_subset_union _ Hx_sup).
        unfold Union_indexed_lambda_r in Hsup_subset_union.
        destruct Hsup_subset_union as [gamma [HDr Hx_gamma]].
        now exists gamma.
      Qed.
      
    Lemma C_sup_elim :
      forall z,
        In _ (C_beta beta_sup A) z ->
        exists beta, D_s beta /\ In _ (C_beta beta A) z.
    Proof.
      intros z Hz_sup.
      destruct C_sup_equiv as [Hsup_subset_union _].
      specialize (Hsup_subset_union _ Hz_sup).
      unfold Union_indexed_lambda_s in Hsup_subset_union.
      destruct Hsup_subset_union as [beta [HDbeta Hz_beta]].
      now exists beta.
    Qed.
    
    Lemma components_to_budget :
      forall beta gamma x,
        D_s beta ->
        D_r gamma ->
        In _ (R_gamma gamma (C_beta beta A)) x ->
        exists b, D b /\ In _ (K_raw b A) x.
    Proof.
      intros beta gamma x HbetaDs HgammaDr Hx_in.
      destruct (upper_bound_in_D beta gamma HbetaDs HgammaDr)
        as [b [Hb_in_D [Hbeta_le Hgamma_le]]].
      assert (Hle : (beta, gamma) <=B b) by (split; assumption).
      exists b; split; [exact Hb_in_D|].
      apply (K_raw_monotone_b A (beta, gamma) b Hle).
      exact Hx_in.
    Qed.
    Lemma sup_budget_to_components :
      forall x,
        In _ (K_raw (supremum_B D) A) x ->
        exists beta gamma,
          D_s beta /\ D_r gamma /\
          In _ (R_gamma gamma (C_beta beta A)) x.
    Proof.
      intros x Hx_sup.
      unfold K_raw in Hx_sup.
      destruct (R_sup_elim (C_beta beta_sup A) x Hx_sup) as [gamma [Hgamma_Dr Hx_gamma]].
      set (S :=Union_indexed_lambda_s D_s (fun beta => C_beta beta A)).
      destruct C_sup_equiv as [HCsup_S HS_Csup].
      assert (Hx_gamma_S : In _ (R_gamma gamma S) x).
      { apply (R_monotone_A gamma _ _ HCsup_S); exact Hx_gamma. }
      set (I        := { beta : Lambda_s | D_s beta }).
      set (le_I     := fun i j : I => le_s (proj1_sig i) (proj1_sig j)).
      set (fam_I    := fun i : I => C_beta (proj1_sig i) A).
      assert (HinhI : inhabited I).
      { destruct D_s_directed as [[beta0 Hbeta0] _]. constructor. exact (exist _ beta0 Hbeta0).  }
      assert (HdirI : IsDirectedFamily le_I fam_I).
      { destruct D_s_directed as [[ask0 Hask0] Hdir_s].
        split.
        - intros [ask1 Hask1] [ask2 Hask2].
          destruct (Hdir_s _ _ Hask1 Hask2)
          as [ask3 [Hask3 [H13 H23]]].
          exists (exist _ ask3 Hask3); split; assumption.
        - intros [ask1 Hask1] [ask2 Hask2] Hle z Hz.
          simpl in *; apply (C_monotone_beta A ask1 ask2 Hle); exact Hz. 
      }
      pose proof
       (R_scott_A gamma I HinhI le_I fam_I HdirI) as [Hscott _].
       assert (Hunions_eq : Same_set Z (Union_indexed_family fam_I) S).
      { 
        unfold Same_set, Union_indexed_family, S; split; intros z Hz.
        - destruct Hz as [i Hz]; destruct i as [ask Hask]; simpl in *; now exists ask.
        - destruct Hz as [ask [Hask Hz]]; now exists (exist _ ask Hask). 
      }
      destruct Hunions_eq as [HUF_to_S HSto_UF].
      assert (Hx_union : In _ (R_gamma gamma (Union_indexed_family fam_I)) x).
      { apply (R_monotone_A gamma _ _ HSto_UF); exact Hx_gamma_S. }
      specialize (Hscott _ Hx_union).
      destruct Hscott as [i Hxi]; destruct i as [ask Hask_Ds]; simpl in *.
      exists ask, gamma; repeat split; assumption.
    Qed.

    Lemma sup_subset_union :
      Included X
               (K_raw (supremum_B D) A)
               (fun x => exists b, D b /\ K_raw b A x).
    Proof.
      intros x Hx_sup.
      destruct (sup_budget_to_components x Hx_sup) as [ask [gamma [Hask_Ds [Hgamma_Dr Hx_RG]]]].
      destruct (components_to_budget ask gamma x Hask_Ds Hgamma_Dr Hx_RG)
        as [b [Hb_in_D Hx_Kb]].
      exists b; split; assumption.
    Qed.
    
    Lemma K_raw_in_K_bar (b : Budget) :
      Included X (K_raw b A) (K_bar b A).
    Proof.
      intros x Hx_raw.
      unfold K_bar; intros C HA_C Hclosed_C.
      assert (Hx_raw_in_C : In _ (K_raw b C) x).
      { apply (K_raw_monotone_A b A C HA_C); exact Hx_raw. }
      apply Hclosed_C; exact Hx_raw_in_C.
    Qed.
  End RawScottBudget.

  Proposition K_raw_scott_b (A : Powerset X) (D : Ensemble Budget) : IsDirected_B D ->
    Same_set X (K_raw (supremum_B D) A) (fun x => exists b, D b /\ K_raw b A x).
  Proof.
    intro HD; split.
    - apply (sup_subset_union A D HD).
    - apply (union_subset_sup A D HD).
  Qed.
  
  Lemma K_bar_extensive (b : Budget) (A : Powerset X) : Included X A (K_bar b A).
  Proof. intros x HxA C HA_C HK_C; exact (HA_C x HxA). Qed.
  
  Lemma K_bar_monotone_A (b : Budget) (A B : Powerset X) :
    Included X A B -> Included X (K_bar b A) (K_bar b B).
  Proof.
    intros H_A_incl_B x Hx_in_KbarA.
    unfold K_bar in *.
    intros C' H_B_incl_C' H_K_raw_closed'.
    apply Hx_in_KbarA.
    - intros y HyA; apply H_B_incl_C'; apply H_A_incl_B; assumption.
    - assumption.
  Qed.

  Lemma K_bar_is_K_raw_closed (b : Budget) (A : Powerset X) :
    Is_K_raw_closed b (K_bar b A).
  Proof.
    intros x Hx_in_K_raw_of_K_bar.
    unfold K_bar.
    intros C H_A_incl_C H_K_raw_closed.
    assert (H_Kbar_incl_C : Included X (K_bar b A) C).
    { intros y Hy_in_Kbar; unfold K_bar in Hy_in_Kbar; apply (Hy_in_Kbar C H_A_incl_C H_K_raw_closed). }
    apply (K_raw_monotone_A b (K_bar b A) C) in H_Kbar_incl_C.
    apply H_K_raw_closed.
    apply H_Kbar_incl_C.
    exact Hx_in_K_raw_of_K_bar.
  Qed.
  
  Lemma K_bar_idempotent (b : Budget) (A : Powerset X) :
    Same_set X (K_bar b (K_bar b A)) (K_bar b A).
  Proof.
    unfold Same_set, Included; split.
    - intros x Hx.
      unfold K_bar in Hx.
      specialize (Hx (K_bar b A)
                     (fun y Hy => Hy)
                     (K_bar_is_K_raw_closed b A)).
      exact Hx.
    - intros x Hx.
      unfold K_bar in *.
      intros C HKbarA_C Hclosed_C.
      assert (HA_C : Included X A C).
      { intros y HyA; apply HKbarA_C; apply K_bar_extensive; exact HyA. }
      exact (Hx C HA_C Hclosed_C).
  Qed.
  
  Lemma K_bar_monotone_b A b1 b2 : b1 <=B b2 -> Included X (K_bar b1 A) (K_bar b2 A).
  Proof.
    intros Hle x Hx_bar1.
    unfold K_bar in *.
    intros C HA_C Hclosed_b2. 
    assert (Hclosed_b1 : Is_K_raw_closed b1 C).
    { unfold Is_K_raw_closed in *.
      intros y Hy.
      apply Hclosed_b2.
      apply (K_raw_monotone_b C b1 b2 Hle); exact Hy. 
    }
    apply (Hx_bar1 C HA_C Hclosed_b1).
  Qed.
  
  Lemma union_subset_Kbar_sup
        (A : Powerset X) (D : Ensemble Budget) (HD : IsDirected_B D) :
    Included X
             (fun x : X => exists b, D b /\ K_bar b A x)
             (K_bar (supremum_B D) A).
  Proof.
    intros x [b [HbD Hx]].
    apply (K_bar_monotone_b A b (supremum_B D)); last exact Hx.
    apply (proj1 (supremum_B_is_lub D HD)); exact HbD.
  Qed.

  Section BigUnionClosure.

    Variable A : Powerset X.
    Variable D : Ensemble Budget.
    Hypothesis HD : IsDirected_B D.

    Definition Idx := { b : Budget | D b }.
    Definition le_Idx (i j : Idx) : Prop :=
      le_B (proj1_sig i) (proj1_sig j).
    Definition fam (i : Idx) : Powerset X :=
      K_bar (proj1_sig i) A.

    Lemma fam_directed : IsDirectedFamily le_Idx fam.
    Proof.
      split.
      - intros [b1 Hb1] [b2 Hb2].
        destruct HD as [_ Hdir].
        destruct (Hdir _ _ Hb1 Hb2) as [b3 [Hb3 [Hb1b3 Hb2b3]]].
        exists (exist _ b3 Hb3); split; assumption.
      - intros [b1 Hb1] [b2 Hb2] Hle. simpl in Hle.
        apply K_bar_monotone_b; exact Hle.
    Qed.

    Lemma Idx_inhabited : inhabited Idx.
    Proof.
      destruct HD as [[b0 Hb0] _]; constructor. exact (exist _ b0 Hb0).
    Qed.

    Lemma climb_to_some_Kbar :
      forall b (HbD : D b) x,
        In _ (K_raw b (fun y => exists d, D d /\ K_bar d A y)) x ->
        exists d, D d /\ In _ (K_bar d A) x.
    Proof.
      intros b HbD x Hx.
      pose (Hsc := K_raw_scott_A b Idx Idx_inhabited le_Idx fam fam_directed).
      destruct Hsc as [Hinto _].
      assert (Hun :
        Same_set X (Union_indexed_family fam)
                   (fun y => exists d, D d /\ K_bar d A y)).
      { split.
        - intros y [i Hy]. destruct i as [d Hd]. simpl in *. now exists d.
        - intros y [d [Hd Hy]]. exists (exist _ d Hd). exact Hy.
      }
      destruct Hun as [Hun12 Hun21].
      assert (Hx' : In _ (K_raw b (Union_indexed_family fam)) x).
      { apply (K_raw_monotone_A b
               (fun y => exists d, D d /\ K_bar d A y)
               (Union_indexed_family fam) Hun21); exact Hx. }

      specialize (Hinto _ Hx'). 
      destruct Hinto as [i Hxi]. destruct i as [d0 Hd0]. simpl in *.
      destruct HD as [_ Hdir].
      destruct (Hdir b d0 HbD Hd0) as
        [d1 [Hd1 [Hb_le_d1 Hd0_le_d1]]].
      assert (Hx1 : In _ (K_raw d1 (K_bar d0 A)) x).
      { apply (K_raw_monotone_b (K_bar d0 A) b d1 Hb_le_d1); exact Hxi. }
      assert (Hincl_bar : Included X (K_bar d0 A) (K_bar d1 A)).
      { apply K_bar_monotone_b; exact Hd0_le_d1. }
      assert (Hx2 : In _ (K_raw d1 (K_bar d1 A)) x).
      { apply (K_raw_monotone_A d1 (K_bar d0 A) (K_bar d1 A) Hincl_bar); exact Hx1. }
      pose proof (K_bar_is_K_raw_closed d1 A) as Hclosed.
      specialize (Hclosed x Hx2).
      now exists d1; split; [exact Hd1 | exact Hclosed].
    Qed.
    
    Lemma big_union_is_closed :
      Is_K_raw_closed (supremum_B D)
                      (fun x => exists b, D b /\ K_bar b A x).
    Proof.
      unfold Is_K_raw_closed; intros x Hx_sup.
      pose (Hsc := K_raw_scott_b
                     (fun y => exists b0, D b0 /\ K_bar b0 A y) D HD).
      destruct Hsc as [Hsup_into _].
      specialize (Hsup_into _ Hx_sup).
      destruct Hsup_into as [b [HbD Hx_b]].
      destruct (climb_to_some_Kbar b HbD x Hx_b)
        as [d [HdD Hx_bar]].
      now exists d.
    Qed.
  End BigUnionClosure.

  Lemma Kbar_sup_subset_big_union
        (A : Powerset X) (D : Ensemble Budget) (HD : IsDirected_B D) :
    Included X
             (K_bar (supremum_B D) A)
             (fun x : X => exists b, D b /\ K_bar b A x).
  Proof.
    set (U := fun x : X => exists b, D b /\ K_bar b A x).
    assert (HU_closed : Is_K_raw_closed (supremum_B D) U)
      by (apply big_union_is_closed; exact HD).
    assert (HA_U : Included X A U).
    {
      intros y HyA.
      destruct HD as [[b0 Hb0] _]. 
      exists b0; split; [exact Hb0|].
      apply K_bar_extensive; exact HyA.
    }
    intros x Hx_Kbar_sup.
    unfold K_bar in Hx_Kbar_sup.
    exact (Hx_Kbar_sup U HA_U HU_closed).
  Qed.

  Proposition K_bar_scott_b (A : Powerset X) (D : Ensemble Budget) : IsDirected_B D ->
    Same_set X (K_bar (supremum_B D) A) (fun x => exists b, D b /\ K_bar b A x).
  Proof.
    intro HD. split.
    - apply Kbar_sup_subset_big_union; exact HD.
    - apply union_subset_Kbar_sup; exact HD.
  Qed.

  Lemma directed_family_Kbar :
    forall b (I : Type) (leI : I -> I -> Prop) (fam : I -> Powerset X),
      IsDirectedFamily leI fam ->
      IsDirectedFamily leI (fun i => K_bar b (fam i)).
  Proof.
    intros b I leI fam [Hupper Hincl]; split.
    - intros i j. destruct (Hupper i j) as [k [Hik Hjk]]. exists k; split; assumption.
    - intros i j Hij. apply K_bar_monotone_A, Hincl, Hij.
  Qed.
  
  Lemma union_of_closed_is_closed :
    forall b (I : Type) (hI : inhabited I) (leI : I -> I -> Prop)
           (fam : I -> Powerset X),
      (forall i, Is_K_raw_closed b (fam i)) ->
      IsDirectedFamily leI fam ->
      Is_K_raw_closed b (Union_indexed_family fam).
  Proof.
    intros b I hI leI fam Hclosed Hdir x Hx_raw.
    pose (Hsc := K_raw_scott_A b I hI leI fam Hdir).
    destruct Hsc as [Hinto _].
    specialize (Hinto _ Hx_raw) as [i Hxi_raw].
    specialize (Hclosed i); unfold Is_K_raw_closed in Hclosed.
    specialize (Hclosed _ Hxi_raw).
    exists i; exact Hclosed.
  Qed.

  Lemma K_bar_scott_A :
    forall b (I : Type) (hI : inhabited I) (leI : I -> I -> Prop)
           (fam : I -> Powerset X),
      IsDirectedFamily leI fam ->
      Same_set X (K_bar b (Union_indexed_family fam))
               (Union_indexed_family (fun i => K_bar b (fam i))).
  Proof.
    intros b I hI leI fam Hdir.
    set (U  := Union_indexed_family fam).
    set (CU := Union_indexed_family (fun i => K_bar b (fam i))).
    unfold Same_set; split.
    - intros x HxK.
      assert (HU_CU : Included X U CU).
      { 
        intros y [i Hy_i]; unfold CU, Union_indexed_family.
        exists i; apply K_bar_extensive, Hy_i. 
      }
      assert (Hclosed_CU : Is_K_raw_closed b CU).
      { 
        apply union_of_closed_is_closed
        with (leI := leI)
             (fam := fun i => K_bar b (fam i)).
        - exact hI.
        - intro i; apply K_bar_is_K_raw_closed.
        - apply directed_family_Kbar, Hdir. 
      }
      unfold K_bar in HxK; apply (HxK CU HU_CU Hclosed_CU).
    - intros x [i Hxi]; apply (K_bar_monotone_A b (fam i) U).
      + intros y Hy; unfold U, Union_indexed_family; exists i; exact Hy.
      + exact Hxi.
  Qed.
  
  Theorem Two_budget_BICO :
      let K_op_bar b := K_bar b in
      (forall b A, Included X A (K_op_bar b A)) /\
      (forall b A, Same_set X (K_op_bar b (K_op_bar b A)) (K_op_bar b A)) /\
      (forall b A B, Included X A B -> Included X (K_op_bar b A) (K_op_bar b B)) /\
      (forall A (D : Ensemble Budget), IsDirected_B D ->
          Same_set X (K_op_bar (supremum_B D) A)
                     (fun x => exists b, D b /\ K_op_bar b A x)) /\
      (forall b (I:Type) (hI:inhabited I) (leI:I->I->Prop) (fam:I->Powerset X),
         IsDirectedFamily leI fam ->
         Same_set X (K_op_bar b (Union_indexed_family fam))
                    (Union_indexed_family (fun i => K_op_bar b (fam i)))).
  Proof.
    split.
    - exact K_bar_extensive.
    - split.
      + exact K_bar_idempotent.
      + split.
        * exact K_bar_monotone_A.
        * split.
          -- exact K_bar_scott_b.
          -- intros b I hI leI fam Hdir. apply (K_bar_scott_A b I hI leI fam Hdir).
  Qed.
  
  Parameter R_inf : Powerset Z -> Powerset X.
  Axiom R_gamma_le_R_inf : forall gamma S, Included X (R_gamma gamma S) (R_inf S).
  Definition set_minus (P : Type) (A B : Powerset P) : Powerset P :=
    fun x => A x /\ ~ (B x).
  Notation "A \\ B" := (set_minus _ A B) (at level 50).
  Definition L_storage (beta : Lambda_s) (D : Powerset X) : Powerset X :=
    D \\ (R_inf (C_beta beta D)).
  Definition L_retrieval (b : Budget) (D : Powerset X) : Powerset X :=
    (fun x => D x /\ R_inf (C_beta (fst b) D) x) \\ (K_raw b D).
  Definition Disjoint (P : Type) (A B : Powerset P) : Prop :=
    forall x, ~ (A x /\ B x).

  Section Loss_Decomposition_Proofs.
    Context {b : Budget} {D : Powerset X}.

    Lemma L_storage_retrieval_disjoint :
      Disjoint X (L_storage (fst b) D) (L_retrieval b D).
    Proof.
      intros x [Hstor Hretr].
      unfold Disjoint, L_storage, L_retrieval, set_minus in *; simpl in *.
      destruct Hstor as [HDx HnR].
      destruct Hretr as [[HDx' HR] HnK].
      apply HnR; exact HR.
    Qed.

    Lemma K_raw_in_R_inf :
      Included X (K_raw b D) (R_inf (C_beta (fst b) D)).
    Proof.
      unfold K_raw.
      intros x Hx.
      apply (R_gamma_le_R_inf (snd b) (C_beta (fst b) D) x Hx).
    Qed.
  
    Lemma loss_decomposition_union :
      Same_set X (fun x => D x /\ ~ K_raw b D x)
               (fun x => L_storage (fst b) D x \/ L_retrieval b D x).
    Proof.
      unfold Same_set, Included; split.
      - intros x [HDx HnotK].
        unfold L_storage, L_retrieval, set_minus in *.
        destruct (classic (R_inf (C_beta (fst b) D) x)) as [Hinf | Hninf].
        + right. repeat split; try assumption.
        + left.  split; assumption.
      - intros x [Hstor | Hretr].
        + 
          destruct Hstor as [HDx Hninf].
          split; [assumption|].
          intro Hk.
          apply Hninf.
          apply K_raw_in_R_inf with (x := x); assumption.
        + 
          destruct Hretr as [[HDx Hinf] HnK].
          split; assumption.
    Qed.

    Proposition Loss_Decomposition :
        Disjoint X (L_storage (fst b) D) (L_retrieval b D) /\
        Same_set X (D \\ K_raw b D)
                   (fun x => L_storage (fst b) D x \/ L_retrieval b D x).
    Proof.
      split.
      - apply L_storage_retrieval_disjoint.
      - unfold set_minus; apply loss_decomposition_union.
    Qed.
  End Loss_Decomposition_Proofs.
  
  Parameter P_store : X -> Lambda_s -> R.
  Parameter P_retr : X -> Lambda_s -> Lambda_r -> R.

  Definition Pr_decomposed (x : X) (b : Budget) : R :=
    (P_store x (fst b)) * (P_retr x (fst b) (snd b)).
  Definition lower_closure_X (A : Powerset X) : Powerset X :=
    fun p_elem : X => exists a_elem : X, A a_elem /\ p_elem <=_X a_elem.
  Definition GR_decomposed (p : R) (b : Budget) : Powerset X :=
    lower_closure_X (fun x => (Pr_decomposed x b > p)%R).
End DECOMPOSITION_OF_LOSS.

Module MULTI_CHANNEL_DECOMPOSITION (DS : DECOMPOSITION_SETTING).
  Import DS.

  Module Mono := DECOMPOSITION_OF_LOSS DS.
  Import Mono.

  Parameter K : Type.
  Parameter Bucket : K -> Powerset X.

  Axiom Bucket_cover : forall x : X, exists k : K, Bucket k x.
  Axiom Bucket_pairwise_disjoint :
    forall k1 k2 x, Bucket k1 x -> Bucket k2 x -> k1 = k2.

  Definition restr (k : K) (A : Powerset X) : Powerset X :=
    fun x => A x /\ Bucket k x.

  Lemma restr_monotone k :
    forall A B, Included X A B -> Included X (restr k A) (restr k B).
  Proof. intros A B H x [HxA Hk]; split; [apply H; exact HxA|exact Hk]. Qed.

  Lemma restr_distrib_union_family k :
    forall (I : Type) (fam : I -> Powerset X),
      Same_set X
        (restr k (Union_indexed_family fam))
        (Union_indexed_family (fun i => restr k (fam i))).
  Proof.
    intros I fam; split.
    - intros x [ [i Hix] Hk ]; exists i; split; [exact Hix|exact Hk].
    - intros x [i [Hix Hk]]; split; [now exists i|exact Hk].
  Qed.


  Definition BudgetVec := K -> Mono.Budget.

  Definition le_Bvec (b1 b2 : BudgetVec) : Prop :=
    forall k, Mono.le_B (b1 k) (b2 k).

  Lemma le_Bvec_refl : forall b, le_Bvec b b.
  Proof. intros b k; apply Mono.le_B_refl. Qed.

  Lemma le_Bvec_trans : forall b1 b2 b3,
    le_Bvec b1 b2 -> le_Bvec b2 b3 -> le_Bvec b1 b3.
  Proof. intros b1 b2 b3 H12 H23 k; eapply Mono.le_B_trans; eauto. Qed.

  Lemma le_Bvec_antisym : forall b1 b2,
    le_Bvec b1 b2 -> le_Bvec b2 b1 -> b1 = b2.
  Proof.
    intros b1 b2 H12 H21; extensionality k.
    apply Mono.le_B_antisym; [apply H12|apply H21].
  Qed.

  Definition IsDirected_Bvec (D : Ensemble BudgetVec) : Prop :=
    (Inhabited BudgetVec D) /\
    (forall b1 b2, D b1 -> D b2 ->
       exists ub, D ub /\ le_Bvec b1 ub /\ le_Bvec b2 ub).

  Definition D_at (D : Ensemble BudgetVec) (k : K) : Ensemble Mono.Budget :=
    fun b => exists bv, D bv /\ b = bv k.

  Lemma D_at_directed :
    forall D, IsDirected_Bvec D -> forall k, Mono.IsDirected_B (D_at D k).
  Proof.
    intros D [ [bv0 Hb0] Hdir ] k; split.
    - destruct (Hdir bv0 bv0 Hb0 Hb0) as [u [Hu _]].
      exists (u k); now exists u.
    - intros b1 b2 [bv1 [Hbv1 ->]] [bv2 [Hbv2 ->]].
      destruct (Hdir bv1 bv2 Hbv1 Hbv2) as [u [Hu [H1u H2u]]].
      exists (u k); split; [now exists u|split; [apply H1u|apply H2u]].
  Qed.

  Definition supremum_Bvec (D : Ensemble BudgetVec) : BudgetVec :=
    fun k => Mono.supremum_B (D_at D k).

  Lemma supremum_Bvec_is_lub :
    forall D, IsDirected_Bvec D ->
      ( forall bv, D bv -> le_Bvec bv (supremum_Bvec D)
      ) /\
      ( forall ub, (forall bv, D bv -> le_Bvec bv ub) ->
                   le_Bvec (supremum_Bvec D) ub).
  Proof.
    intros D HD; split.
    - intros bv Hbv k.
      destruct (Mono.supremum_B_is_lub (D_at D k) (D_at_directed D HD k))
        as [Hub _].
      unfold supremum_Bvec; apply Hub; exists bv; split; [exact Hbv | reflexivity].
    - intros ub Hub k.
      destruct (Mono.supremum_B_is_lub (D_at D k) (D_at_directed D HD k)) as [_ Hleast].
      unfold supremum_Bvec; apply Hleast; intros b Hb.
      destruct Hb as [bv [Hbv ->]]; apply Hub; exact Hbv.
  Qed.

  Definition K_raw_k (k : K) (b : Mono.Budget) (A : Powerset X) : Powerset X :=
    Mono.K_raw b (restr k A).
  Definition K_raw_mc (bv : BudgetVec) (A : Powerset X) : Powerset X :=
    Union_indexed_family (fun k => K_raw_k k (bv k) A).
  Definition Is_K_raw_mc_closed (bv : BudgetVec) (C : Powerset X) : Prop :=
    Included X (K_raw_mc bv C) C.
  Definition K_bar_mc (bv : BudgetVec) (A : Powerset X) : Powerset X :=
    fun x => forall C, Included X A C -> Is_K_raw_mc_closed bv C -> C x.

  Lemma K_raw_k_monotone_A :
    forall k b A B, Included X A B ->
      Included X (K_raw_k k b A) (K_raw_k k b B).
  Proof.
    intros k b A B HAB x Hx.
    unfold K_raw_k in *.
    apply (Mono.K_raw_monotone_A b (restr k A) (restr k B)).
    apply restr_monotone; exact HAB.
    exact Hx.
  Qed.
  
  Lemma restr_family_directed :
    forall k (I:Type) (leI:I->I->Prop) (fam:I->Powerset X),
      IsDirectedFamily leI fam ->
      IsDirectedFamily leI (fun i => restr k (fam i)).
  Proof.
    intros k I leI fam [Hup Hincl]; split.
    - intros i j; destruct (Hup i j) as [u [Hiu Hju]]; exists u; split; assumption.
    - intros i j Hij; apply restr_monotone, Hincl, Hij.
  Qed.

  Lemma K_raw_k_scott_A :
    forall k b (I:Type) (hI:inhabited I) (leI:I->I->Prop) (fam:I->Powerset X),
      IsDirectedFamily leI fam ->
      Same_set X (K_raw_k k b (Union_indexed_family fam))
                 (Union_indexed_family (fun i => K_raw_k k b (fam i))).
  Proof.
    intros k b I hI leI fam Hdir.
    unfold K_raw_k.
    pose proof
      (Mono.K_raw_scott_A b I hI leI (fun i => restr k (fam i))
           (restr_family_directed k I leI fam Hdir))
      as [Hinto Hback].
    destruct (restr_distrib_union_family k I fam) as [Hrfwd Hrbwd].
    split.
    - 
      intros x Hx.
      apply Hinto.
      apply (Mono.K_raw_monotone_A b
               (restr k (Union_indexed_family fam))
               (Union_indexed_family (fun i => restr k (fam i)))
               Hrfwd).
      exact Hx.
    - 
      intros x Hx.
      apply (Mono.K_raw_monotone_A b
               (Union_indexed_family (fun i => restr k (fam i)))
               (restr k (Union_indexed_family fam))
               Hrbwd).
      apply Hback; exact Hx.
  Qed.

  Lemma K_raw_mc_monotone_A :
    forall bv A B, Included X A B ->
      Included X (K_raw_mc bv A) (K_raw_mc bv B).
  Proof.
    intros bv A B HAB x [k Hxk]; exists k.
    eapply K_raw_k_monotone_A; [|apply Hxk]; exact HAB.
  Qed.

  Lemma K_raw_mc_scott_A :
    forall bv (I:Type) (hI:inhabited I) (leI:I->I->Prop) (fam:I->Powerset X),
      IsDirectedFamily leI fam ->
      Same_set X (K_raw_mc bv (Union_indexed_family fam))
                 (Union_indexed_family (fun i => K_raw_mc bv (fam i))).
  Proof.
    intros bv I hI leI fam Hdir; unfold K_raw_mc.
    split.
    - intros x [k Hxk].
      pose proof (K_raw_k_scott_A k (bv k) I hI leI fam Hdir) as [H _].
      specialize (H x Hxk). destruct H as [i Hxi]. exists i. now exists k.
    - intros x [i [k Hxk]]. exists k.
      pose proof (K_raw_k_scott_A k (bv k) I hI leI fam Hdir) as [_ H].
      specialize (H x). apply H. now exists i.
  Qed.

  Lemma K_raw_mc_monotone_bvec :
    forall bv1 bv2 A, le_Bvec bv1 bv2 ->
      Included X (K_raw_mc bv1 A) (K_raw_mc bv2 A).
  Proof.
    intros bv1 bv2 A Hle x [k Hxk]. exists k.
    unfold K_raw_k in *.
    eapply Mono.K_raw_monotone_b; [apply Hle|]; exact Hxk.
  Qed.

  Lemma K_raw_mc_scott_bvec :
    forall A (D : Ensemble BudgetVec),
      IsDirected_Bvec D ->
      Same_set X (K_raw_mc (supremum_Bvec D) A)
                 (fun x => exists bv, D bv /\ K_raw_mc bv A x).
  Proof.
    intros A D HD; split.
    - 
      intros x [k Hxk].
      unfold K_raw_k in Hxk.
      (* Use monolithic "Scott in budget" on the projection D_at D k *)
      pose proof (Mono.K_raw_scott_b (restr k A) (D_at D k)
                    (D_at_directed D HD k)) as [Hinto _].
      specialize (Hinto x Hxk).
      destruct Hinto as [b [Hb Hxk']].
      destruct Hb as [bv [HbD ->]].
      exists bv; split; [exact HbD|].
      exists k; exact Hxk'.
    - 
      intros x [bv [HbD [k Hxk]]].
      destruct (supremum_Bvec_is_lub D HD) as [Hub _].
      specialize (Hub bv HbD).
      exists k.
      eapply Mono.K_raw_monotone_b; [apply Hub|]; exact Hxk.
  Qed.

  (* Hull: closure operator basics  *)
  Lemma K_bar_mc_extensive :
    forall bv A, Included X A (K_bar_mc bv A).
  Proof.
    intros bv A x Hx C HA HC; apply HA; exact Hx.
  Qed.

  Lemma K_bar_mc_monotone_A :
    forall bv A B, Included X A B ->
      Included X (K_bar_mc bv A) (K_bar_mc bv B).
  Proof.
    intros bv A B HAB x Hx C HB HC.
    apply Hx; [intros y Hy; apply HB, HAB, Hy | exact HC].
  Qed.

  Lemma K_bar_mc_is_closed :
    forall bv A, Is_K_raw_mc_closed bv (K_bar_mc bv A).
  Proof.
    intros bv A x Hx C HA HC.
    assert (HKincl : Included X (K_bar_mc bv A) C).
    { intros y Hy; apply Hy; [assumption|assumption]. }
    pose proof (K_raw_mc_monotone_A bv (K_bar_mc bv A) C HKincl x Hx) as HxC.
    apply HC; exact HxC.
  Qed.

  Lemma K_bar_mc_idempotent :
    forall bv A, Same_set X (K_bar_mc bv (K_bar_mc bv A)) (K_bar_mc bv A).
  Proof.
    intros bv A; split.
    - intros x Hx. apply Hx; [intros y Hy; exact Hy | apply K_bar_mc_is_closed].
    - intros x Hx C HA HC.
      assert (HA' : Included X A C).
      { intros y Hy; apply HA; apply K_bar_mc_extensive; exact Hy. }
      apply Hx; [exact HA'|exact HC].
  Qed.

  Lemma K_bar_mc_monotone_bvec :
    forall bv1 bv2 A, le_Bvec bv1 bv2 ->
      Included X (K_bar_mc bv1 A) (K_bar_mc bv2 A).
  Proof.
    intros bv1 bv2 A Hle x Hx C HA HC2.
    assert (HC1 : Is_K_raw_mc_closed bv1 C).
    { intros y Hy. apply HC2.
      eapply K_raw_mc_monotone_bvec; [apply Hle|exact Hy]. }
    apply Hx; [exact HA|exact HC1].
  Qed.

  Lemma union_of_closed_is_closed_mc :
    forall bv (I:Type) (hI:inhabited I) (leI:I->I->Prop) (fam:I->Powerset X),
      (forall i, Is_K_raw_mc_closed bv (fam i)) ->
      IsDirectedFamily leI fam ->
      Is_K_raw_mc_closed bv (Union_indexed_family fam).
  Proof.
    intros bv I hI leI fam Hclosed Hdir x Hx.
    pose proof (K_raw_mc_scott_A bv I hI leI fam Hdir) as [Hinto _].
    specialize (Hinto x Hx) as [i Hxi].
    specialize (Hclosed i) as Hci.
    apply Hci in Hxi.
    exists i. 
    exact Hxi.
  Qed.

  Lemma directed_family_Kbar_mc :
    forall bv (I:Type) (leI:I->I->Prop) (fam:I->Powerset X),
      IsDirectedFamily leI fam ->
      IsDirectedFamily leI (fun i => K_bar_mc bv (fam i)).
  Proof.
    intros bv I leI fam [Hup Hincl]; split.
    - intros i j. destruct (Hup i j) as [k [Hik Hjk]]. exists k; split; assumption.
    - intros i j Hij. apply K_bar_mc_monotone_A, Hincl, Hij.
  Qed.

  Lemma K_bar_mc_scott_A :
    forall bv (I:Type) (hI:inhabited I) (leI:I->I->Prop) (fam:I->Powerset X),
      IsDirectedFamily leI fam ->
      Same_set X (K_bar_mc bv (Union_indexed_family fam))
                 (Union_indexed_family (fun i => K_bar_mc bv (fam i))).
  Proof.
    intros bv I hI leI fam Hdir; split.
    - 
      intros x Hx.
      set (U := Union_indexed_family fam).
      set (CU := Union_indexed_family (fun i => K_bar_mc bv (fam i))).
      assert (HU_in_CU : Included X U CU).
      { intros y [i Hy]; exists i; apply K_bar_mc_extensive, Hy. }
      assert (HCU_closed : Is_K_raw_mc_closed bv CU).
      { 
        set (famK := fun i => K_bar_mc bv (fam i)).
        eapply union_of_closed_is_closed_mc with (fam:=famK).
        - exact hI.
        - intro i; apply K_bar_mc_is_closed.
        - apply directed_family_Kbar_mc, Hdir.
      }
      unfold K_bar_mc in Hx; apply (Hx CU HU_in_CU HCU_closed).
    - 
      intros x [i Hxi].
      apply (K_bar_mc_monotone_A bv (fam i) (Union_indexed_family fam)).
      + intros y Hy; exists i; exact Hy.
      + exact Hxi.
  Qed.

  Lemma union_subset_Kbar_mc_sup :
    forall A (D : Ensemble BudgetVec),
      IsDirected_Bvec D ->
      Included X
        (fun x => exists bv, D bv /\ K_bar_mc bv A x)
        (K_bar_mc (supremum_Bvec D) A).
  Proof.
    intros A D HD x [bv [Hbv Hx]].
    destruct (supremum_Bvec_is_lub D HD) as [Hub _].
    specialize (Hub bv Hbv).
    eapply K_bar_mc_monotone_bvec; [apply Hub|exact Hx].
  Qed.

  Section BigUnionClosure_mc.
    Variable A : Powerset X.
    Variable D : Ensemble BudgetVec.
    Hypothesis HD : IsDirected_Bvec D.

    Definition U : Powerset X :=
      fun x => exists bv, D bv /\ K_bar_mc bv A x.

    Definition Idx := { bv : BudgetVec | D bv }.
    Definition le_Idx (i j : Idx) : Prop :=
      le_Bvec (proj1_sig i) (proj1_sig j).
    Definition fam (i : Idx) : Powerset X :=
      K_bar_mc (proj1_sig i) A.

    Lemma U_as_union_mc :
      Same_set X (Union_indexed_family fam) U.
    Proof.
      unfold Same_set, Union_indexed_family, U; split.
      - intros x [i Hix]. destruct i as [bv Hb]; simpl in *.
        now exists bv.
      - intros x [bv [Hb Hx]]. now exists (exist _ bv Hb).
    Qed.

    Lemma fam_idx_directed_mc :
      IsDirectedFamily le_Idx fam.
    Proof.
      split.
      - intros [bv1 Hb1] [bv2 Hb2].
        destruct HD as [_ Hdir].
        destruct (Hdir bv1 bv2 Hb1 Hb2) as [ub [Hub [H12 H22]]].
        exists (exist _ ub Hub); split; assumption.
      - intros [bv1 Hb1] [bv2 Hb2] Hle.
        simpl in Hle. apply K_bar_mc_monotone_bvec, Hle.
    Qed.

    Lemma U_to_union : Included X U (Union_indexed_family fam).
    Proof. intros x H; apply (proj2 (U_as_union_mc) x); exact H. Qed.
    Lemma union_to_U : Included X (Union_indexed_family fam) U.
    Proof. intros x H; apply (proj1 (U_as_union_mc) x); exact H. Qed.

    Lemma U_closed_mc :
      Is_K_raw_mc_closed (supremum_Bvec D) U.
    Proof.
      unfold Is_K_raw_mc_closed; intros x Hx.
      pose proof (K_raw_mc_scott_bvec U D HD) as [Hinto _].
      specialize (Hinto x Hx).
      destruct Hinto as [bv0 [Hb0 Hraw0]].
      assert (Hx_union : In _ (K_raw_mc bv0 (Union_indexed_family fam)) x).
      { eapply K_raw_mc_monotone_A; [apply U_to_union|exact Hraw0]. }
      assert (Hinh : inhabited Idx) by (constructor; exact (exist _ bv0 Hb0)).
      destruct (K_raw_mc_scott_A bv0 Idx Hinh le_Idx fam fam_idx_directed_mc) as [Hscott _].
      specialize (Hscott x Hx_union).
      destruct Hscott as [i Hi].
      destruct i as [d0 Hd0]; simpl in Hi.

      destruct HD as [_ Hdir].
      destruct (Hdir bv0 d0 Hb0 Hd0) as [d1 [Hd1 [H01 H02]]].
      assert (Hx1 : In _ (K_raw_mc d1 (K_bar_mc d0 A)) x)
        by (eapply K_raw_mc_monotone_bvec; [apply H01|exact Hi]).
      assert (Incl : Included X (K_bar_mc d0 A) (K_bar_mc d1 A))
        by (apply K_bar_mc_monotone_bvec, H02).
      assert (Hx2 : In _ (K_raw_mc d1 (K_bar_mc d1 A)) x)
        by (eapply K_raw_mc_monotone_A; [apply Incl|exact Hx1]).
      pose proof (K_bar_mc_is_closed d1 A) as Hclosed.
      specialize (Hclosed x Hx2).
      exists d1; split; [exact Hd1 | exact Hclosed].
    Qed.

    Lemma A_in_U_mc : Included X A U.
    Proof.
      intros x Hx.
      destruct HD as [[bv0 Hb0] _].
      exists bv0; split; [exact Hb0|].
      apply K_bar_mc_extensive; exact Hx.
    Qed.

  End BigUnionClosure_mc.

  Lemma K_bar_mc_scott_bvec :
    forall A (D : Ensemble BudgetVec),
      IsDirected_Bvec D ->
      Same_set X (K_bar_mc (supremum_Bvec D) A)
                 (fun x => exists bv, D bv /\ K_bar_mc bv A x).
  Proof.
    intros A D HD; split.
    - 
      intros x Hx.
      set (U := fun y => exists bv, D bv /\ K_bar_mc bv A y).
      assert (HU : Is_K_raw_mc_closed (supremum_Bvec D) U)
        by (apply U_closed_mc; exact HD).
      assert (HAU : Included X A U)
        by (apply A_in_U_mc; exact HD).
      unfold K_bar_mc in Hx; exact (Hx U HAU HU).
    - apply union_subset_Kbar_mc_sup; exact HD.
  Qed.
  
  Theorem MultiChannel_BICO :
    let K_op_bar (bv : BudgetVec) := K_bar_mc bv in
      (forall bv A, Included X A (K_op_bar bv A)) /\
      (forall bv A, Same_set X (K_op_bar bv (K_op_bar bv A)) (K_op_bar bv A)) /\
      (forall bv A B, Included X A B -> Included X (K_op_bar bv A) (K_op_bar bv B)) /\
      (forall A (D : Ensemble BudgetVec), IsDirected_Bvec D ->
         Same_set X (K_op_bar (supremum_Bvec D) A)
                    (fun x => exists bv, D bv /\ K_op_bar bv A x)) /\
      (forall bv (I:Type) (hI:inhabited I) (leI:I->I->Prop) (fam:I->Powerset X),
         IsDirectedFamily leI fam ->
         Same_set X (K_op_bar bv (Union_indexed_family fam))
                    (Union_indexed_family (fun i => K_op_bar bv (fam i)))).
  Proof.
    intro K_op_bar; split.
    - intros bv A; apply K_bar_mc_extensive.
    - split.
      + intros bv0 A; apply K_bar_mc_idempotent.
      + split.
        * intros bv0 A B H; apply K_bar_mc_monotone_A; exact H.
        * split.
          -- intros A D HD; apply K_bar_mc_scott_bvec; exact HD.
          -- intros bv0 I hI leI fam Hdir; 
             apply (K_bar_mc_scott_A bv0 I hI leI fam Hdir).
  Qed.
End MULTI_CHANNEL_DECOMPOSITION.


