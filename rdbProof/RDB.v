(* RDB.v *)

Require Import Stdlib.Sets.Ensembles.
Require Import Stdlib.Setoids.Setoid.
Import Ensembles.
From Stdlib Require Import Init.Logic.
From Stdlib Require Import ssreflect ssrfun ssrbool.


(*===========================================================================*)
(* Section 0: Notation and Basic Setting                                     *)
(*===========================================================================*)

Module Type SETTING.

  Parameter X : Type.
  Parameter le_X : X -> X -> Prop.
  Axiom le_X_refl : forall x : X, le_X x x.
  Axiom le_X_antisym : forall x y : X, le_X x y -> le_X y x -> x = y.
  Axiom le_X_trans : forall x y z : X, le_X x y -> le_X y z -> le_X x z.
  Notation "x <=_X y" := (le_X x y) (at level 70).
  Notation "x <_X y" := (le_X x y /\ x <> y) (at level 70).

  Parameter Lambda : Type.
  Parameter le_Lambda : Lambda -> Lambda -> Prop.
  Axiom Lambda_non_empty : inhabited Lambda.
  Axiom le_Lambda_refl : forall l : Lambda, le_Lambda l l.
  Axiom le_Lambda_antisym : forall l1 l2 : Lambda, le_Lambda l1 l2 -> le_Lambda l2 l1 -> l1 = l2.
  Axiom le_Lambda_trans : forall l1 l2 l3 : Lambda, le_Lambda l1 l2 -> le_Lambda l2 l3 -> le_Lambda l1 l3.
  Notation "l1 <= l2" := (le_Lambda l1 l2) (at level 70).
  Notation "l1 < l2" := (le_Lambda l1 l2 /\ l1 <> l2) (at level 70).

  Definition IsDirected (D : Ensemble Lambda) : Prop :=
    (Stdlib.Sets.Ensembles.Inhabited Lambda D) /\
    (forall l1 l2 : Lambda, D l1 -> D l2 -> exists l_upper_bound : Lambda, D l_upper_bound /\ l1 <= l_upper_bound /\ l2 <= l_upper_bound).

  Parameter supremum : Ensemble Lambda -> Lambda.
  Axiom supremum_is_least_upper_bound :
    forall (D : Ensemble Lambda), IsDirected D ->
      ( (forall l_in_D : Lambda, D l_in_D -> l_in_D <= (supremum D)) /\
        (forall upper_b : Lambda, (forall l_in_D : Lambda, D l_in_D -> l_in_D <= upper_b) -> (supremum D) <= upper_b)
      ).

  Definition Powerset (P : Type) : Type := Ensemble P.
  Definition lower_closure (A : Powerset X) : Powerset X :=
    fun p_elem : X => exists a_elem : X, A a_elem /\ p_elem <=_X a_elem.
  Notation "'lc' A" := (lower_closure A) (at level 40).
  Definition minimals (A : Powerset X) : Powerset X :=
    fun a_elem : X => A a_elem /\ (forall a_prime : X, A a_prime -> a_prime <=_X a_elem -> a_prime = a_elem).
  Notation "'Min_X' ( A )" := (minimals A) (at level 60).

End SETTING.


(*===========================================================================*)
(* Section 1: Budget-Indexed Closure Operators                             *)
(*===========================================================================*)

Module BUDGET_INDEXED_CLOSURE_OPERATORS (S : SETTING).

  Import S.

  Parameter K_op : Lambda -> (Powerset X -> Powerset X).
  Notation K_lambda l := (K_op l).

  Axiom A1_Extensivity :
    forall (l : Lambda) (A : Powerset X),
    Included X A (K_lambda l A).

  Axiom A2_Idempotence :
    forall (l : Lambda) (A : Powerset X),
    Same_set X (K_lambda l (K_lambda l A)) (K_lambda l A).

  Axiom A3_Monotonicity_in_A :
    forall (l : Lambda) (A B : Powerset X),
    Included X A B -> Included X (K_lambda l A) (K_lambda l B).

  Definition Union_indexed (idx_set : Ensemble Lambda) (fam : Lambda -> Powerset X) : Powerset X :=
    fun x_val : X => exists l_idx : Lambda, idx_set l_idx /\ (fam l_idx x_val).

  Axiom A4_Scott_Continuity_in_lambda :
    forall (A : Powerset X) (D : Ensemble Lambda) (lambda_star : Lambda),
    IsDirected D ->
    lambda_star = supremum D ->
    Same_set X (K_lambda lambda_star A) (Union_indexed D (fun l' => K_lambda l' A)).
    
  Axiom A5_Lambda_directed :
    forall l1 l2 : Lambda, exists u : Lambda, l1 <= u /\ l2 <= u.


  Theorem P1_Monotonicity_in_lambda :
    forall (A : Powerset X) (l1 l2 : Lambda),
      l1 <= l2 -> Included X (K_lambda l1 A) (K_lambda l2 A).
  Proof.
    move=> A l1 l2 Hle.
    (* 1.  The directed set  D := {l1,l2}.*)
    set D := fun l : Lambda => (l = l1) \/ (l = l2).

    have HD : IsDirected D.
    { split.
      - exists l1. by left.
      - move=> a b Ha Hb.
        exists l2; split; first by right.
        split.
        + (* a <= l₂ *)
          move: Ha => [->|->]; [exact Hle | apply le_Lambda_refl].
        + (* b <= l₂ *)
          move: Hb => [->|->]; [exact Hle | apply le_Lambda_refl]. }
    (* 2.  l₂ is the supremum of D.*)
    have Hsup : supremum D = l2.
    { move: (supremum_is_least_upper_bound D HD) => [Hub Hleast].
      apply: le_Lambda_antisym.
      - (* supremum D <= l₂ *)
        apply: Hleast => l Hl.
        move: Hl => [->|->]; [exact Hle | apply le_Lambda_refl].
      - (* l₂ <= supremum D *)
        apply: Hub. by right. }
    (* 3.  Scott-continuity for that D.*)
    have Hsame :
      Same_set X (K_lambda l2 A) (Union_indexed D (fun l' => K_lambda l' A)).
      by apply: (A4_Scott_Continuity_in_lambda A D l2 HD); rewrite -Hsup.

    move: Hsame => [_ Hunion_to_Kl2].      (* Need Union ⊆ K l₂ *)
    move=> x Hx.                           (* x ∈ K l₁ A            *)
    apply: Hunion_to_Kl2.                  (* show it’s in the union*)
    exists l1; split; [by left | exact Hx].
  Qed.


  (*===========================================================================*)
  (* Section 2 and 3: Information Objects and Contexts                             *)
  (*===========================================================================*)

  Definition InformationObject := Powerset X.

  Definition CorrectedInformation (l : Lambda) (S : InformationObject) : Powerset X :=
    K_lambda l S.

  Definition Contexts (l : Lambda) : Ensemble (Powerset X) :=
    fun (C : Powerset X) => Same_set X (K_lambda l C) C.



  Lemma X_is_context : forall (l : Lambda),
      Contexts l (Full_set X).
  Proof.
    intros l.
    unfold Contexts.
    unfold Same_set.
    split.
    - (* K_lambda l (Full_set X) is included in Full_set X *)
      intros x Hx.
      apply Full_intro.
    - (* Full_set X is included in K_lambda l (Full_set X) *)
      intros x Hx.
      apply A1_Extensivity.
      apply Full_intro.
  Qed.

  Definition Meet_Contexts (l : Lambda) (Coll_Ctx : Ensemble (Powerset X)) : Powerset X :=
    fun x : X => forall C_i : Powerset X, Coll_Ctx C_i -> C_i x.


  Definition BigUnion (F : Ensemble (Powerset X)) : Powerset X :=
    fun x => exists C, F C /\ C x.

  Definition Join_Contexts (l : Lambda) (Coll_Ctx : Ensemble (Powerset X)) : Powerset X :=
    K_lambda l (BigUnion Coll_Ctx).

  Theorem contexts_complete_lattice : forall (l : Lambda) (Coll_Ctx : Ensemble (Powerset X)),
    (forall C, Coll_Ctx C -> Contexts l C) ->
    (exists inf, Contexts l inf /\
        (forall C, Coll_Ctx C -> Included X inf C) /\
        (forall T, Contexts l T -> (forall C, Coll_Ctx C -> Included X T C) -> Included X T inf)
    ) /\
    (exists sup, Contexts l sup /\
        (forall C, Coll_Ctx C -> Included X C sup) /\
        (forall T, Contexts l T -> (forall C, Coll_Ctx C -> Included X C T) -> Included X sup T)
    ).
  Proof.
  intros l0 Coll_Ctx H_Coll.
  split.
  (* Infimum *)
  - exists (Meet_Contexts l0 Coll_Ctx).
    assert (Contexts l0 (Meet_Contexts l0 Coll_Ctx)) as H_meet_ctx.
    {
      unfold Contexts, Meet_Contexts, Same_set.
      split.
      + (* K(M) ⊆ M *)
        intros x Hx_KM C_i HC_i.
        (* C_i is a context, so K C_i ⊆ C_i *)
        destruct (H_Coll C_i HC_i) as [H_KCi_Ci _].
        (* Need K(M) x -> C_i x *)
        assert (Included X (K_lambda l0 (Meet_Contexts l0 Coll_Ctx)) (K_lambda l0 C_i)) as H_incl.
        { apply A3_Monotonicity_in_A.
          intros y Hy_M.
          apply Hy_M; exact HC_i. }
        assert (K_lambda l0 C_i x) by (apply H_incl; exact Hx_KM).
        apply (H_KCi_Ci x) in H; assumption.
      + (* M ⊆ K(M) *)
        intros x Hx_M.
        apply (A1_Extensivity l0 (Meet_Contexts l0 Coll_Ctx)); exact Hx_M.
    }
    split; [exact H_meet_ctx|].
    split.
    + (* Meet is lower bound *)
      intros C HC x Hx_M.
      apply Hx_M; exact HC.
    + (* Meet is greatest lower bound *)
      intros T H_T_ctx H_T_lb x Hx_T C HC.
      apply (H_T_lb C HC x Hx_T).
  (* Supremum *)
  - exists (Join_Contexts l0 Coll_Ctx).
    assert (Contexts l0 (Join_Contexts l0 Coll_Ctx)) as H_join_ctx.
    { unfold Contexts, Join_Contexts.
      apply (A2_Idempotence l0 (BigUnion Coll_Ctx)). }
    split; [exact H_join_ctx|].
    split.
    + (* Join is upper bound *)
      intros C HC x Hx_C.
      unfold Join_Contexts.
      apply (A1_Extensivity l0). exists C. split; assumption.
    + (* Join is least upper bound *)
      intros T H_T_ctx H_T_ub x Hx_join.
      (* inclusion BigUnion ⊆ T *)
      assert (Included X (BigUnion Coll_Ctx) T) as H_BigUnion_T.
      {
        intros y [C [HC Hy_C]].
        apply (H_T_ub C HC y Hy_C).
      }
      assert (Included X (K_lambda l0 (BigUnion Coll_Ctx)) (K_lambda l0 T)) as H_Kincl.
      { apply A3_Monotonicity_in_A; exact H_BigUnion_T. }
      assert (H_KT : K_lambda l0 T x) by (apply H_Kincl; exact Hx_join).
      destruct H_T_ctx as [H_KT_T _].
      apply (H_KT_T x); exact H_KT.
  Qed.
  
  Theorem P2_Directed_Convergence :
    forall (A : Powerset X) (D : Ensemble Lambda) (lambda_star : Lambda),
    IsDirected D ->
    lambda_star = supremum D ->
    (* Part 1: The net (K_op lambda A) for lambda in D is increasing *)
   (forall l1 l2 : Lambda, D l1 -> D l2 -> l1 <= l2 -> Included X (K_lambda l1 A) (K_lambda l2 A)) /\
    (* Part 2: The union of (K_op lambda A) for lambda in D equals K_op lambda_star A *)
   (Same_set X (K_lambda lambda_star A) (Union_indexed D (fun l' => K_lambda l' A))).
  Proof.
    intros A D lambda_star.
    intros H_D_directed H_lambda_star_is_supremum.
    split.
    {
      intros l1 l2 H_l1_in_D H_l2_in_D H_l1_le_l2.
      apply (P1_Monotonicity_in_lambda A l1 l2 H_l1_le_l2).
    }
    {
      apply (A4_Scott_Continuity_in_lambda A D lambda_star H_D_directed H_lambda_star_is_supremum).
    }
  Qed.
  
  
  Lemma IsDirected_Full_set :
    IsDirected (Full_set Lambda).
  Proof.
    unfold IsDirected.
    split.
    - 
      destruct (Lambda_non_empty) as [l].
      exists l.
      apply Full_intro.
    - 
      intros l1 l2 Hl1 Hl2.
      destruct (A5_Lambda_directed l1 l2) as [u [Hu1 Hu2]].
      exists u. split.
      + 
        apply Full_intro.
      + 
        split; assumption.
  Qed.

  Theorem P3_Plateau_Criterion
          (A : Powerset X) (lambda0 : Lambda) :
    (forall l : Lambda, lambda0 <= l ->
                        Same_set X (K_lambda l A) (K_lambda lambda0 A)) ->
    Same_set X (K_lambda lambda0 A)
              (K_lambda (supremum (Full_set Lambda)) A).
  Proof.
    intros H_plateau.
    set (lambda_star := supremum (Full_set Lambda)).
    have Hle : lambda0 <= lambda_star.
    { pose proof
        (supremum_is_least_upper_bound
           (Full_set Lambda) IsDirected_Full_set) as [Hub _].
      specialize (Hub lambda0).
      apply Hub.
      apply Full_intro. }
    specialize (H_plateau lambda_star Hle) as Heq.
     destruct Heq as [Hstar_to_0 H0_to_star].
    split; [exact H0_to_star | exact Hstar_to_0].
  Qed.
  
  Lemma IsDirected_budgets_above (l0 : Lambda) :
    IsDirected (fun l => l0 <= l).
  Proof.
    unfold IsDirected.
    split.
    - 
      exists l0.
      apply le_Lambda_refl.
    - 
      intros l1 l2 H_l0_le_l1 H_l0_le_l2.
      destruct (A5_Lambda_directed l1 l2) as [u [H_l1_le_u H_l2_le_u]].
      exists u; split.
    + 
      apply le_Lambda_trans with l1; assumption.
    + 
      split; assumption.
  Qed.
  
  Theorem P3_Plateau_Criterion_General
      (A : Powerset X) (lambda0 : Lambda) :
    (forall l : Lambda, lambda0 <= l ->
      Same_set X (K_lambda l A) (K_lambda lambda0 A)) ->
      Same_set X (K_lambda (supremum (fun l => lambda0 <= l)) A) (K_lambda lambda0 A).
  Proof.
    intros H_plateau.
    set (D := fun l : Lambda => lambda0 <= l).
    set (lambda_star := supremum D).
    have H_scott : Same_set X (K_lambda lambda_star A)
                           (Union_indexed D (fun l' => K_lambda l' A)).
    { apply (A4_Scott_Continuity_in_lambda A D lambda_star).
      - apply IsDirected_budgets_above.
      - reflexivity. }
    have H_union_eq : Same_set X (Union_indexed D (fun l' => K_lambda l' A))
                              (K_lambda lambda0 A).
    {
      split.
      - 
        intros x Hx_in_union.
        unfold Union_indexed in Hx_in_union.
        destruct Hx_in_union as [l [Hl_in_D Hx_in_KlA]].
        specialize (H_plateau l Hl_in_D) as H_same.
        unfold Same_set in H_same.
        destruct H_same as [H_incl_fwd _].
        apply H_incl_fwd.
        exact Hx_in_KlA.
      - 
        intros x Hx_in_Kl0A.
        unfold Union_indexed.
        exists lambda0.
        split.
        + 
          apply le_Lambda_refl.
        + 
          exact Hx_in_Kl0A.
    }
    split.
    - 
      intros x Hx_in_star.
      assert (Hx_in_union : Union_indexed D (K_op^~ A) x).
      {
        apply (proj1 H_scott).
        exact Hx_in_star.
      }
      apply (proj1 H_union_eq).
      exact Hx_in_union.
    -
      intros x Hx_in_l0.
      assert (Hx_in_union : Union_indexed D (K_op^~ A) x).
      {
        apply (proj2 H_union_eq).
        exact Hx_in_l0.
      }
      apply (proj2 H_scott).
      exact Hx_in_union.
  Qed.

  
End BUDGET_INDEXED_CLOSURE_OPERATORS.

(*===========================================================================*)
(* Section 4: Canonical Construction via Lower Closures                    *)
(*===========================================================================*)

Module CANONICAL_CONSTRUCTION_VIA_LOWER_CLOSURES (S : SETTING).

  Import S.
  Module BICO_local := BUDGET_INDEXED_CLOSURE_OPERATORS S.
  Import BICO_local.

  Parameter RawAchievable : Lambda -> Powerset X.

  Axiom S1_Monotonicity :
    forall l1 l2 : Lambda, l1 <= l2 ->
      Included X (RawAchievable l1) (RawAchievable l2).

  Axiom S2_Scott_Continuity :
    forall (D : Ensemble Lambda) (lambda_star : Lambda),
      IsDirected D ->
      lambda_star = supremum D ->
      Same_set X (RawAchievable lambda_star)
                 (Union_indexed D RawAchievable).

  Definition GuaranteedRegion (l : Lambda) : Powerset X :=
    lower_closure (RawAchievable l).
    
  Lemma lc_monotone : forall (A B : Powerset X),
    Included X A B -> Included X (lower_closure A) (lower_closure B).
  Proof.
    intros A B H_A_incl_B.
    unfold Included; intros x Hx_lcA.
    unfold lower_closure in Hx_lcA.
    destruct Hx_lcA as [a [Ha H_x_le_a]].
    unfold lower_closure.
    exists a. split.
    -
      apply H_A_incl_B; assumption.
    - assumption.
  Qed.
  
  Lemma lc_distributes_over_Union_indexed :
    forall (idx_set : Ensemble Lambda) (fam : Lambda -> Powerset X),
      Same_set X (lower_closure (Union_indexed idx_set fam))
                 (Union_indexed idx_set (fun l => lower_closure (fam l))).
  Proof.
    intros idx_set fam.
    unfold Same_set, Included; split.
    - intros x Hx_lc_union.
      unfold lower_closure in Hx_lc_union.
      destruct Hx_lc_union as [s_val [H_union_s H_x_le_s]].
      unfold Union_indexed in H_union_s.
      destruct H_union_s as [l_val [H_idx_set_l H_fam_l_s]].
      unfold Union_indexed.
      exists l_val. split.
      + exact H_idx_set_l.
      + 
        unfold lower_closure.
        exists s_val. split; assumption.
    - intros x Hx_union_lc.
      unfold Union_indexed in Hx_union_lc.
      destruct Hx_union_lc as [l_val [H_idx_set_l H_lc_fam_l_x]].
      unfold lower_closure in H_lc_fam_l_x.
      destruct H_lc_fam_l_x as [s_val [H_fam_l_s H_x_le_s]].
      unfold lower_closure.
      exists s_val. split.
      + 
        unfold Union_indexed.
        exists l_val. split; assumption.
      + assumption.
  Qed.
  
  Theorem GuaranteedRegion_is_monotone_and_Scott_continuous :
    (* Property 1: Monotonicity *)
    (forall l1 l2 : Lambda, l1 <= l2 ->
      Included X (GuaranteedRegion l1) (GuaranteedRegion l2))
    /\
    (* Property 2: Scott-continuity *)
    (forall (D_idx : Ensemble Lambda) (lambda_s : Lambda),
      IsDirected D_idx ->
      lambda_s = supremum D_idx ->
      Same_set X (GuaranteedRegion lambda_s) (Union_indexed D_idx GuaranteedRegion)).
  Proof.
    split.
    - intros l1 l2 Hle.
      unfold GuaranteedRegion.
      apply lc_monotone.
      apply S1_Monotonicity; exact Hle.
    - intros D_idx lambda_s Hdir Hsup.
      unfold GuaranteedRegion.
      pose proof
        (S2_Scott_Continuity D_idx lambda_s Hdir Hsup)
          as [Hraw₁ Hraw₂].
      assert (Hlc_eq :
        Same_set X (lower_closure (RawAchievable lambda_s))
                     (lower_closure (Union_indexed D_idx RawAchievable))).
      { split; [apply lc_monotone|apply lc_monotone]; assumption. }
      pose proof
        (lc_distributes_over_Union_indexed D_idx RawAchievable)
          as [Hdist₁ Hdist₂].
      split.
      + 
        intros x Hx.
        apply Hdist₁.
        apply (proj1 Hlc_eq).
        exact Hx.
      + 
        intros x Hx.
        apply (proj2 Hlc_eq).
        apply Hdist₂.
        exact Hx.
  Qed.


End CANONICAL_CONSTRUCTION_VIA_LOWER_CLOSURES.

Module CANONICAL_CONSTRUCTION (S : SETTING).
  Import S.
  Module BICO := BUDGET_INDEXED_CLOSURE_OPERATORS S.
  Import BICO.
  
  Parameter RawAchievable : Lambda -> Powerset X.
  Definition GuaranteedRegion (l : Lambda) : Powerset X :=
    lower_closure (RawAchievable l).
  Definition K_can (l : Lambda) (A : Powerset X) : Powerset X :=
    fun x : X => A x \/ GuaranteedRegion l x.
    
  (*===========================================================================*)
  (* Section 4.1: Fixed Points and Contexts in the Canonical Construction    *)
  (*===========================================================================*)

  Theorem K_can_is_fixed_point_iff_GuaranteedRegion_subset :
    forall (l : Lambda) (C : Powerset X),
      Same_set X (K_can l C) C <-> Included X (GuaranteedRegion l) C.
  Proof.
    intros l C.
    unfold K_can. (* K_can l C x is C x \/ GuaranteedRegion l x *)
    split.
    - (* Same_set (C \/ GR l) C -> GR l C= C *)
      intros H_same_set.
      unfold Same_set in H_same_set. destruct H_same_set as [H_union_subset_C _].
      intros x Hx_GR.
      apply H_union_subset_C.
      right; exact Hx_GR.
    - (* GR l C= C -> Same_set (C \/ GR l) C *)
      intros H_GR_subset_C.
      unfold Same_set. split.
      + (* (C \/ GR l) C= C *)
        intros x Hx_union.
        destruct Hx_union as [HxC | HxGR].
        * exact HxC.
        * apply H_GR_subset_C; exact HxGR.
      + (* C C= (C \/ GR l) *)
        intros x HxC.
        left; exact HxC.
  Qed.
  
  Definition Is_Lower_Set (A : Powerset X) : Prop :=
    forall x y : X, A y -> x <=_X y -> A x.

  Lemma lower_closure_is_Lower_Set : forall (M : Powerset X),
    Is_Lower_Set (lower_closure M).
  Proof.
    intros M; unfold Is_Lower_Set, lower_closure.
    intros x y Hex_a_My_yLEa HxLEy.
    destruct Hex_a_My_yLEa as [a [HMa HyLEa]].
    exists a; split.
    - exact HMa.
    - apply le_X_trans with y; assumption.
  Qed.
  
  Lemma GuaranteedRegion_is_Lower_Set : forall (l : Lambda),
    Is_Lower_Set (GuaranteedRegion l).
  Proof.
    intros l; unfold GuaranteedRegion. apply lower_closure_is_Lower_Set.
  Qed.

  Lemma Union_of_Lower_Sets_is_Lower_Set : forall (A B : Powerset X),
    Is_Lower_Set A -> Is_Lower_Set B -> Is_Lower_Set (fun x => A x \/ B x).
  Proof.
    intros A B H_A_ls H_B_ls; unfold Is_Lower_Set.
    intros x y H_union_y H_x_le_y.
    destruct H_union_y as [HyA | HyB].
    - left. apply H_A_ls with y; assumption.
    - right. apply H_B_ls with y; assumption.
  Qed.

  Lemma K_can_preserves_Lower_Sets : forall (l : Lambda) (A : Powerset X),
    Is_Lower_Set A -> Is_Lower_Set (K_can l A).
  Proof.
    intros l A H_A_ls; unfold K_can.
    apply Union_of_Lower_Sets_is_Lower_Set.
    - exact H_A_ls.
    - apply GuaranteedRegion_is_Lower_Set.
  Qed.

  (*===========================================================================*)
  (* Section 4.2: Pareto Frontier                                            *)
  (*===========================================================================*)

  Definition ParetoFrontier (l : Lambda) : Powerset X :=
    minimals (RawAchievable l).
    
  Section RA_props.
  Context
    (RA_monotone :
        forall l1 l2, l1 <= l2 ->
          Included X (RawAchievable l1) (RawAchievable l2))
    (RA_Scott :
        forall (D : Ensemble Lambda) (lambda_star : Lambda),
          IsDirected D ->
          lambda_star = supremum D ->
          Same_set X (RawAchievable lambda_star)
                     (BICO.Union_indexed D RawAchievable)).

  
  Lemma Kcan_A1_Extensivity :
    forall l (A : Powerset X), Included X A (K_can l A).
  Proof. intros l A x Hx. left; exact Hx. Qed.

  Lemma Kcan_A2_Idempotence :
    forall l (A : Powerset X),
      Same_set X (K_can l (K_can l A)) (K_can l A).
  Proof.
    intros l A; split; intros x H.
    - (* K (K A)  ⊆  K A *)
      destruct H as [[HA | HGR] | HGR]; (left + right); assumption.
    - (* K A ⊆ K (K A)          *)
      destruct H as [HA | HGR].
      + left; left; exact HA.
      + right; exact HGR.
  Qed.

  Lemma Kcan_A3_Monotone_in_A :
    forall l (A B : Powerset X),
      Included X A B -> Included X (K_can l A) (K_can l B).
  Proof.
    intros l A B Hsub x Hx; destruct Hx as [HA | HGR].
    - left; apply Hsub; exact HA.
    - right; exact HGR.
  Qed.
  
  
  Lemma Kcan_A4_Scott_in_lambda :
    forall (A : Powerset X) (D : Ensemble Lambda) (lambda_star : Lambda),
      IsDirected D ->
      lambda_star = supremum D ->
      Same_set X (K_can lambda_star A)
              (Union_indexed D (fun l' => K_can l' A)).
  Proof.
    intros A D lambda_star Hdir Hsup; split.

    (* ───────── left-to-right ───────── *)
    - pose proof Hdir as Hdir0.
      destruct Hdir as [[l0 Hl0D] Hlub].
      intros x Hx.
      destruct Hx as [HxA | [a [HaRaw Hle]]].
      + exists l0; split; [exact Hl0D | now left].
      + 
        pose proof (RA_Scott D lambda_star Hdir0 Hsup) as [Raw_to_union _].
        destruct (Raw_to_union _ HaRaw) as [l1 [Hl1D HaRaw_l1]].
        exists l1; split; [exact Hl1D |].
        right; exists a; split; [exact HaRaw_l1 | exact Hle].

  (* ───────── right-to-left ───────── *)
    - intros x [l [HlD HxKl]].
      destruct HxKl as [HxA | [a [HaRaw_l Hle]]].
      + now left.
      + 
        pose proof Hdir as Hdir0.
        pose proof (supremum_is_least_upper_bound D Hdir0) as [Hub _].
        assert (l <= lambda_star)
          by (rewrite Hsup; apply Hub; exact HlD).
        specialize (RA_monotone l lambda_star H) as Hmono.
        specialize (Hmono _ HaRaw_l) as HaRaw_star.
        right; exists a; split; [exact HaRaw_star | exact Hle].
  Qed.
  

  End RA_props.
  Section ZeroBudget.

  Variable zero : Lambda.

  Lemma K_zero_identity_iff_RawEmpty :
    (forall A : Powerset X, Same_set X (K_can zero A) A)
      <-> Same_set X (RawAchievable zero) (Empty_set X).
  Proof.
    split.
    - intros Hid.
      specialize (Hid (Empty_set X)).
      destruct Hid as [KsubsetE _EsubsetK].  

      split. 
      + 
        intros x HxRaw.
        assert (Hlc : GuaranteedRegion zero x).
        { exists x; split; [ exact HxRaw | apply le_X_refl ]. }
        assert (Hk : K_can zero (Empty_set X) x) by (right; exact Hlc).
        apply (KsubsetE _ Hk).
      + 
        intros x HxEmpty. inversion HxEmpty.
    - intros Hraw_empty A.
      destruct Hraw_empty as [RawToEmpty _EmptyToRaw].
      split; intros x H.
      + 
        destruct H as [HA | Hgr]; [ exact HA |].
        destruct Hgr as [a [HaRaw _]].
        specialize (RawToEmpty _ HaRaw). inversion RawToEmpty.
      + 
        left; exact H.
  Qed.

  End ZeroBudget.

(*===========================================================================*)
(* Section 4.2+ : Properties of the Pareto Frontier                         *)
(*===========================================================================*)

  Section ParetoProperties.

  Axiom has_minimals : forall A : Powerset X,
    (Inhabited X A) -> (Inhabited X (minimals A)).

  Theorem pareto_frontier_is_subset_of_raw_achievable :
    forall l, Included X (ParetoFrontier l) (RawAchievable l).
  Proof.
    intros l; unfold ParetoFrontier, minimals; intros x [H_RAx _].
    exact H_RAx.
  Qed.

  Definition upper_closure (A : Powerset X) : Powerset X :=
    fun x => exists a, A a /\ a <=_X x.

  Theorem upper_closure_of_pareto_equals_upper_closure_of_raw_achievable:
    forall l,
      (Inhabited X (RawAchievable l)) ->
      Same_set X (upper_closure (ParetoFrontier l)) (upper_closure (RawAchievable l)).
  Proof.
    intros l H_ra_nonempty.
    split.
    - 
      intros x Hx_uc_P.
      unfold upper_closure in *.
      destruct Hx_uc_P as [p [Hp_P Hp_le_x]].
      assert (RawAchievable l p) by (apply pareto_frontier_is_subset_of_raw_achievable; exact Hp_P).
      exists p; split; assumption.

    - 
      intros x Hx_uc_RA.
      unfold upper_closure in *.
      destruct Hx_uc_RA as [s [Hs_RA Hs_le_x]].
      set (BetterThan_s := fun s' => RawAchievable l s' /\ s' <=_X s).
      assert (H_BetterThan_s_nonempty : Inhabited X BetterThan_s)
        by (exists s; split; [exact Hs_RA | apply le_X_refl]).
      destruct (has_minimals BetterThan_s H_BetterThan_s_nonempty) as [p Hp_min_BetterThan_s].
      destruct Hp_min_BetterThan_s as [p_in_BetterThan_s p_is_minimal_in_BetterThan_s].
      destruct p_in_BetterThan_s as [Hp_RA Hp_le_s].
      assert (p_is_in_ParetoFrontier : ParetoFrontier l p).
      {
        unfold ParetoFrontier, minimals.
        split.
        + 
          exact Hp_RA.
        + 
          intros p' Hp'_RA Hp'_le_p.
          assert (p'_le_s : p' <=_X s) by (apply le_X_trans with p; [exact Hp'_le_p | exact Hp_le_s]).
          assert (p'_in_BetterThan_s : BetterThan_s p') by (unfold BetterThan_s; split; [exact Hp'_RA | exact p'_le_s]).
          apply p_is_minimal_in_BetterThan_s; assumption.
      }
      assert (p_le_x : p <=_X x) by (apply le_X_trans with s; [exact Hp_le_s | exact Hs_le_x]).
      exists p; split; [exact p_is_in_ParetoFrontier | exact p_le_x].
  Qed.

  End ParetoProperties.
  
  Section LowerSetRefinement.
  
    Example K_can_maps_lower_sets_to_lower_sets :
      forall (l : Lambda) (A : Powerset X),
      Is_Lower_Set A -> Is_Lower_Set (K_can l A).
    Proof.
      intros l A H_A_ls.
      apply K_can_preserves_Lower_Sets.
      exact H_A_ls.
    Qed.
    
    Context
      (RA_monotone :
       forall l1 l2, l1 <= l2 ->
         Included X (RawAchievable l1) (RawAchievable l2))
      (RA_Scott :
       forall (D : Ensemble Lambda) (lambda_star : Lambda),
         IsDirected D ->
         lambda_star = supremum D ->
         Same_set X (RawAchievable lambda_star)
           (BICO.Union_indexed D RawAchievable)).
    Example A3_Monotonicity_for_Lower_Sets :
      forall (l : Lambda) (A B : Powerset X),
      Is_Lower_Set A -> Is_Lower_Set B ->
      Included X A B -> Included X (K_can l A) (K_can l B).
    Proof.
      intros l A B _ _.
      apply Kcan_A3_Monotone_in_A; assumption.
    Qed.
    
    Theorem context_in_refined_model_is_lower_set :
      forall (l : Lambda) (C : Powerset X),
      Is_Lower_Set C -> (Same_set X (K_can l C) C) -> Is_Lower_Set C.
    Proof.
      intros l C H_C_is_lower H_C_is_fixed_point.
      assert (H_Kcan_is_LS : Is_Lower_Set (K_can l C)).
      { apply K_can_preserves_Lower_Sets; assumption. }
      unfold Is_Lower_Set.
      intros x y H_y_in_C H_x_le_y.
      apply (proj1 H_C_is_fixed_point).
      unfold Is_Lower_Set in H_Kcan_is_LS.
      apply (H_Kcan_is_LS x y).
      - 
        apply (proj2 H_C_is_fixed_point).
        exact H_y_in_C.
      -
        exact H_x_le_y.
    Qed.
  End LowerSetRefinement.

End CANONICAL_CONSTRUCTION.
