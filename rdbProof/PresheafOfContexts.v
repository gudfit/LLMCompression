(* PresheafofContexts.v *)

Require Import Stdlib.Sets.Ensembles.
Import Ensembles.
Require Import RDB.
Require Import Stdlib.Setoids.Setoid.

(*===========================================================================*)
(* Section 6: Contexts as a Presheaf                                         *)
(*===========================================================================*)

Module ContextPresheaf (S : SETTING).

  Import S.
  Module BICO := BUDGET_INDEXED_CLOSURE_OPERATORS S.
  Import BICO.
  Module CC := CANONICAL_CONSTRUCTION S.
  Import CC.

  Lemma lc_monotone : forall (A B : Powerset X),
    Included X A B -> Included X (lower_closure A) (lower_closure B).
  Proof.
    intros A B H_A_incl_B.
    unfold Included; intros x Hx_lcA.
    unfold lower_closure in Hx_lcA.
    destruct Hx_lcA as [a [Ha H_x_le_a]].
    unfold lower_closure.
    exists a; split.
    - apply H_A_incl_B; assumption.
    - assumption.
  Qed.

  Definition Ctx_can (l : Lambda) : Ensemble (Powerset X) :=
    fun (C : Powerset X) => Same_set X (K_can l C) C.
  
  Lemma ctx_can_iff_GR_subset :
    forall (l : Lambda) (C : Powerset X),
      Ctx_can l C <-> Included X (GuaranteedRegion l) C.
  Proof.
    exact K_can_is_fixed_point_iff_GuaranteedRegion_subset.
  Qed.

  Definition is_directed_collection (E : Ensemble (Powerset X)) : Prop :=
    (Inhabited (Powerset X) E) /\
    (forall C1 C2, E C1 -> E C2 ->
      exists C3, E C3 /\ Included X C1 C3 /\ Included X C2 C3).

  (*===========================================================================*)
  (* Section 6.2: Presheaf of Contexts                                         *)
  (*===========================================================================*)

  Section PresheafProperties.
    
    Context
      (RA_monotone :
        forall l1 l2, l1 <= l2 ->
          Included X (RawAchievable l1) (RawAchievable l2)).

    Lemma GuaranteedRegion_monotone :
      forall l1 l2 : Lambda, l1 <= l2 ->
        Included X (GuaranteedRegion l1) (GuaranteedRegion l2).
    Proof.
      intros l1 l2 Hle.
      unfold GuaranteedRegion.
      apply lc_monotone.
      apply RA_monotone; assumption.
    Qed.

    Theorem contexts_are_contravariant :
      forall l1 l2, l1 <= l2 ->
        Included (Powerset X) (Ctx_can l2) (Ctx_can l1).
    Proof.
      intros l1 l2 H_le.
      unfold Included; intros C H_C_in_Ctx2.
      apply (proj2 (ctx_can_iff_GR_subset l1 C)).
      assert (H_GR1_incl_GR2 : Included X (GuaranteedRegion l1) (GuaranteedRegion l2)).
      { apply GuaranteedRegion_monotone; assumption. }
      assert (H_GR2_incl_C : Included X (GuaranteedRegion l2) C).
      { apply (proj1 (ctx_can_iff_GR_subset l2 C)); assumption. }
      unfold Included.
      intros x Hx_in_GR1.
      apply H_GR2_incl_C.
      apply H_GR1_incl_GR2.
      exact Hx_in_GR1.
    Qed.


    Theorem inclusion_is_Scott_continuous :
      forall l1 l2 (E : Ensemble (Powerset X)),
        l1 <= l2 ->
        is_directed_collection E ->
        (forall C, E C -> Ctx_can l2 C) ->
        Same_set X (K_can l2 (BigUnion E)) (K_can l1 (BigUnion E)).
    Proof.
      intros l1 l2 E H_le H_E_directed H_E_in_Ctx2.
      unfold K_can.
      set (U := BigUnion E).
      split; intros x Hx.
      - destruct Hx as [Hx_U | Hx_GR2].
        + 
          left; assumption.
        + 
          assert (Included X (GuaranteedRegion l2) U).
          {
            intros y Hy_GR2.
            destruct H_E_directed as [H_inhab _].
            destruct H_inhab as [C0 HC0_E].
            specialize (H_E_in_Ctx2 C0 HC0_E).
            apply (proj1 (ctx_can_iff_GR_subset l2 C0)) in H_E_in_Ctx2.
            exists C0; split; [exact HC0_E | apply H_E_in_Ctx2; assumption].
          }
          left; apply H; assumption.
      - destruct Hx as [Hx_U | Hx_GR1].
        + 
          left; assumption.
        + 
          right.
          apply (GuaranteedRegion_monotone l1 l2 H_le).
          assumption.
    Qed.
    
    Context (RA_Scott :
      forall (D : Ensemble Lambda) (lambda_star : Lambda),
      IsDirected D ->
      lambda_star = supremum D ->
      Same_set X (RawAchievable lambda_star)
                 (Union_indexed D RawAchievable)).
    
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
        exists l_val; split.
        + exact H_idx_set_l.
        + unfold lower_closure; exists s_val; split; assumption.
      - intros x Hx_union_lc.
        unfold Union_indexed in Hx_union_lc.
        destruct Hx_union_lc as [l_val [H_idx_set_l H_lc_fam_l_x]].
        unfold lower_closure in H_lc_fam_l_x.
         destruct H_lc_fam_l_x as [s_val [H_fam_l_s H_x_le_s]].
        unfold lower_closure; exists s_val; split.
        + unfold Union_indexed; exists l_val; split; assumption.
        + assumption.
    Qed.
    
    Lemma GuaranteedRegion_Scott_continuous :
      forall (D_idx : Ensemble Lambda) (lambda_s : Lambda),
        IsDirected D_idx ->
        lambda_s = supremum D_idx ->
        Same_set X (GuaranteedRegion lambda_s) (Union_indexed D_idx GuaranteedRegion).
    Proof.
      intros D_idx lambda_s Hdir Hsup.
      unfold GuaranteedRegion.
      split.
      - 
        pose proof (proj1 (RA_Scott D_idx lambda_s Hdir Hsup)) as H_RA_incl_fwd.
        pose proof (lc_monotone _ _ H_RA_incl_fwd) as H_mono_fwd.
        pose proof (proj1 (lc_distributes_over_Union_indexed D_idx RawAchievable)) as H_dist_fwd.
        unfold Included in *. intros x Hx.
        apply H_dist_fwd.
        apply H_mono_fwd.
        exact Hx.
      - 
        pose proof (proj2 (RA_Scott D_idx lambda_s Hdir Hsup)) as H_RA_incl_bwd.
        pose proof (lc_monotone _ _ H_RA_incl_bwd) as H_mono_bwd.
        pose proof (proj2 (lc_distributes_over_Union_indexed D_idx RawAchievable)) as H_dist_bwd.
        unfold Included in *. intros x Hx.
        apply H_mono_bwd.
        apply H_dist_bwd.
        exact Hx.
    Qed.
    
    Definition Intersection_of_Contexts (D : Ensemble Lambda) : Ensemble (Powerset X) :=
      fun C => forall l, D l -> Ctx_can l C.
    
    Theorem contexts_map_sup_to_inf :
      forall (D : Ensemble Lambda) (lambda_star : Lambda),
       IsDirected D ->
        lambda_star = supremum D ->
        Same_set (Powerset X)
        (Ctx_can lambda_star)
        (Intersection_of_Contexts D).
    Proof.
      intros D lambda_star H_D_directed H_sup.
      unfold Ctx_can, Intersection_of_Contexts.
      split; intros C H_C_prop.
      - 
        intros l H_l_in_D.
        apply (proj2 (ctx_can_iff_GR_subset l C)).
        assert (H_GR_star_incl_C : Included X (GuaranteedRegion lambda_star) C)
          by exact (proj1 (ctx_can_iff_GR_subset lambda_star C) H_C_prop).
        assert (l <= lambda_star)
          by (rewrite H_sup; apply (proj1 (supremum_is_least_upper_bound D H_D_directed)); assumption).
        assert (H_GR_l_incl_star : Included X (GuaranteedRegion l) (GuaranteedRegion lambda_star))
          by (apply GuaranteedRegion_monotone; assumption).
        unfold Included in *; intros x Hx.
        apply H_GR_star_incl_C, H_GR_l_incl_star, Hx.
      - 
        apply (proj2 (ctx_can_iff_GR_subset lambda_star C)).
        intros x Hx_in_GR_star.
        pose proof (proj1 (GuaranteedRegion_Scott_continuous D lambda_star H_D_directed H_sup)) as H_scott_incl.
        destruct (H_scott_incl _ Hx_in_GR_star) as [l [HlD HxGRL]].
        specialize (H_C_prop l HlD).
        pose proof (proj1 (ctx_can_iff_GR_subset l C) H_C_prop) as H_GRL_incl_C.
        apply H_GRL_incl_C; assumption.
    Qed.
    
  End PresheafProperties.

End ContextPresheaf.