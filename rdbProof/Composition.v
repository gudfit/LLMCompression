(* Composition.v *)

Require Import Stdlib.Sets.Ensembles.
Import Ensembles.
From Top Require Import RDB.
Require Import Stdlib.Logic.Classical_Prop.
From Stdlib Require Import ssreflect ssrfun ssrbool.

(*===========================================================================*)
(* Section 6.3: On Composing Budget Layers                                   *)
(*===========================================================================*)

Module Composition (S : SETTING).

  Import S.

  Section CompositionSection.

    Context
      (Lambda1 : Type)
      (le_L1 : Lambda1 -> Lambda1 -> Prop)
      (L1_axioms : inhabited Lambda1 /\ (forall x, le_L1 x x) /\ (forall x y, le_L1 x y -> le_L1 y x -> x = y) /\ (forall x y z, le_L1 x y -> le_L1 y z -> le_L1 x z))
      (K_op1 : Lambda1 -> (Powerset X -> Powerset X))
      (K1_axioms : (forall l A, Included X A (K_op1 l A)) /\ (forall l A, Same_set X (K_op1 l (K_op1 l A)) (K_op1 l A)) /\ (forall l A B, Included X A B -> Included X (K_op1 l A) (K_op1 l B)))
      
      (Lambda2 : Type)
      (le_L2 : Lambda2 -> Lambda2 -> Prop)
      (L2_axioms : inhabited Lambda2 /\ (forall x, le_L2 x x) /\ (forall x y, le_L2 x y -> le_L2 y x -> x = y) /\ (forall x y z, le_L2 x y -> le_L2 y z -> le_L2 x z))
      (K_op2 : Lambda2 -> (Powerset X -> Powerset X))
      (K2_axioms : (forall l A, Included X A (K_op2 l A)) /\ (forall l A, Same_set X (K_op2 l (K_op2 l A)) (K_op2 l A)) /\ (forall l A B, Included X A B -> Included X (K_op2 l A) (K_op2 l B))).

    Definition F (l1 : Lambda1) (l2 : Lambda2) (A : Powerset X) : Powerset X :=
      K_op2 l2 (K_op1 l1 A).

    Lemma F_extensive : forall l1 l2 A, Included X A (F l1 l2 A).
    Proof.
      intros l1 l2 A.
      unfold F.
      destruct K1_axioms as [K1_ext_hyp _K1_rest].
      destruct K2_axioms as [K2_ext_hyp _K2_rest].
      intros x Hx_in_A.
      apply (K2_ext_hyp l2 (K_op1 l1 A)). 
      apply (K1_ext_hyp l1 A).
      exact Hx_in_A.
    Qed.


    Lemma F_monotone : forall l1 l2 A B,
      Included X A B -> Included X (F l1 l2 A) (F l1 l2 B).
    Proof.
      intros l1 l2 A B H_incl.
      unfold F.
      destruct K1_axioms as [_ [_ K1_mono]], K2_axioms as [_ [_ K2_mono]].
      apply K2_mono, K1_mono, H_incl.
    Qed.
    
    Definition F_closed (l1 : Lambda1) (l2 : Lambda2) (C : Powerset X) : Prop :=
      Included X (F l1 l2 C) C.

    Definition K_comp (l1 : Lambda1) (l2 : Lambda2) (A : Powerset X) : Powerset X :=
      fun x => forall C, (Included X A C /\ F_closed l1 l2 C) -> C x.

    Theorem K_comp_is_extensive : forall l1 l2 A, Included X A (K_comp l1 l2 A).
    Proof.
      intros l1 l2 A x HxA C [HAC HFC].
      apply HAC; assumption.
    Qed.

    Theorem K_comp_is_monotone : forall l1 l2 A B,
      Included X A B -> Included X (K_comp l1 l2 A) (K_comp l1 l2 B).
    Proof.
      intros l1 l2 A B H_A_incl_B.
      unfold Included.
      intros x Hx_in_KA.
      unfold K_comp in *.
      intros C_prime H_BCprime_and_FCprime.
      destruct H_BCprime_and_FCprime as [H_B_incl_Cprime H_FCprime].
      apply Hx_in_KA.
      split.
      - 
        unfold Included.
        intros y Hy_in_A.
        apply H_B_incl_Cprime.
        apply H_A_incl_B.
        exact Hy_in_A.
      - 
        exact H_FCprime.
    Qed.


    Theorem K_comp_is_idempotent : forall l1 l2 A,
      Same_set X (K_comp l1 l2 (K_comp l1 l2 A)) (K_comp l1 l2 A).
    Proof.
      intros l1 l2 A.
      set (KA := K_comp l1 l2 A).
      set (KKA := K_comp l1 l2 KA). 
      split.
      - 
        unfold Included; intros x Hx_in_KKA.
        assert (H_KA_is_F_closed : F_closed l1 l2 KA).
        {
          unfold F_closed.
          unfold Included; intros y Hy_in_F_KA.
          intros C_spec [H_A_incl_C_spec H_C_spec_is_F_closed].
          assert (H_KA_incl_C_spec : Included X KA C_spec).
          {
            unfold Included; intros z Hz_in_KA.
            unfold K_comp in Hz_in_KA.
            apply (Hz_in_KA C_spec). 
            split; assumption.
          }
          assert (Hy_in_F_C_spec : F l1 l2 C_spec y).
          {
            apply (F_monotone l1 l2 KA C_spec H_KA_incl_C_spec).
            exact Hy_in_F_KA.
          }
          apply H_C_spec_is_F_closed.
          exact Hy_in_F_C_spec.
        }
        unfold K_comp in Hx_in_KKA.
        apply (Hx_in_KKA KA).
        split.
        + 
          unfold Included; intros z Hz_in_KA_for_refl; exact Hz_in_KA_for_refl.
        + 
          exact H_KA_is_F_closed.
      - 
        apply (K_comp_is_extensive l1 l2 KA).
    Qed.

    (* ------------------------------------------------------------------------- *)
    (* Section: Scott Continuity in the Set Argument A                           *)
    (* ------------------------------------------------------------------------- *)

    Definition IsDirected_Sets (mathcalA : Ensemble (Powerset X)) : Prop :=
      (Inhabited (Powerset X) mathcalA) /\
      (forall A1 A2 : Powerset X, mathcalA A1 -> mathcalA A2 ->
        exists A_ub : Powerset X, mathcalA A_ub /\ Included X A1 A_ub /\ Included X A2 A_ub).

    Definition Union_over_sets (mathcalA : Ensemble (Powerset X)) (k_op : Powerset X -> Powerset X) : Powerset X :=
      fun x => exists S, mathcalA S /\ (k_op S x).
    
    Definition BigUnion_sets (mathcalA : Ensemble (Powerset X)) : Powerset X :=
      fun x : X => exists S : Powerset X, mathcalA S /\ S x.
      
    Context
      (K_op1_Scott_cont_A :
         forall l1 (mathcalA : Ensemble (Powerset X)),
           IsDirected_Sets mathcalA ->
           Same_set X (K_op1 l1 (BigUnion_sets mathcalA))
                       (Union_over_sets mathcalA (K_op1 l1)))
      (K_op2_Scott_cont_A :
         forall l2 (mathcalA : Ensemble (Powerset X)),
           IsDirected_Sets mathcalA ->
           Same_set X (K_op2 l2 (BigUnion_sets mathcalA))
                       (Union_over_sets mathcalA (K_op2 l2))).

    Lemma image_of_directed_is_directed :
      forall (k_op : Powerset X -> Powerset X)
             (k_mono : forall A B, Included X A B -> Included X (k_op A) (k_op B))
             (mathcalA : Ensemble (Powerset X)) (H_dir_A : IsDirected_Sets mathcalA),
      IsDirected_Sets (fun S_img => exists S_orig, mathcalA S_orig /\ S_img = k_op S_orig).
    Proof.
      intros k_op k_mono mathcalA H_dir_A.
      destruct H_dir_A as [H_inhab_A H_bounds_A].
      set (mathcal_img S_img := exists S_orig, mathcalA S_orig /\ S_img = k_op S_orig).
      split.
      - 
        destruct H_inhab_A as [S0 HS0A].
        exists (k_op S0). exists S0. split; [exact HS0A | reflexivity].
      - 
        intros K_S1 K_S2 HK_S1 HK_S2.
        destruct HK_S1 as [S1 [HS1A Heq_K_S1]]. subst K_S1.
        destruct HK_S2 as [S2 [HS2A Heq_K_S2]]. subst K_S2.
        destruct (H_bounds_A S1 S2 HS1A HS2A) as [S_ub [HS_ubA [Hincl_S1_Sub Hincl_S2_Sub]]].
        exists (k_op S_ub).
        split.
        + 
          exists S_ub. split; [exact HS_ubA | reflexivity].
        + split.
          * 
            apply k_mono; assumption.
          * 
            apply k_mono; assumption.
    Qed.

    Theorem F_is_Scott_continuous_in_A :
      forall l1 l2 (mathcalA : Ensemble (Powerset X)),
        IsDirected_Sets mathcalA ->
        Same_set X (F l1 l2 (BigUnion_sets mathcalA))
                     (Union_over_sets mathcalA (F l1 l2)).
    Proof.
      intros l1 l2 mathcalA Hdir.
      unfold F.
      split.
      - 
        intros x Hx_in_LHS.
        assert (H_K1_scott_incl :
              Included X (K_op1 l1 (BigUnion_sets mathcalA))
                       (Union_over_sets mathcalA (K_op1 l1))).
        { apply (proj1 (K_op1_Scott_cont_A l1 mathcalA Hdir)). }
        destruct K2_axioms as [_ [_ K2_mono]].
        apply (K2_mono l2 _ _ H_K1_scott_incl) in Hx_in_LHS.
        set (mathcalB S_img := exists S_orig, mathcalA S_orig /\ S_img = K_op1 l1 S_orig).
        
        have H_union_is_bigunion : Same_set X (Union_over_sets mathcalA (K_op1 l1)) (BigUnion_sets mathcalB).
        {
          split; intros y Hy.
          - 
            destruct Hy as [S [HSA HyK1S]].
            exists (K_op1 l1 S); split; [| exact HyK1S].
            exists S; split; [exact HSA | reflexivity].
          - 
            destruct Hy as [S_img [H_S_img_in_B HyS_img]].
            destruct H_S_img_in_B as [S [HSA Heq]]. subst S_img.
            exists S; split; [exact HSA | exact HyS_img] .
        }
        apply (K2_mono l2 _ _ (proj1 H_union_is_bigunion)) in Hx_in_LHS.
        have Hdir_B : IsDirected_Sets mathcalB.
        { 
          apply image_of_directed_is_directed.
          - intros A B H_incl. destruct K1_axioms as [_ [_ K1_mono]]. apply K1_mono; assumption.
          - exact Hdir.
        }
        apply (proj1 (K_op2_Scott_cont_A l2 mathcalB Hdir_B)) in Hx_in_LHS.

        unfold Union_over_sets in Hx_in_LHS.
        destruct Hx_in_LHS as [S_img [H_S_img_in_B Hx_K2_S_img]].
        unfold mathcalB in H_S_img_in_B.
        destruct H_S_img_in_B as [S [HSA Heq]]. subst S_img.
        
        unfold Union_over_sets.
        exists S; split; [exact HSA |].
        unfold F. exact Hx_K2_S_img.

      - 
        intros x Hx_in_RHS.
        unfold Union_over_sets in Hx_in_RHS.
        destruct Hx_in_RHS as [S [HSA HxFS]].
        have H_S_incl_BigU : Included X S (BigUnion_sets mathcalA).
        { intros y HyS. exists S; split; [exact HSA | exact HyS]. }
        apply (F_monotone l1 l2 S (BigUnion_sets mathcalA) H_S_incl_BigU).
        exact HxFS.
    Qed.
  End CompositionSection.



(*===========================================================================*)
(* Section 6.3b: Simple Composition for the Canonical Case                 *)
(*===========================================================================*)

  Section CanonicalCase.

    Context
      (GR1 : Powerset X)
      (GR2 : Powerset X).

    Definition K_can1 (A : Powerset X) : Powerset X := fun x => A x \/ GR1 x.
    Definition K_can2 (A : Powerset X) : Powerset X := fun x => A x \/ GR2 x.
    Definition F_can (A : Powerset X) : Powerset X := K_can2 (K_can1 A).

    Lemma canonical_composition_is_simple : forall (A : Powerset X),
      Same_set X (F_can A) (fun x => A x \/ GR1 x \/ GR2 x).
    Proof.
      intros A.
      unfold F_can, K_can1, K_can2.
      unfold Same_set.
      split.
      -
        unfold Included, In.
        intros x H.
        tauto.
      -
        unfold Included, In.
        intros x H.
        tauto.
    Qed.

    Theorem canonical_composition_is_idempotent : forall (A : Powerset X),
      Same_set X (F_can (F_can A)) (F_can A).
    Proof.
      intros A.
      unfold F_can, K_can1, K_can2.
      unfold Same_set, Included, In.
      split.
      - 
        intros x H.
        tauto.
      -
        intros x H.
        tauto.
    Qed.
  End CanonicalCase.


End Composition.
