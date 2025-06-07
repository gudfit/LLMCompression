(* Composition.v *)

Require Import Stdlib.Sets.Ensembles.
Import Ensembles.
Require Import RDB.

(*===========================================================================*)
(* Section 6.3: On Composing Budget Layers                                   *)
(*===========================================================================*)

Module Composition (S : SETTING).

  Import S.

  Section CompositionSection.

    Context
      (* System 1 *)
      (Lambda1 : Type)
      (le_L1 : Lambda1 -> Lambda1 -> Prop)
      (L1_axioms : inhabited Lambda1 /\ (forall x, le_L1 x x) /\ (forall x y, le_L1 x y -> le_L1 y x -> x = y) /\ (forall x y z, le_L1 x y -> le_L1 y z -> le_L1 x z))
      (K_op1 : Lambda1 -> (Powerset X -> Powerset X))
      (K1_axioms : (forall l A, Included X A (K_op1 l A)) /\ (forall l A, Same_set X (K_op1 l (K_op1 l A)) (K_op1 l A)) /\ (forall l A B, Included X A B -> Included X (K_op1 l A) (K_op1 l B)))
      
      (* System 2 *)
      (Lambda2 : Type)
      (le_L2 : Lambda2 -> Lambda2 -> Prop)
      (L2_axioms : inhabited Lambda2 /\ (forall x, le_L2 x x) /\ (forall x y, le_L2 x y -> le_L2 y x -> x = y) /\ (forall x y z, le_L2 x y -> le_L2 y z -> le_L2 x z))
      (K_op2 : Lambda2 -> (Powerset X -> Powerset X))
      (K2_axioms : (forall l A, Included X A (K_op2 l A)) /\ (forall l A, Same_set X (K_op2 l (K_op2 l A)) (K_op2 l A)) /\ (forall l A B, Included X A B -> Included X (K_op2 l A) (K_op2 l B))).

    (* All subsequent definitions and theorems go inside this section. *)

    Definition F (l1 : Lambda1) (l2 : Lambda2) (A : Powerset X) : Powerset X :=
      K_op2 l2 (K_op1 l1 A).

    Lemma F_extensive : forall l1 l2 A, Included X A (F l1 l2 A).
    Proof.
      intros l1 l2 A.
      unfold F.
      destruct K1_axioms as [K1_ext _], K2_axioms as [K2_ext _].
      unfold Included; intros x HxA.
      apply K2_ext.
      apply K1_ext.
      exact HxA.
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
      intros l1 l2 A B H_A_incl_B x Hx_in_KA.
      unfold K_comp in *.
      intros C [HBC HFC].
      apply Hx_in_KA.
      split.
      - 
        unfold Included; intros y HyA.
        apply HBC.
        apply H_A_incl_B.
        exact HyA.
      - 
        exact HFC.
    Qed.


    Theorem K_comp_is_idempotent : forall l1 l2 A,
      Same_set X (K_comp l1 l2 (K_comp l1 l2 A)) (K_comp l1 l2 A).
    Proof.
      intros l1 l2 A.
      set (KA := K_comp l1 l2 A).
      split.
      - 
        assert (H_KA_F_closed : F_closed l1 l2 KA).
        {
          unfold F_closed; intros x Hx_in_FKA.
          unfold K_comp, KA; intros C [H_A_incl_C H_C_F_closed].
          assert (H_KA_incl_C : Included X KA C) by (intros y Hy; apply Hy; split; assumption).
          apply H_C_F_closed; apply (F_monotone l1 l2 KA C H_KA_incl_C); assumption.
        }
        unfold Included; intros x Hx_in_KKA.
        unfold K_comp in Hx_in_KKA.
        specialize (Hx_in_KKA KA).
        apply Hx_in_KKA.
        split.
        + 
          unfold Included; intros y Hy; exact Hy.
        + 
          exact H_KA_F_closed.
      - 
        exact (K_comp_is_extensive l1 l2 KA).
    Qed.
  End CompositionSection.

End Composition.
