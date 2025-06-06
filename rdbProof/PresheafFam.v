Require Import Stdlib.Sets.Ensembles.
Require Import Stdlib.Init.Logic.
Require Import Stdlib.Logic.FunctionalExtensionality.
Require Import Stdlib.Logic.ProofIrrelevance.
Require Import ssreflect ssrfun ssrbool.
Require Import RDB.

Module Presheaf (S : SETTING).
  Import S.
  Module B := BUDGET_INDEXED_CLOSURE_OPERATORS S.
  Import B.

  Record ClosureOp := {
    clo_fun  : Ensemble X -> Ensemble X;
    clo_ext  : forall A, Included _ A (clo_fun A);
    clo_mono : forall A B, Included _ A B -> Included _ (clo_fun A) (clo_fun B);
    clo_idem : forall A, Same_set _ (clo_fun (clo_fun A)) (clo_fun A)
  }.

  Definition HomCL (K1 K2 : ClosureOp) : Prop :=
    forall A, Included _ (clo_fun K1 A) (clo_fun K2 A).

  Lemma HomCL_refl : forall K, HomCL K K.
  Proof. move=> K A x Hx; exact Hx. Qed.

  Lemma HomCL_trans : forall K1 K2 K3,
      HomCL K1 K2 -> HomCL K2 K3 -> HomCL K1 K3.
  Proof. move=> K1 K2 K3 H12 H23 A x Hx; apply: H23; apply: H12; exact: Hx. Qed.

  Lemma HomCL_antisym : forall K1 K2,
      HomCL K1 K2 -> HomCL K2 K1 -> K1 = K2.
  Proof.
    intros K1 K2 H12 H21.
    destruct K1 as [f1 e1 m1 d1].
    destruct K2 as [f2 e2 m2 d2].
    assert (Heq_fun : f1 = f2). {
      apply functional_extensionality; intro A.
      apply Extensionality_Ensembles; split.
      - apply (H12 A).
      - apply (H21 A).
      }
    subst f2.
    f_equal.
    - apply proof_irrelevance.
    - apply proof_irrelevance.
    - apply proof_irrelevance.
  Qed.

  Definition K_obj (l : Lambda) : ClosureOp :=
    Build_ClosureOp
      (fun A => K_op l A)
      (A1_Extensivity l)
      (fun A B HAB => A3_Monotonicity_in_A l A B HAB)
      (A2_Idempotence l).


  Lemma K_mor : forall l1 l2, le_Lambda l1 l2 -> HomCL (K_obj l1) (K_obj l2).
  Proof. move=> l1 l2 Hle A x Hx; apply: P1_Monotonicity_in_lambda; [exact: Hle | exact: Hx]. Qed.

  Lemma Kobj_extensible : forall (l : Lambda) (A : Ensemble X),
      Included _ A (clo_fun (K_obj l) A).
  Proof.
    move=> l A. simpl. apply A1_Extensivity.
  Qed.

  Lemma Kobj_mono_in_A : forall (l : Lambda) (A B : Ensemble X),
      Included _ A B -> Included _ (clo_fun (K_obj l) A) (clo_fun (K_obj l) B).
  Proof.
    move=> l A B HAB. simpl. apply A3_Monotonicity_in_A; assumption.
  Qed.

  Lemma Kobj_idempotent : forall (l : Lambda) (A : Ensemble X),
      Same_set _ (clo_fun (K_obj l) (clo_fun (K_obj l) A))
                 (clo_fun (K_obj l) A).
  Proof.
    move=> l A. simpl. apply A2_Idempotence.
  Qed.

  Lemma Kobj_is_closure_op : forall (l : Lambda), ClosureOp.
  Proof.
    move=> l. exact (K_obj l).
  Qed.

  Lemma Kobj_Scott_continuous :
    forall (A : Ensemble X) (D : Ensemble Lambda) (lambda_star : Lambda),
      IsDirected D ->
      lambda_star = supremum D ->
      Same_set X
        (clo_fun (K_obj lambda_star) A)
        (Union_indexed D (fun l' => clo_fun (K_obj l') A)).
  Proof.
    move=> A D lambda_star Hdir Hsup.
    simpl. apply: A4_Scott_Continuity_in_lambda; assumption.
  Qed.

End Presheaf.
