(* CatV.v *)

Require Import Stdlib.Sets.Ensembles.
Require Import Stdlib.Init.Logic.
Import Ensembles.

Module Type SET_THEORY_PRELIMINARIES.
  Parameter X : Type.
  Definition PowersetX := Ensemble X.

  Definition Union_indexed {I : Type}
           (idx_domain : Ensemble I) (set_fam : I -> PowersetX) : PowersetX :=
    fun x => exists i : I, idx_domain i /\ set_fam i x.

  Definition is_directed_family_of_sets {J : Type}
           (idx_domain : Ensemble J) (set_fam : J -> PowersetX) : Prop :=
    Inhabited J idx_domain /\
    (forall j₁ j₂, idx_domain j₁ -> idx_domain j₂ ->
      exists k, idx_domain k /\
              Included _ (set_fam j₁) (set_fam k) /\
              Included _ (set_fam j₂) (set_fam k)).
End SET_THEORY_PRELIMINARIES.



(* ---------- Section 1: closure operators ---------------------------------- *)

Module ClosureProperties (STP : SET_THEORY_PRELIMINARIES).
Import STP.

Record is_closure_operator (K : PowersetX -> PowersetX) : Prop := {
  clo_extensivity    : forall A, Included _ A (K A) ;
  clo_monotonicity_A : forall A B, Included _ A B -> Included _ (K A) (K B) ;
  clo_idempotence    : forall A, Same_set _ (K (K A)) (K A)
}.

Definition is_scott_continuous_set_arg (K : PowersetX -> PowersetX) : Prop :=
  forall (J : Type) (idx_domain : Ensemble J) (set_fam : J -> PowersetX),
    is_directed_family_of_sets idx_domain set_fam ->
    Same_set _
      (K (Union_indexed idx_domain set_fam))
      (Union_indexed idx_domain (fun j => K (set_fam j))).

End ClosureProperties.



(* ---------- Section 2: parameters for a directed family of operators ------ *)

Module Type OPERATOR_FAMILY_PARAMS (STP : SET_THEORY_PRELIMINARIES).
Import STP.
Module CP := ClosureProperties STP.  (* re-use the definitions above *)
Import CP.

  Parameter IndexSet : Type.

  Parameter K_family : IndexSet -> PowersetX -> PowersetX.

  Axiom H_K_is_closure_operator
        : forall i, is_closure_operator (K_family i).

  Axiom H_K_is_scott_continuous
        : forall i, is_scott_continuous_set_arg (K_family i).

  Parameter D_ens : Ensemble IndexSet.
  Axiom H_D_ens_is_inhabited : Inhabited IndexSet D_ens.

  Axiom H_K_family_is_directed :
    forall i j, D_ens i -> D_ens j ->
      exists k, D_ens k /\
        (forall A, Included _ (K_family i A) (K_family k A)) /\
        (forall A, Included _ (K_family j A) (K_family k A)).
End OPERATOR_FAMILY_PARAMS.



(* ---------- Section 3: supremum of a directed family of closure ops ------- *)

Module SupremumOfDirectedClosureOperators
       (STP  : SET_THEORY_PRELIMINARIES)
       (OF   : OPERATOR_FAMILY_PARAMS STP).
Import STP OF.
Module CP := ClosureProperties STP.  Import CP.

Definition K_sup (A : PowersetX) : PowersetX :=
  Union_indexed D_ens (fun i => K_family i A).


Lemma K_sup_extensive : forall A, Included _ A (K_sup A).
Proof.
  intros A x HxA.
  destruct H_D_ens_is_inhabited as [i Hi].
  unfold K_sup, Union_indexed.
  exists i; split.
  - exact Hi.
  - 
    destruct (H_K_is_closure_operator i) as [Hext _ _].
    apply Hext; exact HxA.
Qed.

Lemma K_sup_monotone : forall A B,
    Included _ A B -> Included _ (K_sup A) (K_sup B).
Proof.
  intros A B H_A_incl_B.
  intros x Hx_in_Ksup_A.
  unfold K_sup in Hx_in_Ksup_A.
  unfold Union_indexed in Hx_in_Ksup_A.
  destruct Hx_in_Ksup_A as [i [Hi_in_D H_x_in_KfiA]].
  unfold K_sup.
  unfold Union_indexed.
  exists i.
  split.
  - 
    exact Hi_in_D.
  - 
    destruct (H_K_is_closure_operator i) as [extensivity_i monotonicity_i idempotence_i].
    pose proof (monotonicity_i A B H_A_incl_B) as H_incl_KfiA_KfiB.
    apply H_incl_KfiA_KfiB.
    exact H_x_in_KfiA.
Qed.

Lemma KjA_directed A :
  is_directed_family_of_sets D_ens (fun j => K_family j A).
Proof.
  split.
  - (* Inhabited IndexSet D_ens *)
    exact H_D_ens_is_inhabited.
  - (* Directedness: for any i, j in D_ens, find k ≥ i, j *)
    intros i j Hi Hj.
    destruct (H_K_family_is_directed i j Hi Hj) as [k [Hk_in_D [Hle_i Hle_j]]].
    exists k.
    split.
    + (* k ∈ D_ens *)
      exact Hk_in_D.
    + split.
      * (* Included (K_family i A) (K_family k A) *)
        intros x Hx. apply (Hle_i A). exact Hx.
      * (* Included (K_family j A) (K_family k A) *)
        intros x Hx. apply (Hle_j A). exact Hx.
Qed.

Lemma K_sup_idempotent : forall A, Same_set _ (K_sup (K_sup A)) (K_sup A).
Proof.
  intros A. split.
  - 
    intros x Hx.
    unfold K_sup, Union_indexed in Hx.
    destruct Hx as [i [HiD Hx_i]].
    pose proof (H_K_is_scott_continuous i _
                  D_ens
                  (fun j => K_family j A)
                  (KjA_directed A))
      as Hsc_eq.
    destruct Hsc_eq as [Hsc_L2R _].
    specialize (Hsc_L2R x Hx_i).
    unfold Union_indexed in Hsc_L2R.
    destruct Hsc_L2R as [j [HjD Hx_ij]].
    destruct (H_K_family_is_directed i j HiD HjD) as [k [HkD [Hik Hjk]]].
    pose proof (Hik (K_family j A) x Hx_ij) as Hx_kj.
    destruct (H_K_is_closure_operator k) as [_ Kk_monotone Kk_idemp].
    pose proof (Kk_monotone _ _ (Hjk A)) as Hmono_step.
    specialize (Hmono_step x Hx_kj) as Hx_kkA.
    destruct (Kk_idemp A) as [Hk_idem _].
    specialize (Hk_idem _ Hx_kkA) as Hx_kA.
    unfold K_sup, Union_indexed.
    exists k; split; [ exact HkD | exact Hx_kA ].

  - 
    intros x Hx.
    apply (K_sup_extensive (K_sup A)); assumption.
Qed.

Theorem K_sup_is_closure_operator : is_closure_operator K_sup.
Proof.
  split.
  - apply K_sup_extensive.
  - apply K_sup_monotone.
  - apply K_sup_idempotent.
Qed.


End SupremumOfDirectedClosureOperators.

