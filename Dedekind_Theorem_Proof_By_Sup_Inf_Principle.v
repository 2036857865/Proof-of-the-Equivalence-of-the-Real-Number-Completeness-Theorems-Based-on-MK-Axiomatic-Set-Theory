(**********************************************************************)
(*     This is part of Real_Completeness, it is distributed under     *)
(*    the terms of the GNU Lesser General Public License version 3    *)
(*             (see file LICENSE for more details)                    *)
(*                                                                    *)
(*                     Copyright 2026-2031                            *)
(*              Ce Zhang, Guowei Dou and Wensheng Yu                  *)
(**********************************************************************)

(** Dedekind_Theorem_Proof_By_Sup_Inf_Principle *)

Require Export Sup_Inf_Principle.

Theorem Dedekind_Theorema : ∀ x y, divide x y -> ∃ e, e ∈ RC /\ Split x y e.
Proof.
  intros. destruct H, H0, H1, H2, H3. New H3. rename H5 into HR_Divide. 
  unfold R_Divide in H3. 
  assert (∃ u, Boundup_Ens x u).
  { apply NEexE in H2. destruct H2. exists (x0). red. repeat split; auto.
    intros. left. apply H4; auto. }
  apply SupremumT in H5; auto. destruct H5 as [e [H5]]. New H5. 
  rename H7 into HBoundup_Ens_x_e. unfold Boundup_Ens in H5. 
  destruct H5, H7; auto. exists e; split; auto; intros.
  red. split.
  - intros. destruct HR_Divide with a; auto. 
    assert (Boundup_Ens x a).
    { red; intros. repeat split; auto. intros. left. apply H4; auto. }
      apply H6 in H12. apply legRf in H12; auto. contradiction.
  - intros. destruct HR_Divide with a; auto. apply HBoundup_Ens_x_e in H11. 
    apply legRf in H11; auto. contradiction.
Qed.

(* unique *)
Theorem Dedekind_Theoremb : ∀ x y e1 e2, divide x y -> e1 ∈ RC -> e2 ∈ RC
  -> Split x y e1 -> Split x y e2 -> e1 = e2.
Proof.
  assert (∀ x y, divide x y -> ∀ e1 e2, e1 ∈ RC /\ Split x y e1
    -> e2 ∈ RC /\ Split x y e2 -> ~ e1 < e2).
  { intros. intro. destruct H0, H1. red in H3, H4; destruct H3, H4.
    assert(e1 < (e1 + e2) / (1 + 1) /\ (e1 + e2) / (1 + 1) < e2). 
    { apply aver2 in H2; auto. }
    destruct H7.
    apply H5 in H7; apply H4 in H8; auto.
    red in H. destruct H, H9, H10, H11, H12.
    pose proof (H13 _ _ H8 H7). apply xlx in H14; auto. }
  intros. assert(e1 = e2 \/ e1 > e2 \/ e1 < e2). { apply (FAT167 H1 H2). }
  destruct H5; auto. destruct H5.
  + eapply H in H5; eauto; tauto.
  + eapply H in H5; eauto; tauto.
Qed.
