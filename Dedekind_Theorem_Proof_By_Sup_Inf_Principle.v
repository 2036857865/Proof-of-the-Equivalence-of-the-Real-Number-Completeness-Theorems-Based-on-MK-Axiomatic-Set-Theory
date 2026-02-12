(**********************************************************************)
(*     This is part of Real_Completeness, it is distributed under     *)
(*    the terms of the GNU Lesser General Public License version 3    *)
(*             (see file LICENSE for more details)                    *)
(*                                                                    *)
(*                     Copyright 2026-2031                            *)
(*              Ce Zhang, Guowei Dou and ωensheng Yu                  *)
(**********************************************************************)

Require Export Sup_Inf_Principle.

Theorem Dedekind_Theorema : ∀ x y, divide x y -> ∃ e, e ∈ RC /\ Split x y e.
Proof.
  intros. destruct (FstRC x y H) as [?|[?|?]].
  - apply FAT205a_aux1; auto.
  - destruct H0. exists 0. split; auto. red. split; intros.
    + assert (a ∈ NRC). auto. apply H0; auto.
    + assert (a ∈ PRC). auto. apply H1; auto.
  - apply FAT205a_aux2; auto.
Qed.

(* unique *)
Theorem Dedekind_Theoremb : ∀ x y e1 e2, divide x y -> e1 ∈ RC -> e2 ∈ RC
  -> Split x y e1 -> Split x y e2 -> e1 = e2.
Proof.
  intros x y e1 e2 H1 H H0 H3 H4.
  destruct H1 as [fstinR[sndinR[fstne[sndne[]]]]].
  destruct (FAT167 H H0) as [?|[?|?]]; auto;
  apply aver2 in H5; auto; unfold Split in H3,H4;
  destruct H3,H4,H5.
  - apply H7 in H5; auto. apply H3 in H8; auto.
    pose proof (Split_Pc ((e2 + e1) / (1 + 1)) x y). MP. elim H9.
  - apply H6 in H5; auto. apply H4 in H8; auto.
    pose proof (Split_Pc ((e1 + e2) / (1 + 1)) x y). MP. elim H9.
Qed.