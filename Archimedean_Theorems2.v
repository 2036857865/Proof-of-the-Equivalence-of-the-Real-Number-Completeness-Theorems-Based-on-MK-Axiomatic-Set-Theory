(**********************************************************************)
(*     This is part of Real_Completeness, it is distributed under     *)
(*    the terms of the GNU Lesser General Public License version 3    *)
(*             (see file LICENSE for more details)                    *)
(*                                                                    *)
(*                     Copyright 2026-2031                            *)
(*              Ce Zhang, Guowei Dou and ωensheng Yu                  *)
(**********************************************************************)

Require Export Bolzano_Weierstrass_Theorem.

Theorem Archimedean_Theorem2 :∀ x y, x ∈ RC -> x > 0 
  -> y ∈ RC -> exists n, n ∈ Nat /\ NtoR n · x > y.
Proof.
  intros. New H1. apply (@FAT167 y 0) in H2 as [H2|[|]]; auto.
  - subst. exists (One + One)%Nat. split; auto.
  - assert(y / x ∈ RC); auto.
    pose proof ArchimedeanLemma1 (y/x) H3 as [n[]].
    exists n. split; auto. New H0.
    apply (FAT203a (NtoR n) (y / x) (x)) in H6; auto.
    rewrite divRp7 in H6; auto.
  - exists One. split; auto.
Qed.

Theorem Archimedean_Theorem3 :∀ x, x ∈ RC -> x > 0 
  -> exists n, n ∈ Nat /\ NtoR n · x > 1.
Proof.
  intros. New H. apply (Archimedean_Theorem2 x 1) in H1; auto.
Qed.

Theorem Archimedean_Theorem4 : exists e, AccumulationPoint e ran(div1_n).
Proof.
  intros. exists 0. pose proof Archimedean_Theorem3. red. intro s; intros.
  New H0. New H1. apply H in H3; auto. destruct H3 as [N[]].
  exists (1 / (NtoR N)). assert(1 / NtoR N ∈ RC); auto. 
  assert(Ensemble(1 / NtoR N)). { unfold Ensemble; eauto. }
  assert(NtoR N > 0). { apply ng0; auto. }
  assert(1 / NtoR N > 0). {  apply divRC1 ; auto. }
  repeat split; auto.
  - appA2G; auto. repeat split; auto. rewrite AddRpb; auto.
    apply (FAT203a (NtoR N · s) 1 (1 / NtoR N)) in H4; auto.
    rewrite divRC3, FAT195a' in H4; auto.
  - appA2G; auto. exists N. appA2G; auto.
Qed.