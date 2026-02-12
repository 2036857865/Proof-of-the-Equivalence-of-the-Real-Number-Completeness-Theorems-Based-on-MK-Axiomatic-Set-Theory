(**********************************************************************)
(*     This is part of Real_Completeness, it is distributed under     *)
(*    the terms of the GNU Lesser General Public License version 3    *)
(*             (see file LICENSE for more details)                    *)
(*                                                                    *)
(*                     Copyright 2026-2031                            *)
(*              Ce Zhang, Guowei Dou and ωensheng Yu                  *)
(**********************************************************************)

Require Export Cauchy_Convergence_Criterion.

Section completeness_Dedekind.

Variable a0 b0 FirstClass SecondClass : Class.
Hypothesis divideFS : divide FirstClass SecondClass.
Hypothesis Ha : a0 ∈ FirstClass.
Hypothesis Hb : b0 ∈ SecondClass.

Proposition a0_in_RC : a0 ∈ RC.
Proof.
  red in divideFS. destruct divideFS, H0, H1, H2, H3. red in H.
  apply H in Ha; auto.
Qed.

Proposition b0_in_RC : b0 ∈ RC.
Proof.
  red in divideFS. destruct divideFS, H0, H1, H2, H3. red in H0.
  apply H0 in Hb; auto.
Qed. 

Proposition a0_less_b0 : a0 < b0.
Proof.
  red in divideFS. destruct divideFS, H0, H1, H2, H3. 
  red in H4. apply H4; auto.
Qed. 

Proposition Ensemble_a0 : Ensemble a0.
Proof.
  pose proof a0_in_RC; unfold Ensemble; eauto.
Qed. 

Proposition Ensemble_b0 : Ensemble b0.
Proof.
  pose proof b0_in_RC; unfold Ensemble; eauto.
Qed. 

Proposition Ensemble_RC_RC : Ensemble RC × RC.
Proof.
  pose proof EnRC; apply MKT74; auto.
Qed. 

Proposition a0b0_in_RC : [a0, b0] ∈ RC × RC.
Proof.
  unfold Cartesian. appA2G.
  - apply MKT49a. apply Ensemble_a0. apply Ensemble_b0.
  - exists a0. exists b0. pose proof a0_in_RC. pose proof b0_in_RC.
    split; auto.
Qed. 

Let h := \{\ λ u v, u ∈ (RC × RC) /\ (
     ( ((First u) + (Second u))/(1 + 1) ∈ FirstClass ) 
      /\ v = [(((First u) + (Second u))/(1+1)), (Second u)]
  \/ ( ((First u) + (Second u))/(1 + 1) ∈ SecondClass ) 
      /\ v = [(First u),(((First u) + (Second u))/(1+1))]
     ) \}\.

Proposition Functionh : Function (h).
Proof.
  intros. split; intros. apply poisre.
  apply AxiomII' in H as [H[H1]], H0 as [H0[H4 H5]].
  assert(Ensemble x /\ Ensemble y) as [Hx Hy]. { apply MKT49b; auto. }
  assert(Ensemble x /\ Ensemble z) as [_ Hz]. { apply MKT49b; auto. }
  New H1. New H1. apply CartesianRCa in H3; apply CartesianRCb in H6; auto.
  assert((((x) ¹ + (x) ²) / (1 + 1))  ∈ RC); auto.
  assert(Ensemble (x) ¹); unfold Ensemble; eauto.
  assert(Ensemble (x) ²); unfold Ensemble; eauto.
  assert(Ensemble (((x) ¹ + (x) ²) / (1 + 1))); unfold Ensemble; eauto.
  destruct H2 as [[H2 Hy1]|[H2 Hy1]], H5 as [[H5 Hz1]|[H5 Hz1]].
  - rewrite Hy1, Hz1; auto. 
  - red in divideFS. destruct divideFS, H12, H13, H14, H15. red in H16.
    pose proof H16 (((x)¹ + (x)²) / (1 + 1)) (((x) ¹ + (x) ²) / (1 + 1)) H2 H5.
    apply xlx in H17; auto. contradiction.
  - red in divideFS. destruct divideFS, H12, H13, H14, H15. red in H16.
    pose proof H16 (((x)¹ + (x)²) / (1 + 1)) (((x) ¹ + (x) ²) / (1 + 1)) H5 H2.
    apply xlx in H17; auto. contradiction.
  - rewrite Hy1, Hz1; auto. 
Qed.

Proposition domh : dom(h) = RC × RC.
Proof.
  apply AxiomI; split; intros.
  - apply AxiomII in H as [H[]]. apply AxiomII' in H0 as [_[]]; auto.
  - New H. New H. apply AxiomII in H1 as [H1[x[y[H2[]]]]].
    apply AxiomII; split; auto.
    assert(Ensemble x); unfold Ensemble; eauto.
    assert(Ensemble y); unfold Ensemble; eauto.
    assert(Ensemble ((x + y) / (1 + 1))); unfold Ensemble; eauto.
    assert( (First z) = x). { subst. apply MKT54a; auto. }
    assert( (Second z) = y). { subst. apply MKT54b; auto. }
    assert(Ensemble (First z)). { rewrite H8; auto. }
    assert(Ensemble (Second z)). { rewrite H9; auto. }
    assert(Ensemble (((z) ¹ + (z) ²) / (1 + 1))).
    { rewrite H8, H9. unfold Ensemble. exists RC. auto. }
    assert(((z) ¹ + (z) ²) / (1 + 1) ∈ RC). { rewrite H8, H9. auto. }
    TF(((First z) + (Second z))/(1 + 1) ∈ FirstClass).
    + exists [(((First z) + (Second z))/(1+1)),(Second z)]. 
      apply AxiomII'; repeat split; auto.
    + assert(((z) ¹ + (z) ²) / (1 + 1) ∈ SecondClass).
      { red in divideFS. destruct divideFS as [_ [_ [_ [_ [H15 _]]]]].
        pose proof H15 (((z) ¹ + (z) ²) / (1 + 1)) H13; auto. 
        destruct H16; auto. elim H14; auto. }
      exists [(First z), (((First z) + (Second z))/(1+1))]. 
      apply AxiomII'; repeat split; auto.
Qed.

Proposition ranh : ran(h) ⊂ RC × RC.
Proof. 
  unfold Included; intros.
  apply AxiomII in H as [H[]]. apply AxiomII' in H0. destruct H0, H1.
  assert(Ensemble x /\ Ensemble z) as [Hx Hz]. { apply MKT49b; auto. }
  New H1. New H1. apply CartesianRCa in H3; apply CartesianRCb in H4; auto.
  assert((((x) ¹ + (x) ²) / (1 + 1))  ∈ RC); auto.
  assert(Ensemble (x) ¹); unfold Ensemble; eauto.
  assert(Ensemble (x) ²); unfold Ensemble; eauto.
  destruct H2 as [[]|[]]. 
  - subst. appA2G.
  - subst. appA2G.
Qed.

Proposition h_is_Function : Function h /\ dom(h) = RC × RC /\ ran(h) ⊂ RC × RC.
Proof. 
  pose proof Functionh. pose proof domh. pose proof ranh. split; auto.
Qed.

Let g := ∩(\{ λ f, Function f /\ dom(f) = Nat /\ ran(f) ⊂ RC × RC
  /\ f[One] = [a0,b0] /\ (∀ n, n ∈ Nat -> f[(n + One)%Nat] = h[(f[n])]) \}).

Proposition g_uni : ∃ u, Ensemble u/\ \{ λ f, Function f /\ dom(f) = Nat 
  /\ ran(f) ⊂ RC × RC /\ f[One] = [a0,b0] /\ 
  (∀ n, n ∈ Nat -> f[(n + One)%Nat] = h[(f[n])]) \} = [u].
Proof.
  destruct h_is_Function as [H[]]. 
  assert ( exists ! u, Function u /\ dom(u) = Nat
    /\ ran(u) ⊂ RC × RC /\ u[One] = [a0,b0]
    /\ (∀ n, n ∈ Nat -> u[(n + One)%Nat] = h[(u[n])])) as [u[[H2[H3[H4[]]]]]].
  { New H. pose proof a0b0_in_RC. pose proof Ensemble_RC_RC.
    apply (RecursionNex' ([a0,b0]) RC × RC h) in H2; auto. }
  exists u. assert (Ensemble u).
  { apply MKT75; auto. rewrite H3. apply EnNat. }
  split; auto. apply AxiomI; split; intros.
  apply AxiomII in H9 as [H9[H10[H11[H12[]]]]].
  apply MKT41; auto. symmetry. apply H7; auto. 
  apply MKT41 in H9; auto. rewrite H9.
  apply AxiomII; repeat split; auto; destruct H2; auto.
Qed.



Proposition g_is_Function : Function g /\ dom(g) = Nat
  /\ ran(g) ⊂ RC × RC /\ g[One] = [a0,b0]
  /\ (∀ n, n ∈ Nat -> g[(n + One)%Nat] = h[(g[n])]).
Proof.
  destruct g_uni as [u[]]. unfold g. rewrite H0. New H.
  apply MKT44 in H1 as []. rewrite H1.
  assert (u ∈ [u]). { apply MKT41; auto. }
  rewrite <-H0 in H3. apply AxiomII in H3 as [_[H3[H4[H5[]]]]]; auto.
Qed.

Let M := \{\ λ u v, u ∈ Nat /\ v = First (g[u]) \}\.

Let N := \{\ λ u v, u ∈ Nat /\ v = Second (g[u]) \}\.

Proposition M_is_Seq : IsSeq M /\ (∀ x, x ∈ Nat -> M[x] = First g[x])
  /\ M[One] = a0.
Proof.
  destruct g_is_Function as [H[H0[H1[]]]].
  assert (IsSeq M) as [H4[]].
  { repeat split; unfold Relation; intros.
    - apply AxiomII in H4 as [_[x[y[]]]]; eauto.
    - apply AxiomII' in H4 as [_[]], H5 as [_[]].
      rewrite H6,H7; auto.
    - apply AxiomI; split; intros. apply AxiomII in H4 as [_[]].
      apply AxiomII' in H4 as [_[]]; auto.
      apply AxiomII; split; eauto. exists (First (g[z])).
      apply AxiomII'; split; auto. apply MKT49a; eauto.
      rewrite <-H0 in H4. apply Property_Value,Property_ran,H1 in H4; auto.
      apply AxiomII in H4 as [H4[x[y[]]]]. rewrite H5 in *.
      apply MKT49b in H4 as []. rewrite MKT54a; eauto.
    - unfold Included; intros. apply AxiomII in H4 as [_[]].
      apply AxiomII' in H4 as [_[]]. rewrite <-H0 in H4.
      apply Property_Value,Property_ran,H1 in H4; auto.
      apply AxiomII in H4 as [H4[x0[y0[H6[]]]]].
      rewrite H6 in H4. apply MKT49b in H4 as [].
      rewrite H5,H6,MKT54a; auto. }
  assert (∀ x, x ∈ Nat -> M[x] = First g[x]).
  { intros. New H7. rewrite <-H5 in H8.
    apply Property_Value,AxiomII' in H8 as [_[]]; auto. }
  split; [(split)|split]; auto. rewrite H7,H2,MKT54a; eauto.
Qed.

Proposition N_is_Seq : IsSeq N /\ (∀ x, x ∈ Nat -> N[x] = Second g[x])
  /\ N[One] = b0.
Proof.
  destruct g_is_Function as [H[H0[H1[]]]].
  assert (IsSeq N) as [H4[]].
  { repeat split; unfold Relation; intros.
    - apply AxiomII in H4 as [_[x[y[]]]]; eauto.
    - apply AxiomII' in H4 as [_[]], H5 as [_[]].
      rewrite H6,H7; auto.
    - apply AxiomI; split; intros. apply AxiomII in H4 as [_[]].
      apply AxiomII' in H4 as [_[]]; auto.
      apply AxiomII; split; eauto. exists (Second (g[z])).
      apply AxiomII'; split; auto. apply MKT49a; eauto.
      rewrite <-H0 in H4. apply Property_Value,Property_ran,H1 in H4; auto.
      apply AxiomII in H4 as [H4[x[y[]]]]. rewrite H5 in *.
      apply MKT49b in H4 as []. rewrite MKT54b; eauto.
    - unfold Included; intros. apply AxiomII in H4 as [_[]].
      apply AxiomII' in H4 as [_[]]. rewrite <-H0 in H4.
      apply Property_Value,Property_ran,H1 in H4; auto.
      apply AxiomII in H4 as [H4[x0[y0[H6[]]]]].
      rewrite H6 in H4. apply MKT49b in H4 as [].
      rewrite H5,H6,MKT54b; auto. }
  assert (∀ x, x ∈ Nat -> N[x] = Second g[x]).
  { intros. New H7. rewrite <-H5 in H8.
    apply Property_Value,AxiomII' in H8 as [_[]]; auto. }
  split; [(split)|split]; auto. rewrite H7,H2,MKT54b; eauto.
Qed.

Lemma Dedekind_Lemma1 : ∀ n, n ∈ Nat -> M[n] ∈ FirstClass.
Proof.
  apply Mathematical_Induction_Nat.
  - pose proof M_is_Seq as [_[_ ]]. rewrite H; auto.
  - intros. pose proof M_is_Seq as [H1[H2 ]]. 
    assert((k + One)%Nat ∈ Nat); auto. New H. 
    apply H2 in H5; auto. New H4. apply H2 in H6. 
    pose proof g_is_Function. destruct H7, H8, H9, H10. New H.
    apply H11 in H12. rewrite H6, H12.
    assert(g [k] ∈ ran( g)).
    { rewrite <- H8 in H. apply Property_Value, Property_ran in H; auto. } 
    assert(g [k] ∈ dom(h)).
    { pose proof domh. rewrite H14. unfold Included in H9. 
      apply H9 in H13; auto. }
    pose proof Functionh. New H14. apply Property_Value in H16; auto. 
    appA2H H16; auto. destruct H17, H17, H17, H18. 
    New H16. apply MKT49c1 in H20. New H16. apply MKT49c2 in H21. 
    rename H20 into Ensemble_gk. rename H21 into Ensemble_hgk.
    apply (MKT55 g[k] h[g[k]] x x0) in H17; auto. destruct H17. 
    rewrite H20. rewrite H17 in Ensemble_gk, H13, H14, H16. 
    rewrite H20 in Ensemble_hgk. New H18. unfold Cartesian in H21. 
    appA2H H21. clear H21. destruct H22, H21, H21, H22.
    assert(Ensemble x1); unfold Ensemble; eauto.
    assert(Ensemble x2); unfold Ensemble; eauto.
    assert((x) ¹ = x1). { rewrite H21; apply MKT54a; auto. }
    assert((x) ² = x2). { rewrite H21; apply MKT54b; auto. }
    rewrite H26 in H19. rewrite H27 in H19. 
    assert(((x1 + x2) / (1 + 1)) ∈ RC); auto.
    assert(Ensemble ((x1 + x2) / (1 + 1))); unfold Ensemble; eauto.
    destruct H19 as [[]|[]].
    + assert((x0) ¹ = (x1 + x2) / (1 + 1)). { rewrite H30; apply MKT54a; auto. }
      rewrite H31; auto.
    + assert((x0) ¹ = x1). { rewrite H30; apply MKT54a; auto. }
      rewrite H31; auto. rewrite <- H26, <- H17, <- H5; auto.
Qed.

Lemma Dedekind_Lemma2 : ∀ n, n ∈ Nat -> N[n] ∈ SecondClass.
  apply Mathematical_Induction_Nat.
  - pose proof N_is_Seq as [_[_ ]]. rewrite H; auto.
  - intros. pose proof N_is_Seq as [H1[H2 ]]. 
    assert((k + One)%Nat ∈ Nat); auto. New H. 
    apply H2 in H5; auto. New H4. apply H2 in H6. 
    pose proof g_is_Function. destruct H7, H8, H9, H10. New H.
    apply H11 in H12. rewrite H6, H12.
    assert(g [k] ∈ ran( g)).
    { rewrite <- H8 in H. apply Property_Value, Property_ran in H; auto. } 
    assert(g [k] ∈ dom(h)).
    { pose proof domh. rewrite H14. unfold Included in H9. 
      apply H9 in H13; auto. }
    pose proof Functionh. New H14. apply Property_Value in H16; auto. 
    appA2H H16; auto. destruct H17, H17, H17, H18. 
    New H16. apply MKT49c1 in H20. New H16. apply MKT49c2 in H21. 
    rename H20 into Ensemble_gk. rename H21 into Ensemble_hgk.
    apply (MKT55 g[k] h[g[k]] x x0) in H17; auto. destruct H17. 
    rewrite H20. rewrite H17 in Ensemble_gk, H13, H14, H16. 
    rewrite H20 in Ensemble_hgk. New H18. unfold Cartesian in H21. 
    appA2H H21. clear H21. destruct H22, H21, H21, H22.
    assert(Ensemble x1); unfold Ensemble; eauto.
    assert(Ensemble x2); unfold Ensemble; eauto.
    assert((x) ¹ = x1). { rewrite H21; apply MKT54a; auto. }
    assert((x) ² = x2). { rewrite H21; apply MKT54b; auto. }
    rewrite H26 in H19. rewrite H27 in H19. 
    assert(((x1 + x2) / (1 + 1)) ∈ RC); auto.
    assert(Ensemble ((x1 + x2) / (1 + 1))); unfold Ensemble; eauto.
    destruct H19 as [[]|[]].
    + assert((x0) ² = x2). { rewrite H30; apply MKT54b; auto. }
      rewrite H31; auto. rewrite <- H27, <- H17, <- H5; auto.
    + assert((x0) ² = (x1 + x2) / (1 + 1)). { rewrite H30; apply MKT54b; auto. }
      rewrite H31; auto.
Qed.

Lemma Dedekind_Lemma3 : Increase M.
Proof.
  destruct N_is_Seq as [[H[]][]]. destruct M_is_Seq as [[H4[]][]].
  assert (∀ k, k ∈ Nat -> M[k] ≤ M[(k + One)%Nat]).
  { intros. rewrite H7,H7; auto. destruct h_is_Function as [H10[]].
    destruct g_is_Function as [H13[H14[H15[]]]]. rewrite H17; auto.
    assert (g[k] ∈ dom(h)).
    { rewrite <-H14 in H9. apply Property_Value,Property_ran,H15
      in H9; auto. rewrite H11; auto. }
    apply Property_Value,AxiomII' in H18; auto. destruct H18, H19. 
    New H18. apply MKT49c1 in H21. New H18. apply MKT49c2 in H22. 
    New H19. unfold Cartesian in H23. appA2H H23. clear H23. 
    destruct H24, H23, H23, H24. rename H24 into xRC. rename H25 into x0RC. 
    rename H21 into Ensemble_gk. rename H22 into Ensemble_hgk. New Ensemble_gk. 
    rewrite H23 in H21. New H21. apply MKT49c1 in H22. apply MKT49c2 in H21.
    assert((g [k]) ¹ = x). { rewrite H23. apply (MKT54a x x0) in H21; auto. }
    assert((g [k]) ² = x0). { rewrite H23. apply (MKT54b x x0) in H21; auto. }
    assert(Ensemble (((g [k]) ¹ + (g [k]) ²) / (1 + 1))).
    { rewrite H24, H25. assert((x + x0) ∈ RC); auto.
      assert(Ensemble (x + x0)); unfold Ensemble; eauto. }
    rename H26 into Ensemble_g12. 
    rewrite <- H24 in H22. rewrite <- H25 in H21. clear H24 H25 xRC x0RC.
    assert((g [k]) ¹ ∈ RC). { apply CartesianRCa; auto. }
    assert((g [k]) ² ∈ RC). { apply CartesianRCb; auto. }
    destruct H20 as [[]|[]].
    - assert((h [g [k]]) ¹ = (((g [k]) ¹ + (g [k]) ²) / (1 + 1))). 
      { rewrite H26. 
        apply (MKT54a (((g [k]) ¹ + (g [k]) ²) / (1 + 1)) (g [k]) ²); auto. }
      assert((g [k]) ¹ < (g [k]) ²). 
      { New H9. New H9. apply H2 in H28. apply H7 in H29.
        rewrite <- H28, <- H29. pose proof Dedekind_Lemma1 k H9.
        pose proof Dedekind_Lemma2 k H9. destruct divideFS as [_[_[_[_[_ ]]]]].
        red in H32. apply H32; auto. }
      rewrite H27. red; left. apply aver_Cor3; auto.
    - assert((h [g [k]]) ¹ = (g [k]) ¹). 
      { rewrite H26. apply (MKT54a ((g [k]) ¹) (((g [k]) ¹ + (g [k]) ²) / 
        (1 + 1))) in H22; auto. }
      rewrite H27. red; right; auto. }
  destruct M_is_Seq as [M_Seq _].
  assert (∀ k, k ∈ Nat -> M[k] ∈ RC). { intros. apply (anRC M); auto. }
  red. split; auto. intros. generalize dependent m.
  set (P := fun k => NtoR n < NtoR k -> M[n] ≤ M[k]).
  assert (∀ n, n ∈ Nat -> P n).
  { New H11. New H11. apply NtoRRC in H13. apply FAT24 in H11.  
    apply Mathematical_Induction_Nat; unfold P; intros.
    - apply NtoR3a in H11; auto. 
      apply (@legRf (NtoR One) (NtoR n)) in H11; auto. contradiction. 
    - New H14. apply (@FAT10 n k) in H17; auto. destruct H17.
      + rewrite H17. apply H9; auto.
      + destruct H17.
        * apply FAT25a in H17; auto. apply NtoR3' in H16; auto. 
          apply (@legNf (k + One)%Nat n) in H17; auto. contradiction.
        * apply NtoR3 in H17; auto. New H17. apply H15 in H17. New H14. 
          apply H9 in H19; auto. destruct H17.
          red; left. apply (FAT172 (M [n]) (M [k]) (M [(k + One)%Nat])); auto. 
          rewrite H17; auto. 
  }
  unfold P in H12. intros. red. apply H12 in H13 as []; auto.
Qed.

Lemma Dedekind_Lemma4 : Decrease N.
Proof.
  destruct N_is_Seq as [[H[]][]]. destruct M_is_Seq as [[H4[]][]].
  assert (∀ k, k ∈ Nat -> N[(k + One)%Nat] ≤ N[k]).
  { intros. rewrite H2,H2; auto. destruct h_is_Function as [H10[]].
    destruct g_is_Function as [H13[H14[H15[]]]]. rewrite H17; auto.
    assert (g[k] ∈ dom(h)).
    { rewrite <-H14 in H9. apply Property_Value,Property_ran,H15
      in H9; auto. rewrite H11; auto. }
    apply Property_Value,AxiomII' in H18; auto. destruct H18, H19. 
    New H18. apply MKT49c1 in H21. New H18. apply MKT49c2 in H22. 
    New H19. unfold Cartesian in H23. appA2H H23. clear H23. 
    destruct H24, H23, H23, H24. rename H24 into xRC. rename H25 into x0RC. 
    rename H21 into Ensemble_gk. rename H22 into Ensemble_hgk. New Ensemble_gk. 
    rewrite H23 in H21. New H21. apply MKT49c1 in H22. apply MKT49c2 in H21.
    assert((g [k]) ¹ = x). { rewrite H23. apply (MKT54a x x0) in H21; auto. }
    assert((g [k]) ² = x0). { rewrite H23. apply (MKT54b x x0) in H21; auto. }
    assert(Ensemble (((g [k]) ¹ + (g [k]) ²) / (1 + 1))).
    { rewrite H24, H25. assert((x + x0) ∈ RC); auto.
      assert(Ensemble (x + x0)); unfold Ensemble; eauto. }
    rename H26 into Ensemble_g12. 
    rewrite <- H24 in H22. rewrite <- H25 in H21. clear H24 H25 xRC x0RC.
    assert((g [k]) ¹ ∈ RC). { apply CartesianRCa; auto. }
    assert((g [k]) ² ∈ RC). { apply CartesianRCb; auto. }
    destruct H20 as [[]|[]].
    - assert((h [g [k]]) ² = (g [k]) ²). 
    { rewrite H26. apply (MKT54b (((g [k]) ¹ + (g [k]) ²) / (1 + 1)) 
      ((g [k]) ²)) in H21; auto. }
      rewrite H27. red; right; auto.
    - assert((h [g [k]]) ² = (((g [k]) ¹ + (g [k]) ²) / (1 + 1))). 
      { rewrite H26. apply (MKT54b (g [k]) ¹ (((g [k]) ¹ + (g [k]) ²) / 
        (1 + 1))) in H22; auto. }
      assert((g [k]) ¹ < (g [k]) ²). 
      { New H9. New H9. apply H2 in H28. apply H7 in H29.
        rewrite <- H28, <- H29. pose proof Dedekind_Lemma1 k H9.
        pose proof Dedekind_Lemma2 k H9. destruct divideFS as [_[_[_[_[_ ]]]]].
        red in H32. apply H32; auto. }
      rewrite H27. red; left. apply aver_Cor3'; auto. }
  destruct N_is_Seq as [N_Seq _].
  assert (∀ k, k ∈ Nat -> N[k] ∈ RC). { intros. apply (anRC N); auto. }
  red. split; auto. intros. generalize dependent m.
  set (P := fun k => NtoR n < NtoR k -> N[k] ≤ N[n]).
  assert (∀ m, m ∈ Nat -> P m).
  { New H11. New H11. apply NtoRRC in H13. apply FAT24 in H11.  
    apply Mathematical_Induction_Nat; unfold P; intros.
    - apply NtoR3a in H11; auto. 
      apply (@legRf (NtoR One) (NtoR n)) in H11; auto. contradiction. 
    - New H14. apply (@FAT10 n k) in H17; auto. destruct H17.
      + rewrite H17. apply H9; auto.
      + destruct H17.
        * apply FAT25a in H17; auto. apply NtoR3' in H16; auto. 
          apply (@legNf (k + One)%Nat n) in H17; auto. contradiction.
        * apply NtoR3 in H17; auto. New H17. apply H15 in H17. New H14. 
          apply H9 in H19; auto. destruct H17.
          red; left. apply (FAT172 (N [(k + One)%Nat]) (N [k]) (N [n])); auto.
          rewrite <- H17; auto. }
  unfold P in H12. intros. red. apply H12 in H13 as []; auto.
Qed.
    
Lemma Dedekind_Lemma5_L0 : ILT_Seq M N.
Proof.
  red. pose proof M_is_Seq. pose proof N_is_Seq. destruct H, H0.
  split; auto. split; auto. clear H0 H H1 H2. intro k. intros.
  pose proof Dedekind_Lemma1 k H. pose proof Dedekind_Lemma2 k H. 
  destruct divideFS as [_[_[_[_[_ ]]]]]. red in H2. apply H2; auto.
Qed.


Lemma Dedekind_Lemma5_L1 : ∀n : Class,n ∈ Nat 
  -> | M [n] - N [n] | = ((b0 - a0) · ( 1 + 1)) · div1_2expn [n].
Proof.
  pose proof M_is_Seq. pose proof N_is_Seq. destruct H, H0, H1, H2.
  pose proof Vaulediv1_2expn. pose proof div1_2expn_Lemma0. 
  apply Mathematical_Induction_Nat. 
  - rewrite H3. rewrite H4. assert(One ∈ Nat); auto. rewrite H6.
    pose proof a0_less_b0. 
    assert(a0 ∈ RC). { rewrite <- H3. apply anRC; auto. }
    assert(b0 ∈ RC). { rewrite <- H4. apply anRC; auto. }
    assert(b0 - a0 <> 0). { New H9. apply (@FAT167 a0 b0) in H11; auto. }
    rewrite (FAT194 (b0 - a0) (1 + 1)); auto.
    rewrite (divRC3 (1 + 1) (b0 - a0)); auto.
  - intros. pose proof div1_2expn_Lemma1 k H7. rewrite H9.
    assert((k + One)%Nat ∈ Nat); auto. pose proof H1 (k + One)%Nat H10. 
    pose proof H2 (k + One)%Nat H10. rewrite H11, H12. clear H9 H11 H12. 
    rename H8 into HMNk. pose proof g_is_Function.
    destruct H8, H9, H11, H12. pose proof H13 k H7.
    destruct h_is_Function as [H15[]].
    assert (g[k] ∈ dom(h)).
    { rewrite <- H9 in H7. apply Property_Value, Property_ran, H11 in H7; auto. 
      rewrite H16; auto. }
    apply Property_Value,AxiomII' in H18; auto. destruct H18, H19. 
    New H18. apply MKT49c1 in H21. New H18. apply MKT49c2 in H22. 
    New H19. unfold Cartesian in H23. appA2H H23. clear H23. 
    destruct H24, H23, H23, H24. rename H24 into xRC. rename H25 into x0RC. 
    rename H21 into Ensemble_gk. rename H22 into Ensemble_hgk. New Ensemble_gk. 
    rewrite H23 in H21. New H21. apply MKT49c1 in H22. apply MKT49c2 in H21.
    assert((g [k]) ¹ = x). { rewrite H23. apply (MKT54a x x0) in H21; auto. }
    assert((g [k]) ² = x0). { rewrite H23. apply (MKT54b x x0) in H21; auto. }
    assert(Ensemble (((g [k]) ¹ + (g [k]) ²) / (1 + 1))).
    { rewrite H24, H25. assert((x + x0) ∈ RC); auto.
      assert(Ensemble (x + x0)); unfold Ensemble; eauto. }
    rename H26 into Ensemble_g12. 
    rewrite <- H24 in H22. rewrite <- H25 in H21. clear H24 H25 xRC x0RC.
    rewrite H14. pose proof H1 k H7 as Hgk1. pose proof H2 k H7 as Hgk2.
    pose proof Dedekind_Lemma5_L0. red in H24. destruct H24 as [_[_]]. 
    pose proof H24 k H7. assert(| M [k] - N [k] | = N [k] - M [k]); auto.
    assert((k + One)%Nat ∈ Nat); auto.  pose proof H24 (k + One)%Nat H27.
    assert(| M [(k + One)%Nat] - N [(k + One)%Nat] | = N [(k + One)%Nat] - 
    M [(k + One)%Nat]); auto. rewrite Hgk1, Hgk2 in HMNk. clear H24 H25 H28.
    destruct H20.
    + destruct H20. 
      assert((h [g [k]]) ¹ = (((g [k]) ¹ + (g [k]) ²) / (1 + 1))). 
      { rewrite H24. 
        apply (MKT54a (((g [k]) ¹ + (g [k]) ²) / (1 + 1)) (g [k]) ²); auto. }
      assert((h [g [k]]) ² = (g [k]) ²). 
      { rewrite H24. 
        apply (MKT54b (((g [k]) ¹ + (g [k]) ²) / (1 + 1)) (g [k]) ²); auto. }
        rewrite H28, H25. apply CartesianRCa in H19 as gk1_in_RC.
        apply CartesianRCb in H19 as gk2_in_RC. rewrite AbE; auto.
        rewrite aver_Cor5'; auto. rewrite Abs1; auto. rewrite AbE; auto.
        rewrite HMNk. pose proof a0_in_RC. pose proof b0_in_RC.
        assert((b0 - a0) · (1 + 1) ∈ RC); auto.
        assert(div1_2expn [k] ∈ RC).
        { pose proof Vaulediv1_2expn k H7. rewrite H33. 
          assert((1 + 1) ^ k ∈ RC); auto. }
        rewrite <- divRC4; auto. apply FAT199; auto.
    + destruct H20.
      assert((h [g [k]]) ¹ = (g [k]) ¹). 
      { rewrite H24. apply (MKT54a ((g [k]) ¹) (((g [k]) ¹ + (g [k]) ²) / 
        (1 + 1))) in H22; auto. }
      assert((h [g [k]]) ² = ((g [k]) ¹ + (g [k]) ²) / (1 + 1)). 
      { rewrite H24. apply (MKT54b ((g [k]) ¹) (((g [k]) ¹ + (g [k]) ²) / 
        (1 + 1))) in H22; auto. }
      rewrite H28, H25. apply CartesianRCa in H19 as gk1_in_RC.
      apply CartesianRCb in H19 as gk2_in_RC. rewrite aver_Cor5, Abs1; auto. 
      rewrite HMNk. pose proof a0_in_RC. pose proof b0_in_RC.
      assert((b0 - a0) · (1 + 1) ∈ RC); auto.
      assert(div1_2expn [k] ∈ RC).
      { pose proof Vaulediv1_2expn k H7. rewrite H33. 
        assert((1 + 1) ^ k ∈ RC); auto. }
      rewrite <- divRC4; auto. apply FAT199; auto.
Qed.

Lemma Dedekind_Lemma5 : Limit_E M N.
Proof.
  red.  pose proof M_is_Seq. pose proof N_is_Seq. destruct H, H1, H0, H3.
  split; auto. split; auto. intros. pose proof Dedekind_Lemma5_L1.
  pose proof ArchimedeanLemma7. red in H8. destruct H8, H9.
  pose proof a0_in_RC as a0_in_RC. pose proof b0_in_RC as b0_in_RC.
  assert(((b0 - a0) · (1 + 1)) ∈ RC); auto.
  assert((b0 - a0) · (1 + 1) <> 0) as H'.
  { pose proof a0_less_b0. assert((b0 - a0) <> 0); auto. }
  assert(ε / ((b0 - a0) · (1 + 1)) ∈ RC); auto.
  pose proof a0_less_b0. rename H9 into H_0_in_RC.
  assert(((b0 - a0) · (1 + 1)) > 0); auto.
  assert(ε / ((b0 - a0) · (1 + 1)) > 0). { apply divRC1; auto. }
  apply H10 in H14; auto. destruct H14 as [N0 [H14]].
  exists N0. split; auto. intros. pose proof H15 n H16 H17.
  pose proof H7 n H16. rewrite H19. clear H19.
  assert(div1_2expn [n] > 0). 
  { pose proof Vaulediv1_2expn n H16. rewrite H19. 
    assert((1 + 1) ^ n > 0); auto. apply divRC1; auto. }
  assert(| div1_2expn [n] - 0 | = div1_2expn [n]). 
  { assert(div1_2expn [n] ∈ RC).
    { pose proof Vaulediv1_2expn n H16. rewrite H20; auto. }
    rewrite MinRpb; auto. }
  rewrite H20 in H18. clear H20. apply (FAT203a (ε / ((b0 - a0) · (1 + 1))) 
  (div1_2expn [n]) ((b0 - a0) · (1 + 1)))in H18; auto. 
  rewrite divRp7 in H18; auto. rewrite FAT194; auto.
Qed.

Let N_minus_M := \{\ λ u v, u ∈ Nat /\ v = N[u] - M[u] \}\.

Proposition N_minus_M_Cor1 : IsSeq N_minus_M 
  /\ (∀ x, x ∈ Nat -> N_minus_M[x] = N[x] - M[x]) /\ N_minus_M[One] = b0 - a0.
Proof.
  assert (IsSeq N_minus_M) as [H4[]].
  { repeat split; unfold Relation; intros.
    - appA2H H. destruct H0, H0, H0, H1. exists x. exists x0; auto.
    - appA2H H. destruct H1, H1, H1, H2. 
      appA2H H0. destruct H4, H4, H4, H5. 
      New H. apply MKT49b in H7 as []. New H0. apply MKT49b in H9 as [_]. 
      apply MKT55 in H1 as []; auto. apply MKT55 in H4 as []; auto. subst; auto.
    - apply AxiomI; split; intros. apply AxiomII in H as [_[]].
      apply AxiomII' in H as [_[]]; auto.
      apply AxiomII; split; eauto. exists (N[z] - M[z]).
      apply AxiomII'; split; auto. apply MKT49a; eauto. unfold Ensemble.
      exists RC. pose proof M_is_Seq as [].  pose proof N_is_Seq as [].
      New H. New H. apply (anRC M) in H4; auto.
    - unfold Included; intros. apply AxiomII in H as [_[]].
      apply AxiomII' in H as [_[]]. pose proof M_is_Seq as []. 
      pose proof N_is_Seq as []. New H. New H. apply (anRC M) in H5; auto. 
      apply (anRC N) in H6; auto. rewrite H0; auto. }
  assert (∀ x, x ∈ Nat -> N_minus_M[x] = N[x] - M[x]).
  { intros. New H1. rewrite <- H in H2.
    apply Property_Value,AxiomII' in H2 as [_[]]; auto. }
  split; [(split)|split]; auto. 
  pose proof M_is_Seq as [_[_[]]].  pose proof N_is_Seq as [_[_[]]].
  apply H1; auto. 
Qed.

Proposition N_minus_M_Cor2 : Conv_Seq N_minus_M.
Proof.
  red. pose proof N_minus_M_Cor1. destruct H, H0. exists 0.
  red. split; auto. split; auto. intros. pose proof Dedekind_Lemma5.
  red in H4. destruct H4, H5. New H2. apply H6 in H7; auto. 
  destruct H7 as [n0[H7]]. exists n0. split; auto. intros. New H9.
  apply H8 in H11; auto. New H9. New H. rename H13 into H'. red in H. 
  destruct H, H13. rewrite <- H13 in H12. apply Property_Value in H12; auto.
  appA2H H12. destruct H15, H15, H15, H16. 
  assert(Ensemble n); unfold Ensemble; eauto.
  assert(Ensemble (N_minus_M [n])).
  { unfold Ensemble; exists RC. apply anRC; auto. }
  apply MKT55 in H15; auto. destruct H15. subst. rewrite MinRpb, H17; auto.
  rewrite AbE; auto. 
Qed.

Proposition N_minus_M_Cor3 : ∀ ε, ε ∈ RC /\ 0 < ε 
  -> (∃ n0, n0 ∈ Nat /\ ∀ n m, n ∈ Nat -> m ∈ Nat -> NtoR n0 < NtoR n 
  -> NtoR n0 < NtoR m -> |(N_minus_M[n] - N_minus_M[m])| < ε).
Proof.
  pose proof N_minus_M_Cor1. destruct H, H0. pose proof N_minus_M_Cor2.
  apply Theorem2_11; auto.
Qed.

Proposition N_minus_M_Cor4 : ∀ n, n ∈ Nat -> N_minus_M[n] = N[n] - M[n].
Proof.
  pose proof N_minus_M_Cor1. destruct H, H0. New H. destruct H2, H3. intros.
  apply H0; auto.
Qed.

Proposition N_minus_M_Cor5 : ∀ ε, ε ∈ RC /\ 0 < ε 
  -> (∃ n0, n0 ∈ Nat /\ ∀ n m, n ∈ Nat -> m ∈ Nat -> NtoR n0 < NtoR n 
  -> NtoR n0 < NtoR m -> |( (N[n] - M[n]) - ( N[m] - M[m]))| < ε).
Proof.
  pose proof N_minus_M_Cor3. pose proof N_minus_M_Cor4. intros. New H1.
  apply H in H2. destruct H2 as [n0[]]. exists n0. split; auto.
  intros. pose proof H0 n H4. pose proof H0 m H5. rewrite <- H8, <- H9.
  apply H3; auto.
Qed.

Proposition N_minus_M_Cor6 : ∀ ε, ε ∈ RC /\ 0 < ε 
  -> (∃ n0, n0 ∈ Nat /\ ∀ n m, n ∈ Nat -> m ∈ Nat -> NtoR n0 < NtoR n 
      -> NtoR n0 < NtoR m -> |( (N[n] - N[m]) - ( M[n] - M[m]))| < ε).
Proof.
  pose proof N_minus_M_Cor5. intros. New H0. apply H in H1. 
  destruct H1 as [n0[]]. exists n0. split; auto.
  intros. pose proof H2 n m H3 H4 H5 H6. 
  pose proof N_is_Seq as [H8 _]. pose proof M_is_Seq as [H9 _].
  assert(N [m] ∈ RC). { apply anRC; auto. }
  assert(M [m] ∈ RC). { apply anRC; auto. }
  assert(| N[n] - M[n] - (N[m] - M[m]) | = | N[n] - N[m] - (M[n] - M[m]) |).
  { rewrite Min1; auto. rewrite Min1; auto. 
    rewrite (FAT186  (N [n]) (- M [n]) (- N [m])); auto.
    rewrite (FAT186  (N [n]) (- N [m]) (- M [n])); auto.
    rewrite (@FAT175 (- M [n]) (- N [m])); auto. }
  rewrite <- H12; auto.
Qed.

Theorem FAT182a2' : ∀ X Y, X ∈ RC -> Y ∈ RC -> Y ≤ X -> 0 ≤ (X - Y).
Proof.
  intros. destruct H1.
  - red; left. apply FAT182a2; auto.
  - red; right. subst. rewrite xminx; auto.
Qed.

Proposition N_minus_M_Cor7 : ∀ ε, ε ∈ RC /\ 0 < ε 
  -> (∃ n0, n0 ∈ Nat /\ ∀ n m, n ∈ Nat -> m ∈ Nat -> NtoR n0 < NtoR n 
  -> NtoR n0 < NtoR m -> |M[n] - M[m]| < ε).
Proof.
  pose proof N_minus_M_Cor6. intros. New H0. apply H in H1. 
  destruct H1 as [n0[]]. exists n0. split; auto.
  intros. pose proof H2 n m H3 H4 H5 H6. New H3.
  pose proof M_is_Seq as [Hm _]. pose proof N_is_Seq as [Hn _].
  assert(M [n] ∈ RC). { apply anRC; auto. }
  assert(N [n] ∈ RC). { apply anRC; auto. }
  apply (@FAT10 m n) in H8; auto. destruct H8 as [H8|[]].
  - subst. rewrite xminx; auto. destruct H0. rewrite Zabs; auto. 
  - assert(0 ≤ N [n] - N [m]).
    { pose proof Dedekind_Lemma4. red in H11. destruct H11.
      assert(NtoR n < NtoR m). { apply NtoR3; auto. }
      apply (H12 n m) in H13; auto. destruct H13.
      + red; left; apply FAT182a2; auto.
      + rewrite H13, xminx; auto. red; right; auto. }
    assert(M [n] - M [m] ≤ 0).
    { pose proof Dedekind_Lemma3. red in H12. destruct H12.
      assert(NtoR n < NtoR m). { apply NtoR3; auto. }
      apply (H13 n m) in H14; auto. destruct H14.
      + red; left; apply FAT182c2; auto.
      + rewrite H14, xminx; auto. red; right; auto. }
    assert(|N [n] - N [m] - (M [n] - M [m])| = N [n] - N [m] - (M[n] - M[m])).
    { assert(N [n] - N [m] ∈ RC); auto. assert(M [n] - M [m] ∈ RC); auto.
      assert(N [n] - N [m] - (M [n] - M [m]) ∈ RC); auto.
      apply AbPRC0; auto. apply (FAT182a2' (N[n] - N[m]) (M[n] - M[m])); auto.
      apply (T173 (M [n] - M [m]) 0 (N [n] - N [m])); auto. }
    rewrite H13 in H7; clear H13. 
    assert(N [n] - N [m] - (M [n] - M [m]) ≥ - (M [n] - M [m])).
    { destruct H11.
      + red. left. 
        apply (FAT188c2 0 (N [n] - N [m]) (- (M [n] - M [m]))) in H11; auto.
        rewrite MinRpa in H11; auto.
      + rewrite <- H11. red; right; rewrite MinRpa; auto. }
    assert(- (M [n] - M [m]) = | M [n] - M [m] | ).
    { symmetry. apply AbNRC0; auto. }
    assert(N [n] - N [m] - (M [n] - M [m]) ≥ | M [n] - M [m] |).
    { rewrite <- H14; auto. }
    assert(N [n] - N [m] ∈ RC); auto. assert(M [n] - M [m] ∈ RC); auto.
    assert(N [n] - N [m] - (M [n] - M [m]) ∈ RC); auto. destruct H0.
    apply (FAT172 _ (N [n] - N [m] - (M [n] - M [m])) _); auto.
  - assert(0 ≤ M [n] - M [m]).
    { pose proof Dedekind_Lemma3. red in H11. destruct H11.
      assert(NtoR m < NtoR n). { apply NtoR3; auto. }
      apply (H12 m n) in H13; auto. destruct H13.
      + red; left; apply FAT182a2; auto.
      + rewrite H13, xminx; auto. red; right; auto. }
    assert(N [n] - N [m] ≤ 0).
    { pose proof Dedekind_Lemma4. red in H12. destruct H12.
      assert(NtoR m < NtoR n). { apply NtoR3; auto. }
      apply (H13 m n) in H14; auto. destruct H14.
      + red; left; apply FAT182c2; auto.
      + rewrite H14, xminx; auto. red; right; auto. }
    assert(|N [n] - N [m] - (M [n] - M [m])| = M [n] - M [m] - (N[n] - N[m])).
    { assert(N [n] - N [m] ∈ RC); auto. assert(M [n] - M [m] ∈ RC); auto.
      assert(N [n] - N [m] - (M [n] - M [m]) ∈ RC); auto.
      rewrite AbE; auto.
      apply AbPRC0; auto. apply (FAT182a2' (M [n] - M [m]) (N[n] - N[m])); auto.
      apply (T173 (N [n] - N [m]) 0 (M [n] - M [m])); auto. }
    rewrite H13 in H7; clear H13. 
    assert(M [n] - M [m] - (N [n] - N [m]) ≥ (M [n] - M [m])).
    { destruct H12.
      + red. left. apply FAT183a1 in H12; auto. rewrite Zmin in H12.
        apply (FAT188c2 0 (-(N [n] - N [m])) (M [n] - M [m])) in H12; auto.
        rewrite AddRpa in H12; auto. 
        rewrite (@FAT175 (-(N [n] - N [m])) (M [n] - M [m])) in H12; auto. 
      + rewrite H12. red; right. rewrite MinRpb; auto. }
    assert((M [n] - M [m]) = | M [n] - M [m] | ).
    { symmetry. apply AbPRC0; auto. }
    assert(M [n] - M [m] - (N [n] - N [m]) ≥ | M [n] - M [m] |).
    { rewrite <- H14; auto. }
    assert(N [n] - N [m] ∈ RC); auto. assert(M [n] - M [m] ∈ RC); auto.
    assert(M [n] - M [m] - (N [n] - N [m]) ∈ RC); auto. destruct H0.
    apply (FAT172 _ (M [n] - M [m] - (N [n] - N [m])) _); auto.
Qed. 

Lemma Dedekind_Lemma6_1 : ∀ ε, ε ∈ RC /\ 0 < ε 
  -> (∃ n0, n0 ∈ Nat /\ ∀ n m, n ∈ Nat -> m ∈ Nat
  -> NtoR n0 < NtoR n -> NtoR n0 < NtoR m -> |(M[n] - M[m])| < ε).
Proof.
  intros. pose proof N_minus_M_Cor7 ε H. destruct H0 as[n0[]].
  exists n0. split; auto.
Qed.

Proposition Dedekind_Lemma6_2 : Conv_Seq M.
Proof.
  pose proof M_is_Seq as []. pose proof Dedekind_Lemma6_1. 
  apply Theorem2_11; auto. 
Qed.

Proposition Dedekind_Lemma7_2 : Conv_Seq N.
Proof.
  red. pose proof Dedekind_Lemma5. pose proof Dedekind_Lemma6_2. red in H0.
  destruct H0 as [s]. 
  assert(s ∈ RC). 
  { unfold Limit in H0. destruct H0 as [_[H0 _]]; auto. }
  exists s. apply (Limit_Equal M N s) in H; auto.
  pose proof N_is_Seq as []; auto.
Qed.

Proposition Dedekind_Lemma7_1 : ∀ ε, ε ∈ RC /\ 0 < ε 
  -> (∃ n0, n0 ∈ Nat /\ ∀ n m, n ∈ Nat -> m ∈ Nat
  -> NtoR n0 < NtoR n -> NtoR n0 < NtoR m -> |(N[n] - N[m])| < ε).
Proof.
  pose proof N_is_Seq as []. pose proof Dedekind_Lemma7_2. 
  apply Theorem2_11; auto. 
Qed.

Theorem Dedekind_Lemma8 : ∃ e, e ∈ RC /\ Split FirstClass SecondClass e.
Proof.
  pose proof Dedekind_Lemma6_2. pose proof Dedekind_Lemma7_2.
  red in H, H0. destruct H as [s]. exists s. destruct H0 as [s1].
  assert(s = s1). 
  { pose proof Dedekind_Lemma5. New H. New H0. New H2. red in H3, H4.
    destruct H3, H4, H5, H6. apply (Limit_Equal M N s) in H2; auto.
    apply (LimUni N s s1); auto. }
  rewrite <- H1 in H0. clear H1.
  assert(s ∈ RC). 
  { unfold Limit in H0. destruct H0 as [_[H0 _]]; auto. }
  split; auto. red. split; intro z; intros.
  - assert(s - z ∈ RC /\ 0 < s - z) as []. 
    { split; auto. apply FAT182a2; auto. }
    red in H. destruct H as [H[_]].
    pose proof H6 (s - z) H4 H5.  destruct H7 as [n0[]].
    assert(NtoR n0 < NtoR (n0 + One)%Nat).
    { apply NtoR3; auto. apply FAT18; auto. }
    apply H8 in H9; auto.
    assert(∃ n1, n1 = (n0 + One)%Nat /\ n1 ∈ Nat) as [n1 []].
    { exists (n0 + One)%Nat. split; auto. }
    assert(z < M [n1]).
    { subst. assert(M [(n0 + One)%Nat] ∈ RC). { apply anRC; auto. }
      rewrite AbE in H9; auto. apply Ab1 in H9 as [_ H9]; auto.
      rewrite FAT175 in H9; auto. rewrite (@FAT175 s (-z)) in H9; auto.
      apply FAT188c1 in H9; auto. apply FAT183c2; auto. }
    pose proof Dedekind_Lemma1 n1 H11.
    destruct divideFS as [H15[H16[H17[H18[H19 H20]]]]].
    apply (Split_Pa (M [n1]) z FirstClass SecondClass); auto.
  - assert(z - s ∈ RC /\ 0 < z - s) as []. 
    { split; auto. apply FAT182a2; auto. }
    red in H0. destruct H0 as [H0[_]].
    pose proof H6 (z - s) H4 H5.  destruct H7 as [n0[]].
    assert(NtoR n0 < NtoR (n0 + One)%Nat).
    { apply NtoR3; auto. apply FAT18; auto. }
    apply H8 in H9; auto.
    assert(∃ n1, n1 = (n0 + One)%Nat /\ n1 ∈ Nat) as [n1 []].
    { exists (n0 + One)%Nat. split; auto. }
    assert(N [n1] < z).
    { subst. assert(N [(n0 + One)%Nat] ∈ RC). { apply anRC; auto. }
      apply Ab1 in H9 as [_ H9]; auto. apply FAT188c1 in H9; auto. }
    pose proof Dedekind_Lemma2 n1 H11.
    destruct divideFS as [H15[H16[H17[H18[H19 H20]]]]].
    apply (Split_Pb (N [n1]) z FirstClass SecondClass); auto.
Qed.

End completeness_Dedekind.

Theorem FAT205a : ∀ x y, divide x y -> ∃ e, e ∈ RC /\ Split x y e.
Proof. 
  intros. New H. red in H0. destruct H0, H1, H2, H3, H4.
  assert(∃a0, a0 ∈ x). { apply NEexE; auto. }
  assert(∃b0, b0 ∈ y). { apply NEexE; auto. }
  destruct H6 as [a0], H7 as [b0].
  pose proof Dedekind_Lemma8 a0 b0 x y H H6 H7; auto.
Qed.

Theorem FAT205b : ∀ x y e1 e2, divide x y -> e1 ∈ RC -> e2 ∈ RC
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
  + eapply H in H5. contradiction. eauto. auto. auto.
  + eapply H in H5. contradiction. eauto. auto. auto.
Qed.