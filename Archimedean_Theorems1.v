(**********************************************************************)
(*     This is part of Real_Completeness, it is distributed under     *)
(*    the terms of the GNU Lesser General Public License version 3    *)
(*             (see file LICENSE for more details)                    *)
(*                                                                    *)
(*                     Copyright 2026-2031                            *)
(*              Ce Zhang, Guowei Dou and ωensheng Yu                  *)
(**********************************************************************)

Require Export Monotone_Bounded_Theorem.

Theorem Mathematical_Induction_Nat : ∀ (P :Class -> Prop), P One
  -> (∀ k, k ∈ Nat -> P k -> P (k+One)%Nat) -> (∀ n, n ∈ Nat -> P n).
Proof.
  intros. assert (\{λ x, x ∈ Nat /\ P x \} = Nat).
  { apply FAA5; try red; intros.
    - appA2H H2; tauto.
    - appA2G.
    - appA2H H2. destruct H3. appA2G. split; auto. rewrite <- FAT4a; auto. }
  rewrite <- H2 in H1. appA2H H1; tauto.
Qed.

Theorem FAA3' : ∀ x, x ∈ Nat -> (x + One)%Nat <> One.
Proof.
  intros. rewrite FAT4a; auto. apply FAA3; auto.
Qed.

Theorem FAA4' : ∀ x y, x ∈ Nat -> y ∈ Nat ->  (x + One)%Nat = (y + One)%Nat
  -> x = y.
Proof.
  intros. rewrite FAT4a in H1; rewrite FAT4a in H1; auto. apply FAA4; auto.
Qed.

Theorem Recursion' : ∀ F a, Function F -> dom(F) = RC -> ran(F) ⊂ RC -> a ∈ RC 
  -> (exists h, Function h /\ dom(h) = Nat /\ ran(h) ⊂ RC /\ h[One] = a /\ 
     (∀ n, n ∈ Nat -> h[(n + One)%Nat] = F[(h[n])])).
Proof.
  intros. pose proof EnRC. assert(OnTo F RC RC). { red. split; auto. }
   apply (@RecursionNex F RC a) in H4; auto. destruct H4. exists x.
   destruct H4 as [[] []]. destruct H5. split; auto. repeat split; auto.
   intros. New H9. apply H7 in H10. rewrite FAT4a; auto.
Qed.

Theorem Recursion : ∀ F a, Function F -> dom(F) = RC -> ran(F) ⊂ RC -> a ∈ RC 
  -> (exists ! h, Function h /\ dom(h) = Nat /\ ran(h) ⊂ RC 
  /\ h[One] = a /\ (∀ n, n ∈ Nat -> h[(n + One)%Nat] = F[(h[n])])).
Proof.
  intros. pose proof EnRC. assert(OnTo F RC RC). { red. split; auto. }
   apply (@RecursionNex F RC a) in H4; auto. destruct H4. exists x.
   destruct H4 as [[] []], H5. split; auto. split; auto. repeat split; auto.
   intros. New H9. apply H7 in H10. rewrite FAT4a; auto.
  intros. destruct H9 as [H9 [H10 [H11 []]]]. apply MKT71; auto.
  intros. destruct (classic (x0 ∈ Nat)).
  - generalize dependent x0. apply Mathematical_Induction_Nat.
    + rewrite H6, H12; auto.
    + intros. New H14. New H14. rename H17 into HkNat. apply H13 in H14. 
      apply H7 in H16; rewrite <- FAT4a in H16; auto;
      rewrite H14, H16, H15; auto.
  - New H14. rewrite <- H5 in H14. rewrite <- H10 in H15. apply MKT69a in H14. 
    apply MKT69a in H15. rewrite H14, H15; auto.
Qed.

Lemma RecursionNex' : ∀a A F : Class, 
  Ensemble A -> Function F -> dom(F) = A -> ran(F) ⊂ A -> a ∈ A 
  -> ∃y,unique (λ f : Class,Function f /\ dom( f) = Nat /\ ran( f) ⊂ A 
  /\ f [One] = a /\ (∀n : Class,n ∈ Nat -> f [(n + One)%Nat] = F [f [n]])) y.
Proof.
  intros. assert(OnTo F A A). { red. split; auto. }
  apply (@RecursionNex F A a) in H4; auto. destruct H4. exists x.
  destruct H4 as [[] []]. destruct H5. split; auto. split; auto. 
  repeat split; auto. intros. New H9. apply H7 in H10. rewrite FAT4a; auto.
  intros. destruct H9 as [H9 [H10 [H11 []]]]. apply MKT71; auto.
  intros. destruct (classic (x0 ∈ Nat)).
  - generalize dependent x0. apply Mathematical_Induction_Nat.
    + rewrite H6, H12; auto.
    + intros. New H14. New H14. rename H17 into HkNat. apply H13 in H14; apply 
      H7 in H16. rewrite <- FAT4a in H16; auto; rewrite H14, H16, H15; auto.
  - New H14. rewrite <- H5 in H14. 
    rewrite <- H10 in H15. 
    apply MKT69a in H14. apply MKT69a in H15. 
    rewrite H14, H15; auto.
Qed.

Theorem construction_Exponent : ∀ m, m ∈ RC
  -> (exists ! f, Function f /\ dom(f) = Nat /\ ran(f) ⊂ RC
  /\ f[One] = m /\ (∀ n, n ∈ Nat -> f[(n + One)%Nat] = f[n] · m)).
Proof.
  intros. assert (Function (\{\ λ u v, u ∈ RC /\ v = u · m \}\)).
  { split; intros. unfold Relation. intros; apply AxiomII in H0 as 
    [H0[u[v[H1[]]]]]; eauto. apply AxiomII' in H0 as [H0[]].
    apply AxiomII' in H1 as [H1[]]. rewrite H3,H5; auto. }
  apply (Recursion _ m) in H0 as [f[[H0[H1[H2[]]]]]]; auto.
  - exists f. split; auto. 
    + split; auto. repeat split; auto. intros. New H5. pose proof H6 as H6'. 
      apply H4 in H6. rewrite H6. apply AxiomI; split; intros.
      * apply AxiomII in H8 as []. apply H9.
        assert (Ensemble ((f[n])·m)).
        { assert (((f[n])· m) ∈ RC). 
          { assert (f[n] ∈ RC).
            { apply H2. apply (@ Property_ran n).
              apply Property_Value. auto. rewrite H1; auto. } 
            apply mulRC; auto. } 
           eauto. }
        apply AxiomII; split; auto. apply AxiomII'.
        assert (f[n] ∈ RC).
        { apply H2. apply (@ Property_ran n). 
          apply Property_Value; auto.
          rewrite H1; auto. } 
        split; auto. apply MKT49a; eauto.
      * apply AxiomII; split; eauto. intros. apply AxiomII in H9 as [].
        apply AxiomII' in H10. destruct H10 as [H11[]]. rewrite H12; auto.
    + intros g [H6[H7[H8[]]]]. apply H5. split; auto.
      repeat split; auto.
      intros. pose proof H11 as H11'.
      apply H10 in H11. rewrite H11.
      apply AxiomI; split; intros.
      * apply AxiomII; split; eauto. intros. apply AxiomII in H13 as []. 
        apply AxiomII' in H14 as [H14[]]. rewrite H16; auto.
      * apply AxiomII in H12 as []. apply H13. apply AxiomII.
        assert (Ensemble (g[n]· m)).
        { assert ((g[n]·m) ∈ RC).
          { assert (g[n] ∈ RC).
            { apply H8. apply (@ Property_ran n).
              apply Property_Value; auto. rewrite H7; auto. } 
            apply mulRC; auto. } 
           eauto. }
        split; auto. apply AxiomII'.
        assert (g[n] ∈ RC).
        { rewrite <-H7 in H11'. 
          apply Property_Value in H11'; auto.
          apply Property_ran in H11'. apply H8 in H11'; auto. }
        split; auto. apply MKT49a; eauto.
  - apply AxiomI; split; intros. apply AxiomII in H1 as [H1[y]].
    apply AxiomII' in H2 as [H2[]]; auto. apply AxiomII; split; eauto.
    exists (z·m). apply AxiomII'. split; auto. apply MKT49a; eauto.
  - unfold Included; intros. apply AxiomII in H1 as [H1[]].
    apply AxiomII' in H2 as [H2[]]. rewrite H4.
    apply mulRC; auto.
Qed.

Corollary ExpFunction_uni: ∀ m, m ∈ RC
  -> exists f, Ensemble f /\ \{ λ f,Function f /\ dom(f) = Nat 
  /\ ran(f) ⊂ RC /\ f[One] = m /\ 
  (∀ n, n ∈ Nat -> f[(n+One)%Nat] = f[n]·m) \} = [f].
Proof.
  intros. pose proof H as H'. 
  apply construction_Exponent in H as [f[]].
  exists f. split. destruct H as [H1[H2[H3[]]]].
  apply MKT75; auto. rewrite H2. apply EnNat.
  apply AxiomI; split; intros.
  - apply AxiomII in H1 as [H2[H3[H4[H5[]]]]]. apply MKT41; auto.
    + apply MKT75. destruct H; auto. destruct H as [H7[]]. rewrite H. 
      apply EnNat.
    + symmetry. apply H0; split; auto.
  - apply AxiomII; split; auto.
    + apply MKT41 in H1.
      ++ rewrite H1. apply MKT75. destruct H; auto. destruct H as [H2[]]. 
         rewrite H. apply EnNat.
      ++ destruct H as [H3[]]. apply MKT75; auto. rewrite H. apply EnNat.
    + apply MKT41 in H1. 
      ++ rewrite H1; auto. 
      ++ destruct H as [H3[]]. apply MKT75; auto. rewrite H. apply EnNat.
Qed.

Definition ExpFunction a := ∩\{ λ h, Function h /\ 
  dom(h) = Nat /\ ran(h) ⊂ RC /\ h[One] = a /\ 
  ∀ n, n ∈ Nat -> h[(n + One)%Nat] = h[n] · a \}.

Definition Exp a n := (ExpFunction a)[n].

Notation "x ^ y" :=(Exp x y): RC_scope.

Corollary expRC : ∀ x y, x ∈ RC -> y ∈ Nat -> (x ^ y) ∈ RC.
Proof.
  intros. unfold Exp. pose proof H as H'.
  apply ExpFunction_uni in H as [f[]].
  assert (f ∈ [f]). { apply MKT41; auto. }
  assert ((ExpFunction x) = f).
  { unfold ExpFunction. rewrite H1. apply MKT44; auto. }
  rewrite H3. rewrite <- H1 in H2.
  apply AxiomII in H2 as [H2[H5[H6[H7[]]]]].
  assert (f[y] ∈ ran(f)).
  { apply (@Property_ran y),Property_Value; auto.
    rewrite H6; auto. }
  apply H7; auto.
Qed.

Global Hint Resolve expRC : core.

Theorem P_Ex1: ∀ x, x ∈ RC -> Function (ExpFunction x).
Proof.
  intros. apply ExpFunction_uni in H as [f[]].
  assert (f ∈ [f]). { apply MKT41; auto. }
  assert ((ExpFunction x) = f).
  { unfold ExpFunction. rewrite H0. apply MKT44; auto. }
  rewrite H2. rewrite <- H0 in H1. apply AxiomII in H1.
  destruct H1 as [H3[]]; auto.
Qed.

Theorem P_Ex2: ∀ x, x ∈ RC -> x ^ One = x.
Proof.
  intros. apply AxiomI; split; intros.
  - apply AxiomII in H0 as [].
    apply H1. apply AxiomII; split; eauto.
    apply AxiomII; split. pose proof FAA1.
    apply AxiomII in H2 as [H3[]]. apply MKT49a; eauto.
    intros. apply AxiomII in H2 as [H3[H4[H5[H6[]]]]].
    rewrite <- H2. apply Property_Value; auto. rewrite H5. 
    apply FAA1.
  - apply AxiomII; split; eauto. intros.
    assert (x ∈ \{ λ y, [One, y] ∈ ExpFunction x \}).
    { apply AxiomII; split; eauto. apply AxiomII; split.
      pose proof FAA1. apply MKT4' in H2 as [].
      apply MKT49a; eauto. intros.
      apply AxiomII in H2 as [H3[H4[H5[H6[]]]]].
      rewrite <- H2. apply Property_Value; auto. rewrite H5. 
      apply FAA1. }
    assert (y = x).
    { apply AxiomII in H1,H2. destruct H1,H2.
      apply Property_Fun in H3,H4. rewrite H3; auto. 
      apply P_Ex1; auto. apply P_Ex1; auto. }
    rewrite H3; auto.
Qed.

Corollary Exp_mult1 : ∀ x a, x ∈ RC -> x > 0 -> a ∈ Nat
  -> x ^ (a + One)%Nat = x ^ a · x.
Proof.
  intros.
  pose proof FAA1. pose proof (@MulNp a One). pose proof (@AddNp a One). 
  New H1. New H1. apply H3 in H5; auto. apply H4 in H6; auto. clear H3 H4.
  rename H6 into H4. New H2.
  assert (∀ a, a ∈ Nat -> x ^ (a + One)%Nat = (x ^ a) · x).
  { apply Mathematical_Induction_Nat.
    - apply AxiomI; split; intros. 
      + apply AxiomII in H6 as []. apply H7.
        apply AxiomII; split. pose proof (P_Ex2 x H). 
        rewrite H8. pose proof (mulRC x x H H); eauto.
        apply AxiomII; split. apply MKT49a. 
        New H2. New H2.
        pose proof (@MulNp One One). pose proof (@AddNp One One). 
        apply H10 in H8; auto. apply H11 in H9; auto. eauto.
        rewrite P_Ex2; eauto.
        pose proof (mulRC x x H H); eauto.
        intros. apply AxiomII in H9 as [H9[H10[H11[H12[]]]]].
        pose proof H3. apply H14 in H15.
        rewrite P_Ex2; auto. rewrite H13 in H15.
        rewrite <-H15. apply Property_Value; auto.
        rewrite H11. apply AddNp; auto.
      + apply AxiomII; split; eauto.
        intros. apply AxiomII in H7. destruct H7.
        assert ([(One + One)%Nat, x ^ One · x] ∈ ExpFunction x).
        { apply AxiomII; split. apply MKT49a.
          New H2. New H2. pose proof (@MulNp One One). 
          pose proof (@AddNp One One). apply H11 in H9; auto. 
          apply H12 in H10; auto. eauto.
          rewrite P_Ex2; eauto.
          pose proof (mulRC x x H H); eauto. rename H9 into HxmulRC.
          intros. apply AxiomII in H9 as [H9[H10[H11[H12[]]]]].
          pose proof H3. apply H14 in H15. rewrite P_Ex2; eauto.
          rewrite H13 in H15. rewrite <-H15. 
          apply Property_Value; auto. rewrite H11.
          pose proof (@AddNp One One). apply H16 in H2; auto. }
        assert (y = x ^ One · x).
        { apply P_Ex1 in H. unfold Function in H.
          destruct H. apply H10 with (One + One)%Nat; auto. }
        rewrite H10; auto.
     - intros. New H2. New H2. 
        pose proof (@AddNp k One). pose proof (@MulNp k One). 
        apply H10 in H8; auto. apply H11 in H9; auto. eauto. clear H10 H11.
        pose proof (expRC x (k+One)%Nat H H8).
        pose proof (mulRC (x^(k+One)%Nat) x H10 H).
        apply AxiomI; split; intros.
        + apply AxiomII in H12 as []. apply H13. apply AxiomII; split; eauto.
          apply AxiomII; split. apply MKT49a; eauto. New H2. New H2. pose proof 
          (@AddNp (k+One)%Nat One). pose proof (@MulNp (k+One)%Nat One). apply 
          H16 in H14; auto. apply H17 in H15; auto. clear H14 H15 H16 H17. 
          intros. assert ((ExpFunction x) = y).
          { apply ExpFunction_uni in H as [f[]]. rewrite H15 in H14. unfold 
            ExpFunction. rewrite H15. apply MKT41 in H14; auto. rewrite H14. 
            apply MKT44; auto. } rewrite <-H15.
          assert (y[(k+One)%Nat] = x ^(k+One)%Nat). { rewrite <-H15. auto. }
          apply AxiomII in H14 as [H17[H18[H19[H20[]]]]].
          pose proof H8 as H8'. apply H21 in H8.
          rewrite H16 in H8. rewrite <-H8. rewrite H15. 
          apply Property_Value; auto. rewrite H19.
          pose proof (@AddNp (k+One)%Nat One). 
          apply H22 in H2; auto.
        + apply AxiomII; split; eauto.
          intros. apply AxiomII in H13 as [].
          assert ([(k+One+One)%Nat, x ^ (k+One)%Nat · x] ∈ ExpFunction x).
          { apply AxiomII; split. apply MKT49a; eauto. New H2. New H2.
            pose proof (@MulNp (k+One)%Nat One). pose proof (@AddNp (k+One)%Nat 
            One). apply H17 in H15; auto. apply H18 in H16; auto. clear H15 H16 
            H17 H18. intros. assert ((ExpFunction x) = y0).
            { apply ExpFunction_uni in H as [f[]].
              rewrite H16 in H15. unfold ExpFunction.
              rewrite H16. apply MKT41 in H15; auto.
              rewrite H15. apply MKT44; auto. } rewrite <-H16.
            assert (y0[(k+One)%Nat] = x ^(k+One)%Nat). { rewrite <-H16. auto. } 
            apply AxiomII in H15 as [H18[H19[H20[H21[]]]]].
            apply H22 in H8. rewrite H17 in H8. rewrite <- H8. rewrite H16.
            apply Property_Value; auto. rewrite H20. New H2. New H2.
            pose proof (@MulNp k One). pose proof (@AddNp k One). 
            apply H25 in H23; auto. }
        assert (y = x ^ (k+One)%Nat · x).
        { apply P_Ex1 in H. unfold Function in H.
          destruct H. apply H16 with (k+One+One)%Nat; auto. } 
        rewrite H16; auto. }
    apply H6 in H1; auto.
Qed.

Fact exp2ng0 : ∀ n, n ∈ Nat -> (1 + 1) ^ n > 0.
Proof.
  intros. 
  cut (∀ n, n ∈ Nat -> (1 + 1) ^ n > 0); auto.
  apply Mathematical_Induction_Nat.
  - rewrite P_Ex2; auto.
  - intros. rewrite Exp_mult1; auto. 
Qed.

Global Hint Resolve P_Ex1 P_Ex2 Exp_mult1 exp2ng0: core. 

Fact exp2not0 : ∀ n, n ∈ Nat -> (1 + 1) ^ n <> 0.
Proof.
  intros. pose proof exp2ng0 n H. auto.
Qed.

Global Hint Resolve exp2not0: core. 

Definition div1_n := \{\ λ a b, a ∈ Nat /\ b = 1/NtoR a \}\.

Fact Functiondiv1_n : Function (div1_n).
Proof.
  intros. red. split.
  - apply poisre.
  - intros. apply AxiomII' in H; apply AxiomII' in H0; deand. subst. auto.
Qed.

Fact Domdiv1_n : dom( div1_n) = Nat.
Proof.
  apply AxiomI; split. 
  + intros. New H. unfold div1_n in H0. appA2H H0. destruct H1. appA2H H1. 
    destruct H2, H2, H2, H3. New H0. apply MKT49b in H1. destruct H1. apply 
    (MKT55 z x x0 x1) in H1; auto. apply H1 in H2. destruct H2. subst; auto.
  + intros. unfold div1_n. appA2G. assert (Ensemble z); unfold Ensemble; eauto.
    assert (Ensemble (1 / NtoR z)); unfold Ensemble; eauto.
    exists(1 / NtoR z). appA2G. 
Qed.

Fact Randiv1_n : ran( div1_n) ⊂ RC.
Proof.
  unfold Included. intros. New H. unfold div1_n in H0. appA2H H0. destruct H1. 
  appA2H H1.  destruct H2, H2, H2, H3. New H0. apply MKT49b in H1. destruct H1. 
  apply (MKT55 x z x0 x1) in H1; auto. apply H1 in H2. destruct H2. subst; auto.
Qed.

Fact Seqdiv1_n : IsSeq (div1_n).
Proof.
  intros. red. pose proof Functiondiv1_n. pose proof Domdiv1_n. 
  pose proof Randiv1_n. split; auto. 
Qed.

Fact Vaulediv1_n : ∀ n, n ∈ Nat -> div1_n[n] = 1/NtoR n.
Proof.
  intros. pose proof Functiondiv1_n. pose proof Domdiv1_n. pose proof Randiv1_n. 
  pose proof H as H'. rewrite <- H1 in H. New H. apply Property_Value in H3; 
  auto. assert([n, 1 / NtoR n] ∈ div1_n).
  { unfold div1_n. appA2G; auto. assert(Ensemble n); unfold Ensemble; eauto.
    assert(Ensemble (1 / NtoR n)); unfold Ensemble; eauto. }
  unfold Function in H0. destruct H0. apply (H5 n div1_n [n] (1/NtoR n)); auto.
Qed.

Definition div1_2n := \{\ λ a b, a ∈ Nat /\ b = (1/((1 + 1) · NtoR a)) \}\.

Fact Functiondiv1_2n : Function (div1_2n).
Proof.
  intros. red. split.
  - apply poisre.
  - intros. apply AxiomII' in H; apply AxiomII' in H0; deand. subst. auto.
Qed.

Fact Domdiv1_2n : dom(div1_2n) = Nat.
Proof.
    apply AxiomI; split. 
  + intros. New H. unfold div1_2n in H0. appA2H H0. destruct H1. appA2H H1. 
    destruct H2, H2, H2, H3. New H0. apply MKT49b in H1. destruct H1. apply 
    (MKT55 z x x0 x1) in H1; auto. apply H1 in H2. destruct H2. subst; auto.
  + intros. unfold div1_2n. appA2G. assert (Ensemble z); unfold Ensemble; eauto.
    assert (Ensemble ((1 + 1) · (NtoR z))); unfold Ensemble; eauto.
    assert (Ensemble (1/(1 + 1))); unfold Ensemble; eauto.
    assert (Ensemble (1/(NtoR z))); unfold Ensemble; eauto.
    assert (Ensemble 1); unfold Ensemble; eauto.
    assert (1 ∈ RC); auto.
    assert (((1 + 1) · NtoR z) ∈ RC); auto.  
    assert ((1 / ((1 + 1) · NtoR z)) ∈ RC); auto.
    assert (Ensemble (1 / ((1 + 1) · NtoR z))); unfold Ensemble; eauto.
    exists(1/((1 + 1) · NtoR z)). appA2G. 
Qed.

Fact Randiv1_2n : ran( div1_2n) ⊂ RC.
Proof.
  unfold Included. intros. New H. unfold div1_n in H0. appA2H H0. destruct H1. 
  appA2H H1. destruct H2, H2, H2, H3. New H0. apply MKT49b in H1. destruct H1. 
  apply (MKT55 x z x0 x1) in H1; auto. apply H1 in H2. destruct H2. subst; auto.
Qed. 

Fact Seqdiv1_2n : IsSeq (div1_2n).
Proof.
  intros. red. pose proof Functiondiv1_2n. pose proof Domdiv1_2n. 
  pose proof Randiv1_2n. split; auto. 
Qed. 


Fact Vaulediv1_2n : ∀ n, n ∈ Nat -> div1_2n[n] = (1/((1 + 1) · NtoR n)) .
Proof.
  intros. pose proof Functiondiv1_2n. pose proof Domdiv1_2n. pose proof 
  Randiv1_2n. pose proof H as H'. rewrite <- H1 in H. New H. apply 
  Property_Value in H3; auto. assert([n, 1/((1 + 1) · NtoR n)] ∈ div1_2n).
  { unfold div1_2n. appA2G; auto. assert(Ensemble n); unfold Ensemble; eauto.
    assert (1 ∈ RC); auto. assert (((1 + 1) · NtoR n) ∈ RC); auto.  
    assert ((1 / ((1 + 1) · NtoR n)) ∈ RC). { apply divRc3; auto. }
    assert(Ensemble (1/((1 + 1) · NtoR n))); unfold Ensemble; eauto. }
  unfold Function in H0. destruct H0. 
  apply (H5 n div1_2n [n] (1/((1 + 1) · NtoR n))); auto.
Qed.

Definition exp2n f := IsSeq f /\ (∀ n, n ∈ Nat -> f[n] = (1+1) ^ n).

Fact exp2n1 : ∀ f n, n ∈ Nat -> exp2n f -> f[n] > 0.
Proof.
  intros. red in H0. destruct H0. New H. apply H1 in H2. clear H1.
  rewrite H2. apply exp2ng0; auto.
Qed.

Definition div1_2expn := \{\ λ a b, a ∈ Nat /\ b = (1 /((1 + 1) ^ a)) \}\.

Fact Functiondiv1_2expn : Function (div1_2expn).
Proof.
  intros. red. split.
  - apply poisre.
  - intros. apply AxiomII' in H; apply AxiomII' in H0; deand. subst. auto.
Qed.

Fact Domdiv1_2expn : dom(div1_2expn) = Nat.
Proof.
  apply AxiomI; split. 
  + intros. New H. unfold div1_2expn in H0. appA2H H0. destruct H1. appA2H H1. 
    destruct H2, H2, H2, H3. New H0. apply MKT49b in H1. destruct H1. apply 
    (MKT55 z x x0 x1) in H1; auto. apply H1 in H2. destruct H2. subst; auto.
  + intros. unfold div1_2expn. appA2G. assert (Ensemble z); unfold Ensemble; 
    eauto. assert (1 ∈ RC); auto. assert (((1 + 1) ^ z) ∈ RC); auto.
    assert ((1 / ((1 + 1) ^ z)) ∈ RC). { apply divRc3; auto. }
    assert (Ensemble (1 / ((1 + 1) ^ z))); unfold Ensemble; eauto.
    exists(1/((1 + 1) ^ z)). appA2G.
Qed. 

Fact Randiv1_2expn : ran( div1_2expn) ⊂ RC.
Proof.

  unfold Included. intros. New H. unfold div1_n in H0. appA2H H0. destruct H1. 
  appA2H H1. destruct H2, H2, H2, H3. New H0. apply MKT49b in H1. destruct H1. 
  apply (MKT55 x z x0 x1) in H1; auto. apply H1 in H2. destruct H2. subst; auto.
Qed.

Fact Seqdiv1_2expn : IsSeq (div1_2expn).
Proof.
  intros. red. pose proof Functiondiv1_2expn. pose proof Domdiv1_2expn. 
  pose proof Randiv1_2expn. split; auto.
Qed.

Fact Vaulediv1_2expn : ∀ n, n ∈ Nat -> div1_2expn[n] = (1 /((1 + 1) ^ n)).
Proof.
  intros. pose proof Functiondiv1_2expn. pose proof Domdiv1_2expn. 
  pose proof Randiv1_2expn. pose proof H as H'. rewrite <- H1 in H. New H. 
  apply Property_Value in H3; auto. assert (((1 + 1) ^  n) ∈ RC); auto. 
  assert ((1 / ((1 + 1) ^ n)) ∈ RC). { apply divRc3; auto. }
  assert (Ensemble (1 / ((1 + 1) ^ n))); unfold Ensemble; eauto.
  assert([n, (1 /((1 + 1) ^ n))] ∈ div1_2expn).
  { unfold div1_n. appA2G; auto. } 
  unfold Function in H0. destruct H0. 
  apply (H8 n div1_2expn [n] (1 /((1 + 1) ^ n))) in H7; auto.
Qed.

Fact divRC1' : ∀ x y, x ∈ PRC -> y ∈ PRC -> (x / y) ∈ PRC.
Proof.
  intros. pose proof twoprc. reqa2. auto.
Qed.

Fact divRC1 : ∀ x y, x ∈ RC -> y ∈ RC -> x > 0 -> y > 0 -> (x / y) > 0.
Proof. 
  intros. assert(x / y ∈ RC); auto. apply FAT169a' in H1; auto. 
  apply FAT169a' in H2; auto. apply FAT169a; auto. apply divRC1'; auto.
Qed.

Fact divRp7' : ∀ x y, x ∈ RC -> y ∈ RC -> y <> 0 -> y · (x / y) = x.
Proof.
  intros. rewrite FAT194; auto. apply divRp7; auto. 
Qed.

Theorem FAT195a' : ∀ X, X ∈ RC -> 1 · X = X.
Proof.
  intros. rewrite FAT194; auto. apply FAT195a; auto.
Qed.

Fact divRC2 : ∀ x y, x ∈ RC -> y ∈ RC -> x > 0 -> y > 0 -> x > y 
  -> 1 / x < 1 / y.
Proof.
  intros. New H1. New H2. pose proof (divRC1 1 x). pose proof (divRC1 1 y).
  apply H6 in H4; auto. apply H7 in H5; auto. clear H6 H7.
  apply (FAT203a x y (1/x)) in H3; auto. apply xg0 in H1; auto. 
  rewrite (divRp7' 1 x) in H3; auto. apply (FAT203a 1 (y · (1 / x)) (1 / y)) in 
  H3; auto. rewrite (FAT195a' (1 / y)) in H3; auto. rewrite FAT194 in H3; auto. 
  rewrite <- FAT199 in H3; auto. rewrite (FAT194 (1 / y) y) in H3; auto. 
  apply xg0 in H2; auto.
  rewrite (divRp7' 1 y) in H3; auto. rewrite FAT195a' in H3; auto.
Qed.

Fact divRC3 : ∀ x y, x ∈ RC -> y ∈ RC -> x <> 0 -> (x · y) · (1 / x) = y.
Proof. 
  intros. rewrite (FAT194 x y); auto. 
  assert((1 / x) ∈ RC). { apply divRc3; auto. }
  rewrite (FAT199 y x (1 / x)); auto. rewrite (divRp7' 1 x); auto. 
  apply FAT195a; auto.
Qed.

Fact divRC3' : ∀ x y, x ∈ RC -> y ∈ RC -> x <> 0 -> (y · x) · (1 / x) = y.
Proof. 
  intros. rewrite (FAT194 y x); auto. apply divRC3; auto.
Qed.

Fact divRC2' : ∀ x y, x ∈ RC -> y ∈ RC -> x > 0 -> y > 0 -> 1 / x < 1 / y 
  -> x > y.
Proof.
  intros. New H1. New H2. pose proof (divRC1 1 x). pose proof (divRC1 1 y).
  apply H6 in H4; auto. apply H7 in H5; auto. clear H6 H7.
  apply (FAT203a (1/y) (1/x) (x · y)) in H3; auto. apply xg0 in H1, H2; auto. 
  rewrite (FAT194 (1 / x) (x · y)), (divRC3 x y) in H3; auto. 
  rewrite (FAT194 (1 / y) (x · y)), (divRC3' y x) in H3; auto.
Qed.

Fact divRC3min : ∀ x y, x ∈ RC -> y ∈ RC -> x <> 0 -> -(x · y) · (1 / x) = -y.
Proof. 
  intros. rewrite (FAT194 x y); auto. 
  assert((1 / x) ∈ RC). { apply divRc3; auto. }
  rewrite <- (FAT197a y x); auto. rewrite (FAT199 (-y) x (1 / x)); auto. 
  rewrite (divRp7' 1 x); auto. apply FAT195a; auto.
Qed.

Fact divRC4 : ∀ x y, x ∈ RC -> y ∈ RC -> y <> 0 -> x · (1 / y) = x / y.
Proof. 
  intros. pose proof divRp7. New H0.
  apply (H2 x y) in H3; auto.
  assert(x · (1 / y) = (x / y) · y · (1 / y)).
  { rewrite H3; auto. }
  rewrite H4. rewrite (FAT194 (x / y) y); auto. apply (divRC3 y (x / y)); auto.
Qed.

Fact mulEql' : ∀ x y z, x ∈ RC -> y ∈ RC -> z ∈ RC -> z <> 0 -> x · z = y · z 
  -> x = y.
Proof.
  intros. assert(y · z ∈ RC); auto. assert(x · z ∈ RC); auto.
   apply (mulEql (x · z) (y · z) (1/z)) in H3; auto. 
   rewrite (divRC3' z x) in H3; auto. rewrite (divRC3' z y) in H3; auto.
Qed.

Global Hint Resolve mulEql': core. 

Fact divRp6' : ∀ x, x ∈ RC -> x <> 0 -> x · (1 / x) = 1.
Proof.
  intros. rewrite (divRC4 x x); auto. apply divRp6; auto.
Qed.

Fact divRC5 : ∀ x y, x ∈ RC -> y ∈ RC -> x <> 0 -> y <> 0 -> 
  1 / (x · y) = (1 / x) · (1 / y).
Proof.
  intros. assert(x · y ≠ 0). { apply xynot0; auto. }
  apply (mulEql' (1 / (x · y)) ((1 / x) · (1 / y)) (x · y)); auto.
  rewrite (divRp7 1 (x · y)), <- (FAT199 ((1 / x) · (1 / y)) x y); auto.
  assert((((1 / x) · (1 / y)) · x) = 1 / y).
  { rewrite (FAT194 ((1 / x) · (1 / y)) x); auto. rewrite <- (FAT199 x (1 / x) 
    (1 / y)); auto. rewrite (divRp6' x); auto. apply FAT195a'; auto. }
  rewrite H4. rewrite (divRp7 1 y); auto.
Qed.

Fact divRC6 : ∀ x y z, x ∈ RC -> y ∈ RC -> z ∈ RC -> y <> 0 -> z <> 0 -> 
  x / y / z = x / (y · z).
Proof.
  intros. rewrite <- (divRC4 (x / y) z); auto. New H3. 
  apply (xynot0 y z) in H3; auto. rewrite <- (divRC4 x (y · z)); auto. 
  rewrite (divRC5 y z); auto. rewrite <- (divRC4 x y); auto. 
  rewrite (FAT199 x (1 / y) (1 / z)); auto.
Qed.

Theorem ArchimedeanLemma5 : ∃ x, x ∈ RC /\ Limit div1_n x.
Proof.
  intros. pose proof Functiondiv1_n. pose proof Seqdiv1_n. 
  apply (MCTdown div1_n 0).
  - red. split; auto. intros. red. left. New H1. apply Vaulediv1_n in H4.
    New H2. apply Vaulediv1_n in H5. rewrite H4. rewrite H5. apply divRC2; auto.
  - red. pose proof zinr. split; auto. split; auto. intros. 
    rewrite Vaulediv1_n; auto.
    New H2. assert(1 > 0); auto. assert(NtoR n > 0); auto. red. left.
    apply divRC1; auto.
Qed.
 
Theorem ArchimedeanLemma5' : ∃ x, x ∈ RC /\ Limit div1_2n x.
Proof.
  intros. pose proof Functiondiv1_2n. 
  pose proof Seqdiv1_2n. apply (MCTdown div1_2n 0).
  - red. split; auto. intros. red. left. New H1. apply Vaulediv1_2n in H4.
    New H2. apply Vaulediv1_2n in H5. rewrite H4. rewrite H5. 
    assert((1 + 1) · NtoR n < (1 + 1) · NtoR m). { apply dou2; auto. }
    apply divRC2; auto.
  - red. pose proof zinr. split; auto. split; auto. intros. 
    rewrite Vaulediv1_2n; auto.
    New H2. assert(1 > 0); auto. assert(NtoR n > 0); auto. red. left.
    apply divRC1; auto.
Qed.

Lemma Limitun :∀ S x y, Limit S x -> Limit S y -> x = y.
Proof.
  intros. red in H. red in H0. destruct H as [H []]. destruct H0 as [_ []].
  New H1. apply (@FAT167 x y) in H4; auto. 
  destruct H4; auto. destruct H4.
  + assert(exists z, z ∈ RC /\ z = x - y).
    { exists (x - y). auto. } destruct H5 as [z []].
    assert(z/(1+1) ∈ RC); auto. New H7. New H7. 
    assert(z > 0). 
    { subst. apply (FAT188a2 x y (-y)) in H4; auto. rewrite xminx in H4; auto. }
    assert(z/(1+1) > 0). { apply divRC1; auto. }
    apply H2 in H8; auto. apply H3 in H9; auto. destruct H8, H9, H8, H9.
    assert(exists n, n ∈ Nat /\ n = (x0 + x1)%Nat). 
    { exists (x0 + x1)%Nat; auto. }
    destruct H14 as [n[]]. New H14. New H14.
    assert(NtoR x0 < NtoR n). 
    { subst. apply NtoR3; auto. apply (@FAT18 x0 x1) in H8; auto. }
    assert(NtoR x1 < NtoR n). 
    { subst. apply NtoR3; auto. New H8. apply (@FAT18 x1 x0) in H8; auto. 
      rewrite FAT6 in H8; auto. }
    apply H12 in H16; auto. apply H13 in H17; auto. New H14. 
    apply (anRC S) in H20; auto. apply Ab1 in H16; auto. apply Ab1 in H17; auto.
    destruct H16. destruct H17. apply (@FAT189 (S [n] - x) (- (z / (1 + 1))) 
    (z / (1 + 1)) (S [n] - y)) in H16; auto. 
    apply (FAT188a2 (S [n] - x + z / (1 + 1)) (- (z / (1 + 1)) + (S [n] - y)) 
    (z / (1 + 1))) in H16; auto. New H5. apply (halfsum z) in H23.
    assert(S [n] - x + z / (1 + 1) + z / (1 + 1) = (S [n] - x + z)).
    { rewrite (FAT186' (S [n] - x) (z / (1 + 1)) (z / (1 + 1))); auto.
      rewrite H23. auto. }
    rewrite H24 in H16. New H7. apply (xminx' (z / (1 + 1))) in H25.
    rewrite (MincEx6 (z / (1 + 1)) (S [n] - y)) in H16; auto.
    rewrite (FAT186'  S[n] (- x) z) in H16; auto.
    rewrite (@FAT175 S[n] (- x + z)) in H16; auto.
    rewrite (@FAT175 S[n] (-y)) in H16; auto.
    apply (FAT188c1 (- y) (- x + z) (S [n])) in H16; auto.
    rewrite H6 in H16. rewrite (MincEx3 y x) in H16; auto.
    apply xlx in H16; auto. contradiction.
  + assert(exists z, z ∈ RC /\ z = y - x). { exists (y - x). auto. } 
    destruct H5 as [z []]. assert(z/(1+1) ∈ RC); auto. New H7. New H7. 
    assert(z > 0). 
    { subst. apply (FAT188a2 y x (-x)) in H4; auto. rewrite xminx in H4; auto. }
    assert(z/(1+1) > 0). { apply divRC1; auto. }
    apply H2 in H8; auto. apply H3 in H9; auto. destruct H8, H9, H8, H9.
    assert(exists n, n ∈ Nat /\ n = (x0+x1)%Nat). { exists (x0+x1)%Nat; auto. }
    destruct H14 as [n[]]. New H14. New H14.
    assert(NtoR x0 < NtoR n). 
    { subst. apply NtoR3; auto. apply (@FAT18 x0 x1) in H8; auto. }
    assert(NtoR x1 < NtoR n). 
    { subst. apply NtoR3; auto. New H8. apply (@FAT18 x1 x0) in H8; auto. 
      rewrite FAT6 in H8; auto. }
    apply H12 in H16; auto. apply H13 in H17; auto. New H14. apply (anRC S) in 
    H20; auto. apply Ab1 in H16; auto. apply Ab1 in H17; auto. destruct H16. 
    destruct H17. apply (@FAT189 (S [n] - y) (- (z / (1 + 1))) (z / (1 + 1)) 
    (S [n] - x)) in H17; auto. apply (FAT188a2 (S [n] - y + z / (1 + 1)) 
    (- (z / (1 + 1)) + (S [n] - x)) (z / (1 + 1))) in H17; auto.
    New H5. apply (halfsum z) in H23.
    assert(S [n] - y + z / (1 + 1) + z / (1 + 1) = (S [n] - y + z)).
    { rewrite (FAT186' (S [n] - y) (z / (1 + 1)) (z / (1 + 1))); auto.
      rewrite H23. auto. }
    rewrite H24 in H17. New H7. apply (xminx' (z / (1 + 1))) in H25.
    rewrite (MincEx6 (z / (1 + 1)) (S [n] - x)) in H17; auto.
    rewrite (FAT186'  S[n] (- y) z) in H17; auto.
    rewrite (@FAT175 S[n] (- y + z)) in H17; auto.
    rewrite (@FAT175 S[n] (-x)) in H17; auto.
    apply (FAT188c1 (- x) (- y + z) (S [n])) in H17; auto.
    rewrite H6 in H17. rewrite (MincEx3 x y) in H17; auto.
    apply xlx in H17; auto. contradiction.
Qed.

Fact NtoR5 : ∀ n, n ∈ Nat -> NtoR ((One + One) · n)%Nat = (1 + 1) · NtoR n.
Proof.
  intros. rewrite (FAT30b One One n); auto. 
  rewrite <- (NtoR2 (One · n)%Nat (One · n)%Nat); auto.
  rewrite <- (NtoRM One n); auto.
  rewrite NtoROne; auto. rewrite FAT195a'; auto.
  rewrite FAT194; auto. rewrite FAT201a; auto.
  rewrite FAT195a; auto. 
Qed.

Fact NtoR6 : NtoR (One + One)%Nat = (1 + 1).
Proof.
  intros. rewrite <- (NtoR2 (One) (One)); auto.
Qed.

Theorem ArchimedeanLemma6 : Limit div1_n 0.
Proof.
  pose proof ArchimedeanLemma5. destruct H, H.
  pose proof Functiondiv1_2n. pose proof Seqdiv1_2n. 
  assert(Limit div1_2n x).
  { red. split; auto. split; auto. intros. red in H0. destruct H0, H5.
    pose proof H3 as H3'. apply H6 in H3; auto. destruct H3 as [N [] ].
    exists (N). split; auto. intros.
    assert(((One + One) · n)%Nat ∈ Nat); auto.
    assert(NtoR N < NtoR ((One + One) · n)%Nat).
    { rewrite NtoR5; auto.
      apply (@FAT171 (NtoR N) (NtoR n) ((1 + 1) · NtoR n)); auto.
      apply ng0 in H8. apply (dou1 (NtoR n)); auto. }
    apply H7 in H10; auto.
    rewrite Vaulediv1_2n; auto. rewrite Vaulediv1_n in H10; auto.
    assert(NtoR ((One + One) · n)%Nat = ((1 + 1) · NtoR n)). 
    { rewrite NtoR5; auto. }
    rewrite H12 in H10. auto. }
  assert(Limit div1_2n (x/(1+1))).
  { red in H0. destruct H0, H4. red. split; auto. split; auto. intros.
    New H6. assert((1 + 1) · ε ∈ RC); auto.
    assert((1 + 1) · ε > 0); auto.
    apply H5 in H9; auto. destruct H9 as [N[]]. exists N. split; auto.
    intros. New H10. assert(n ∈ Nat); auto.
    New H13.
    apply H11 in H15; auto.
    rewrite Vaulediv1_2n; auto. rewrite Vaulediv1_n in H15; auto.
    assert((1 / (1 + 1)) > 0); auto.
    apply Ab1; auto. apply Ab1 in H15; auto. destruct H15. split.
    + apply (FAT203a (1 / NtoR n - x) (- ((1 + 1) · ε)) (1 / (1 + 1))) in H15; 
      auto. rewrite (divRC3min (1 + 1) ε) in H15; auto. 
      rewrite (divRC4 (1 / NtoR n - x) (1 + 1)) in H15; auto.
      rewrite <- (divRp4 (1 / NtoR n) (1 + 1) (- x)) in H15; auto. New H12.
      apply nnot0 in H19. rewrite (divRC6 1 (NtoR n) (1 + 1)) in H15; auto. 
      rewrite (FAT194 (NtoR n) (1 + 1)) in H15; auto.  
      rewrite <- (divRp3  x (1 + 1)); auto.
    + apply (FAT203a ((1 + 1) · ε) (1 / NtoR n - x) (1 / (1 + 1))) in H18; auto.
      rewrite (divRC3 (1 + 1) ε) in H18; auto. 
      rewrite (divRC4 (1 / NtoR n - x) (1 + 1)) in H18; auto.
      rewrite <- (divRp4 (1 / NtoR n) (1 + 1) (- x)) in H18; auto. New H12.
      apply nnot0 in H19. rewrite (divRC6 1 (NtoR n) (1 + 1)) in H18; auto. 
      rewrite (FAT194 (NtoR n) (1 + 1)) in H18; auto.
      rewrite <- (divRp3  x (1 + 1)); auto. }
  assert(x = x / (1 + 1)).
  { apply (Limitun div1_2n x (x / (1 + 1))) in H4; auto. }
  apply (mulEql x (x / (1 + 1)) (1 + 1)) in H5; auto.
  rewrite (divRp7 x (1+1)) in H5; auto. rewrite FAT201a in H5; auto.
  rewrite FAT195a in H5; auto. apply (FAT188b2 (x+x) x (-x)) in H5; auto.
  rewrite FAT186' in H5; auto. rewrite xminx in H5; auto. 
  rewrite AddRpb in H5; auto. subst; auto.
Qed.

Lemma ArchimedeanLemma1 :∀ x, x ∈ RC -> exists n, n ∈ Nat /\ NtoR n > x.
Proof.
  intros. destruct (@FAT167 x 0) as [H1 | [H1 | H1]]; auto.
  - subst. exists One. split; auto.
  - pose proof ArchimedeanLemma6. destruct H0, H2.
    assert(1/x > 0). { apply divRC1; auto. }
    New H4. apply H3 in H5; auto. destruct H5 as[N []]. 
    assert(((One + One) · N)%Nat ∈ Nat); auto.
    assert(NtoR N < NtoR ((One + One) · N)%Nat).
    { rewrite NtoR5; auto. apply dou1; auto. }
    exists((One + One) · N)%Nat. split; auto. New H7. apply H6 in H9; auto.
    rewrite Vaulediv1_n in H9; auto. rewrite MinRpb in H9; auto.
    assert(NtoR ((One + One) · N)%Nat > 0). { apply ng0; auto. }
    apply (divRC1 1 (NtoR ((One + One) · N)%Nat)) in H10; auto.
    apply AbPRC in H10; auto. rewrite H10 in H9. apply divRC2'; auto.
  - exists One. split; auto. apply (@FAT171 x 0 (NtoR One)); auto. 
    apply (ng0 One); auto.
Qed.

Fact z1 : ∀ x, x ∈ RC -> ~ x ≠ 0 -> x = 0.
Proof.
  intros. Absurd. red in H0. apply H0 in H1; auto. contradiction.
Qed.

Fact z2 : ∀ x, x ∈ RC -> x ≠ 0 -> 1 / x ≠ 0.
Proof.
  intros. Absurd. apply z1 in H1; auto. apply (divRp8 1 x) in H1; auto.
Qed.

Fact divRC7 : ∀ x, x ∈ RC -> x ≠ 0 -> 1 / (1 / x) = x.
Proof.
  intros. 
  assert(1 / x ≠ 0). { apply z2; auto. }
  assert(1 / (1 / x) ∈ RC). { apply divRc3; auto. }
  apply (mulEql' (1 / (1 / x)) x (1 / x)); auto. 
  rewrite divRp6'; auto. rewrite (divRp7 1 (1 / x)); auto.
Qed.

Fact dou3 : ∀ x, x ∈ RC -> (1 + 1) · x = x + x.
Proof.
  intros. rewrite (FAT201b x 1 1); auto. rewrite (FAT195a'); auto.
Qed.

Fact dou3' : ∀ x, x ∈ RC -> x · (1 + 1) = x + x.
Proof.
  intros. rewrite (FAT194 x (1 + 1)); auto. apply dou3; auto.
Qed.

Global Hint Resolve dou3: core.

Fact exp2ngn1 : ∀ n, n ∈ Nat -> (1 + 1) ^ n ≥ NtoR n + 1.
Proof.
  intros. 
  cut (∀ n, n ∈ Nat -> (1 + 1) ^ n ≥ NtoR n + 1); auto.
  apply Mathematical_Induction_Nat.
  - rewrite P_Ex2; auto. rewrite NtoROne. red. right; auto.
  - intros. rewrite Exp_mult1; auto. rewrite <- NtoR2; auto. rewrite NtoROne.
    assert((1 + 1) ^ k ∈ RC); auto.
    apply (dou2' ((NtoR k) + 1) ((1 + 1) ^ k)) in H1; auto.
    rewrite (FAT194 (1 + 1) ((1 + 1) ^ k)) in H1; auto. apply (T173 
    (NtoR k + 1 + 1) ((1 + 1) · (NtoR k + 1)) ((1 + 1) ^ k · (1 + 1))); auto.
    rewrite (dou3 (NtoR k + 1)); auto.
    New H0. apply ng0 in H3. apply (FAT188a2 (NtoR k) 0 1) in H3; auto.
    rewrite AddRpa in H3; auto.
    assert(NtoR k + 1 ≤ NtoR k + 1). { red. right; auto. }
    assert(1 ≤ NtoR k + 1). { red. left; auto. }
    apply(@FAT191b (NtoR k + 1) (NtoR k + 1) 1 (NtoR k + 1)); auto.
Qed.

Fact add0 : 0 < 1.
Proof.
  intros. pose proof NtoROne. rewrite <- H. apply (ng0 One); auto.
Qed.

Global Hint Resolve add0 : core.

Fact FAT168a' : ∀ x y, x ∈ RC -> y ∈ RC -> x < y -> y > x.
Proof.
  intros. auto.
Qed.

Global Hint Resolve FAT168a' : core.

Fact add1 : ∀ x, x ∈ RC -> x + 1 > x.
Proof.
  intros. apply FAT168a'; auto. 
Qed.

Global Hint Resolve add1 : core.

Fact exp2ngn : ∀ n, n ∈ Nat -> (1 + 1) ^ n > NtoR n.
Proof.
  intros. pose proof exp2ngn1 n. New H. apply H0 in H1.
  assert((NtoR n) + 1 > (NtoR n)); auto.
  apply(FAT172 (NtoR n) (NtoR n + 1) ((1 + 1) ^ n)); auto.
Qed.

Theorem ArchimedeanLemma7 : Limit div1_2expn 0.
Proof.
  pose proof Functiondiv1_2expn. pose proof Seqdiv1_2expn. 
  pose proof ArchimedeanLemma1. 
  red. split; auto. split; auto. intros. 
  assert(1/ε ∈ RC). { apply divRc1; auto. }
  assert(1/ε > 0). { apply divRC1; auto. }
  New H4. apply H1 in H6. destruct H6 as [N[]].
  exists N. split; auto. intros.
  
  assert((1 + 1) ^ n > 0). { apply exp2ng0; auto. }
  assert(1 / (1 + 1) ^ n ∈ RC). { apply divRc1; auto. }
  assert(1 / (1 + 1) ^ n > 0). { apply divRC1; auto. }
  rewrite Vaulediv1_2expn; auto. rewrite MinRpb; auto. 
  rewrite AbPRC; auto. 
  pose proof exp2ngn n. New H8; apply H13 in H14. apply divRC2 in H14; auto. 
  apply divRC2 in H7; auto. 
  New H2. New H3. apply xg0 in H16; auto. rewrite divRC7 in H7; auto.
  apply divRC2 in H9; auto.
  apply (@FAT171 (1 / (1 + 1) ^ n) (1 / NtoR n) (1 / NtoR N)) in H14; auto.
  apply (@FAT171 (1 / (1 + 1) ^ n) (1 / NtoR N) ε) in H14; auto.  
Qed.