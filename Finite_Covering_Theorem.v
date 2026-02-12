(**********************************************************************)
(*     This is part of Real_Completeness, it is distributed under     *)
(*    the terms of the GNU Lesser General Public License version 3    *)
(*             (see file LICENSE for more details)                    *)
(*                                                                    *)
(*                     Copyright 2026-2031                            *)
(*              Ce Zhang, Guowei Dou and ωensheng Yu                  *)
(**********************************************************************)

Require Export Nested_Closed_Interval_Theorem.

Notation "］ a , b ［" := (\{ λ x, x ∈ RC /\ a ∈ RC /\ b ∈ RC 
  /\ a < x /\ x < b \}) (at level 5, a at level 0, b at level 0) : RC_scope.

(* 闭区间 *)
Notation "［ a , b ］" := (\{ λ x, x ∈ RC /\ a ∈ RC /\ b ∈ RC 
  /\ a ≤ x /\ x ≤ b \}) (at level 5, a at level 0, b at level 0) : RC_scope.
  

Definition IsOpenIntervalFamily F := ∀ n, n ∈ F -> (∃ a b, n = ］ a , b ［).
Definition OpenCover a b F := a ∈ RC /\ b ∈ RC /\ IsOpenIntervalFamily F 
  /\ a < b /\ (∀ c, c ∈ ［a , b］ -> (∃ h, h ∈ F /\ c ∈ h)).
Definition FinCover a b F := a ∈ RC /\ b ∈ RC /\ IsOpenIntervalFamily F 
  /\ a < b /\ (∃ f, f ⊂ F /\ Finite f /\ OpenCover a b f).
Definition InfinCover_Only a b F := OpenCover a b F /\ ~ FinCover a b F.

Fact aver_Cor0 : ∀ x, x ∈ RC -> x = (x + x) · (1 / (1 + 1)).
Proof.
  intros. rewrite <- dou3; auto. rewrite divRC3; auto.
Qed.

Fact aver_Cor1 : ∀ x y z, x ∈ RC -> y ∈ RC -> z ∈ RC -> z < x -> z < y 
  -> z < (x + y) / (1 + 1).
Proof.
  intros. assert ((z + z) < (x + y)). { apply FAT189; auto. }
  apply (FAT203a (x + y) (z + z) (1 / (1 + 1))) in H4; auto.
  rewrite divRC4 in H4; auto. rewrite <- aver_Cor0 in H4; auto.
Qed.

Fact aver_Cor2 : ∀ x y z, x ∈ RC -> y ∈ RC -> z ∈ RC -> z > x -> z > y 
  -> (x + y) / (1 + 1) < z.
Proof.
  intros. assert ((z + z) > (x + y)). { apply FAT189; auto. }
  apply (FAT203a (z + z) (x + y) (1 / (1 + 1))) in H4; auto.
  rewrite <- aver_Cor0 in H4; auto. rewrite divRC4 in H4; auto. 
Qed.

Fact OpenInterval_Cor0ab : ∀ a b z, z ∈ RC -> z ∈ ］ a , b ［ -> a < b.
Proof.
  intros. appA2H H0. destruct H1, H2, H3, H4. apply (@FAT171 a z b); auto.
Qed.

Fact OpenInterval_Cor0a : ∀ a b z, z ∈ RC -> z ∈ ］ a , b ［ -> a < z.
Proof.
  intros. appA2H H0. destruct H1, H2, H3, H4; auto.
Qed.

Fact OpenInterval_Cor0b : ∀ a b z, z ∈ RC -> z ∈ ］ a , b ［ -> z < b.
Proof.
  intros. appA2H H0. destruct H1, H2, H3, H4; auto.
Qed.

Fact OpenInterval_Cor1 : ∀ a b c d, a ∈ RC -> b ∈ RC -> c ∈ RC -> d ∈ RC 
  -> a < b -> c < d -> ］ a , b ［ = ］ c , d ［ -> a = c /\ b = d.
Proof.
  intros. 
  assert(∀z : Class,z ∈ ］ a, b ［ <-> z ∈ ］ c, d ［). 
  { intros. split; intros.
    + rewrite H5 in H6; auto.
    + rewrite <- H5 in H6; auto. }
  pose proof(@FAT167 a c) H H1. pose proof(@FAT167 b d) H0 H2.
  assert(((a + c) / (1 + 1)) ∈ RC) as averac_in_RC; auto.
  assert(Ensemble ((a + c) / (1 + 1))) as averac_Ensemble.
  { unfold Ensemble. exists RC; auto. }
  assert(((c + a) / (1 + 1)) ∈ RC) as averca_in_RC; auto.
  assert(Ensemble ((c + a) / (1 + 1))) as averca_Ensemble.
  { unfold Ensemble. exists RC; auto. }
  assert(((b + d) / (1 + 1)) ∈ RC) as averbd_in_RC; auto.
  assert(Ensemble ((b + d) / (1 + 1))) as averbd_Ensemble.
  { unfold Ensemble. exists RC; auto. }
  assert(((d + b) / (1 + 1)) ∈ RC) as averdb_in_RC; auto.
  assert(Ensemble ((d + b) / (1 + 1))) as averdb_Ensemble.
  { unfold Ensemble. exists RC; auto. }
  assert(((a + b) / (1 + 1)) ∈ RC) as averab_in_RC; auto.
  assert(Ensemble ((a + b) / (1 + 1))) as averab_Ensemble.
  { unfold Ensemble. exists RC; auto. }
  assert(((c + d) / (1 + 1)) ∈ RC) as avercd_in_RC; auto.
  assert(Ensemble ((c + d) / (1 + 1))) as avercd_Ensemble.
  { unfold Ensemble. exists RC; auto. }
  destruct H7 as [H7 | []]; destruct H8 as [H8 | []]. 
  - auto.
  - split; auto. pose proof H6 ((d + b)/(1+1)) as [].
    New H8; apply (aver2 d b) in H11 as []; auto. 
    assert(((d + b)/(1+1)) ∈ ］ a, b ［).
    { appA2G. repeat split; auto. subst. apply aver_Cor1; auto. }
    apply H9 in H13. apply OpenInterval_Cor0b in H13; auto.
    apply (@lgRf ((d + b) / (1 + 1)) d) in H13; auto. contradiction.
  - split; auto. pose proof H6 ((b + d)/(1+1)) as [].
    New H8; apply (aver2 b d) in H11 as []; auto. 
    assert(((b + d)/(1+1)) ∈ ］ c, d ［).
    { appA2G. repeat split; auto. subst. apply aver_Cor1; auto. } 
    apply H10 in H13. apply OpenInterval_Cor0b in H13; auto.
    apply (@lgRf ((b + d) / (1 + 1)) b) in H13; auto. contradiction.
  - split; auto. pose proof H6 ((c + a)/(1+1)) as [].
    New H7; apply (aver2 c a) in H11 as []; auto. 
    assert(((c + a)/(1+1)) ∈ ］ c, d ［).
    { appA2G. repeat split; auto. subst. apply aver_Cor2; auto. }
    apply H10 in H13. apply OpenInterval_Cor0a in H13; auto.
    apply (@lgRf ((c + a) / (1 + 1)) a) in H12; auto. contradiction.
  - TF(d ≤ a).
    + pose proof H6 ((a + b)/(1+1)) as []. 
      New H3; apply (aver2 a b) in H12 as []; auto. 
      assert(((a + b)/(1+1)) ∈ ］ a, b ［).
      { appA2G. }
      apply H10 in H14. apply OpenInterval_Cor0b in H14; auto.
      apply (@FAT171 a ((a + b) / (1 + 1)) d) in H14; auto. destruct H9. 
      apply (@lgRf a d) in H14; auto. contradiction.
      apply (@elRf a d) in H14; auto. contradiction.
    + apply NotleR in H9; auto. pose proof H6 ((c + a)/(1+1)) as [].
      New H7; apply (aver2 c a) in H12 as []; auto. 
      assert(((c + a)/(1+1)) ∈ ］ c, d ［).
      { appA2G. repeat split; auto. subst. apply aver_Cor2; auto. }
      apply H11 in H14. apply OpenInterval_Cor0a in H14; auto.
      apply (@lgRf ((c + a) / (1 + 1)) a) in H13; auto. contradiction.
  - pose proof H6 ((b + d)/(1+1)) as [].
    New H8; apply (aver2 b d) in H11 as []; auto. 
    New H. apply (@FAT171 c a b) in H13; auto.
    assert(((b + d)/(1+1)) ∈ ］ c, d ［).
    { appA2G. repeat split; auto. subst. apply aver_Cor1; auto. } 
    apply H10 in H14. apply OpenInterval_Cor0b in H14; auto.
    apply (@lgRf ((b + d) / (1 + 1)) b) in H14; auto. contradiction.
  - split; auto. pose proof H6 ((a + c)/(1+1)) as [].
    New H7; apply (aver2 a c) in H11 as []; auto. 
    assert(((a + c)/(1+1)) ∈ ］ a, b ［).
    { appA2G. repeat split; auto. subst. apply aver_Cor2; auto. }
    apply H9 in H13. apply OpenInterval_Cor0a in H13; auto.
    apply (@lgRf c ((a + c) / (1 + 1))) in H12; auto. contradiction.
  - pose proof H6 ((d + b)/(1+1)) as [].
    New H8; apply (aver2 d b) in H11 as []; auto. 
    New H1. apply (@FAT171 a c d) in H13; auto.
    assert(((d + b)/(1+1)) ∈ ］ a, b ［).
    { appA2G. repeat split; auto. subst. apply aver_Cor1; auto. } 
    apply H9 in H14. apply OpenInterval_Cor0b in H14; auto.
    apply (@lgRf ((d + b) / (1 + 1)) d) in H14; auto. contradiction.
  - TF(b ≤ c).
    + pose proof H6 ((a + b)/(1+1)) as []. 
      New H3; apply (aver2 a b) in H12 as []; auto. 
      assert(((a + b)/(1+1)) ∈ ］ a, b ［).
      { appA2G. }
      apply H10 in H14. apply OpenInterval_Cor0a in H14; auto.
      apply (@FAT171 c ((a + b) / (1 + 1)) b) in H14; auto. destruct H9. 
      apply (@lgRf c b) in H14; auto. contradiction.
      apply (@elRf c b) in H14; auto. contradiction.
    + apply NotleR in H9; auto. pose proof H6 ((a + c)/(1+1)) as [].
      New H7; apply (aver2 a c) in H12 as []; auto. 
      assert(((a + c)/(1+1)) ∈ ］ a, b ［).
      { appA2G. repeat split; auto. subst. apply aver_Cor2; auto. }
      apply H10 in H14. apply OpenInterval_Cor0a in H14; auto.
      apply (@lgRf ((a + c) / (1 + 1)) c) in H13; auto. contradiction.
Qed.

Definition MathMin := \{\ λ u v, u ∈ (RC × RC) /\ ( ((First u) > (Second u) 
  /\ v = (Second u)) \/ ((First u) ≤ (Second u) /\ v = (First u)) ) \}\.

Fact CartesianRCa: ∀ x, x ∈ RC × RC -> (x) ¹ ∈ RC.
Proof.
  intros. unfold Cartesian in H. appA2H H. destruct H0, H0, H0, H1.
  assert (Ensemble x0); unfold Ensemble; eauto.
  assert (Ensemble x1); unfold Ensemble; eauto.
  apply (MKT54a x0 x1) in H3; auto. rewrite <- H0 in H3. rewrite H3; auto.
Qed.
  
Fact CartesianRCb: ∀ x, x ∈ RC × RC -> (x) ² ∈ RC.
Proof.
  intros. unfold Cartesian in H. appA2H H. destruct H0, H0, H0, H1.
  assert (Ensemble x0); unfold Ensemble; eauto.
  assert (Ensemble x1); unfold Ensemble; eauto.
  apply (MKT54b x0 x1) in H3; auto. rewrite <- H0 in H3. rewrite H3; auto.
Qed.

Fact FunctionMathMin : Function (MathMin).
Proof.
  intros. split; intros. apply poisre. apply AxiomII' in H, H0. 
  New H. destruct H1 as [_ [H1 _]]. 
  New H1. apply CartesianRCa in H1. apply CartesianRCb in H2.
  rename H1 into Hx1. rename H2 into Hx2.
  destruct H as [H[H1[H2 | H2]]], H2, H0 as [H0[H4[H5 | H5]]], H5.
  - subst; auto.
  - apply (@legRf (x) ¹ (x) ²) in H2; auto. contradiction.
  - apply (@legRf (x) ¹ (x) ²) in H2; auto. contradiction.
  - subst; auto.
Qed.


Fact domMathMin : dom(MathMin) = RC × RC.
Proof.
  apply AxiomI; split; intros.
  - apply AxiomII in H as [H[]]. apply AxiomII' in H0 as [_[]]; auto.
  - New H. New H. apply AxiomII in H1 as [H1[x[y[H2[]]]]].
    apply AxiomII; split; auto.
    assert(Ensemble x); unfold Ensemble; eauto.
    assert(Ensemble y); unfold Ensemble; eauto.
    assert(Ensemble z); unfold Ensemble; eauto.
    assert( (First z) = x). { subst. apply MKT54a; auto. }
    assert( (Second z) = y). { subst. apply MKT54b; auto. }
    New H3. apply (@FAT167 x y) in H10; auto.
    destruct H10.
    + exists x. appA2G. exists z. exists x. repeat split; auto.
      right. rewrite H8, H9. split; auto. red. right; auto.
    + destruct H10.
      * exists y. appA2G. exists z. exists y. repeat split; auto.
        left. rewrite H8, H9. split; auto.
      * exists x. appA2G. exists z. exists x. repeat split; auto.
        right. rewrite H8, H9. split; auto. red. left; auto.
Qed.

Fact ranMathMin : ran(MathMin) ⊂ RC.
Proof.
   unfold Included; intros.
  - apply AxiomII in H as [H[]]. apply AxiomII' in H0.
    destruct H0 as [H0[H1]]; auto. destruct H2.
    + destruct H2. rewrite H3. apply CartesianRCb; auto.
    + destruct H2. rewrite H3. apply CartesianRCa; auto.
Qed.
 
Theorem MathMineq : ∀ x y, x ∈ RC -> y ∈ RC -> 
  MathMin [([ x , y ])] = x \/ MathMin [([ x , y ])] = y.
Proof.
  intros. New H. apply (@FAT167 x y) in H1; auto.
  assert([x, y] ∈ dom(MathMin)).
  { pose proof domMathMin. rewrite H2. unfold Cartesian. appA2G. 
    apply MKT49a; unfold Ensemble; eauto. }
  pose proof FunctionMathMin. apply Property_Value in H2; auto. 
  appA2H H2; auto. destruct H4, H4, H4, H5. 
  apply MKT49b in H2. destruct H2. 
  apply (MKT55 ([x, y]) MathMin[[x, y]] x0 x1) in H2; auto. apply H2 in H4.
  destruct H4. destruct H6, H6.
  - right. subst. rewrite H9. apply MKT54b; unfold Ensemble; eauto.
  - left. subst. rewrite H9. apply MKT54a; unfold Ensemble; eauto.
Qed.

Theorem MathMinRC : ∀ x y, x ∈ RC -> y ∈ RC -> MathMin [([ x , y ])] ∈ RC.
Proof.
  intros. pose proof MathMineq. New H. apply (H1 x y) in H2; auto.
  destruct H2; rewrite H2; auto.
Qed.

Fact MathMin1 :∀ x y, x ∈ RC -> y ∈ RC -> MathMin [[x, y]] = x -> x ≤ y.
Proof.
  intros. New H. apply (@FAT167 x y) in H2; auto.
  assert([x, y] ∈ dom(MathMin)).
  { pose proof domMathMin. rewrite H3. unfold Cartesian. appA2G. 
    apply MKT49a; unfold Ensemble; eauto. }
  pose proof FunctionMathMin. apply Property_Value in H3; auto. 
  appA2H H3; auto. destruct H5, H5, H5, H6. 
  apply MKT49b in H3. destruct H3. New H3.
  apply (MKT55 ([x, y]) MathMin[[x, y]] x0 x1) in H9; auto. apply H9 in H5.
  destruct H5.
  assert(Ensemble x0); unfold Ensemble; eauto.
  assert(x1 ∈ RC). { rewrite <- H10.  apply MathMinRC; auto. }
  assert(Ensemble x1); unfold Ensemble; eauto. 
  assert(Ensemble x); unfold Ensemble; eauto.
  assert(Ensemble y); unfold Ensemble; eauto. New H14. New H14.
  apply (MKT54a x y) in H16; auto. 
  apply (MKT54b x y) in H17; auto. rewrite H5 in H16, H17. 
  rewrite H16, H17 in H7. destruct H7, H7.
  - rewrite H1 in H10. subst. red; right; auto.
  - auto.
Qed.

Fact MathMin2 :∀ x y, x ∈ RC -> y ∈ RC -> MathMin [[x, y]] = y -> y ≤ x.
Proof.
  intros. New H. apply (@FAT167 x y) in H2; auto.
  assert([x, y] ∈ dom(MathMin)).
  { pose proof domMathMin. rewrite H3. unfold Cartesian. appA2G. 
    apply MKT49a; unfold Ensemble; eauto. }
  pose proof FunctionMathMin. apply Property_Value in H3; auto. 
  appA2H H3; auto. destruct H5, H5, H5, H6. 
  apply MKT49b in H3. destruct H3. New H3.
  apply (MKT55 ([x, y]) MathMin[[x, y]] x0 x1) in H9; auto. apply H9 in H5.
  destruct H5. assert(Ensemble x0); unfold Ensemble; eauto.
  assert(x1 ∈ RC). { rewrite <- H10.  apply MathMinRC; auto. }
  assert(Ensemble x1); unfold Ensemble; eauto. 
  assert(Ensemble x); unfold Ensemble; eauto.
  assert(Ensemble y); unfold Ensemble; eauto. New H14. New H14.
  apply (MKT54a x y) in H16; auto. 
  apply (MKT54b x y) in H17; auto. rewrite H5 in H16, H17. 
  rewrite H16, H17 in H7. destruct H7, H7.
  - red; left; auto.
  - subst. rewrite <- H1, H18. red; right; auto.
Qed.

Fact Rcase2 : ∀ x y, x ∈ RC -> y ∈ RC -> (x ≤ y \/ y ≤ x).
Proof.
  intros. destruct (@FAT167 x y) as [H' | [H' | H']]; auto.
  + left. red. right; auto.
  + right. red. left; auto.
  + left. red. left; auto.
Qed.

Corollary CoverP1 : ∀ x y cH, FinCover x ((x + y)/(1 + 1)) cH -> 
  FinCover ((x + y)/(1 + 1)) y cH -> FinCover x y cH.
Proof.
  intros; destruct H, H1 as [HR1 H1], H1, H2.
  destruct H0, H4 as [HR2 H4], H4, H5.
  destruct H3 as [R1 []], H7. destruct H6 as [R2 []], H9. New H2.
  apply (@FAT171 x ((x + y) / (1 + 1)) y) in H11; auto.
  red; split; auto. repeat split; auto. 
  exists (R1 ∪ R2); repeat split; auto; intros.
  - red; intros. unfold Union in H12. appA2H H12. destruct H13; auto.
  - apply MKT168; auto.
  - red. intros. red in H4. apply H4. unfold Union in H12. appA2H H12.
    destruct H13; auto.
  - appA2H H12. destruct H13 ,H14, H15, H16. New H13. 
    apply (Rcase2 c ((x + y) / (1 + 1))) in H18; auto. destruct H18.
    * assert (c ∈ ［x , ((x + y) / (1 + 1))］). { appA2G. }
      apply H8 in H19. destruct H19, H19.
      exists x0; split; auto. unfold Union. appA2G.
    * assert (c ∈ ［((x + y) / (1 + 1)) , y］). { appA2G. }
      apply H10 in H19. destruct H19, H19.
      exists x0; split; auto. unfold Union. appA2G.
Qed.

Fact property_not : ∀ P Q,
  (~(P /\ Q) <-> (~P) \/ (~Q)) /\ (~(P \/ Q) <-> (~P) /\ (~Q)).
Proof.
  intros; destruct (classic P); tauto.
Qed.

Proposition property_not' : ∀ P, (~ (~ P) <-> P).
Proof.
  intros; destruct (classic P); tauto.
Qed.

Fact InClosedInterval : ∀ x a b, x ∈ ［a , b］ -> x ∈ RC /\ a ≤ x /\ x ≤ b 
  /\ a ∈ RC /\ b ∈ RC.
Proof.
  intros. appA2H H. destruct H0, H1, H2, H3. split; auto.
Qed.

Corollary CoverP2 : ∀ x y cH, InfinCover_Only x y cH -> InfinCover_Only x 
  ((x + y)/(1 + 1)) cH \/ InfinCover_Only ((x + y)/(1 + 1)) y cH.
Proof.
  intros. TF (InfinCover_Only x ((x + y)/(1 + 1)) cH); auto.
  right; Absurd. apply property_not in H0; apply property_not in H1.
  destruct H, H0, H. destruct H3, H4, H5. 
  - elim H0; red. split; auto. split; auto. split; auto. split; intros.
    + apply aver2; auto.
    + apply H6. New H7. apply InClosedInterval in H7. destruct H7, H9, H10.
      appA2G. repeat split; auto.
      apply (T173 c ((x + y) / (1 + 1)) y); eauto. left; apply aver2; auto.
  - destruct H1. destruct H3, H4, H5.
    + elim H1; red. split; auto. split; auto. split; auto. split; intros.
      * apply aver2 ; auto.
      * apply H6. New H7. apply InClosedInterval in H7. destruct H7, H9, H10.
        appA2G. repeat split; auto.
        apply (T173 x ((x + y) / (1 + 1)) c); eauto. left; apply aver2; auto.
    + apply -> property_not' in H0; apply -> property_not' in H1.
      elim H2; apply CoverP1; auto.
Qed.

Fact aver_Cor3 : ∀ x y, x ∈ RC -> y ∈ RC -> x < y -> x < (x + y) / (1 + 1).
Proof.
  intros. apply aver2 in H1; auto. destruct H1; auto.
Qed.

Global Hint Resolve aver_Cor3 : core.

Fact aver_Cor3' : ∀ x y, x ∈ RC -> y ∈ RC -> x < y -> (x + y) / (1 + 1) < y.
Proof.
  intros. apply aver2 in H1; auto. destruct H1; auto.
Qed.

Global Hint Resolve aver_Cor3' : core.

Fact aver_Cor4 : ∀ x y, x ∈ RC -> y ∈ RC -> (x + y) / (1 + 1) < y -> x < y.
Proof.
  intros. apply (FAT203d ((x + y) / (1 + 1)) y (1 + 1)) in H1; auto. 
  rewrite divRp7 in H1; auto. rewrite FAT194 in H1; auto. 
  rewrite dou3 in H1; auto. apply FAT188c1 in H1; auto.
Qed.

Global Hint Resolve aver_Cor4 : core.

Fact aver_Cor4' : ∀ x y, x ∈ RC -> y ∈ RC -> x < (x + y) / (1 + 1) -> x < y.
Proof.
  intros. apply (FAT203d x ((x + y) / (1 + 1)) (1 + 1)) in H1; auto. 
  rewrite divRp7 in H1; auto. rewrite FAT194, dou3 in H1; auto. 
  rewrite (@FAT175 x y) in H1; auto. apply FAT188c1 in H1; auto.
Qed.

Global Hint Resolve aver_Cor4' : core.

Fact Min1 : ∀ x y z, x ∈ RC -> y ∈ RC -> z ∈ RC -> x - (y - z) = x - y + z.
Proof.
  intros. rewrite FAT175; auto. rewrite FAT181; auto. rewrite (FAT175); auto. 
  assert(z - y = - y + z). { rewrite FAT175 ; auto. }
  rewrite H2. rewrite FAT186; auto. 
Qed.

Fact Min2 : ∀ x y z, x ∈ RC -> y ∈ RC -> z ∈ RC -> x - (y + z) = x - y - z.
Proof.
  intros. rewrite FAT175; auto. rewrite FAT180; auto. rewrite (FAT175); auto. 
  rewrite <- FAT186' ; auto.
Qed.
  
Global Hint Resolve Min1 Min2 : core.

Fact aver_Cor5 : ∀ x y, x ∈ RC -> y ∈ RC 
  -> x - (x + y) / (1 + 1) = (x - y) / (1 + 1).
Proof.
  intros. rewrite <- divRp4; auto. New H. apply halfsum in H1. rewrite Min2; 
  auto. assert(x - x / (1 + 1) - y / (1 + 1) = x / (1 + 1) + x / (1 + 1) 
  - x / (1 + 1) - y / (1 + 1)). { rewrite H1; auto. }
  rewrite H2. rewrite MincEx2; auto. rewrite (divRp5 x (1 + 1) y); auto.
Qed.

Fact aver_Cor5' : ∀ x y, x ∈ RC -> y ∈ RC 
  -> y - (x + y) / (1 + 1) = (y - x) / (1 + 1).
Proof.
  intros. pose proof aver_Cor5 y x H0 H. rewrite (@FAT175 x y); auto.
Qed.

Global Hint Resolve aver_Cor5 aver_Cor5' : core.

Fact Mul1 : ∀ x, x ∈ RC -> x · 0 = 0.
Proof.
  intros. apply MulRpf; auto.
Qed.

Fact Mul1' : ∀ x, x ∈ RC -> 0 · x = 0.
Proof.
  intros. apply MulRpe; auto.
Qed.

Global Hint Resolve Mul1 Mul1' : core.

Fact divRC8 : ∀ y, y ∈ RC -> y <> 0 -> 0 / y = 0.
Proof.
  intros. rewrite <- divRC4; auto. 
Qed.

Global Hint Resolve divRC8 : core.

Fact Abs1 : ∀ y, y ∈ RC -> |y / ( 1 + 1)| = |y| / ( 1 + 1).
Proof.
  intros. New H. apply (@FAT167 y 0) in H0; auto. destruct H0 as [H0 | []].
  - subst. rewrite Zabs; auto. rewrite divRC8; auto. rewrite Zabs; auto.
  - New H0. apply AbPRC in H1; auto. rewrite H1. apply AbPRC; auto.
  - New H0. apply AbNRC in H1; auto. rewrite H1. rewrite AbNRC; auto.
    + auto. rewrite divRp3; auto.
    + rewrite <- divRC4; auto.
Qed.

Global Hint Resolve Abs1 : core.

Section completeness_Cover.
Variable a0 b0 cH : Class.

Hypothesis InfinCover_Only_a0_b0_cH : InfinCover_Only a0 b0 cH.

Proposition IsOpenIntervalFamily_cH : IsOpenIntervalFamily cH.
Proof.
  red in InfinCover_Only_a0_b0_cH. 
  destruct InfinCover_Only_a0_b0_cH as [], H as[H1 [H2[]]]; auto.
Qed.

Proposition OpenCover_a0_b0_cH : OpenCover a0 b0 cH.
Proof.
  red in InfinCover_Only_a0_b0_cH. 
  destruct InfinCover_Only_a0_b0_cH as []; auto.
Qed.

Proposition a0_in_RC : a0 ∈ RC.
Proof.
  pose proof OpenCover_a0_b0_cH. red in H. destruct H, H0; auto.
Qed.

Proposition b0_in_RC : b0 ∈ RC.
Proof.
  pose proof OpenCover_a0_b0_cH. red in H. destruct H, H0; auto.
Qed. 

Proposition a0_less_b0 : a0 < b0.
Proof.
  red in InfinCover_Only_a0_b0_cH. destruct InfinCover_Only_a0_b0_cH.
  red in H. destruct H as [_[_[H[]]]]; auto.
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
     ((InfinCover_Only (First u) (((First u) + (Second u))/(1 + 1)) cH) 
      /\ (InfinCover_Only (((First u) + (Second u))/(1 + 1)) (Second u) cH) 
      /\ v = [(First u),(((First u) + (Second u))/(1+1))])
  \/ ((InfinCover_Only (First u) (((First u) + (Second u))/(1 + 1)) cH) 
      /\ ~ (InfinCover_Only (((First u) + (Second u))/(1 + 1)) (Second u) cH) 
      /\ v = [(First u),(((First u) + (Second u))/(1+1))])
  \/ ((InfinCover_Only (((First u) + (Second u))/(1 + 1)) (Second u) cH) 
      /\ ~ (InfinCover_Only (First u) (((First u) + (Second u))/(1 + 1)) cH)
      /\ v = [(((First u) + (Second u))/(1+1)),(Second u)])
  \/ ( ~ (InfinCover_Only (First u) (((First u) + (Second u))/(1 + 1)) cH) 
      /\ ~ (InfinCover_Only (((First u) + (Second u))/(1 + 1)) (Second u) cH) 
      /\ v = [0 , 0])
      ) \}\.

Proposition Functionh : Function (h).
Proof.
  intros. split; intros. apply poisre.
  apply AxiomII' in H as [H[H1[[H2[]]|[]]]] , H0 as [H0[H5[[H6[]]|[]]]].
  rewrite H4,H8; auto. destruct H6 as [H6[]]. rewrite H4,H8; auto.
  destruct H6 as [[H6[]]|[]]. elim H7; auto. 
  destruct H7 as [H7[]]. elim H7; auto. 
  destruct H2 as [H2[]]. rewrite H4,H8; auto.
  destruct H2 as [H2[]], H3 as [H3[]]. rewrite H6,H8; auto.
  destruct H2 as [H2[]].
  destruct H3 as [[H3[]]|[]]. elim H4; auto. elim H3; auto. 
  destruct H2 as [[H2[]]|[]]. elim H7; auto. destruct H7. elim H7; auto.
  destruct H2 as [[H2[]]|[]]. destruct H3. elim H4; auto.
  destruct H3. elim H2; auto.
  destruct H2 as [[H2[]]|[]], H3 as [[H3[]]|[]]. rewrite H6,H8; auto.
  destruct H7. elim H7; auto. destruct H4. elim H4; auto.
  destruct H4, H6. rewrite H7,H8; auto.
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
    TF((InfinCover_Only (First z) (((First z) + (Second z))/(1 + 1)) cH)).
    + TF((InfinCover_Only (((First z) + (Second z))/(1 + 1)) (Second z) cH)).
      * exists [(First z),(((First z) + (Second z))/(1+1))]. 
        apply AxiomII'; repeat split; auto.
        apply MKT49a; auto. subst. apply MKT49a; auto. rewrite H8; auto. 
        rewrite H8; auto. rewrite H9; auto.
      * exists [(First z),(((First z) + (Second z))/(1+1))].
        apply AxiomII'; repeat split; auto.
        apply MKT49a; auto. subst. apply MKT49a; auto. rewrite H8; auto. 
        rewrite H8; auto. rewrite H9; auto.
    + TF((InfinCover_Only (((First z) + (Second z))/(1 + 1)) (Second z) cH)).
      * exists [(((First z) + (Second z))/(1+1)),(Second z)]. 
        apply AxiomII'; repeat split; auto.
        apply MKT49a; auto. subst. apply MKT49a; auto. rewrite H8; auto. 
        rewrite H9; auto. rewrite H9; auto.
        right. right. left. split; auto.
      * exists [0 , 0]. 
        apply AxiomII'; repeat split; auto.
        right. right. right. split; auto.
Qed.

Proposition ranh : ran(h) ⊂ RC × RC.
Proof.
  unfold Included; intros.
  - apply AxiomII in H as [H[]]. apply AxiomII' in H0.
    destruct H0 as [H0[H1[]]]; auto. destruct H2 as [H2[]].
    + subst. appA2G. exists (x) ¹. exists (((x) ¹ + (x) ²) / (1 + 1)).
      unfold Cartesian in H1. appA2H H1. destruct H4, H4, H4, H5.
      assert(Ensemble x0); unfold Ensemble; eauto.
      assert(Ensemble x1); unfold Ensemble; eauto.
      New H7. apply (MKT54a x0 x1) in H9; auto. rewrite <- H4 in H9.
      New H7. apply (MKT54b x0 x1) in H10; auto. rewrite <- H4 in H10.
      rewrite <- H9 in H5. rewrite <- H10 in H6. repeat split; auto.
    + unfold Cartesian; appA2G. 
      unfold Cartesian in H1. appA2H H1. destruct H3, H3, H3, H4.
      assert(Ensemble x0); unfold Ensemble; eauto.
      assert(Ensemble x1); unfold Ensemble; eauto.
      New H7. apply (MKT54a x0 x1) in H8; auto. rewrite <- H3 in H8.
      New H7. apply (MKT54b x0 x1) in H9; auto. rewrite <- H3 in H9.
      rewrite <- H9 in H5. rewrite <- H8 in H4. 
      destruct H2; auto. 
      * destruct H2 as [H2[]]. exists (x) ¹. exists (((x) ¹ + (x) ²) / (1 + 1)).
        split; auto.
      * destruct H2; auto. 
        ** destruct H2 as [H2[]]. exists (((x) ¹ + (x) ²) / (1 + 1)). exists (x) ². 
           split; auto.
        ** destruct H2 as [H2[]]. exists 0. exists 0.
           split; auto.
Qed.

Proposition h_is_Function : Function (h) /\ dom(h) = RC × RC /\ ran(h) ⊂ RC × RC.
Proof.
  pose proof Functionh. pose proof domh. pose proof ranh.
  split; auto.
Qed.

Let g := ∩(\{ λ f, Function f /\ dom(f) = Nat /\ ran(f) ⊂ RC × RC
  /\ f[One] = [a0,b0] /\ (∀ n, n ∈ Nat -> f[(n + One)%Nat] = h[(f[n])]) \}).

Proposition g_uni : ∃ u, Ensemble u
  /\ \{ λ f, Function f /\ dom(f) = Nat /\ ran(f) ⊂ RC × RC
    /\ f[One] = [a0,b0] /\ (∀ n, n ∈ Nat -> f[(n + One)%Nat] = h[(f[n])]) \} = [u].
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
  apply Ensemble_a0. apply Ensemble_b0.
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
  apply Ensemble_a0. apply Ensemble_b0.
Qed.

Lemma InfinCover_Only_a0_b0_cH' : InfinCover_Only (M[One]) (N[One]) cH.
Proof.
  intros. pose proof M_is_Seq. pose proof N_is_Seq. destruct H, H0, H1, H2.
  rewrite H3, H4; auto.
Qed.

Lemma FL1 : ∀ n, n ∈ Nat -> InfinCover_Only (M[n]) (N[n]) cH.
Proof.
  apply Mathematical_Induction_Nat. apply InfinCover_Only_a0_b0_cH'. intros.
  pose proof M_is_Seq. pose proof N_is_Seq. destruct H1, H2, H3, H4.
  clear H5 H6. assert((k + One)%Nat ∈ Nat); auto. New H5. New H6. 
  apply H3 in H6. apply H4 in H7. New H. New H. apply H3 in H8. apply H4 in H9.
  rewrite H8, H9 in H0. rewrite H6, H7. clear H1 H2 H3 H4 H5 H6 H7 H8 H9.
  assert((k + One)%Nat ∈ Nat); auto. clear M N. pose proof g_is_Function.
  New H. destruct H2, H4, H5, H6. apply H7 in H3. rewrite H3.
  assert(g [k] ∈ ran( g)).
  { rewrite <- H4 in H. apply Property_Value, Property_ran in H; auto. } 
  assert(g [k] ∈ dom(h)).
  { pose proof domh. rewrite H9. unfold Included in H5. apply H5 in H8; auto. }
  pose proof Functionh. New H9. apply Property_Value in H11; auto. 
  appA2H H11; auto. destruct H12, H12, H12, H13. 
  New H11. apply MKT49c1 in H15. New H11. apply MKT49c2 in H16. 
  rename H15 into Ensemble_gk. rename H16 into Ensemble_hgk.
  apply (MKT55 g[k] h[g[k]] x x0) in H12; auto. destruct H12. subst.
  New H13. unfold Cartesian in H12. appA2H H12. clear H12. destruct H15, H12, 
  H12, H15. rename H15 into xRC. rename H16 into x0RC. New Ensemble_gk. rewrite 
  H12 in H15. New H15. apply MKT49c1 in H15. apply MKT49c2 in H16.
  assert((g [k]) ¹ = x). { rewrite H12. apply (MKT54a x x0) in H15; auto. }
  assert((g [k]) ² = x0). { rewrite H12. apply (MKT54b x x0) in H15; auto. }
  assert(Ensemble (((g [k]) ¹ + (g [k]) ²) / (1 + 1))).
  { rewrite H17, H18. assert((x + x0) ∈ RC); auto.
    assert(Ensemble (x + x0)); unfold Ensemble; eauto. }
  rename H19 into Ensemble_g12. 
  rewrite <- H17 in H15. rewrite <- H18 in H16. clear H17 H18 xRC x0RC.
  destruct H14.
  - destruct H14, H17. 
    assert((h [g [k]]) ¹ = (g [k]) ¹). 
    { rewrite H18. apply (MKT54a ((g [k]) ¹) 
      (((g [k]) ¹ + (g [k]) ²) / (1 + 1))) in H15; auto. }
    assert((h [g [k]]) ² = ((g [k]) ¹ + (g [k]) ²) / (1 + 1)). 
    { rewrite H18. apply (MKT54b ((g [k]) ¹) 
      (((g [k]) ¹ + (g [k]) ²) / (1 + 1))) in H15; auto. }
    rewrite H19, H20; auto.
  - destruct H14.
    + destruct H14, H17. 
    assert((h [g [k]]) ¹ = (g [k]) ¹). 
    { rewrite H18. apply (MKT54a ((g [k]) ¹) 
      (((g [k]) ¹ + (g [k]) ²) / (1 + 1))) in H15; auto. }
    assert((h [g [k]]) ² = ((g [k]) ¹ + (g [k]) ²) / (1 + 1)). 
    { rewrite H18. apply (MKT54b ((g [k]) ¹) 
      (((g [k]) ¹ + (g [k]) ²) / (1 + 1))) in H15; auto. }
    rewrite H19, H20; auto.
    + destruct H14.
      * destruct H14, H17. 
        assert((h [g [k]]) ¹ = (((g [k]) ¹ + (g [k]) ²) / (1 + 1))). 
        { rewrite H18. apply (MKT54a (((g [k]) ¹ + (g [k]) ²) / (1 + 1)) 
          ((g [k]) ²)) in H16; auto. }
        assert((h [g [k]]) ² = (g [k]) ²). 
        { rewrite H18. apply (MKT54b (((g [k]) ¹ + (g [k]) ²) / (1 + 1)) 
          ((g [k]) ²)) in H16; auto. }
        rewrite H19, H20; auto.
      * destruct H14, H17. apply CoverP2 in H0. destruct H0.
        ++ elim H14; auto.
        ++ elim H17; auto.
Qed.

Fact NtoR3a: ∀ x y, x ∈ Nat -> y ∈ Nat -> (x ≤ y)%Nat -> NtoR x ≤ NtoR y.
Proof.
  intros. red. destruct H1.
  - left. apply NtoR3 in H1; auto.
  - right. apply NtoR1; auto.
Qed.

      
Lemma FL2 : Increase M.
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
    destruct H20.
    - destruct H20, H24. 
      assert((h [g [k]]) ¹ = (g [k]) ¹). 
      { rewrite H25. apply (MKT54a ((g [k]) ¹) 
        (((g [k]) ¹ + (g [k]) ²) / (1 + 1))) in H22; auto. }
      rewrite H26. red in H24. destruct H24. red in H24. 
      destruct H24 as [_[_[_[]]]]. red; right; auto.
    - destruct H20.
      + destruct H20, H24. 
      assert((h [g [k]]) ¹ = (g [k]) ¹). 
      { rewrite H25. apply (MKT54a ((g [k]) ¹) 
        (((g [k]) ¹ + (g [k]) ²) / (1 + 1))) in H22; auto. }
      rewrite H26. red; right; auto.
      + destruct H20.
        * destruct H20, H24. 
          assert((h [g [k]]) ¹ = (((g [k]) ¹ + (g [k]) ²) / (1 + 1))). 
          { rewrite H25. apply (MKT54a (((g [k]) ¹ + (g [k]) ²) / (1 + 1)) 
            (g [k]) ²); auto. }
          rewrite H26. red in H20. destruct H20, H20, H28, H29, H30. 
          apply CartesianRCa in H19. apply aver_Cor4 in H30; auto. 
          red; left. apply aver_Cor3 in H30; auto.
        * destruct H20, H24.
          New H9. New H9. New H9. pose proof FL1. 
          apply H29 in H26. clear H29. apply H2 in H27. apply H7 in H28.
          rewrite H27, H28 in H26. apply CoverP2 in H26. destruct H26.
          ++ elim H20; auto.
          ++ elim H24; auto.
  }
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
          ** red; left. apply (FAT172 (M [n]) (M [k]) (M [(k + One)%Nat]));auto.
          ** rewrite H17; auto. 
  }
  unfold P in H12. intros. red. apply H12 in H13 as []; auto.
Qed.


Lemma FL3 : Decrease N.
Proof.
  destruct M_is_Seq as [[H[]][]]. destruct N_is_Seq as [[H4[]][]].
  assert (∀ k, k ∈ Nat -> N[(k + One)%Nat] ≤ N[k]).
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
    destruct H20.
    - destruct H20, H24. 
      assert((h [g [k]]) ² = ((g [k]) ¹ + (g [k]) ²) / (1 + 1)). 
      { rewrite H25.  apply (MKT54b ((g [k]) ¹) 
        (((g [k]) ¹ + (g [k]) ²) / (1 + 1))) in H22; auto. }
      rewrite H26. red in H24. destruct H24. red in H24. 
      destruct H24 as [_[_[_[]]]]. red; left; auto.
    - destruct H20.
      + destruct H20, H24. 
        assert((h [g [k]]) ² = ((g [k]) ¹ + (g [k]) ²) / (1 + 1)). 
        { rewrite H25. apply (MKT54b ((g [k]) ¹) 
          (((g [k]) ¹ + (g [k]) ²) / (1 + 1))) in H22; auto. }
      rewrite H26. red in H20. destruct H20. red in H20. 
      destruct H20 as [_[_[_[]]]]. apply CartesianRCa in H19 as gk1_in_RC.
      apply CartesianRCb in H19 as gk2_in_RC. apply aver_Cor4' in H20; auto. 
      red; left. apply aver_Cor3' in H20; auto.
      + destruct H20.
        * destruct H20, H24. assert((h [g [k]]) ² = (g [k]) ²). 
          { rewrite H25. apply (MKT54b (((g [k]) ¹ + (g [k]) ²) / 
            (1 + 1)) (g [k]) ²); auto. } rewrite H26. red; right; auto.
        * destruct H20, H24.
          New H9. New H9. New H9. pose proof FL1. 
          apply H29 in H26. clear H29. apply H2 in H27. apply H7 in H28.
          rewrite H27, H28 in H26. apply CoverP2 in H26. destruct H26.
          ++ elim H20; auto.
          ++ elim H24; auto.
  }
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
          ** red; left. apply (FAT172 (N [(k + One)%Nat]) (N [k]) (N [n]));auto. 
          ** rewrite <- H17; auto. 
  }
  unfold P in H12. intros. red. apply H12 in H13 as []; auto.
Qed.



Fact b0_up_a0 : a0 < b0.
Proof.
  red in InfinCover_Only_a0_b0_cH. destruct InfinCover_Only_a0_b0_cH.
  red in H. destruct H, H1, H2, H3; auto.
Qed.

Lemma FL4 : ILT_Seq M N.
Proof.
  red. pose proof M_is_Seq. pose proof N_is_Seq. destruct H, H0.
  split; auto. split; auto. clear H0 H H1 H2.
  destruct M_is_Seq as [[H[]][]], N_is_Seq as [[H4[]][]].
  apply Mathematical_Induction_Nat; intros.
  - rewrite H3,H8. apply b0_up_a0.
  - assert((k + One)%Nat ∈ Nat); auto. New H11.
    apply H2 in H11. apply H7 in H12.
    destruct g_is_Function as [H13[H14[H15[]]]].
    rewrite H17 in H11,H12; auto. rewrite H11,H12.
    destruct h_is_Function as [H18[]]. New H9. rewrite <-H14 in H21.
    apply Property_Value,Property_ran,H15 in H21; auto.
    rewrite <-H19 in H21.
    apply Property_Value in H21; auto.
    apply AxiomII' in H21. destruct H21. apply MKT49b in H21 as [].
    destruct H22 as [H22[[H24[]]|[]]].
    + New H23. rewrite H26 in H27. apply MKT49b in H27 as [].
      New H22. New H22. apply CartesianRCa in H29. apply CartesianRCb in H30.
      assert(((g [k]) ¹ + (g [k]) ²) ∈ RC); auto.
      assert(Ensemble ((g [k]) ¹ + (g [k]) ²)); unfold Ensemble; eauto.
      assert(((g [k]) ¹ + (g [k]) ²) / (1 + 1) ∈ RC); auto.
      assert(Ensemble ((g [k]) ¹ + (g [k]) ² / (1+1))); unfold Ensemble; eauto.
      New H27. New H27.
      apply (MKT54a (g [k]) ¹ (((g [k]) ¹ + (g [k]) ²) / (1+1))) in H35; auto.
      apply (MKT54b (g [k]) ¹ (((g [k]) ¹ + (g [k]) ²) / (1+1))) in H36; auto.
      rewrite <- H26 in H35, H36. red in H24. destruct H24. red in H24. 
      destruct H24 as [_ [_[_[]]]]. rewrite H35, H36; auto.
    + destruct H25, H25. New H23. rewrite H26 in H27. apply MKT49b in H27 as [].
      New H22. New H22. apply CartesianRCa in H29. apply CartesianRCb in H30.
      assert(((g [k]) ¹ + (g [k]) ²) ∈ RC); auto.
      assert(Ensemble ((g [k]) ¹ + (g [k]) ²)); unfold Ensemble; eauto.
      assert(((g [k]) ¹ + (g [k]) ²) / (1 + 1) ∈ RC); auto.
      assert(Ensemble ((g [k]) ¹ + (g [k]) ² / (1+1))); unfold Ensemble; eauto.
      New H27. New H27.
      apply (MKT54a (g [k]) ¹ (((g [k]) ¹ + (g [k]) ²) / (1+1))) in H35; auto.
      apply (MKT54b (g [k]) ¹ (((g [k]) ¹ + (g [k]) ²) / (1+1))) in H36; auto.
      rewrite <- H26 in H35, H36. red in H24. destruct H24. red in H24. 
      destruct H24 as [_ [_[_[]]]]. rewrite H35, H36; auto.
    + destruct H25 as [H25| H25].
       * destruct H25, H25. New H23. 
         rewrite H26 in H27. apply MKT49b in H27 as [].
         New H22. New H22. apply CartesianRCa in H29. apply CartesianRCb in H30.
         assert(((g [k]) ¹ + (g [k]) ²) ∈ RC); auto.
         assert(Ensemble ((g [k]) ¹ + (g [k]) ²)); unfold Ensemble; eauto.
         assert(((g [k]) ¹ + (g [k]) ²) / (1 + 1) ∈ RC); auto.
         assert(Ensemble ((g [k]) ¹ + (g [k]) ²/(1+1))); unfold Ensemble; eauto.
         New H27. New H27.
         apply (MKT54a (((g [k]) ¹ + (g [k]) ²)/(1+1)) (g [k]) ² ) in H35; auto.
         apply (MKT54b (((g [k]) ¹ + (g [k]) ²)/(1+1)) (g [k]) ² ) in H36; auto.
         rewrite <- H26 in H35, H36. red in H24. destruct H24. red in H24. 
         destruct H24 as [_ [_[_[]]]]. rewrite H35, H36; auto.
       * destruct H25, H25. pose proof FL1.  
         assert((k + One)%Nat ∈ Nat); auto. apply H27 in H28. red in H28.
         destruct H28. red in H28. destruct H28 as [_ [_[_[]]]].
         rewrite <- H11. rewrite <- H12; auto.
Qed.

Fact div1_2expn_Lemma0 : div1_2expn[One] = 1 / (1 + 1).
Proof.
  intros. assert(One ∈ Nat); auto. pose proof Vaulediv1_2expn. apply H0 in H.
  rewrite H. clear H H0.
  assert(1 ∈ RC); auto. New H. New H.
  assert((1 + 1) ^ One = (1 + 1)). { intros. apply P_Ex2; auto. }
  rewrite H2; auto.
Qed.

Fact div1_2expn_Lemma1 : ∀k : Class,k ∈ Nat -> 
  div1_2expn[(k + One)%Nat] = div1_2expn[k] · (1 / ( 1 + 1)).
Proof.
  intros. pose proof Vaulediv1_2expn k H. assert((k + One)%Nat ∈ Nat); auto.
  pose proof Vaulediv1_2expn (k + One)%Nat H1. rewrite H0, H2. New H. 
  apply (Exp_mult1 (1 + 1) k) in H3; auto. rewrite H3. apply divRC5; auto.
Qed.
    
Lemma FL5_Lemma0 : ∀n : Class,n ∈ Nat 
  -> | M [n] - N [n] | = ((b0 - a0) · ( 1 + 1)) · div1_2expn [n].
Proof.
  pose proof M_is_Seq. pose proof N_is_Seq. destruct H, H0, H1, H2.
  pose proof Vaulediv1_2expn. pose proof div1_2expn_Lemma0. 
  apply Mathematical_Induction_Nat. 
  -- rewrite H3. rewrite H4. assert(One ∈ Nat); auto. rewrite H6.
    pose proof a0_less_b0. 
    assert(a0 ∈ RC). { rewrite <- H3. apply anRC; auto. }
    assert(b0 ∈ RC). { rewrite <- H4. apply anRC; auto. }
    assert(b0 - a0 <> 0). { New H9. apply (@FAT167 a0 b0) in H11; auto. }
    rewrite (FAT194 (b0 - a0) (1 + 1)); auto.
    rewrite (divRC3 (1 + 1) (b0 - a0)); auto.
  -- intros. pose proof div1_2expn_Lemma1 k H7. rewrite H9.
    assert((k + One)%Nat ∈ Nat); auto. pose proof H1 (k + One)%Nat H10. 
    pose proof H2 (k + One)%Nat H10. rewrite H11, H12. clear H9 H11 H12. 
    rename H8 into HMNk. pose proof g_is_Function. destruct H8, H9, H11, H12. 
    pose proof H13 k H7. destruct h_is_Function as [H15[]].
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
    pose proof FL4. red in H24. destruct H24 as [_[_]]. pose proof H24 k H7. 
    assert(| M [k] - N [k] | = N [k] - M [k]); auto.
    assert((k + One)%Nat ∈ Nat); auto.  pose proof H24 (k + One)%Nat H27.
    assert(| M [(k + One)%Nat] - N [(k + One)%Nat] | = N [(k + One)%Nat] - 
    M [(k + One)%Nat]); auto. rewrite Hgk1, Hgk2 in HMNk. clear H24 H25 H28.
    destruct H20.
      - destruct H20, H24. 
      assert((h [g [k]]) ¹ = (g [k]) ¹). 
      { rewrite H25. apply (MKT54a ((g [k]) ¹) (((g [k]) ¹ + (g [k]) ²) / 
        (1 + 1))) in H22; auto. } 
      assert((h [g [k]]) ² = ((g [k]) ¹ + (g [k]) ²) / (1 + 1)). 
      { rewrite H25.  apply (MKT54b ((g [k]) ¹) (((g [k]) ¹ + (g [k]) ²) / 
        (1 + 1))) in H22; auto. }
      rewrite H28, H30. apply CartesianRCa in H19 as gk1_in_RC.
      apply CartesianRCb in H19 as gk2_in_RC. rewrite aver_Cor5; auto. rewrite 
      Abs1; auto. rewrite HMNk. pose proof a0_in_RC. pose proof b0_in_RC.
      assert((b0 - a0) · (1 + 1) ∈ RC); auto.
      assert(div1_2expn [k] ∈ RC).
      { pose proof Vaulediv1_2expn k H7. rewrite H34. 
        assert((1 + 1) ^ k ∈ RC); auto. }
      rewrite <- divRC4; auto. apply FAT199; auto.
    - destruct H20.
      + destruct H20, H24. 
      assert((h [g [k]]) ¹ = (g [k]) ¹). 
      { rewrite H25. apply (MKT54a ((g [k]) ¹) (((g [k]) ¹ + (g [k]) ²) / 
        (1 + 1))) in H22; auto. }
      assert((h [g [k]]) ² = ((g [k]) ¹ + (g [k]) ²) / (1 + 1)). 
      { rewrite H25. apply (MKT54b ((g [k]) ¹) (((g [k]) ¹ + (g [k]) ²) / 
        (1 + 1))) in H22; auto. }
      rewrite H28, H30. apply CartesianRCa in H19 as gk1_in_RC. apply 
      CartesianRCb in H19 as gk2_in_RC. rewrite aver_Cor5; auto. rewrite Abs1; 
      auto. rewrite HMNk. pose proof a0_in_RC. pose proof b0_in_RC.
      assert((b0 - a0) · (1 + 1) ∈ RC); auto.
      assert(div1_2expn [k] ∈ RC).
      { pose proof Vaulediv1_2expn k H7. rewrite H34. 
        assert((1 + 1) ^ k ∈ RC); auto. }
      rewrite <- divRC4; auto. apply FAT199; auto.
      + destruct H20.
        * destruct H20, H24. 
          assert((h [g [k]]) ¹ = (((g [k]) ¹ + (g [k]) ²) / (1 + 1))). 
          { rewrite H25. apply (MKT54a (((g [k]) ¹ + (g [k]) ²) / (1 + 1)) 
            (g [k]) ²); auto. }
          assert((h [g [k]]) ² = (g [k]) ²). 
          { rewrite H25. apply (MKT54b (((g [k]) ¹ + (g [k]) ²) / (1 + 1)) 
            (g [k]) ²); auto. }
          rewrite H28, H30. apply CartesianRCa in H19 as gk1_in_RC.
          apply CartesianRCb in H19 as gk2_in_RC. rewrite AbE; auto.
          rewrite aver_Cor5'; auto. rewrite Abs1; auto. rewrite AbE; auto.
          rewrite HMNk. pose proof a0_in_RC. pose proof b0_in_RC.
          assert((b0 - a0) · (1 + 1) ∈ RC); auto.
          assert(div1_2expn [k] ∈ RC).
          { pose proof Vaulediv1_2expn k H7. rewrite H34. 
            assert((1 + 1) ^ k ∈ RC); auto. }
          rewrite <- divRC4; auto. apply FAT199; auto.
        * destruct H20, H24. New H7. pose proof FL1. apply H30 in H28. 
          clear H30. rewrite Hgk1 in H28. rewrite Hgk2 in H28. 
          apply CoverP2 in H28. destruct H28. elim H20; auto. elim H24; auto.
Qed.

Lemma FL5 : Limit_E M N.
Proof.
  red.  pose proof M_is_Seq. pose proof N_is_Seq. destruct H, H1, H0, H3.
  split; auto. split; auto. intros. pose proof FL5_Lemma0.
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

Theorem FLtoFinCover : exists n, n ∈ Nat /\ FinCover (M[n]) (N[n]) cH.
Proof.
  New InfinCover_Only_a0_b0_cH. red in H. destruct H.
  generalize FL1 FL2 FL3 FL4 FL5; intros.
  assert (NestedIntervals M N). { red. split; auto. }
  clear H3 H2 H5.
  destruct (Cor_NIT _ _ H6) as [z [H5 H7]], H7.
  red in H. destruct H as [a0RC [b0RC [IsOpenIntervalFamily_cH[a0lb0]]]].
  assert(z ∈ ［ a0, b0 ］).
  { assert(One ∈ Nat); auto. apply H2 in H7. pose proof M_is_Seq.
    pose proof N_is_Seq. destruct H8 as [_ [_ H8]]. destruct H9 as [_ [_ H9]].
    rewrite H8, H9 in H7. clear H8 H9.
    destruct H7. appA2G. }
  apply H in H7. destruct H7 as [ch []]. red in IsOpenIntervalFamily_cH.
  New H7. apply IsOpenIntervalFamily_cH in H9. destruct H9 as [a[b]].
  rewrite H9 in H7, H8. clear H9.
  New H8. appA2H H9. destruct H10 as [zRC [aRC[bRC[alz zlb]]]].
  assert(MathMin [[z - a,b - z]] ∈ RC). { apply MathMinRC; auto. }
  assert(MathMin [[z - a,b - z]] > 0). 
  {  pose proof MathMineq.
     assert(z - a ∈ RC); auto. assert(b - z ∈ RC); auto.
     assert(z - a > 0); auto. assert(b - z > 0); auto. apply 
     (H11 (z - a) (b - z)) in H12; auto. destruct H12; rewrite H12; auto. }
  apply H3 in H11; auto.
  destruct H11 as [N0[]]. 
  assert(NtoR N0 ∈ RC); auto.
  pose proof ArchimedeanLemma1. apply H14 in H13. destruct H13 as [n0], H13.
  exists n0. split; auto. New H13. red. clear H14. New H16. 
  red in H4. destruct H4, H17. New H14. apply H18 in H19. 
  apply (anRC M) in H16; auto. apply (anRC N) in H14; auto.
  repeat split; auto.
  set (singlecH := [ ］ a , b ［ ]).
  assert(］ a, b ［ ∈ μ). { apply MKT19; unfold Ensemble; eauto. }
  rename H20 into H'.
  exists singlecH. repeat split; auto.
  - unfold Included. intros. unfold singlecH in H20. appA2H H20.
    rewrite H21; auto.
  - unfold singlecH. apply finsin; auto.
  - unfold IsOpenIntervalFamily. intros. unfold singlecH in H20. appA2H H20.
    exists a. exists b; auto. 
  - intros. exists ］ a , b ［. split.
    + appA2G.
    + appA2G. appA2H H20. destruct H21, H22, H23, H24. split; auto. split; auto. 
      split; auto. assert(MathMin [[z - a, b - z]] = z - a \/ MathMin 
      [[z - a, b - z]] = b - z). { apply (MathMineq(z - a) (b - z)); auto. }
      New H13. apply H12 in H27; auto. destruct H27. destruct H26; split.
      * rewrite H26 in H27. 
        assert(z - (z - a) = a). 
        { rewrite Min1; auto. rewrite xminx; auto. rewrite AddRpa; auto. }
        rewrite H29 in H27. apply (FAT172 a M[n0] c); auto.
      * rewrite H26 in H28. apply MathMin1 in H26; auto.
        assert(z + (z - a) = z + z - a). { rewrite FAT186'; auto. }
        assert(z + z - a ≤ b). 
        { destruct H26.
          + red; left. apply (FAT188a1 b (z + z - a) (-z)); auto.
            rewrite FAT186; auto. rewrite FAT186; auto. rewrite <- FAT180; auto.
            rewrite Min2; auto. rewrite (MincEx2 z (-a)); auto. 
          + rewrite FAT186; auto. rewrite H26; auto. rewrite <- FAT186; auto.
            rewrite MincEx2; auto. red; right. auto. }
        rewrite H29 in H28. 
        assert(c < z + z - a). apply (FAT172 c N[n0] (z + z - a)); auto.
        apply (FAT172 c (z + z - a) b); auto.
      * rewrite H26 in H27. apply MathMin2 in H26; auto.
        assert(z - (b - z) = z + z - b). rewrite Min1; auto. 
        rewrite FAT186; auto. rewrite (@FAT175 (-b) z); auto. 
        rewrite <- FAT186; auto.
        assert(a ≤ z + z - b). 
        { destruct H26. 
          + red; left. apply (FAT188c1 a (z + z - b) (-z)); auto.
            rewrite FAT186; auto. rewrite FAT186; auto. rewrite <- FAT180; auto.
            rewrite Min2; auto. rewrite (MincEx2 z (-b)); auto. 
            apply FAT183a1 in H26; auto. rewrite FAT181 in H26; auto.
            rewrite FAT181 in H26; auto.
          + rewrite <- H29. rewrite H26; auto. rewrite Min1; auto.
            rewrite xminx; auto. rewrite AddRpa; auto. red; right; auto. }
        rewrite H29 in H27. 
        assert(a < M [n0]). apply (FAT172 a (z + z - b) M[n0]); auto.
        apply (FAT172 a M[n0] c); auto.
      * rewrite H26 in H28. 
        assert(z + (b - z) = b). { rewrite <- FAT186; auto. }
        rewrite H29 in H28. apply (FAT172 c N[n0] b); auto.
Qed.



Theorem FL1_FinCover_Contradiction : False.
Proof.
  pose proof FLtoFinCover. destruct H, H.
  pose proof FL1. apply H1 in H. clear H1. red in H. destruct H.
  elim H1; auto.
Qed.



End completeness_Cover.

Theorem FinorInfin : ∀a0 b0 cH, OpenCover a0 b0 cH -> 
  FinCover a0 b0 cH \/ InfinCover_Only a0 b0 cH.
Proof.
  intros. TF(FinCover a0 b0 cH).
  - left; auto.
  - right. red. split; auto.
Qed.

Theorem FinCoverT : ∀a0 b0 cH, OpenCover a0 b0 cH -> FinCover a0 b0 cH.
Proof.
  intros. pose proof (FinorInfin a0 b0 cH). 
  pose proof (FL1_FinCover_Contradiction a0 b0 cH).
  New H. apply H0 in H2; auto. destruct H2.
  - auto.
  - apply H1 in H2; auto; contradiction.
Qed.