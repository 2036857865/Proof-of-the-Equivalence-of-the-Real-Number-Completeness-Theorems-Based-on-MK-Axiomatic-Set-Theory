(**********************************************************************)
(*     This is part of Real_Completeness, it is distributed under     *)
(*    the terms of the GNU Lesser General Public License version 3    *)
(*             (see file LICENSE for more details)                    *)
(*                                                                    *)
(*                     Copyright 2026-2031                            *)
(*              Ce Zhang, Guowei Dou and ωensheng Yu                  *)
(**********************************************************************)

Require Export Dedekind_Theorem_Proof_By_Sup_Inf_Principle.

Definition IsSeq f := Function f /\ dom(f) = Nat /\ ran(f) ⊂ RC.

Definition Increase S := IsSeq S /\ 
  (∀ n m, n ∈ Nat -> m ∈ Nat -> NtoR n < NtoR m -> (S[n]) ≤ (S[m])).
Definition Decrease S := IsSeq S /\ 
  (∀ n m, n ∈ Nat -> m ∈ Nat -> NtoR n < NtoR m -> (S[m]) ≤ (S[n])).

Definition Boundup_Seq y S := IsSeq S /\ y ∈ RC 
  /\ (∀ n, n ∈ Nat -> (S[n]) ≤ y).
Definition Bounddown_Seq y S := IsSeq S /\ y ∈ RC 
  /\ (∀ n, n ∈ Nat -> y ≤ (S[n])).

Definition Limit S x := IsSeq S /\ x ∈ RC /\ (∀ ε, ε ∈ RC -> 0 < ε -> 
  (∃ N, N ∈ Nat /\ (∀ n, n ∈ Nat -> NtoR N < NtoR n -> AbsR[S[n] - x] < ε))).

Corollary Cor_supremum : ∀ s S, supremum S s ->
  ∀ ε, ε ∈ RC -> ε > 0 -> ∃ x, x ∈ S /\ (s - ε) < x.
Proof.
  intros; destruct H; Absurd. unfold Boundup_Ens in H. destruct H, H4.
  assert (s - ε ∈ RC); auto. assert (Boundup_Ens S (s - ε)).
  { red; intros. split; auto. split; auto.
    intros. TF(x ≤ s - ε); auto. apply NotleR in H8; auto. elim H3; eauto. }
  apply H2 in H7. assert(ε ≤ ε). { apply xleRx; auto. }
  apply (@FAT191b s (s - ε) ε ε) in H8; auto. rewrite MincEx1 in H8; auto.
  assert((-s) ≤ (-s)). { apply xleRx; auto. }
  apply (@FAT191b (s + ε) s (-s) (-s)) in H9; auto. 
  rewrite MincEx2 in H9; auto. rewrite xminx in H9; auto.
  apply legRf in H9; auto. contradiction.
Qed.

Corollary Cor_infimum : ∀ s S, infimum S s -> 
  ∀ ε, ε ∈ RC -> ε > 0 -> ∃ x, x ∈ S /\ x < (s + ε).
Proof.
  intros; destruct H; Absurd.
  unfold Boundup_Ens in H. destruct H, H4.
  assert (s + ε ∈ RC); auto.
  assert (Bounddown_Ens S (s + ε)).
  { red; intros. split; auto. split; auto. intros. TF(s + ε ≤ x); auto. 
    apply NotleR in H8; auto. elim H3; eauto. }
  apply H2 in H7. assert(ε ≤ ε). { apply xleRx; auto. }
  assert((-s) ≤ (-s)). { apply xleRx; auto. }
  apply (@FAT191b (s + ε) s (-s) (-s)) in H9; auto. 
  rewrite MincEx2 in H9; auto. rewrite xminx in H9; auto.
  apply legRf in H9; auto. contradiction.
Qed.

Corollary AbE : ∀ x y, x ∈ RC -> y ∈ RC -> |x - y| = |y - x|.
Proof.
  intros. New H. apply (@FAT167 x y) in H; auto. destruct H.
  - rewrite H. auto.
  - destruct H.
    + New H. New H. apply FAT182c2 in H2; auto. apply FAT182a2 in H3; auto.
      apply AbNRC in H2; auto. apply AbPRC in H3; auto. rewrite H2. rewrite H3. 
      rewrite FAT181; auto.
    + New H. New H. apply FAT182c2 in H2; auto. apply FAT182a2 in H3; auto.
      apply AbNRC in H2; auto. apply AbPRC in H3; auto. rewrite H2. rewrite H3. 
      rewrite FAT181; auto.
Qed.

Corollary Ab1 : ∀ x y, x ∈ RC -> y ∈ RC -> |y| < x <-> -x < y /\ y < x .
Proof.
  split.
  - intros. New H0. apply adsRC in H2.
    assert(|y| ≥ 0). { apply FAT170; auto. }
    assert((0 ≤ |y| /\ |y| < x) \/ (0 < |y| /\ |y| ≤ x)). { left. split; auto. }
    apply FAT172 in H4; auto. New H0. apply (@FAT167 y 0) in H5; auto. split. 
    -- apply NNPP; intro. apply Notle in H6; auto. destruct H5.
       + subst. apply FAT176a1 in H4; auto. apply (@legRf 0 (-x)) in H6; auto.
       + destruct H5.
         ++ apply FAT176a1 in H4; auto. 
           assert((y ≤ - x /\ - x < 0) \/ (y < - x /\ - x ≤ 0)). 
           { left. split; auto. } 
           apply FAT172 in H7; auto. apply (@lgRf y 0) in H7; auto.
         ++ apply (minsie2' x y) in H6; auto.
            apply AbNRC in H5; auto. rewrite <- H5 in H6.
            apply (@legRf x (|y|) ) in H6; auto.
    -- apply NNPP; intro. apply Notle in H6; auto. destruct H5.
       + subst. apply (@legRf x 0) in H6; auto.
       + destruct H5.
         ++ apply AbPRC in H5; auto. rewrite <- H5 in H6.
            apply (@legRf x (|y|) ) in H6; auto.
         ++ assert((x ≤ y /\ y < 0) \/ (x < y /\ y ≤ 0)). 
            { left. split; auto. } 
            apply FAT172 in H7; auto. apply (@lgRf x 0) in H7; auto.
  - intros. New H0. apply adsRC in H2.
    assert(|y| ≥ 0). { apply FAT170; auto. }
    destruct H1. Absurd. apply Notle in H5; auto. 
    New H. apply (@FAT167 x 0) in H6; auto. destruct H6.
    -- subst. rewrite Zmin in H1. apply (@lgRf y 0) in H4; auto. contradiction.
    -- destruct H6.
       + New H0. apply (@FAT167 y 0) in H7; auto. destruct H7.
         ++ subst. rewrite Zabs in H5. 
            apply (@legRf x 0) in H5; auto. contradiction.
         ++ destruct H7.
            { rewrite AbPRC in H5; auto. 
              apply (@legRf x y) in H5; auto. contradiction. }
            { rewrite AbNRC in H5; auto. apply (FAT183c1 (-x) y) in H1; auto.
              rewrite FAT177 in H1; auto. 
              apply (@legRf x (-y)) in H1; auto. contradiction. }
       + apply (FAT183c1 (x) 0) in H6; auto. rewrite Zmin in H6.
         apply (@FAT171 0 (-x) y) in H6; auto. apply AbPRC in H6; auto. 
         rewrite H6; auto.
Qed.

Corollary Ab2 : ∀ x y, x ∈ RC -> y ∈ RC -> |x + y| ≤ |x| + |y|.
Proof.
  intros. New H. apply (@FAT167 x 0)in H1; auto. 
  New H0. apply (@FAT167 y 0)in H2; auto. generalize Zabs; intros. 
  rename H3 into Hab0.
  New H0; apply AddRpb in H3; New H0; apply (@FAT175 0 y) in H4; auto;
  New H0; apply adsRC in H5.
  New H; apply AddRpb in H6; New H; apply (@FAT175 0 x) in H7; auto;
  New H; apply adsRC in H8.
  destruct H1.
  - subst. rewrite H4, Hab0, H3. rewrite AddRpa; auto. red. right; auto.
  - destruct H1. 
    + New H1. apply AbPRC in H9; auto. destruct H2.
      ++ subst. rewrite H6, Hab0. rewrite AddRpb; auto. red. right; auto.
      ++ destruct H2.
         +++ New H2. apply AbPRC in H10; auto. 
             assert(| x + y | = x + y). { apply AbPRC; auto. } 
             rewrite H11, H10, H9. right; auto.
         +++ New H2. apply AbNRC in H10; auto. assert(x + y ∈ RC); auto. 
             New H11. apply (@FAT167 (x + y) 0) in H12; auto.
             destruct H12.
             { rewrite H12, H9, Hab0, H10. left. apply FAT182a2; auto. 
               apply (@FAT171 y 0 x); auto. }
             destruct H12.
             { New H12. apply AbPRC in H13; auto. rewrite H13, H9, H10. 
               left. apply (FAT190 x x (-y) y); auto. 
               left. split. right; auto. 
               New H2; apply FAT176c1 in H14; apply (@FAT171 y 0 (-y)); auto. }
             { New H12. apply AbNRC in H13; auto. rewrite H13, H9, H10. 
               left. New H. apply (FAT180 x y) in H14; auto. rewrite H14. 
               apply (FAT190 x (-x) (-y) (-y)); auto. right. split. 
               New H1; apply FAT176a1 in H15. apply (@FAT171 (-x) 0 x); auto. 
               right; auto.  }
    + New H1. apply AbNRC in H9; auto. destruct H2.
      ++ subst. rewrite H6, Hab0. rewrite AddRpb; auto. red. right; auto.
      ++ destruct H2.
         +++ New H2. apply AbPRC in H10; auto. assert(x + y ∈ RC); auto. 
             New H11. apply (@FAT167 (x + y) 0) in H12; auto.
             destruct H12.
             { rewrite H12, H9, Hab0, H10. left. New H0. 
               apply (@FAT175 (-x) y) in H13; auto. rewrite H13. 
               apply FAT182a2; auto. apply (@FAT171 x 0 y); auto. }
             destruct H12.
             { New H12. apply AbPRC in H13; auto. rewrite H13, H9, H10. 
               left. New H. apply (FAT190 (-x) x y y); auto. right. split. 
               New H1; apply FAT176c1 in H15; apply (@FAT171 x 0 (-x)); auto. 
               right; auto. }
             { New H12. apply AbNRC in H13; auto. rewrite H13, H9, H10. 
               left. New H. apply (FAT180 x y) in H14; auto. rewrite H14. 
               apply (FAT190 (-x) (-x) y (-y)); auto. left. split. right; auto.
               New H2; apply FAT176a1 in H15. apply (@FAT171 (-y) 0 y); auto. }
         +++ New H2. apply AbNRC in H10; auto. 
             assert(| x + y | = - (x + y)). { apply AbNRC; auto. } 
             rewrite H11, H10, H9. right; auto. apply FAT180; auto.
Qed.

Global Hint Resolve AbE Ab1 Ab2: core. 

Corollary Ab4 : ∀ x y, x ∈ RC -> y ∈ RC -> x > y -> |x - y| = x - y.
Proof.
  intros. apply AbPRC; auto.
Qed.

Corollary Ab6' : ∀ x y, x ∈ RC -> y ∈ RC -> y < x -> |y - x| = x - y.
Proof.
  intros. rewrite <- FAT178; auto. rewrite FAT181; auto. 
Qed.

Corollary Ab8 : ∀ x, x ∈ RC -> x <> 0 -> |x| > 0.
Proof.
  intros. New H. apply FAT170 in H1.
  destruct H1; auto. elim H0. 
  New H. apply (@FAT167 x 0) in H2; auto. destruct H2; auto.
  destruct H2. 
  - apply Ab4 in H2; auto. rewrite MinRpb in H2; auto. rewrite H2 in H1. auto.
  - apply Ab6' in H2; auto. rewrite MinRpb in H2; auto. rewrite H2 in H1. auto.
    rewrite MinRpa in H1; auto. assert( - x = 0); auto. 
    apply (FAT176b2 x) in H3; auto.
Qed.

Corollary Ab8' : ∀ x y, x ∈ RC -> y ∈ RC -> x <> y -> |x - y| > 0.
Proof.
  intros. apply Ab8; auto. 
Qed.

Global Hint Resolve Ab4 Ab6' Ab8: core. 

Theorem anRC : ∀ a n,
  IsSeq a -> n ∈ Nat -> a [n] ∈ RC.
Proof.
  intros. 
  set (J:= \{ λ r , ∃ t, t ∈ Nat /\ r = a[t] \}).
  assert (J ⊂ RC).
  { red; intros. unfold J in H1. appA2H H1. destruct H2, H2. rewrite H3.
    unfold IsSeq in H. destruct H, H4. 
    apply (xInX ran(a) a[x]); auto. unfold Range. rewrite <- H3. appA2G; auto. 
    exists x. rewrite <- H4 in H2. New H2.
    unfold Domain in H2. appA2H H2. destruct H7.
    rewrite H3. apply Property_Value; auto. }
  apply (xInX J (a [n])); auto. unfold J. appA2G. unfold Ensemble. exists μ.
  apply MKT69b. unfold IsSeq in H. destruct H, H2. rewrite H2. auto.
Qed.

Global Hint Resolve anRC: core. 

Theorem MCTup : ∀ a y,
  Increase a -> Boundup_Seq y a -> ∃ z, z ∈ RC /\ Limit a z.
Proof.
  intros; red in H, H0. 
  set (J:= \{ λ r , ∃ t, t ∈ Nat /\ r = a[t] \}).
  assert (J ⊂ RC).
  { red; intros. unfold J in H1. appA2H H1. destruct H2, H2. rewrite H3.
    destruct H. unfold IsSeq in H. destruct H, H5. 
    apply (xInX ran(a) a[x]); auto. unfold Range. rewrite <- H3. appA2G; auto. 
    exists x. rewrite <- H5 in H2. New H2. rename H7 into dom. 
    unfold Domain in H2. appA2H H2. destruct H7.
    rewrite H3. apply Property_Value; auto. }
  rename H1 into HRC.
  assert (∃ p, supremum J p).
  { apply SupremumT.
    - auto.
    - red. intros. assert (a[One] ∈ μ). 
      { apply MKT69b. destruct H. unfold IsSeq in H. destruct H, H3. 
        rewrite H3. auto. }
      rename H2 into HOne. assert (a[One] ∈ J). { unfold J. appA2G. }
      rewrite H1 in H2. apply MKT16 in H2; auto.
    - exists y; red; intros. repeat split; auto.
      + destruct H0, H1; auto.
      + intros. unfold J in H1. appA2H H1. destruct H2, H2. subst.
        destruct H0, H3. apply H4; auto. }
  destruct H1 as [z H1]; New H1; destruct H1.
  New H1. unfold Boundup_Ens in H4. destruct H4, H5.
  exists z. split; auto. red; intros. destruct H. split; auto. split; auto. 
  intros. eapply Cor_supremum in H2; eauto. destruct H2, H2.
  unfold J in H2. appA2H H2. destruct H11 as [n []]. 
  exists n; intros. split; auto. intros. New H13. 
  apply (anRC a n0) in H15; auto.
  New H11. rename H16 into HnNat.
   apply (anRC a n) in H11; auto. 
  apply Ab1; auto. split.
  - apply H7 in H14; auto. subst.
    assert(((z - ε) ≤ (a[n]) /\ (a[n]) < (a[n0])) \/ 
    ((z - ε) < (a[n]) /\ (a[n]) ≤ (a[n0]))). { right. split; auto. } 
    apply FAT172 in H12; auto. apply (FAT188c1 (-ε) (a [n0] - z) (z)); auto.
    rewrite (@FAT175 (-ε) z); auto. rewrite MincEx1; auto.
  - assert(a [n0] ∈ J). { unfold J. appA2G. }
    apply H6 in H16. apply (FAT188c1 (a [n0] - z) ε z); auto. 
    rewrite MincEx1; auto.
    assert(((z ≥ a [n0]) /\ (ε > 0)) \/ ((z > a [n0]) /\ (ε ≥ 0))).
    { left. split; auto. } 
    apply FAT190 in H17; auto. rewrite AddRpb in H17.
    apply si2'; rewrite (@FAT175 ε z); auto. auto.
Qed.

Theorem MCTdown : ∀ a y,
  Decrease a -> Bounddown_Seq y a -> ∃ z, z ∈ RC /\ Limit a z.
Proof.
  intros; red in H, H0. 
  set (J:= \{ λ r , ∃ t, t ∈ Nat /\ r = a[t] \}).
  assert (J ⊂ RC).
  { red; intros. unfold J in H1. appA2H H1. destruct H2, H2. rewrite H3.
    destruct H. unfold IsSeq in H. destruct H, H5. 
    apply (xInX ran(a) a[x]); auto. unfold Range. rewrite <- H3. appA2G; auto. 
    exists x. rewrite <- H5 in H2. New H2. rename H7 into dom. 
    unfold Domain in H2. appA2H H2. destruct H7.
    rewrite H3. apply Property_Value; auto. }
  rename H1 into HRC.
  assert (∃ p, infimum J p).
  { apply InfimumT.
    - auto.
    - red. intros.
      assert (a[One] ∈ μ). 
      { apply MKT69b. destruct H. unfold IsSeq in H. destruct H, H3. 
        rewrite H3. auto. }
      rename H2 into HOne.
      assert (a[One] ∈ J). 
      { unfold J. appA2G. }
      rewrite H1 in H2. apply MKT16 in H2; auto.
    - exists y; red; intros. repeat split; auto.
      + destruct H0, H1; auto.
      + intros. unfold J in H1. appA2H H1. destruct H2, H2. subst.
        destruct H0, H3. apply H4; auto. }
  destruct H1 as [z H1]; New H1; destruct H1.
  New H1. unfold Bounddown_Ens in H4. destruct H4, H5.
  exists z. split; auto. red; intros. destruct H. split; auto. split; auto. 
  intros. eapply Cor_infimum in H2; eauto. destruct H2, H2.
  unfold J in H2. appA2H H2. destruct H11 as [n []].
  exists n; intros. split; auto. intros. New H13. 
  apply (anRC a n0) in H15; auto.
  New H11. rename H16 into HnNat.
  apply (anRC a n) in H11; auto. 
  apply Ab1; auto. split.
  - assert(a [n0] ∈ J). { unfold J. appA2G. }
    apply H6 in H16. apply (FAT188c1 (-ε) (a [n0] - z) z); auto. 
    rewrite MincEx1; auto. apply FAT176a1 in H9. 
    apply si2 in H9. apply sie2 in H16.
    assert(((0 ≥ (- ε)) /\ (a [n0] > z)) \/ ((0 > (- ε)) /\ (a [n0] ≥ z))). 
    { right. split; auto. } 
    apply FAT190 in H17; auto. apply si2' in H17. rewrite AddRpa in H17; auto.
  - apply H7 in H14; auto. subst.
    assert(((a[n0]) ≤ (a[n]) /\ (a[n]) < (z + ε)) \/ ((a[n0]) < (a[n]) 
    /\ (a[n]) ≤ (z + ε))). { left. split; auto. } 
    apply FAT172 in H12; auto. apply (FAT188c1 (a [n0] - z) (ε) (z)); auto.
    rewrite MincEx1; auto. rewrite @FAT175 in H12; auto.
Qed.
