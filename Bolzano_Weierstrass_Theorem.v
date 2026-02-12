(**********************************************************************)
(*     This is part of Real_Completeness, it is distributed under     *)
(*    the terms of the GNU Lesser General Public License version 3    *)
(*             (see file LICENSE for more details)                    *)
(*                                                                    *)
(*                     Copyright 2026-2031                            *)
(*              Ce Zhang, Guowei Dou and ωensheng Yu                  *)
(**********************************************************************)

Require Export Finite_Covering_Theorem.

Fact Zmin' : 0 = -0.
Proof.
  pose proof Zmin. auto.
Qed.

Global Hint Resolve Zmin': core. 

Fact AbNRC0 : ∀ y, y ∈ RC -> y ≤ 0 -> |y| = -y.
Proof.
  intros. destruct H0; auto. subst; rewrite Zabs; auto. 
Qed.

Fact AbPRC0 : ∀ y, y ∈ RC -> 0 ≤ y -> |y| = y.
Proof.
  intros. destruct H0; auto. subst; rewrite Zabs; auto. 
Qed.

Global Hint Resolve AbNRC0 AbPRC0: core. 

Corollary Max_nat_2 : ∀ N0 N1, N0 ∈ Nat -> N1 ∈ Nat -> 
  (∃ N, N ∈ Nat /\ NtoR N0 < NtoR N /\ NtoR N1 < NtoR N).
Proof.
  intros. exists (N0 + N1)%Nat; split; auto. split.
  - apply NtoR3; auto. apply FAT18; auto.
  - apply NtoR3; auto. rewrite FAT6; auto. apply FAT18; auto.
Qed.

Fact Leq_P4 : ∀ x y, x ∈ RC -> y ∈ RC -> x ≤ y \/ y ≤ x.
Proof.
  intros. New H. apply (@FAT167 x y) in H1; auto. destruct H1 as [H1 | []].
  - left; right; auto.
  - right; left; auto.
  - left; left; auto.
Qed.

Corollary Max_nat_3 : ∀ N0 N1 N2, N0 ∈ Nat -> N1 ∈ Nat -> N2 ∈ Nat -> 
  (∃ N, N ∈ Nat /\ NtoR N0 < NtoR N /\ NtoR N1 < NtoR N /\ NtoR N2 < NtoR N).
Proof.
  intros. destruct (Leq_P4 (NtoR N0) (NtoR N1)) as [Ha | Ha]; auto.
  - destruct (Leq_P4 (NtoR N1) (NtoR N2)) as [Hb | Hb]; auto.
    + exists (N2 + One)%Nat.
      assert (NtoR N0 ≤ NtoR N2). 
      { apply (T173 _ (NtoR N1) _); auto. }
      assert (NtoR N2 < NtoR (N2 + One)%Nat). 
      { apply NtoR3; auto. apply FAT18; auto. }
      assert (NtoR N0 < NtoR (N2 + One)%Nat). 
      { apply (FAT172 _ (NtoR N2) _); auto. }
      assert (NtoR N1 < NtoR (N2 + One)%Nat). 
      { apply (FAT172 _ (NtoR N2) _); auto. }
      repeat split; auto.
    + exists ((N1 + One)%Nat).
      assert (NtoR N1 < NtoR (N1 + One)%Nat). 
      { apply NtoR3; auto. apply FAT18; auto. }
      assert (NtoR N0 < NtoR (N1 + One)%Nat). 
      { apply (FAT172 _ (NtoR N1) _); auto. }
      assert (NtoR N2 < NtoR (N1 + One)%Nat). 
      { apply (FAT172 _ (NtoR N1) _); auto. }
      repeat split; auto.
  - destruct (Leq_P4 (NtoR N0) (NtoR N2)) as [Hb | Hb]; auto.
    + exists ((N2 + One)%Nat).
      assert (NtoR N2 < NtoR (N2 + One)%Nat). 
      { apply NtoR3; auto. apply FAT18; auto. }
      assert (NtoR N2 < NtoR (N2 + One)%Nat). 
      { apply NtoR3; auto. apply FAT18; auto. }
      assert (NtoR N0 < NtoR (N2 + One)%Nat). 
      { apply (FAT172 _ (NtoR N2) _); auto. }
      assert (NtoR N1 < NtoR (N2 + One)%Nat). 
      { apply (FAT172 _ (NtoR N0) _); auto. }
      repeat split; auto.
    + exists ((N0 + One)%Nat).
      assert (NtoR N0 < NtoR (N0 + One)%Nat). 
      { apply NtoR3; auto. apply FAT18; auto. }
      assert (NtoR N1 < NtoR (N0 + One)%Nat). 
      { apply (FAT172 _ (NtoR N0) _); auto. }
      assert (NtoR N2 < NtoR (N0 + One)%Nat). 
      { apply (FAT172 _ (NtoR N0) _); auto. }
      repeat split; auto.
Qed.

Fact Abs2 : ∀ y, y ∈ RC -> | - y | = |y|.
Proof. 
  intros. New H; apply (@FAT167 y 0) in H0; auto. destruct H0 as [|[]].
  - subst. rewrite Zmin, Zabs; auto.
  - rewrite AbNRC, AbPRC; auto.
  - New H0. apply AbNRC in H0; auto. rewrite H0. apply FAT176c1 in H1; auto.
Qed.

Fact Abs3 : ∀ y, y ∈ RC -> | | y | | = |y|.
Proof.
  intros. New H; apply (@FAT167 y 0) in H0; auto. destruct H0 as [|[]].
  - subst. rewrite Zabs, Zabs; auto.
  - rewrite AbPRC, AbPRC; auto.
  - auto. 
Qed.

Global Hint Resolve Abs2 Abs3: core. 

Global Hint Resolve FAT176a1 FAT176b1 FAT176c1: core. 

Proposition Abs5 : ∀ x y, x ∈ RC -> y ∈ RC -> |(x + y)| ≤ |x| + |y|
  /\ |(x - y)| ≤ |x| + |y| /\ |(|x| - |y|)| ≤ |(x - y)|.
Proof.
  intros. repeat split.
  - apply Ab2; auto.
  - New H. apply (Ab2 x (-y)) in H1; auto. rewrite Abs2 in H1; auto.
  - New H; apply (@FAT167 x 0) in H1; auto.
    New H0; apply (@FAT167 y 0) in H2; auto.
    New H; apply (@FAT167 x y) in H3; auto.
    destruct H1 as [|[]], H2 as [|[]].
    + subst. rewrite Zmin, Zabs, AddRpb, AddRpa, Zmin, Zabs; auto.
      red; right; auto.
    + subst. rewrite Zabs, MinRpa, MinRpa; auto.
      rewrite Abs2, Abs2, Abs3; auto. red; right; auto.
    + subst. rewrite Zabs, MinRpa, MinRpa; auto.
      rewrite Abs2, Abs2, Abs3; auto. red; right; auto.
    + subst. rewrite Zabs, MinRpb, MinRpb; auto.
      rewrite Abs3; auto. red; right; auto.
    + destruct H3 as [|[]].
      * subst. rewrite xminx, xminx; auto. red; right; auto.
      * rewrite (AbPRC x), (AbPRC y); auto. red; right; auto.
      * rewrite (AbPRC x), (AbPRC y); auto. red; right; auto.
    + assert(x > y). { apply (@FAT171 _ 0 _); auto. }
      assert(x - y > 0); auto. 
      rewrite (AbPRC x), (AbNRC y), FAT177, (AbPRC (x - y)); auto.
      apply (T173 _ (|x| + |y|) _); auto.
      rewrite (AbPRC x), (AbNRC y); auto. red; right; auto.
    + subst. assert(-x > 0). { apply FAT176c1; auto. }
      rewrite Zabs, MinRpb, MinRpb, (AbNRC x), (AbPRC (-x)); auto.
      red; right; auto.
    + assert(x < y). { apply (@FAT171 _ 0 _); auto. }
      assert(x - y < 0); auto. 
      rewrite (AbNRC x), (AbPRC y), (AbNRC (x - y)); auto.
      assert(-x ∈ RC); auto. apply (Ab2 (-x) (-y)) in H6; auto.
      assert(-x > 0); auto. rewrite (AbPRC (-x)), (AbNRC (-y)) in H6; auto. 
      rewrite FAT180; auto.
    + destruct H3 as [|[]].
      * subst. rewrite xminx, xminx; auto. red; right; auto.
      * rewrite (AbNRC x), (AbNRC y), FAT177, AbE, FAT175;auto. red; right;auto.
      * rewrite (AbNRC x), (AbNRC y), FAT177, AbE, FAT175;auto. red; right;auto.
Qed.

Proposition Abs8 : ∀ x y z, x ∈ RC -> y ∈ RC -> z ∈ RC
  -> |x - y| ≤ |x - z| + |y - z|.
Proof.
  intros. assert(x - y = (x - z) - (y - z)).
  { rewrite FAT180, FAT177; auto. rewrite (@FAT175 (-y) z); auto. 
    symmetry. apply MincEx4; auto. }
  rewrite H2. apply Abs5; auto.
Qed.

Corollary FAT190' : ∀ x y z w, x ∈ RC -> y ∈ RC -> z ∈ RC
  -> w ∈ RC -> x ≤ y -> z < w -> x + z < y + w.
Proof.
  intros. apply FAT190; auto.
Qed.

Global Hint Resolve Abs5 Abs8: core.
 
Fact aver_Cor6 : ∀ x y, x ∈ RC -> y ∈ RC 
  -> y + (x - y) / (1 + 1) = (x + y) / (1 + 1).
Proof.
  intros. rewrite <- divRp4; auto.
  assert(x / (1 + 1) ∈ RC). { apply divRc3; auto. }
  assert(y / (1 + 1) ∈ RC). { apply divRc3; auto. }
  assert(x / (1 + 1) + - y / (1 + 1) = x / (1 + 1) - y / (1 + 1)).
  { rewrite divRp3; auto. }
  rewrite H3. rewrite (@FAT175 (x / (1 + 1)) (- (y / (1 + 1)))), 
  <- FAT186; auto. New H0. apply (aver_Cor5 y 0) in H4; auto. rewrite AddRpb, 
  MinRpb in H4; auto. rewrite H4. rewrite FAT175, divRp4; auto.
Qed.

Global Hint Resolve aver_Cor6 : core.

Theorem MathInd_Ma : ∀ E, E ⊂ Nat -> One ∈ E
  -> (∀ x, x ∈ E -> (x + One)%Nat ∈ E) -> E = Nat.
Proof.
  intros. 
  apply MKT27; split; auto. unfold Included; intros.
  assert((∀ z, z ∈ Nat -> z ∈ E)).
  { apply Mathematical_Induction_Nat. 
    - auto.
    - intros. apply H1; auto. }
  apply H3; auto.
Qed.

Theorem one_is_min_in_N : ∀ n, n ∈ Nat -> NtoR n ≤ 1 -> n = One.
Proof.
  intros. pose proof @FAT24 n H. destruct H0.
  - assert(1 = NtoR One); auto. rewrite H2 in H0. apply NtoR3' in H0; auto.
    apply legNf in H0; auto. contradiction.
  - assert(1 = NtoR One); auto. rewrite H2 in H0. apply NtoR1' in H0; auto.
Qed.

Theorem one_is_min_in_N' : ∀ n, n ∈ Nat -> 1 ≤ NtoR n.
Proof.
  intros. pose proof @FAT24 n H. destruct H0.
  - apply NtoR3 in H0; auto. assert(1 = NtoR One); auto. rewrite H1; auto.
    red; left; auto.
  - subst; auto. assert(1 = NtoR One); auto. rewrite H0; red; right; auto.
Qed.

Proposition Nat_P4 : ∀ m n, m ∈ Nat -> n ∈ Nat -> NtoR n < NtoR (m + One)%Nat
  -> NtoR n ≤ NtoR m.
Proof.
  intros. apply NtoR3' in H1; auto. apply @FAT25a in H1; auto. destruct H1.
  - apply FAT20a in H1; auto. apply NtoR3 in H1; auto. red; left; auto.
  - apply FAT20b in H1; auto. subst. red; right; auto.
Qed.

Corollary Nat_P4a: ∀ m n, m ∈ Nat -> n ∈ Nat -> NtoR (n + One)%Nat ≤ NtoR m 
  -> NtoR n < NtoR m.
Proof.
  intros. assert((n + One ≤ m)%Nat).
  { destruct H1. 
    - apply NtoR3' in H1; auto.
    - apply NtoR1' in H1; auto. }
  apply @FAT25b in H2; auto. apply NtoR3; auto.
Qed.

Proposition Nat_P4b : ∀ m n, m ∈ Nat -> n ∈ Nat -> NtoR n < NtoR m 
  -> NtoR (n + One)%Nat ≤ NtoR m.
Proof.
  intros. apply NtoR3' in H1; auto. apply @FAT25a in H1; auto. 
  assert(NtoR (n + One)%Nat ≤ NtoR m).
  { destruct H1. 
    - apply NtoR3 in H1; auto. red; left; auto.
    - apply NtoR1 in H1; auto. red; right; auto. }
  auto.
Qed.

(* 有限覆盖 -> 聚点原理 *)


(* 聚点定义 *)

Definition AccumulationPoint e E := ∀ x, x ∈ RC -> x > 0 -> ∃ y, y ∈ RC 
  /\ y ∈ ］ (e - x) , (x + e) ［ /\ y ∈ E /\ y <> e.

Theorem MKT160_Cor : ∀ {f}, Function f -> Ensemble f -> Finite dom(f) 
  -> Finite ran(f).
Proof.
  intros. pose proof @MKT160 f H H0. red. red in H2. destruct H2.
  - red in H1. pose proof Property_W. red in H3. destruct H3. red in H4. pose 
    proof H4 (P[dom( f)]) H1. red in H5. pose proof H5 (P [ran( f)]) H2; auto.
  - rewrite H2; auto.
Qed.

Theorem APT : ∀ E x y, x < y -> ~ Finite E -> Bounddown_Ens E x -> 
  Boundup_Ens E y -> ∃ e, AccumulationPoint e E.
Proof.
  assert (∀ E, ~ (∃ e, AccumulationPoint e E) -> ∀ z, ∃ δ, δ ∈ RC /\ δ > 0 
    /\ (∀ w, w ∈  ］ (z - δ), (δ + z) ［ /\ w ∈ E -> w = z)) as G.
  { intros. Absurd; elim H. exists z; red; intros. 
    Absurd; elim H0. exists x. split; auto. split; intros; auto. 
    destruct H4; Absurd. elim H3. exists w. split; auto. 
    appA2H H4. destruct H7; auto. }
  intros. red in H1, H2; Absurd. destruct H1 as [E_Included_RC[x_in_RC]].
  destruct H2 as [_[y_in_RC]]. pose proof (G E H3).
  set(cH := \{ λ u, ∃ z δ : Class,z ∈ RC /\ δ ∈ RC /\ δ > 0
    /\ (∀w : Class,w ∈ ］ (z - δ), (δ + z) ［ /\ w ∈ E -> w = z)
    /\ u = ］ (z - δ), (δ + z) ［  \}).
  assert(IsOpenIntervalFamily cH).
  { red. intros. appA2H H5. destruct H6 as [z[ δ[_[_[_[]]]]]].
    exists (z - δ). exists (δ + z). auto. }
  assert(OpenCover x y cH).
  { red. split; auto. split; auto. split; auto. split; auto. intros.
    New H6. appA2H H7. destruct H8, H9, H10, H11. pose proof H4 c.
    destruct H13, H13, H14. 
    exists (］ (c - x0), (x0 + c) ［). split.
    - appA2G. 
      + assert(］ (c - x0), (x0 + c) ［ ⊂ RC ).
        { red. intros. appA2H H16. destruct H17; auto. }
        apply MKT33 in H16; auto. apply EnRC.
      + exists c. exists x0. split; auto.
    - appA2G. repeat split; auto. }
  apply FinCoverT in H6; destruct H6 as [H6 [H7[H8[H9[ch[H11[]]]]]]].
  assert( E ⊂ ［ x, y ］).
  { red. intros. pose proof H1 z H13. pose proof H2 z H13. appA2G.
    repeat split; auto. }
  assert(∀ m, m ∈ E -> m ∈ ［ x, y ］).
  { intros. red in H13. apply H13; auto. }
  set(ch' := \{ λ u, ∃z δ : Class,z ∈ RC /\ δ ∈ RC /\ δ > 0 
    /\ ( ］ (z - δ), (δ + z) ［ ) ∈ ch
    /\ u = z  \}).
  set (fun_ch_to_ch' := \{\  λ u v, 
     ∃z δ : Class,z ∈ RC /\ δ ∈ RC /\ δ > 0 /\ u = ］ (z - δ), (δ + z) ［ 
    /\ u ∈ ch /\ v = z \}\ ).
  assert(Function fun_ch_to_ch') as Function_fun_ch_to_ch'.
  { intros. split; intros. apply poisre.
    appA2H H15. appA2H H16. destruct H17 as [x1[y1[]]]. 
    destruct H18 as [x2[y2[]]]. destruct H19 as [z1[δ1[H21[H22[H23[H24[]]]]]]]. 
    destruct H20 as [z2[δ2[H20[H26[H27[H28[]]]]]]]. subst.
    pose proof MKT49b x0 y0 H15 as []. New H17.
    apply (MKT55 x0 y0 ］ (z1 - δ1), (δ1 + z1) ［ z1) in H28 as []; auto.
    New H18. New H16. apply MKT49c2 in H32; auto.
    apply (MKT55 x0 z ］ (z2 - δ2), (δ2 + z2) ［ z2) in H31 as []; auto.
    rewrite H28 in H31.
    assert(z1 - δ1 < δ1 + z1); auto. 
    assert(z2 - δ2 < δ2 + z2); auto. 
    apply OpenInterval_Cor1 in H31 as []; auto.
    apply (FAT188b2 (z1 - δ1) (z2 - δ2) (δ1 + z1)) in H31; auto.
    assert(z1 - δ1 + (δ1 + z1) = z1 + z1); auto. 
    rewrite H37 in H31. rewrite H36 in H31.
    assert(z2 - δ2 + (δ2 + z2) = z2 + z2); auto. 
    rewrite H38 in H31. rewrite <- dou3' in H31; auto. 
    rewrite <- (dou3' z2) in H31; auto. apply mulEql'  in H31; auto.
    subst. auto. }
  assert(dom(fun_ch_to_ch') = ch) as dom_fun_ch_to_ch'.
  { apply AxiomI. intro a. split; intros.
    - apply AxiomII in H15 as [H15[]]. apply AxiomII' in H16 as [_[]]; auto.
      destruct H16 as[δ[_[_[_[[]]]]]], H16; auto.
    - red in H11. New H15. rename H16 into a_in_ch. apply H11 in H15. 
      appA2H H15. destruct H16 as [z[δ[H17[H18[]]]]], H19. rewrite H20. 
      rewrite H20 in H15, a_in_ch. 
      appA2G. exists z. apply AxiomII'; repeat split; auto.
      + apply MKT49a; auto. unfold Ensemble; eauto.
      + exists z. exists δ. repeat split; auto. }
  assert(ran(fun_ch_to_ch') = ch') as ran_fun_ch_to_ch'.
  { apply AxiomI. intro a. split; intros.
    - appA2G. apply AxiomII in H15 as [H15[]]. 
      apply AxiomII' in H16 as [H16[]]; auto.
      destruct H17 as [δ[H17[H18[H19[H20[]]]]]]. exists x1. exists δ.
      New H21. rewrite H20 in H21. repeat split; auto.
    - appA2H H15. 
      destruct H16 as [z[δ[H17[H18[]]]]], H19. rewrite H20. rewrite H20 in H15. 
      appA2G. exists ］ (z - δ), (δ + z) ［. apply AxiomII'; repeat split; auto.
      + apply MKT49a; auto. unfold Ensemble; eauto.
      + exists z. exists δ. repeat split; auto. }
  assert(Ensemble ch) as Ensemble_ch.
  { apply Property_Finite; auto. }
  assert(Ensemble ch') as Ensemble_ch'.
  { assert(ch' ⊂ RC).
    { unfold Included. intros. appA2H H15. 
      destruct H16, H16, H16, H17, H18, H19. rewrite <- H20 in H16; auto. }
    apply MKT33 in H15; auto. apply EnRC. }
  assert(Finite ch') as Finite_ch'.
  { rewrite <- ran_fun_ch_to_ch'. rewrite <- ran_fun_ch_to_ch' in Ensemble_ch'.
    rewrite <- dom_fun_ch_to_ch' in Ensemble_ch, H10.
    apply (@MKT160_Cor fun_ch_to_ch'); auto. apply MKT75; auto. }
  assert(∀ m, m ∈ E -> (m ∈ ch')).
  { intros. pose proof H14 m H15. red in H12. 
    destruct H12 as[_[_[_[_ H12]]]].
    pose proof H12 m H16. destruct H17, H17. appA2G. red in H11. 
    pose proof H11 x0 H17. appA2H H19. destruct H20 as [z[δ[H25[H21[H22[]]]]]].
    exists z. exists δ. repeat split; auto. rewrite <- H23; auto. 
    apply H20. split. rewrite <- H23; auto. auto. }
  assert(E ⊂ ch').
  { red. intros. apply H15; auto. }
  assert(Finite E).
  { intros. apply (@finsub ch' E); auto. }
  elim H0; auto.
Qed.

Fact OpenInterval_Cor0a_in_RC : ∀ a b z, z ∈ RC -> z ∈ ］ a , b ［ -> a ∈ RC.
Proof.
  intros. appA2H H0. destruct H1, H2, H3, H4; auto.
Qed. 

Fact OpenInterval_Cor0b_in_RC : ∀ a b z, z ∈ RC -> z ∈ ］ a , b ［ -> b ∈ RC.
Proof.
  intros. appA2H H0. destruct H1, H2, H3, H4; auto.
Qed. 

Fact addRdom : dom(addR 1) = RC.
Proof.
  apply AxiomI; split. 
  + intros. unfold addR in H. appA2H H. destruct H0. appA2H H0. destruct H1.
    destruct H1. destruct H1, H2. New H0. apply MKT49b in H4. destruct H4. 
    apply (MKT55 z x x0 x1) in H1; auto. destruct H1. subst; auto.
  + intros. unfold minR. appA2G. assert (Ensemble z); unfold Ensemble; eauto.
    New H. assert(1 + z ∈ RC); auto. assert (Ensemble (1 + z)); 
    unfold Ensemble; eauto. exists(1 + z). appA2G. exists(z). exists(1 + z).
    assert(1 ∈ NRC -> False). 
    { intro. assert(1 > 0); auto. assert(1 ∈ PRC); auto. 
      apply FAT169b in H4. apply (@lgRf 1 0); auto. }
     repeat split; auto.
    - apply AddRpc; auto.
    - intros. apply H4 in H5; contradiction.
    - intros. pose proof not1_0; elim H6; auto.
    - intros. rewrite H5; auto.
    - intros. apply AddRpe; auto.
    - intros. apply AddRpg; auto.
    - intros. apply AddRpi; auto.
    - intros. apply AddRpf; auto.
    - intros. apply AddRph; auto.
    - intros. apply AddRpj; auto.
Qed. 

Fact addRC2 : ∀ e, 1 + e ∈ RC -> e ∈ RC.
Proof.
  intros. assert(1 ∈ RC); auto.
  assert(dom(addR 1) = RC). { apply addRdom. }
  assert(Function minR). { apply mirf. }
  assert (Ensemble (1 + e)); unfold Ensemble; eauto. rewrite <- H1.
  apply NNPP. intro. apply MKT69a in H4. rewrite H4 in H. 
  assert (Ensemble μ); unfold Ensemble; eauto. 
  assert (~ Ensemble μ); apply MKT39. auto.
Qed. 

Proposition AccumulationPoint_Core : ∀ E e, AccumulationPoint e E -> e ∈ RC.
Proof.
  intros.
  
  New H. red in H0. assert(1 ∈ RC); auto. apply H0 in H1; auto. 
  destruct H1, H1, H2. 
  apply (OpenInterval_Cor0b_in_RC (e - 1) (1 + e) x) in H2; auto.
  apply addRC2; auto.
Qed. 

Definition AccumulationPoint' e E := ∀ x, x ∈ RC -> x > 0 -> e ∈ RC 
  -> ~ Finite \{ λ z , z ∈ ］ (e - x) , (x + e) ［ /\ z ∈ E /\ z ∈ RC\}.

Definition No_Empty A := ∃ x, In x A.

Fact Finite_RC_has_min : ∀ S, S ⊂ RC -> Finite S -> ~ S = Φ 
  -> ∃ m, m ∈ S /\ (∀ y, y ∈ S -> m ≤ y).
Proof.
  set (P := fun k => (∀ S,S ⊂ RC -> P[S] = k -> ~ S = Φ 
    -> ∃m, m ∈ S /\(∀ y, y ∈ S -> m ≤ y))).
  assert(∀ n, n ∈ ω -> P n).
  { apply Mathematical_Induction.
    - red. intros. pose proof @carE S H0. subst. elim H1; auto.
    - intros. red. red in H0. intros.
      assert(exists x0, x0 ∈ S).
      { Absurd. elim H3. 
        assert(∀ x0, ~ x0 ∈ S). { Absurd. elim H4. 
          pose proof not_all_not_ex Class _ H5 as []. exists x; auto. }
        apply NEexE in H3 as []. pose proof H5 x. elim H6; auto. }
      destruct H4 as [x0].
      set(S' := \{ λ u, ~ u = x0 /\ u ∈ S \}).
      assert(S = S' ∪ [x0]).
      { apply AxiomI. split; intros.
        + unfold Union. appA2G. TF(z ∈ S'); auto. right. Absurd. elim H6.
          appA2G. split; auto. red in H7. red; intros. apply H7. subst. 
          unfold Singleton. appA2G.
        + unfold Union in H5. appA2H H5. destruct H6.
          * appA2H H6. destruct H7; auto.
          * unfold Singleton in H6. appA2H H6.
            assert(Ensemble x0). { unfold Ensemble; eauto. }
            apply MKT19 in H8. apply H7 in H8. subst; auto. }
      assert(~ x0 ∈ S').
      { Absurd. apply NNPP' in H6. appA2H H6. destruct H7. elim H7; auto. }
      assert(S' ⊂ S).
      { red. intros. appA2H H7. destruct H8; auto. }
      assert(Finite S).
      { red. rewrite H2. apply MKT134; auto. }
      assert(Finite S').
      { red. apply finsub in H7; auto. }
      assert(Ensemble x0).
      { red; eauto. }
      assert(MK_Structure1.P [S'] = k).
      { New H10. apply (@finue S' x0) in H11; auto. rewrite <- H5 in H11.
        rewrite H2 in H11. unfold PlusOne in H2. New H9. red in H12.
        apply MKT136; auto. }
      assert(S' ⊂ RC).
      { red. intros. red in H1, H7. apply H7 in H12; auto. }
      TF(S' = Φ).
      + rewrite H13 in H5. rewrite MKT17 in H5. subst. exists x0. split; auto.
        intros. red; right. appA2H H5. apply MKT19 in H10. 
        pose proof H11 H10; auto.
      + New H12. apply H0 in H14; auto. destruct H14 as [m[]].
        assert(m ∈ RC). { red in H1, H7. apply H7 in H14; auto. }
        assert(x0 ∈ RC). { red in H1. apply H1 in H4; auto. }
        TF(m ≤ x0).
        * exists m. split. red in H7. apply H7; auto. intros. rewrite H5 in H19. 
          appA2H H19. destruct H20. apply H15; auto. appA2H H20. 
          apply MKT19 in H10. apply H21 in H10. rewrite H10; auto.
        * apply NotleR in H18; auto. exists x0. split.
          ** rewrite H5. appA2G.
          ** intros. assert(y ∈ RC). { red in H1. apply H1 in H19; auto. }
             rewrite H5 in H19. appA2H H19. destruct H21.
             apply H15 in H21; auto. red; left. apply (FAT172 x0 m y); auto.
             appA2H H21. apply MKT19 in H10. apply H22 in H10. rewrite H10;auto.
             red; right; auto. }
  intros. unfold P in H. red in H1. pose proof (H MK_Structure1.P [S]) H1.
  assert(MK_Structure1.P [S] = MK_Structure1.P [S]); auto.
Qed.

Corollary Cor_acc : ∀ e E, AccumulationPoint e E -> AccumulationPoint' e E.
Proof.
  intros. red. red in H. intros. rename H2 into e_in_RC.
  Absurd; apply (NNPP (Finite \{ λ z ,z ∈ ］ (e - x), (x + e) ［ 
  /\ z ∈ E /\ z ∈ RC\})) in H2.
  set(Abs := \{λ v, exists u, 
    u ∈ \{ λ z , z ∈ ］ (e - x), (x + e) ［ /\ z ∈ E /\ z ≠ e /\ z ∈ RC \} 
    /\ v = | u - e| \}).
  set(eNeighborhood_and_E := \{ λ z, z ∈ ］ (e - x), (x + e) ［ /\ z ∈ E 
  /\ z ≠ e /\ z ∈ RC \}).
  set(f := \{\ λ u v, u ∈ eNeighborhood_and_E /\ v = | u - e| \}\).
  assert(Abs ⊂ RC). 
  { red. intros. appA2H H3. destruct H4 as [u[]]. appA2H H4. destruct H6.
    New H6. appA2H H8. destruct H9. rewrite H5. apply adsRC; auto. }
  assert(Finite Abs). 
  { assert(Function f).
    { intros. split; intros. apply poisre.
      appA2H H4. appA2H H5. destruct H6 as [x1[y1[]]]. 
      destruct H7 as [x2[y2[]]]. destruct H8, H9. 
      apply MKT49b in H4 as []. apply MKT49b in H5 as []. 
      apply MKT55 in H6 as []; auto. apply MKT55 in H7 as []; auto.
      subst; auto. }
    assert(dom(f) = eNeighborhood_and_E).
    { apply AxiomI. intro u. split; intros.
      - apply AxiomII in H5 as [H5[]]. apply AxiomII' in H6 as [_[]]; auto.
      - appA2H H5. destruct H6, H7, H8. 
        appA2G. exists (| u - e |). apply AxiomII'; repeat split; auto.
        + apply MKT49a; auto. unfold Ensemble; eauto.
        + appA2G. }
    assert(ran(f) = Abs).
    { apply AxiomI. intro v. split; intros.
      - appA2G. appA2H H6. destruct H7. appA2H H7. destruct H8, H8, H8, H9.
        apply MKT49b in H7 as []. apply MKT55 in H8 as []; auto. subst.
        exists x1. split; auto.
      - appA2H H6. destruct H7, H7. appA2H H7. destruct H9, H10, H11. subst.
        appA2G. exists x0. appA2G. exists x0. exists (| x0 - e |). 
        repeat split; auto. appA2G. }
    assert(Finite eNeighborhood_and_E).
    { assert(eNeighborhood_and_E 
         ⊂ \{ λ z, z ∈ ］ (e - x), (x + e) ［ /\ z ∈ E /\ z ∈ RC \}).
      { red. intros. appA2G. appA2H H7. destruct H8, H9, H10. 
        repeat split; auto. }
      apply (@finsub (\{ λ z,z ∈ ］ (e - x), (x + e) ［ /\ z ∈ E /\ z ∈ RC \}) 
        eNeighborhood_and_E); auto. }
      rewrite <- H5 in H7. rewrite <- H6. apply MKT160_Cor; auto. 
      unfold Ensemble. apply MKT75; auto. rewrite H5. 
      apply Property_Finite; auto. rewrite H5 in H7; auto. }
  TF(eNeighborhood_and_E = Φ).
  - pose proof H x H0 H1. destruct H6 as [y0[H6[H7[H8]]]]. assert(~ y0 ∈ Φ). 
  { Absurd. apply NNPP' in H10. apply MKT16; contradiction. }
    rewrite <- H5 in H10. elim H10. appA2G.
  - assert(Abs ≠ Φ) as Abs_NotΦ.
    { Absurd. 
      assert(Abs = Φ). { red in H6. Absurd. apply H6 in H7; contradiction. }
      assert(∀ a, ~ a ∈ Abs). 
      { intros. rewrite H7. Absurd. apply NNPP' in H8.
        apply MKT16 in H8; contradiction. }
      New H5. apply NEexE in H9 as [x0]. appA2H H9.
      assert((| x0 - e |) ∈ RC). 
      { apply adsRC; auto. destruct H10. appA2H H10. destruct H12. auto. }
      assert(Ensemble (| x0 - e |)); unfold Ensemble; eauto.
      assert(| x0 - e | ∈ Abs). 
      { appA2G. exists x0. split; auto. appA2G. }
      apply NEexE; eauto. }
    apply Finite_RC_has_min in H4; auto. destruct H4 as [xmin[]].
    assert(xmin > 0). 
    { appA2H H4. destruct H7 as [x0[]]. rewrite H8.
      assert((x0 - e) ∈ RC). 
      { appA2H H7. destruct H9. appA2H H9. destruct H11. auto. }
      apply FAT170 in H9. red in H9. destruct H9; auto. 
      appA2H H7. destruct H10, H11. assert(| x0 - e | = 0); auto. destruct H12.
      apply Ab9 in H13; auto. }
    New H7. rename H8 into xmin_g0.
    New H6. apply H in H7 as [y[H7[H9[]]]]; auto.
    assert(| y - e | ∈ RC). 
    { apply adsRC; auto. }
    assert(xmin < x).
    { apply NEexE in H5 as [y1]. New H5. appA2H H13. destruct H14, H15, H16.
      assert(|y1 - e| ∈ Abs).
      { appA2G. unfold Ensemble. exists RC. apply adsRC; auto. }
      apply H8 in H18.
      assert(|y1 - e| < x).
      { appA2H H14. destruct H19, H20, H21, H22. apply Ab1; auto; split.
        * apply (FAT188c1 (-x) (y1 - e) e); auto. rewrite MincEx1; auto.
          rewrite FAT175; auto.
        * apply (FAT188c1 (y1 - e) x e); auto. rewrite MincEx1; auto. }
        apply (FAT172 xmin (| y1 - e |) x); auto. }
    assert(| y - e | ∈ Abs). 
    { appA2G. exists y. split; auto. appA2G. split; auto. appA2H H9. appA2G.
      destruct H14, H15, H16, H17. repeat split; auto.
      + assert(e - x < e - xmin). 
        { rewrite FAT175; auto. rewrite (@FAT175 e (- xmin)); auto.
          apply FAT188c2; auto. apply FAT183a1; auto. }
        apply (@FAT171 (e - x) (e - xmin) y); auto.
      + assert(e + xmin < x + e). 
        { rewrite FAT175; auto. apply FAT188c2; auto. }
        apply (@FAT171 y (e + xmin) (x + e)); auto. rewrite FAT175; auto. }
    New H14. apply H8 in H15. 
    assert(| y - e | < xmin ).
    { New H9. appA2H H16. destruct H17, H18, H19, H20. 
      pose proof @FAT167 y e H7 e_in_RC. destruct H22.
      + assert(y - e = 0); auto. rewrite H23. rewrite Zabs; auto.
      + destruct H22.
        * assert(| y - e | = y - e). { apply Ab4; auto. }
          rewrite H23. apply (FAT188c1 (y - e) xmin e); auto. 
          rewrite MincEx1; auto.
        * assert(| e - y | = e - y). { apply Ab4; auto. }
          assert(| e - y | = | y - e |). { apply AbE; auto. }
          rewrite <- H24. rewrite H23. apply (FAT188c1 (e - y) xmin y); auto. 
          rewrite MincEx1; auto. apply (FAT188c1 e (xmin + y) (-xmin)); auto. 
          rewrite MincEx2; auto. }
    apply (@legRf xmin (| y - e |)) in H15; auto.
Qed.
 
Definition StrictMonoInc_Fun f := Function f /\ (∀ x1 x2, x1 ∈ dom(f) 
  -> x2 ∈ dom(f) -> NtoR x1 < NtoR x2 -> NtoR f[x1] < NtoR f[x2]).
  
Definition SubSeq x y := IsSeq x /\ IsSeq y
  /\ (∃ f, StrictMonoInc_Fun f /\ dom(f) = Nat /\ ran(f) ⊂ Nat
    /\ (∀ n, n ∈ Nat -> y[n] = x[f[n]])).

Definition Conv_Seq x := ∃ a, Limit x a.