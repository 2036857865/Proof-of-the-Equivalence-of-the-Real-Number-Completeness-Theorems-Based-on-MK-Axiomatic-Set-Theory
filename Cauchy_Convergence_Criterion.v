(**********************************************************************)
(*     This is part of Real_Completeness, it is distributed under     *)
(*    the terms of the GNU Lesser General Public License version 3    *)
(*             (see file LICENSE for more details)                    *)
(*                                                                    *)
(*                     Copyright 2026-2031                            *)
(*              Ce Zhang, Guowei Dou and ωensheng Yu                  *)
(**********************************************************************)

Require Export Sequential_Compactness_Theorem.

Fact K_Leq_Fk  : ∀ f k, Function f -> dom(f) = Nat -> ran(f) ⊂ Nat
  -> k ∈ dom(f) -> StrictMonoInc_Fun f -> NtoR k ≤ NtoR f[k].
Proof.
  intros. set (F:= \{ λ n, n ∈ Nat /\ NtoR n ≤ NtoR f[n] \}).
  assert (F = Nat).
  { apply MathInd_Ma; unfold Included; intros.
    - apply AxiomII in H4; tauto.
    - apply AxiomII. repeat split; auto. 
      assert (f[One] ∈ Nat). 
      { apply H1, (@ Property_ran One), Property_Value; auto; 
        rewrite H0; auto. }
      pose proof one_is_min_in_N'. apply H5; auto.
    - apply AxiomII in H4 as [H4 []].
      assert (x ∈ dom(f) /\ (x + One)%Nat ∈ dom(f)) as [].
      { split; [rewrite H0; auto|rewrite H0; auto]. }
      assert (f[x] ∈Nat /\ f[(x + One)%Nat] ∈Nat) as [].
      { split; [apply H1, (@ Property_ran x), Property_Value; auto
        |apply H1, (@ Property_ran (x + One)%Nat), Property_Value; auto]. }
      apply AxiomII; repeat split; eauto.
      assert (NtoR f[x] < NtoR f[(x + One)%Nat]).
      { apply H3; auto. apply Nat_P4a; auto.
        red; right; auto. }
      apply Nat_P4b; auto. apply (FAT172 _ (NtoR f[x]) _); auto. }
  rewrite H0, <-H4 in H2. apply AxiomII in H2; tauto.
Qed.

Definition lim x := ∩(\{ λ a, a ∈ RC /\ Limit x a \}).

Corollary Lim_getValue : ∀ x a, IsSeq x -> a ∈ RC -> Limit x a -> lim x = a.
Proof.
  intros. apply AxiomI; split; intros.
  - apply AxiomII in H2 as []. apply H3. apply AxiomII; split; eauto.
  - apply AxiomII; split; eauto. intros. apply AxiomII in H3 as [H3 []].
    assert (a = y). { apply Limitun with x; auto. }
    rewrite <-H6; auto.
Qed.

Theorem Theorem2_5 : ∀ x y, IsSeq x -> IsSeq y -> Conv_Seq x -> Conv_Seq y 
  -> (∃ N0, N0 ∈ Nat /\ (∀ n, n ∈ Nat -> NtoR N0 < NtoR n -> x[n] ≤ y[n])) 
  -> lim x ≤ lim y.
Proof.
  intros. destruct H1 as [a [_ [Ha]]], H2 as [b [_ [Hb]]].
  pose proof H as IsSeq_x. pose proof H0 as IsSeq_y.
  destruct H as [H []], H0 as [H0 []]. 
  assert (∀ε, ε ∈ RC /\ 0 < ε -> a < b + (ε + ε)).
  { intros. pose proof H8 as []. New H10. destruct H3 as [N0 [Hc Hd]].
    apply H1 in H11 as He; auto. destruct He as [N1 [He Hf]].
    apply H2 in H11 as Hg; auto. destruct Hg as [N2 [Hg Hh]].
    destruct (Max_nat_3 N0 N1 N2) as [N [Hi [Hj [Hk Hl]]]]; auto.
    assert (x[N] ∈ RC).
    { apply H5, (@ Property_ran N), Property_Value; auto. rewrite H4; auto. }
    assert (y[N] ∈ RC).
    { apply H7, (@ Property_ran N), Property_Value; auto; rewrite H6; auto. }
    apply Hd in Hj; apply Hf in Hk; apply Hh in Hl; auto.
    New Hk. rename Hk into H14. New Hl. rename Hl into H16. 
    apply Ab1 in H13 as [], H15 as []; auto.
    apply (FAT188c2 _ _ a) in H13; auto.
    rewrite MincEx1, FAT175 in H13; auto.
    apply (FAT188c2 _ _ b) in H18; auto.
    rewrite MincEx1, FAT175 in H18; auto.
    assert (a - ε < b + ε).
    { New H3. apply (@FAT172 (a - ε) (x [N]) (y [N])) in H19; auto.
      apply (@FAT171 _ (y [N]) _); auto. }
    apply (FAT188c2 _ _ ε) in H19; auto.
    rewrite MincEx1, FAT186 in H19; auto. }
  pose proof H1; pose proof H2. rename H1 into H11. rename H2 into H12.
  rename IsSeq_x into H1. rename IsSeq_y into H2. clear H9 H10.
  assert(Limit x a). { red. split; auto. }
  assert(Limit y b). { red. split; auto. }
  apply Lim_getValue in H9; auto; apply Lim_getValue in H10; auto.
  rewrite H9; rewrite H10. apply NNPP; intro. apply NotleR in H13; auto.
  New H13. apply (FAT188c2 _ _ a) in H13 as H15; auto.
  assert (b + a ≤ a + a). { red; left; auto. }
  assert (0 < (1 + 1)) as Hm.
  { apply FAT169a; auto. }
  assert (0 < (1/(1 + 1))) as Hn. { pose proof add0. apply Pdiv2; auto. }
  assert ((1 + 1) ∈ (RC ~ [0])) as Ho.
  { apply MKT4'; split; auto. apply AxiomII; split; eauto.
    intro. apply MKT41 in H17; eauto. }
  assert ((1/(1 + 1)) ∈ (RC ~ [0])) as Hp. 
  { apply MKT4'; split; auto. apply AxiomII; split; eauto.
    intro. apply MKT41 in H17; eauto. apply (@egRf (1 / (1 + 1)) 0); auto. }
  assert (a · (1 + 1) = a + a).
  { rewrite FAT194; auto. } 
  assert (b = b · (1 + 1) - b).
  { rewrite FAT194, dou3, MincEx2; auto. }
  assert (0 < (a - b)) as Hq.
  { apply FAT182a2; auto. }
  pose proof Hp. apply MKT4' in H19 as [H19 H20]. pose proof Hn. New H21.
  assert (((a - b)/ (1 + 1))/ (1 + 1) ∈ RC 
    /\ 0 < ((a - b)/ (1 + 1)) / ((1 + 1))).
  { split; auto. apply Pdiv2; auto. }
  apply H8 in H23. rewrite halfsum, aver_Cor6 in H23; auto.
  apply aver_Cor4' in H23; auto. apply (@lgRf a b); auto.
Qed. 

Theorem Theorem2_11 : ∀ x, IsSeq x -> Conv_Seq x 
  <-> (∀ ε, ε ∈ RC /\ 0 < ε -> (∃ N, N ∈ Nat /\ ∀ n m, n ∈ Nat -> m ∈ Nat
    -> NtoR N < NtoR n -> NtoR N < NtoR m -> |(x[n] - x[m])| < ε)).
Proof.
  assert ((1 + 1) ∈ RC) as Ha; auto.
  assert (0 < 1 + 1) as Hb.
  { apply FAT169a; auto. } 
  assert (0 < 1 / (1 + 1)) as Hc. { apply Pdiv2; auto. }
  assert ((1 + 1) ∈ (RC ~ [0])) as Hd.
  { apply setminP; auto. intro. appA2H H. assert(0 ∈ μ); auto. }
  assert(1 / (1 + 1) ∈ RC) as Hf; auto.
  split; intros.
  - destruct H0 as [A [Hg [A_in_RC]]]. 
    pose proof H1 as Hh. destruct H1 as [Hi Hj].
    assert (ε / (1 + 1) ∈ RC); auto.
    assert (0 < ε / (1 + 1)) as H1'. { apply Pdiv2; auto. }
    apply H0 in H1 as H2; auto. destruct H2 as [N1 []].
    apply H0 in H1 as H4; auto. destruct H4 as [N2 []].
    destruct (Max_nat_2 _ _ H2 H4) as [N [H6 []]].
    exists N; split; auto; intros.
    assert (NtoR N1 < NtoR n).
    { apply (@FAT171 (NtoR N1) (NtoR N) (NtoR n)); auto. }
    assert (NtoR N2 < NtoR m).
    { apply (@FAT171 (NtoR N2) (NtoR N) (NtoR m)); auto. }
    apply H3 in H13; auto; apply H5 in H14; auto.
    assert (x[n] ∈ RC /\ x[m] ∈ RC) as [Hk Hl].
    { split; apply anRC; auto. }
    assert (|(A - x[m])| = |(x[m] - A)|). { apply AbE; auto. }
    apply (FAT172 _ (|(x[n] - A)|+ |(x [m] - A)|) _); auto.
    left; split. apply (Abs8 (x [n]) (x [m]) A); auto.
    assert (ε + ε = ε · (1 + 1)).
    { rewrite FAT194, dou3; auto. }
    assert (ε = ((ε + ε) / (1 + 1))).
    { rewrite H16, <- divRp2, divRp7 ; auto. }
    assert (ε = ε / (1 + 1) + ε / (1 + 1)). 
    { symmetry. apply halfsum ; auto. }
    rewrite H18. apply FAT189; auto.
  - assert (BoundedSeq x).
    { unfold BoundedSeq. split; auto.
      assert (1 ∈ RC /\ 0 < 1). { split; auto. }
      apply H0 in H1 as [N0 []]. assert (NtoR N0 < NtoR (N0 + One)%Nat).
      { apply NtoR3; auto. apply FAT18; auto. }
      assert (∀ n, n ∈ Nat -> NtoR N0 < NtoR n 
        -> |(x[n] - x[(N0 + One)%Nat])| < 1). { intros. apply H2; auto. }
      assert (x[(N0 + One)%Nat] ∈ RC) as Hz. { apply anRC; auto. }
      assert (∀ n, n ∈ Nat -> NtoR N0 < NtoR n 
        -> |(x[n])| ≤ |(x[(N0 + One)%Nat])| + 1).
      { intros. apply H4 in H6 as H7; auto.
        assert (x[n] ∈ RC).
        { apply anRC; auto. }
        assert (|(x[n])| = |(x[(N0 + One)%Nat] + (x[n] - x[(N0 + One)%Nat]))|).
        { rewrite <- FAT186, MincEx2; auto. }
        red; left. apply (FAT172 _ (| x [(N0 + One)%Nat]| + |x [n] - 
        x [(N0 + One)%Nat]|) _); auto. left; split.
        --- rewrite H9. apply Abs5; auto.
        --- apply FAT190'; auto. red; right; auto. }
        set (F:= \{ λ N0, N0 ∈ Nat /\ (∃ M1, M1 ∈ RC /\ ∀ n, n ∈ Nat 
          -> NtoR n ≤ NtoR N0 -> |(x[n])| ≤ M1) \}).
        assert (F = Nat).
        { apply MathInd_Ma; unfold Included; intros.
          --- apply AxiomII in H6; tauto.
          --- apply AxiomII; repeat split. eauto. auto.
              assert (x[One] ∈ RC). { apply anRC; auto. }
              exists (|(x[One])|); split; auto. intros.
              assert (n = One).
              { apply one_is_min_in_N; auto. }
              rewrite H9. red; right; auto.
          --- apply AxiomII in H6 as [_[H6 [M0 []]]].
              apply AxiomII; repeat split. eauto. auto.
              assert (x[(x0 + One)%Nat] ∈ RC). { apply anRC; auto. }
              destruct (@FAT167 M0 (|x[(x0+One)%Nat]|) ) as [H10 |[H10 | H10]]; 
              auto.
           +++ exists M0; split; auto. intros.
               destruct (classic (n = (x0 + One)%Nat)).
               *** rewrite H10, H13. red; right; auto.
               *** assert (NtoR n < NtoR (x0 + One)%Nat). 
                   { destruct H12; auto. elim H13. apply NtoR1'; auto. }
                   assert (NtoR n ≤ NtoR x0).
                   { apply Nat_P4 in H14; auto. }
                   apply H8; auto.
            +++ exists M0; split; auto. intros.
                destruct (classic (n = (x0 + One)%Nat)).
                *** rewrite H13. red; left; auto. 
                *** assert (NtoR n < NtoR (x0 + One)%Nat).
                    { destruct H12; auto. elim H13. apply NtoR1'; auto. }
                    assert (NtoR n ≤ NtoR x0).
                   { apply Nat_P4 in H14; auto. }
                    apply H8; auto.
            +++ exists (|x[(x0 + One)%Nat]|); split; auto. intros.
                destruct (classic (n = (x0 + One)%Nat)).
                *** rewrite H13. red; right; auto. 
                *** assert (NtoR n < NtoR (x0 + One)%Nat).
                    { destruct H12; auto. elim H13. apply NtoR1'; auto. }
                    assert (NtoR n ≤ NtoR x0).
                   { apply Nat_P4 in H14; auto. }
                    assert (x[n] ∈ RC).
                    { apply anRC; auto. }
                    red; left.
                    apply (FAT172 (| x [n] |) M0 _); auto. }
      pose proof H1 as Hy; rewrite <-H6 in Hy.
      apply AxiomII in Hy as [_[_[M []]]].
      destruct (@FAT167 M (|x[(N0 + One)%Nat]| + 1)) as [H9 | [H9 | H9]];
      auto.
      -- exists (|x[(N0 + One)%Nat]| + 1); split; auto. intros.
         assert (x[n] ∈ RC). { apply anRC; auto. }
         destruct (@FAT167 (NtoR n) (NtoR N0)) as [H12 | [H12 | H12]]; auto.
         ++ destruct H12. apply H8 in H10 as H14; auto. rewrite H9 in H14; auto.
            red; right; auto.
         ++ apply H8 in H10 as H13. rewrite H9 in H13; auto.
            red; left; auto.
      -- exists M; split; auto. intros.
         assert (x[n] ∈ RC). { apply anRC; auto. } 
         destruct (@FAT167 (NtoR n) (NtoR N0)) as [H12 | [H12 | H12]]; auto.
         ++ destruct H12. apply H8 in H10 as H14; auto. red; right; auto.
         ++ apply H5 in H10 as H13; auto. red; left.
            apply (FAT172 _ (|x[(N0 + One)%Nat]| + 1) _); auto.
         ++ apply H8; auto. red; left; auto. 
      -- exists (|x[(N0 + One)%Nat]| + 1); split; auto. intros.
         destruct (@FAT167 (NtoR n) (NtoR N0)) as [H12 | [H12 | H12]]; auto.
         ++ apply H8 in H10 as H13. red; left. apply (FAT172 _ M _); auto. 
            red; right; auto.
         ++ apply H8 in H10 as H13. red; left. apply (FAT172 _ M _); auto. 
            red; left; auto. }
    apply Theorem2_10 in H1 as [y [Hz Hy]]. destruct Hy as [ξ [Hx Hy]].
    pose proof Hy as H1. destruct H1. 
    destruct Hz as [Hz [_[f [Hu [Ht [Hs]]]]]]. exists ξ; split; auto.
    split; auto; intros. rename Hx into H'. rename Hy into Hx.
    rename H1 into Hy. rename H' into H1. pose proof Hx as Hw. 
    destruct Hw as [_ Hw].
    assert (ε / (1 + 1) ∈ RC /\ 0 < ε / (1 + 1)).
    { split; auto. apply Pdiv2; auto. }
    apply H0 in H6 as [N []]. exists N; split; auto; intros.
    assert (∀ k, k ∈ Nat -> NtoR N < NtoR k -> |(x[n] - y[k])| < ε / (1 + 1)).
    { intros. assert (∃ nk, nk ∈ Nat /\ NtoR N < NtoR nk /\ y[k] = x[nk]).
      { pose proof H10. rewrite <- Ht in H12.
        pose proof Hu. destruct H13 as [H13 _]. apply K_Leq_Fk  in H12; auto.
        assert (f[k] ∈ Nat).
        { apply Hs, (@ Property_ran k), Property_Value; auto;
          rewrite Ht; auto. }
        assert (NtoR N < NtoR f[k]). { apply (FAT172 _ (NtoR k) _); auto. }
        apply H3 in H10 as H16. exists f[k]; split; auto. }
        destruct H12 as [nk [H12 []]]. rewrite H14; auto. }
    set (z:= \{\ λ k v, k ∈ Nat /\ v ∈ RC /\ v = |(x[n] - y[k])| \}\).
    assert (x[n] ∈ RC) as Hv.
    { destruct Hz as [Hz []]. apply H12, (@ Property_ran n), Property_Value;
      auto; rewrite H11; auto. }
    assert (Function z).
    { split; intros.
      -- unfold Relation; intros. apply AxiomII in H11 as [_[x0 [y0]]].
         exists x0, y0; tauto.
      -- apply AxiomII' in H11 as [H11 [H13 [H14]]].
         apply AxiomII' in H12 as [H12 [H16 [H17]]].
         apply MKT49b in H11 as [], H12 as []. rewrite H15, H18; auto. }
    assert (IsSeq z).
    { split; auto; split.
      -- apply AxiomI; split; intros.
         ++ apply AxiomII in H12 as [_[y0]]. apply AxiomII' in H12; tauto.
         ++ assert (y[z0] ∈ RC).
            { destruct H1 as [H1 []]. apply H14, (@ Property_ran z0),
              Property_Value; auto; rewrite H13; auto. }
            assert (|(x[n] - y[z0])| ∈ RC); auto. 
            apply AxiomII; split; eauto. exists (|x[n] - y[z0]|).
            apply AxiomII'; repeat split; auto. apply MKT49a; eauto.
      -- unfold Included; intros. apply AxiomII in H12 as [_[k]].
         apply AxiomII' in H12; tauto. }
    assert (Limit z (|x[n] - ξ|)).
    { split; auto. split; auto. intros. destruct Hx as [_ Hx]. 
      rename H14 into H13'. apply Hx in H13 as H14; auto.
      destruct H14 as [N0 []]. rename H13' into H16. exists N0; split; auto.
      intros. apply H15 in H18 as H19; auto.
      assert (y[n0] ∈ RC).
      { destruct H1 as [H1 []]. apply H21, (@ Property_ran n0), 
        Property_Value; auto; rewrite H20; auto. }
      assert (|(x[n] - y[n0])| ∈ RC). { auto. }
      assert (|(x[n] - ξ)| ∈ RC). { auto. }
      assert (|(x[n] - y[n0])| = z[n0]).
      { apply Property_Fun; auto. apply AxiomII'; repeat split;
        auto. apply MKT49a; eauto. }
      rewrite <-H23. apply (FAT172 _ (|(y[n0] - ξ)|) _); auto.
      left; split; auto.
      assert (y[n0] - ξ = -((x[n] - y[n0]) - (x[n] - ξ))).
      { repeat rewrite Minus_P3, Minus_P4; auto. symmetry.
        rewrite FAT181; auto. rewrite (FAT181 (x [n]) (y [n0])); auto. }
      assert (|(x[n] - y[n0] - (x[n] - ξ))| = |(-(x[n] - y[n0] - (x[n] - ξ)))|). 
      { rewrite Abs2; auto. }
      rewrite H24, <-H25. apply Abs5; auto. }
    set (c := \{\ λ n v, n ∈ Nat /\ v ∈ RC /\ v = ε / (1 + 1) \}\).
    assert (Function c).
    { split; intros.
      -- unfold Relation; intros. apply AxiomII in H14 as [_[x0 [y0]]].
         exists x0, y0; tauto.
      -- apply AxiomII' in H14 as [_[H14 []]], H15 as [_[_[]]].
         rewrite H17, H18; auto. }
    assert (IsSeq c).
    { split; auto; split.
      -- apply AxiomI; split; intros.
         ++ apply AxiomII in H15 as [_[y0]]. apply AxiomII' in H15; tauto.
         ++ apply AxiomII; split; eauto. exists (ε / (1 + 1)).
            apply AxiomII'; repeat split; auto.
            apply MKT49a; eauto.
      -- unfold Included; intros. apply AxiomII in H15 as [_[x0]].
         apply AxiomII' in H15; tauto. }
    assert (Limit c (ε / (1 + 1))).
    { split; auto. split; auto. intros. destruct H13 as [_[H13' H13]]. 
      rename H17 into H16'. apply H13 in H16 as H17; auto.
      destruct H17 as [N0 []]. rename H16' into H19. 
      exists N0; split; auto. intros.
      assert (ε / (1 + 1) = c[n0]).
      { apply Property_Fun; auto. apply AxiomII'; repeat split;
        auto. apply MKT49a; eauto. }
      assert (|0| = 0). { apply Zabs. }
      assert (|0| < ε0). { rewrite H23; auto. }
      rewrite <-H22, xminx; auto. }
    assert (Conv_Seq z /\ Conv_Seq c) as [].
    { red in H13. destruct H13, H17. red in H16. destruct H16, H19.
      split; [exists (|(x[n] - ξ)|); split; auto; split; auto|
      exists (ε / (1 + 1)); split; auto; split; auto]. }
    assert (ε / (1 + 1) < ε).
    { assert (1 < (1 + 1)).
      { assert (1 + 0 < 1 + 1); auto.
        { apply FAT190'; auto. red; right; auto. } }
      assert (0 < ε / (1 + 1)); auto. { apply Pdiv2; auto. } 
      apply (aver2 0 ε) in H5 as [_]; auto. rewrite AddRpa in H5; auto. }
    apply (FAT172 _ (ε / (1 + 1)) _); auto. left; split; auto.
    apply Lim_getValue in H13 as H20, H16 as H21; auto.
    rewrite <-H20, <-H21. apply Theorem2_5; auto.
    exists N; split; auto. intros. 
    assert (y[n0] ∈ RC).
    { destruct H1 as [H1 []]. apply H25, (@ Property_ran n0), Property_Value;
      auto; rewrite H24; auto. }
    assert (|(x[n] - y[n0])| ∈ RC); auto. 
    assert (|(x[n] - y[n0])| = z[n0]).
    { apply Property_Fun; auto. apply AxiomII'; repeat split; auto.
      apply MKT49a; eauto. }
    assert (ε / (1 + 1) = c[n0]).
    { apply Property_Fun; auto. apply AxiomII'; repeat split; auto.
      apply MKT49a; eauto. }
    rewrite <-H26, <-H27. red; left. apply H10; auto.
Qed.

