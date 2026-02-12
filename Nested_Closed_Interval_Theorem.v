(**********************************************************************)
(*     This is part of Real_Completeness, it is distributed under     *)
(*    the terms of the GNU Lesser General Public License version 3    *)
(*             (see file LICENSE for more details)                    *)
(*                                                                    *)
(*                     Copyright 2026-2031                            *)
(*              Ce Zhang, Guowei Dou and ωensheng Yu                  *)
(**********************************************************************)

Require Export Archimedean_Theorems1.

Definition ILT_Seq a b := IsSeq a /\ IsSeq b /\ (∀ n, n ∈ Nat -> a[n] < b[n]).

(* 定义：lim(n -> ∞)  (b[n] - a[n]) = 0 *)
Definition Limit_E a b := IsSeq a /\ IsSeq b /\ (∀ ε, ε ∈ RC -> 0 < ε -> 
(∃ N, N ∈ Nat /\ (∀ n, n ∈ Nat -> NtoR N < NtoR n -> AbsR[a[n] - b[n]] < ε))).

(* 定义：闭区间套 *)
Definition NestedIntervals a b := Increase a /\ 
  Decrease b /\ ILT_Seq a b /\ Limit_E a b.

(* 4.2 证明 闭区间套定理 存在性 *)

Corollary Increase_limitP : ∀ a ξ, 
  Increase a -> Limit a ξ -> (∀ n, n ∈ Nat -> a[n] ≤ ξ).
Proof.
  intros. red in H, H0. red. destruct H. destruct H0, H3. 
  New H1. apply (anRC a n) in H5; auto.   
  destruct (@FAT167 (a[n]) ξ) as [H6 | [H6 | H6]]; auto.
  assert (a[n] - ξ > 0). 
  { apply (FAT188a1 (a [n] - ξ) 0 ξ); auto. 
    New H3; apply AddRpa in H7. rewrite H7. rewrite MincEx1; auto. }
  apply H4 in H7; auto. destruct H7 as [N []]. 
  destruct (@FAT10 n N) as [ | [ | ]]; auto. 
  - generalize (@FAT18 N One). intros; subst n.
    apply H10 in H7; auto. apply FAT11 in H7; auto. clear H10.
    apply NtoR3 in H7; auto. New H7. apply H2 in H7; apply H8 in H9; auto.
    New H1. rename H10 into HN1. apply SucinNat in HN1. 
    rewrite <- FAT4a in HN1; auto. apply (anRC a (N + One)%Nat) in HN1; auto.
    assert (a[(N + One)%Nat] > ξ).
    { apply (FAT172 ξ (a [N]) (a [(N + One)%Nat])); auto. }
    rewrite Ab4 in H9; auto.
    assert(a [(N + One)%Nat] < a [N] ).
    { apply (FAT188c1 (a[(N + One)%Nat]) (a[N]) (- ξ)); auto. }
    apply legRf in H7; auto. contradiction.
  - generalize (@FAT18 n One). intros. New H1. 
    apply H10 in H11; auto. apply FAT11 in H11; auto. clear H10.
    apply NtoR3 in H11; auto. apply NtoR3 in H9; auto.
    assert( NtoR N < NtoR (n + One)%Nat ).
    { apply (@FAT171 (NtoR N) (NtoR n) (NtoR (n + One)%Nat)); auto. }
    apply H8 in H10; apply H2 in H11; auto.
    assert(a [(n + One)%Nat] ∈ RC). { apply anRC; auto. }
    assert (ξ < a [(n + One)%Nat]).
    { apply (FAT172 ξ (a [n]) (a [(n + One)%Nat])); auto. }
    rewrite Ab4 in H10; auto.
    assert(a [(n + One)%Nat] < a [n] ).
    { apply (FAT188c1 (a[(n + One)%Nat]) (a[n]) (- ξ)); auto. }
    apply legRf in H14; auto. contradiction.
  - generalize (@FAT18 N One); intros. New H7. 
    apply H10 in H11; auto. apply FAT11 in H11; auto. clear H10.
    apply NtoR3 in H11; auto. apply NtoR3 in H9; auto.
    assert(a [(N + One)%Nat] ∈ RC). { apply anRC; auto. }
    assert((NtoR n) < (NtoR (N + One)%Nat) ).
    { apply (@FAT171 (NtoR n) (NtoR N) (NtoR (N + One)%Nat)); auto. }
    apply H2 in H12; auto.
    assert (a [(N + One)%Nat] > ξ). 
    { apply (FAT172 (ξ) (a [n]) (a [(N + One)%Nat])); auto. }
    New H11. apply H8 in H11; auto. rewrite Ab4 in H11; auto.
    assert(a [(N + One)%Nat] < a [n] ).
    { apply (FAT188c1 (a[(N + One)%Nat]) (a[n]) (- ξ)); auto. }
    apply legRf in H15; auto. contradiction.
Qed.

Corollary Decrease_limitP : ∀ a ξ, 
  Decrease a -> Limit a ξ -> (∀ n, n ∈ Nat -> ξ ≤ a[n]).
Proof.
  intros. red in H, H0. red. destruct H. destruct H0, H3. 
  New H1. apply (anRC a n) in H5; auto.   
  destruct (@FAT167 (a[n]) ξ) as [H6 | [H6 | H6]]; auto.
  assert (ξ - a[n] > 0). {  
    apply (FAT188a1 (ξ - a[n]) 0 (a[n])); auto. 
    New H5; apply AddRpa in H7. rewrite H7. rewrite MincEx1; auto. }
  apply H4 in H7; auto. destruct H7 as [N []]. 
  destruct (@FAT10 n N) as [ | [ | ]]; auto. 
  - generalize (@FAT18 N One). intros; subst n.
    apply H10 in H7; auto. apply FAT11 in H7; auto. clear H10.
    apply NtoR3 in H7; auto. New H7. apply H2 in H7; apply H8 in H9; auto.
    New H1. rename H10 into HN1. apply SucinNat in HN1. 
    rewrite <- FAT4a in HN1; auto. apply (anRC a (N + One)%Nat) in HN1; auto.
    assert (a[(N + One)%Nat] < ξ).
    { apply (FAT172 (a [(N + One)%Nat]) (a [N]) ξ); auto. }
      rewrite Ab6' in H9; auto.
      assert(a [N] < a [(N + One)%Nat] ).
    { apply (FAT183c1 (ξ - (a [(N + One)%Nat])) (ξ - a [N])) in H9; auto.
      rewrite (FAT181 ξ  a[(N + One)%Nat]) in H9; auto. 
      rewrite (FAT181 ξ  a[N]) in H9; auto.
      apply (FAT188c1 (a[N]) (a[(N + One)%Nat]) (- ξ)); auto. }
    apply legRf in H7; auto. contradiction.
  - generalize (@FAT18 n One). intros. New H1. 
    apply H10 in H11; auto. apply FAT11 in H11; auto. clear H10.
    apply NtoR3 in H11; auto. apply NtoR3 in H9; auto.
    assert( NtoR N < NtoR (n + One)%Nat ).
    { apply (@FAT171 (NtoR N) (NtoR n) (NtoR (n + One)%Nat)); auto. }
    apply H8 in H10; apply H2 in H11; auto.
    assert(a [(n + One)%Nat] ∈ RC). { apply anRC; auto. }
    assert (a [(n + One)%Nat] < ξ).
    { apply (FAT172 (a [(n + One)%Nat]) (a [n]) ξ); auto. }
    rewrite Ab6' in H10; auto.
    assert(a [n] < a [(n + One)%Nat] ).
    { apply (FAT183c1 (ξ - (a [(n + One)%Nat])) (ξ - a [n])) in H10; auto.
      rewrite (FAT181 ξ  a[(n + One)%Nat]) in H10; auto. 
      rewrite (FAT181 ξ  a[n]) in H10; auto.
      apply (FAT188c1 (a[n]) (a[(n + One)%Nat]) (- ξ)); auto. }
    apply legRf in H14; auto. contradiction.
  - generalize (@FAT18 N One); intros. New H7. 
    apply H10 in H11; auto. apply FAT11 in H11; auto. clear H10.
    apply NtoR3 in H11; auto. apply NtoR3 in H9; auto.
    assert(a [(N + One)%Nat] ∈ RC). { apply anRC; auto. }
    assert((NtoR n) < (NtoR (N + One)%Nat) ).
    { apply (@FAT171 (NtoR n) (NtoR N) (NtoR (N + One)%Nat)); auto. }
      apply H2 in H12; auto.
      assert (a [(N + One)%Nat] < ξ). 
    { apply (FAT172 (a [(N + One)%Nat]) (a [n]) (ξ)); auto. }
    New H11. apply H8 in H11; auto. rewrite Ab6' in H11; auto.
    assert(a [n] < a [(N + One)%Nat] ).
    { apply (FAT183c1 (ξ - (a [(N + One)%Nat])) (ξ - a [n])) in H11; auto.
      rewrite (FAT181 ξ  a[(N + One)%Nat]) in H11; auto. 
      rewrite (FAT181 ξ  a[n]) in H11; auto.
      apply (FAT188c1 (a[n]) (a[(N + One)%Nat]) (- ξ)); auto. }
    apply legRf in H15; auto. contradiction.
Qed.

Corollary Limit_Equal : ∀ a b n, n ∈ RC -> IsSeq b -> Limit a n -> Limit_E a b 
  -> Limit b n.
Proof.
  intros. red in H1. red in H2. destruct H1, H3. destruct H2, H5.
  red. split; auto. split; auto. intros. assert(ε / (1 + 1) ∈ RC); auto.
  New H8. apply FAT169a' in H10; auto. apply half1 in H10; auto. apply FAT169a 
  in H10; auto. rename H10 into Hεdiv2. New H9. apply H4 in H9; auto.
  apply H6 in H10; auto. destruct H9, H9. destruct H10, H10.
  New H9. apply (@AddNp x x0) in H13; auto. exists((x + x0)%Nat). split; auto.
  intros. generalize (@FAT18 x x0); intros. generalize (@FAT18 x0 x); intros.
  New H10. apply (FAT6 x0 x) in H18; auto. rewrite H18 in H17. clear H18.
  New H10. New H10. apply H16 in H18; auto. apply H17 in H19; auto.
  apply NtoR3 in H18; auto. apply NtoR3 in H19; auto.
  apply (@FAT171 (NtoR x) (NtoR (x + x0)%Nat) (NtoR n0)) in H18; auto.
  apply (@FAT171 (NtoR x0) (NtoR (x + x0)%Nat) (NtoR n0)) in H19; auto.
  apply H11 in H18; auto. apply H12 in H19; auto. 
  New H14. New H14. apply (anRC a) in H20; auto. apply (anRC b) in H21; auto.
  assert((b [n0] - a [n0]) ∈ RC); auto.  rewrite AbE in H19; auto.
  apply Ab1 in H18; auto. apply Ab1 in H19; auto. destruct H18, H19.
  apply (@FAT189 (a [n0] - n) (- (ε / (1 + 1))) (b [n0] - a [n0]) 
  (- (ε / (1 + 1)))) in H18; auto. apply (@FAT189 (ε / (1 + 1)) (a [n0] - n) 
  (ε / (1 + 1)) (b [n0] - a [n0])) in H23; auto.
  (*化简 H18 H23 即可 *)
  New H7. apply (halfsum ε) in H25; auto.
  assert((ε / (1 + 1)) ∈ RC); auto.
  apply (FAT180 (ε / (1 + 1)) (ε / (1 + 1))) in H26; auto. rewrite H25 in H26.
  rewrite H25 in H23. rewrite <- H26 in H18. 
  assert((a [n0] - n ) ∈ RC); auto.
  assert(a [n0] - n + (b [n0] - a [n0]) = b[n0] - n).
  { apply (@FAT175 (a [n0] - n ) (b [n0] - a [n0])) in H27; auto. }
  rewrite H28 in H18, H23.
  apply Ab1; auto.
Qed.
  
Theorem NITex : ∀ a b, NestedIntervals a b -> 
  ∃ ξ, (∀ n, n ∈ Nat -> a[n] ≤ ξ /\ ξ ≤ b[n]) /\ Limit a ξ /\ Limit b ξ.
Proof.
  intros. red in H. destruct H, H0, H1.
  assert (Boundup_Seq (b[One]) a).
  { red; intros. red in H, H0, H1. destruct H, H0, H1, H5. generalize(FAA1); 
    intros. apply (anRC b) in H7; auto. split; auto. split; auto.
    intros. destruct (@FAT24 n); auto.
    - apply NtoR3 in H9; auto. pose proof H9. apply H3 in H9; auto. New H8.
      apply H6 in H8. apply H4 in H10; auto.
      New H11. New H11.
      apply (anRC a n) in H12; auto. apply (anRC b n) in H13; auto.
      apply (T173 a [n] b [n] b [One]); auto. red; left; auto.
    - rewrite H9; auto. red; left; auto. }
  destruct (MCTup _ _ H H3) as [ξ H4]. destruct H4.
  assert (Limit b ξ).
  { apply (Limit_Equal a b ξ); auto. red in H0. destruct H0; auto. }
  exists ξ. split; auto.
  intros. split.
  - apply Increase_limitP; auto. 
  - apply Decrease_limitP; auto.
Qed.

Corollary Pr_2a : ∀ {z}, z ∈ RC -> z > 0 -> (z / (1 + 1)) > 0.
Proof.
  intros; auto.
Qed.

Corollary LimUni : ∀ a x y, IsSeq a -> x ∈ RC -> y ∈ RC -> 
  Limit a x -> Limit a y -> x = y.
Proof.
  intros; destruct (classic (x = y)); auto.
  apply Ab8' in H4; auto. assert(x - y ∈ RC); auto. apply adsRC in H5. 
  rename H5 into HabRC.
  apply Pr_2a in H4; auto; pose proof H4.
  apply H2 in H4; auto. destruct H4 as [N1 H6].
  apply H3 in H5; auto; destruct H5 as [N2 H7].
  destruct H6, H7.
  assert((N1 + N2)%Nat ∈ Nat). { apply (@AddNp N1 N2); auto. }
  rename H8 into HNat.
  assert(NtoR (N1 + N2)%Nat > (NtoR N1)). 
  { apply NtoR3; auto; apply FAT18; auto. }
  assert(NtoR (N1 + N2)%Nat > (NtoR N2)). 
  { apply NtoR3; auto. New H6. apply (FAT6 N1 N2) in H9; auto. 
    rewrite H9. apply FAT18; auto. }
  apply H5 in H8; auto. apply H7 in H9; auto.
  New HNat. apply (anRC a (N1 + N2)%Nat) in H10; auto.
  assert(|x - a [(N1 + N2)%Nat]| ∈ RC). { apply adsRC; auto. }
  assert(|a [(N1 + N2)%Nat] - x| ∈ RC). { apply adsRC; auto. }
  assert(|a [(N1 + N2)%Nat] - y| ∈ RC). { apply adsRC; auto. }
  New H8. apply (@FAT189 (| x - y | / (1 + 1)) (| a [(N1 + N2)%Nat] - x |) 
     (| x - y | / (1 + 1)) (| a [(N1 + N2)%Nat] - y |))in H14; auto.
  assert((| x - y | / (1 + 1) + | x - y | / (1 + 1)) = | x - y |).
  { apply (halfsum (| x - y |)); auto. }
  rewrite H15 in H14. clear H15.
  assert((x - a [(N1 + N2)%Nat]) ∈ RC); auto.
  apply(Ab2 (x - a [(N1 + N2)%Nat]) (a [(N1 + N2)%Nat] - y)) in H15; auto.
  assert((x - a [(N1 + N2)%Nat] + (a [(N1 + N2)%Nat] - y)) = (x - y)).
  { apply (MincEx4 x y (a [(N1 + N2)%Nat])); auto. }
  rewrite H16 in H15. rewrite(AbE  x (a [(N1 + N2)%Nat])) in H15; auto.
  assert(| a [(N1 + N2)%Nat] - x | + | a [(N1 + N2)%Nat] - y | ∈ RC). auto.
  apply (@legRf (| x - y |) (| a [(N1 + N2)%Nat] - x | 
  + | a [(N1 + N2)%Nat] - y |)) in H14; auto. contradiction.
Qed.
  
Theorem NITuni : ∀ a b, NestedIntervals a b -> ∀ ξ1 ξ2, ξ1 ∈ RC -> ξ2 ∈ RC ->
  (∀ n, n ∈ Nat ->  a[n] ≤ ξ1 /\ ξ1 ≤ b[n]) /\ Limit a ξ1 /\ Limit b ξ1 ->
  (∀ n, n ∈ Nat ->  a[n] ≤ ξ2 /\ ξ2 ≤ b[n]) /\ Limit a ξ2 /\ Limit b ξ2 
  -> ξ1 = ξ2.
Proof.
  intros. New H. red in H4. destruct H4. red in H4. destruct H4. 
  destruct H2 as [_ [H2 _]], H3 as [_ [H3 _]].
  apply (LimUni a ξ1 ξ2); auto.
Qed.

Corollary Cor_NIT': ∀ a b, NestedIntervals a b -> 
  (∃ ξ, ξ ∈ RC /\ (∀ n, n ∈ Nat -> a[n] ≤ ξ /\ ξ ≤ b[n]) /\ 
  (∀ ε,ε ∈ RC -> ε > 0 -> ∃ N, ∀ n, N ∈ Nat -> n ∈ Nat -> (NtoR n > NtoR N) 
  -> ((ξ - ε) < (a[n])) /\ ((b[n]) < (ξ + ε)))).
Proof.
  intros. apply NITex in H; destruct H as [ξ H], H, H0.
  assert(ξ ∈ RC). { red in H0. destruct H0, H2; auto. } 
  exists ξ; split; auto. split; intros; auto. 
  destruct H0, H5; New H4; apply H6 in H7; auto; destruct H7, H7.
  destruct H1, H9; New H4; apply H10 in H11; auto; destruct H11, H11.
  exists (x + x0)%Nat; intros.
  (* 显然 *)
  assert(NtoR n > NtoR x). 
  { apply NtoR3; apply NtoR3' in H15; auto. New H7.
    apply (@FAT18 x x0) in H16; auto. 
    apply (@FAT15 x (x + x0)%Nat n) in H16; auto. }
  assert(NtoR n > NtoR x0).
  { apply NtoR3; apply NtoR3' in H15; auto. New H7.
    apply (@FAT18 x0 x) in H17; auto. rewrite FAT6 in H17; auto.
    apply (@FAT15 x0 (x + x0)%Nat n) in H17; auto. }
  apply H8 in H16; auto. apply H12 in H17; auto.
  split.
  - New H14. apply (anRC a) in H18; auto. apply Ab1 in H16; auto; destruct H16.
    apply (FAT188c1 (ξ - ε) a[n] (- ξ)); auto. 
    New H2; apply (MincEx2 ξ (- ε)) in H20; auto. rewrite H20; auto.
  - New H14. apply (anRC b) in H18; auto. apply Ab1 in H17; auto; destruct H17.
    apply (FAT188c1 b[n] (ξ + ε) (- ξ)); auto. 
    New H2; apply (MincEx2 ξ (ε)) in H20; auto. rewrite H20; auto.
Qed.

Corollary Cor_NIT: ∀ a b, NestedIntervals a b -> 
  (∃ ξ, ξ ∈ RC /\ (∀ n, n ∈ Nat -> a[n] ≤ ξ /\ ξ ≤ b[n]) /\ 
  (∀ ε,ε ∈ RC -> ε > 0 -> ∃ N, N ∈ Nat /\ (∀ n, n ∈ Nat -> (NtoR n > NtoR N)
  -> ((ξ - ε) < (a[n])) /\ ((b[n]) < (ξ + ε))))).
Proof.
  intros. apply NITex in H; destruct H as [ξ H], H, H0.
  assert(ξ ∈ RC). { red in H0. destruct H0, H2; auto. } 
  exists ξ; split; auto. split; intros; auto. 
  destruct H0, H5; New H4; apply H6 in H7; auto; destruct H7, H7.
  destruct H1, H9; New H4; apply H10 in H11; auto; destruct H11, H11.
  exists (x + x0)%Nat; intros. New H11. split; auto. intros.
  assert(NtoR n > NtoR x). 
  { apply NtoR3; apply NtoR3' in H15; auto. New H7.
    apply (@FAT18 x x0) in H16; auto. 
    apply (@FAT15 x (x + x0)%Nat n) in H16; auto. }
  assert(NtoR n > NtoR x0).
  { apply NtoR3; apply NtoR3' in H15; auto. New H7.
    apply (@FAT18 x0 x) in H17; auto. rewrite FAT6 in H17; auto.
    apply (@FAT15 x0 (x + x0)%Nat n) in H17; auto. }
  apply H8 in H16; auto. apply H12 in H17; auto.
  split.
  - New H14. apply (anRC a) in H18; auto. apply Ab1 in H16; auto; destruct H16.
    apply (FAT188c1 (ξ - ε) a[n] (- ξ)); auto. 
    New H2; apply (MincEx2 ξ (- ε)) in H20; auto. rewrite H20; auto.
  - New H14. apply (anRC b) in H18; auto. apply Ab1 in H17; auto; destruct H17.
    apply (FAT188c1 b[n] (ξ + ε) (- ξ)); auto. 
    New H2; apply (MincEx2 ξ (ε)) in H20; auto. rewrite H20; auto.
Qed.