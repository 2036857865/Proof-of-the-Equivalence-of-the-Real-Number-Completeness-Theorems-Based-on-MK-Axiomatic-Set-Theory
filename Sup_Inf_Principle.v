(**********************************************************************)
(*     This is part of Real_Completeness, it is distributed under     *)
(*    the terms of the GNU Lesser General Public License version 3    *)
(*             (see file LICENSE for more details)                    *)
(*                                                                    *)
(*                     Copyright 2026-2031                            *)
(*              Ce Zhang, Guowei Dou and ωensheng Yu                  *)
(**********************************************************************)

Require Export FA_R1.

Open Scope RC_scope.

Fact rcisEnsemble : ∀ x, x ⊂ RC -> Ensemble x.
Proof.
  intros. apply MKT33 in H; auto. apply EnRC.
Qed.

Fact SNS : ∀ x S, x ∈ S -> x ∈ ¬S -> False.
Proof.
  intros. unfold Complement in H0. appA2H H0.
  unfold NotIn in H1; destruct H1; auto.
Qed.
  
Fact NotleR : ∀ r1 r2, r1 ∈ RC -> r2 ∈ RC -> ~ (r2 ≤ r1) -> r1 < r2.
Proof.
  intros. 
  assert(r1 = r2 \/ r1 > r2 \/ r1 < r2). { apply (FAT167 H H0). }
  destruct H2.
  + unfold leR in H1. destruct H1; auto.
  + destruct H2; auto. unfold leR in H1. destruct H1. auto.
Qed.

Fact Notle : ∀ r1 r2, r1 ∈ RC -> r2 ∈ RC -> ~ (r2 < r1) -> r1 ≤ r2.
Proof.
  intros. 
  assert(r1 = r2 \/ r1 > r2 \/ r1 < r2). { apply (FAT167 H H0). }
  destruct H2.
  + unfold leR. right; auto.
  + unfold leR. destruct H2; auto. elim H1. apply si2'; auto.
Qed.

Fact AUnionNotA : ∀ a , a ∪ ¬ a = μ.
Proof.
  intros. eqext.
  assert(Ensemble z). { unfold Ensemble. exists (a ∪ ¬ a); auto. }
  + apply MKT19b in H0; auto.
  + unfold Union. appA2G.
    TF(z ∈ a).
    - left; auto.
    - right. unfold Complement. appA2G.
Qed.

Fact minRdom : dom(minR) = RC.
Proof.
  apply AxiomI; split. 
  + intros. unfold minR in H. appA2H H. destruct H0. appA2H H0. destruct H1.
    destruct H1. destruct H1, H2. New H0. apply MKT49b in H4. destruct H4. 
    apply (MKT55 z x x0 x1) in H1; auto. destruct H1. subst; auto.
  + intros. unfold minR. appA2G. assert (Ensemble z); unfold Ensemble; eauto.
    New H. apply minRC in H1. assert (Ensemble (-z)); unfold Ensemble; eauto.
    exists(-z). appA2G. exists(z). exists(-z). repeat split; auto.
    - intros. apply Pmin in H3; auto.
    - intros. apply Nmin in H3; auto.
    - intros. rewrite H3. apply Zmin.
Qed.

Fact minRC' : ∀ X, (-X) ∈ RC -> X ∈ RC.
Proof.
  intros. 
  (* 怎么写比较快？ *)
  assert(dom(minR) = RC). { apply minRdom. }
  assert(Function minR). { apply mirf. }
  assert (Ensemble (-X)); unfold Ensemble; eauto.
  rewrite <- H0.
  apply NNPP. intro. apply MKT69a in H3. rewrite H3 in H. 
  assert (Ensemble μ); unfold Ensemble; eauto. 
  assert (~ Ensemble μ); apply MKT39.
  auto.
Qed.

Fact xInX : ∀ X x, X ⊂ RC -> x ∈ X -> x ∈ RC.
Proof.
  intros. unfold Included in H. apply H in H0. auto.
Qed.

Global Hint Resolve xInX : core.

Global Hint Resolve adsRC : core.

Fact mulRC1' : ∀ a b, a ∈ RC -> b ∈ RC -> a > 0 -> b > 0 -> a · b > 0.
Proof.
  intros. apply FAT169a. apply (mulRC1 a b). 
  apply FAT169a'; auto. apply FAT169a'; auto.
Qed.

Global Hint Resolve mulRC1': core. 

Fact mulEql : ∀ x y z, x ∈ RC -> y ∈ RC -> z ∈ RC -> x = y -> x · z = y · z.
Proof.
  intros. subst. auto.
Qed.

Global Hint Resolve mulEql: core. 

Fact FAT199' : ∀ X Y Z, X ∈ RC -> Y ∈ RC -> Z ∈ RC -> (X · Y) · Z = X · Y · Z.
Proof.
  intros. auto.
Qed.

Global Hint Resolve FAT199': core. 

Fact sie2 : ∀ X Y, Y ≤ X -> X ≥ Y.
Proof.
  auto.
Qed.

Fact sie2' : ∀ X Y, Y ≥ X -> X ≤ Y.
Proof.
  auto.
Qed.

Fact xlx : ∀ x, x ∈ RC -> x < x -> False.
Proof.
  intros. New H0. apply si2 in H1. apply lgRf in H0; auto.
Qed.

Fact xleRx : ∀ x, x ∈ RC -> x ≤ x.
Proof.
  intros. TF(x ≤ x); auto. apply NotleR in H0; auto. 
  apply xlx in H0; auto. contradiction.
Qed.

Fact xg0 : ∀ x, x ∈ RC -> x > 0 -> x ≠ 0.
Proof.
  intros. red. intros. rewrite <- H1 in H0. apply xlx in H0; auto.
Qed.

Global Hint Resolve xg0: core. 

Fact xl0 : ∀ x, x ∈ RC -> x < 0 -> x ≠ 0.
Proof.
  intros. red. intros. rewrite <- H1 in H0. apply xlx in H0; auto.
Qed.

Global Hint Resolve xl0: core. 

Fact minsie2 : ∀ x y, x ∈ RC -> y ∈ RC -> -x ≤ y -> - y ≤ x.
Proof.
  intros. assert(∃ z, z = -x). { exists (-x); auto. }
  destruct H2. rewrite <- H2 in H1. destruct H1.
  New H. apply minRC in H3. rewrite <- H2 in H3.
  + apply FAT183c1 in H1; auto. rewrite H2 in H1. rewrite FAT177 in H1; auto.
    red. left. apply si2'; auto.
  + red; right; rewrite H1 in H2. rewrite H2. apply FAT177; auto. 
Qed.

Global Hint Resolve minsie2: core. 

Fact minsie2' : ∀ x y, x ∈ RC -> y ∈ RC -> y ≤ -x -> x ≤ - y.
Proof.
  intros. assert(∃ z, z = -x). { exists (-x); auto. }
  destruct H2. rewrite <- H2 in H1. destruct H1.
  New H. apply minRC in H3. rewrite <- H2 in H3.
  + apply FAT183c1 in H1; auto. rewrite H2 in H1. rewrite FAT177 in H1; auto.
    red. left. apply si2'; auto.
  + red; right. rewrite <- H1 in H2. rewrite H2. rewrite FAT177; auto. 
Qed.

Global Hint Resolve minsie2': core. 

Fact MincEx1 : ∀ X Y, X ∈ RC -> Y ∈ RC -> Y - X + X = Y.
Proof.
  intros. rewrite @ FAT175 with (Y - X) (X); auto. apply MincEx; auto.
Qed.

Global Hint Resolve MincEx1: core. 

Fact xminx : ∀ X, X ∈ RC -> X - X = 0.
Proof.
  intros. apply (FAT188b1 (X - X) 0 X); auto. 
  rewrite MincEx1; auto. rewrite AddRpa; auto.
Qed.

Global Hint Resolve xminx: core. 

Fact MinRpb : ∀ x, x ∈ RC -> x - 0 = x.
Proof.
  intros. apply (FAT187b x 0 x); auto. apply AddRpa; auto.
Qed.

Global Hint Resolve MinRpb: core. 

Fact MinRpa : ∀ x, x ∈ RC -> 0 - x = - x.
Proof.
  intros. apply (FAT187b 0 x (-x)); auto.
Qed.

Global Hint Resolve MinRpa: core. 

Fact aminb : ∀ x y, x ∈ RC -> y ∈ RC -> x - y = x + (- y).
Proof.
  intros. auto.
Qed.

Global Hint Resolve aminb: core. 

Fact xminx' : ∀ X, X ∈ RC -> - X + X = 0.
Proof.
  intros. New H. apply MinRpa in H. rewrite <- H. apply(MincEx1 X 0); auto.
Qed.

Global Hint Resolve xminx': core. 

Fact RealCompare1: ∀ x, x ∈ RC -> x > 0 -> -x < 0.
Proof.
  intros. apply (FAT188a2 x 0 (-x)) in H0; auto. rewrite xminx in H0; auto.
  rewrite MinRpa in H0; auto.
Qed.

Global Hint Resolve RealCompare1 : core.

Fact MincEx2 : ∀ X Y, X ∈ RC -> Y ∈ RC -> X + Y - X = Y.
Proof.
  intros. apply (FAT187b (X + Y) X Y); auto.
Qed.

Global Hint Resolve MincEx2: core. 

Fact MincEx3 : ∀ y x, x ∈ RC -> y ∈ RC -> - x + (x - y) = - y.
Proof.
  intros. New H. apply minRC in H1. New H1. apply minRC' in H2. 
  New H1. apply (@FAT175 (-x) (x - y)) in H3; auto. rewrite H3. 
  apply (MincEx2 x (-y)); auto.
Qed.

Global Hint Resolve MincEx3: core. 

Fact MincEx4 : ∀ x y z, x ∈ RC -> y ∈ RC -> z ∈ RC -> x - z + (z - y) = x - y.
Proof.
  intros. assert((- z + (z - y)) ∈ RC); auto. assert((-y) ∈ RC); auto.
  New H0. apply (MincEx3 y z) in H4; auto. 
  assert(x - z + (z - y) = x + (- z + (z - y))). 
  { apply (FAT186 x (-z) (z - y)); auto. }
  rewrite H5, H4; auto.
Qed.

Global Hint Resolve MincEx4: core. 

Fact MincEx5 : ∀ x y z, x ∈ RC -> y ∈ RC -> z ∈ RC -> z - x + (y - z) = y - x.
Proof.
  intros. assert((y - z) ∈ RC); auto. assert((-z) ∈ RC); auto.
  New H. apply (@FAT175 (z-x)(y-z)) in H2; auto. rewrite H2. 
  apply (MincEx4 y x z); auto.
Qed.

Global Hint Resolve MincEx5: core. 

Theorem FAT177' : ∀ X, X ∈ RC -> - -X = X.
Proof.
  intros. apply funv; auto. apply AxiomII'.
  pose proof (minRC _ H). repeat split; intros; rxo; auto.
  - apply FAT169a in H1; auto. apply FAT176c2 in H1; auto.
    apply FAT169b' in H1; auto. rewrite Nmin; auto. GE.
  - apply FAT169b in H1; auto. apply FAT176a2 in H1; auto.
    apply FAT169a' in H1; auto. rewrite Pmin; auto. GE.
  - apply FAT176b2; auto.
Qed.

Global Hint Resolve FAT177': core. 

Fact MincEx6 : ∀ X Y, X ∈ RC -> Y ∈ RC -> - X + Y + X = Y.
Proof.
  intros. New H0. New H. apply minRC in H. apply (MincEx2 (-X) Y) in H1; auto.
  New H2. apply FAT177' in H3. rewrite H3 in H1. auto.
Qed.

Global Hint Resolve MincEx6: core. 

Theorem FAT186' : ∀ X Y Z, X ∈ RC -> Y ∈ RC -> Z ∈ RC
  -> X + Y + Z = X + (Y + Z).
Proof.
  intros. pose proof (FAT184 _ H).
  pose proof (FAT184 _ H0). pose proof (FAT184 _ H1).
  destruct H2 as [x1[x2[?[]]]]. destruct H3 as [y1[y2[?[]]]].
  destruct H4 as [z1[z2[?[]]]]. subst. rewrite FAT185'; auto.
  rewrite FAT185'; auto. rewrite (Lemma_FAT185a x1 y1 z1); auto.
  rewrite (Lemma_FAT185a x2 y2 z2); auto. rewrite <- FAT185'; auto.
  rewrite <- FAT185'; auto.
Qed.

Global Hint Resolve FAT186': core. 

Fact addminx : ∀ X Y, X ∈ RC -> Y ∈ RC -> X + - Y = X - Y.
Proof.
  intros; auto.
Qed.

Global Hint Resolve addminx: core. 

Fact not1_0 : 1 ≠ 0.
Proof.
  red. intro. assert (1 > 0); auto. apply xg0 in H0; auto.
Qed.

Global Hint Resolve not1_0 : core.

Fact not1_0' : 1 = 0 -> False.
Proof.
  intros. apply not1_0; auto.
Qed.

Fact halfsum : ∀ x , x ∈ RC -> x / (1 + 1) + x / (1 + 1) = x.
Proof.
  intros. assert(1 ∈ RC); auto. assert(1 + 1 ∈ RC); auto.
  assert(x = (x / (1 + 1)) · (1 + 1)). 
  { apply (divRp7 x (1 + 1)) in H1; auto. }
  New H0. apply(FAT201a (x / (1 + 1)) 1 1) in H3; auto.
  assert((x / (1 + 1)) ∈ RC). { apply (divRp7 x (1 + 1)) in H1; auto. } 
  apply FAT195a in H4. rewrite H4 in H3. rewrite <- H3. auto.
Qed.

Global Hint Resolve halfsum: core. 

Fact halfsum' : ∀ x , x ∈ RC -> - (x / (1 + 1)) - x / (1 + 1) = - x.
Proof.
  intros. 
  assert(1 ∈ RC); auto. assert(1 + 1 ∈ RC); auto.
  assert(x = (x / (1 + 1)) · (1 + 1)). 
  { apply (divRp7 x (1 + 1)) in H1; auto. }
  New H0. apply(FAT201a (x / (1 + 1)) 1 1) in H3; auto.
  assert((x / (1 + 1)) ∈ RC). { apply (divRp7 x (1 + 1)) in H1; auto. } 
  New H4. apply (FAT180 (x / (1 + 1)) (x / (1 + 1))) in H4; auto.
  apply halfsum in H. rewrite H in H4. auto.
Qed.

Global Hint Resolve halfsum': core. 

Fact Pdiv2 : ∀ x, x ∈ RC -> x > 0 -> x / (1 + 1) > 0.
Proof.
  intros. apply (aver2 0 x) in H0; auto. destruct H0. 
  rewrite AddRpa in H0; auto.
Qed.

Global Hint Resolve Pdiv2: core. 

Fact dou1 : ∀ x, x ∈ RC -> x > 0 -> (1 + 1) · x > x.
Proof.
  intros. rewrite (FAT194 (1+1) x); auto. rewrite (FAT201a x 1 1); auto. 
  rewrite FAT195a; auto. apply (FAT188a2 x 0 x) in H0; auto.
  apply AddRpa in H; auto. rewrite H in H0. auto.
Qed.

Global Hint Resolve dou1: core. 

Fact dou2 : ∀ x y, x ∈ RC -> y ∈ RC -> x < y -> (1 + 1) · x < (1 + 1) · y.
Proof.
  intros. rewrite (FAT194 (1+1) x); auto. rewrite (FAT194 (1+1) y); auto.
  rewrite (FAT201a x 1 1); auto. rewrite (FAT201a y 1 1); auto.
  rewrite FAT195a; auto. rewrite (FAT195a y); auto. 
  apply (@FAT189 y x y x) in H1; auto.
Qed.

Global Hint Resolve dou2: core. 

Fact dou2' : ∀ x y, x ∈ RC -> y ∈ RC -> x ≤ y -> (1 + 1) · x ≤ (1 + 1) · y.
Proof.
  intros. rewrite (FAT194 (1+1) x); auto. rewrite (FAT194 (1+1) y); auto.
  rewrite (FAT201a x 1 1); auto. rewrite (FAT201a y 1 1); auto.
  rewrite FAT195a; auto. rewrite (FAT195a y); auto. 
  apply (@FAT191a y x y x) in H1; auto.
Qed.

Global Hint Resolve dou2': core. 

Fact xynot0 : ∀ x y, x ∈ RC -> y ∈ RC -> x <> 0 -> y <> 0 -> x · y ≠ 0.
Proof.
  intros. intros. destruct (inRC H) as [?|[?|?]];
  destruct (inRC H0) as [?|[?|?]];try contradiction.
  - assert(x · y > 0); auto.
  - assert(x · y < 0); auto.
  - assert(x · y < 0); auto.
  - assert(x · y > 0); auto.
Qed.

Global Hint Resolve xynot0: core. 

Fact nnot0 : ∀ n, n ∈ Nat -> NtoR n ≠ 0.
Proof.
  intros. apply (@NtoRP n) in H. apply FAT169a in H. apply xg0; auto.
Qed.

Global Hint Resolve nnot0: core. 

Fact ng0 : ∀ n, n ∈ Nat -> NtoR n > 0.
Proof.
  intros. apply (@NtoRP n) in H. apply FAT169a in H; auto.
Qed.

Global Hint Resolve ng0: core. 

(* compute *)
Fact Add1 : ∀ x y, x ∈ RC -> y ∈ RC -> 0 < y -> x < x + y.
Proof.
  intros. apply (@FAT188a2 y 0 x) in H1; auto. rewrite AddRpa in H1; auto.
  rewrite FAT175 in H1; auto.
Qed.

Global Hint Resolve Add1: core. 

Fact Add1' : ∀ x y, x ∈ RC -> y ∈ RC -> 0 < y -> x - y < x.
Proof.
  intros. apply (@FAT188a2 y 0 x) in H1; auto. rewrite AddRpa in H1; auto.
  apply (@FAT188a2 (y + x) x (-y)) in H1; auto.
  rewrite MincEx2 in H1; auto.
Qed.

Global Hint Resolve Add1': core. 

Fact Add1'' : ∀ x y, x ∈ RC -> y ∈ RC -> 0 < y -> x < y + x.
Proof.
  intros. apply (@FAT188a2 y 0 x) in H1; auto. rewrite AddRpa in H1; auto.
Qed.

Global Hint Resolve Add1'': core. 

Fact Add2 : ∀ x y, x ∈ RC -> y ∈ RC -> 0 < y -> x - y < x + y.
Proof.
  intros. pose proof Add1 x y H H0 H1. pose proof Add1' x y H H0 H1.
  apply (@FAT171 (x - y) x (x + y)); auto.
Qed.

Global Hint Resolve Add2: core. 

Fact Add2' : ∀ x y, x ∈ RC -> y ∈ RC -> 0 < y -> x - y < y + x.
Proof.
  intros. assert(y + x = x + y). { apply(@FAT175 y x); auto. }
  rewrite H2; auto.
Qed.

Global Hint Resolve Add2': core. 

Fact Add3 : ∀ x y, x ∈ RC -> y ∈ RC -> x - y + (x + y) = x + x.
Proof.
  intros. rewrite (@FAT175 x (-y)); auto. 
  rewrite (@FAT175 (- y + x) (x + y)); auto. rewrite <- FAT186'; auto.
  apply (@FAT188b2 _ _ x); auto. rewrite FAT186'; auto. rewrite xminx; auto.
  rewrite AddRpb; auto.
Qed.

Global Hint Resolve Add3: core. 

Fact Add3' : ∀ x y, x ∈ RC -> y ∈ RC -> x - y + (y + x) = x + x.
Proof.
  intros. assert(y + x = x + y). { apply(@FAT175 y x); auto. }
  rewrite H1; auto.
Qed.

Global Hint Resolve Add3': core. 

Global Hint Resolve FAT181 FAT182a1 FAT182b1 FAT182c1: core. 
Global Hint Resolve FAT182a2 FAT182b2 FAT182c2: core. 

Corollary AbNRC : ∀ y, y ∈ RC -> y < 0 -> |y| = -y.
Proof.
  intros. New H0. apply FAT169b' in H0; auto. New H0. apply Nabs in H2; auto.
  rewrite <- Nmin in H2; auto.
Qed.

Corollary AbPRC : ∀ y, y ∈ RC -> y > 0 -> |y| = y.
Proof.
  intros. New H0. apply FAT169a' in H0; auto. New H0. apply Pabs in H2; auto.
Qed.

Global Hint Resolve AbNRC AbPRC: core. 

Corollary Ab9 : ∀ x y, x ∈ RC -> y ∈ RC -> |x - y| = 0 -> x = y.
Proof.
  intros. pose proof @FAT167 x y H H0. destruct H2; auto. destruct H2.
  - apply FAT182a2 in H2; auto. apply AbPRC in H2; auto. rewrite H2 in H1. auto.
  - assert(x - y < 0); auto. apply AbNRC in H3; auto. rewrite H3 in H1.
    rewrite FAT181 in H1; auto. assert(y = x); auto.
Qed.

Proposition NNPP' : ∀ P, ~~P -> P.
Proof.
  intros; destruct (classic P); tauto.
Qed.

Proposition not_ex_all_not :
 ∀ U P, ~ (∃ n : U, P n) -> ∀ n : U, ~ P n.
Proof.
  intros. intro. elim H; eauto.
Qed.

Definition Boundup_Ens S M := S ⊂ RC /\ M ∈ RC /\ (∀ x, x ∈ S -> x ≤ M).

Definition Bounddown_Ens S L := S ⊂ RC /\ L ∈ RC /\ (∀ x, x ∈ S -> L ≤ x).

Definition supremum S η := Boundup_Ens S η /\ (∀ z, Boundup_Ens S z -> η ≤ z).

Definition infimum S ξ := Bounddown_Ens S ξ 
  /\ (∀ z, Bounddown_Ens S z -> z ≤ ξ).

Definition Max S c := S ⊂ RC /\ c ∈ S /\ (∀ x, x ∈ S -> x ≤ c).

Definition Min S c := S ⊂ RC /\ c ∈ S /\ (∀ x, x ∈ S -> c ≤ x).

Lemma STlemma1 :∀ X α, X ⊂ RC -> α ∈ RC -> X ≠ Φ -> 
  ~ (∀x : Class,x ∈ X -> x ≤ α) -> (∃x1 : Class,x1 ∈ X /\ α < x1).
Proof.
  intros.
  apply NNPP. intro. elim H2. intros. apply NNPP. intro. elim H3. exists x.
  split; auto. apply NotleR; auto.
Qed.

Theorem SupremumT : ∀ X, X ⊂ RC -> X <> Φ -> (∃ c, Boundup_Ens X c) 
  -> exists η, supremum X η.
Proof.
  intros. destruct H1. TF (∃ m, Max X m).
  - destruct H2 as [m H2]. exists m. red; split.
    + red; split; auto. split.
      ++ destruct H2, H3. unfold Included in H2. apply H2; auto.
      ++ intros. destruct H2, H4. apply H5; auto.
    + intros. destruct H2, H4. unfold Boundup_Ens in H3.
      destruct H3, H6. apply H7; auto.
  - set (upperset := \{ λ a, Boundup_Ens X a \}).
    set (other := RC ~ upperset).
    assert (∃ y, y ∈ RC /\ Split other upperset y).
    { apply FAT205a. red. repeat split.
      + red; intros. unfold upperset in H3. unfold Boundup_Ens in H3. 
        appA2H H3. destruct H4; auto.
      + red; intros. unfold other in H3. appA2H H3. destruct H4, H5; auto.
      + red; intros. unfold other in H3. apply NEexE in H0. destruct H0. 
        assert(x0 ∈ RC ~ upperset).
        { unfold Setminus. unfold Intersection. appA2G. split.
          ++ unfold Included in H; apply H; auto.
          ++ unfold upperset. appA2G. unfold NotIn. intro. appA2H H4.
             unfold Boundup_Ens in H5. destruct H5, H6. 
             unfold Max in H2. apply H2. exists x0. split; auto. }
        rewrite H3 in H4. apply MKT16 in H4; auto.
      + red; intros.
        assert(x ∈ upperset).
        { unfold upperset. appA2G. unfold Boundup_Ens in H1. destruct H1, H4.
          unfold Ensemble; eauto. }
        rewrite H3 in H4. apply MKT16 in H4; auto.
      + red; intros. unfold other. apply MKT4. rewrite MKT6. 
        unfold Setminus. rewrite MKT8'. assert(upperset ⊂ RC). 
        { unfold Included; intros; unfold upperset in H4; unfold Boundup_Ens 
          in H4. appA2H H4. destruct H5, H6; auto. } New H4. apply MKT29 in H5.
        assert(upperset ∪ ¬ upperset = μ). { apply AUnionNotA. }
        rewrite H5. rewrite H6. rewrite MKT20'. auto.
      + red; intros. unfold other. unfold upperset in H4. appA2H H4.
        unfold other in H3. unfold upperset in H3. appA2H H3. destruct H6.
        appA2H H7. unfold Boundup_Ens in H5. destruct H5, H9.
        assert(~ Boundup_Ens X a). { intro. destruct H8. appA2G. }
        unfold Boundup_Ens in H11. assert(~ (∀x : Class,x ∈ X -> x ≤ a)). 
        { intro. destruct H11. split; auto. }
        New H12. apply STlemma1 in H13; auto. destruct H13. destruct H13.
        New H13. apply H10 in H13. assert(a < x0 /\ x0 ≤ b). { split; auto. }
        assert((a ≤ x0 /\ x0 < b) \/ (a < x0 /\ x0 ≤ b)). { right; auto. }
        apply FAT172 in H17; auto. }
    destruct H3. exists x0. red; split.
    + assert(upperset ⊂ RC).
      { unfold Included; intros. unfold upperset in H4. 
        unfold Boundup_Ens in H4. appA2H H4. destruct H5, H6; auto. }
      assert(other ⊂ RC).
      { unfold other. unfold Setminus. unfold Included. intros. 
        apply MKT4' in H5. destruct H5; auto. }
      assert(X ⊂ other).
      { unfold other. unfold Setminus. unfold Included. intros. apply MKT4'.
        destruct H3. split; auto. unfold Complement. appA2G. unfold upperset.
        unfold NotIn. intro. appA2H H8. unfold Boundup_Ens in H9.
        destruct H9, H10. assert(Max X z). { red; split; auto. }
        elim H2. exists z; auto. }
      destruct H3. unfold Boundup_Ens. repeat split; auto. intros.
      unfold Included in H6. apply H6 in H8. destruct H7.
      New H5. unfold Included in H10. New H8. apply H10 in H11.
      TF (x1 ≤ x0).
      ++ auto.
      ++ assert(x1 > x0). { apply NotleR in H12; auto. }
         apply H9 in H13; auto.
         unfold other in H8. unfold Setminus in H8. unfold Intersection in H8.
         appA2H H8. destruct H14. unfold Complement in H15. appA2H H15.
         unfold NotIn in H16. destruct H16; auto.
    + intros. New H4. rename H5 into Boundup_Ens_X_z. destruct H3; unfold Split 
      in H5; destruct H5; unfold Boundup_Ens in H4. destruct H4, H7; unfold 
      other in H5; unfold upperset in H6; apply NNPP; intro. apply NotleR in H9; 
      auto; apply si2' in H9; apply H5 in H9; auto; unfold Setminus in H9; 
      unfold Intersection in H9; appA2H H9; destruct H10; unfold upperset in 
      H11. assert(~ z ∈ \{ λ a, Boundup_Ens X a \}). 
      { intro. apply SNS in H11; auto. } elim H12. appA2G.
Qed.

Theorem InfimumT : ∀ X, X ⊂ RC -> X <> Φ -> (∃ c, Bounddown_Ens X c)
  -> exists ξ, infimum X ξ.
Proof.
  intros. destruct H1.
  set (X' := \{ λ r, (- r) ∈ X \}).
  assert (∃ y, supremum X' y). 
  { apply SupremumT.
    - red. intros. unfold X' in H2. appA2H H2. unfold Included in H.
      apply H in H3. apply minRC' in H3; auto.
    - apply NEexE in H0. destruct H0. unfold Included in H. New H0. 
      apply H in H2. New H2. apply minRC in H2. New H2. rename H4 into Hminx0. 
      apply minRC in H2. New H0. New H3. apply FAT177 in H5; apply FAT164 in H5; 
      auto. rewrite H5 in H0. assert(∃ z, z = - x0). { exists (-x0); auto. } 
      destruct H6. assert(- - x0 = - x1). { rewrite H6. auto. }
      rewrite H7 in H0. assert(x1 ∈ X'). 
      { unfold X'. appA2G. rewrite <- H6 in Hminx0. unfold Ensemble. 
        exists RC; auto. }
      red; intros. rewrite H9 in H8. apply MKT16 in H8; auto.
    - unfold Bounddown_Ens in H1. destruct H1, H2.
      unfold Boundup_Ens. assert(∃ z, z = - x). { exists (-x); auto. } 
      destruct H4. exists x0. repeat split.
      + unfold X'. unfold Included. intros. appA2H H5. unfold Included in H1.
        apply H1 in H6. apply minRC' in H6; auto.
      + apply minRC in H2. rewrite <- H4 in H2; auto.
      + intros. unfold X' in  H5. appA2H H5. New H6. apply xInX in H7; auto.
        apply minRC' in H7. rename H7 into Hx1RC.
        rewrite H4. apply H3 in H6.
        red. destruct H6.
        ++ left. assert(x = -x0). 
           { rewrite H4. apply FAT177 in H2. rewrite H2; auto. } 
           rewrite H7 in H6. New H2; apply minRC in H8. rewrite <- H4 in H8.
           rewrite <- H4. apply FAT183a2 in H6; auto. 
        ++ right. rewrite H6. apply FAT177 in Hx1RC. auto. }
  destruct H2 as [y [H2]].
  exists (-y); split. try red; intros.
  + repeat split.
    - auto.
    - unfold Boundup_Ens in H2. destruct H2, H4. apply minRC in H4; auto.
    - intros. unfold Boundup_Ens in H2. destruct H2, H5. unfold X' in H6. New H.
      New H4. unfold Included in H7. apply H7 in H8. apply minsie2; auto. 
      clear H8. clear H7. apply H6. appA2G. New H4. apply xInX in H4; auto. 
      apply FAT177 in H4. rewrite H4; auto. 
  + intros. New H4. rename H5 into Bounddown_Ens_X_z. 
    unfold Bounddown_Ens in H4. destruct H4, H5. unfold Boundup_Ens in H3. 
    New H2. unfold Boundup_Ens in H7. destruct H7, H8. apply minsie2'; auto. 
    apply H3. New H5. apply minRC in H10. repeat split; auto. intros. New H11.
    apply xInX in H12; auto. apply minRC in H12. apply minsie2'; auto.
    apply H6. unfold X' in H11. appA2H H11. auto.
Qed.

Theorem Sup_Inf_Principle : ∀ X, X ⊂ RC -> X <> Φ
  -> ((∃ c, Boundup_Ens X c) -> exists η, supremum X η)
     /\ ((∃ c, Bounddown_Ens X c) -> exists ξ, infimum X ξ).
Proof.
  intros. split; intros.
  - apply SupremumT; auto.
  - apply InfimumT; auto.
Qed.