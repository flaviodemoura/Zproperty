(** * The Z property implies Confluence *)

Definition Rel (A:Type) := A -> A -> Prop.

Inductive trans {A} (red: Rel A) : Rel A :=
| singl: forall a b,  red a b -> trans red a b
| transit: forall b a c,  red a b -> trans red b c -> trans red a c.

Arguments transit {A} {red} _ _ _ _ _ .

Lemma trans_composition {A} (R: Rel A):
  forall t u v, trans R t u -> trans R u v -> trans R t v.
Proof.
  intros t u v H1 H2. induction H1.
  - apply transit with b; assumption.
  - apply transit with b.
    + assumption.
    + apply IHtrans; assumption.
Qed.

Inductive refltrans {A:Type} (R: Rel A) : A -> A -> Prop :=
| refl: forall a, (refltrans R) a a
| rtrans: forall a b c, R a b -> refltrans R b c -> refltrans R a c.

Lemma refltrans_composition {A} (R: Rel A): forall t u v, refltrans R t u -> refltrans R u v -> refltrans R t v.
Proof.
  intros t u v.
  intros H1 H2.
  induction H1.
  - assumption.
  - apply rtrans with b.
    + assumption.
    + apply IHrefltrans; assumption.
Qed.

Lemma refltrans_composition2 {A} (R: Rel A): forall t u v, refltrans R t u -> R u v -> refltrans R t v.
Proof.
  intros t u v H1 H2. induction H1.
  - apply rtrans with v.
    + assumption.
    + apply refl.
  - apply IHrefltrans in H2.
    apply rtrans with b; assumption.
Qed.

Lemma trans_to_refltrans {A:Type} (R: Rel A): forall a b, trans R a b -> refltrans R a b.
Proof.
  intros a b Htrans.
  induction Htrans.
  - apply rtrans with b.
    + assumption.
    + apply refl.
  - apply rtrans with b; assumption.
Qed.

Definition Confl {A:Type} (R: Rel A) := forall a b c, (refltrans R) a b -> (refltrans R) a c -> (exists d, (refltrans R) b d /\ (refltrans R) c d).

Definition f_is_Z {A:Type} (R: Rel A) (f: A -> A) := forall a b, R a b -> ((refltrans R)  b (f a) /\ (refltrans R) (f a) (f b)).

Definition Z_prop {A:Type} (R: Rel A) := exists f:A -> A, forall a b, R a b -> ((refltrans R) b (f a) /\ (refltrans R) (f a) (f b)).

Theorem Z_prop_implies_Confl {A:Type}: forall R: Rel A, Z_prop R -> Confl R.
Proof.
  intros R HZ_prop.
  unfold Z_prop, Confl in *.
  intros a b c Hrefl1 Hrefl2.
  destruct HZ_prop as [g HZ_prop].
  generalize dependent c.
  induction Hrefl1.
  - intros c Hrefl2.
    exists c; split.
    + assumption.
    + apply refl.
  - intros c0 Hrefl2.
    assert (Hbga: refltrans R b (g a)).
    { apply HZ_prop; assumption.  }
    assert (Haga: refltrans R a (g a)).
    { apply rtrans with b; assumption.  }
    clear H. generalize dependent b.
    induction Hrefl2.
    + intros b Hrefl1 IHHrefl1 Hbga.
      assert (IHHrefl1_ga := IHHrefl1 (g a));
        apply IHHrefl1_ga in Hbga.
      destruct Hbga.
      exists x; split.
      * apply H.
      * apply refltrans_composition with (g a); [assumption | apply H].
    + intros b0 Hrefl1 IHHrefl1 Hb0ga.
      apply IHHrefl2 with b0.
      * apply refltrans_composition with (g a); apply HZ_prop; assumption.
      * assumption.
      * assumption.
      * apply refltrans_composition with (g a); [ assumption | apply HZ_prop; assumption].
Qed.

Definition SemiConfl {A:Type} (R: Rel A) := forall a b c, R a b -> (refltrans R) a c -> (exists d, (refltrans R) b d /\ (refltrans R) c d).

Theorem Z_prop_implies_SemiConfl {A:Type}: forall R: Rel A, Z_prop R -> SemiConfl R.
Proof.
  intros R HZ_prop.
  unfold Z_prop in HZ_prop.
  unfold SemiConfl.
  destruct HZ_prop.
  intros a b c Hrefl Hrefl'.
  assert (Haxa: refltrans R a (x a)).
  { apply rtrans with b.  - assumption.  - apply H.  assumption.  }
  apply H in Hrefl.
  destruct Hrefl.
  clear H1.
  generalize dependent b.
  induction Hrefl'.
  - intros.
    exists (x a).
    split; assumption.
  - intros.
    destruct IHHrefl' with b0.
    + apply refltrans_composition with (x a); apply H; assumption.
    + apply refltrans_composition with (x b).
      * apply refltrans_composition with (x a).
        ** assumption.
        ** apply H.
           assumption.
      * apply refl.
    + exists x0.
      assumption.
Qed.

Theorem Semi_equiv_Confl {A: Type}: forall R: Rel A, Confl R <-> SemiConfl R.
Proof.
  unfold Confl.
  unfold SemiConfl.
  intro R.
  split.
  - intros.
    apply H with a.
    + apply rtrans with b.
      * assumption.
      * apply refl.
    + assumption.
  - intros.
    generalize dependent c.
    induction H0.
    + intros.
      exists c.
      split.
      * assumption.
      * apply refl.
    + intros.
      specialize (H a).
      specialize (H b).
      specialize (H c0).
      apply H in H0.
      * destruct H0.
        destruct H0.
        apply IHrefltrans in H0.
        destruct H0.
        destruct H0.
        exists x0.
        split.
        ** assumption.
        ** apply refltrans_composition with x; assumption.
      * assumption.
Qed.

Corollary Zprop_implies_Confl_via_SemiConfl {A:Type}: forall R: Rel A, Z_prop R -> Confl R.
Proof. intros R HZ_prop. apply Semi_equiv_Confl. generalize dependent HZ_prop.
       apply Z_prop_implies_SemiConfl. Qed.

(** * An extension of the Z property: Compositional Z *)

Definition f_is_weak_Z {A} (R R': Rel A) (f: A -> A) := forall a b, R a b -> ((refltrans R') b (f a) /\ (refltrans R') (f a) (f b)).

Definition comp {A} (f1 f2: A -> A) := fun x:A => f1 (f2 x).
Notation "f1 # f2" := (comp f1 f2) (at level 40).

Inductive union {A} (red1 red2: Rel A) : Rel A :=
| union_left: forall a b, red1 a b -> union red1 red2 a b
| union_right: forall a b, red2 a b -> union red1 red2 a b.
Notation "R1 !_! R2" := (union R1 R2) (at level 40).

Lemma union_or {A}: forall (r1 r2: Rel A) (a b: A), (r1 !_! r2) a b <-> (r1 a b) \/ (r2 a b).
Proof.
  intros r1 r2 a b; split.
  - intro Hunion.
    inversion Hunion; subst.
    + left; assumption.
    + right; assumption.
  - intro Hunion.
    inversion Hunion.
    + apply union_left; assumption.
    + apply union_right; assumption.
Qed.

Require Import Setoid.
Require Import ZArith.

Lemma equiv_refltrans {A}: forall (R R1 R2: Rel A), (forall x y, R x y <-> (R1 !_! R2) x y) -> forall x y, refltrans (R1 !_! R2) x y -> refltrans R x y.
Proof.
  intros.
  induction H0.
  - apply refl.
  - apply rtrans with b.
    + apply H. assumption.
    + assumption.
  Qed.

Definition Z_comp {A:Type} (R :Rel A) := exists (R1 R2: Rel A) (f1 f2: A -> A), (forall x y, R x y <-> (R1 !_! R2) x y) /\ f_is_Z R1 f1 /\ (forall a b, R1 a b -> (refltrans R) ((f2 # f1) a) ((f2 # f1) b)) /\ (forall a b, b = f1 a -> (refltrans R) b (f2 b)) /\ (f_is_weak_Z R2 R (f2 # f1)).

Lemma refltrans_union {A:Type}: forall (R R' :Rel A) (a b: A), refltrans R a b -> refltrans (R !_! R') a b.
Proof.
  intros R R' a b Hrefl.
  induction Hrefl.
  - apply refl.
  - apply rtrans with b.
    + apply union_left. assumption.
    + assumption.
Qed.

Require Import Setoid.
Lemma refltrans_union_equiv {A}: forall (R R1 R2 : Rel A), (forall (x y : A), (R x y <-> (R1 !_! R2) x y)) -> forall (x y: A), refltrans (R1 !_! R2) x y -> refltrans R x y.
Proof.
  intros.
  induction H0.
  + apply refl.
  + apply rtrans with b.
    - apply H. assumption.
    - assumption.
Qed.

Theorem Z_comp_implies_Z_prop {A:Type}: forall (R :Rel A), Z_comp R -> Z_prop R.
Proof.
  intros R H.
  unfold Z_prop. unfold Z_comp in H. destruct H as
  [ R1 [ R2 [f1 [f2 [Hunion [H1 [H2 [H3 H4]]]]]]]].
  exists (f2 # f1).
  intros a b HR.
  apply Hunion in HR. inversion HR; subst. clear HR.
  - split.
    + apply refltrans_composition with (f1 a).
      * apply H1 in H.
        destruct H as [Hb Hf].
        apply (refltrans_union R1 R2) in Hb.
        apply refltrans_union_equiv with R1 R2.
        ** apply Hunion.
        ** apply Hb.
      * apply H3 with a; reflexivity.
    + apply H2; assumption. 
  - apply H4; assumption.
Qed.

(** Now we can use the proofs of the theorems [Z_comp_implies_Z_prop]
and [Z_prop_implies_Confl] to conclude that compositional Z is a
sufficient condition for confluence. *)

Corollary Z_comp_is_Confl {A}: forall (R: Rel A), Z_comp R -> Confl R.
Proof.
  intros R H.
  apply Z_comp_implies_Z_prop in H.
  apply Z_prop_implies_Confl; assumption.
Qed.

Theorem Z_comp_thm {A:Type}: forall (R :Rel A) (R1 R2: Rel A) (f1 f2: A -> A), (forall x y, R x y <-> (R1 !_! R2) x y) /\ f_is_Z R1 f1 /\ (forall a b, R1 a b -> (refltrans R) ((f2 # f1) a) ((f2 # f1) b)) /\ (forall a b, b = f1 a -> (refltrans R) b (f2 b)) /\ (f_is_weak_Z R2 R (f2 # f1)) -> f_is_Z R (f2 # f1).
Proof.
  intros R R1 R2 f1 f2 H.
  destruct H as [Hunion [H1 [H2 [H3 H4]]]].
  unfold f_is_Z.
  intros a b Hab.
  apply Hunion in Hab.
  inversion Hab; subst. clear Hab; split.
  - apply refltrans_composition with (f1 a).
    assert (Hbf1a: refltrans (R1 !_! R2) b (f1 a)).
    { apply refltrans_union. apply H1; assumption. }
    apply equiv_refltrans with R1 R2.
    + assumption.
    + assumption.
    + apply H3 with a; reflexivity.
  - unfold comp.
    assert (H' := H).
    apply H1 in H.
    destruct H as [H Hf1].
    clear H.
    apply H2; assumption.
  - apply H4; assumption.
Qed. 

Corollary Z_comp_eq_corol {A:Type}: forall (R :Rel A) (R1 R2: Rel A) (f1 f2: A -> A), (forall x y, R x y <-> (R1 !_! R2) x y) /\ (forall a b, R1 a b -> (f1 a) = (f1 b)) /\ (forall a, (refltrans R1) a (f1 a)) /\ (forall b a, a = f1 b -> (refltrans R) a (f2 a)) /\ (f_is_weak_Z R2 R (f2 # f1)) -> f_is_Z R (f2 # f1).
Proof.
  intros R R1 R2 f1 f2 H.
  destruct H as [Hunion [H1 [H2 [H3 H4]]]].
  pose proof (Z_comp_thm := Z_comp_thm R R1 R2 f1 f2).
  apply Z_comp_thm. split.
  - assumption.
  - split.
    + unfold f_is_Z.
      intros a b Hab. split.
      * apply H1 in Hab.
        rewrite Hab.
        apply H2.
      * apply H1 in Hab.
        rewrite Hab.
        apply refl.
    + split.
      * intros a b Hab.
        unfold comp.
        apply H1 in Hab.
        rewrite Hab.
        apply refl.
      * split; assumption.
Qed.
        
Definition Z_comp_eq {A:Type} (R :Rel A) := exists (R1 R2: Rel A) (f1 f2: A -> A), (forall x y, R x y <-> (R1 !_! R2) x y) /\ (forall a b, R1 a b -> (f1 a) = (f1 b)) /\ (forall a, (refltrans R1) a (f1 a)) /\ (forall b a, a = f1 b -> (refltrans R) a (f2 a)) /\ (f_is_weak_Z R2 R (f2 # f1)).

Lemma Z_comp_eq_implies_Z_comp {A:Type}: forall (R : Rel A), Z_comp_eq R -> Z_comp R.
Proof.
  intros R Heq. unfold Z_comp_eq in Heq.
  destruct Heq as [R1 [R2 [f1 [f2 [Hunion [H1 [H2 [H3 H4]]]]]]]].
  unfold Z_comp.
  exists R1, R2, f1, f2.
  split.
  - assumption.
  - split.
    + unfold f_is_Z.
      intros a b H; split.
      * apply H1 in H. rewrite H. apply H2.
      * apply H1 in H. rewrite H. apply refl.
    + split.
      * intros a b H.
        unfold comp.
        apply H1 in H.
        rewrite H.
        apply refl.
      * split; assumption.
Qed.

Lemma Z_comp_eq_implies_Z_prop {A:Type}: forall (R : Rel A), Z_comp_eq R -> Z_prop R.
Proof.
  intros R Heq.
  unfold Z_comp_eq in Heq.
  destruct Heq as [R1 [R2 [f1 [f2 [Hunion [H1 [H2 [H3 H4]]]]]]]].
  unfold Z_prop.  exists (f2 # f1).
  intros a b Hab.
  split.
  - apply Hunion in Hab.
    inversion Hab; subst.
    + unfold comp.
      apply H1 in H. rewrite H.
      apply refltrans_composition with (f1 b).
      * assert (H5: refltrans R1 b (f1 b)).
        {
          apply H2.
        }
        apply refltrans_union_equiv with R1 R2.
        ** assumption.
        ** apply refltrans_union. assumption.
      * apply H3 with b. reflexivity.
    + apply H4. assumption.
  - apply Hunion in Hab.
    inversion Hab. subst.
    + unfold comp. apply H1 in H. rewrite H. apply refl.
    + apply H4. assumption.
Qed.
