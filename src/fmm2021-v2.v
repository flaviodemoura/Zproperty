Definition Rel (A:Type) := A -> A -> Prop.

Inductive refltrans {A:Type} (R: Rel A) : Rel A :=
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

Definition Confl {A:Type} (R: Rel A) := forall a b c, (refltrans R) a b -> (refltrans R) a c -> (exists d, (refltrans R) b d /\ (refltrans R) c d).

Definition f_is_Z {A:Type} (R: Rel A) (f: A -> A) := forall a b, R a b -> ((refltrans R)  b (f a) /\ (refltrans R) (f a) (f b)). 

Definition Z_prop {A:Type} (R: Rel A) := exists f:A -> A, f_is_Z R f.

Theorem Z_prop_implies_Confl_fail1 {A:Type}: forall R: Rel A, Z_prop R -> Confl R.
Proof.
  intros R HZ_prop. 
  unfold Z_prop, Confl in *. 
  intros a b c Hrefl1 Hrefl2.
  generalize dependent c.
  generalize dependent b.
  generalize dependent a.
  apply (refltrans_ind A R (fun a b => forall c: A, _ -> exists d: A, _)).
  - intros a c Hac_star.
    exists c; split.
    + assumption. 
    + apply refl.
  - intros a b' b  Hab' Hb'b_star IH1 c Hac_star.
    generalize dependent Hab'.
    generalize dependent c.
    generalize dependent a.    
    apply (refltrans_ind A R (fun a c => R a b' -> exists d: A, _)).
    + intros a Hab'.
      exists b; split.
      * apply refl.
      * apply rtrans with b'; assumption.
    + intros a c' c  Hac' Hc'c IH2 Hab'.
Abort.

Theorem Z_prop_implies_Confl {A:Type}: forall R: Rel A, Z_prop R -> Confl R.
Proof.
  intros R HZ_prop. 
  unfold Z_prop, Confl in *. 
  intros a b c Hrefl1 Hrefl2. 
  generalize dependent c.
  generalize dependent b.
  generalize dependent a.
  apply (refltrans_ind A R (fun a b => forall c: A, _ -> exists d: A, _)).
  - intros a c Hac_star.
    exists c; split.
    + assumption. 
    + apply refl.
  - intros a b' b  Hab' Hb'b_star IH1 c Hac_star.
    assert (Hab'_Z := Hab').
    destruct HZ_prop as [f HZ_prop].
    apply HZ_prop in Hab'_Z.
    destruct Hab'_Z as [Hb'fa_star Hfafb'_star].
    assert (Hafa_star: refltrans R a (f a)).
    {
      apply rtrans with b'; assumption.
    }
    clear Hab' Hfafb'_star.
    generalize dependent Hb'fa_star.
    generalize dependent Hafa_star.
    generalize dependent c.
    generalize dependent a.    
    apply (refltrans_ind A R (fun a c => refltrans R a (f a) -> refltrans R b' (f a) -> exists d: A, _)).
    + intros a Hafa_star Hb'fa_star.
      apply IH1 in Hb'fa_star.
      inversion Hb'fa_star as [d [Hbd_star Hfad_star]].
      exists d; split.
      * assumption.
      * apply refltrans_composition with (f a); assumption.
    + intros a c' c  Hac' Hc'c_star IH2 Hafa_star Hb'fa_star.
      apply HZ_prop in Hac'.
      destruct Hac' as [Hc'fa_star Hfafc'_star].
      apply IH2; apply refltrans_composition with (f a); assumption.
Qed.

Theorem Z_prop_implies_Confl' {A:Type}: forall R: Rel A, Z_prop R -> Confl R.
Proof.
  intros R HZ_prop. 
  unfold Z_prop, Confl in *. 
  intros a b c Hrefl1 Hrefl2. 
  generalize dependent c.
  induction Hrefl1.
  - intros c Hrefl2. 
    exists c; split.
    + assumption. 
    + apply refl.
  - intros c0 Hrefl2.
    assert (H' := H).
    destruct HZ_prop as [f HZ_prop].
    apply HZ_prop in H'.
    destruct H' as [H1 H2].
    assert (Hfa:  refltrans R a (f a)).
    {
      apply rtrans with b; assumption.
    }
    clear H H2.
    induction Hrefl2.
    + apply IHHrefl1 in H1.
      destruct H1 as [d [H11 H12]].
      exists d; split.
      * assumption.
      * apply refltrans_composition with (f a); assumption.
    + apply HZ_prop in H.
      destruct H as [H H'].
      apply IHHrefl2; apply refltrans_composition with (f a); assumption.
Qed.

Definition f_is_weak_Z {A} (R R': Rel A) (f: A -> A) := forall a b, R a b -> ((refltrans R') b (f a) /\ (refltrans R') (f a) (f b)).

Definition comp {A} (f1 f2: A -> A) := fun x:A => f1 (f2 x).
Notation "f1 # f2" := (comp f1 f2) (at level 40).

Inductive union {A} (red1 red2: Rel A) : Rel A :=
| union_left: forall a b, red1 a b -> union red1 red2 a b
| union_right: forall a b, red2 a b -> union red1 red2 a b.
Notation "R1 !_! R2" := (union R1 R2) (at level 40).

Lemma refltrans_union {A:Type}: forall (R R' :Rel A) (a b: A), refltrans R a b -> refltrans (R !_! R') a b.
Proof.
  intros R R' a b Hrefl.
  induction Hrefl.
  - apply refl.
  - apply rtrans with b.
    + apply union_left. assumption.
    + assumption.
Qed.

Lemma equiv_refltrans {A}: forall (R R1 R2: Rel A), (forall x y, R x y <-> (R1 !_! R2) x y) -> forall x y, refltrans (R1 !_! R2) x y -> refltrans R x y.
Proof.
  intros.
  induction H0.
  - apply refl.
  - apply rtrans with b.
    + apply H. assumption.
    + assumption.
  Qed.

Definition Z_comp {A:Type} (R R1 R2: Rel A) := exists (f1 f2: A -> A), (forall x y, R x y <-> (R1 !_! R2) x y) /\ f_is_Z R1 f1 /\ (forall a b, R1 a b -> (refltrans R) ((f2 # f1) a) ((f2 # f1) b)) /\ (forall a b, b = f1 a -> (refltrans R) b (f2 b)) /\ (f_is_weak_Z R2 R (f2 # f1)).

Theorem Z_comp_implies_Z_prop {A:Type}: forall (R R1 R2 :Rel A), Z_comp R R1 R2 -> Z_prop R.
Proof.
  intros R R1 R2 H.
  unfold Z_prop. unfold Z_comp in H. destruct H as
  [ f1 [f2 [Hunion [H1 [H2 [H3 H4]]]]]].
  exists (f2 # f1).
  unfold f_is_Z.
  intros a b HR.
  apply Hunion in HR. inversion HR; subst. clear HR.
  - split.
    + apply refltrans_composition with (f1 a).
      * apply H1 in H.
        destruct H as [Hb Hf].
        apply (refltrans_union R1 R2) in Hb.
        apply equiv_refltrans with R1 R2.
        ** apply Hunion.
        ** apply Hb.
      * apply H3 with a; reflexivity.
    + apply H2; assumption. 
  - apply H4; assumption.
Qed.

Corollary Z_comp_is_Confl {A}: forall (R R1 R2: Rel A), Z_comp R R1 R2 -> Confl R.
Proof.
  intros R R1 R2 H.
  apply Z_comp_implies_Z_prop in H.
  apply Z_prop_implies_Confl; assumption.
Qed.

Corollary Z_comp_eq_corol {A:Type}: forall (R R1 R2: Rel A), exists (f1 f2: A -> A), (forall x y, R x y <-> (R1 !_! R2) x y) /\ (forall a b, R1 a b -> (f1 a) = (f1 b)) /\ (forall a, (refltrans R1) a (f1 a)) /\ (forall b a, a = f1 b -> (refltrans R) a (f2 a)) /\ (f_is_weak_Z R2 R (f2 # f1)) -> f_is_Z R (f2 # f1).
Proof.
  intros R R1 R2.
  pose proof (Z_comp_thm := Z_comp_implies_Z_prop R).
  unfold Z_prop in Z_comp_thm.
  unfold Z_comp in Z_comp_thm.
  intro H.
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
        apply equiv_refltrans with R1 R2.
        ** assumption.
        ** apply refltrans_union. assumption.
      * apply H3 with b. reflexivity.
    + apply H4. assumption.
  - apply Hunion in Hab.
    inversion Hab; subst.
    + unfold comp. apply H1 in H. rewrite H. apply refl.
    + apply H4. assumption.
Qed.
