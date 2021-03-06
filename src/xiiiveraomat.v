(** Basic definitions *)

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

(** Z property implies confluence *)

Definition Confl {A:Type} (R: Rel A) := forall a b c, (refltrans R) a b -> (refltrans R) a c -> (exists d, (refltrans R) b d /\ (refltrans R) c d).

Definition Z_prop {A:Type} (R: Rel A) := exists f:A -> A, forall a b, R a b -> ((refltrans R) b (f a) /\ (refltrans R) (f a) (f b)).

Theorem Z_prop_implies_Confl_fail1 {A:Type}: forall R: Rel A, Z_prop R -> Confl R.
Proof.
  intros R HZ_prop. 
  unfold Z_prop, Confl in *. 
  intros a b c Hrefl1 Hrefl2.
  Print nat.
  Check nat_ind.
  Check refltrans_ind.
  generalize dependent c.
  generalize dependent b.
  generalize dependent a.
  Check refltrans_ind.
  apply (refltrans_ind A R (fun a b => forall c: A, _ -> exists d: A, _)).
  - intros a c Hac_star.
    exists c; split.
    + assumption. 
    + apply refl.
  - intros a b' b  Hab' Hb'b_star IH1 c Hac_star.
    Check refltrans_ind.
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

Theorem Z_prop_implies_Confl_fail2 {A:Type}: forall R: Rel A, Z_prop R -> Confl R.
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
    (* *)
  - intros a b' b  Hab' Hb'b_star IH1 c Hac_star.
    assert (Hab'_Z := Hab').
    destruct HZ_prop as [f HZ_prop].
    apply HZ_prop in Hab'_Z.
    destruct Hab'_Z as [Hb'fa_star Hfafb'_star].
    assert (Hafa_star: refltrans R a (f a)).
    {
      apply rtrans with b'; assumption.
    }
    clear Hab'.
    Check refltrans_ind.
    generalize dependent Hfafb'_star.
    generalize dependent Hb'fa_star.
    generalize dependent Hafa_star.
    generalize dependent c.
    generalize dependent a.    
    apply (refltrans_ind A R (fun a c => refltrans R a (f a) -> refltrans R b' (f a) -> refltrans R (f a) (f b') -> exists d: A, _)).
    + intros a Hafa_star Hb'fa_star Hfafb'_star.
      apply IH1 in Hb'fa_star.
      inversion Hb'fa_star as [d [Hbd_star Hfad_star]].
      exists d; split.
      * assumption.
      * apply refltrans_composition with (f a); assumption.
    + intros a c' c  Hac' Hc'c_star IH2 Hafa_star Hb'fa_star Hfafb'_star.
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
    (* *)
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

(** The compositional Z-property *)

Definition f_is_Z {A:Type} (R: Rel A) (f: A -> A) := forall a b, R a b -> ((refltrans R)  b (f a) /\ (refltrans R) (f a) (f b)). 

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

Lemma refltrans_union_l {A:Type}: forall (R R' :Rel A) (a b: A), refltrans R a b -> refltrans (R !_! R') a b.
Proof.
  intros R R' a b Hrefl.
  induction Hrefl.
  - apply refl.
  - apply rtrans with b.
    + apply union_left; assumption.
    + assumption.
Qed.

Definition Z_comp {A:Type} (R :Rel A) := exists (R1 R2: Rel A) (f1 f2: A -> A),
    R = (R1 !_! R2) /\
    f_is_Z R1 f1 /\
    (forall a b, R1 a b -> (refltrans R) (f2 a) (f2 b)) /\
    (forall a b, b = f1 a -> (refltrans R) b (f2 b)) /\
    (f_is_weak_Z R2 R (f2 # f1)).

Theorem Z_comp_implies_Z_prop {A:Type}: forall (R :Rel A), Z_comp R -> Z_prop R.
Proof.
  intros R H. 
  unfold Z_prop.
  unfold Z_comp in H.
  destruct H as [ R1 [ R2 [f1 [f2 [Hunion [H1 [H2 [H3 H4]]]]]]]]. 
  exists (f2 # f1). 
  intros a b HR. 
  inversion Hunion; subst.
  clear H.
  inversion HR; subst. 
  - split. 
    + apply refltrans_composition with (f1 a). 
      * apply H1 in H.
        destruct H.
        apply refltrans_union_l; assumption. 
      * apply H3 with a; reflexivity.    
    + apply H1 in H.
      destruct H.
      clear H HR.
      unfold comp. 
      induction H0. 
      * apply refl. 
      * apply refltrans_composition with (f2 b0). 
        ** apply H2; assumption. 
        ** apply IHrefltrans. 
  - apply H4; assumption. 
Qed.

Corollary Z_comp_is_Confl {A}: forall (R: Rel A), Z_comp R -> Confl R.
Proof.
  intros R H.
  apply Z_comp_implies_Z_prop in H.
  apply Z_prop_implies_Confl; assumption.
Qed.

Definition Z_comp_eq {A:Type} (R :Rel A) := exists (R1 R2: Rel A) (f1 f2: A -> A), R = (R1 !_! R2) /\ (forall a b, R1 a b -> (f1 a) = (f1 b)) /\ (forall a, (refltrans R1) a (f1 a)) /\ (forall b a, a = f1 b -> (refltrans R) a (f2 a)) /\ (f_is_weak_Z R2 R (f2 # f1)).
        
Lemma Z_comp_eq_implies_Z_prop {A:Type}: forall (R : Rel A), Z_comp_eq R -> Z_prop R.
Proof.
  intros R Heq.
  unfold Z_comp_eq in Heq. 
  destruct Heq as [R1 [R2 [f1 [f2 [Hunion [H1 [H2 [H3 H4]]]]]]]].
  unfold Z_prop.
  exists (f2 # f1). 
  intros a b Hab. 
  inversion Hunion; subst; clear H.
  inversion Hab; subst; clear Hab. 
  - unfold comp; split. 
    + apply refltrans_composition with (f1 b). 
      * apply refltrans_union_l.
        apply H2. 
      * apply H1 in H.
        rewrite H.
        apply H3 with b; reflexivity. 
    + apply H1 in H.
      rewrite H.
      apply refl. 
  - apply H4; assumption. 
Qed.
