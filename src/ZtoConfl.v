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

Lemma transit' {A:Type} (R: Rel A):
  forall t u v, trans R t u -> R u v -> trans R t v.
Proof.
  intros t u v H1 H2. induction H1.
  - apply transit with b. 
    + assumption.
    + apply singl.
      assumption.
  - apply IHtrans in H2.
    apply transit with b; assumption.
Qed.

Lemma trans_composition' {A} (R: Rel A):
  forall t v, trans R t v -> (R t v \/ exists u, trans R t u /\ R u v).
Proof.
 intros t v H.
 induction H.
 - left; assumption.
 - right.
   destruct IHtrans.
   + exists b.
     split.
     * apply singl.
       assumption.
     * assumption.
   + destruct H1.
     exists x.
     split.
     * apply transit with b.
       ** assumption.
       ** apply H1.
     * apply H1.
Qed.

Inductive refltrans {A:Type} (R: Rel A) : A -> A -> Prop :=
| refl: forall a, (refltrans R) a a
| rtrans: forall a b c, R a b -> refltrans R b c -> refltrans R a c.

Lemma refltrans_composition {A} (R: Rel A):
  forall t u v, refltrans R t u -> refltrans R u v -> refltrans R t v.
Proof.
  intros t u v H1 H2. induction H1.
  - assumption.
  - apply rtrans with b.
    + assumption.
    + apply IHrefltrans; assumption.
Qed.

Lemma rtrans' {A} (R: Rel A): forall t u v, refltrans R t u -> R u v -> refltrans R t v.
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

Definition Z_prop {A:Type} (R: Rel A) := exists wb:A -> A, forall a b, R a b -> ((refltrans R) b (wb a) /\ (refltrans R) (wb a) (wb b)).

Definition f_is_Z {A:Type} (R: Rel A) (f: A -> A) := forall a b, R a b -> ((refltrans R)  b (f a) /\ (refltrans R) (f a) (f b)). 

Lemma f_is_Z_implies_Z_prop {A:Type}: forall (R: Rel A) (f:A -> A), f_is_Z R f -> Z_prop R.
Proof.
  intros R f H.
  unfold Z_prop.
  exists f.
  unfold f_is_Z in H.
  assumption.
Qed.

Theorem Z_prop_implies_Confl {A:Type}: forall R: Rel A, Z_prop R -> Confl R.
Proof.
  intros R HZ_prop.
  unfold Z_prop in HZ_prop.
  unfold Confl.
  destruct HZ_prop as [wb HZ_prop].
  intros a b c Hrefl1 Hrefl2.
  generalize dependent c.
  induction Hrefl1.
  - intros c Hrefl.
    exists c; split.
    + assumption.
    + apply refl.
  - intros c0 Hrefl2.
    assert (Hbwba: refltrans R b (wb a)).
    {
      apply HZ_prop; assumption.
    }
    assert (Hawba: refltrans R a (wb a)).
    {
      apply rtrans with b; assumption.
    }
    clear H.
    generalize dependent b.
    induction Hrefl2.
    + intros b Hone IHHrefl1 HZb.
      assert (IHHrefl1_wba := IHHrefl1 (wb a)).
      apply IHHrefl1_wba in HZb.
      destruct HZb.
      exists x; split.
      * apply H.
      * apply refltrans_composition with (wb a).
        ** assumption.
      ** apply H.
    + intros b0 Hrefl1 IHHrefl1 H'.
      apply IHHrefl2 with b0.
      * apply refltrans_composition with (wb a); apply HZ_prop; assumption.
      * assumption.
      * assumption.
      * apply refltrans_composition with (wb a).
        ** assumption.
        ** apply HZ_prop; assumption.
Qed.

(* begin hide *)
Inductive union {A} (red1 red2: Rel A) : Rel A :=
 | union_left: forall a b,  red1 a b -> union red1 red2 a b
 | union_right: forall a b,  red2 a b -> union red1 red2 a b.

Notation "R1 !_! R2" := (union R1 R2) (at level 40).

Lemma union_idemp {A}: forall (R : Rel A),  (R !_! R) = R.
Proof.
Admitted.  
  
Definition comp {A} (f1 f2: A -> A) := fun x:A => f1 (f2 x).
Notation "f1 # f2" := (comp f1 f2) (at level 40).
(* end hide *)

Definition f_is_weak_Z {A} (R R': Rel A) (f: A -> A) := forall a b, R a b -> ((refltrans R')  b (f a) /\ (refltrans R') (f a) (f b)). 

Definition Z_comp {A:Type} (R :Rel A) := exists (R1 R2: Rel A) (f1 f2: A -> A), R = (R1 !_! R2) /\ f_is_Z R1 f1 /\ (forall a b, R1 a b -> (refltrans R) (f2 a) (f2 b)) /\ (forall a b, b = f1 a -> (refltrans R) b (f2 b)) /\ (f_is_weak_Z R2 R (f2 # f1)).

Lemma refltrans_union {A:Type}: forall (R R' :Rel A) (a b: A), refltrans R a b -> refltrans (R !_! R') a b.
Proof.
  intros R R' a b Hrefl.
  induction Hrefl.
  - apply refl.
  - apply rtrans with b.
    + apply union_left; assumption.
    + assumption.
Qed.
    
Lemma Z_comp_implies_Z_prop {A:Type}: forall (R :Rel A), Z_comp R -> Z_prop R.
Proof.
  intros R H.
  unfold Z_comp in H.
  destruct H as [ R1 [ R2 [f1 [f2 [Hunion [HfZ [Hrefl [HIm Hweak]]]]]]]].
  apply f_is_Z_implies_Z_prop with (f2 # f1).
  unfold f_is_Z in *.
  unfold f_is_weak_Z in Hweak.
  intros a b HR.
  inversion Hunion; subst.
  clear H.
  inversion HR; subst.
  - split.
    + apply refltrans_composition with (f1 a).
      * apply HfZ in H.
        destruct H.
        apply refltrans_union; assumption.
      * apply HIm with a; reflexivity.
    + apply HfZ in H.
      destruct H.
      clear H HR.
      unfold comp.
      induction H0.
      * apply refl.
      * apply refltrans_composition with (f2 b0).
        ** apply Hrefl; assumption.
        ** assumption.
  - apply Hweak; assumption.    
Qed.

Lemma Z_prop_implies_Z_comp {A:Type}: forall (R : Rel A), Z_prop R -> Z_comp R.
Proof.
  intros R HZ_prop.
  unfold Z_prop in HZ_prop.
  destruct HZ_prop.
  unfold Z_comp.
  exists R. exists R. exists x. exists (@id A). split.
  - symmetry.
    apply union_idemp.
  - split.
    + assumption.
    + split.
      * intros a b Hab.
        apply rtrans with b.
        ** assumption.
        ** apply refl.
      * split.
        ** intros a b Heq.
           apply refl.
        ** auto.
Qed.

Theorem Z_comp_equiv_Z_prop {A:Type}: forall (R : Rel A), Z_prop R <-> Z_comp R.
Proof.
  split.
  - apply Z_prop_implies_Z_comp.
  - apply Z_comp_implies_Z_prop.
Qed.

Corollary Z_comp_is_Confl {A}: forall (R: Rel A), Z_comp R -> Confl R.
Proof.
  intros R H.
  apply Z_comp_implies_Z_prop in H.
  apply Z_prop_implies_Confl; assumption.  
Qed.

Definition Z_comp_eq {A:Type} (R :Rel A) := exists (R1 R2: Rel A) (f1 f2: A -> A), R = (R1 !_! R2) /\ (forall a b, R1 a b -> (f1 a) = (f1 b)) /\ (forall a, (refltrans R1) a (f1 a)) /\ (forall b a, a = f1 b -> (refltrans R) a (f2 a)) /\ (f_is_weak_Z R2 R (f2 # f1)).

Definition Z_comp_eq' {A:Type} (R :Rel A) := exists (R1 R2: Rel A) (f : A -> A), R = (R1 !_! R2) /\ (forall a b, R1 a b -> (f a) = (f b)) /\ (forall a, (refltrans R2) a (f a)) /\ (f_is_weak_Z R2 R f).

(*
Definition Z_comp_new_eq {A:Type} (R :Rel A) := forall (R1 R2: Rel A), R = (R1 !_! R2) -> exists (f1 f2: A -> A), (forall a b, R1 a b -> (f1 a) = (f1 b)) /\ (forall a, (refltrans R1) a (f1 a)) /\ (forall b a, a = f1 b -> (refltrans R) a (f2 a)) /\ (f_is_weak_Z R2 R (f2 # f1)).
 *)

Lemma Z_comp_eq'_implies_Z_prop {A:Type}: forall (R : Rel A), Z_comp_eq' R -> Z_prop R.
Proof.
  unfold Z_comp_eq'.
  unfold Z_prop.
  intros R H.
  destruct H as [R1 [R2 [f [Hunion [HR1eqf [HR2f Hweak]]]]]].
  exists f.
  intros a b Hab.
  inversion Hunion; subst.
  clear H.
  split.
  - induction Hab.
    + apply HR1eqf in H.
      apply refltrans_composition with (f b).
      * specialize (HR2f b).
        induction HR2f.
        ** apply refl.
        **  apply rtrans with b.
            *** apply union_right; assumption.
            *** apply IHHR2f; assumption.
      * rewrite H; apply refl.
    + apply Hweak; assumption.
  - induction Hab.
    + apply HR1eqf in H.
      rewrite <- H.
      apply refl.
    + apply Hweak; assumption.
Qed.

Lemma Z_comp_eq_implies_Z_prop {A:Type}: forall (R : Rel A), Z_comp_eq R -> Z_prop R.
Proof.
  unfold Z_comp_eq.
  unfold Z_prop.
  intros R H.
  destruct H as [R1 [R2 [f1 [f2 [Hunion [HR1eqf1 [Haf1a [HRf2 Hweak]]]]]]]].
  exists (f2 # f1).
  inversion Hunion; subst.
  clear H.
  intros a b Hab.
  split.
  - induction Hab.
    + apply HR1eqf1 in H.
      apply refltrans_composition with (f1 b).
      * specialize (Haf1a b).
        induction Haf1a.
        **  apply refl.
        **  apply rtrans with b.
            *** apply union_left.
                assumption.
            *** apply IHHaf1a; assumption.
      * rewrite <- H in *.
        apply HRf2 with b; assumption.
    + apply Hweak; assumption.
  - inversion Hab; subst.
    + apply HR1eqf1 in H.
      assert (H2: ((f2 # f1) a) = ((f2 # f1) b)).
      {
        unfold comp.
        apply f_equal; assumption.
      }
      rewrite H2.
      apply refl.
    + apply Hweak; assumption.
Qed.

(*
Lemma Z_comp_eq_implies_Z_prop {A:Type}: forall (R : Rel A), Z_comp_eq R -> Z_prop R.
Proof.
  unfold Z_comp_eq.
  unfold Z_prop.
  intros.
  destruct H as [R1 [R2 [f1 [f2 [Hunion [HR1eqf1 [Haf1a [HRf2 Hweak]]]]]]]].
  exists (f2 # f1).
  inversion Hunion; subst.
  clear H.
  intros a b Hab.
  assert (H':  forall a : A, refltrans R2 a (f1 a)).
  {
    admit.
  }
  split.
  - induction Hab.
    + apply HR1eqf1 in H.
      apply refltrans_composition with (f1 b).
      * specialize (H' b).
        induction H'.
        **  apply refl.
        **  apply rtrans with b.
            *** apply union_right.
                assumption.
            *** apply IHH'; assumption.




        induction Haf1a.
        **  apply refl.
        **  apply rtrans with b.
            *** apply union_left.
                assumption.
            *** apply IHHaf1a; assumption.
      * rewrite <- H in *.
        apply HRf2 with b; assumption.
    + apply Hweak; assumption.
  - inversion Hab; subst.
    + apply HR1eqf1 in H.
      assert (H2: ((f2 # f1) a) = ((f2 # f1) b)).
      {
        unfold comp.
        apply f_equal; assumption.
      }
      rewrite H2.
      apply refl.
    + apply Hweak; assumption.
Qed.
*)

Require Import Morphisms.

(*
Require Import Setoid.

Definition Z_prop_mod {A:Type} (R : Rel A) := exists eqA, Equivalence eqA ->  (exists wb:A -> A, forall a b, R a b -> ((refltrans R) b (wb a) /\ (refltrans R) (wb a) (wb b)) /\ (forall c d, eqA c d -> wb c = wb d)).

Definition Z_prop_mod' {A:Type} (R : Rel A) := exists eqA, Equivalence eqA /\  (exists wb:A -> A, forall a b, R a b -> ((refltrans R) b (wb a) /\ (refltrans R) (wb a) (wb b)) /\ (forall c d, eqA c d -> wb c = wb d)).

Definition Z_prop_mod2 {A:Type} (R : Rel A) := forall eqA, Equivalence eqA ->  (exists wb:A -> A, forall a b, R a b -> ((refltrans R) b (wb a) /\ (refltrans R) (wb a) (wb b)) /\ (forall c d, eqA c d -> wb c = wb d)).
 *)

Definition Z_prop_mod3 {A:Type} (R eqA : Rel A) := Equivalence eqA /\  (exists wb:A -> A, forall a b, R a b -> ((refltrans R) b (wb a) /\ (refltrans R) (wb a) (wb b)) /\ (forall c d, eqA c d -> wb c = wb d)).

(*
Lemma Z_prop_mod2_implies_Z_prop_mod3 {A:Type}: forall (R eqA : Rel A), Z_prop_mod2 R -> Z_prop_mod3 R eqA. 
Proof.
  intros R eqA Hmod.
  unfold Z_prop_mod2 in Hmod.
  unfold Z_prop_mod3.
  intros HeqA.
  apply Hmod in HeqA.
  assumption.
Qed.

Lemma Z_prop_mod3_implies_Z_prop_mod {A:Type}: forall (R eqA : Rel A), Z_prop_mod3 R eqA -> Z_prop_mod R. 
Proof.
  intros R eqA Hmod3.
  unfold Z_prop_mod3 in Hmod3.
  unfold Z_prop_mod.
  exists eqA.
  intros HeqA.
  apply Hmod3 in HeqA.
  assumption.
Qed.

Corollary Z_prop_mod_implies_Z_comp {A:Type}: forall (R eqA: Rel A), Z_prop_mod2 R eqA -> Z_comp R.
Proof.
  intros R eqA H.
  unfold Z_prop_mod2 in H.
  unfold Z_comp.
*)


(** Some experiments: the next proof does not seem to have a constructive proof in the general setting of ARS. *)
Lemma Z_prop_fun {A}: forall (R: Rel A) (x : A -> A), ( forall(a b: A), R a b -> (refltrans R b (x a) /\ refltrans R (x a) (x b))) -> ( forall(a : A), refltrans R a (x a)).
Proof.
  intros R x HZ_prop a.
Admitted.

Lemma Z_prop_mon {A}: forall (R: Rel A) (x : A -> A), ( forall(a b: A), R a b -> (refltrans R b (x a) /\ refltrans R (x a) (x b))) -> forall u v : A, refltrans R u v -> refltrans R (x u) (x v).
Proof.
  intros R x H a b H0.
  induction H0.
  - apply refl.
  - apply H in H0.
    apply refltrans_composition with (x b).
    + apply H0.
    + assumption.
Qed.

Theorem Z_prop_implies_Confl' {A:Type}: forall R: Rel A, Z_prop R -> Confl R.
(* begin hide *)
Proof.
  intros R HZ_prop.
  unfold Z_prop in HZ_prop.
  destruct HZ_prop.
  unfold Confl.
  intros a b c Hrefl1.
  generalize dependent c.
  induction Hrefl1.
  - intros c Hrefl.
    exists c; split.
    + assumption.
    + apply refl.      
  - intros c' Hrefl2.
    inversion Hrefl2; subst.
    + exists c; split.
      * apply refl.
      * apply rtrans with b; assumption.
    + assert (H3 := IHHrefl1 (x c')).
      assert (H4 : refltrans R b (x c')).
      {
        apply refltrans_composition with (x b0).
        - apply refltrans_composition with (x a).
          + apply H; assumption.
          + apply H; assumption.
        - apply Z_prop_mon; assumption.
      }
      apply H3 in H4.
      destruct H4 as [d].
      exists d; split.
      * apply H4.
      * apply refltrans_composition with (x c').
        ** apply Z_prop_fun; assumption.
        ** apply H4.
Qed.

(** Proof using semi-confluence *)
Definition SemiConfl {A:Type} (R: Rel A) := forall a b c, R a b -> (refltrans R) a c -> (exists d, (refltrans R) b d /\ (refltrans R) c d).

Theorem Z_prop_implies_SemiConfl {A:Type}: forall R: Rel A, Z_prop R -> SemiConfl R.
Proof.
  intros R HZ_prop.
  unfold Z_prop in HZ_prop.
  unfold SemiConfl.
  destruct HZ_prop.
  intros a b c Hrefl Hrefl'.
  assert (Haxa: refltrans R a (x a)).
  {
   apply rtrans with b.
   - assumption.
   - apply H.
     assumption.
  }
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

(** Comparing regularity *)

Definition P_regular {A} (R: Rel A) :=
  forall (P:A -> Prop) t t', R t t' -> P t /\ P t'.

Definition P_wregular {A} (R: Rel A) :=
  forall (P:A -> Prop) t t', P t -> R t t' -> P t'.

Definition P_wregular' {A} (R: Rel A) :=
  forall (P:A -> Prop) t t', (P t /\ R t t') -> P t'.

Lemma P_wregular_equiv_P_wregular' {A}: forall (R: Rel A), P_wregular R <-> P_wregular' R.
Proof.
  intro R; split.
  - unfold P_wregular.
    unfold P_wregular'.
    intros Hwreg P t t' Hand.
    destruct Hand as [Ht Hred].
    apply Hwreg with t; assumption.
  - unfold P_wregular.
    unfold P_wregular'.
    intros Hwreg P t t' Ht Hred.
    apply Hwreg with t.
    split; assumption.
Qed.

Lemma P_wregular_imples_P_regular {A}: forall (R: Rel A), P_regular R -> P_wregular R.
Proof.
  intros R Hreg.
  unfold P_regular in Hreg.
  unfold P_wregular.
  intros P t t' Ht Hred.
  apply (Hreg P) in Hred.
  apply Hred.
Qed.

Definition tri_prop_elem {A} (a : A) (R: Rel A) :=
  exists a', forall b, R a b -> R b a'.

Definition tri_prop {A} (R: Rel A) :=
  forall a, tri_prop_elem a R.

Lemma tri_prop_imples_Z_prop {A}: forall R: Rel A, tri_prop R -> Z_prop R.
Proof.
  intros R Htri.
  unfold tri_prop in Htri.
  unfold tri_prop_elem in Htri.
  unfold Z_prop.
Admitted.
