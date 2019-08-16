(** * Introduction *)

(**

    This work is about confluence of abstract rewriting systems, which
    is a model of computation based on the notion of
    reduction. Confluence of abstract rewriting systems is concerned
    about the decidability of the reduction relation. This property is
    undecidable in general.

    In ??, Oomstrom presents a property called Z, which turns out to be a sufficient condiction to get confluence. For a given abstract rewriting system [(A,\to)], one says that it satisfies the Z property if, forall [a,b \in A] there exists a function [f: A \to A] such that 

We present a formalisation ...

*)

(** * Z Property implies Confluence *)
(* begin hide *)
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

(* end hide *)  

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

Inductive union {A} (red1 red2: Rel A) : Rel A :=
 | union_left: forall a b,  red1 a b -> union red1 red2 a b
 | union_right: forall a b,  red2 a b -> union red1 red2 a b.

Notation "R1 !_! R2" := (union R1 R2) (at level 40).

Lemma union_idemp {A}: forall (R : Rel A), union R R = R.
Proof.
Admitted.  
  
Definition comp {A} (f1 f2: A -> A) := fun x:A => f1 (f2 x).
Notation "f1 # f2" := (comp f1 f2) (at level 40).

Definition f_is_weak_Z {A} (R R': Rel A) (f: A -> A) := forall a b, R a b -> ((refltrans R')  b (f a) /\ (refltrans R') (f a) (f b)). 

Definition Z_comp {A:Type} (R :Rel A) := exists (R1 R2: Rel A) (f1 f2: A -> A), R = (R1 !_! R2) /\ f_is_Z R1 f1 /\ (forall a b, (refltrans R1) a b -> (refltrans R) (f2 a) (f2 b)) /\ (forall a b, b = f1 a -> (refltrans R) b (f2 b)) /\ (f_is_weak_Z R2 R (f2 # f1)).

(*
Definition Z_comp {A:Type} (R1 R2 :Rel A) := exists (f1 f2: A -> A), f_is_Z R1 f1 /\ (forall a b, (refltrans R1) a b -> (refltrans (R1 !_! R2)) (f2 a) (f2 b)) /\ (forall a b, b = f1 a -> (refltrans (R1 !_! R2)) b (f2 b)) /\ (f_is_weak_Z R2 (R1 !_! R2) (f2 # f1)).

Definition Z_comp_new {A:Type} (R :Rel A) := forall (R1 R2: Rel A), R = (R1 !_! R2) -> exists (f1 f2: A -> A), f_is_Z R1 f1 /\ (forall a b, (refltrans R1) a b -> (refltrans R) (f2 a) (f2 b)) /\ (forall a b, b = f1 a -> (refltrans R) b (f2 b)) /\ (f_is_weak_Z R2 R (f2 # f1)).

Lemma Z_comp_implies_Z_comp_new {A: Type}: forall (R1 R2: Rel A), Z_comp R1 R2 <-> Z_comp_new (R1 !_! R2).
Proof.
  intros R1 R2; split.
  - intro HZ_comp.
    unfold Z_comp in HZ_comp.
    destruct HZ_comp as [f1 [f2 [Hf_is_Z [H1 [H2 H3]]]]].
    unfold Z_comp_new.
    intros R3 R4 Heq.
    admit.
  - intro HZ_comp_new.
    unfold Z_comp_new in HZ_comp_new.
    unfold Z_comp.
      apply HZ_comp_new.
      reflexivity.
Admitted.    
*)

Lemma Z_comp_implies_Z_prop {A:Type}: forall (R :Rel A), Z_comp R -> Z_prop R.
Proof.
  intros R H.
  unfold Z_comp in H.
  destruct H as [ R1 [ R2 [f1 [f2 [H0 [H1 [H2 [H3 H4]]]]]]]].
  apply f_is_Z_implies_Z_prop with (f2 # f1).
  unfold f_is_Z in *.
  unfold f_is_weak_Z in H4.
  intros.
  split.
  - inversion H0; subst.
    clear H5.
    destruct H.
    + apply refltrans_composition with (f1 a).
      * apply H1 in H.
        destruct H.
        induction H.
        **  apply refl.
        **  apply rtrans with b.
            *** apply union_left.
                assumption.
            *** apply IHrefltrans.
                apply refltrans_composition with (f1 a0).
                **** assumption.
                **** apply H1.
                     assumption.
      * apply H3 with a. trivial.
    + apply H4 in H.
      apply H.
  - inversion H0; subst.
    clear H5.
    destruct H.
    + apply H2.
      apply H1.
      assumption.
    + apply H4 in H.
      apply H.
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
        assumption.
      * split.
        ** intros a b Heq.
           apply refl.
        ** assumption.
Qed.

(*
Lemma Z_comp_new_implies_Z_prop {A:Type}: forall (R : Rel A), Z_comp_new R -> Z_prop R.
Proof.
  intros R HZ_comp_new.
  unfold Z_comp_new in HZ_comp_new.
  unfold Z_prop.

  
Lemma Z_comp_new_implies_Z_prop {A:Type}: forall (R R1 R2 :Rel A), R = R1 !_! R2 -> Z_comp_new R -> Z_prop R.
Proof.
  intros R R1 R2 Hunion HZ_comp_new.
  unfold Z_comp_new in HZ_comp_new.
  unfold Z_prop.
  assert (H: exists f1 f2 : A -> A,
                  f_is_Z R1 f1 /\
                  (forall a b : A, refltrans R1 a b -> refltrans R (f2 a) (f2 b)) /\
                  (forall a b : A, b = f1 a -> refltrans R b (f2 b)) /\ f_is_weak_Z R2 R (f2 # f1)).
  {
    apply HZ_comp_new.
    assumption.
  }
  clear HZ_comp_new.
  destruct H as [f1 [f2 [Hf_is_Z [H1 H2]]]].
  exists (f2 # f1).
  intros a b Hred; split.

  
  assert (Haux: forall R R1 R2 : Rel A, R = R1 !_! R2 -> Z_comp_new R -> Z_comp R).
  {
    unfold Z_comp_new.
    unfold Z_comp.
    intros R R1 R2 H H0.
    destruct H0 with R1 R2.
    - assumption.
    - exists R1.
      exists R2.
      exists x.
      destruct H1.
      exists x0.
      split; assumption.
  }
  intros R R1 R2 H H0.
  apply Z_comp_implies_Z_prop.
  apply Haux with R1 R2; assumption.
Qed.
 *)

Theorem Z_comp_equiv_Z_prop {A:Type}: forall (R : Rel A), Z_prop R <-> Z_comp R.
Proof.
  split.
  - apply Z_prop_implies_Z_comp.
  - apply Z_comp_implies_Z_prop.
Qed.

Definition Z_comp_eq {A:Type} (R :Rel A) := exists (R1 R2: Rel A) (f1 f2: A -> A), R = (R1 !_! R2) /\ (forall a b, R1 a b -> (f1 a) = (f1 b)) /\ (forall a, (refltrans R1) a (f1 a)) /\ (forall b a, a = f1 b -> (refltrans R) a (f2 a)) /\ (f_is_weak_Z R2 R (f2 # f1)).

Definition Z_comp_eq' {A:Type} (R :Rel A) := exists (R1 R2: Rel A) (f : A -> A), R = (R1 !_! R2) /\ (forall a b, R1 a b -> (f a) = (f b)) /\ (forall a, (refltrans R2) a (f a)) /\ (f_is_weak_Z R2 R f).

(*
Definition Z_comp_new_eq {A:Type} (R :Rel A) := forall (R1 R2: Rel A), R = (R1 !_! R2) -> exists (f1 f2: A -> A), (forall a b, R1 a b -> (f1 a) = (f1 b)) /\ (forall a, (refltrans R1) a (f1 a)) /\ (forall b a, a = f1 b -> (refltrans R) a (f2 a)) /\ (f_is_weak_Z R2 R (f2 # f1)).
 *)

Lemma Z_comp_eq_implies_Z_prop' {A:Type}: forall (R : Rel A), Z_comp_eq' R -> Z_prop R.
Proof.
Admitted.

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

Lemma Z_comp_eq_implies_Z_prop_mod3 {A:Type}: forall (R eqA: Rel A), Z_comp_eq R -> Z_prop_mod3 R eqA.
Proof.
  intros R eqA H.
  unfold Z_comp_eq in H.
  destruct H as [R1 [R2 [f1 [f2 [Hunion [Heq [H1 [H2 H3]]]]]]]].
  unfold Z_prop_mod3. split.
  Admitted.
  
Lemma Z_prop_mod3_implies_Z_comp_eq {A:Type}: forall (R eqA: Rel A), Z_prop_mod3 R eqA -> Z_comp_eq (eqA !_! R).
Proof.
  intros R eqA H.
  unfold Z_prop_mod3 in H.
  destruct H as [Heq H].  
  destruct H.
  unfold Z_comp_eq.
  exists eqA. exists R. exists x. exists x. split.
  - reflexivity.
  - split.
    + intros a b.
      assert (H' := H a b); clear H.
    +
      
  
  
Corollary Z_comp_new_implies_Z_prop_mod {A:Type}: forall (R R1 R2 : Rel A), R = R1 !_! R2 -> Z_comp_new R -> Z_prop_mod R.
Proof.
  intros R R1 R2 Hunion Hnew.
  unfold Z_comp_new in Hnew.
  apply Hnew in Hunion.
  clear Hnew.
  destruct Hunion as [f1 [f2 [H1 [H2 [H3 H4]]]]].
Admitted.

Lemma Z_prop_mod_implies_Z_comp_eq {A:Type}: forall (R: Rel A), Z_prop_mod R -> Z_comp_eq R.
Proof.
Admitted.

Lemma Z_prop_mod'_implies_Z_comp_new_eq {A:Type}: forall (R: Rel A), Z_prop_mod' R -> Z_comp_new_eq R.
Proof.
  intros R H.
  unfold Z_prop_mod' in H.
  destruct H as [eq [Heq [wb H]]].
  unfold Z_comp_new_eq.
  intros R1 R2 Hcomp.
  exists wb. 
Admitted.

Corollary Z_comp_implies_Z_prop_mod {A:Type}: forall (R : Rel A), Z_comp R -> Z_prop_mod R.
Proof.
  intros R Hcomp.
  unfold Z_comp in Hcomp.
  unfold Z_prop_mod.
  destruct Hcomp as [R1 [R2 [f1 [f2 [Hunion [Hf1_is_Z [H1 H2]]]]]]].
  exists R1.
  intros Heq.
  exists (f2 # f1). intros a b Hred; subst.
  inversion Hred; subst.
  - split.
    + clear Hred.
      split.
      * apply refltrans_composition with (f1 a).
        **  apply Hf1_is_Z in H.
            destruct H.
            induction H.
            *** apply refl.
            *** apply rtrans with b.
                ****  apply union_left.
                      assumption.
                ****  apply IHrefltrans.
                      apply refltrans_composition with (f1 a0).
                      ***** assumption.
                      ***** apply Hf1_is_Z.
                            assumption.
        ** apply H2 with a. trivial.
      * apply Hf1_is_Z in H.
        destruct H.
        apply H1 in H0; assumption.
    + intros c d HR1.
      apply f_equal.
      admit.
  - split.
    + apply H2 in H.
        apply H.
    + intros c d HR1.
      apply f_equal.
    admit.
Admitted.

Definition Confl {A:Type} (R: Rel A) := forall a b c, (refltrans R) a b -> (refltrans R) a c -> (exists d, (refltrans R) b d /\ (refltrans R) c d).

Theorem Z_prop_implies_Confl {A:Type}: forall R: Rel A, Z_prop R -> Confl R.
Proof.
  intros R HZ_prop.
  unfold Z_prop in HZ_prop.
  destruct HZ_prop.
  unfold Confl.
  intros a b c Hrefl1.
  generalize dependent c.
  induction Hrefl1.
  - intros c Hrefl.
    exists c. split.
    + assumption.
    + apply refl.
  - intros c1 Hrefl2.
    assert (Hbxa: refltrans R b (x a)).
    {
      apply H; assumption.
    }
    assert (Haxa: refltrans R a (x a)).
    {
      apply rtrans with b; assumption.
    }
    clear H0.
    generalize dependent b.
    induction Hrefl2.
    + intros b Hrefl1 IHHrefl1 Hbxa.
      destruct IHHrefl1 with (x a).
      * assumption.
      * exists x0.
        split.
        ** apply H0.
        ** apply refltrans_composition with (x a).
        *** assumption.
        *** apply H0.
    + intros b0 Hrefl1 IHHrefl1 Hb0xa.
      apply IHHrefl2 with b0.
      * apply refltrans_composition with (x a); apply H; assumption.
      * assumption.
      * assumption.
      * apply refltrans_composition with (x a).
        ** assumption.
        ** apply H.
           assumption.
Qed.

Corollary Z_comp_is_Confl {A}: forall (R: Rel A), Z_comp R -> Confl R.
Proof.
  intros R H.
  apply Z_comp_implies_Z_prop in H.
  apply Z_prop_implies_Confl; assumption.  
Qed.

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
