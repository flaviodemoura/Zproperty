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
| transit: forall b a c,  red a b -> trans red b c -> trans red a c
.

Arguments transit {A} {red} _ _ _ _ _ .

Lemma trans_composition {A}:
  forall (R: Rel A) t u v, trans R t u -> trans R u v -> trans R t v
.
Proof.
  intros R t u v H1 H2. induction H1.
  - apply transit with b; assumption.
  - apply transit with b.
    + assumption.
    + apply IHtrans; assumption.
Qed.

Lemma transit' {A:Type}:
  forall (R: Rel A) t u v, trans R t u -> R u v -> trans R t v
.
Proof.
  intros R t u v H1 H2. induction H1.
  - apply transit with b. 
    + assumption.
    + apply singl.
      assumption.
  - apply IHtrans in H2.
    apply transit with b; assumption.
Qed.

Lemma trans_composition' {A}:
  forall (R: Rel A) t v, trans R t v -> (R t v \/ exists u, trans R t u /\ R u v).
Proof.
 intros R t v H.
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
| rtrans: forall a b c, R a b -> refltrans R b c -> refltrans R a c
.

Lemma refltrans_composition {A}:
  forall (R: Rel A) t u v, refltrans R t u -> refltrans R u v -> refltrans R t v
.
Proof.
  intros R t u v H1 H2. induction H1.
  - assumption.
  - apply rtrans with b.
    + assumption.
    + apply IHrefltrans; assumption.
Qed.

Lemma refltrans_composition' {A}:
    forall (R: Rel A) t u v, refltrans R t u -> R u v -> refltrans R t v.
Proof.
  intros R t u v H1 H2. induction H1.
  - apply rtrans with v.
    + assumption.
    + apply refl.
  - apply IHrefltrans in H2.
    apply rtrans with b.
    + assumption.
    + assumption.
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

Lemma CompReflTrans {A} (R: Rel A): forall a b c, refltrans R a b -> refltrans R b c -> refltrans R a c
.
Proof.
intros a b c H H0.
induction H.
- assumption.
- apply IHrefltrans in H0.
  apply rtrans with b; assumption.
Qed.
(* end hide *)  

Definition Zprop {A:Type} (R: Rel A) := exists wb:A -> A, forall a b, R a b -> ((refltrans R) b (wb a) /\ (refltrans R) (wb a) (wb b)).

Definition f_is_Z {A:Type} (R: Rel A) (f: A -> A) := forall a b, R a b -> ((refltrans R)  b (f a) /\ (refltrans R) (f a) (f b)). 

Lemma f_is_Z_implies_Zprop {A:Type}: forall (R: Rel A) (f:A -> A), f_is_Z R f -> Zprop R.
Proof.
  intros R f H.
  unfold Zprop.
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
  intros R.
Admitted.  
  
Definition comp {A} (f1 f2: A -> A) := fun x:A => f1 (f2 x).
Notation "f1 # f2" := (comp f1 f2) (at level 40).

Definition f_weak_Z {A} (R R': Rel A) (f: A -> A) := forall a b, R a b -> ((refltrans R')  b (f a) /\ (refltrans R') (f a) (f b)). 

Definition Z_comp {A:Type} (R :Rel A) := exists (R1 R2: Rel A) (f1 f2: A -> A), R = (R1 !_! R2) /\ f_is_Z R1 f1 /\ (forall a b, (refltrans R1) a b -> (refltrans R) (f2 a) (f2 b)) /\ (forall a b, b = f1 a -> (refltrans R) b (f2 b)) /\ (f_weak_Z R2 R (f2 # f1)).

Definition Z_comp' {A:Type} (R :Rel A) := exists (R1 R2: Rel A), R = (R1 !_! R2) -> forall (f1 f2: A -> A), f_is_Z R1 f1 /\ (forall a b, (refltrans R1) a b -> (refltrans R) (f2 a) (f2 b)) /\ (forall a b, b = f1 a -> (refltrans R) b (f2 b)) /\ (f_weak_Z R2 R (f2 # f1)).

Definition Z_comp'' {A:Type} (R R1 R2: Rel A) := R = (R1 !_! R2) -> forall (f1 f2: A -> A), f_is_Z R1 f1 /\ (forall a b, (refltrans R1) a b -> (refltrans R) (f2 a) (f2 b)) /\ (forall a b, b = f1 a -> (refltrans R) b (f2 b)) /\ (f_weak_Z R2 R (f2 # f1)).

Definition Z_comp_weak {A:Type} (R :Rel A) := exists (R1 R2: Rel A), R = (R1 !_! R2) -> forall (f1: A -> A), f_is_Z R1 f1 -> (forall a b, (refltrans R1) a b -> (refltrans R) (f1 a) (f1 b)) -> (f_weak_Z R2 R f1).

Definition Z_comp2 {A:Type} (R :Rel A) := forall (R1 R2: Rel A), R = (R1 !_! R2) -> exists (f : A -> A), f_is_Z R1 f /\ f_is_Z R2 f.

Lemma Z_comp2_implies_Zprop {A:Type}: forall (R :Rel A), Z_comp2 R -> Zprop R.
Proof.
  intros R HZcomp.
  unfold Z_comp2 in HZcomp.
  unfold Zprop.
  assert (H: R = R!_!R).
  {
    symmetry.
    apply union_idemp.
  }
  assert (H': exists f : A -> A, f_is_Z R f /\ f_is_Z R f).
  {
    apply HZcomp; assumption.
  }
  destruct H'.
  exists x.
  apply H0.
Qed.

Lemma Zprop_implies_Z_comp2 {A:Type}: forall (R :Rel A), Zprop R -> Z_comp2 R.
Proof.
  intros R HZprop.
  unfold Zprop in HZprop.
  inversion HZprop.
  unfold Z_comp2.
  intros R1 R2 Hunion.
  rewrite Hunion in H.
Admitted.  

  
Definition Z_comp2' {A:Type} (R R1 R2: Rel A) := forall (f : A -> A), R = (R1 !_! R2) -> f_is_Z R1 f /\ f_is_Z R2 f.

Lemma Z_comp2'_implies_Z_comp'' {A:Type}: forall (R R1 R2 :Rel A), Z_comp2' R R1 R2 -> Z_comp'' R R1 R2.
Proof.
  intros R R1 R2 HZ2.
  unfold Z_comp2' in HZ2.
  unfold Z_comp''.
  intro H.
  intros f1 f2. split.
  - assert (H': f_is_Z R1 f1 /\ f_is_Z R2 f1).
    {
      apply HZ2; assumption.
    }
    apply H'.
  - split.
    + intros a b Hrefl.
      assert (H': f_is_Z R1 f1 /\ f_is_Z R2 f1).
    {
      apply HZ2; assumption.
    }
Admitted.
    
  
Definition Z_comp3 {A:Type} (R :Rel A) := exists (R1 R2 R3: Rel A), R = ((R1 !_! R2) !_! R3) -> forall (f1 : A -> A), f_is_Z R1 f1 /\ f_is_Z R2 f1 /\ f_is_Z R3 f1.

Theorem comp_Z_implies_Z {A:Type}: forall (R R1 R2 :Rel A) (f1 f2: A -> A), R = (R1 !_! R2) -> f_is_Z R1 f1 -> (forall a b, (refltrans R1) a b -> (refltrans R) (f2 a) (f2 b)) -> (forall a b, b = f1 a -> (refltrans R) b (f2 b)) -> (f_weak_Z R2 R (f2 # f1)) -> f_is_Z R (f2 # f1).
Proof.
  intros.
  unfold f_is_Z in *.
  unfold f_weak_Z in H3.
  intros.
  split.
  - inversion H; subst.
    clear H5.
    destruct H4.
    + apply refltrans_composition with (f1 a).
      * apply H0 in H.
        destruct H.
        induction H.
        **  apply refl.
        **  apply rtrans with b.
            *** apply union_left.
                assumption.
            *** apply IHrefltrans.
                apply refltrans_composition with (f1 a0).
                **** assumption.
                **** apply H0.
                      assumption.
      * apply H2 with a. trivial.
    + apply H3 in H.
      apply H.
  - inversion H; subst.
    clear H5.
    destruct H4.
    + apply H1.
      apply H0.
      assumption.
    + apply H3 in H.
      apply H.
Qed.

Lemma Z_comp_implies_Z {A:Type}: forall (R :Rel A), Z_comp R -> Zprop R.
Proof.
  intros R H.
  unfold Z_comp in H.
  inversion H as [ R1 [ R2 [f1 [f2 [H0 [H1 [H2 [H3 H4]]]]]]]].
  apply f_is_Z_implies_Zprop with (f2 # f1).
  apply comp_Z_implies_Z with R1 R2; assumption.
Qed.

Lemma Z_implies_Z_comp {A:Type}: forall (R : Rel A), Zprop R -> Z_comp R.
Proof.
  intros R HZprop.
  unfold Zprop in HZprop.
  destruct HZprop.
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

Theorem Z_comp_equiv_Z {A:Type}: forall (R : Rel A), Zprop R <-> Z_comp R.
Proof.
  split.
  - apply Z_implies_Z_comp.
  - apply Z_comp_implies_Z.
Qed.

Lemma Z_comp_eq {A:Type}: forall (R R1 R2 :Rel A) (f1 f2: A -> A), R = (R1 !_! R2) -> (forall a b, R1 a b -> (f1 a) = (f1 b)) -> (forall a, (refltrans R1) a (f1 a)) -> (forall b a, a = f1 b -> (refltrans R) a (f2 a)) -> (f_weak_Z R2 R (f2 # f1)) -> f_is_Z R (f2 # f1).
Proof.
  intros R R1 R2 f1 f2 Hunion HR1eqf1 Haf1a HRf2 Hweak.  
  unfold f_is_Z.
  unfold f_weak_Z in Hweak.
  inversion Hunion; subst.
  clear H.
  intros a b Hab.
  split.
  - induction Hab.
    + apply HR1eqf1 in H.
      specialize (HRf2 a).
      specialize (HRf2 (f1 b)).
      apply refltrans_composition with (f1 b).
      * specialize (Haf1a b).
        induction Haf1a.
        ** apply refl.
        ** apply rtrans with b.
            *** apply union_left.
                assumption.
            *** apply IHHaf1a; assumption.
      * rewrite <- H in *.
        apply HRf2. reflexivity.
    + apply Hweak in H.
      apply H.
  - induction Hab.
    + apply HR1eqf1 in H.
      specialize (HRf2 a).
      specialize (HRf2 (f1 b)).
      apply refltrans_composition with (f1 b).
      * admit.
      * rewrite H in *.
        apply HRf2. reflexivity.
    + apply Hweak in H.
      apply H.
Admitted.

Theorem Z_comp_equiv_Z_comp_weak {A:Type}: forall (R : Rel A), Z_comp R <-> Z_comp_weak R.
Proof.
  unfold Z_comp.
  unfold Z_comp_weak.
  split.
  - intros.
    destruct H.
    destruct H.
    destruct H.
    destruct H.
    destruct H.
    destruct H0.
    destruct H1.
    destruct H2.
    exists x.
    exists x0.
    intros.
    admit.
  - intros.
    destruct H.
    destruct H.
    exists x.
    exists x0.
Admitted.

Require Import Morphisms.

Definition Zprop_mod {A:Type} (R eqA:Rel A) := Equivalence eqA ->  (exists wb:A -> A, forall a b, R a b -> ((refltrans R) b (wb a) /\ (refltrans R) (wb a) (wb b)) /\ (forall c d, eqA c d -> wb c = wb d)).


Corollary Z_comp_implies_Zprop_mod {A:Type}: forall (R eqA: Rel A), Z_comp R -> Zprop_mod R eqA.
Proof.
  intros R eqA Hcomp.
  unfold Z_comp in Hcomp.
  unfold Zprop_mod.
  intros Heq.
  destruct Hcomp as [R1 [R2 [f1 [f2 [Hunion [Hf1_is_Z [H1 H2]]]]]]].
  exists f2.
  intros a b Hred. split.
  - split.
    + admit.
    + admit.
  - Admitted.

(** Establish equivalence(?) between Z_comp and Zprop_mod *)
Theorem Z_comp_equiv_Z_mod {A: Type}: forall (R eqA: Rel A), Z_comp R <-> Zprop_mod R eqA.
Proof.
  unfold Z_comp.
  unfold Zprop_mod.
  split.
  - intros.
    destruct H.
    destruct H.
    destruct H.
    destruct H.
    destruct H.
    destruct H1.
    destruct H2.
    destruct H3.
    exists x2.
    intros.
    split.
    + inversion H; subst.
      unfold f_weak_Z in H4.
      admit.
    + intros.
      apply f_equal.
      admit.
  - intros.
Admitted.


Definition Confl {A:Type} (R: Rel A) := forall a b c, (refltrans R) a b -> (refltrans R) a c -> (exists d, (refltrans R) b d /\ (refltrans R) c d).


Theorem Zprop_implies_Confl {A:Type}: forall R: Rel A, Zprop R -> Confl R.
Proof.
  intros R HZprop.
  unfold Zprop in HZprop.
  destruct HZprop.
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
        ** apply CompReflTrans with (x a).
        *** assumption.
        *** apply H0.
    + intros b0 Hrefl1 IHHrefl1 Hb0xa.
      apply IHHrefl2 with b0.
      * apply CompReflTrans with (x a); apply H; assumption.
      * assumption.
      * assumption.
      * apply CompReflTrans with (x a).
        ** assumption.
        ** apply H.
           assumption.
Qed.

Corollary Z_comp_is_Confl {A}: forall (R: Rel A), Z_comp R -> Confl R.
Proof.
  intros R H.
  apply Z_comp_implies_Z in H.
  apply Zprop_implies_Confl; assumption.  
Qed.

(** Some experiments: the next proof does not seem to have a constructive proof in the general setting of ARS. *)
Lemma Zprop_fun {A}: forall (R: Rel A) (x : A -> A), ( forall(a b: A), R a b -> (refltrans R b (x a) /\ refltrans R (x a) (x b))) -> ( forall(a : A), refltrans R a (x a)).
Proof.
  intros R x HZprop a.
Admitted.

Lemma Zprop_mon {A}: forall (R: Rel A) (x : A -> A), ( forall(a b: A), R a b -> (refltrans R b (x a) /\ refltrans R (x a) (x b))) -> forall u v : A, refltrans R u v -> refltrans R (x u) (x v).
Proof.
  intros R x H a b H0.
  induction H0.
  - apply refl.
  - apply H in H0.
    apply refltrans_composition with (x b).
    + apply H0.
    + assumption.
Qed.

Theorem Zprop_implies_Confl' {A:Type}: forall R: Rel A, Zprop R -> Confl R.
(* begin hide *)
Proof.
  intros R HZprop.
  unfold Zprop in HZprop.
  destruct HZprop.
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
        - apply Zprop_mon; assumption.
      }
      apply H3 in H4.
      destruct H4 as [d].
      exists d; split.
      * apply H4.
      * apply refltrans_composition with (x c').
        ** apply Zprop_fun; assumption.
        ** apply H4.
Qed.

(** Proof using semi-confluence *)
Definition SemiConfl {A:Type} (R: Rel A) := forall a b c, R a b -> (refltrans R) a c -> (exists d, (refltrans R) b d /\ (refltrans R) c d).

Theorem Zprop_implies_SemiConfl {A:Type}: forall R: Rel A, Zprop R -> SemiConfl R.
Proof.
  intros R HZprop.
  unfold Zprop in HZprop.
  unfold SemiConfl.
  destruct HZprop.
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
    + apply CompReflTrans with (x a); apply H; assumption.
    + apply CompReflTrans with (x b).
      * apply CompReflTrans with (x a).
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
      ** apply CompReflTrans with x; assumption.
    * assumption.
Qed.


Definition CompZ {A:Type} (R R1 R2: Rel A) := exists w1 w2:A -> A, forall a b, R a b -> ((refltrans R) b (wb a) /\ (refltrans R) (wb a) (wb b)).


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

Lemma tri_imples_Z {A}: forall R: Rel A, tri_prop R -> Zprop R.
Proof.
  intros R Htri.
  unfold tri_prop in Htri.
  unfold tri_prop_elem in Htri.
  unfold Zprop.
  Admitted.