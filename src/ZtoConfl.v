Definition Rel (A:Type) := A -> A -> Prop.

Definition NF {A:Type} (a:A) (R: Rel A) := ~(exists b, R a b).

Inductive refltrans {A:Type} (R: Rel A) : A -> A -> Prop :=
| refl: forall a, (refltrans R) a a
| rtrans: forall a b c, R a b -> refltrans R b c -> refltrans R a c.

Definition Zprop {A:Type} (R: Rel A) := exists wb:A -> A, forall a b, R a b -> ((refltrans R) b (wb a) /\ (refltrans R) (wb a) (wb b)).

Definition Confl {A:Type} (R: Rel A) :=
  forall a b c, (refltrans R) a b -> (refltrans R) a c -> (exists d, (refltrans R) b d /\ (refltrans R) c d).

Lemma CompReflTrans {A} (R: Rel A): forall a b c, refltrans R a b -> refltrans R b c -> refltrans R a c.
Proof.
intros a b c H H0.
induction H.
- assumption.
- apply IHrefltrans in H0.
  apply rtrans with b; assumption.
Qed.
  
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
      apply H.
      assumption.
    }
    assert (Haxa: refltrans R a (x a)).
    {
      apply rtrans with b.
      assumption.
      apply Hbxa.
    }
    clear H0.
    generalize dependent b.
    induction Hrefl2.
    + intros.
      specialize (IHHrefl1 (x a)).
      destruct IHHrefl1.
      assumption.
      exists x0.
      split.
      * apply H0.
      * apply CompReflTrans with (x a).
        assumption.
        apply H0.
    + intros.
      assert (IHHrefl1': forall c0 : A,
           refltrans R b0 c0 ->
           exists d : A, refltrans R c d /\ refltrans R c0 d).
      {
        assumption.
      }
      specialize (IHHrefl1 (x b)).
      destruct IHHrefl1.
      apply CompReflTrans with (x a).
      assumption.
      apply H.
      assumption.
      apply IHHrefl2 with b0.
      * apply CompReflTrans with (x a).
          ** apply H.
             assumption.
          ** apply H.
             assumption.
      * assumption.
      * destruct IHHrefl2 with b0.
        ** apply CompReflTrans with (x a).
           *** apply H.
               assumption.
           *** apply H.
               assumption.
        ** assumption.
        ** assumption.
        ** apply CompReflTrans with (x a).
           *** assumption.
           *** apply H.
               assumption.
        ** apply IHHrefl1'.
      * apply CompReflTrans with (x a).
        ** assumption.
        ** apply H.
           assumption.
Qed.

