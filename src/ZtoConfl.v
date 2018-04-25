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
assumption.
apply IHrefltrans in H0.
apply rtrans with b.
assumption.
assumption.
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
    assert (Hreflto: refltrans R b (x a) -> refltrans R (x a) (x b)).
    {
      apply H in H0.
      intros.
      destruct H0.
      assumption.
    }
    assert (Hcons: refltrans R a (x b)).
    {
      apply CompReflTrans with (x a).
      - apply CompReflTrans with b.
        + apply rtrans with b.
          * assumption.
          * apply refl.
        + apply H in H0.
          destruct H0.
          assumption.
      - apply H.
        assumption.
    }
    assert (Hba1: refltrans R b (x a)).
    {
      apply H.
      assumption.
    }
    apply IHHrefl1 in Hba1.
    destruct Hba1.
    induction Hrefl2.
    exists c.
    split.
    apply refl.
    apply rtrans with b.
    assumption.
    assumption.
    assert (Hba2: refltrans R b0 (x a)).
    {
      apply H.
      assumption.
    }
    assert (Hba1: refltrans R b (x a)).
    {
      apply H.
      assumption.
    }
Admitted.


