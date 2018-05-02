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
    assert (HZprop: refltrans R b (x a)).
    {
      apply H; assumption.
    }
    assert (HZprop': refltrans R b (x a)).
    {
      assumption.
    }
    apply IHHrefl1 in HZprop'.
    inversion HZprop'.
    destruct H1 as [Hcx0 Hxax0].
    clear HZprop' IHHrefl1.
    assert (Hac: refltrans R a c).
    {
      apply rtrans with b; assumption.
    }
    assert (Hax0: refltrans R a x0).
    {
      apply CompReflTrans with c; assumption.
    }    
    clear H0 Hrefl1 HZprop Hcx0.
    generalize dependent c.
    induction Hrefl2.
    + intros c Hrefl. exists c. split.
      * apply refl.
      * assumption.
    + intros c' Hrefl.
      apply IHHrefl2.
      * apply CompReflTrans with (x a).
        ** apply H in H0.
Admitted.


