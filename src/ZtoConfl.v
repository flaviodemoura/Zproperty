Definition Rel (A:Type) := A -> A -> Prop.

Definition NF {A:Type} (a:A) (R: Rel A) := ~(exists b, R a b).

(* Transitive closure of a reduction relation *)
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
  
Definition Zprop {A:Type} (R: Rel A) := exists wb:A -> A, forall a b, R a b -> ((refltrans R) b (wb a) /\ (refltrans R) (wb a) (wb b))
.

Definition Confl {A:Type} (R: Rel A) :=
  forall a b c, (refltrans R) a b -> (refltrans R) a c -> (exists d, (refltrans R) b d /\ (refltrans R) c d)
.

Lemma CompReflTrans {A} (R: Rel A): forall a b c, refltrans R a b -> refltrans R b c -> refltrans R a c
.
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
      assumption.
      exists x0.
      split.
      * apply H0.
      * apply CompReflTrans with (x a).
        assumption.
        apply H0.
    + intros b0 Hrefl1 IHHrefl1 Hb0xa.
      assert (IHHrefl1': forall c0 : A,
           refltrans R b0 c0 ->
           exists d : A, refltrans R c d /\ refltrans R c0 d).
      {
        assumption. 
      }
      assert (Hb0xb : refltrans R b0 (x b)).
      {
        apply CompReflTrans with (x a).
        assumption.
        apply H.
        assumption.
      }
      destruct IHHrefl1 with (x b).
      * assumption.
      * apply IHHrefl2 with b0.
        ** apply CompReflTrans with (x a); apply H; assumption.
        ** assumption.
        ** destruct IHHrefl2 with b0.
          *** apply CompReflTrans with (x a); apply H; assumption.
          *** assumption.
          *** assumption.
          *** assumption.
          *** assumption.
        ** assumption. 
Qed.

