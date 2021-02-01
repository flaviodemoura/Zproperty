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

(* begin hide *)
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

Definition Z_prop {A:Type} (R: Rel A) := exists f:A -> A, forall a b, R a b -> ((refltrans R) b (f a) /\ (refltrans R) (f a) (f b)).

Definition f_is_Z {A:Type} (R: Rel A) (f: A -> A) := forall a b, R a b -> ((refltrans R)  b (f a) /\ (refltrans R) (f a) (f b)). 

Theorem Z_prop_implies_Confl {A:Type}: forall R: Rel A, Z_prop R -> Confl R.
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

Theorem Z_comp_implies_Z_prop {A:Type}: forall (R :Rel A), Z_comp R -> Z_prop R.
Proof.
  intros R H. 
  unfold Z_prop. unfold Z_comp in H. destruct H as
  [ R1 [ R2 [f1 [f2 [Hunion [H1 [H2 [H3 H4]]]]]]]]. (** %\comm{Now
      unfold the definitions of $Z\_prop$ and $Z\_comp$ as presented
      before, and name the hypothesis of the compositional Z as in
      Theorem \ref{thm:zcomp}. We need to prove that there exists a
      map, say $f$, that is Z as shown by the current proof context:
      \newline

      \includegraphics[scale=0.4]{fig8.png} }% *)
  
  exists (f2 # f1). (** %\comm{We will prove that the composition $f_2 \circ f_1$
  is Z.}% *)
  
  intros a b HR. (** %\comm{Let $a$ and $b$ be elements of $A$, and suppose
  that $a$ $R$-reduces to $b$ in one step, i.e. that $a \to_R b$ and
  call $HR$ this hypothesis.}% *)
  
  inversion Hunion; subst.  clear H.  inversion HR; subst. (** %\comm{Since
  $R$ is the union of $R1$ and $R2$, one has that $a$ reduces to $b$
  in one step via either $R1$ or $R2$. Therefore, there are two cases
  to consider:}% *)

  - split. (** %\comm{Firstly, suppose that $a$ $R1$-reduces in one step to
    $b$, i.e. $a \to_{R1} b$.}% *)

    + apply refltrans_composition with (f1 a). (** %\comm{In order to prove
    that $b \tto_R (f_2 (f_1\ a))$, we first need to show that $b
    \tto_{R1} (f_1\ a)$, and then that $(f_1\ a) \tto_R (f_2 (f_1\ a))$ as
    shown in Figure \ref{fig:zcomp}.}% *)
      
      * apply H1 in H.  destruct H. apply refltrans_union; assumption. (**
    %\comm{The proof of $b \tto_{R1} (f_1\ a)$ is done from the fact that $f_1$
    is Z for $R1$.}% *)
 
      * apply H3 with a; reflexivity. (** %\comm{The proof that $(f_1\ a)
    \tto_R (f_2 (f_1\ a))$ is a direct consequence of the hypothesis
    $H3$.}% *)
        
    + apply H1 in H.  destruct H.  clear H HR.  unfold comp. (** %\comm{The
    proof that $(f_2 (f_1\ a))$ $R$-reduces to $(f_2 (f_1\ b))$ is
    more tricky. Initially, note that, since $a \to_{R1} b$ then we
    get that $(f_1\ a) \tto_{R1} (f_1\ b)$ by the Z property.}% *)
      
      induction H0. (** %\comm{Now, the goal can be obtained from $H2$ as
      long as $(f_1\ a) \to_{R1} (f_1\ b)$, but from the hypothesis
      $H0$ we have that $(f_1\ a) \tto_{R1} (f_1\ b)$. Therefore, we
      proceed by induction on $H0$.}% *)
      
      * apply refl. (** %\comm{The reflexive case is trivial because $a$ and
        $b$ are equal.}% *)
        
      * apply refltrans_composition
              
        with (f2 b0). (** %\comm{In the transitive case, we have that $(f_1\ a)$ $R1$-reduces to
        $(f_1\ b)$ in at least one step. The current proof context is
        as follows, up to renaming of variables:

        \includegraphics[scale=0.5]{fig9.png}

      Therefore, there exists some element $b0$ such that $a0\to_{R1}
      b0$ and $b0 \tto_{R1} c$ and we need to prove that $(f_2\ a0)
      \tto_{R1\cup R2} (f_2\ c)$. This can be done in two steps using
      the transitivity of [refltrans] taking $(f_2\ b0)$ as the
      intermediary term.}% *)
        
        ** apply H2; assumption. (** %\comm{The first subgoal is then $(f_2\
           a0)\tto_{(R1 \cup R2)} (f_2\ b0)$ that is proved by
           hypothesis $H2$.}% *)
           
        ** assumption. (** %\comm{And the second subgoal $(f_2\ b0) \tto_{(R1
           \cup R2)} (f_2\ c)$ is proved by the induction
           hypothesis.}% *)
           
  - apply H4; assumption. (** %\comm{Finally, when $a$ $R2$-reduces in one
    step to $b$ one concludes the proof using the assumption that
    $(f_2 \circ f_1)$ is weak Z.}% *)
    
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

(** Rewriting Systems with equations is another interesting and
    non-trivial topic %\cite{winkler89,terese03}%. The confluence of
    rewriting systems with an equivalence relation can also be proved
    by a variant of the compositional Z, known as Z property
    modulo%~\cite{AK12b}%.

    %\begin{theorem}\label{cor:zcomp} Let
     $(A,\to_R)$ be an ARS such that $\to_R = \to_1 \cup \to_2$. If
     there exist mappings $f_1,f_2: A \to A$ such that
     \begin{enumerate} \item $a \to_1 b$ implies $f_1(a) = f_1(b)$
     \item $a \tto_1 f_1(a), for all a$ \item $a \tto_R f_2(a)$ holds
     for any $a\in Im(f_1)$ \item $f_2 \circ f_1$ is weakly Z for
     $\to_2$ by $\to_R$ \end{enumerate} then $f_2 \circ f_1$ is Z for
     $(A,\to_R)$, and hence $(A,\to_R)$ is confluent. \end{theorem}%

    We define the predicate [Z_comp_eq] corresponding to the
    hypothesis of Theorem %\ref{cor:zcomp}%, and then we prove
    directly that if [Z_comp_eq] holds for a relation [R] then [Zprop
    R] also holds. This approach differs from
    %\cite{Nakazawa-Fujita2016}% that proves Theorem
    %\ref{cor:zcomp}%, which is a Corollary in %\cite{Nakazawa-Fujita2016}%, 
    directly from Theorem %\ref{thm:zcomp}% *)

Definition Z_comp_eq {A:Type} (R :Rel A) := exists (R1 R2: Rel A) (f1 f2: A -> A), R = (R1 !_! R2) /\ (forall a b, R1 a b -> (f1 a) = (f1 b)) /\ (forall a, (refltrans R1) a (f1 a)) /\ (forall b a, a = f1 b -> (refltrans R) a (f2 a)) /\ (f_is_weak_Z R2 R (f2 # f1)).
        
Lemma Z_comp_eq_implies_Z_prop {A:Type}: forall (R : Rel A), Z_comp_eq R -> Z_prop R.
Proof.
  intros R Heq.  unfold Z_comp_eq in Heq. (** %\comm{Let $R$ be a relation
  and suppose that $R$ satisfies the predicate $Z\_comp\_eq$.}% *)
  
  destruct Heq as [R1 [R2 [f1 [f2 [Hunion [H1 [H2 [H3 H4]]]]]]]]. (**
  %\comm{Call $Hi$ the $i$th hypothesis as in \ref{cor:zcomp}.}% *)
  
  unfold Z_prop.  exists (f2 # f1). (** %\comm{From the definition of the
  predicate $Z\_prop$, we need to find a map, say $f$ that is Z. Let
  $(f_2 \circ f_1)$ be such map.}%  *)
  
  intros a b Hab. (** %\comm{In order to prove that $(f_2 \circ f_1)$ is Z,
  let $a$ and $b$ be arbitrary elements of type $A$, and $Hab$ be the
  hypothesis that $a \to_{R} b$.}% *)
  
  inversion Hunion; subst; clear H.  inversion Hab; subst; clear Hab. (**
  %\comm{Since $a$ $R$-reduces in one step to $b$ and $R$ is the union of the
  relations $R1$ and $R2$ then we consider two cases:}% *)
  
  - unfold comp; split. (** %\comm{The first case is when $a \to_{R1}
    b$. This is equivalent to say that $f_2 \circ f_1$ is weak Z for
    $R1$ by $R1 \cup R2$.}% *)
    
    + apply refltrans_composition with (f1 b). (** %\comm{Therefore, we first
    prove that $b \tto_{(R1\cup R2)} (f_2 (f_1\ a))$, which can be
    reduced to $b \tto_{(R1\cup R2)} (f_1\ b)$ and $(f_1\ b)
    \tto_{(R1\cup R2)} (f_2 (f_1\ a))$ by the transitivity of
    $refltrans$.}% *)
      
      * apply refltrans_union.  apply H2. (** %\comm{From hypothesis $H2$, we
        know that $a \tto_{R1} (f_1\ a)$ for all $a$, and hence
        $a\tto_{(R1\cup R2)} (f_1\ a)$ and we conclude.}% *)
        
      * apply H1 in H.  rewrite H.  apply H3 with b; reflexivity. (**
        %\comm{The proof that $(f_1\ b)\tto_{(R1\cup R2)} (f_2 (f_1\ a))$ is
        exactly the hypothesis $H3$.}% *)

    + apply H1 in H.  rewrite H.  apply refl. (** %\comm{The proof that $(f_2
    (f_1\ a)) \tto_{(R1\cup R2)} (f_2 (f_1\ b))$ is done using the
    reflexivity of $refltrans$ because $(f_2 (f_1\ a)) = (f_2 (f_1\
    b))$ by hypothesis $H1$.}% *)
      
  - apply H4; assumption. (** %\comm{When $a \to_{R2} b$ then we are done by
    hypothesis $H4$.}% *)

Qed.

