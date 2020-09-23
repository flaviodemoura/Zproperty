(** * The Z property implies Confluence

  An ARS, say $(A,R)$, is defined as a pair composed of a set $A$ and
  binary relation over this set $R:A\times A$. Let $a,b\in A$. We
  write $a\to_R b$ (or $R\ a\ b$ in Coq) to denote that $(a,b)\in R$,
  and we say that $a$ $R$-reduces to $b$ in one step. The reflexive
  transitive closure of a relation [R], written as $\tto_R$, is
  defined by the following inference rules: %\begin{mathpar}
  \inferrule*[Right={$(refl)$}]{~}{a \tto_R a} \and
  \inferrule*[Right={$(rtrans)$}]{a\to_R b \and b \tto_R c}{a \tto_R
  c} \end{mathpar}% %\noindent% where $a,b$ and $c$ are universally
  quantified variables as one makes explicit in the corresponding Coq
  definition: *)
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

(**
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
Qed. *)
(* end hide *)

Inductive refltrans {A:Type} (R: Rel A) : A -> A -> Prop :=
| refl: forall a, (refltrans R) a a
| rtrans: forall a b c, R a b -> refltrans R b c -> refltrans R a c.

(** The rules named ([refl]) and ([rtrans]) are called _constructors_
in the Coq definition. The first constructor, namely [refl], states
the reflexivity axiom for $\tto_R$, while [rtrans] extends the
reflexive transitive closure of [R], if one has at least a one-step
reduction. As a first example, let's have a look at the proof of
transitivity of $\tto_R$:

%\begin{lemma} Let $\to_R$ be a binary relation over a set $A$. For
all $t, u, v \in A$, if $t \tto_R u$ and $u \tto_R v$ then $t \tto_R
v$.  \end{lemma}%

 Despite its simplicity, the proof of this lemma will help us explain
the way in which we will relate English annotations with the proof
steps. Coq proofs are written between the reserved words [Proof] and
[Qed] (lines 1 and 9), and each proof command finishes with a
dot. Proofs can be structured with bullets (- in the first level, + in
the second level, * in the third level, ** in the fourth level, and so
on). The corresponding informal proof proceed as follows: The
corresponding lemma in Coq, named [refltrans_composition], is stated
as follows: *)

Lemma refltrans_composition {A} (R: Rel A): forall t u v, refltrans R t u -> refltrans R u v -> refltrans R t v.
Proof.  
  intros t u v. (** %\comm{Let $t,u,v$ be elements of $A$.}% *)
  
  intros H1 H2. (** %\comm{Let $H1$ (respectively, $H2$) be the hipothesis that $t \tto_R   u$ (respectively, $u \tto_R v$).}% *)
  
  induction H1. (** %\comm{The proof procceds by induction on the
    hipothesis $H1$. Therefore there is one case for each constructor
    of the reflexive transitive closure of $R$. The structure of the
    proof context determines the shape of the induction hypothesis,
    and this fact will be essential to understand the inductive proof
    of the next theorem.}% *)
  
  - assumption. (** %\comm{For the base case, which corresponds to the rule $refl$, $t$ and $u$ are the same element and hence the goal coincides with the hipothesis $H2$.}% *)
    
  - apply rtrans with b. (** %\comm{For the inductive case, $t \tto_R
    u$ is build from $t \to_R b$ and $b \tto_R u$, for some $b$, and
    as induction hipothesis one has that $b \tto_R v$. Therefore, one
    can prove that $t \tto_R v$ by applying the rule ($rtrans$) with
    $b$ as the intermediary term:

\begin{mathpar} \inferrule*[Right={$(rtrans)$}]{t\to_R b \and b \tto_R
  v}{t \tto_R v} \end{mathpar}

 We have then two subproofs:}% *)
    
    + assumption. (** %\comm{The proof that $t\to_R b$ is one of the hipothesis, and we are done.}% *)
      
    + apply IHrefltrans; assumption.  (** %\comm{The proof that
$b\tto_R v$ is obtained from the induction hipothesis, and this proof
can be better visualized by the corresponding deduction tree:

\begin{mathpar}
\inferrule*[Right={$MP$}]{
\inferrule*[Right={$IH$}]{~}{b\tto_R u \to b\tto_R v} \and
\inferrule*[Right={H2}]{~}{b\tto_R u}}{b\tto_R v}
\end{mathpar} }% *)
Qed. 
(* begin hide *)
(**
<<
1. Proof.  
2.  intros t u v.  
3.  intros H1 H2.  
4.  induction H1.
5.  - assumption.  
6.  - apply rtrans with b.  
7.  + assumption.  
8.  + apply IHrefltrans; assumption.  
9. Qed. 
>>

This work is not a Coq tutorial, but our idea is that it should
also be readable for those unfamiliar with the Coq proof Assistant. In
addition, this paper is built directly from a Coq proof script, which
means that we are forced to present the ideas and the results in a
more organized and systematic way that is not necessarily the more
pedagogical one. *)

(** %{\bf Proof}.%

    Let $t, u, v \in A$, i.e. they are elements of type [A], or
    elements of the set [A] (line 2). Call [H1] (resp. [H2]) the
    hypothesis that $t \tto_R u$ (resp. $u\tto_R v$) (line 3). The
    proof proceeds by induction on the hypothesis [H1] (line 4),
    i.e. by induction on $t \tto_R u$. The structure of the proof
    context determines the shape of the induction hypothesis, and this
    fact will be essential to understand the inductive proof of the
    next theorem. As shown in Figure %\ref{fig:trans}%, [H1] and [H2]
    are the only hypothesis (the other lines are just declaration of
    variables), therefore the induction hypothesis subsumes [H2].

      %\begin{figure}[h] \centering
        \includegraphics[scale=0.6]{fig1.png} \caption{Transitivity of
        $\tto_R$}\label{fig:trans} \end{figure}%

    The first case is when $t \tto_R u$ is generated by the
    constructor [refl], which is an axiom and hence we are done (line
    5).  The second case, i.e. the recursive case is more interesting
    because $t \tto_R u$ is now generated by [rtrans] (line 6). This
    means that there exists an element, say $b$, such that $t \to_R b$
    and $b \tto_R u$. Therefore, in order to prove that $t \tto_R u$,
    we can apply the rule [rtrans] taking [b] as the intermediary
    term. The proof of the recursive case can be better visualized by
    the corresponding deduction tree: %{\scriptsize \begin{mathpar}
    \inferrule*[Right=MP]{\inferrule*[Right=MP]{\inferrule*[Right={
    $rtrans$}]{~}{\inferrule*[Right={$(\forall_e)$}]{\forall x\ y\ z,
    x\to_R y \to y\tto_R z \to x\tto_R z}{t\to_R b \to b\tto_R u \to
    t\tto_R u}} \and \inferrule*[Right={H}]{~}{t\to_R b}}{ b\tto_R u
    \to t\tto_R u} \and \inferrule*[Right=MP]{\inferrule*[Right={
    $IH$}]{~}{u\tto_R v \to b\tto_R u} \and
    \inferrule*[Right={H2}]{~}{u\tto_R v}}{b\tto_R u}}{t\tto_R u}
    \end{mathpar}}%

    Each branch of the above tree corresponds to a new goal in the Coq
    proof. Therefore, we have two subcases (or subgoals) to prove: In
    this subgoal we need to prove that $t \to_R b$, which we have as
    hypothesis (line 7). In the second subgoal (line 8), we need to
    prove that $b \tto_R u$. To do so, we apply the induction
    hypothesis [IHrefltrans]: $u \tto_R v \to b \tto_R u$, where
    $u\tto_R v$ is the hypothesis [H2]. $\hfill\Box$ *)
(* end hide *)

(** This example is interesting because it shows how Coq works, how
each command line (also known as tactics or tacticals depending on its
structure) corresponds, in general, to several steps of natural
deduction rules. *)

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
(* end hide *)

(** The reflexive transitive closure of a relation is used to define
    the notion of confluence: no matter how the reduction is done, the
    result will always be the same. In other words, every divergence
    is joinable as stated by the following diagram:

    $\centerline{\xymatrix{ & a \ar@{->>}[dl] \ar@{->>}[dr] & \\ b
    \ar@{.>>}[dr] & & c \ar@{.>>}[dl] \\ & d & }}$


    Formally, this means that if an expression $a$ can be reduced in
    two different ways to the expressions $b$ and $c$, then there
    exists an expression $d$ such that both $b$ and $c$ reduce to
    $d$. The existential quantification is expressed by the dotted
    lines in the diagram. This notion is defined in the Coq system as
    follows: *)

Definition Confl {A:Type} (R: Rel A) := forall a b c, (refltrans R) a b -> (refltrans R) a c -> (exists d, (refltrans R) b d /\ (refltrans R) c d).

(** In %\cite{dehornoy2008z}%, V. van Oostrom gives a sufficient
    condition for an ARS to be confluent, known as the _Z Property_:

    %\begin{definition} Let $(A,\to_R)$ be an ARS. Then $(A,\to_R)$
      has the Z property, if there exists a map $f:A \to A$ such that
      the following diagram holds:
    
      \[ \xymatrix{ a \ar[r]_R & b \ar@{.>>}[dl]^R\\ f(a)
      \ar@{.>>}[r]_R & f(b) \\ } \] \end{definition}%

The corresponding Coq definition is given as: *)

Definition Z_prop {A:Type} (R: Rel A) := exists f:A -> A, forall a b, R a b -> ((refltrans R) b (f a) /\ (refltrans R) (f a) (f b)).

(** Alternatively, for a given function [f], one can say that [f] satisfies the Z property, or that [f] is Z, if the above conditions hold for [f]: *)

Definition f_is_Z {A:Type} (R: Rel A) (f: A -> A) := forall a b, R a b -> ((refltrans R)  b (f a) /\ (refltrans R) (f a) (f b)). 

(** The first contribution of this work is a constructive proof of the
    fact that the Z property implies confluence. Our proof uses nested
    induction, and hence it differs from the one in %\cite{kes09}%
    (that follows %\cite{dehornoy2008z}%) and the one in %\cite{zproperty}% 
    in the sense that it does not rely on analyzing whether 
    a term is in normal form or not, avoiding necessity of 
    the law of the excluded middle . As a result, we have 
    an elegant inductive proof of the fact that if a binary relation
    has the Z property then it is confluent. In addition, we
    formalized this proof in the Coq proof assistant. In
    %\cite{zproperty}%, B. Felgenhauer et.al. formalized in Isabelle/HOL 
    the Z property and its relation to confluence. 
    In what follows, we present the theorem
    and its proof interleaving Coq code and the corresponding
    comments. *)

Theorem Z_prop_implies_Confl {A:Type}: forall R: Rel A, Z_prop R -> Confl R.
Proof.
  intros R HZ_prop. (** Let [R] be a relation over [A] that satisfies
    the Z property, which will be denoted by [HZ_prop] for future
    reference. *)

  unfold Z_prop, Confl in *. (** Unfolding both definitions of
  [Z_prop] and [Confl], we get the following proof context:

     % \includegraphics[scale=0.6]{fig3.png}% *)

  intros a b c Hrefl1 Hrefl2. (** Let [a, b] and [c] be elements of
     the set [A], [Hrefl1] the hypothesis that $a \tto_R b$, and
     [Hrefl2] the hypothesis that $a\tto_R c$. We need to prove that
     there exists [d] such that $b\tto_R d$ and $c\tto_R d$ *)
  
  destruct HZ_prop as [g HZ_prop]. (** We know from the hypothesis
     [HZ_prop] that there exists a mapping [f] that is Z. Let's call
     [g] this mapping, and we get following proof context:

      %\includegraphics[scale=0.6]{fig4.png}%

      The proof proceeds by nested induction, firstly on the length of
      the reduction from [a] to [b], and then on the length of the
      reduction from [a] to [c]. *)
  
  generalize dependent c. (** Before the first induction,
      i.e. induction on [Hrefl1], the element [c] needs to be
      generalized so that it can be afterwards instantiated with any
      reduct of [a]. *)
  
  induction Hrefl1. (** The induction on [Hrefl1] corresponds to
       induction on the reflexive transitive closure of the relation
       [R], and since [refltrans] has two rules, the goal splits in
       two subgoals, one for each possible way of constructing $a
       \tto_R b$. *)
  
  - intros c Hrefl2. (** In the first case, we have that $b = a$ since
    we are in the reflexive case. This means that we have to prove
    that there exists [d], such that $a \tto_R d$ and $c \tto_R d$. *)
    
    exists c; split. (** Taking [d] as [c], the proof is simplified to $a
    \tto_R c$ and $c \tto_R c$. *)

    + assumption. (** The first component is exactly the hypothesis
        [Hrefl2] and, *) 

    + apply refl. (** $c \tto_R c$ corresponds to an application of
        the [refl] axiom. %\newline%

        The interesting part of the proof is then given by the
        inductive case, i.e. when $a\tto_R b$ is generated by the rule
        [(rtrans)]. In this case, the reduction from [a] to [b] is
        done in at least one step, therefore there must exists an
        element $a'$ such that the following diagram holds.

        % \[\xymatrix{ & & a \ar@{->}[dl] \ar@{->>}[dr] & \\ & a'
        \ar@{->>}[dl] & & c \ar@{.>>}[ddll] \\ b \ar@{.>>}[dr] & & &
        \\ & d & & }\] %

        (* The corresponding proof context is as follows:

        %\includegraphics[scale=0.6]{fig5.png}% *)

        The induction hypothesis states that every divergence from
        $a'$ that reduces to $b$ from one side converges: [IHHrefl1]
        : $\forall c_0 : A, a'\tto_R c_0 \to (\exists d : A, b\tto_R d
        \land c_0\tto_R d$). Now, we'd like apply induction on the
        hypothesis [Hrefl2] (a\tto_R c), but the current proof context has the
        hypothesis [H]: $a\to_R a'$ ([a] reduces to [a'] in one step),
        and hence it is the sole hypothesis depending on [a] in the
        current proof context. If we were to apply induction on [Hrefl2] now, 
        the generated induction hypothesis [IHrefl2] would assume that there is 
        a term $a''$ such that $a \to_R a'' \tto_R c$ and would require that 
        $a'' \to_R a'$, which is generally false. In order to circumvent 
        this problem, we need to discard the hypothesis [H] from our proof 
        context, and replace it by another relevant information derived from 
        the Z property as shown in what follows. *)

  - intros c0 Hrefl2. (** Let $c_0$ be a reduct of $a$, and [Hrefl2]
    be the hypothesis $a \tto_R c_0$. So the reduction $a\tto_R c$ in
    the above diagram is now $a\tto_R c_0$ due to a renaming of
    variables automatically done by the Coq system. In addition, the
    reduction $a \to_R a' \tto_R b$ is now $a\to_R b \tto_R c$, as
    shown below:

    %\includegraphics[scale=0.6]{fig5-1.png}%

    Before applying induction to [Hrefl2]: $a \tto_R c_0$, we will derive 
    $b\tto_R (g\ a)$ and $a\tto_R (g\ a)$ from the proof context so we can
    discard the hypothesis [H]: $a\to_R. *)

    assert (Hbga: refltrans R b (g a)).
    { apply HZ_prop; assumption.  } (** We call [Hbga] the reduction
    $b\tto_R (g\ a)$ that is directly obtained from the Z property. *)

    assert (Haga: refltrans R a (g a)).
    { apply rtrans with b; assumption.  } (** Call [Haga] the
        reduction $a\tto_R (g\ a)$, and prove it using the
        transitivity of $\tto_R$, since $a \to_R b$ and $b \tto_R (g\
        a)$.

        Diagrammatically, we change from the situation on the left to
        the one on the right:

        %\begin{tabular}{c@{\hskip 0.5cm}c} $\xymatrix{ & & a
        \ar@{->>}[ddrr]_R \ar@{->}[dl]^R & & \\ & b \ar@{->>}[dl]^R &
        & & \\ c \ar@{.>>}[ddrr]_R & & & & c_0 \ar@{.>>}[ddll]^R \\ &
        & & & \\ & & d & & }$ & $\xymatrix{ & & a \ar@{->>}[ddrr]_R
        \ar@{->>}[dd]_R & & \\ & b \ar@{->>}[dl]^R \ar@{->>}[dr]_R & &
        & \\ c \ar@{.>>}[ddrr]_R & & (g \; a) & & c_0
        \ar@{.>>}[ddll]^R \\ & & & & \\ & & d & & }$ \end{tabular}% *) 

    clear H. generalize dependent b. (** At this point we can remove
      the hypothesis [H] from the context, and generalize [b]. Doing so, 
      we generalize [IHHrefl1], which, in conjunction with the hypotheses 
      that depend on a (namely, [Hrefl2], [Hbga], and [Haga]), will form 
      the four necessary conditions for use of the second inductive 
      hypothesis, [IHHrefl2]*)

    induction Hrefl2. (** Now we are ready to start the induction on
    the reduction $a\tto_R c_0$, and we have two subgoals. *)
    
    + intros b Hrefl1 IHHrefl1 Hbga. (** The first subgoal corresponds
        to the reflexive case that is closed by the induction
        hypothesis [IHHrefl1]:

        %\[\xymatrix{ & & a \ar@{->>}[dd]^{H2} & & \\ & b
        \ar@{->>}[dl]_{Hrefl1} \ar@{->>}[dr]^{H1} & & & \\ c
        \ar@{.>>}[dr] & IHHrefl1 & (g \; a) \ar@{.>>}[dl] & & \\ & d &
        &&}\]% *)
      
      assert (IHHrefl1_ga := IHHrefl1 (g a)); apply IHHrefl1_ga in Hbga. (**
      In order to apply [IHHrefl1], we instantiate $c_0$ with $(g\
      a)$. *)
      
      destruct Hbga. (** Therefore, there exists an element, say $x$,
      such that both $c\tto_R x$ and $(g\ a) \tto_R x$. *)
      
      exists x; split. (** We then take $x$ to show that $c\tto_R x$ and $a
      \tto_R x$. *)
      
      * apply H. (** Note that $c\tto_R x$ is already an hypothesis,
        and we are done. *)
        
      * apply refltrans_composition with (g a); [assumption | apply H]. (**
      The proof of $a \tto_R x$ is done by the transitivity of
      $\tto_R$ taking $(g\ a)$ as the intermediate step. *)
           
    + intros b0 Hrefl1 IHHrefl1 Hb0ga. (** The second subgoal corresponds
        to the case in which $a\tto_R c_0$ is generated by the rule
        $(rtrans)$. Therefore, there exists a term $b$ such that
        $a\to_R b$ and $b \tto_R c_0$. The corresponding proof context
        after introducing the universally quantified variable [b0],
        the hypothesis [Hrefl1] and the induction hypothesis
        [IHHrefl1] generated by the first outer induction and the fact
        that $b0 \tto_R (g\ a)$ is given by:

        %\includegraphics[scale=0.6]{fig7.png}% *)

      apply IHHrefl2 with b0. (** The second goal, i.e. the inductive case is 
      the consequent on IHHrefl2, so we can apply IHHrefl2 to prove it. Doing so, 
      we must prove the antecedent of IHHrefl2, which consists of four separate 
      hypotheses that we must prove. Those hypotheses are as follows: *)
      
      * apply refltrans_composition with (g a); apply HZ_prop; assumption. (**
      %1. $b \tto_R (g\ b)$: This is proved by the transitivity of the
      reflexive transitive closure of \coqdocvar{R} using the
      hypothesis (H: $a\to_R b$) and \coqdocvar{HZ\_prop}: $\forall a\
      b: a \to_R b \to (b \tto_R (g\ a) \land (g\ a) \tto_R (g\ b))$. *)
        
      * assumption. (** %2. $b0 \tto_R c$: This is exactly the
          hypothesis \coqdocvar{Hrefl1}%. *)

      * assumption. (** %3. $\forall c0: b0 \tto_R c0 \to (\exists d:
            c \tto_R d \land c0 \tto_R d)$: This is exactly the
            induction hypothesis \coqdocvar{IHHrefl1}.% *)

      * apply refltrans_composition with (g a); [ assumption | apply HZ_prop; assumption]. (**
      %4. $b0 \tto_R (g\ b)$: This is proved by the transitivity of
      the reflexive transitive closure of \coqdocvar{R} using the
      hypothesis (\coqdocvar{H'}: $b0 \tto_R (g\ a)$ and the fact that
      $(g\ a) \tto_R (g\ b)$ that is obtained from the fact that
      \coqdocvar{R} satisfies the Z property (hypothesis
      \coqdocvar{HZ\_prop}).% *)
        
Qed.

(** Another proof *)

Lemma refltrans_f_is_Z_refltrans {A:Type}: forall (R: Rel A) a b f, f_is_Z R f -> (refltrans R) a b -> (refltrans R) (f a) (f b).
Proof.
  intros R a b f H Hab.
  unfold f_is_Z in H.
  induction Hab.
  - apply refl.
  - apply H in H0.
    destruct H0 as [H1 H2].
    apply refltrans_composition with (f b); assumption.
Qed.

Lemma refltrans_f_is_Z {A:Type}: forall (R: Rel A) a f, f_is_Z R f -> (refltrans R) a (f a).
Proof.
  intros R a f H.
  unfold f_is_Z in H.
Admitted.

  Theorem Z_prop_implies_Confl2 {A:Type}: forall R: Rel A, Z_prop R -> Confl R.
  Proof.
    intros R H.
    unfold Z_prop in H.
    destruct H as [g H].
    unfold Confl.
    intros a b c H1 H2.
    generalize dependent c.
    induction H1.
    - intros c H1.
      exists c; split.
      + assumption.
      + apply refl.
    - intros c0 H2.
      apply H in H0.
      destruct H0 as [Hga Hgb].
      assert (refltrans R (g a) (g c0)).
      {
        apply  refltrans_f_is_Z_refltrans.
        - assumption.
        - assumption.
      }
      assert (refltrans R c0 (g c0)).
      {
        apply refltrans_f_is_Z; assumption.
      }
      assert (refltrans R b (g c0)).
      {
        apply refltrans_composition with (g a); assumption.
      }
      apply IHrefltrans in H4.
      destruct H4 as [d [H4 H5]].
      exists d; split.
      +  assumption.
      + apply refltrans_composition with (g c0); assumption.     
Qed.
      
(** An alternative proof that Z implies confluence is possible via the
    notion of semiconfluence, which is equivalent to confluence, as
    done in %\cite{zproperty}%. Unlike the proof in %\cite{zproperty}% and 
    similarly to our previous proof, our proof of the Theorem that 
    Z implies semiconfluence is constructive, but we
    will not explain it here due to lack of space; any
    interested reader can find it in the Coq file in our GitHub
    repository. *)
  
Definition SemiConfl {A:Type} (R: Rel A) := forall a b c, R a b -> (refltrans R) a c -> (exists d, (refltrans R) b d /\ (refltrans R) c d).

Theorem Z_prop_implies_SemiConfl {A:Type}: forall R: Rel A, Z_prop R -> SemiConfl R.
(* begin hide *)
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
(* end hide *)

Theorem Semi_equiv_Confl {A: Type}: forall R: Rel A, Confl R <-> SemiConfl R.
(* begin hide *)
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
(* end hide *)

Corollary Zprop_implies_Confl_via_SemiConfl {A:Type}: forall R: Rel A, Z_prop R -> Confl R.
Proof.
  intros R HZ_prop.
  apply Semi_equiv_Confl.
  generalize dependent HZ_prop.
  apply Z_prop_implies_SemiConfl.
Qed.

(** * An extension of the Z property: Compositional Z

    In this section we present a formalization of an extension of the
    Z property with compositional functions, known as _Compositional
    Z_, as presented in %\cite{Nakazawa-Fujita2016}%. The
    compositional Z is an interesting property because it allows a
    kind of modular approach to the Z property in such a way that the
    reduction relation can be split into two parts. More precisely,
    given an ARS $(A,\to_R)$, one must be able to decompose the
    relation $\to_R$ into two parts, say $\to_1$ and $\to_2$ such that
    $\to_R = \to_1\cup \to_2$. This kind of decomposition can be done
    in several interesting situations such as the $\lambda$-calculus
    with $\beta\eta$-reduction%\cite{Ba84}%, extensions of the
    $\lambda$-calculus with explicit substitutions%\cite{accl91}%, the
    $\lambda\mu$-calculus%\cite{Parigot92}%, etc. But before
    presenting the full definition of the Compositional Z, we need
    to define the _weak Z property_:

    %\begin{figure}[h] \centering \[ \xymatrix{ a \ar[r]_R & b
        \ar@{.>>}[dl]^x\\ f(a) \ar@{.>>}[r]_x & f(b) \\ } \]
        \caption{The weak Z property}\label{fig:weakZ} \end{figure}%
    
    %\begin{definition} Let $(A,\to_R)$ be an ARS and $\to_R'$ a
     relation on $A$. A mapping $f$ satisfies the {\it weak Z
     property} for $\to_R$ by $\to_R'$ if $a\to_R b$ implies $b \tto_R'
     f(a)$ and $f(a) \tto_R' f(b)$ (cf. Figure
     \ref{fig:weakZ}). Therefore, a mapping $f$ satisfies the Z
     property for $\to_R$ if it satisfies the weak Z property by
     itself.  \end{definition}%

    When $f$ satisfies the weak Z property, we also say that $f$ is
    weakly Z, and the corresponding definition in Coq is given as
    follows: *)

Definition f_is_weak_Z {A} (R R': Rel A) (f: A -> A) := forall a b, R a b -> ((refltrans R') b (f a) /\ (refltrans R') (f a) (f b)).

(** The compositional Z is an extension of the Z property for
compositional functions, where composition is defined as usual: *)

Definition comp {A} (f1 f2: A -> A) := fun x:A => f1 (f2 x).
Notation "f1 # f2" := (comp f1 f2) (at level 40).

(** %\noindent% and the disjoint union is inductively defined as: *)

Inductive union {A} (red1 red2: Rel A) : Rel A :=
| union_left: forall a b, red1 a b -> union red1 red2 a b
| union_right: forall a b, red2 a b -> union red1 red2 a b.
Notation "R1 !_! R2" := (union R1 R2) (at level 40).

(* begin hide *)
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
(* end hide *)

(** We are now ready to present the definition of the compositional Z:

    %\begin{theorem}\cite{Nakazawa-Fujita2016}\label{thm:zcomp} Let
     $(A,\to_R)$ be an ARS such that $\to_R = \to_1 \cup \to_2$. If
     there exists mappings $f_1,f_2: A \to A$ such that
     \begin{enumerate} \item $f_1$ is Z for $\to_1$ \item $a \to_1 b$
     implies $f_2(a) \tto f_2(b)$ \item $a \tto f_2(a)$ holds for any
     $a\in Im(f_1)$ \item $f_2 \circ f_1$ is weakly Z for $\to_2$ by
     $\to_R$ \end{enumerate} then $f_2 \circ f_1$ is Z for
     $(A,\to_R)$, and hence $(A,\to_R)$ is confluent.  \end{theorem}%

    We define the predicate [Z_comp] that corresponds to the premises
    of Theorem %\ref{thm:zcomp}%, i.e. to the conjunction of items
    (i), (ii), (iii) and (iv) in addition to the fact that $\to_R =
    \to_1 \cup \to_2$, where $\to_1$ (resp. $\to_2$) is written as
    [R1] (resp. [R2]): *)

Definition Z_comp {A:Type} (R :Rel A) := exists (R1 R2: Rel A) (f1 f2: A -> A), R = (R1 !_! R2) /\ f_is_Z R1 f1 /\ (forall a b, R1 a b -> (refltrans R) (f2 a) (f2 b)) /\ (forall a b, b = f1 a -> (refltrans R) b (f2 b)) /\ (f_is_weak_Z R2 R (f2 # f1)).

(* begin hide *)
Lemma refltrans_union {A:Type}: forall (R R' :Rel A) (a b: A), refltrans R a b -> refltrans (R !_! R') a b.
Proof.
  intros R R' a b Hrefl.
  induction Hrefl.
  - apply refl.
  - apply rtrans with b.
    + apply union_left; assumption.
    + assumption.
Qed.
(* end hide *)

(** As stated by Theorem %\ref{thm:zcomp}%, the compositional Z gives
    a sufficient condition for compositional functions to be Z. In
    other words, compositional Z implies Z, which is justified by the
    diagrams of Figure %\ref{fig:zcomp}%.
 
    %\begin{figure}[h]\begin{tabular}{l@{\hskip 3cm}l} $\xymatrix{ a
    \ar@{->}[rr]^1 && b \ar@{.>>}[dll]_1\\ f_1(a)\ar@{.>>}[d]
    \ar@{.>>}[rr]^1 && f_1(b) \\ f_2(f_1(a)) \ar@{.>>}[rr] &&
    f_2(f_1(b)) }$ & $\xymatrix{ a \ar@{->}[rr]^2 && b
    \ar@{.>>}[ddll]\\ & & \\ f_2(f_1(a)) \ar@{.>>}[rr] && f_2(f_1(b))
    }$ \end{tabular}\caption{Compositional Z implies
    Z}\label{fig:zcomp}\end{figure}%
  
    In what follows, we present our commented Coq proof of this fact:
    *)

Theorem Z_comp_implies_Z_prop {A:Type}: forall (R :Rel A), Z_comp R -> Z_prop R.
Proof.
  intros R H. (** Let [R] be a relation over [A], and [H] the
      hypothesis that [R] satisfies the compositional Z. *)

  unfold Z_prop.  unfold Z_comp in H.  destruct H as [ R1 [ R2 [f1 [f2 [Hunion [H1 [H2 [H3 H4]]]]]]]]. (**
      Now unfold the definitions of [Z_prop] and [Z_comp] as presented
      before, and name the hypothesis of the compositional Z as in
      Theorem %\ref{thm:zcomp}%. We need to prove that there exists a
      map, say [f], that is Z as shown by the current proof context:
      %\newline%

      %\includegraphics[scale=0.6]{fig8.png}% *)
  
  exists (f2 # f1). (** We will prove that the composition $f_2 \circ f_1$
  is Z. *)
  
  intros a b HR. (** Let [a] and [b] be elements of [A], and suppose
  that [a] [R]-reduces to [b] in one step, i.e. that $a \to_R b$ and
  call [HR] this hypothesis. *)
  
  inversion Hunion; subst.  clear H.  inversion HR; subst. (** Since
  [R] is the union of [R1] and [R2], one has that [a] reduces to [b]
  in one step via either [R1] or [R2]. Therefore, there are two cases
  to consider: *)

  - split. (** Firstly, suppose that [a] [R1]-reduces in one step to
    [b], i.e. $a \to_{R1} b$. *)

    + apply refltrans_composition with (f1 a). (** In order to prove
    that $b \tto_R (f_2 (f_1\ a))$, we first need to show that $b
    \tto_{R1} (f_1\ a)$, and then that $(f_1\ a) \tto_R (f_2 (f_1\ a))$ as
    shown in Figure %\ref{fig:zcomp}%. *)
      
      * apply H1 in H.  destruct H. apply refltrans_union; assumption. (**
    The proof of $b \tto_{R1} (f_1\ a)$ is done from the fact that $f_1$
    is Z for [R1]. *)
 
      * apply H3 with a; reflexivity. (** The proof that $(f_1\ a)
    \tto_R (f_2 (f_1\ a))$ is a direct consequence of the hypothesis
    [H3]. *)
        
    + apply H1 in H.  destruct H.  clear H HR.  unfold comp. (** The
    proof that $(f_2 (f_1\ a))$ [R]-reduces to $(f_2 (f_1\ b))$ is
    more tricky. Initially, note that, since $a \to_{R1} b$ then we
    get that $(f_1\ a) \tto_{R1} (f_1\ b)$ by the Z property. *)
      
      induction H0. (** Now, the goal can be obtained from [H2] as
      long as $(f_1\ a) \to_{R1} (f_1\ b)$, but from the hypothesis
      [H0] we have that $(f_1\ a) \tto_{R1} (f_1\ b)$. Therefore, we
      proceed by induction on [H0]. *)
      
      * apply refl. (** The reflexive case is trivial because [a] and
        [b] are equal. *)
        
      * apply refltrans_composition with (f2 b0). (** In the
        transitive case, we have that $(f_1\ a)$ [R1]-reduces to
        $(f_1\ b)$ in at least one step. The current proof context is
        as follows, up to renaming of variables:

      %\includegraphics[scale=0.6]{fig9.png}%

      Therefore, there exists some element $b0$ such that $a0\to_{R1}
      b0$ and $b0 \tto_{R1} c$ and we need to prove that $(f_2\ a0)
      \tto_{R1\cup R2} (f_2\ c)$. This can be done in two steps using
      the transitivity of [refltrans] taking $(f_2\ b0)$ as the
      intermediary term. *)
        
        ** apply H2; assumption. (** The first subgoal is then $(f_2\
           a0)\tto_{(R1 \cup R2)} (f_2\ b0)$ that is proved by
           hypothesis [H2]. *)
           
        ** assumption. (** And the second subgoal $(f_2\ b0) \tto_{(R1
           \cup R2)} (f_2\ c)$ is proved by the induction
           hypothesis. *)
           
  - apply H4; assumption. (** Finally, when [a] [R2]-reduces in one
    step to [b] one concludes the proof using the assumption that
    $(f_2 \circ f_1)$ is weak Z. *)
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
  intros R Heq.  unfold Z_comp_eq in Heq. (** Let [R] be a relation
  and suppose that [R] satisfies the predicate [Z_comp_eq]. *)
  
  destruct Heq as [R1 [R2 [f1 [f2 [Hunion [H1 [H2 [H3 H4]]]]]]]]. (**
  Call [Hi] the [i]th hypothesis as in %\ref{cor:zcomp}%. *)
  
  unfold Z_prop.  exists (f2 # f1). (** From the definition of the
  predicate [Z_prop], we need to find a map, say [f] that is Z. Let
  $(f_2 \circ f_1)$ be such map.  *)
  
  intros a b Hab. (** In order to prove that $(f_2 \circ f_1)$ is Z,
  let [a] and [b] be arbitrary elements of type [A], and [Hab] be the
  hypothesis that $a \to_{R} b$. *)
  
  inversion Hunion; subst; clear H.  inversion Hab; subst; clear Hab. (**
  Since [a] [R]-reduces in one step to [b] and [R] is the union of the
  relations [R1] and [R2] then we consider two cases: *)
  
  - unfold comp; split. (** The first case is when $a \to_{R1}
    b$. This is equivalent to say that $f_2 \circ f_1$ is weak Z for
    $R1$ by $R1 \cup R2$. *)
    
    + apply refltrans_composition with (f1 b). (** Therefore, we first
    prove that $b \tto_{(R1\cup R2)} (f_2 (f_1\ a))$, which can be
    reduced to $b \tto_{(R1\cup R2)} (f_1\ b)$ and $(f_1\ b)
    \tto_{(R1\cup R2)} (f_2 (f_1\ a))$ by the transitivity of
    [refltrans]. *)
      
      * apply refltrans_union.  apply H2. (** From hypothesis [H2], we
        know that $a \tto_{R1} (f_1\ a)$ for all $a$, and hence
        $a\tto_{(R1\cup R2)} (f_1\ a)$ and we conclude. *)
        
      * apply H1 in H.  rewrite H.  apply H3 with b; reflexivity. (**
        The proof that $(f_1\ b)\tto_{(R1\cup R2)} (f_2 (f_1\ a))$ is
        exactly the hypothesis [H3]. *)

    + apply H1 in H.  rewrite H.  apply refl. (** The proof that $(f_2
    (f_1\ a)) \tto_{(R1\cup R2)} (f_2 (f_1\ b))$ is done using the
    reflexivity of [refltrans] because $(f_2 (f_1\ a)) = (f_2 (f_1\
    b))$ by hypothesis [H1]. *)
      
  - apply H4; assumption. (** When $a \to_{R2} b$ then we are done by
    hypothesis [H4]. *)

Qed.

