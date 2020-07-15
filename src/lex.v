(** * An application: Proving Confluence of a Calculus with Explicit Substitutions *)

(* begin hide *)

(** * The Z property implies Confluence

  An ARS, say $(A,R)$, is defined as a pair composed of a set $A$ and
  binary operation over this set $R:A\times A$. Let $a,b\in A$. We
  write $a\ R\ b$ or $a\to_R b$ to denote that $(a,b)\in R$, and we
  say that $a$ $R$-reduces to $b$ in one step. The arrow notation will
  be prefered because it is more convenient for expressing reductions,
  so the reflexive transitive closure of a relation [R], written as
  $\tto_R$, is defined by the following inference rules:
  %\begin{mathpar} \inferrule*[Right={$(refl)$}]{~}{a \tto_R a} \and
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
(* end hide *)

Inductive refltrans {A:Type} (R: Rel A) : A -> A -> Prop :=
| refl: forall a, (refltrans R) a a
| rtrans: forall a b c, R a b -> refltrans R b c -> refltrans R a c.

(** The rules named ([refl]) and ([rtrans]) are called _constructors_
in the Coq definition. The first constructor states the reflexivity
axiom for $\tto_R$, while [rtrans] extends the reflexive transitive
closure of [R], if one has at least a one-step reduction. As a first
example, let's have a look at the proof of transitivity of $\tto_R$:

%\begin{lemma} Let $\to_R$ be a binary relation over a set $A$. If $t
\tto_R u$ and $u \tto_R v$ then $t \tto_R v$, $\forall t,u,v \in A$.
\end{lemma}%

 Although its proof is simple, it will help us to explain the way we will
relate English annotations with the proof steps. The corresponding
lemma in Coq, named [refltrans_composition], is stated as follows: *)

Lemma refltrans_composition {A} (R: Rel A): forall t u v, refltrans R t u -> refltrans R u v -> refltrans R t v.
(* begin hide *)
Proof.  
 intros t u v.  
 intros H1 H2.  
 induction H1.
 - assumption.  
 - apply rtrans with b.  
 + assumption.  
 + apply IHrefltrans; assumption.  
Qed. 
(* end hide *)
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
pedagogical one. Coq proofs are written between the reserved words
[Proof] and [Qed] (lines 1 and 9), and each proof command finishes
with a dot. Proofs can be structured with bullets (- in the first
level, + in the second level, * in the third level, ** in the fourth
level, and so on). The corresponding informal proof proceed as
follows: *)

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
 
(** This example is interesting because it shows how Coq works, how
each command line (also known as tactics or tacticals depending on its
structure) corresponds, in general, to several steps of natural
deduction rules. *)

(* begin hide *)
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

(** Alternatively, when [f] satisfies the Z property, one says that [f] is Z: *)

Definition f_is_Z {A:Type} (R: Rel A) (f: A -> A) := forall a b, R a b -> ((refltrans R)  b (f a) /\ (refltrans R) (f a) (f b)). 

(** The first contribution of this work is a constructive proof of the
    fact that the Z property implies confluence. Our proof uses nested
    induction, and hence it differs from the one in %\cite{kes09}%
    (that follows %\cite{dehornoy2008z}%) in the sense that it does
    not rely on the law of the excluded middle. As a result, we have
    an elegant inductive proof of the fact that if a binary relation
    has the Z property then it is confluent. In addition, we
    formalized this proof in the Coq proof assistant. In
    %\cite{zproperty}%, B. Felgenhauer et.al. formalized the Z
    property in Isabelle/HOL. In what follows, we present the theorem
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
        $a'$, that reduces to $b$ from one side, converges: [IHHrefl1]
        : $\forall c_0 : A, a'\tto_R c_0 \to (\exists d : A, b\tto_R d
        \land c_0\tto_R d$). The idea is to apply induction on the
        hypothesis [Hrefl2], but the current proof context has the
        hypothesis [H]: $a\to_R a'$ ([a] reduces to [a'] in one step),
        and hence it is the sole hypothesis depending on [a] in the
        current proof context. Therefore, suppose that $a\tto_R c$ is
        built as $a \to_R a'' \tto_R c$ in the case of the constructor
        [rtrans]. The induction step in this case will assume that
        $a''$ reduces in one step to $a'$, which is not true in
        general. Note that all hypothesis, that do not have $a$ as
        parameter, do not contribute to the shape of the induction
        hypothesis. In order to circumvent this problem, we need to
        remove the hypothesis [H], and replace it by another relevant
        information derived from the Z property as shown in what
        follows. *)
  
  - intros c0 Hrefl2. (** Let $c_0$ be a reduct of $a$, and [Hrefl2]
    be the hypothesis $a \tto_R c_0$. So the reduction $a\tto_R c$ in
    the above diagram is now $a\tto_R c_0$ due to a renaming of
    variables automatically done by the Coq system. In addition, the
    reduction $a \to_R a' \tto_R b$ is now $a\to_R b \tto_R c$, as
    shown below:

    %\includegraphics[scale=0.6]{fig5-1.png}%

    Before applying induction to [Hrefl2]: $a \tto_R c_0$, we will be
    replace the hypothesis [H]: $a\to_R b$ by two other properties
    that are proved from the Z property: $b\tto_R (g\ a)$ and $a\tto_R
    (g\ a)$. *)

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

    clear H; generalize dependent b. (** At this point we can remove
      the hypothesis [H] from the context, and generalize [b]. *)

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

      apply IHHrefl2 with b0. (** The second goal, i.e. the inductive
        case can be proved by the second induction hypothesis
        [IHHrefl2], and each of the 4 conditions generated by this
        hypothesis is solved as follows: *) 
      
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

(** An alternative proof that Z implies confluence is possible via the
    notion of semiconfluence, which is equivalent to confluence, as
    done in %\cite{zproperty}%. Our proof is also constructive, but we
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
    
    %\begin{definition} Let $(A,\to_R)$ be an ARS and $\to_x$ a
     relation on $A$. A mapping $f$ satisfies the {\it weak Z
     property} for $\to_R$ by $\to_x$ if $a\to_R b$ implies $b \tto_x
     f(a)$ and $f(a) \tto_x f(b)$ (cf. Figure
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

    %\begin{corollary}\cite{Nakazawa-Fujita2016}\label{cor:zcomp} Let
     $(A,\to_R)$ be an ARS such that $\to_R = \to_1 \cup \to_2$. If
     there exist mappings $f_1,f_2: A \to A$ such that
     \begin{enumerate} \item $a \to_1 b$ implies $f_1(a) = f_1(b)$
     \item $a \tto_1 f_1(a), \forall a$ \item $a \tto_R f_2(a)$ holds
     for any $a\in Im(f_1)$ \item $f_2 \circ f_1$ is weakly Z for
     $\to_2$ by $\to_R$ \end{enumerate} then $f_2 \circ f_1$ is Z for
     $(A,\to_R)$, and hence $(A,\to_R)$ is confluent. \end{corollary}%

    We define the predicate [Z_comp_eq] corresponding to the
    hypothesis of Corollary %\ref{cor:zcomp}%, and then we prove
    directly that if [Z_comp_eq] holds for a relation [R] then [Zprop
    R] also holds. This approach differs from
    %\cite{Nakazawa-Fujita2016}% that proves Corollary
    %\ref{cor:zcomp}% directly from Theorem %\ref{thm:zcomp}% *)

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



(*Require Import ZtoConfl.*)

Definition var := nat.

Require Import Arith MSetList Setoid.

Declare Module Var_as_OT : UsualOrderedType
  with Definition t := var.
Module Import VarSet := MSetList.Make Var_as_OT.

Definition vars := VarSet.t.

Notation "{}" := (VarSet.empty).
Notation "{{ x }}" := (VarSet.singleton x).
Notation "s [=] t " := (VarSet.Equal s t) (at level 70, no associativity). 
Notation "E \u F" := (VarSet.union E F)  (at level 68, left associativity).
Notation "x \in E" := (VarSet.In x E) (at level 69).
Notation "x \notin E" := (~ VarSet.In x E) (at level 69).
Notation "E << F" := (VarSet.Subset E F) (at level 70, no associativity).
Notation "E \rem F" := (VarSet.remove F E) (at level 70).

Lemma eq_var_dec : forall x y : var, {x = y} + {x <> y}.
Proof. exact eq_nat_dec. Qed.

Lemma not_or_equiv_and_not: forall (A B: Prop), ~(A \/ B) <-> ~ A /\ ~ B.
Proof.
  split.
  - intro H.
    split.
    + intro H0.
      destruct H.
      left. 
      assumption.
    + intro H0.
      destruct H.
      right.
      assumption.
  - intros H H0.
    destruct H.
    destruct H0; contradiction.
Qed.

Notation "x == y" := (eq_var_dec x y) (at level 67).
Notation "i === j" := (Peano_dec.eq_nat_dec i j) (at level 67).

Lemma notin_union : forall x E F,
  x \notin (E \u F) <-> (x \notin E) /\ (x \notin F).
Proof.
intros x E F.
apply iff_stepl with (~((x \in E) \/ (x \in F))).
- apply not_or_equiv_and_not.
- split; unfold not; intros; destruct H; apply union_spec in H0; assumption.
Qed.

(** Pre-terms are defined according to the following grammar: *)
Inductive pterm : Set :=
  | pterm_bvar : nat -> pterm
  | pterm_fvar : var -> pterm
  | pterm_app  : pterm -> pterm -> pterm
  | pterm_abs  : pterm -> pterm
  | pterm_sub : pterm -> pterm -> pterm.

Notation "t [ u ]" := (pterm_sub t u) (at level 70).

Fixpoint fv (t : pterm) {struct t} : vars :=
  match t with
  | pterm_bvar i    => {}
  | pterm_fvar x    => {{x}}
  | pterm_app t1 t2 => (fv t1) \u (fv t2)
  | pterm_abs t1    => (fv t1)
  | pterm_sub t1 t2 => (fv t1) \u (fv t2)
  end.

(* From Metatheory_Tactics - Arthur Chargueraud. REVISAR *)
Ltac gather_vars_with F :=
  let rec gather V :=
    match goal with
    | H: ?S |- _ =>
      let FH := constr:(F H) in
      match V with
      | {} => gather FH
      | context [FH] => fail 1
      | _ => gather (FH \u V)
      end
    | _ => V
    end in
  let L := gather {} in eval simpl in L.

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => {{ x }}) in
  let D := gather_vars_with (fun x : pterm => fv x) in
  constr:(A \u B \u D).

Ltac beautify_fset V :=
  let rec go Acc E :=
     match E with
     | ?E1 \u ?E2 => let Acc1 := go Acc E1 in
                     go Acc1 E2
     | {}  => Acc
     | ?E1 => match Acc with
              | {} => E1
              | _ => constr:(Acc \u E1)
              end
     end
  in go {} V.

Require Import List Omega.
Open Scope list_scope.

Lemma max_lt_l :
  forall (x y z : nat), x <= y -> x <= max y z.
Proof.
  induction x; auto with arith.
  induction y; induction z; simpl; auto with arith.
Qed.

Lemma finite_nat_list_max : forall (l : list nat),
  { n : nat | forall x, In x l -> x <= n }.
Proof.
  induction l as [ | l ls IHl ].
  - exists 0; intros x H; inversion H.
  - inversion IHl as [x H]; clear IHl.
    exists (max x l).
    intros x' Hin.
    inversion Hin; subst.
    + auto with arith.
    + assert (x' <= x); auto using max_lt_l.
Qed.      

Lemma finite_nat_list_max' : forall (l : list nat),
  { n : nat | ~ In n l }.
Proof.
  intros l. case (finite_nat_list_max l); intros x H.
  exists (S x). intros J. assert (K := H _ J); omega.
Qed.

Definition var_gen (L : vars) : var :=
  proj1_sig (finite_nat_list_max' (elements L)).

Lemma var_gen_spec : forall E, (var_gen E) \notin E.
Proof.
  unfold var_gen. intros E.
  destruct (finite_nat_list_max' (elements E)) as [n pf].
  simpl. intros a. 
  destruct pf.
  apply elements_spec1 in a.
  rewrite InA_alt in a.
  destruct a as [y [H1 H2]].
  subst; assumption.
Qed.
  
Lemma var_fresh : forall (L : vars), { x : var | x \notin L }.
Proof.
  intros L. exists (var_gen L). apply var_gen_spec.
Qed.

Ltac pick_fresh_gen L Y :=
  let Fr := fresh "Fr" in
  let L := beautify_fset L in
  (destruct (var_fresh L) as [Y Fr]).

Ltac pick_fresh Y :=
  let L := gather_vars in (pick_fresh_gen L Y).

Fixpoint open_rec (k : nat) (u : pterm) (t : pterm) : pterm :=
  match t with
  | pterm_bvar i    => if k === i then u else (pterm_bvar i)
  | pterm_fvar x    => pterm_fvar x
  | pterm_app t1 t2 => pterm_app (open_rec k u t1) (open_rec k u t2)
  | pterm_abs t1    => pterm_abs (open_rec (S k) u t1)
  | pterm_sub t1 t2 => pterm_sub (open_rec (S k) u t1) (open_rec k u t2)
  end.

Definition open t u := open_rec 0 u t.

Notation "{ k ~> u } t" := (open_rec k u t) (at level 67).
Notation "t ^^ u" := (open t u) (at level 67). 
Notation "t ^ x" := (open t (pterm_fvar x)).   

Fixpoint close_rec  (k : nat) (x : var) (t : pterm) : pterm :=
  match t with
  | pterm_bvar i    => pterm_bvar i
  | pterm_fvar x'    => if x' == x then (pterm_bvar k) else pterm_fvar x'
  | pterm_app t1 t2 => pterm_app (close_rec k x t1) (close_rec k x t2)
  | pterm_abs t1    => pterm_abs (close_rec (S k) x t1)
  | pterm_sub t1 t2 => pterm_sub (close_rec (S k) x t1) (close_rec k x t2)
  end.

Definition close t x := close_rec 0 x t.

(** Implicit substitution for free names *)
Fixpoint m_sb (z : var) (u : pterm) (t : pterm) : pterm :=
  match t with
  | pterm_bvar i    => pterm_bvar i
  | pterm_fvar x    => if x == z then u else (pterm_fvar x)
  | pterm_abs t1    => pterm_abs (m_sb z u t1)
  | pterm_app t1 t2 => pterm_app (m_sb z u t1) (m_sb z u t2)
  | pterm_sub t1 t2 => pterm_sub (m_sb z u t1) (m_sb z u t2)
  end.
Notation "[ z ~> u ] t" := (m_sb z u t) (at level 62).

(** Substitution for a fresh name is identity. *)
Lemma subst_fresh : forall x t u,   x \notin fv t ->  [x ~> u] t = t.
Proof.
  intros x t.
  generalize dependent x.
  induction t.
  - intros x u Hfv.
    reflexivity.
  - intros x u Hfv.
    simpl.
    destruct (v == x); subst.
    + simpl in *.
      unfold not in Hfv.
      destruct Hfv.
      apply singleton_spec; reflexivity.
    + reflexivity.
  - intros x u Hfv.
    simpl in *.
    apply notin_union in Hfv.
    destruct Hfv as [Hfv1 Hfv2].
    specialize (IHt1 x u).
    apply IHt1 in Hfv1.
    rewrite Hfv1.
    specialize (IHt2 x u).
    apply IHt2 in Hfv2.
    rewrite Hfv2.
    reflexivity.
  - intros x u Hfv.
    simpl in *.
    specialize (IHt x u).
    apply IHt in Hfv.
    rewrite Hfv.
    reflexivity.
  - intros x u Hfv.
    simpl in *.
    apply notin_union in Hfv.
    destruct Hfv as [Hfv1 Hfv2].
    specialize (IHt1 x u).
    apply IHt1 in Hfv1.
    rewrite Hfv1.
    specialize (IHt2 x u).
    apply IHt2 in Hfv2.
    rewrite Hfv2.
    reflexivity.
Qed.

Lemma m_sb_intro: forall t u x n, x \notin (fv t) -> [x ~> u] (open_rec n (pterm_fvar x) t)  = open_rec n u t.
Proof.
  intro t; induction t.
  - intros u x n' Hfv.
    assert (H1 := subst_fresh).
    specialize (H1 x (pterm_bvar n) u).
    apply H1 in Hfv.
    simpl.
    rewrite <- Hfv.
    destruct (n' === n).
    + simpl.
      destruct (x == x).
      * reflexivity.
      * contradiction.
    + reflexivity.
  - intros u x n' Hfv.
    simpl.
    destruct (v == x).
    + rewrite e in Hfv.
      destruct Hfv.
      apply singleton_spec; reflexivity.
    + reflexivity.
  - intros u x n Hfv.
    simpl in *.
    apply notin_union in Hfv.
    destruct Hfv as [Hfv1 Hfv2].
    specialize (IHt1 u x n).
    apply IHt1 in Hfv1.
    rewrite Hfv1.
    specialize (IHt2 u x n).
    apply IHt2 in Hfv2.
    rewrite Hfv2.
    reflexivity.
  - intros u x n Hfv.
    unfold open.
    simpl.
    f_equal.
    apply IHt.
    assumption.
  - intros u x n Hfv.
    simpl in *.
    apply notin_union in Hfv.
    destruct Hfv as [Hfv1 Hfv2].
    specialize (IHt1 u x (S n)).
    apply IHt1 in Hfv1.
    rewrite Hfv1.
    specialize (IHt2 u x n).
    apply IHt2 in Hfv2.
    rewrite Hfv2.
    reflexivity.
Qed.

Corollary m_sb_intro_open: forall x t u, x \notin (fv t) -> [x ~> u] (t ^ x)  = t ^^ u.
Proof.
  intros x t u Hfv.
  apply m_sb_intro; assumption.
Qed.

(** ES terms are expressions without dangling deBruijn indexes. *)

Inductive term : pterm -> Prop :=
  | term_var : forall x,
      term (pterm_fvar x)
  | term_app : forall t1 t2,
      term t1 -> 
      term t2 -> 
      term (pterm_app t1 t2)
  | term_abs : forall L t1,
      (forall x, x \notin L -> term (t1 ^ x)) ->
      term (pterm_abs t1)
  | term_sub : forall L t1 t2,
     (forall x, x \notin L -> term (t1 ^ x)) ->
      term t2 -> 
      term (pterm_sub t1 t2).

Definition body t := exists L, forall x, x \notin L -> term (t ^ x).

Fixpoint lc_at (k:nat) (t:pterm) : Prop :=
  match t with
  | pterm_bvar i    => i < k
  | pterm_fvar x    => True
  | pterm_app t1 t2 => lc_at k t1 /\ lc_at k t2
  | pterm_abs t1    => lc_at (S k) t1
  | pterm_sub t1 t2 => (lc_at (S k) t1) /\ lc_at k t2
  end.

Lemma lc_at_weaken_ind : forall k1 k2 t,
  lc_at k1 t -> k1 <= k2 -> lc_at k2 t.
Proof.
  intros k1 k2 t.
  generalize dependent k2.
  generalize dependent k1.
  induction t.
  - intros k1 k2 Hlc_at Hle.
    simpl in *.
    apply Nat.lt_le_trans with k1; assumption.
  - intros k1 k2 Hlc_at Hle.
    simpl. auto.
  - intros k1 k2 Hlc_at Hle.
    simpl in *.
    destruct Hlc_at as [H1 H2].
    split.
    + apply IHt1 with k1; assumption.
    + apply IHt2 with k1; assumption.
  - intros k1 k2 Hlc_at Hle.
    simpl.
    simpl in Hlc_at.
    apply IHt with (S k1).
    + assumption.
    + apply Peano.le_n_S; assumption.
  - intros k1 k2 Hlc_at Hle.
    simpl in *.
    destruct Hlc_at as [H1 H2].
    split.
    + apply IHt1 with (S k1).
      * assumption.
      * apply Peano.le_n_S; assumption.
    + apply IHt2 with k1; assumption.
Qed.

Lemma lc_at_open_var_rec : forall x t k,
  lc_at k (open_rec k x t) -> lc_at (S k) t.
Proof.
  intros x t.
  induction t; simpl. 
  - intro k.
    destruct (k === n); subst; auto with arith.
  - auto.
  - intros k H.
    destruct H as [Ht1 Ht2].
    split.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
  - intros k Hlc_at.
    apply IHt; assumption.
  - intros k H.
    destruct H as [Ht1 Ht2].
    split.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
Qed.

Lemma term_to_lc_at : forall t, term t -> lc_at 0 t.
Proof.
  intros t Hterm.
  induction Hterm.
  - simpl; auto.
  - simpl; split; assumption.
  - pick_fresh y.
    apply notin_union in Fr.
    destruct Fr as [Fr Hfv].
    apply H0 in Fr.
    apply lc_at_open_var_rec in Fr.
    simpl; assumption.
  - simpl.
    split.
    + pick_fresh y.
      apply notin_union in Fr.
      destruct Fr as [Fr Hfv].
      apply notin_union in Fr.
      destruct Fr as [Fr Hfv'].
      apply H0 in Fr.
      apply lc_at_open_var_rec in Fr.
      assumption.
    + assumption.
Qed.

Lemma lc_at_open_rec : forall n t u, term u -> (lc_at (S n) t -> lc_at n (open_rec n u t)).
Proof.
  intros n t u T H.
  generalize dependent n.
  induction t.
  - intros n' Hlc_at.
    simpl in *.
    destruct (n' === n).
    + apply term_to_lc_at in T.
      apply lc_at_weaken_ind with 0.
      * assumption.
      * auto with arith.
    + simpl.
      apply lt_n_Sm_le in Hlc_at.
      apply le_lt_or_eq in Hlc_at.
      destruct Hlc_at.
      * assumption.
      * symmetry in H. contradiction.
  - intros n Hlc_at.
    simpl in *.
    auto.
  - intros n Hlc_at.
    simpl in *.
    destruct Hlc_at as [H1 H2].
    split.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
  - intros n Hlc_at.
    apply IHt.
    simpl in Hlc_at; assumption.    
  - intros n H.
    inversion H; subst; clear H.
    simpl; split.
    + apply IHt1; assumption.      
    + apply IHt2; assumption.
Qed.

Corollary lc_at_open : forall n t u, term u -> (lc_at (S n) t <-> lc_at n (open_rec n u t)).
Proof.
  intros n t u; split.
  - apply lc_at_open_rec; assumption. 
  - apply lc_at_open_var_rec.
Qed.

Lemma lc_at_open_rec_leq : forall n k t u, n <= k -> lc_at n t -> lc_at n (open_rec k u t).
Proof.
  intros n k t0.
  generalize dependent k.
  generalize dependent n.
  induction t0.
  - intros n' k u Hleq Hlc_at. 
    simpl.
    destruct (k === n).
    + inversion Hlc_at.
      * subst.
        apply Nat.nle_succ_diag_l in Hleq; contradiction.
      * subst.
        apply le_S_gt in H.
        apply le_S_gt in Hleq.
        apply gt_asym in H; contradiction.
    + assumption.
  - intros n' k u Hleq Hlc_at.
    assumption.
  - intros n' k u Hleq Hlc_at.
    destruct Hlc_at.
    simpl; split.
    + apply IHt0_1; assumption.
    + apply IHt0_2; assumption.
  - intros n' k u Hleq Hlc_at.
    simpl in *.
    apply IHt0.
    + apply le_n_S; assumption.
    + assumption.
  - intros n' k u Hleq Hlc_at.
    destruct Hlc_at.
    simpl in *; split.
    + apply IHt0_1.
      * apply le_n_S; assumption.
      * assumption.
    + apply IHt0_2; assumption.
Qed.
  
Lemma lc_at_open_rec_rename: forall t x y m n, lc_at m (open_rec n (pterm_fvar x) t) -> lc_at m (open_rec n (pterm_fvar y) t).
Proof.
  intro t; induction t.
  - intros x y m k.
    simpl.
    destruct (k === n); tauto.
  - intros x y m n H.
    simpl; auto.
  - intros x y m n H.
    simpl in *.
    inversion H as [H1 H2]; split.
    + apply IHt1 with x; assumption.
    + apply IHt2 with x; assumption.
  - intros x y m n H.
    simpl in *.
    apply IHt with x; assumption.
  - intros x y m n Hlc_at.
    simpl in *.
    destruct Hlc_at as [H1 H2]; split.
    + apply IHt1 with x; assumption.      
    + apply IHt2 with x; assumption.
Qed.

Fixpoint pterm_size (t : pterm) {struct t} : nat :=
 match t with
 | pterm_bvar i    => 1
 | pterm_fvar x    => 1
 | pterm_abs t1    => 1 + (pterm_size t1)
 | pterm_app t1 t2 => 1 + (pterm_size t1) + (pterm_size t2)
 | pterm_sub t1 t2 => 1 + (pterm_size t1) + (pterm_size t2)
 end.

Lemma pterm_size_positive: forall t, 0 < pterm_size t.
Proof.
  induction t0; simpl; auto with arith.
Qed.
    
Lemma pterm_size_open: forall t x, pterm_size (t^x) = pterm_size t.
Proof.
  unfold open.
  intros t x.
  generalize dependent 0.
  generalize dependent x.
  induction t.
  - unfold open_rec.
    intros x n'.
    destruct (n' === n); reflexivity.
  - reflexivity.
  - simpl.
    intros x n.
    destruct (IHt1 x n).
    destruct (IHt2 x n).
    reflexivity.
  - simpl.
    intros x n.
    destruct (IHt x (S n)); reflexivity.
  - simpl.
    intros x n.
    destruct (IHt1 x (S n)).
    destruct (IHt2 x n).
    reflexivity.
Qed.

Lemma strong_induction :  forall Q: nat -> Prop,
    (forall n, (forall m, m < n -> Q m) -> Q n) ->
    forall n, Q n.
Proof.
  intros Q IH n.
  assert (H := nat_ind (fun n => (forall m : nat, m < n -> Q m))).
  apply IH.
  apply H.
  - intros m Hlt; inversion Hlt.
  - intros n' H' m Hlt.
    apply IH.
    intros m0 Hlt'.
    apply H'.
    apply lt_n_Sm_le in Hlt.
    apply lt_le_trans with m; assumption.
Qed.

Lemma pterm_size_induction :
 forall P : pterm -> Prop,
 (forall t,
    (forall t', pterm_size t' < pterm_size t ->
    P t') -> P t) ->
 (forall t, P t).
Proof.
  intros P IH t.
  remember (pterm_size t) as n eqn:H.
  assert (HsiInst := strong_induction (fun n => forall t, n = pterm_size t -> P t)).
  generalize dependent t.
  generalize dependent n.
  apply HsiInst.
  intros n' Hind t Hsz.
  apply IH.
  intros t' Hlt.
  apply Hind with (pterm_size t').
  - rewrite Hsz; assumption.  
  - reflexivity.
Qed.

Theorem term_equiv_lc_at: forall t, term t <-> lc_at 0 t.
Proof.
  intro t; split.
  - apply term_to_lc_at.
  - induction t using pterm_size_induction.
    induction t0.
    + intro Hlc_at.
      inversion Hlc_at.
    + intro Hlc_at.
      apply term_var.
    + simpl.
      intro Hlc_at.
      destruct Hlc_at as [Hlc1 Hlc2].
      apply term_app.
      * apply H.
        ** simpl.
           apply lt_trans with (pterm_size t0_1 + pterm_size t0_2).
           *** apply Nat.lt_add_pos_r.
               apply pterm_size_positive.
           *** auto.
        ** assumption.
      * apply H.
        ** simpl.
           apply lt_trans with (pterm_size t0_1 + pterm_size t0_2).
           *** apply Nat.lt_add_pos_l.
               apply pterm_size_positive.
           *** auto.
        ** assumption.
    + intro Hlc_at. 
      apply term_abs with (fv t0).
      intros x Hfv.
      apply H.
      * rewrite pterm_size_open.
        simpl; auto.
      * simpl in Hlc_at.
        apply lc_at_open.
        ** apply term_var.
        ** assumption.
    + intro Hlc_at.
      apply term_sub with (fv t0_1).
      * intros x Hfv.
        apply H.
        ** rewrite pterm_size_open.
           simpl; auto with arith.
        ** simpl in Hlc_at.
           apply lc_at_open.
           *** apply term_var.
           *** apply Hlc_at.
      * apply IHt0_2.
        ** intros t H0 H1.
           apply H.
           *** simpl.
               assert (a_lt_ab: forall a b c, a < c -> a < b + c).
               {
                 intros a b c Habc.
                 induction b.
                 auto with arith.
                 assert (S_in_out: S b + c = S (b + c)).
                 {
                   auto with arith.
                 }
                 rewrite S_in_out.
                 auto with arith.
               }
               assert (S_out_in: forall t1 t2, S (pterm_size t2 + pterm_size t1) = pterm_size t2 + S (pterm_size t1)).
               {
                 intros.
                 apply plus_n_Sm.
               }
               rewrite S_out_in.
               apply a_lt_ab.
               auto with arith.
           *** assumption.
        ** simpl in Hlc_at.
           apply Hlc_at.
Qed.

Theorem body_lc_at: forall t, body t <-> lc_at 1 t.
Proof.
  intro t.
  split.
  - intro Hbody.
    unfold body in Hbody.
    destruct Hbody.
    assert (Hlc_at :  forall x0 : elt, x0 \notin x -> lc_at 0 (t ^ x0)).
    {
      intros x' Hnot.
      apply term_equiv_lc_at.
      apply H; assumption.
    }
    clear H.
    unfold open in Hlc_at.
    pick_fresh y.
    apply notin_union in Fr.
    destruct Fr.
    apply Hlc_at in H.
    generalize dependent H.
    apply lc_at_open.
    apply term_var.
  - intro Hlc_at.
    unfold body.
    exists (fv t).
    intros x Hnot.
    apply term_equiv_lc_at.
    unfold open.
    apply lc_at_open.
    + apply term_var.
    + assumption.
Qed.

(* Falso: tome t1 = 0 e t2 = x
Lemma pterm_abs_open: forall t1 t2 x, term (t1^x) -> term (t2^x) -> t1^x = t2^x -> pterm_abs t1 = pterm_abs t2. 
Proof.
  intros t1 t2 x Hbody.
  generalize dependent x.
  generalize dependent t2.
Admitted.


Lemma pterm_sub_open: forall t1 t2 t3 x, t1^x = t2^x -> pterm_sub t1 t3 = pterm_sub t2 t3. 
Proof.
Admitted.
*)

Lemma open_k_Sk: forall t x y k k', k <> k' -> {k ~> pterm_fvar y} ({k' ~> pterm_fvar x} close_rec k' x t) = {k' ~> pterm_fvar x} close_rec k' x ({k ~> pterm_fvar y} t).
Proof.
  intros t x y k k' H.
  generalize dependent k.
  generalize dependent k'.
  induction t.
  - intros k' k H.
    simpl.
    destruct (k' === n).
    + subst.
      destruct (k === n).
      * contradiction.
      * simpl.
        destruct (n === n).
        **  reflexivity.
        **  contradiction.
    + simpl.
      destruct (k === n).
      * unfold close_rec.
        destruct (y == x).
        **  subst.
            simpl.
            destruct (k' === k').
            *** reflexivity.
            *** contradiction.
        **  reflexivity.
      * simpl.
        destruct (k' === n).
        **  contradiction.
        **  reflexivity.
  - intros k' k H.
    simpl.
    destruct (v == x).
    + simpl.
      destruct (k' === k').
      * reflexivity.
      * contradiction.
    + reflexivity.
  - intros k' k H.
    simpl.
    rewrite IHt1.
    + rewrite IHt2.
      * reflexivity.
      * assumption.
    + assumption.
  - intros k' k H.
    specialize (IHt (S k')).
    specialize (IHt (S k)).
    simpl.
    rewrite IHt.
    + reflexivity.
    + apply not_eq_S; assumption.
  - intros k' k H.
    simpl.
    specialize (IHt1 (S k')).
    specialize (IHt1 (S k)).
    specialize (IHt2 k').
    specialize (IHt2 k).
    rewrite IHt1.
    + rewrite IHt2.
      * reflexivity.
      * assumption.
    + apply not_eq_S; assumption.
Qed.

(** bswap replaces 0s by 1s and vice-versa. Any other index is preserved. *)
Fixpoint has_free_index (k:nat) (t:pterm) : Prop :=
  match t with
    | pterm_bvar n => if (k === n) then True else False
    | pterm_fvar x => False
    | pterm_app t1 t2 => (has_free_index k t1) \/ (has_free_index k t2)
    | pterm_abs t1 => has_free_index (S k) t1
    | pterm_sub t1 t2 => (has_free_index (S k) t1) \/ (has_free_index k t2)
  end.

Lemma has_index: forall i, has_free_index i (pterm_bvar i).
Proof.
  intro i. simpl. destruct (i === i); auto.
Qed.

Lemma not_has_free_index: forall t k x, ~(has_free_index k (open_rec k (pterm_fvar x) t)).
Proof.
  intro t; induction t.
  - intros k x H.
    case (k === n).
    + intro Heq. subst.
      simpl in H.
      destruct (n === n).
      * simpl in *.
        auto.
      * apply n0.
        reflexivity.
    + intro H'.
      simpl in H.
      destruct (k === n).
      * contradiction.
      * simpl in H.
        destruct (k === n).
        ** contradiction.
        ** auto.
  - intros k x H.
    simpl in H.
    auto.
  - intros k x H.
    simpl in H.
    destruct H.
    + generalize H.
      apply IHt1.
    + generalize H.
      apply IHt2.
  - intros k x H.
    simpl in H.
    generalize H.
    apply IHt.
  - intros k x H.
    simpl in H.
    destruct H.
    + generalize H.
      apply IHt1.
    + generalize H.
      apply IHt2.
Qed.  

Lemma has_index_open_rec: forall t k n x, k<>n -> has_free_index k t -> has_free_index k (open_rec n x t).
Proof.
    intro t; induction t.
  - intros k n' x Hneq H.
    simpl.
    destruct (n' === n).
    + subst.
      simpl in H.
      destruct (k === n); contradiction.
    + assumption.
  - intros k n x Hneq H.
    simpl in *. auto.
  - intros k n x Hneq Happ.
    simpl in *.
    destruct Happ.
    + left.
      apply IHt1; assumption.
    + right.
      apply IHt2; assumption.
  - intros k n x Hneq H.
    simpl in *.
    apply IHt.
    + apply not_eq_S; assumption. 
    + assumption.
  - intros k n x Hneq Hsub.
    simpl in *.
    destruct Hsub.
    + left.
      apply IHt1.
      * apply not_eq_S; assumption.
      * assumption.
    + right.
      apply IHt2; assumption.
Qed.
      
Lemma has_index_open: forall t k x, has_free_index (S k) t -> has_free_index (S k) (t ^ x).
Proof.
  intros t k x H.
  unfold open.
  apply has_index_open_rec.
  - apply Nat.neq_succ_0.
  - assumption.
Qed.    
  
Lemma open_rec_close_rec_term: forall t x k, ~(has_free_index k t) -> open_rec k (pterm_fvar x) (close_rec k x t) = t.
Proof.
  intro t; induction t.
  - intros x k Hnot.
    simpl in *.
    destruct (k === n).
    + contradiction.
    + reflexivity.
  - intros x k Hnot.
    unfold open_rec.
    simpl.
    destruct (v == x).
    + subst.
      destruct (k === k).
        * reflexivity.
        * contradiction.
    + reflexivity.
  - simpl.
    intros x k Hnot.
    apply not_or_equiv_and_not in Hnot.
    destruct Hnot as [Hnot1 Hnot2].
    specialize (IHt1 x).
    specialize (IHt2 x).
    apply IHt1 in Hnot1.
    apply IHt2 in Hnot2.
    rewrite Hnot1.
    rewrite Hnot2.
    reflexivity.
  - intros x k Hnot.
    simpl.
    rewrite IHt.
    + reflexivity.
    + simpl in Hnot; assumption.
  - simpl.
    intros x k Hnot.
    apply not_or_equiv_and_not in Hnot.
    destruct Hnot as [Hnot1 Hnot2].
    specialize (IHt1 x).
    specialize (IHt2 x).
    apply IHt1 in Hnot1.
    apply IHt2 in Hnot2.
    rewrite Hnot1.
    rewrite Hnot2.
    reflexivity.
Qed.

Lemma term_not_free_index: forall t, term t -> (forall k, ~(has_free_index k t)). 
Proof.
  intros t Hterm.
  induction Hterm.
  - intro k; simpl. auto.
  - intros k H.
    simpl in H.
    destruct H.
    + generalize H.
      apply IHHterm1.
    + generalize H.
      apply IHHterm2.
  - unfold open in H0.
    intros k Habs.
    simpl in *.
    pick_fresh y.
    apply (has_index_open _ _ y) in Habs.
    generalize Habs.
    apply H0.
    apply notin_union in Fr.
    destruct Fr.
    apply notin_union in H1.
    destruct H1.
    assumption.
  - intros k Hsub.
    pick_fresh y.
    inversion Hsub; subst.
    + clear Hsub.
      apply (has_index_open _ _ y) in H1.
      generalize H1.
      apply H0.
      apply notin_union in Fr.
      destruct Fr.
      apply notin_union in H2.
      destruct H2.
      apply notin_union in H2.
      destruct H2.
      assumption.
    + generalize H1.
      apply IHHterm.
Qed.    

Lemma term_bvar: forall n x, term (pterm_bvar n^x) -> n=0.
Proof.
  unfold open.
  unfold open_rec.
  intro n.
  destruct (0 === n).
  - subst; reflexivity.
  - intros v Hterm; inversion Hterm.
Qed.

Corollary open_close_term: forall t x, term t -> (close t x)^x = t.
Proof.
  intros t x Hterm.
  apply open_rec_close_rec_term.
  apply term_not_free_index; assumption.
Qed.

(** The locally nameless framework manipulates expressions that are a representation of the lambda-terms, and not all pre-terms. In this sense, if t reduces to t' then both t and t' are terms: *)
Definition term_regular (R : Rel pterm) :=
  forall t t', R t t' -> term t /\ term t'.

(** Check if y \notin (fv t') is necessary. *)
Definition red_rename (R : Rel pterm) :=
  forall x t t' y,
    x \notin (fv t) ->
    x \notin (fv t') ->
  R (t ^ x) (t' ^ x) -> 
  R (t ^ y) (t' ^ y).

Lemma body_app: forall t1 t2, body (pterm_app t1 t2) -> body t1 /\ body t2.
Proof.
  intros t1 t2 Hbody.
  inversion Hbody; subst.
  unfold body.
  split.
  - exists x.
    intros x0 Hnot.
    apply H in Hnot.
    inversion Hnot; subst.
    assumption.
  - exists x.
    intros x0 Hnot.
    apply H in Hnot.
    inversion Hnot; subst.
    assumption.
Qed.
  
Lemma term_regular_trans: forall R, term_regular R -> term_regular (trans R).
Proof.
unfold term_regular.
intros R H t t' Htrans.
induction Htrans.
- apply H; assumption.
- destruct IHHtrans as [Hb Hc].
  apply H in H0.
  destruct H0 as [Ha Hb'].
  auto.
Qed.
   
Corollary term_open_rename: forall t x y, term (t^x) -> term (t^y).  
Proof.
  intros t x y H.
  apply term_to_lc_at in H.
  apply term_equiv_lc_at.
  unfold open in H.
  apply lc_at_open_rec_rename with x; assumption.
Qed.

Lemma body_to_term: forall t x, x \notin fv t -> body t -> term (t^x).
Proof.
  intros t x Hfc Hbody.
  unfold body in Hbody.
  destruct Hbody as [L H].
  pick_fresh y.
  apply notin_union in Fr.
  destruct Fr as [Fr Hfvt].
  apply notin_union in Fr.
  destruct Fr as [Fr Hfvx].
  apply H in Fr.
  apply term_open_rename with y; assumption.
Qed.


Fixpoint bswap_rec (k : nat) (t : pterm) : pterm :=
  match t with
  | pterm_bvar i    => if k === i then (pterm_bvar (S k))
                       else (if (S k) === i then (pterm_bvar k) else t)
  | pterm_fvar x    => t
  | pterm_app t1 t2 => pterm_app (bswap_rec k t1) (bswap_rec k t2)
  | pterm_abs t1    => pterm_abs (bswap_rec (S k) t1)
  | pterm_sub t1 t2 => pterm_sub (bswap_rec (S k) t1) (bswap_rec k t2)
  end.
      
Definition bswap t := bswap_rec 0 t.
Notation "& t" := (bswap t) (at level 67).

Lemma bswap_preserves: forall t, ~(has_free_index 0 t) -> ~(has_free_index 1 t) -> & t = t.
Proof.
  intro t. unfold bswap. generalize 0.
  generalize dependent t. induction t0.
  - intros n' Hn HSn. unfold bswap_rec.
    destruct (n' === n) as [ Heq | Hdiff ]; subst.
    + apply False_ind. apply Hn. apply has_index.
    + destruct (S n' === n) as [ HSeq | HSdiff ]; subst.
      * apply False_ind. apply HSn. apply has_index.        
      * reflexivity.
  - intros n Hn HSn. reflexivity.
  - intros n Hn HSn. simpl in *. apply Decidable.not_or in Hn.
    destruct Hn as [ Hnt1 Hnt2 ]. apply Decidable.not_or in HSn.
    destruct HSn as [ HSnt1 HSnt2 ]. rewrite IHt0_1. rewrite IHt0_2. reflexivity.
    assumption. assumption. assumption. assumption.          
  - intros n Hn HSn. simpl in *. rewrite IHt0. reflexivity. 
    intro HSn'. apply Hn. assumption. intro HSSn. apply HSn. assumption.
  - intros n Hn HSn. simpl in *. apply Decidable.not_or in Hn.
    destruct Hn as [ Hnt1 Hnt2 ]. apply Decidable.not_or in HSn.
    destruct HSn as [ HSnt1 HSnt2 ]. rewrite IHt0_1. rewrite IHt0_2. reflexivity.
    assumption. assumption. assumption. assumption.
Qed.  

Lemma lc_at_bswap_rec: forall t k i, k <> (S i) -> lc_at k t -> lc_at k (bswap_rec i t).
Proof.
  intro t; induction t.
  - intros k i Hneq Hlt.
    simpl in *.
    case (i === n).
    + intro.
      inversion e; subst.
      simpl.
      destruct Hlt. 
      * contradiction.
      * auto with arith.
    + intro.
      case (S i === n).
      * intro.
        destruct e.
        case (i === i).
        ** simpl.
           auto with arith.
        ** contradiction. 
      * intro.
        destruct n.
        auto.
        assert (ni: i <> n).
        {
         auto.
        }
        case (i === n).
        ** contradiction. 
        ** trivial.
  - trivial.
  - intros k i Hneq Hlc_at.
    simpl in *.
    split.
    + apply IHt1 in Hneq.
      * assumption.
      * apply Hlc_at.
    + apply IHt2 in Hneq.
      * assumption.
      * apply Hlc_at.
  - intros k i Hneq Hlc_at.
    simpl in *.
    apply IHt.
    + auto.
    + assumption.
  - intros k i Hneq Hlc_at.
    simpl in *.
    split.
    + assert (HneqS: S k <> S (S i)).
      {
        auto.
      }
      apply IHt1 in HneqS.
      * assumption. 
      * apply Hlc_at.
    + apply IHt2 in Hneq.
      * assumption.
      * apply Hlc_at.
Qed.

Corollary lc_at_bswap: forall t k, k <> 1 -> lc_at k t -> lc_at k (& t).
Proof.
  intros t k.
  apply lc_at_bswap_rec.
Qed.
  
Lemma bswap_rec_id : forall n t, bswap_rec n (bswap_rec n t)  = t.
Proof.
 intros n t. generalize dependent n. 
 induction t.
 - intros n'.
   unfold bswap_rec.
   case (n' === n). 
   + intro H1.
     case (n' === S n').
     * assert (Q: n' <> S n'). auto with arith.
       contradiction.
     * rewrite H1.
       intro H2.
       case (S n === S n).
       ** reflexivity.
       ** contradiction.
   + intro H1.
     case (S n' === n).
     * intro H2.
       case (n' === n').
       ** rewrite H2.
          reflexivity.
       ** contradiction.
     * intro H2.
       case (n' === n).
       ** contradiction.
       ** intro H3.
          case (S n' === n).
          *** contradiction.
          *** reflexivity.
 - reflexivity.
 - intro n.
   simpl.
   rewrite (IHt1 n).
   rewrite (IHt2 n).
   reflexivity.
 - intro n.
   simpl.
   rewrite (IHt (S n)).
   reflexivity.
 - intro n.
   simpl.
   rewrite (IHt1 (S n)).
   rewrite (IHt2 n).
   reflexivity.
Qed.

Lemma bswap_idemp : forall t, (& (& t)) = t.
Proof.
  intro t. unfold bswap.
  apply bswap_rec_id.
Qed.

Lemma lc_at_bvar: forall k n, lc_at k (pterm_bvar n) -> n < k.
Proof.
  auto.
Qed.

Lemma lc_at_least_open_rec: forall t k n u, k <= n -> lc_at k t -> {n ~> u} t = t.
Proof.
  intro t; induction t.
  - intros k n' u H H0.
    apply lc_at_bvar in H0.
    unfold open_rec.
    assert (H1: n < n').
    {
      apply Nat.lt_le_trans with k; assumption.
    }
    destruct (n' === n).
      + subst.
        apply False_ind.
        generalize dependent H1.
        apply Nat.lt_irrefl.
      + reflexivity.
    - reflexivity.
    - intros k n u H H0.
      simpl in *.
      assert (H': k <= n).
      {
        assumption.
      }
      f_equal.
      + apply IHt1 with k.
        * assumption.
        * apply H0.
      + apply IHt2 with k.
        * assumption.
        * apply H0.
    - intros k n u H H0.
      simpl in *.
      f_equal.
      apply IHt with (S k).
      + auto with arith.
      + assumption.
    - intros k n u H H0.
      simpl in *.
      f_equal.
      + apply IHt1 with (S k).
        * auto with arith.
        * apply H0. 
      + apply IHt2 with k.
        * assumption.
        * apply H0.
Qed. 
        
Lemma open_rec_term: forall t n u,  term t -> {n ~> u} t = t.
Proof.
  intros t n u Hterm.
  apply term_to_lc_at in Hterm.
  generalize dependent Hterm.
  apply lc_at_least_open_rec.
  apply Peano.le_0_n.
Qed.  

Lemma open_rec_commute: forall t u k x, term u -> ({k ~> pterm_fvar x} ({S k ~> u} t)) = ({k ~> u}({S k ~> pterm_fvar x} (bswap_rec k t))).
Proof.
  intro t; induction t.
  - intros u k x Hterm.
    unfold bswap_rec.
    destruct (k === n); subst.
    + replace ({S n ~> pterm_fvar x} pterm_bvar (S n)) with (pterm_fvar x).
      * unfold open_rec at 2.
        destruct (S n === n).
        ** apply False_ind.
           generalize dependent e.
           apply Nat.neq_succ_diag_l.
        ** unfold open_rec.
           destruct (n === n).
           *** reflexivity.
           *** contradiction.
      * unfold open_rec.
        destruct (S n === S n).
        ** reflexivity.
        ** contradiction.
    + destruct (S k === n); subst.
      * unfold open_rec at 2.
        destruct (S k === S k).
        ** unfold open_rec at 3.
           destruct (S k === k).
           *** apply False_ind.
               generalize  dependent e0.
               apply Nat.neq_succ_diag_l.
           *** unfold open_rec at 2.
               destruct (k === k).
               **** apply open_rec_term; assumption.
               **** contradiction.
        ** contradiction.
      * unfold open_rec at 2.
        unfold open_rec at 3.
        destruct (S k === n).
        ** contradiction.
        ** unfold open_rec.
           destruct (k === n).
           *** contradiction.
           *** reflexivity.
  - reflexivity.
  - intros u k x Hterm.
    simpl.
    f_equal.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
  - intros u k x Hterm.
    simpl.
    f_equal.
    apply IHt; assumption.
  - intros u k x Hterm.
    simpl.
    f_equal.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
Qed.

Corollary bswap_commute: forall t u x, term u -> ({0 ~> pterm_fvar x} ({1 ~> u} t)) = ({0 ~> u}({1 ~> pterm_fvar x} (& t))).
Proof.
  intros t u x.
  apply open_rec_commute.
Qed.
  
(** Contextual closure of terms. *)
Inductive ES_contextual_closure (R: Rel pterm) : Rel pterm :=
  | ES_redex : forall t s, R t s -> ES_contextual_closure R t s
  | ES_app_left : forall t t' u, ES_contextual_closure R t t' -> term u ->
	  		      ES_contextual_closure R (pterm_app t u) (pterm_app t' u)
  | ES_app_right : forall t u u', ES_contextual_closure R u u' -> term t ->
	  		       ES_contextual_closure R (pterm_app t u) (pterm_app t u')
  | ES_abs_in : forall t t' L, (forall x, x \notin L -> ES_contextual_closure R (t^x) (t'^x)) ->
                               ES_contextual_closure R (pterm_abs t) (pterm_abs t')
  | ES_sub : forall t t' u L, (forall x, x \notin L -> ES_contextual_closure R (t^x) (t'^x)) ->
                         term u -> ES_contextual_closure R  (t [u]) (t' [u])
  | ES_sub_in : forall t u u', ES_contextual_closure R u u' -> body t ->
	  	               ES_contextual_closure R  (t [u]) (t [u']). 

Lemma term_regular_ctx: forall R, term_regular R -> term_regular (ES_contextual_closure R).
Proof.
  intros R Hred.
  unfold term_regular.
  intros t t' Hcc.
  induction Hcc.
  - apply Hred; assumption.
  - split.
    + apply term_app; auto.
      apply IHHcc.
    + apply term_app; auto.
      apply IHHcc.
  - split.
    + apply term_app; auto.
      apply IHHcc.
    + apply term_app; auto.
      apply IHHcc.
  - split.
    + apply term_abs with L.
      apply H0.
    + apply term_abs with L.
      apply H0.
  - split.
    + apply term_sub with L.
      * apply H0.
      * assumption.
    + apply term_sub with L.
      * apply H0.
      * assumption.
  - split.
    + apply term_sub with (fv t0).
      * intros x Hfv.
        apply body_to_term; assumption.
      * apply IHHcc.
    + apply term_sub with (fv t0).
      * intros x Hfv.
        apply body_to_term; assumption.
      * apply IHHcc.
Qed.


(*Require Import ZtoConfl infraES.*)

(** Context for the equation is different from the reduction
context. The equation is not term regular. *)
Inductive eqc_ctx : Rel pterm :=
| eqc_def: forall t u v, term u -> term v -> eqc_ctx (t[u][v]) ((& t)[v][u])
| eqc_app_left : forall t t' u, eqc_ctx t t' -> eqc_ctx (pterm_app t u) (pterm_app t' u)
| eqc_app_right : forall t u u', eqc_ctx u u' -> eqc_ctx (pterm_app t u) (pterm_app t u')
| eqc_abs_in : forall t t' L, (forall x, x \notin L -> eqc_ctx (t^x) (t'^x)) ->
                        eqc_ctx (pterm_abs t) (pterm_abs t')
| eqc_sub : forall t t' u L, (forall x, x \notin L -> eqc_ctx (t^x) (t'^x)) ->
                       eqc_ctx (t [u]) (t' [u])
| eqc_sub_in : forall t u u', eqc_ctx u u' -> eqc_ctx (t [u]) (t [u']).

(* begin hide *)

(*
Lemma eqc_sym : forall t u, eqc t u -> eqc u t.
Proof.
  intros t u H.
  inversion H; subst. 
  replace t0 with (&(& t0)) at 2.
  - apply eqc_def.
    + apply lc_at_bswap.
      * auto.
      * assumption.
    + assumption.
    + assumption.
  - apply bswap_idemp.
Qed.

Lemma term_regular_eqc : term_regular eqc.
Proof.
 unfold term_regular.
 intros t t' Heqc.
 inversion Heqc; subst; split.
 - apply term_sub with (fv t0).
   + intros x Hfv.
     unfold open; simpl.
     apply term_sub with (fv t0).
     * intros x' Hfv'.
       unfold open.
       apply term_equiv_lc_at.
       apply lc_at_open.
       ** apply term_var.
       ** apply lc_at_open.
          *** apply term_var.
          *** assumption.
     * apply term_equiv_lc_at.
       apply lc_at_open.
       ** apply term_var.
       ** apply term_equiv_lc_at in H0.
          apply lc_at_weaken_ind with 0.
          *** assumption.
          *** auto.
   + assumption.
 - apply term_sub with (fv t0).
   + intros x Hfv.
     unfold open; simpl.
     apply term_sub with (fv t0).
     * intros x' Hfv'.
       unfold open.
       apply term_equiv_lc_at.
       apply lc_at_open.
       ** apply term_var.
       ** apply lc_at_open.
          *** apply term_var.
          *** apply lc_at_bswap.
              **** auto.
              **** assumption.
     * apply term_equiv_lc_at.
       apply lc_at_open.
       ** apply term_var.
       ** apply term_equiv_lc_at in H1.
          apply lc_at_weaken_ind with 0.
          *** assumption.
          *** auto.
   + assumption.
Qed.


Definition eqc_ctx (t u: pterm) := ES_contextual_closure eqc t u. *)
Notation "t =c u" := (eqc_ctx t u) (at level 66).

Lemma eqc_ctx_term: forall t t', term t -> t =c t' -> term t'.
Proof.
  intros t t' Hterm Heqc.
  generalize dependent Hterm.
  induction Heqc.
  - intro Hterm.
    apply term_sub with (fv t0).
    + intros x Hfv.
      unfold open.
      simpl.
      apply term_sub with (fv t0).
      * intros x' Hfv'.
        unfold open.
        apply term_equiv_lc_at in Hterm.
        inversion Hterm; clear Hterm.
        inversion H1; clear H1.
        apply term_equiv_lc_at.
        apply lc_at_open.
        ** apply term_var.
        ** apply lc_at_open.
           *** apply term_var.
           *** apply lc_at_bswap.
               **** auto.
               **** assumption.
      * rewrite open_rec_term; assumption.
    + assumption.
  - intro Happ.
    inversion Happ; subst.
    apply term_app.
    + apply IHHeqc; assumption.    
    + assumption.
  - intro Happ.
    inversion Happ; subst.
    apply term_app.
    + assumption.    
    + apply IHHeqc; assumption.
  -  intro Habs.
     inversion Habs; subst.
     apply term_abs with (L \u L0).
     intros x Hnotin.
     apply H0.
     + apply notin_union in Hnotin.
       destruct Hnotin as [HL HL0].
       assumption.
     + apply H2.
       apply notin_union in Hnotin.
       destruct Hnotin as [HL HL0].
       assumption.
  - intro Hterm.
    inversion Hterm; subst.
    clear Hterm.
    apply term_sub with (L \u L0).
    + intros x Hnotin.
      apply notin_union in Hnotin.
      destruct Hnotin as [HL HL0].
      apply H0.
      * assumption.
      * apply H3; assumption.
    + assumption.
  - intro Hterm.
    inversion Hterm; subst.
    clear Hterm.
    apply term_sub with L.
    + intros x Hnotin.
      apply H1; assumption.
    + apply IHHeqc; assumption.
Qed.

(* Corollary term_regular_eqc_ctx: term_regular eqc_ctx.
Proof.
  apply term_regular_ctx.
  apply term_regular_eqc.
Qed. *)

Lemma eqc_ctx_sym : forall t u, t =c u -> u =c t.
Proof.
  intros t0 u H. induction H.
  - replace t0 with (&(& t0)) at 2.
    + apply eqc_def; assumption.
    + apply bswap_idemp.
  - apply eqc_app_left; assumption. 
  - apply eqc_app_right; assumption. 
  - apply eqc_abs_in with L; assumption. 
  - apply eqc_sub with L; assumption.
  - apply eqc_sub_in; assumption.
Qed.

(*
Definition eqc_trans (t u: pterm) := trans eqc_ctx t u.
Notation "t =c+ u" := (eqc_trans t u) (at level 66).

Corollary term_regular_eqc_trans: term_regular eqc_trans.
Proof.
  apply term_regular_trans.
  apply term_regular_eqc_ctx.
Qed.*)

(* Lemma eqc_trans_app: forall t t' u u', t =c+ t' -> u =c+ u' -> (pterm_app t u =c+ pterm_app t' u'). *)
(* Proof. *)
(*   intros t t' u u' Htt' Huu'. *)
(*   apply trans_composition with (pterm_app t' u). *)
(*   - inver clear Huu'. *)
(*     induction Htt'. *)
(*     + apply singl. *)
(*       apply ES_app_left. *)
(*     + *)   
(*   - *)
(* end hide *)

(** A specialized reflexive transitive closure is needed in order to guarantee that
 the expressions are terms, and not only pre-terms in the reflexive case. 
Inductive refltrans_term (R: Rel pterm) : pterm -> pterm -> Prop :=
| refl_term: forall a, term a -> (refltrans_term R) a a
| rtrans_term: forall a b c, R a b -> refltrans_term R b c -> refltrans_term R a c
.*)

Definition eqC (t : pterm) (u : pterm) := refltrans eqc_ctx t u.
Notation "t =e u" := (eqC t u) (at level 66).
(* begin hide *)
Lemma eqC_term: forall t t', term t -> t =e t' -> term t'.
Proof.
  intros t t' Hterm HeqC.
  generalize dependent Hterm.
  induction HeqC.
  - intro Hterm; assumption.
  - intro Hterm.
    apply IHHeqC.
    apply eqc_ctx_term with a; assumption.
Qed.
 
(* Corollary red_regular_eqC: red_regular eqC. *)
(* Proof. *)
(*   apply red_regular_refltrans. *)
(*   apply red_regular_eqc_ctx. *)
(* Qed. *)

(* Lemma eqC_term_regular: term_regular eqC. *)
(* Proof. *)
(*   intros t t' HeqC. *)
(*   induction HeqC. *)
(*   - apply term_regular_eqc_ctx in H. *)
(*     assumption. *)
(*   - apply term_regular_eqc_ctx in H. *)
(*     destruct H as [Ha Hb]. *)
(*     destruct IHHeqC as [Hb' Hc]. *)
(*     split; [apply Ha | apply Hc]. *)
(* Qed. *)

Lemma refltrans_composition_eqC:
    forall t u v, t =e u -> u =c v -> t =e v.
Proof.
  intros t u v HeqC Heqc_ctx.
  generalize dependent Heqc_ctx.
  induction HeqC.
  - intro Heqc_ctx.
    apply rtrans with v.
    + assumption.
    + apply refl.
  - intro Heqc_ctx.
    apply rtrans with b.
    + assumption.
    + apply IHHeqC; assumption.
Qed.

(** =e is an equivalence relation *)

Lemma eqC_refl: forall t, t =e t.
Proof.
  intro t.
  apply refl.
Qed.

Lemma eqC_sym : forall t u, t =e u -> u =e t.
Proof.
  intros t u H.
  induction H.
 - apply eqC_refl.
 - apply eqc_ctx_sym in H.
   clear H0.
   apply refltrans_composition_eqC with b; assumption.
Qed.
   
Lemma eqC_trans : forall t u v, t =e u -> u =e v -> t =e v.
Proof.
 intros t u v H H'.
 generalize dependent v.
 induction H.
 - intros v H'.
   assumption.
 - intros v H''.
   apply IHrefltrans in H''.
   apply rtrans with b; assumption.
Qed.

Require Import Morphisms.

Instance eqC_equiv : Equivalence eqC.
Proof.
  split.
  - unfold Reflexive.
    apply eqC_refl.
  - unfold Symmetric.
    intros x y Heq.
    apply eqC_sym; trivial.
  - unfold Transitive.
    intros x y z Heq Heq'.
    apply eqC_trans with y; trivial.
Qed. 

Definition red_ctx_mod_eqC (R: Rel pterm) (t: pterm) (u : pterm) : Prop :=
           exists t', exists u', (t =e t')/\(R t' u')/\(u' =e u).

Lemma term_regular_red_ctx_mod_eqC: forall R, term_regular R -> term_regular (red_ctx_mod_eqC R).
Proof.
  intros R H.
  unfold term_regular in *.
  intros t t' Hred.
  unfold red_ctx_mod_eqC in Hred.
  destruct Hred as [u [u' [HeqC [HR HeqC']]]].
  apply H in HR.
  destruct HR as [Hu Hu'].
  split.
  - apply eqC_sym in HeqC.
    apply eqC_term with u; assumption.
  - apply eqC_term with u'; assumption.
Qed.

(** =e Rewriting *)

Instance rw_eqC_red: forall R, Proper (eqC ==> eqC ==> iff) (red_ctx_mod_eqC R).
Proof.
  intro R; split.
  - intro H1.
    unfold red_ctx_mod_eqC in *.
    destruct H1 as [x'[x'' [Heq1 [HR Heq2]]]].
    exists x', x''; split.
    + apply eqC_sym in H.
      apply eqC_trans with x; assumption.
    + split.
      * assumption.
      * apply eqC_trans with x0; assumption.
  - intro H1.
    unfold red_ctx_mod_eqC in *.
    destruct H1 as [y' [y'' [Heq1 [HR Heq2]]]].
    exists y',y''; split.
    + apply eqC_trans with y; assumption. 
    + split.
      * assumption.
      * apply eqC_sym in H0.
        apply eqC_trans with y0; assumption.
Qed.

(* Instance rw_eqC_trs : forall R, Proper (eqC ==> eqC ==> iff) (trans (red_ctx_mod_eqC R)).
Proof.
 intro R; split.
 - intro H1.
   induction H1.
   + apply singl.
     apply eqC_sym in H.
     apply eqC_sym in H0.
     generalize dependent H1.
     apply rw_eqC_red; assumption.
   + Admitted. +++ *)
(* Instance rw_eqC_lc_at : forall n, Proper (eqC ==> iff) (lc_at n). *)
(* Proof. *)
(*   Admitted. *)
(* (*  intros_all. apply lc_at_eqC; trivial. *) *)
(* (* Qed. *) *)

(* Instance rw_eqC_body : Proper (eqC ==> iff) body. *)
(* Proof. *)
(*   Admitted. *)
(* (*  intros_all. rewrite body_eq_body'. rewrite body_eq_body'. *) *)
(* (*  unfold body'. rewrite H. reflexivity. *) *)
(* (* Qed. *) *)

Instance rw_eqC_term : Proper (eqC ==> iff) term.
Proof.
  intros t t' H; split.
  - intro Hterm.
    apply eqC_term in H; assumption.
  - intro Hterm.
    apply eqC_sym in H.
    apply eqC_term in H; assumption.
Qed.
    
(* (*  intros_all. rewrite term_eq_term'. rewrite term_eq_term'. *) *)
(* (*  unfold term'. rewrite H. reflexivity. *) *)
(* (* Qed. *) *)

(* Instance rw_eqC_fv : Proper (eqC ==> VarSet.Equal) fv. *)
(* Proof. *)
(*   unfold Equal. *)
(*   intros. *)
(*   Admitted. *)
(* (*  intros_all. apply eqC_fv; trivial. *) *)
(* (* Qed. *) *)

Instance rw_eqC_app : Proper (eqC ==> eqC ==> eqC) pterm_app.
  intros x y H x0 y0 H0.
  induction H.
  - induction H0.
    + reflexivity.
    + apply rtrans with (pterm_app a b).
      * apply eqc_app_right; assumption.
      * assumption.
  - apply rtrans with (pterm_app b x0).
      * apply eqc_app_left; assumption.
      * assumption.
Qed.

Instance rw_eqC_sub_in : forall t, Proper (eqC ++> eqC) (pterm_sub t).
Proof.
  intros t x y H.
  induction H.
  - reflexivity.
  - apply rtrans with (t [b]).
    + apply eqc_sub_in; assumption.
    + assumption.
Qed.

(** Lex rules *)
(* end hide *)
Inductive rule_b : Rel pterm  :=
  reg_rule_b : forall (t u:pterm),
    body t -> term u ->
    rule_b (pterm_app(pterm_abs t) u) (t[u]).
(* begin hide *)

Lemma term_regular_b: term_regular rule_b.
Proof.
 unfold term_regular.
 intros t t' Hr.
 inversion Hr; subst.
 split.
 - apply term_app.
   + unfold body in H.
     destruct H.
     apply term_abs with x.
     assumption.
   + assumption. 
 - unfold body in H.
   destruct H.
   apply term_sub with x; assumption.
Qed.

(* talvez a forma de evitar os lemas seguintes seja a inclusão de close_rec 
Lemma open_rec_abs: forall t t1 n x, {n ~> pterm_fvar x} t = pterm_abs t1 -> exists u,  t = pterm_abs u.
Proof.
  Admitted.
  
Lemma open_rec_app: forall t t1 t2 n x, {n ~> pterm_fvar x} t = pterm_app t1 t2 -> exists u v,  t = pterm_app u v.
Proof.
  Admitted.
  
Corollary open_rec_app_abs: forall t t1 t2 n x, {n ~> pterm_fvar x} t = pterm_app (pterm_abs t1) t2 -> exists u v,  t = pterm_app (pterm_abs u) v.
Proof.
  intros t0 t1 t2 n x Heq.
  apply open_rec_app in Heq.
  destruct Heq as [u [v]]; subst.
  exists 
  exists (close_rec n x t2).
  (* incluir lema sobre composição entre open_rec e close_rec *)
Admitted.
  *)

Lemma rule_b_compat_open: forall t t' n x, rule_b t t' -> rule_b ({n ~> pterm_fvar x}t) ({n ~> pterm_fvar x}t').
Proof.
  intros t1 t2 n x.
  - intro Hrule_b.
    inversion Hrule_b; subst.
    simpl.
    apply reg_rule_b.
    + unfold body in *.
      destruct  H.
      exists x0. intros x1 Hnotin.
      unfold open.
      apply term_equiv_lc_at.
      apply lc_at_open_rec.
      * apply term_var.
      * apply lc_at_open_rec_leq.
        ** apply Peano.le_n_S.
           apply Peano.le_0_n.
        ** apply  body_lc_at.
           unfold body.
           exists x0; assumption.
    + assert (H' : {n ~> pterm_fvar x} u = u).
      * apply open_rec_term; assumption.
      * rewrite H'; assumption.
Qed.
(* não funciona em termos  
  - intro Hrule_b.
    remember ({n ~> pterm_fvar x} t1) as t.
    remember (({n ~> pterm_fvar x} t2)) as t'. 
    induction Hrule_b.
    generalize dependent x.
    generalize dependent n.
    generalize dependent t2.
    induction t1.
    + intros t2 n' x H.
      simpl in H.
      destruct (n' === n); inversion H.
    + intros t2 n' x H.
      simpl in H; inversion H.
    + intros t2 n' x H.
      simpl in H.
      inversion H; subst.
      rewrite <- H0 in H.
      rewrite <- H2 in H.
      (* here we probably need the close_rec operation *)
      admit.
    + intros t2 n' x H.
      simpl in H; inversion H.
    + intros t2 n' x H.
      simpl in H; inversion H.
Admitted. *)

Lemma open_close_redex: forall t t0 u x y, t^x = pterm_app (pterm_abs t0) u -> t^y = pterm_app ((close (pterm_abs t0) x)^y) (close u x)^y.
Proof.
Admitted.

(** Este lema é falso: tome t como um b-redex contendo n solto. 
Lemma red_out:  forall t t' x n, rule_b ({n ~> pterm_fvar x} t) ({n ~> pterm_fvar x} t') -> rule_b t t'.
Proof.
  induction t.
  - intros t' x n0 H.
    simpl in H.
    destruct (n0 === n); subst.
    + inversion H.
    + inversion H.
  - intros t' x n H.
    simpl in H; inversion H.
  - admit.
  - intros t' x n H.
    simpl in H.
    Admitted. *)

Lemma open_rec_msb: forall t k x y x0, x <> x0 -> [x ~> pterm_fvar y] (open_rec k (pterm_fvar x0) t) = (open_rec k (pterm_fvar x0) ([x ~> pterm_fvar y] t)).
Proof.
  intro t; induction t using pterm_size_induction.
  intros k x y x0 Hdiff.
  generalize dependent t0.
  intro t; case t.
  - intros n IH.
    admit.
  - intros v IH.
    admit.
  - intros t1 t2 IH.
    admit.
  - intros t1 IH.
    simpl in *.
    rewrite IH.
    + reflexivity.
    + admit.
    + assumption.
Admitted.

Corollary open_msb: forall t x y x0, x <> x0 -> [x ~> pterm_fvar y] t ^ x0 = ([x ~> pterm_fvar y] t) ^ x0.
Proof.
  intros t x y x0 Hdiff.
  apply open_rec_msb; assumption.
Qed.
  
Lemma term_rename: forall t x y, term t -> term ([x ~> pterm_fvar y] t).
Proof.
  intros t x y H; induction H.
  - admit.
  - admit.
  - simpl.
    apply term_abs with L.
    intros x0 Hnot.
    replace (([x ~> pterm_fvar y] t1) ^ x0) with ([x ~> pterm_fvar y] (t1 ^ x0)).
    + apply H0; assumption.
    + assert (Hdiff: x <> x0).
      {
        admit.
      }
      apply open_msb; assumption.
  - Admitted.

Lemma body_rename: forall t x y, body t -> body ([x ~> pterm_fvar y] t).
Proof.
  intros t x y Hbody.
  unfold body in *.
  destruct Hbody.
  exists x0.
  pick_fresh z.
  intros x1 Hnot. 
  replace (([x ~> pterm_fvar y] t) ^ x1) with ([x ~> (pterm_fvar y)^ x1] (t ^ x1)).
  - apply term_rename.
    apply H in Hnot; assumption.
  - Admitted.
 
Lemma red_out:  forall t t' x y, rule_b t t' -> rule_b ([x ~> pterm_fvar y] t) ([x ~> pterm_fvar y] t').
Proof.
  intros t t' x y H.
  inversion H; subst.
  simpl.
  apply reg_rule_b.
  - apply body_rename; assumption.
  - apply term_rename; assumption.
Qed.    
  
Lemma red_rename_b: red_rename rule_b.
Proof.
  unfold red_rename.
  intros x t t' y Hfv Hfv' Hb.
  assert (Hsb: t^y = [x ~> pterm_fvar y] t ^ x).
  {
    symmetry.
    apply m_sb_intro; assumption.
  }
  rewrite Hsb.
  assert (Hsb': t' ^ y = [x ~> pterm_fvar y] t' ^ x).
  {
    symmetry.
    apply m_sb_intro_open; assumption.
  }
  rewrite Hsb'.
  apply red_out; assumption.
Qed.  

  (* generalize dependent t'. *)
  (* generalize dependent y. *)
  (* generalize dependent x. *)
  (* induction t. *)
  (* - intros x Hfvx y t' Hfvt' Hbx. *)
  (*   admit. *)
  (* - admit. *)
  (* - intros x Hfvx y t' Hfvt' Hbx. *)
  (*   admit. *)
  (* - intros x Hfvx y t' Hfvt' Hbx. *)
    
  (* unfold open in *. *)
  (* apply rule_b_compat_open. *)


  (* inversion Hb; subst. *)
  (* symmetry in H. *)
  (* assert (Hy : t^y = pterm_app ((close (pterm_abs t0) x)^y) (close u x)^y). *)
  (* { *)
  (*   apply open_close_redex; assumption. *)
  (* } *)

  (* Admitted. *)
(*   rewrite open_close_term. *)
(*   (* escrever o lema open_close_redex *) *)

(*   generalize dependent x. *)
(*   generalize dependent y. *)
(*   generalize dependent t'. *)
(*   induction t. *)
(*   - case n. *)
(*     + intros t y x Hfv1 Hfv2 Hb. *)
(*       simpl in Hb. *)
(*       inversion Hb. *)
(*     + intros n' t y x Hfv1 Hfv2 Hb. *)
(*       simpl in Hb. *)
(*       inversion Hb. *)
(*   - intros t y x Hfv1 Hfv2 Hb. *)
(*     simpl in Hb. *)
(*     inversion Hb. *)
(*   - intros t y x Hfv1 Hfv2 Hb. *)
(*     simpl in *. *)
(*   - *)
(*   - *)

(*   apply rule_b_compat_open in Hb. *)
(*   apply rule_b_compat_open; assumption. *)
(* Qed. *)

(* end hide *)
Definition b_ctx t u := ES_contextual_closure rule_b t u. 
Notation "t ->_B u" := (b_ctx t u) (at level 66).
(* begin hide *)
Corollary term_regular_b_ctx : term_regular b_ctx.
Proof.
  apply term_regular_ctx.
  apply term_regular_b.
Qed.

Lemma red_rename_b_ctx: red_rename b_ctx.
Proof.
  unfold red_rename.
  intros x t t' y Ht Ht' HB.
Admitted.
(* Lemma eqC_preserves_redex: forall t1 t2 u, pterm_app (pterm_abs t2) u =e t1 -> exists t v, t1 = pterm_app (pterm_abs t) v.
Proof.
Admitted.

Lemma eqC_preserves_sub: forall t1 t2 u,  (t1 [t2]) =e u -> exists t v, u = (t [ v ]).
Proof.
Admitted. *)
  
(* Instance rw_eqC_B : Proper (eqC ==> eqC ==> iff) b_ctx. *)
(* Proof. *)
(*   intros x x' H u u' H'; split. *)
(*   - intro HB. *)
(*     Admitted. *)
  (*   inversion HB; subst. *)
  (*   + inversion H0; subst. *)
  (*     inversion H; subst. *)
  (*     * inversion H'; subst. *)
  (*       ** apply ES_redex. *)
  (*          apply reg_rule_b; assumption. *)
  (*       ** destruct H'. *)
  (*          *** apply ES_redex. *)
  (*              assumption. *)
  (*          *** *)
  (*     * *)
  (*   generalize dependent x'. *)
  (*   generalize dependent u'. *)
  (*   induction HB. *)
  (*   + intros t1' Heq1 t1 Heq2. *)
  (*     inversion H; subst. *)
  (*     apply eqC_preserves_redex in Heq2. *)
  (*     destruct Heq2 as [t [v H']]. *)
  (*     rewrite H'. *)
  (*     apply eqC_preserves_sub in Heq1. *)
  (*     destruct Heq1 as [t' [v' H'']]. *)
  (*     rewrite H''. *)
  (*     apply ES_redex. *)
  (*     admit. *)
  (*   + admit. *)
  (*   + admit. *)
  (*   + admit. *)
  (*   + admit. *)
  (*   + admit. *)
  (* - Admitted. *)
   
(* end hide *)  
Inductive sys_x : Rel pterm :=
| reg_rule_var : forall t, term t -> sys_x (pterm_bvar 0 [t]) t
| reg_rule_gc : forall t u, term t -> term u -> sys_x (t[u]) t
| reg_rule_app : forall t1 t2 u, body t1 -> body t2 -> term u ->
  sys_x ((pterm_app t1 t2)[u]) (pterm_app (t1[u]) (t2[u]))
| reg_rule_abs : forall t u, lc_at 2 t -> term u ->
  sys_x ((pterm_abs t)[u]) (pterm_abs ((& t)[u]))
| reg_rule_comp : forall t u v, lc_at 2 t -> has_free_index 0 u ->
                           lc_at 1 u -> term v ->
  sys_x (t[u][v]) (((& t)[v])[ u[ v ] ]).
(* begin hide *)
Lemma term_regular_sys_x: term_regular sys_x.
Proof.
  intros t u Hsys.
  induction Hsys.
  - split.
    + apply term_sub with (fv t).
      * intros x Hfv.
        unfold open; simpl.
        apply term_var.
      * assumption.
    + assumption.
  - split.
    + apply term_sub with (fv t).
      * intros x Hfv.
        unfold open; simpl.
        rewrite open_rec_term; assumption.
      * assumption.
    + assumption.    
  - unfold body in *.
    destruct H.
    destruct H0.
    split.
    + apply term_sub with (x \u x0).
      * intros x' Hfv.
        apply notin_union in Hfv.
        destruct Hfv as [Hx Hx0].
        unfold open; simpl.
        apply term_app.
        ** apply H in Hx; assumption.
        ** apply H0 in Hx0; assumption.
      * assumption.
    + apply term_app.
      * apply term_sub with x; assumption.
      * apply term_sub with x0; assumption.
  - split.
    + apply term_sub with (fv (pterm_abs t)).
      * intros x Hnot.
        apply body_to_term.
        **  assumption.
        **  apply body_lc_at.
            apply H.
      * assumption.
    + apply term_abs with (fv (& t[u])).
      intros x Hnot.
      apply body_to_term.
      * assumption.
      * apply body_lc_at.
        split.
        **  clear x u H0 Hnot.
            apply lc_at_bswap_rec.
            *** auto.
            *** assumption.
        **  apply lc_at_weaken_ind with 0.
            *** apply term_to_lc_at; assumption.
            *** auto with arith.
  - split.
    + apply term_sub with (fv (t[u])).
      * intros x Hnot.
        apply body_to_term.
        **  assumption.
        **  apply body_lc_at.
            split; assumption.
      * assumption.
    + apply term_sub with (fv (& t[v])).
      * intros x Hnot.
        apply body_to_term.
        **  assumption.
        **  apply body_lc_at.
            split.
            *** clear u v H0 H1 H2 x Hnot.
                apply lc_at_bswap_rec.
                ****  auto.
                ****  assumption.
            *** apply lc_at_weaken_ind with 0.
                ****  apply term_equiv_lc_at; assumption.
                **** auto with arith.
      * apply term_sub with (fv u).
        **  intros x Hnot.
            apply body_to_term.
            *** assumption.
            *** apply body_lc_at; assumption.
        **  assumption.
Qed.

Definition x_ctx t u := ES_contextual_closure sys_x t u. 
Notation "t ->_x u" := (x_ctx t u) (at level 59, left associativity).

(** avaliar *)

Lemma red_rename_x_ctx: red_rename x_ctx.
Proof.
  unfold red_rename.
  intros x t t' y Ht Ht' HX.
Admitted.

Corollary term_regular_x_ctx : term_regular x_ctx.
Proof.
  apply term_regular_ctx.
  apply term_regular_sys_x.
Qed.

Inductive lx: Rel pterm :=
| b_ctx_rule : forall t u, t ->_B u -> lx t u
| x_ctx_rule : forall t u, t ->_x u -> lx t u.
Notation "t ->_Bx u" := (lx t u) (at level 59, left associativity).
Notation "t ->_lx* u" := ((refltrans lx) t u) (at level 59, left associativity).

Lemma red_rename_lx: red_rename lx.
Proof.
  unfold red_rename.
  intros x t t' y Ht Ht' Hlx.
  inversion Hlx; subst.
  - apply b_ctx_rule.
    generalize x t t' y Ht Ht' H.
    apply red_rename_b_ctx.
  - apply x_ctx_rule.
    generalize x t t' y Ht Ht' H.
    apply red_rename_x_ctx.
Qed.

Lemma Bx_app_left: forall t1 t2 t3, term t3 -> t1 ->_Bx t2 -> pterm_app t1 t3 ->_Bx pterm_app t2 t3.
Proof.
  intros t1 t2 t3 Hterm HBx.
  inversion HBx; subst.
  - apply b_ctx_rule.
    apply ES_app_left; assumption.
  - apply x_ctx_rule.
    apply ES_app_left; assumption.
Qed.

Lemma Bx_app_right: forall t1 t2 t3, term t1 -> t2 ->_Bx t3 -> pterm_app t1 t2 ->_Bx pterm_app t1 t3.
Proof.
  intros t1 t2 t3 Hterm HBx.
  inversion HBx; subst.
  - apply b_ctx_rule.
    apply ES_app_right; assumption.
  - apply x_ctx_rule.
    apply ES_app_right; assumption.
Qed.

Lemma Bx_abs: forall t1 t2 L, (forall x, x \notin L -> t1^x ->_Bx t2^x) -> pterm_abs t1 ->_Bx pterm_abs t2.
Proof.
  intros t1 t2 L HBx.
  pick_fresh x.
  apply notin_union in Fr.
  destruct Fr as [Fr Fvt2].
  apply notin_union in Fr.
  destruct Fr as [Fr Fvt1].
  apply HBx in Fr.
  inversion Fr; subst.
  - clear Fr.
    apply b_ctx_rule.
    apply ES_abs_in with (fv t1 \u fv t2).
    intros x' HL.
    generalize H.
    apply red_rename_b_ctx; assumption.
  - apply x_ctx_rule.
    apply ES_abs_in with (fv t1 \u fv t2).
    intros.
    generalize H.
    apply red_rename_x_ctx; assumption.
Qed.

Lemma Bx_sub: forall t1 t2 t3 L, (forall x, x \notin L -> t1^x ->_Bx t2^x) -> term t3 -> pterm_sub t1 t3 ->_Bx pterm_sub t2 t3.
Proof.
  intros t1 t2 t3 L HBx Hterm.
  pick_fresh x.
  apply notin_union in Fr.
  destruct Fr as [Fr Fvt3].
  apply notin_union in Fr.
  destruct Fr as [Fr Fvt2].
  apply notin_union in Fr.
  destruct Fr as [Fr Fvt1].
  apply HBx in Fr.
  clear Fvt3.
  inversion Fr; subst.
  - apply b_ctx_rule.
    apply ES_sub with L.
    + intros x' Hnot.
      generalize H.
      apply red_rename_b_ctx; assumption.
    + assumption.
  - apply x_ctx_rule.
    apply ES_sub with L.
    + intros x' Hnot.
      generalize H.
      apply red_rename_x_ctx; assumption.
    + assumption.
Qed.

Lemma Bx_sub_in: forall t1 t2 t3, body t1 -> t2 ->_Bx t3 -> pterm_sub t1 t2 ->_Bx pterm_sub t1 t3.
Proof.
  intros t1 t2 t3 Hbody HBx.
  inversion HBx; subst.
  - apply b_ctx_rule.
    apply ES_sub_in; assumption.
  - apply x_ctx_rule.
    apply ES_sub_in; assumption.
Qed.

Lemma lx_star_app_left: forall t1 t2 t3, term t3 -> t1 ->_lx* t2 -> pterm_app t1 t3 ->_lx* pterm_app t2 t3.
Proof.
  intros t1 t2 t3 Hterm Hlx.
  induction Hlx.
  - apply refl.
  - apply rtrans with (pterm_app b t3).
    + apply Bx_app_left; assumption.
    + assumption.
Qed.

Lemma lx_star_app_right: forall t1 t2 t3, term t1 -> t2 ->_lx* t3 -> pterm_app t1 t2 ->_lx* pterm_app t1 t3.
Proof.
  intros t1 t2 t3 Hterm Hlx.
  induction Hlx.
  - apply refl.
  - apply rtrans with (pterm_app t1 b).
    + apply Bx_app_right; assumption.
    + assumption.
Qed.

Lemma lx_star_abs: forall t1 t2 L, (forall x, x \notin L -> t1^x ->_lx* t2^x) -> pterm_abs t1 ->_lx* pterm_abs t2.
Proof.
  intros t1 t2 L Hlx.
  pick_fresh x.
  apply notin_union in Fr.
  destruct Fr as [Fr Fvt2].
  apply notin_union in Fr.
  destruct Fr as [Fr Fvt1].
  apply Hlx in Fr.
  clear Hlx Fvt1 Fvt2.
Admitted.

Lemma lx_star_sub: forall t1 t2 t3 L, (forall x, x \notin L -> t1^x ->_lx* t2^x) -> term t3 -> pterm_sub t1 t3 ->_lx* pterm_sub t2 t3.
Proof.
  intros t1 t2 t3 L Hlx Hterm.
  pick_fresh x.
  apply notin_union in Fr.
  destruct Fr as [Fr Fvt3].
  apply notin_union in Fr.
  destruct Fr as [Fr Fvt2].
  apply notin_union in Fr.
  destruct Fr as [Fr Fvt1].
  apply Hlx in Fr.
  clear Fvt1 Fvt2 Fvt3.
Admitted.

Lemma lx_star_sub_in: forall t1 t2 t3, body t1 -> t2 ->_lx* t3 -> pterm_sub t1 t2 ->_lx* pterm_sub t1 t3.
Proof.
  intros t1 t2 t3 Hbody Hlx.
  induction Hlx.
  - apply refl.
  - apply rtrans with (t1 [b]).
    + apply Bx_sub_in; assumption.
    + assumption.
Qed.

(* Lemmas provados baseados em versões antigas de lemmas anteriores
Lemma lx_star_abs: forall t1 t2, t1 ->_lx* t2 -> pterm_abs t1 ->_lx* pterm_abs t2.
Proof.
  intros t1 t2 Hlx.
  induction Hlx.
  - apply refl.
  - apply rtrans with (pterm_abs b).
    + apply Bx_abs; assumption.
    + assumption.
Qed.

Lemma lx_star_sub: forall t1 t2 t3, term t3 -> t1 ->_lx* t2 -> pterm_sub t1 t3 ->_lx* pterm_sub t2 t3.
Proof.
  intros t1 t2 t3 Hterm Hlx.
  induction Hlx.
  - apply refl.
  - apply rtrans with (b [t3]).
    + apply Bx_sub; assumption.
    + assumption.
Qed.*)

Instance rw_eqC_lx : Proper (eqC ==> eqC ==> iff) lx.
Proof.
  intros x x' H u u' H'.
  split.
  - intro HBx.
    generalize dependent x'.
    generalize dependent u'.
    induction HBx.
    + intros.
      apply b_ctx_rule.
      admit.
    + admit.
  - Admitted.

(*
Lemma Bx_app_left: forall t t' u, term u -> t ->_Bx t' -> pterm_app t u ->_Bx pterm_app t' u. 
Proof.
  intros t t' u HBx.
  inversion HBx; subst; clear HBx.
  - apply b_ctx_rule.
    apply ES_app_left. assumption.
  - apply x_ctx_rule.
    apply ES_app_left; assumption.
Qed.    

Lemma Bx_app_right: forall u u' t, u ->_Bx u' -> pterm_app t u ->_Bx pterm_app t u'. 
Proof.
  intros u u' t HBx.
  inversion HBx; subst; clear HBx.
  - apply b_ctx_rule.
    apply ES_app_right; assumption.
  - apply x_ctx_rule.
    apply ES_app_right; assumption.
Qed. *)    

(*
Lemma Bx_sub: forall t t' u L, (forall x, x \notin L -> t^x ->_Bx t'^x) -> (t[u]) ->_Bx (t'[u]). 
Proof.
  intros t t' u L H.
  pick_fresh y.
  apply notin_union in Fr.
  destruct Fr as [Fr Hu].
  apply notin_union in Fr.
  destruct Fr as [Fr Ht'].
  apply notin_union in Fr.
  destruct Fr as [Fr Ht].
  apply H in Fr.
  inversion Fr; subst; clear Fr.
  - apply b_ctx_rule.
    apply ES_sub with (fv t).
    intros x Hfv.
Admitted. 

Lemma Bx_sub_in: forall u u' t, u ->_Bx u' -> (t[u]) ->_Bx (t[u']). 
Proof.
  intros u u' t HBx.
  inversion HBx; subst; clear HBx.
  - apply b_ctx_rule.
    apply ES_sub_in; assumption.
  - apply x_ctx_rule.
    apply ES_sub_in; assumption.
Qed. *)   

Corollary term_regular_lx: term_regular lx.
Proof.
  unfold term_regular.
  intros t t' HBx.
  induction HBx.
  - apply term_regular_b_ctx; assumption.
  - apply term_regular_x_ctx; assumption.
Qed.
    
(* Definition trans_x t u := trans x_ctx t u.
Notation "t ->_x+ u" := (trans_x t u) (at level 59, left associativity).
  
Lemma x_trans_app_left: forall t t' u, t ->_x+ t' -> pterm_app t u ->_x+ pterm_app t' u. 
Proof.
  intros t t' u Hx.
  induction Hx.
  - apply singl.
    apply ES_app_left; assumption.
  - apply transit with (pterm_app b u).
    + apply ES_app_left; assumption.
    + assumption.    
Qed. 

Lemma x_trans_app_right: forall  u u' t, u ->_x+ u' -> pterm_app t u ->_x+ pterm_app t u'. 
Proof.
  intros u u' t Hx.
  induction Hx.
  - apply singl.
    apply ES_app_right; assumption.
  - apply transit with (pterm_app t b).
    + apply ES_app_right; assumption.
    + assumption.    
Qed. *)   

(* Lemma x_trans_sub: forall t t' u L, (forall x, x \notin L -> t^x ->_x+ t'^x) -> (t[u]) ->_x+ (t'[u]). 
Proof.
Admitted.

Lemma x_trans_sub_in: forall u u' t, u ->_x+ u' -> (t[u]) ->_x+ (t[u']). 
Proof.
  intros u u' t Hred.
  induction Hred.
  - apply singl.
    apply ES_sub_in; assumption.
  - apply transit with (t[b]). 
    + apply ES_sub_in; assumption.
    + assumption.
Qed.
    
Corollary term_regular_trans_x: term_regular trans_x.
Proof.
  apply term_regular_trans.
  apply term_regular_x_ctx.
Qed. *)

Definition ex t u := red_ctx_mod_eqC x_ctx t u.
Notation "t ->_ex u" := (ex t u) (at level 59, left associativity).

(* Lemma ex_app_left: forall t t' u, t ->_ex t' -> pterm_app t u ->_ex pterm_app t' u. 
Proof.
  intros t t' u Hex.
  inversion Hex; subst; clear Hex.
  destruct H as [v [Heq [Hx Heq']]].
  unfold ex. unfold red_ctx_mod_eqC.
  exists (pterm_app x u).
  exists (pterm_app v u).
  split.
  - rewrite Heq; apply refl.
  - split.
    + apply ES_app_left; assumption.      
    + rewrite Heq'; apply refl.
Qed. 

Lemma ex_app_right: forall u u' t, u ->_ex u' -> pterm_app t u ->_ex pterm_app t u'. 
Proof.
  intros u u' t Hex.
  inversion Hex; subst; clear Hex.
  destruct H as [v [Heq [Hx Heq']]].
  unfold ex. unfold red_ctx_mod_eqC.
  exists (pterm_app t x).
  exists (pterm_app t v).
  split.
  - rewrite Heq; apply refl.
  - split.
    + apply ES_app_right; assumption.      
    + rewrite Heq'; apply refl.
Qed. *)

(*
Lemma ex_sub: forall t t' u L, (forall x, x \notin L -> t^x ->_ex t'^x) -> (t[u]) ->_ex (t'[u]). 
Proof.
Admitted.

Lemma ex_sub_in: forall u u' t, u ->_ex u' -> (t[u]) ->_ex (t[u']). 
Proof.
  intros u u' t Hred.
  unfold ex in *.
  unfold red_ctx_mod_eqC in *.
  destruct Hred as [v [v' [Heq [Hx Heq']]]].
  exists (t[v]). exists (t[v']). split.
  - rewrite Heq.
    apply refl.
  - split.
    + apply ES_sub_in.
      * assumption.
      * admit.
    + rewrite Heq'.
      apply refl.
Admitted.
 *)

Corollary term_regular_ex: term_regular ex.
Proof.
  unfold term_regular.
  intros t t' Hex.
  apply term_regular_red_ctx_mod_eqC in Hex.
  - assumption.
  - apply term_regular_x_ctx.
Qed.
  
Definition trans_ex t u := trans ex t u.
Notation "t ->_ex+ u" := (trans_ex t u) (at level 59, left associativity).

(* Lemma ex_trans_app_left: forall t t' u, t ->_ex+ t' -> pterm_app t u ->_ex+ pterm_app t' u. 
Proof.
  intros t t' u Hex.
  induction Hex.
  - apply singl.
    apply ex_app_left; assumption.
  - apply transit with (pterm_app b u).
    + apply ex_app_left; assumption.
    + assumption.
Qed.

Lemma ex_trans_app_right: forall u u' t, u ->_ex+ u' -> pterm_app t u ->_ex+ pterm_app t u'. 
Proof.
  intros u u' t Hex.
  induction Hex.
  - apply singl.
    apply ex_app_right; assumption.
  - apply transit with (pterm_app t b).
    + apply ex_app_right; assumption.
    + assumption.
Qed. 

Corollary ex_trans_app: forall t t' u u', t ->_ex+ t' -> u ->_ex+ u' -> pterm_app t u ->_ex+ pterm_app t' u'. 
Proof.
  intros t t' u u' Ht Hu.
  apply trans_composition with (pterm_app t' u).
  apply ex_trans_app_left; assumption.
  apply ex_trans_app_right; assumption.
Qed.

Lemma ex_trans_abs: forall t t', t ->_ex+ t' -> (pterm_abs t) ->_ex+ (pterm_abs t'). 
Proof.
Admitted. *)

(* Lemma ex_trans_sub: forall t t' u L, (forall x, x \notin L -> t^x ->_ex+ t'^x) -> (t[u]) ->_ex+ (t'[u]). 
Proof.
Admitted.

Lemma ex_trans_sub_in: forall u u' t, u ->_ex+ u' -> (t[u]) ->_ex+ (t[u']).
Proof.
  intros u u' t Hex.
  induction Hex.
  - apply singl.
    apply ex_sub_in; assumption.
  - apply transit with (t[b]).
    + apply ex_sub_in; assumption.            
    + assumption.    
Qed. *)
  
Corollary term_regular_trans_ex : term_regular trans_ex.
Proof.
  apply term_regular_trans.
  apply term_regular_ex.
Qed.

Lemma full_comp: forall t u, body t -> term u -> t[u] ->_ex+ (t ^^ u). 
Proof.
  intros t u Hbody.
  generalize dependent u.
  generalize dependent Hbody.
  induction t using pterm_size_induction.
  generalize dependent H.
  case t0.
  - intros n IH Hbody u Hu.
    generalize dependent IH.
    generalize dependent Hbody.
    destruct n.
    + intros Hbody IH.
      unfold open.
      simpl.
      apply singl.
      unfold ex.
      unfold red_ctx_mod_eqC.
      exists (pterm_bvar 0 [u]).
      exists u. split.
      * reflexivity.
      * split.
        ** unfold x_ctx.
           apply ES_redex.
           apply reg_rule_var.
           assumption.
        ** reflexivity.
    + intros Hbody IH.
      unfold open.
      simpl.
      Admitted.
  (*   + intros Hbody IH. *)
  (*     unfold open. *)
  (*     simpl. *)
  (*     apply singl. *)
  (*     unfold ex. *)
  (*     unfold red_ctx_mod_eqC. *)
  (*     exists (pterm_bvar (S n) [u]). *)
  (*     exists (pterm_bvar (S n)). *)
  (*     split. *)
  (*     * reflexivity. *)
  (*     * split. *)
  (*       ** unfold x_ctx. *)
  (*          apply ES_redex. *)
  (*          apply reg_rule_gc. *)
  (*          intro H. *)
  (*          inversion H. *)
  (*       ** reflexivity. *)
  (* - intros v IH Hbody u Hterm. *)
  (*   unfold open; simpl. *)
  (*   apply singl. *)
  (*   unfold ex. *)
  (*   unfold red_ctx_mod_eqC. *)
  (*   exists (pterm_fvar v [u]). *)
  (*   exists (pterm_fvar v). *)
  (*   split. *)
  (*   + reflexivity. *)
  (*   + split. *)
  (*     * unfold x_ctx. *)
  (*       apply ES_redex. *)
  (*       apply reg_rule_gc. *)
  (*       intro H. *)
  (*       inversion H. *)
  (*     * reflexivity. *)
  (* - intros t1 t2 IH Hbody u Hterm. *)
  (*   apply transit with (pterm_app (t1[u]) (t2[u])). *)
  (*   + unfold ex. *)
  (*     unfold red_ctx_mod_eqC. *)
  (*     exists (pterm_app t1 t2 [u]). *)
  (*     exists (pterm_app (t1 [u]) (t2 [u])). *)
  (*     split. *)
  (*     * reflexivity. *)
  (*     * split. *)
  (*       ** unfold x_ctx. *)
  (*          apply ES_redex. *)
  (*          apply reg_rule_app. *)
  (*       ** reflexivity. *)
  (*   + unfold open. simpl. *)
  (*     apply body_app in Hbody. *)
  (*     destruct Hbody as [Hbody1 Hbody2]. *)
  (*     apply ex_trans_app. *)
  (*     * apply IH. *)
  (*       ** simpl. *)
  (*          rewrite <- Nat.add_succ_r. *)
  (*          apply Nat.lt_add_pos_r. *)
  (*          apply Nat.lt_0_succ. *)
  (*       ** assumption. *)
  (*       ** assumption. *)
  (*     * apply IH. *)
  (*       ** simpl. *)
  (*          rewrite <- Nat.add_succ_l. *)
  (*          rewrite plus_comm. *)
  (*          apply Nat.lt_add_pos_r. *)
  (*          apply Nat.lt_0_succ. *)
  (*       ** assumption. *)
  (*       ** assumption. *)
  (* - intros t1 IH Hbody u Hterm. *)
  (*   apply transit with (pterm_abs ((&t1)[u])). *)
  (*   + unfold ex. *)
  (*     unfold red_ctx_mod_eqC. *)
  (*     exists (pterm_abs t1 [u]). *)
  (*     exists (pterm_abs ((& t1) [u])). *)
  (*     split. *)
  (*     * reflexivity. *)
  (*     * split. *)
  (*       ** apply ES_redex. *)
  (*          apply reg_rule_abs. *)
  (*       ** reflexivity. *)
  (*   + unfold open. *)
  (*     simpl. *)
  (*     unfold open in IH. *)
  (*     assert (IH':= IH (& t1)). *)
  (*     assert (H: ({0 ~> u} (& t1)) = ({1 ~> u} t1)). *)
  (*     { *)
  (*       admit. *)
  (*     } *)
  (*     rewrite <- H. *)
  (*     apply ex_trans_abs. *)
  (*     apply IH'. *)
  (*     admit. *)
(*
          apply reg_rule_var.
        ** reflexivity.
    + intros Hbody IH.
      unfold open.
      simpl.
      apply singl.
      unfold ex.
      unfold red_ctx_mod_eqC.
      exists (pterm_bvar (S n) [u]).
      exists (pterm_bvar (S n)).
      split.
      * reflexivity.
      * split.
        ** unfold x_ctx.
           apply ES_redex.
           apply reg_rule_gc.
           intro H.
           inversion H.
        ** reflexivity.
  - intros v IH Hbody u Hterm.
    unfold open; simpl.
    apply singl.
    unfold ex.
    unfold red_ctx_mod_eqC.
    exists (pterm_fvar v [u]).
    exists (pterm_fvar v).
    split.
    + reflexivity.
    + split.
      * unfold x_ctx.
        apply ES_redex.
        apply reg_rule_gc.
        intro H.
        inversion H.
      * reflexivity.
  - intros t1 t2 IH Hbody u Hterm.
    apply transit with (pterm_app (t1[u]) (t2[u])).
    + unfold ex.
      unfold red_ctx_mod_eqC.
      exists (pterm_app t1 t2 [u]).
      exists (pterm_app (t1 [u]) (t2 [u])).
      split.
      * reflexivity.
      * split.
        ** unfold x_ctx.
           apply ES_redex.
           apply reg_rule_app.
        ** reflexivity.
    + unfold open. simpl.
      apply body_app in Hbody.
      destruct Hbody as [Hbody1 Hbody2].
      apply ex_trans_app.
      * apply IH.
        ** simpl.
           rewrite <- Nat.add_succ_r.
           apply Nat.lt_add_pos_r.
           apply Nat.lt_0_succ.
        ** assumption.
        ** assumption.
      * apply IH.
        ** simpl.
           rewrite <- Nat.add_succ_l.
           rewrite plus_comm.
           apply Nat.lt_add_pos_r.
           apply Nat.lt_0_succ.
        ** assumption.
        ** assumption.
  - intros t1 IH Hbody u Hterm.
    apply transit with (pterm_abs ((&t1)[u])).
    + admit.
    + apply ex_trans_abs with (fv t1).
      
        admit. *)

    (* case n. *)
    (* + intros Hbody u. *)
    (*   unfold open; simpl. *)
    (*   apply singl. *)
    (*   unfold ex. *)
    (*   unfold red_ctx_mod_eqC. *)
    (*   exists (pterm_bvar 0 [u]). *)
    (*   exists u. split. *)
    (*   * reflexivity. *)
    (*   * split. *)
    (*     ** apply ES_redex. *)
    (*        apply reg_rule_var. *)
    (*     ** reflexivity. *)
    (* + intros n' Hbody u. *)
    (*   unfold body in Hbody. *)
    (*   destruct Hbody. *)
    (*   pick_fresh x0. *)
    (*   apply notin_union in Fr. *)
    (*   destruct Fr as [Fr Hu]. *)
    (*   apply notin_union in Fr. *)
    (*   destruct Fr as [Fr Hn']. *)
    (*   apply notin_union in Fr. *)
    (*   destruct Fr as [Fr Hn]. *)
    (*   apply H0 in Fr. *)
    (*   unfold open in Fr; simpl in Fr. *)
    (*   inversion Fr. *)

    (* intros Hbody u. *)
    (* apply singl. *)
    (* unfold ex. *)
    (* unfold red_ctx_mod_eqC. *)
    (* exists (pterm_fvar v [u]). *)
    (* exists (pterm_fvar v); split. *)
    (* + reflexivity. *)
    (* + split. *)
    (*   * apply ES_redex. *)
    (*     apply reg_rule_gc. *)
    (*     apply term_var. *)
    (*   * unfold open; reflexivity. *)
 
    (* intro H0. *)
    (* unfold open. *)
    (* simpl. *)
    (* intro u. *)
    (* apply transit with  (pterm_app (t0_1[u]) (t0_2[u]) ). *)
    (* unfold ex. *)
    (* unfold red_ctx_mod_eqC. *)
    (* exists  (pterm_app t0_1 t0_2 [u]). *)
    (* exists (pterm_app (t0_1 [u]) (t0_2 [u])); split. *)
    (* + reflexivity. *)
    (* + split. *)
    (*   * apply ES_redex. *)
    (*     apply reg_rule_app. *)
    (*   * reflexivity. *)
    (* + unfold body in H. *)
    (*   destruct H0. *)
    (*   apply ex_trans_app. *)
    (*   * apply IHt0_1. *)
    (*     unfold body. *)
    (*     intros t Hlt IH u0. *)
    (*     exists x. *)
    (*     intros x1 Hx1. *)
    (*     apply H in Hx1. *)
    (*     unfold open in Hx1. *)
    (*     inversion Hx1; subst. *)
    (*     assumption. *)
    (*   * apply IHt2. *)
    (*     unfold body. *)
    (*     exists x. *)
    (*     intros x1 Hx1. *)
    (*     apply H in Hx1. *)
    (*     unfold open in Hx1. *)
    (*     inversion Hx1; subst. *)
    (*     assumption. *)

    (* - intros t IH Hbody u Hu. *)
  (*   apply transit with (pterm_abs ((& t) [u])). *)
  (*   + unfold ex. *)
  (*     unfold red_ctx_mod_eqC. *)
  (*     exists ((pterm_abs t) [u]). *)
  (*     exists  (pterm_abs ((& t) [u])); split. *)
  (*     * reflexivity. *)
  (*     * split. *)
  (*       ** apply ES_redex. *)
  (*          apply reg_rule_abs. *)
  (*       ** reflexivity. *)
  (*   + unfold open; simpl. *)
  (*     apply ex_trans_abs with (fv t). *)
  (*     intros x Hfv. *)
  (*     unfold open. *)
  (*     simpl. *)
  (*     assert (H1: ({0 ~> pterm_fvar x} ({1 ~> u} t)) = ({0 ~> u}({1 ~> pterm_fvar x} (& t)))). *)
  (*     { apply bswap_commute; assumption. } *)
  (*     rewrite H1. *)
  (*     assert (H2: {1 ~> pterm_fvar x} (& t) = {0 ~> pterm_fvar x} t). *)
  (*     { admit. } *)
  (*     rewrite H2. *)
  (*     assert (H3: {0 ~> pterm_fvar x} u = u). *)
  (*     { admit. } *)
  (*     rewrite H3. *)
  (*     unfold open in IH. *)
  (*     apply IH. *)
  (*     * admit. *)
  (*     * admit. *)
  (*     * assumption. *)
    (* - Admitted. *)

Definition lex t u := red_ctx_mod_eqC lx t u.
Notation "t ->_lex u" := (lex t u) (at level 59, left associativity).

(* Lemma lex_app_left: forall t t' u, t ->_lex t' -> pterm_app t u ->_lex pterm_app t' u. 
Proof.
  intros t t' u Hlex.
  inversion Hlex; clear Hlex.
  destruct H as [v [Heq [HBx Heq']]].
  unfold lex. unfold red_ctx_mod_eqC.
  exists (pterm_app x u).
  exists (pterm_app v u).
  split.
  - rewrite Heq; apply refl.
  - split.
    + apply Bx_app_left; assumption.
    + rewrite Heq'; apply refl.
Qed.

Lemma lex_app_right: forall u u' t, u ->_lex u' -> pterm_app t u ->_lex pterm_app t u'. 
Proof.
  intros u u' t Hlex.
  inversion Hlex; clear Hlex.
  destruct H as [v [Heq [HBx Heq']]].
  unfold lex. unfold red_ctx_mod_eqC.
  exists (pterm_app t x).
  exists (pterm_app t v).
  split.
  - rewrite Heq; apply refl.
  - split.
    + apply Bx_app_right; assumption.
    + rewrite Heq'; apply refl.
Qed. *)

(* Lemma lex_sub: forall t t' u L, (forall x, x \notin L -> t^x ->_lex t'^x) -> (t[u]) ->_lex (t'[u]). 
Proof.
Admitted. 

Lemma lex_sub_in: forall u u' t, u ->_lex u' -> (t[u]) ->_lex (t[u']).
Proof.
  intros u u' t Hlex.
  unfold lex in *.
  unfold red_ctx_mod_eqC in *.
  destruct Hlex as [v [v' [Heq [HBx Heq']]]].
  exists (t[v]). exists (t[v']). split.
  - rewrite Heq.
    apply refl.
  - split.
    + apply Bx_sub_in; assumption.
    + rewrite Heq'.
      apply refl.
Qed. *)     
    
Corollary term_regular_lex : term_regular lex.
Proof.
  apply term_regular_red_ctx_mod_eqC.
  apply term_regular_lx.
Qed.
  
Definition trans_lex t u := trans lex t u.
Notation "t ->_lex+ u" := (trans_lex t u) (at level 59, left associativity).

(* Lemma lex_trans_app_left: forall t t' u, t ->_lex+ t' -> pterm_app t u ->_lex+ pterm_app t' u. 
Proof.
  intros t t' u Hlex.
  induction Hlex.
  - apply singl.
    apply lex_app_left; assumption.
  - apply transit with (pterm_app b u).
    + apply lex_app_left; assumption.
    + assumption.
Qed.

Lemma lex_trans_app_right: forall u u' t, u ->_lex+ u' -> pterm_app t u ->_lex+ pterm_app t u'. 
Proof.
  intros u u' t Hlex.
  induction Hlex.
  - apply singl.
    apply lex_app_right; assumption.
  - apply transit with (pterm_app t b).
    + apply lex_app_right; assumption.
    + assumption.
Qed. *)

(* Lemma lex_trans_sub: forall t t' u L, (forall x, x \notin L -> t^x ->_lex+ t'^x) -> (t[u]) ->_lex+ (t'[u]). 
Proof.
Admitted. 

Lemma lex_trans_sub_in: forall u u' t, u ->_lex+ u' -> (t[u]) ->_lex+ (t[u']).
Proof.
  intros u u' t Hlex.
  induction Hlex.
  - apply singl.
    apply lex_sub_in; assumption.
  - apply transit with (t[b]).
    + apply lex_sub_in; assumption.
    + assumption.
Qed. *)

Corollary term_regular_trans_lex : term_regular trans_lex.
Proof.
  apply term_regular_trans.
  apply term_regular_lex.
Qed.
  
Lemma trans_ex_to_lex: forall t u, t ->_ex+ u -> t ->_lex+ u.
Proof.
  intros t u Hex.
  induction Hex.
  - apply singl.
    unfold ex in H.
    unfold lex.
    unfold red_ctx_mod_eqC in *.
    destruct H.
    destruct H.
    exists x.
    exists x0.
    split.
    + apply H.
    + split.
      * apply x_ctx_rule; apply H.
      * apply H.
  - apply transit with b.
    + unfold ex in H.
      unfold lex.
      unfold red_ctx_mod_eqC in *.
      destruct H.
      destruct H.
      exists x.
      exists x0.
      split.
      * apply H.
      * split.
        **  apply x_ctx_rule; apply H.
        **  apply H.
    + assumption.
Qed.

Definition refltrans_lex t u := refltrans lex t u.
Notation "t ->_lex* u" := (refltrans_lex t u) (at level 59, left associativity).

(* Lemma lex_refltrans_app_left: forall t t' u, t ->_lex* t' -> pterm_app t u ->_lex* pterm_app t' u. 
Proof.
  intros t t' u Hlex.
  induction Hlex.
  - apply refl.
  - apply rtrans with (pterm_app b u).
    + apply lex_app_left; assumption.
    + assumption.
Qed.

Lemma lex_refltrans_app_right: forall u u' t, u ->_lex* u' -> pterm_app t u ->_lex* pterm_app t u'. 
Proof.
  intros u u' t Hlex.
  induction Hlex.
  - apply refl.
  - apply rtrans with (pterm_app t b).
    + apply lex_app_right; assumption.
    + assumption.
Qed. *)

(* Lemma lex_refltrans_sub: forall t t' u L, (forall x, x \notin L -> t^x ->_lex* t'^x) -> (t[u]) ->_lex* (t'[u]). 
Proof.
Admitted.

Lemma lex_refltrans_sub_in: forall u u' t, u ->_lex* u' -> (t[u]) ->_lex* (t[u']).
Proof.
  intros u u' t Hlex.
  induction Hlex.
  - apply refl.
  - apply rtrans with (t[b]).
    + apply lex_sub_in; assumption.
    + assumption.
Qed. 
      
Lemma term_regular_refltrans_lex : term_regular refltrans_lex.
Proof.
  unfold term_regular.
  intros t t' Hlex Hterm.
  induction Hlex.
  - assumption.
  - apply IHHlex.
    apply term_regular_lex in H.
    apply H; assumption.
Qed. 

Lemma lex_trans: forall t u v, t ->_lex* u -> u ->_lex* v -> t ->_lex* v.
Proof.
  intros.
  induction H.
   - assumption.
   - apply IHrefltrans in H0.
     apply rtrans with b.
    + assumption.
    + assumption.
Qed. 
  
Lemma sys_BxEqc: forall a a' b b', a ->_lex b -> a =e a' -> b =e b' -> a' ->_lex b'.
Proof.
  intros a a' b b' Hlex Heq Heq'.
  rewrite <- Heq.
  rewrite <- Heq'.
  assumption.
Qed. *)
(* end hide *)
