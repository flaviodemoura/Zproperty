(** * The Z property implies Confluence

  An ARS is defined as a pair composed of a set and binary operation
  over this set. Given an ARS $(A,R)$, where $A$ is a set and
  $R:A\times A$ and $a,b: A$, we write $a\ R\ b$ or $a\to_R b$ to
  denote that $a$ reduces to $b$ via $R$. The arrow notation will be
  prefered because it is more convenient for expressing reductions, so
  the reflexive transitive closure of a relation [R] is written as
  $\tto_R$, or simply $\tto$ is [R] if clear from the context. *)

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

(** Formally the reflexive transitive closure of a relation [R] is
inductively defined as: *)

Inductive refltrans {A:Type} (R: Rel A) : A -> A -> Prop :=
| refl: forall a, (refltrans R) a a
| rtrans: forall a b c, R a b -> refltrans R b c -> refltrans R a c.

(** This definition has two constructors ([refl] and [[rtrans]]). The
first constructor states that [R] is reflexive, and [rtrans] extends
the reflexive transitive closure of [R] if one has at least a one step
reduction. As a first example, we will prove that the reflexive
transitive closure of a relation [R] is transitive. Although it is too
simple, it will made clear the way we will decorate and explain the
mechanic proofs. The lemma named [refltrans_composition] is stated as
follows: *)

Lemma refltrans_composition {A} (R: Rel A):
  forall t u v, refltrans R t u -> refltrans R u v -> refltrans R t v.

(** This work is not a Coq tutorial, but our idea is that it should be
readable for those unfamiliar to the Coq proof Assistant. In addition,
this paper is built directly from a Coq proof script, which means that
we are forced to present the ideas and the results in a more organized
and systematic way that is not necessarily the more pedagogical
one. In this way, we decided to comment the proof steps giving the
general idea of what they do. It is a good practice to write proofs
between the reserved words [Proof] and [Qed]. *)

Proof. 
  intros t u v H1 H2.
  induction H1.
  - assumption.
  - apply rtrans with b.
    + assumption.
    + apply IHrefltrans; assumption.
Qed.

(** The first line introduces the universally quantified variables
[t,u,v] and the hypothesis [H1] and [H2], that correspond to the
antecedent of the implications, to the proof context. This
introduction could be read as: let [t,u] and [v] be elements of type
[A] (or be elements of the set [A]), [H1] be the fact that the pair
[(t,u)] is in the reflexive transitive closure of [R], and [H2], the
fact that [(u,v)] is in the reflexive transitive closure of [R]. The
corresponding proof context is as follows: %\newline%
 
%\includegraphics[scale=0.6]{fig1.png}%

The proof is by induction on the reflexive transitive closure of
[R]. Therefore, we will have two cases, one for each constructor of
[refltrans]. Note that proofs can be structured with bullets that
represent the different branches within the proof. The first case,
means that [refltrans R t u], i.e. the hypothesis [H1] was built with
the constructor [refl], and hence [t] and [u] must be the same
element, say [t]. Therefore, [H2] becomes [refltrans T t v], which is
exactly the goal. Therefore, this branch of the proof is closed by the
tactic [assumption] that tells the system that the goal corresponds to
one of the hypothesis of the current proof context. The second case,
i.e. the recursive case is more interesting: now we are assuming that
the hypothesis [H1] was built with the constructor [rtrans], and hence
there exists an element, say [w], such that [R t w] and [refltrans R w
u]. In addition, we have the induction hypothesis stating the property
we want to prove (i.e. the transitivity of [refltrans]) but restricted
from [w]. This corresponds to the following proof context up to
renaming of variables: %\newline%

%\includegraphics[scale=0.6]{fig2.png}%

Therefore, in order to prove the goal [refltrans R a v] we apply the
constructor [rtrans] with [b] as the intermediate term. This split the
goal into two new subgoals, each of them now identified with the
bullet [+]. The first argument of the [rtrans] constructor is a
one-step reduction that corresponds to the hypothesis [H] because we
choose [b] as the intermediate term. This subgoal then closes by the
tactic [assumption]. The other subgoal is [refltrans R b v] that is
proved by the induction hypothesis [IHrefltrans] followed by
[assumption] because its antecedent is exactly the hypothesis
[H2]. The corresponding description as a natural deduction tree is as
follows:

%{\small \begin{mathpar}
  \inferrule*[Right=MP]{\inferrule*[Right=MP]{\inferrule*[Right={\sf
  rtrans}]{~}{\inferrule*[Right={$(\forall_e)$}]{\forall x\ y\ z, R\
  x\ y \to refltrans\ R\ y\ z \to refltrans\ R\ x\ z}{R\ a\ b \to
  refltrans\ R\ b\ v \to refltrans\ R\ a\ v}} \and
  \inferrule*[Right=H]{~}{R\ a\ b}}{refltrans\ R\ b\ v \to refltrans\
  R\ a\ v} \and \nabla}{refltrans\ R\ a\ v} \end{mathpar}}%

%\noindent% where $\nabla$ denotes the following derivation tree:

%\begin{mathpar} \inferrule*[Right=MP]{\inferrule*[Left={\sf
 IHrefltrans}]{~}{refltrans\ R\ c\ v \to refltrans\ R\ b\ v} \and
 \inferrule*[Right=H2]{~}{refltrans\ R\ c\ v}}{refltrans\ R\ b\ v}
 \end{mathpar}%

This example is interesting because it shows how Coq works, how
tactics correspond in general to several steps of natural deduction
rules, and how proofs can be structured with bullets. *)

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

(** The reflexive transitive closure of a relation is used to define the
notion of confluence: no matter how the reduction is done, the result
will always be the same. In other words, every divergence is joinable
as stated by the following diagram:

  $\xymatrix{ & a \ar@{->>}[dl] \ar@{->>}[dr] & \\ b
    \ar@{.>>}[dr] & & c \ar@{.>>}[dl] \\ & d & }$

  Therefore, if an expression $a$ can be reduced in two different ways
  to the expressions $b$ and $c$, then there exists an expression $d$
  such that both $b$ and $c$ reduces to $d$. The existential
  quantification is expressed by the dotted lines in the diagram. This
  notion is defined in the Coq system as follows: *)

Definition Confl {A:Type} (R: Rel A) := forall a b c, (refltrans R) a b -> (refltrans R) a c -> (exists d, (refltrans R) b d /\ (refltrans R) c d).

(** Direct proofs of confluence are sometimes difficult, and the Z
    property provides a sufficient condition to conclude the
    confluence of an ARS. In %\cite{ZPropertyDraft}%, V. van Oostrom
    gives a suficient condition for an ARS to be confluent, known as
    the _Z Property_:

    %\begin{definition} Let $(A,\to)$ be an abstract rewriting system
      (ARS). The system $(A,\to)$ has the Z property, if there exists
      a map $f:A \to A$ such that the following diagram holds:
    
      \[ \xymatrix{ a \ar[r] & b \ar@{.>>}[dl]\\ f(a) \ar@{.>>}[r] &
      f(b) \\ } \] \end{definition}%

The corresponding Coq definition is given as: *)

Definition Z_prop {A:Type} (R: Rel A) := exists f:A -> A, forall a b, R a b -> ((refltrans R) b (f a) /\ (refltrans R) (f a) (f b)).

(** Alternatively, when [f] satisfies the Z property one says that [f] is Z: *)

Definition f_is_Z {A:Type} (R: Rel A) (f: A -> A) := forall a b, R a b -> ((refltrans R)  b (f a) /\ (refltrans R) (f a) (f b)). 

(** The first contribution of this work is a constructive proof of the
    fact that the Z property implies confluence. Our proof is
    constructive, and hence differs from the one in %\cite{kes09}%
    (that follows %\cite{ZPropertyDraft}%) in the sense that it does
    not rely on the law of the excluded middle. As a result, we have
    an elegant inductive proof of the fact that if a binary relation
    has the Z property then it is confluent. In addition, we
    formalized this proof in the Coq proof assistant. In
    %\cite{zproperty}%, B. Felgenhauer et.al. formalized the Z
    property in Isabelle/HOL. In what follows we present the theorem
    and its proof interleaving English and Coq code. *)

Theorem Z_prop_implies_Confl {A:Type}: forall R: Rel A, Z_prop R -> Confl R.

(** The hole proof is written between the reserved words [Proof] and
    [Qed]. We comment the commands in blocks in order to stay as close
    as possible to the corresponding English explanation. In addition,
    Coq commands (or tactics) usually perform blocks of natural
    deduction steps followed by simplification steps as seen in the
    previous example. Let [R] be a relation over [A] that satisfies
    the Z property, which will be denoted by [HZ_prop] for future
    reference. *)

Proof.
  intros R HZ_prop.

  (** %\noindent% Then we unfold both definitions, *)

  unfold Z_prop in HZ_prop.
  unfold Confl.

  (** %\noindent% and we get the following proof context:

     % \includegraphics[scale=0.6]{fig3.png}%

     Let [a, b] and [c] be elements of the set [A], [Hrefl1] the
     hypothesis that [a] [R]-reduces to [b] in an arbitrary number of
     steps, i.e. that [(a,b)] is in the reflexive transitive closure
     of [R], and [Hrefl2] the hypothesis that [(a,c)] is in the
     reflexive transitive closure of [R]. 
   *)
  
  intros a b c Hrefl1 Hrefl2.

  (** In addition, by the hypothesis [HZ_prop], we know that there
     exists a mapping [f] that is Z. Let's call [g] this mapping. *)
  
  destruct HZ_prop as [g HZ_prop].

  (** The corresponding proof context is as follows:

      %\includegraphics[scale=0.6]{fig4.png}%

      Now we need to show that there exists an element [d] such that
      both [b] and [c] [R]-reduces to [d]. The proof proceeds by
      nested induction, firstly on the length of the reduction from
      [a] to [b], and then on the length of the reduction from [a] to
      [c]. While performing the first induction, i.e. on [Hrefl1] that
      depends only on [a] and [b], the element [c] needs to be
      generalized so that it can be afterwards instantiated with any
      reduct of [a].

   *)
  
  generalize dependent c.
  induction Hrefl1.

  (** The induction on [Hrefl1] means that we are performing induction
      on the reflexive transitive closure of the relation [R], and
      since [refltrans] has two constructors, the goal split in two
      subgoals, one for each constructor of [refltrans]:

      %\includegraphics[scale=0.6]{fig5.png}%

      The first constructor, namely [refl], is the reflexive part of
      the closure of [R], i.e. the case when [a] is equal to [b]. This
      case is proved by taking [c] as [d].  *)
  
  - intros c Hrefl2.
    exists c; split.

    (** The goal is then the conjunction [refltrans\ R\ a\ c\ /\
        refltrans\ R\ c\ c] whose first component is exactly the
        hypothesis [Hrefl2] and the second corresponds to an
        application of the [refl] axiom. *)
    
    + assumption.
    + apply refl.

    (** The interesting case is given by the inductive case, i.e. by
        the constructor [rtrans], where the reduction from [a] to [b]
        is done in at least one step. Therefore, in this case there
        exists an element [a'] such that the following diagram holds.

        %\xymatrix{ & & a \ar@{->}[dl] \ar@{->>}[dr] & \\ & b
        \ar@{->>}[dl] & & c0 \ar@{.>>}[ddll] \\ c \ar@{.>>}[dr] & & &
        \\ & d & & }%

     *)  
      
  - intros c0 Hrefl2.

    (** The corresponding proof context is as follows:

        %\includegraphics[scale=0.6]{fig5.png}%

        The induction hypothesis [IHHrefl1] states that every
        divergence from [b], that goes to [c] from one side,
        converges. The idea is to then apply induction on the
        hypothesis [Hrefl2], but the current proof context has the
        hypothesis [H: R\ a\ b] which will generate in the induction
        hypothesis the condition that the one-step reduct of [a] must
        reduce in one step to [b], and this is clearly not the case in
        general. In order to circumvent this problem, we need to
        remove the hypothesis [H], but the information ([R\ a\ b]) is
        essential and cannot be simply removed. At this point the Z
        property plays an essential role. Therefore, before applying
        induction to [Hrefl2], we will be replace the hypothesis [H]
        by two other properties that are directly obtained from the Z
        property: ([refltrans R b (g a)]) and ([refltrans R a (g
        a)]). Diagrammatically, we change from the situation on the
        left to the one on the right:

        %\begin{tabular}{c@{\hskip 2cm}c} \xymatrix{ & & a
        \ar@{->>}[ddrr] \ar@{->}[dl] & & \\ & b \ar@{->>}[dl] & & & \\
        \bullet \ar@{.>>}[ddrr] & & & & \bullet \ar@{.>>}[ddll]\\ & &
        & & \\ & & \bullet & & } & \xymatrix{ & & a \ar@{->>}[ddrr]
        \ar@{->>}[dd] & & \\ & b \ar@{->>}[dl] \ar@{->>}[dr] & & & \\
        \bullet \ar@{.>>}[ddrr] & & (g \; a) & & \bullet
        \ar@{.>>}[ddll]\\ & & & & \\ & & \bullet & & } \end{tabular}%

     *)
    
    assert (Hbga: refltrans R b (g a)).
    {
      apply HZ_prop; assumption.
    }
    assert (Haga: refltrans R a (g a)).
    {
      apply rtrans with b; assumption.
    }
    clear H.    
    generalize dependent b.

    (** So the current proof context, after generalizing [b], is as
        follows, and we are ready to apply the inner induction. 

        %\includegraphics[scale=0.6]{fig6.png}%

     *)

    induction Hrefl2.

    (** The first goal corresponds to the reflexive case, which
        corresponds to the following diagram:

        $\xymatrix{ & & a \ar@{->>}[dd] & & \\ & b \ar@{->>}[dl]
        \ar@{->>}[dr] & & & \\ c & & (g \; a) & & \\ }$

        %\noindent% and we need to prove that $a$ and $c$ converge,
        which can be achieved by the first induction hypothesis
        [IHHrefl1]. *)
    
    + intros b Hone IHHrefl1 HZb.
      assert (IHHrefl1_ga := IHHrefl1 (g a)).
      apply IHHrefl1_ga in HZb.
      destruct HZb.
      exists x; split.
      * apply H.
      * apply refltrans_composition with (g a).
        ** assumption.
        ** apply H.

    (** The second goal, i.e. the inductive case can be proved by the
        second induction hypothesis [IHHrefl2].  *)
           
    + intros b0 Hrefl1 IHHrefl1 H'.

      (** The corresponding proof context after introducing the
          universally quantified variable [b0], the hypothesis
          [Hrefl1] and the induction hypothesis [IHHrefl1] generated
          by the first outer induction and the fact that [(b0,g\ a)]
          is in the reflexive transitive closure of [R] is given by:

          %\includegraphics[scale=0.6]{fig7.png}%
          *)
      
      apply IHHrefl2 with b0.

      (** Each condition generated by [IHHrefl2] is solved as follows:
      %1. (\coqdocvar{refltrans} \coqdocvar{R}
      \coqdocvar{b} (\coqdocvar{g} \coqdocvar{b})): This is proved by
      the transitivity of the reflexive transitive closure of
      \coqdocvar{R} using the hypothesis (\coqdocvar{H}: \coqdocvar{R}
      \coqdocvar{a} \coqdocvar{b}) and \coqdocvar{HZ\_prop}:
      \coqdockw{\ensuremath{\forall}} \coqdocvar{a} \coqdocvar{b}:
      \coqdocvar{R} \coqdocvar{a} \coqdocvar{b}
      \ensuremath{\rightarrow} \coqdocvar{refltrans} \coqdocvar{R}
      \coqdocvar{b} (\coqdocvar{g} \coqdocvar{a}) \ensuremath{\land}
      \coqdocvar{refltrans} \coqdocvar{R} (\coqdocvar{g}
      \coqdocvar{a}) (\coqdocvar{g} \coqdocvar{b}). *)
      
      * apply refltrans_composition with (g a); apply HZ_prop; assumption.

      (** %2. (\coqdocvar{refltrans} \coqdocvar{R} \coqdocvar{b0}
          \coqdocvar{c}): This is exactly the hypothesis
          \coqdocvar{Hrefl1}%. *)
        
      * assumption.

        (** %3. (\coqdockw{\ensuremath{\forall}} \coqdocvar{c0}:
            \coqdocvar{A}, \coqdocvar{refltrans} \coqdocvar{R}
            \coqdocvar{b0} \coqdocvar{c0} \ensuremath{\rightarrow}
            \coqdoctac{\ensuremath{\exists}} \coqdocvar{d}:
            \coqdocvar{A}, \coqdocvar{refltrans} \coqdocvar{R}
            \coqdocvar{c} \coqdocvar{d} \coqdoctac{\ensuremath{\land}}
            \coqdocvar{refltrans} \coqdocvar{R} \coqdocvar{c0}
            \coqdocvar{d}): This is exactly the induction hypothesis
            \coqdocvar{IHHrefl1}.% *)
        
      * assumption.

        (** %4. (\coqdocvar{refltrans} \coqdocvar{R} \coqdocvar{b0}
            (\coqdocvar{wb} \coqdocvar{b})): This is proved by the
            transitivity of the reflexive transitive closure of
            \coqdocvar{R} using the hypothesis (\coqdocvar{H'}:
            \coqdocvar{refltrans} \coqdocvar{R} \coqdocvar{b0}
            (\coqdocvar{g} \coqdocvar{a})) and the fact that
            (\coqdocvar{refltrans} \coqdocvar{R} (\coqdocvar{g}
            \coqdocvar{a}) (\coqdocvar{g} \coqdocvar{b})) that is
            obtained from the fact that \coqdocvar{R} satisfies the Z
            property (hypothesis \coqdocvar{HZ\_prop}).% *)
        
      * apply refltrans_composition with (g a).
        ** assumption.
        ** apply HZ_prop; assumption.
Qed.

(** An alternative proof that Z implies confluence is possible via the
    notion of semiconfluence, which is equivalent to confluence, as
    done in %\cite{zproperty}%. Our proof is also constructive, but we
    will not explain it here due to lack of space, but as the
    interested reader can visit the Coq file in our GitHub
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

(** * An extension of the Z property: Compositional Z

    In this section we present a formalization of an extension of the
    Z property with compositional functions, known as _Compositional
    Z_, as presented in %\cite{Nakazawa-Fujita2016}%. The
    compositional Z is an interesting property because it allows a
    kind of modular approach to the Z property in such a way that the
    reduction relation can be split into two parts. More precisely,
    given an ARS $(A,\to)$, one must be able to decompose the relation
    $\to$ into two parts, say $\to_1$ and $\to_2$ such that $\to =
    \to_1\cup \to_2$. The disjoint union can be inductively defined in
    Coq as follows: *)

Inductive union {A} (red1 red2: Rel A) : Rel A :=
 | union_left: forall a b,  red1 a b -> union red1 red2 a b
 | union_right: forall a b,  red2 a b -> union red1 red2 a b.

Notation "R1 !_! R2" := (union R1 R2) (at level 40).

(** This kind of decomposition can be done in several interesting
    situations such as the $\lambda$-calculus with
    $\beta\eta$-reduction%\cite{Ba84}%, extensions of the
    $\lambda$-calculus with explicit substitutions%\cite{accl91}%, the
    $\lambda\mu$-calculus%\cite{Parigot92}%, etc.  *)

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

(** The compositional Z is defined in terms of a weaker property:

    %\begin{definition} Let $(A,\to)$ be an ARS and $\to_x$ another
    relation on $A$. A mapping $f$ satisfies the {\it weak Z property}
    for $\to$ by $\to_x$ if $a\to b$ implies $b \tto_x f(a)$ and $f(a)
    \tto_x f(b)$. Therefore, a mapping $f$ satisfies the Z property
    for $\to$, if it satisfies the weak Z property by itself.
    \end{definition}%

    When $f$ satisfies the weak Z property, we also say that $f$ is
    weakly Z, and the corresponding definition in Coq is given as
    follows: *)

Definition f_is_weak_Z {A} (R R': Rel A) (f: A -> A) := forall a b, R a b -> ((refltrans R')  b (f a) /\ (refltrans R') (f a) (f b)).

(** The compositional Z is an extension of the Z property for
    compositional functions, where composition is defined as usual: *)

Definition comp {A} (f1 f2: A -> A) := fun x:A => f1 (f2 x).
Notation "f1 # f2" := (comp f1 f2) (at level 40).

(** We are now ready to present the definition of the compositional Z:

    %\begin{theorem}\cite{Nakazawa-Fujita2016}\label{thm:zcomp} Let
    $(A,\to)$ be an ARS such that $\to = \to_1 \cup \to_2$. If there
    exists mappings $f_1,f_2: A \to A$ such that \begin{enumerate}
    \item $f_1$ is Z for $\to_1$ \item $a \to_1 b$ implies $f_2(a)
    \tto f_2(b)$ \item $a \tto f_2(a)$ holds for any $a\in Im(f_1)$
    \item $f_2 \circ f_1$ is weakly Z for $\to_2$ by $\to$
    \end{enumerate} then $f_2 \circ f_1$ is Z for $(A,\to)$, and hence
    $(A,\to)$ is confluent.  \end{theorem}%

    We define the predicate [Z_comp] that corresponds to the
    hypothesis of Theorem %\ref{them:zcomp}%, where $\to_1$
    (resp. $\to_2$) is written as [R1] (resp. [R2]): *)

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

(** As stated by Theorem %\ref{them:zcomp}%, the compositional Z gives
    a sufficient condition for compositional functions to be Z. In
    other words, compositional Z implies Z, which can be seen by the
    diagrams of Figure %\ref{fig:zcomp}%
 
    %\begin{figure}\begin{tabular}{l@{\hskip 3cm}l} \xymatrix{ a
    \ar@{->}[rr]^1 && b \ar@{.>>}[dll]_1\\ f_1(a)\ar@{.>>}[d]
    \ar@{.>>}[rr]^1 && f_1(b) \\ f_2(f_1(a)) \ar@{.>>}[rr] &&
    f_2(f_1(b)) } & \xymatrix{ a \ar@{->}[rr]^2 && b \ar@{.>>}[ddll]\\
    & & \\ f_2(f_1(a)) \ar@{.>>}[rr] && f_2(f_1(b)) }
    \end{tabular}\caption{Compositional Z implies
    Z}\label{fig:zcomp}\end{figure}%
  
    In what follows, we present our Coq proof of this fact in the same
    style of the first section by interleaving English followed by the
    corresponding Coq code. *)

Theorem Z_comp_implies_Z_prop {A:Type}: forall (R :Rel A), Z_comp R -> Z_prop R.
Proof.

  (** Let [R] be a relation over [A], and [H] the hypothesis that [R]
      satisfies compositional Z. *)

  intros R H.

  (** Now unfold the definitions of [Z_prop] and [Z_comp] as presented
      before, and name the hypothesis of compositional Z as in
      Theorem %\ref{thm:zcomp}%. *)

  unfold Z_prop.
  unfold Z_comp in H.
  destruct H as [ R1 [ R2 [f1 [f2 [Hunion [H1 [H2 [H3 H4]]]]]]]].

  (** We need to prove that there exists a map, say [f], that is Z as
      shown by the current proof context:

      %\includegraphics[scale=0.6]{fig8.png}%

      Take the composition [f2 # f1] as [f] as suggested by the above
      diagrams, and show that [f2 # f1] is Z. *)
  
  exists (f2 # f1).

  (** So, let [a] and [b] be elements of [A], and suppose that [a]
  [R]-reduces to [b] in one step. Call [HR] this hypothesis.  *)
  
  intros a b HR.

  (** Since [R] is the union of [R1] and [R2], one has that [a]
  reduces to [b] in one step via either [R1] or [R2].  *)
  
  inversion Hunion; subst.
  clear H.
  inversion HR; subst.

  (** Firstly, suppose that [a] [R1]-reduces in one step to [b].  *)
  
  - split.

    (** In order to prove that [b] R-reduces to [((f2 # f1) a)], we
    first need to show that [b] [R1]-reduces to [(f1 a)] as shown in
    Figure %\ref{fig:zcomp}%. *)
    
    + apply refltrans_composition with (f1 a).
      * apply H1 in H.
        destruct H.
        apply refltrans_union; assumption.

        (** The next step is then to prove that [(f1 a)] [R]-reduces
            to [((f2 # f1) a)], which is a direct consequence of
            [H3]. *)
        
      * apply H3 with a; reflexivity.

    (** The proof that [((f2 # f1) a)] [R]-reduces to [((f2 # f1) b)]
    is more tricky. Initially, note that, since [R1 a b] then we get
    that [refltrans R1 (f1 a) (f1 b)] by the Z property. *)
        
    + apply H1 in H.
      destruct H.
      clear H HR.
      unfold comp.

      (** Now, the goal can be obtained from [H2] as long as [R1 (f1
      a) (f1 b)], but we only have that [refltrans R1 (f1 a) (f1
      b)]. Therefore, we use induction on this hypothesis. *)
      
      induction H0.

      (** The reflexive case is trivial because [a] and [b] are equal.
      *)
      
      * apply refl.

      (** In the transitive case, we have that [(f1 a)] [R1]-reduces
      to [(f1 b)] in at least one step. The current proof context is
      as follows:

      %\includegraphics[scale=0.6]{fig9.png}%

      Therefore, there exists some [b0] such that [R1 a0 b0] and
      [refltrans R1 b0 c] and we need to prove that [refltrans (R1 !_!
      R2) (f2 a0) (f2 c)]. This can be done in two steps by
      transitivity of [refltrans] taking [(f2 b0)] as the intermediary
      term. *)
        
      * apply refltrans_composition with (f2 b0).

        (** The first subgoal is then [refltrans (R1 !_! R2) (f2 a0)
        (f2 b0)] that is proved by hypothesis [H2]. *)
        
        ** apply H2; assumption.

        (** And the second subgoal [refltrans (R1 !_! R2) (f2 b0) (f2
        c)] is proved by the induction hypothesis. *)
           
        ** assumption.

  (** Finally, when [a] [R2]-reduces in one step to [b] one concludes
      the proof using the assumption that [(f2 # f1)] is weak Z. *)
           
  - apply H4; assumption.    
Qed.

(** Now we can use the proofs of the theorems [Z_comp_implies_Z_prop]
    and [Z_prop_implies_Confl] to conclude that compositional Z is a
    suficient condition for confluence. *)

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
    $(A,\to)$ be an ARS such that $\to = \to_1 \cup \to_2$. If there
    exists mappings $f_1,f_2: A \to A$ such that \begin{enumerate}
    \item $a \to_1 b$ implies $f_1(a) = f_1(b)$ \item $a \tto_1
    f_1(a), \forall a$ \item $a \tto f_2(a)$ holds for any $a\in
    Im(f_1)$ \item $f_2 \circ f_1$ is weakly Z for $\to_2$ by $\to$
    \end{enumerate} then $f_2 \circ f_1$ is Z for $(A,\to)$, and hence
    $(A,\to)$ is confluent.  \end{corollary}%

    We define the predicate [Z_comp_eq] corresponding to the
    hypothesis of Corollary %\ref{cor:zcomp}%, and then we prove
    directly that if [Z_comp_eq] holds for a relation [R] then [Zprop
    R] also holds. This approach differs from
    %\cite{Nakazawa-Fujita2016}% that proves Corollary
    %\ref{cor:zcomp}% directly from Theorem %\ref{thm:zcomp}% *)

Definition Z_comp_eq {A:Type} (R :Rel A) := exists (R1 R2: Rel A) (f1 f2: A -> A), R = (R1 !_! R2) /\ (forall a b, R1 a b -> (f1 a) = (f1 b)) /\ (forall a, (refltrans R1) a (f1 a)) /\ (forall b a, a = f1 b -> (refltrans R) a (f2 a)) /\ (f_is_weak_Z R2 R (f2 # f1)).
        
Lemma Z_comp_eq_implies_Z_prop {A:Type}: forall (R : Rel A), Z_comp_eq R -> Z_prop R.
Proof.

  (** Let [R] be a relation and suppose that [R] satisfies the
      predicate [Z_comp_eq]. *)
  
  intros R Heq.
  unfold Z_comp_eq in Heq.

  (** Call [Hi] the [i]th hypothesis as in %\ref{cor:zcomp}%.  *)
  
  destruct Heq as [R1 [R2 [f1 [f2 [Hunion [H1 [H2 [H3 H4]]]]]]]].

  (** From the definition of the predicate [Z_prop], we need to find a
      map, say [f] that is Z. Let [(f2 # f1)] be such map.  *)
  
  unfold Z_prop.
  exists (f2 # f1).

  (** In order to prove that [(f2 # f1)] is Z, let [a] and [b] be
      arbitrary elements of type [A], and [Hab] be the hypothesis that
      [a] [R]-reduces in one step to [b].  *)
  
  intros a b Hab.

  (** Since [a] [R]-reduces in one step to [b] and [R] is the union of
      the relations [R1] and [R2] then we consider two cases: *)
  
  inversion Hunion; subst; clear H.
  inversion Hab; subst; clear Hab.
  
  (** The first case is when [a] [R1]-reduces in one step to [b]. *)
  
  - unfold comp; split.

    (** This is equivalent to say that [f2 # f1] is weak Z for [R1] by
    [R1 !_! R2]. Therefore, we first prove that [refltrans (R1 !_! R2)
    b (f2 (f1 a))], which can be reduced to [refltrans (R1 !_! R2) b
    (f1 b)] and [refltrans (R1 !_! R2) (f1 b) (f2 (f1 a))] by the
    transitivity of [refltrans]. *)
    
    + apply refltrans_composition with (f1 b).

      (** From hypothesis [H2], we know that [refltrans R1 a (f1 a)]
          for all [a], and hence [refltrans (R1 !_! R2) a (f1 a)] and
          we conclude.*)
      
      * apply refltrans_union.
        apply H2.

        (** The proof that [refltrans (R1 !_! R2) (f1 b) (f2 (f1 a))]
        is exactly the content of hypothesis [H3].  *)
        
      * apply H1 in H.
        rewrite H.
        apply H3 with b; reflexivity.

        (** The proof that [refltrans (R1 !_! R2) (f2 (f1 a)) (f2 (f1
            b))] is done using the reflexivity of [refltrans] because
            [ (f2 (f1 a)) = (f2 (f1 b))] by hypothesis [H1. ]*)
        
    + apply H1 in H.
      rewrite H.
      apply refl.

      (** When [a] [R2]-reduces in one step to [b] then we are done by
      hypothesis [H4]. *)
      
  - apply H4; assumption.
Qed.

(*
Corollary Z_comp_eq_implies_Z_comp {A:Type}: forall (R : Rel A), Z_comp_eq R -> Z_comp R.
Proof.
  intros R Heq.
  unfold Z_comp_eq in Heq.
  destruct Heq as [R1 [R2 [f1 [f2 [Hunion [H1 [H2 [H3 H4]]]]]]]].
  unfold Z_comp.
  exists R1, R2, f1, f2; split.
  - assumption.
  - split.
    + unfold f_is_Z.
      intros a b Hab; split.
      * apply H1 in Hab.
        rewrite Hab.
        apply H2.
      * apply H1 in Hab.
        rewrite Hab.
        apply refl.
    + split.
      * intros a b Hab.
        admit.
      * split.
        ** apply H3.
        ** apply H4.
Admitted.
*)
