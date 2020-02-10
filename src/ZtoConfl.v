(** * The Z property implies Confluence

  Confluence is an important property concerning the determinism of
  the computational process in the sense one says that a program is
  confluent if every two ways of evaluating this program result in the
  very same answer. In the particular case of Abstract Rewriting
  Systems (ARS), which are the focus of this work, confluence can be
  beautifully expressed by diagrams as we will see next. By
  definition, an ARS is simply a pair composed of a set and binary
  operation over this set. Given an ARS $(A,R)$, where $A$ is a set
  and $R:A\times A$ and $a,b: A$, we write $a\ R\ b$ or $a\to_R b$ to
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

    %\begin{definition}\label{def:zcomp} Let $(A,\to)$ be an ARS such
    that $\to = \to_1 \cup \to_2$. If there exists mappings $f_1,f_2:
    A \to A$ such that \begin{enumerate} \item $f_1$ is Z for $\to_1$
    \item $a \to_1 b$ implies $f_2(a) \tto f_2(b)$ \item $a \tto
    f_2(a)$ holds for any $a\in Im(f_1)$ \item $f_2 \circ f_1$ is
    weakly Z for $\to_2$ by $\to$ \end{enumerate} then $f_2 \circ f_1$
    is Z for $(A,\to)$, and hence $(A,\to)$ is confluent.
    \end{definition}%

    %\noindent% and the corresponding Coq definition, where $\to_1$
    (resp. $\to_2$) appears as [R1] (resp. [R2]),
    is given by: *)

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

(** The compositional Z gives a sufficient condition for compositional
    functions to be Z. In other words, compositional Z implies Z,
    which is given by the following diagrams:
 
    %\begin{tabular}{l@{\hskip 3cm}l} \xymatrix{ a \ar@{->}[rr]^1 && b
    \ar@{.>>}[dll]_1\\ f_1(a)\ar@{.>>}[d] \ar@{.>>}[rr]^1 && f_1(b) \\
    f_2(f_1(a)) \ar@{.>>}[rr] && f_2(f_1(b)) } & \xymatrix{ a
    \ar@{->}[rr]^2 && b \ar@{.>>}[ddll]\\ & & \\ f_2(f_1(a))
    \ar@{.>>}[rr] && f_2(f_1(b)) } \end{tabular}%
  
    In what follows, we present our Coq proof of this fact in the same
    style of the first section by interleaving English followed by the
    corresponding Coq code. *)

Lemma Z_comp_implies_Z_prop {A:Type}: forall (R :Rel A), Z_comp R -> Z_prop R.
Proof.

  (** Let [R] be a relation over [A], and [H] the hypothesis that [R]
      satisfies compositional Z. *)
  
  intros R H.

  (** Now unfold the definitions of [Z_prop] and [Z_comp] as presented
      before, and organize the items of compositional Z as in
      Definition %\ref{def:zcomp}%. *)
  
  unfold Z_prop.
  unfold Z_comp in H.
  destruct H as [ R1 [ R2 [f1 [f2 [Hunion [HfZ [Hrefl [HIm Hweak]]]]]]]].

  
  exists (f2 # f1).
  intros a b HR.
  inversion Hunion; subst.
  clear H.
  inversion HR; subst.
  - split.
    + apply refltrans_composition with (f1 a).
      * apply HfZ in H.
        destruct H.
        apply refltrans_union; assumption.
      * apply HIm with a; reflexivity.
    + apply HfZ in H.
      destruct H.
      clear H HR.
      unfold comp.
      induction H0.
      * apply refl.
      * apply refltrans_composition with (f2 b0).
        ** apply Hrefl; assumption.
        ** assumption.
  - apply Hweak; assumption.    
Qed.

(*
Lemma Z_prop_implies_Z_comp {A:Type}: forall (R : Rel A), Z_prop R -> Z_comp R.
Proof.
  intros R HZ_prop.
  unfold Z_prop in HZ_prop.
  destruct HZ_prop.
  unfold Z_comp.
  exists R. exists R. exists x. exists (@id A). split.
  - symmetry.
    change (R !_! R) with R \/ R.
    apply union_idemp.
  - split.
    + assumption.
    + split.
      * intros a b Hab.
        apply rtrans with b.
        ** assumption.
        ** apply refl.
      * split.
        ** intros a b Heq.
           apply refl.
        ** auto.
Qed.

Theorem Z_comp_equiv_Z_prop {A:Type}: forall (R : Rel A), Z_prop R <-> Z_comp R.
Proof.
  split.
  - apply Z_prop_implies_Z_comp.
  - apply Z_comp_implies_Z_prop.
Qed.
*)

Corollary Z_comp_is_Confl {A}: forall (R: Rel A), Z_comp R -> Confl R.
Proof.
  intros R H.
  apply Z_comp_implies_Z_prop in H.
  apply Z_prop_implies_Confl; assumption.  
Qed.

(* begin hide *)
Definition Z_comp_eq {A:Type} (R :Rel A) := exists (R1 R2: Rel A) (f1 f2: A -> A), R = (R1 !_! R2) /\ (forall a b, R1 a b -> (f1 a) = (f1 b)) /\ (forall a, (refltrans R1) a (f1 a)) /\ (forall b a, a = f1 b -> (refltrans R) a (f2 a)) /\ (f_is_weak_Z R2 R (f2 # f1)).

Definition Z_comp_eq' {A:Type} (R :Rel A) := exists (R1 R2: Rel A) (f : A -> A), R = (R1 !_! R2) /\ (forall a b, R1 a b -> (f a) = (f b)) /\ (forall a, (refltrans R2) a (f a)) /\ (f_is_weak_Z R2 R f).

(*
Definition Z_comp_new_eq {A:Type} (R :Rel A) := forall (R1 R2: Rel A), R = (R1 !_! R2) -> exists (f1 f2: A -> A), (forall a b, R1 a b -> (f1 a) = (f1 b)) /\ (forall a, (refltrans R1) a (f1 a)) /\ (forall b a, a = f1 b -> (refltrans R) a (f2 a)) /\ (f_is_weak_Z R2 R (f2 # f1)).
 *)

Lemma Z_comp_eq'_implies_Z_prop {A:Type}: forall (R : Rel A), Z_comp_eq' R -> Z_prop R.
Proof.
  unfold Z_comp_eq'.
  unfold Z_prop.
  intros R H.
  destruct H as [R1 [R2 [f [Hunion [HR1eqf [HR2f Hweak]]]]]].
  exists f.
  intros a b Hab.
  inversion Hunion; subst.
  clear H.
  split.
  - induction Hab.
    + apply HR1eqf in H.
      apply refltrans_composition with (f b).
      * specialize (HR2f b).
        induction HR2f.
        ** apply refl.
        **  apply rtrans with b.
            *** apply union_right; assumption.
            *** apply IHHR2f; assumption.
      * rewrite H; apply refl.
    + apply Hweak; assumption.
  - induction Hab.
    + apply HR1eqf in H.
      rewrite <- H.
      apply refl.
    + apply Hweak; assumption.
Qed.

Lemma Z_comp_eq_implies_Z_prop {A:Type}: forall (R : Rel A), Z_comp_eq R -> Z_prop R.
Proof.
  unfold Z_comp_eq.
  unfold Z_prop.
  intros R H.
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
(* end hide *)
