Definition Rel (A:Type) := A -> A -> Prop.

Definition NF {A:Type} (a:A) (R: Rel A) := ~(exists b, R a b).

(* Transitive closure of a reduction relation *)
Inductive trans {A} (red: Rel A) : Rel A :=
| singl: forall a b,  red a b -> trans red a b
| transit: forall b a c,  red a b -> trans red b c -> trans red a c
.

Arguments transit {A} {red} _ _ _ _ _ .

Inductive refltrans {A:Type} (R: Rel A) : A -> A -> Prop :=
| refl: forall a, (refltrans R) a a
| rtrans: forall a b c, R a b -> refltrans R b c -> refltrans R a c.

Lemma refltrans_composition {A}:
    forall (R: Rel A) t u v, refltrans R t u -> refltrans R u v -> refltrans R t v.
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
  Admitted.
  
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

(** Confluence of the Lex-calculus *)

Definition var := nat.

Require Import Arith MSetList.

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

Notation "x == y" := (eq_var_dec x y) (at level 67).
Notation "i === j" := (Peano_dec.eq_nat_dec i j) (at level 67).

Inductive pterm : Set :=
  | pterm_bvar : nat -> pterm
  | pterm_fvar : var -> pterm
  | pterm_app  : pterm -> pterm -> pterm
  | pterm_abs  : pterm -> pterm
  | pterm_sub : pterm -> pterm -> pterm.

Notation "t [ u ]" := (pterm_sub t u) (at level 70).

(** Opening up abstractions and substitutions *)
Fixpoint open_rec (k : nat) (u : pterm) (t : pterm) {struct t} : pterm :=
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

(** Variable closing *)
Fixpoint close_rec  (k : nat) (x : var) (t : pterm) {struct t} : pterm :=
  match t with
  | pterm_bvar i    => pterm_bvar i
  | pterm_fvar x'    => if x' == x then (pterm_bvar k) else pterm_fvar x'
  | pterm_app t1 t2 => pterm_app (close_rec k x t1) (close_rec k x t2)
  | pterm_abs t1    => pterm_abs (close_rec (S k) x t1)
  | pterm_sub t1 t2 => pterm_sub (close_rec (S k) x t1) (close_rec k x t2)
  end.

Definition close t x := close_rec 0 x t.

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
Hint Constructors term.

(** Local closure of terms *)
Fixpoint lc_at (k:nat) (t:pterm) : Prop :=
  match t with
  | pterm_bvar i    => i < k
  | pterm_fvar x    => True
  | pterm_app t1 t2 => lc_at k t1 /\ lc_at k t2
  | pterm_abs t1    => lc_at (S k) t1
  | pterm_sub t1 t2 => (lc_at (S k) t1) /\ lc_at k t2
  end.

Definition body t := exists L, forall x, x \notin L -> term (t ^ x).

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
  intro i. simpl. case (i === i).
  - intro. auto.
  - intro. apply n. reflexivity.
Qed.  

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

(** Contextual closure of terms. *)
Inductive ES_contextual_closure (R: Rel pterm) : Rel pterm :=
  | ES_redex : forall t s, R t s -> ES_contextual_closure R t s
  | ES_app_left : forall t t' u, term u -> ES_contextual_closure R t t' ->
	  		      ES_contextual_closure R (pterm_app t u) (pterm_app t' u)
  | ES_app_right : forall t u u', term t -> ES_contextual_closure R u u' ->
	  		       ES_contextual_closure R (pterm_app t u) (pterm_app t u')
  | ES_abs_in : forall t t' L, (forall x, x \notin L -> ES_contextual_closure R (t^x) (t'^x)) ->
                               ES_contextual_closure R (pterm_abs t) (pterm_abs t')
  | ES_subst_left : forall t t' u L, term u ->
                                     (forall x, x \notin L -> ES_contextual_closure R (t^x) (t'^x)) ->
	                             ES_contextual_closure R  (t [u]) (t' [u])
  | ES_subst_right : forall t u u', body t -> ES_contextual_closure R u u' ->
	  	                    ES_contextual_closure R  (t [u]) (t [u']).

Inductive eqc : Rel pterm :=
| eqc_def: forall t u v, lc_at 2 t -> term u -> term v -> eqc (t[u][v]) ((& t)[v][u]).
Definition eqc_ctx (t u: pterm) := ES_contextual_closure eqc t u.
Notation "t =c u" := (eqc_ctx t u) (at level 66).
Definition eqc_trans (t u: pterm) := trans eqc_ctx t u.
Notation "t =c+ u" := (eqc_trans t u) (at level 66).
Definition eqC (t : pterm) (u : pterm) := refltrans eqc_ctx t u.
Notation "t =e u" := (eqC t u) (at level 66).

Lemma lc_at_bswap: forall t k, k <> 1 -> lc_at k t -> lc_at k (& t).
Proof.
Admitted.  

Lemma bswap_rec_id : forall n t, bswap_rec n (bswap_rec n t)  = t.
Proof.
 intros n t. generalize dependent n. 
 induction t.
 Admitted.

(*  (* bvar *) *)
(*  intros n'. unfolds bswap_rec. *)
(*  case (n' === n). intro H1. *)
(*  case (n' === S n'). intros H2. *)
(*  assert (Q: n' <> S n'). omega. *)
(*  contradiction. intro H2. *)
(*  case (S n' === S n'). intro H3. *)
(*  rewrite H1. trivial. intro H3. *)
(*  assert (Q: S n' = S n'). trivial. *)
(*  contradiction. intro H. fold bswap_rec. *)
(*  case (S n' === n). intro H1. unfolds bswap_rec. *)
(*  case (n' === n'). intro H2. rewrite H1. trivial. *)
(*  intros H2. assert (Q: n' = n'). trivial. *)
(*  contradiction. intro H1. unfolds bswap_rec. *)
(*  case (n' === n). intro H2. contradiction. intro H2. *)
(*  case (S n' === n). intro H3. contradiction. intro H3. *)
(*  trivial. *)
(*  (* fvar *) *)
(*  intro n. simpl. trivial. *)
(*  (* app *) *)
(*  intro n. simpl. rewrite (IHt1 n). rewrite (IHt2 n). *)
(*  trivial. *)
(*  (* abs *) *)
(*  intro n. simpl. rewrite (IHt (S n)). trivial. *)
(*  (* sub *) *)
(*  intro n. simpl. rewrite (IHt1 (S n)). rewrite (IHt2 n). *)
(*  trivial. *)
(*  (* sub' *) *)
(*  intro n. simpl. rewrite (IHt1 (S n)). rewrite (IHt2 n). *)
(*  trivial. *)
(* Qed. *)

Lemma bswap_idemp : forall t, (& (& t)) = t.
Proof.
  intro t. unfold bswap.
  apply bswap_rec_id.
Qed.

Lemma eqc_sym : forall t u, eqc t u -> eqc u t.
Proof.
 intros t u H. inversion H; subst. 
 replace t0 with (&(& t0)) at 2.
 - apply eqc_def.
   + apply lc_at_bswap. auto. assumption.
   + assumption.
   + assumption.
 - apply bswap_idemp.
Qed.

Lemma eqc_ctx_sym : forall t u, t =c u -> u =c t.
Proof.
  intros t u H. induction H.
  - Admitted.
  
(*   apply ES_redex. apply eqc_sym; assumption. *)
(*   apply ES_app_left; assumption. *)
(*   apply ES_app_right; assumption. *)
(*   apply ES_abs_in with L; assumption. *)
(*   apply ES_subst_left with L; assumption. *)
(*   apply ES_subst_right; assumption. *)
(* Qed. *)

Lemma eqC_trans : forall t u v, t =e u -> u =e v -> t =e v.
Proof.
 intros t u v H H'.
 generalize dependent t.
 induction H'.
 - intros v H; assumption.
 - intros v H1.
   apply IHH'. clear H'.
   apply refltrans_composition' with a; assumption.
Qed.

Lemma eqC_sym : forall t u, t =e u -> u =e t.
Proof.
 intros t u H. induction H.
 - apply refl.
 - apply eqc_ctx_sym in H.
   assert (H': b =e a).
   {
     apply rtrans with a.
     + assumption.
     + apply refl.
   }
   apply eqC_trans with b; assumption.
Qed.
  
Definition red_ctx_mod_eqC (R: Rel pterm) (t: pterm) (u : pterm) :=
           exists t', exists u', (t =e t')/\(R t' u')/\(u' =e u).

Inductive rule_b : Rel pterm  :=
   reg_rule_b : forall (t u:pterm),  body t -> term u ->  
     rule_b (pterm_app(pterm_abs t) u) (t[u]).
Notation "t ->_B u" := (rule_b t u) (at level 66).

Inductive sys_x : Rel pterm :=
| reg_rule_var : forall t, sys_x (pterm_bvar 0 [t]) t
| reg_rule_gc : forall t u, term t -> sys_x (t[u]) t
| reg_rule_app : forall t1 t2 u, 
  sys_x ((pterm_app t1 t2)[u]) (pterm_app (t1[u]) (t2[u]))
| reg_rule_lamb : forall t u, 
  sys_x ((pterm_abs t)[u]) (pterm_abs ((& t)[u]))
| reg_rule_comp : forall t u v, has_free_index 0 u ->
  sys_x (t[u][v]) (((& t)[v])[ u[ v ] ]).

Notation "t ->_x u" := (sys_x t u) (at level 59, left associativity).

Inductive sys_Bx: Rel pterm :=
| B_lx : forall t u, t ->_B u -> sys_Bx t u
| sys_x_lx : forall t u, t ->_x u -> sys_Bx t u.

Definition lex t u :=  red_ctx_mod_eqC sys_Bx t u.

Lemma sys_BxEqc: forall a a' b b', sys_Bx a b -> a =e a' -> b =e b' -> sys_Bx a' b'.
Proof.
Admitted.  

(** Implicit substitution, for free names *)
Fixpoint isb_aux (n:nat) (t u : pterm) : pterm :=
  match t with
  | pterm_bvar i    => if n === i then u else t
  | pterm_fvar x    =>  t
  | pterm_abs t1    => pterm_abs (isb_aux (S n) t1 u)
  | pterm_app t1 t2 => pterm_app (isb_aux n t1 u) (isb_aux n t2 u)
  | pterm_sub t1 t2 => pterm_sub (isb_aux (S n) t1 u) (isb_aux n t2 u)
  end.

Definition isb t u := isb_aux 0 t u.

(** Superdevelpment function *)
Fixpoint sd (t : pterm) : pterm :=
  match t with
  | pterm_bvar i    => t
  | pterm_fvar x    => t
  | pterm_abs t1    => pterm_abs (sd t1)
  | pterm_app t1 t2 => let t0 := (sd t1) in
                      match t0 with
                      | pterm_abs t' => isb t' (sd t2)
                      | _ => pterm_app (sd t1) (sd t2)
                      end 
  | pterm_sub t1 t2 => isb (sd t1) (sd t2)
  end.

Lemma to_sd: forall t, refltrans lex t (sd t).
Proof.
  induction t0.
  - simpl.
    apply refl.
  - simpl.
    apply refl.
  - Admitted.
  
Lemma BxZlex: forall a b, sys_Bx a b -> refltrans lex b (sd a) /\ refltrans lex (sd a) (sd b).
Proof.
  intros a b HBx; split.
  - inversion HBx; subst. clear HBx.
    inversion H; subst. simpl.
Admitted.
  
Theorem Zlex: Zprop lex.
Proof.
  unfold Zprop.
  exists sd.
  intros a b Hlex.
  unfold lex in Hlex.
  inversion Hlex.
  destruct H as [x' [Heq1 [Hsys Heq2]]].
  assert (Hsys': sys_Bx a b).
  {
    apply sys_BxEqc with x x'.
    - assumption.
    - apply eqC_sym in Heq1; assumption.
    - assumption.
  }
  generalize dependent Hsys'.
  apply BxZlex.
Qed.

Corollary lex_is_confluent: Confl lex.
Proof.
  apply Zprop_implies_Confl.
  apply Zlex.
Qed.