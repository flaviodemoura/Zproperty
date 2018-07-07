(** Confluence of the Lex-calculus through Z property. *)

Require Import ZtoConfl.

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

Notation "x == y" := (eq_var_dec x y) (at level 67).
Notation "i === j" := (Peano_dec.eq_nat_dec i j) (at level 67).

Lemma notin_union : forall x E F,
  x \notin (E \u F) <-> (x \notin E) /\ (x \notin F).
Proof.
assert (not_or: forall (A B: Prop), ~(A \/ B) <-> ~ A /\ ~ B).
{
  unfold not.
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
}
intros x E F.
apply iff_stepl with (~((x \in E) \/ (x \in F))).
- apply not_or.
- split; unfold not; intros; destruct H; apply union_spec in H0; assumption.
Qed.

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

(** From Metatheory_Tactics - Arthur Chargueraud. REVISAR *)

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

(** Opening up abstractions and substitutions *)
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

(** Variable closing *)
Fixpoint close_rec  (k : nat) (x : var) (t : pterm) : pterm :=
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

Definition term_regular (R : Rel pterm) :=
  forall t t', R t t' -> term t -> term t'.

Definition red_rename (R : Rel pterm) :=
  forall x t t' y,
  x \notin (fv t) -> x \notin (fv t') ->
  R (t ^ x) (t' ^ x) -> 
  R (t ^ y) (t' ^ y).

Definition body t := exists L, forall x, x \notin L -> term (t ^ x).

Lemma term_regular_trans: forall R, term_regular R -> term_regular (trans R).
Proof.
unfold term_regular.
intros R H t' t0 H0 H1.
induction H0.
- apply H with a; assumption.
- apply IHtrans.
  apply H with a; assumption.
Qed.
    
(** Local closure of terms *)
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
  - intros k1 k2 Hlc H.
    simpl in *.
    apply Nat.lt_le_trans with k1; assumption.
  - intros k1 k2 Hlc Hle.
    simpl. auto.
  - intros k1 k2 Hlc Hle.
    simpl in *.
    destruct Hlc as [H1 H2].
    split.
    + apply IHt1 with k1; assumption.
    + apply IHt2 with k1; assumption.
  - intros k1 k2 Hlc Hle.
    simpl.
    simpl in Hlc.
    apply IHt with (S k1).
    + assumption.
    + apply Peano.le_n_S; assumption.
  - intros k1 k2 Hlc Hle.
    simpl in *.
    destruct Hlc as [H1 H2].
    split.
    + apply IHt1 with (S k1).
      * assumption.
      * apply Peano.le_n_S; assumption.
    + apply IHt2 with k1; assumption.
Qed.

Lemma lc_rec_open_var_rec : forall x t k,
  lc_at k (open_rec k x t) -> lc_at (S k) t.
Proof.
  intros x t.
  induction t; simpl. 
  - intro k.
    case (k === n).
    + intros Heq Hlc.
      subst.
      auto with arith.
    + intros Hneq Hlc.
      simpl in Hlc.
      apply lt_trans with k.
      * assumption.
      * auto with arith.
  - intros n t; auto.
  - intros k H.
    destruct H as [Ht1 Ht2].
    split.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
  - intros k Hlc.
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
    apply lc_rec_open_var_rec in Fr.
    simpl; assumption.
  - simpl.
    split.
    + pick_fresh y.
    apply notin_union in Fr.
    destruct Fr as [Fr Hfv].
    apply notin_union in Fr.
    destruct Fr as [Fr Hfv'].
    apply H0 in Fr.
    apply lc_rec_open_var_rec in Fr.
    assumption.
    + assumption.
Qed.  

Lemma lc_at_open_rec : forall n t u, term u -> (lc_at (S n) t -> lc_at n (open_rec n u t)).
Proof.
  intros n t u T H.
  generalize dependent n.
  induction t.
  - intros n' Hlc.
    simpl in *.
    case (n' === n).
    + intro H; subst.
      apply term_to_lc_at in T.
      apply lc_at_weaken_ind with 0.
      * assumption.
      * auto with arith.
    + intro Hneq.
      simpl.
      apply lt_n_Sm_le in Hlc.
      apply le_lt_or_eq in Hlc.
      destruct Hlc.
      * assumption.
      * symmetry in H. contradiction.
  - intros n Hlc.
    simpl in *.
    auto.
  - intros n Hlc.
    simpl in *.
    destruct Hlc as [H1 H2].
    split.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
  - intros n Hlc.
    apply IHt.
    simpl in Hlc; assumption.    
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
  - apply lc_rec_open_var_rec.
Qed.

Lemma lc_at_open_rec_rename: forall t x y m n, lc_at m (open_rec n (pterm_fvar x) t) -> lc_at m (open_rec n (pterm_fvar y) t).
Proof.
  Admitted.
  (* induction t. simpl. introv H. case_nat. constructor. assumption. *)
(*   simpl. intros; trivial. simpl. introv H. destruct H. *)
(*   apply (IHt1 x y) in H. apply (IHt2 x y) in H0. *)
(*   split; assumption. simpl. *)
(*   introv H. apply IHt with x. assumption. simpl. *)
(*   introv H. destruct H. split. apply IHt1 with x; assumption. apply IHt2 with x; assumption. *)
(*   simpl. trivial. *)
(* Qed.   *)

Corollary term_open_rename: forall t x y, term (t^x) -> term (t^y).  
Proof.
  Admitted.
(*   introv H. apply term_eq_term' in H. apply term_eq_term'. *)
(*   apply lc_at_open_rec_rename with x. assumption. *)
(* Qed. *)

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
  apply term_open_rename with y.
  assumption.
Qed.

Theorem term_equiv_lc_at: forall t, term t <-> lc_at 0 t.
Proof.
  intro t; split.
  - intro Hterm.
    induction Hterm.
    + simpl; auto.
    + simpl; split.
      * apply IHHterm1.
      * apply IHHterm2.
    + pick_fresh y.
      unfold open in H0.
      simpl.
      apply lc_at_open with (pterm_fvar y).
      * apply term_var.
      * apply H0.
        apply notin_union in Fr.
        apply Fr.
    + simpl; split.
      * pick_fresh y.
        unfold open in H0.
        apply lc_at_open with (pterm_fvar y).
        ** apply term_var.
        ** apply H0.
           apply notin_union in Fr.
           destruct Fr.
           apply notin_union in H1.
           apply H1.
      * assumption.
  - intro Hlc.
    induction t.
    + inversion Hlc.
    + apply term_var.
    + simpl in Hlc.
      destruct Hlc as [Hlc1 Hlc2]. 
      apply term_app.
      * apply IHt1; assumption.
      * apply IHt2; assumption.
    + apply term_abs with (fv t0).
      intros x Hfv.
      admit.
    + Admitted.

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

Lemma lc_at_bswap: forall t k, k <> 1 -> lc_at k t -> lc_at k (& t).
Proof.
  induction k.
  - induction t0.
    + intros.
  apply Nat.nlt_0_r in H0.
  contradiction.
    + trivial.
    + intros.
      destruct H0.
      assert (H': 0 <> 1).
      {
        assumption.
      }
    apply IHt0_1 in H.
      * apply IHt0_2 in H'.
        ** simpl.
           split.
            *** assumption.
            *** assumption.
        ** assumption.
      * assumption.
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

(** Contextual closure of terms. *)
Inductive ES_contextual_closure (R: Rel pterm) : Rel pterm :=
  | ES_redex : forall t s, R t s -> ES_contextual_closure R t s
  | ES_app_left : forall t t' u, ES_contextual_closure R t t' ->
	  		      ES_contextual_closure R (pterm_app t u) (pterm_app t' u)
  | ES_app_right : forall t u u', ES_contextual_closure R u u' ->
	  		       ES_contextual_closure R (pterm_app t u) (pterm_app t u')
  | ES_abs_in : forall t t' L, (forall x, x \notin L -> ES_contextual_closure R (t^x) (t'^x)) ->
                               ES_contextual_closure R (pterm_abs t) (pterm_abs t')
  | ES_sub : forall t t' u L, (forall x, x \notin L -> ES_contextual_closure R (t^x) (t'^x)) ->
	                        ES_contextual_closure R  (t [u]) (t' [u])
  | ES_sub_in : forall t u u', ES_contextual_closure R u u' ->
	  	               ES_contextual_closure R  (t [u]) (t [u']).

Lemma term_regular_ctx: forall R, term_regular R -> term_regular (ES_contextual_closure R).
Proof.
  intros R Hred.
  unfold term_regular.
  intros t t' H Hterm.
  induction H.
  - apply Hred with t0; assumption.
  - inversion Hterm; subst; clear Hterm.
    apply term_app.
    + apply IHES_contextual_closure; assumption.
    + assumption.
  - inversion Hterm; subst; clear Hterm.
    + apply term_app.
      * assumption.
      * apply IHES_contextual_closure; assumption.
  - inversion Hterm; subst. 
    apply term_abs with (L \u L0).
    intros x HL.
    apply notin_union in HL.
    destruct HL as [HnL HnL0].
    apply H0.
    + assumption.
    + apply H2; assumption.
  - inversion Hterm; subst; clear Hterm.
    apply term_sub with (L \u L0).
    + intros x HL.
       Admitted.
(*       * assumption. *)
(*     + apply term_sub with L. *)
(*       * apply H1. *)
(*       * assumption. *)
(*   - split. *)
(*     + apply term_sub with (fv t0). *)
(*       * intros x Hfv. *)
(*         apply body_to_term; assumption. *)
(*       * apply IHES_contextual_closure. *)
(*     + apply term_sub with (fv t0). *)
(*       * intros x Hfv. *)
(*         apply body_to_term; assumption. *)
(*       * apply IHES_contextual_closure. *)
(* Qed. *)
    
Inductive eqc : Rel pterm :=
| eqc_def: forall t u v, term u -> term v -> eqc (t[u][v]) ((& t)[v][u]).

Lemma eqc_sym : forall t u, eqc t u -> eqc u t.
Proof.
 intros t u H. inversion H; subst. 
 replace t0 with (&(& t0)) at 2.
 - apply eqc_def; assumption.
 - apply bswap_idemp.
Qed.

Lemma term_regular_eqc : term_regular eqc.
Proof.
  (* unfold red_regular. intros t t' Heqc; split. *)
  (* - inversion Heqc; subst. clear Heqc. *)
  (*   apply term_sub with (fv t0 \u fv u). *)
  (*   + intros x Hfv. unfold open; simpl. *)
  (*     apply term_sub with (fv t0 \u {{x}}). *)
  (*     * intros x' Hfv'. *)
  (*       apply term_equiv_lc_at. *)
  (*       apply lc_at_open. *)
  (*       ** apply term_var. *)
  (*       ** apply lc_at_open. *)
  (*          *** apply term_var. *)
  (*          *** assumption. *)
  (*     * admit. *)
  (*   + admit. *)
  - Admitted.
(*   apply term'_to_term. unfold term'. *)
(*   apply lc_at_open; trivial. *)
(*   apply lc_at_open; trivial. *)
(*   apply term'_to_term. *)
(*   apply lc_at_open; trivial. *)
(*   apply term_to_term' in H1. unfold term' in H1. *)
(*   apply lc_at_weaken_ind with 0. assumption. auto. assumption. *)

(*   inversion H; subst. clear H. *)
(*   apply term_sub with (fv t0 \u fv u). *)
(*   intros_all. unfold open. simpl. *)
(*   apply term_sub with (fv t0 \u {{x}}). *)
(*   intros_all. apply term'_to_term. unfold term'. *)
(*   apply lc_at_open; trivial. *)
(*   apply lc_at_open; trivial.   *)
(*   apply lc_at_bswap. auto. assumption. *)
(*   apply term'_to_term. *)
(*   apply lc_at_open; trivial. *)
(*   apply term_to_term' in H2. unfold term' in H2. *)
(*   apply lc_at_weaken_ind with 0. assumption. auto. assumption. *)
(* Qed. *)
  
Definition eqc_ctx (t u: pterm) := ES_contextual_closure eqc t u.
Notation "t =c u" := (eqc_ctx t u) (at level 66).

Corollary term_regular_eqc_ctx: term_regular eqc_ctx.
Proof.
  apply term_regular_ctx.
  apply term_regular_eqc.
Qed.
  
Lemma eqc_ctx_sym : forall t u, t =c u -> u =c t.
Proof.
  intros t u H. induction H.
  - apply ES_redex. apply eqc_sym; assumption. 
  - apply ES_app_left; assumption. 
  - apply ES_app_right; assumption. 
  - apply ES_abs_in with L; assumption. 
  - apply ES_sub with L; assumption.
  - apply ES_sub_in; assumption.
Qed.

        
Definition eqc_trans (t u: pterm) := trans eqc_ctx t u.
Notation "t =c+ u" := (eqc_trans t u) (at level 66).

Corollary term_regular_eqc_trans: term_regular eqc_trans.
Proof.
  apply term_regular_trans.
  apply term_regular_eqc_ctx.
Qed.

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
      
Definition eqC (t : pterm) (u : pterm) := refltrans eqc_ctx t u.
Notation "t =e u" := (eqC t u) (at level 66).

(* Corollary red_regular_eqC: red_regular eqC. *)
(* Proof. *)
(*   apply red_regular_refltrans. *)
(*   apply red_regular_eqc_ctx. *)
(* Qed. *)
  
(** =e is an equivalence relation *)

Lemma eqC_rf : forall t, t =e t.
Proof.
  intro t.
  apply refl.
Qed.

Lemma eqC_trans : forall t u v, t =e u -> u =e v -> t =e v.
Proof.
 intros t u v H H'.
 generalize dependent t.
 induction H'.
 - intros v H'; assumption.
 - intros v H''.
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

Instance eqC_eq : Equivalence eqC.
Proof.
  split.
  - unfold Reflexive. apply eqC_rf.
  - unfold Symmetric.
    intros x y Heq.
    apply eqC_sym; trivial.
  - unfold Transitive.
    intros x y z Heq Heq'.
    apply eqC_trans with y; trivial.
Qed.
    
Definition red_ctx_mod_eqC (R: Rel pterm) (t: pterm) (u : pterm) :=
           exists t', exists u', (t =e t')/\(R t' u')/\(u' =e u).

Lemma term_regular_red_ctx_mod_eqC: forall R, term_regular R -> term_regular (red_ctx_mod_eqC R). 
Proof.
  intros R Hreg.
  unfold term_regular.
  intros t t' Hctx.
  induction Hctx.
 Admitted.
  
(** =e Rewriting *)

Instance rw_eqC_red : forall R, Proper (eqC ==> eqC ==> iff) (red_ctx_mod_eqC R).
Proof.
Admitted.
(*  intros_all. split. intro H1. *)
(*  unfold red_ctx_mod_eqC in *. *)
(*  destruct H1. destruct H1. destruct H1. destruct H2. *)
(*  exists x1 x2. split.  *)
(*  apply eqC_sym in H. *)
(*  apply eqC_trans with x; assumption. *)
(*  split. assumption. *)
(*  apply eqC_trans with x0; assumption. *)
(*  intro H1. *)
(*  unfold red_ctx_mod_eqC in *. *)
(*  destruct H1. destruct H1. destruct H1. destruct H2. *)
(*  exists x1 x2. split.  *)
(*  rewrite <- H1; assumption. split; trivial. *)
(*  rewrite H3. rewrite H0.  *)
(*  reflexivity. *)
(* Qed. *)

Instance rw_eqC_trs : forall R, Proper (eqC ==> eqC ==> iff) (trans (red_ctx_mod_eqC R)).
Proof.
Admitted.
(*     intros_all. split.  *)
(*     intro H'. *)
(*     inversion H'; subst. *)
(*     apply one_step_reduction. *)
(*     destruct H1. destruct H1.  destruct H1. destruct H2. *)
(*     exists x1 x2. *)
(*     split. rewrite <- H; auto. *)
(*     split; auto. rewrite <- H0; auto. *)
(*     constructor 2 with u. rewrite <- H; auto. *)
(*     apply transitive_star_derivation' in H2. *)
(*     destruct H2. *)
(*     constructor 1. *)
(*     destruct H2. destruct H2.  destruct H2. destruct H3. *)
(*     unfold red_ctx_mod_eqC. exists x1 x2. *)
(*     split; auto. split; auto. rewrite H4; auto. *)
(*     destruct H2. destruct H2. destruct H3. destruct H3. *)
(*     apply transitive_star_derivation'. *)
(*     right. exists x1. split; auto. exists x2. split; auto. *)
(*     destruct H4. destruct H4.  destruct H4. destruct H5. *)
(*     exists x3 x4. split; auto. split; auto. rewrite H6; auto. *)

(*     intro H'. *)
(*     inversion H'; subst. *)
(*     apply one_step_reduction. *)
(*     destruct H1. destruct H1.  destruct H1. destruct H2. *)
(*     exists x1 x2. *)
(*     split. rewrite H; auto. *)
(*     split; auto. rewrite H0; auto. *)
(*     constructor 2 with u. rewrite H; auto. *)
(*     apply transitive_star_derivation' in H2. *)
(*     destruct H2. *)
(*     constructor 1. *)
(*     destruct H2. destruct H2.  destruct H2. destruct H3. *)
(*     unfold red_ctx_mod_eqC. exists x1 x2. *)
(*     split; auto. split; auto. rewrite H4; auto. symmetry; auto. *)
(*     destruct H2. destruct H2. destruct H3. destruct H3. *)
(*     apply transitive_star_derivation'. *)
(*     right. exists x1. split; auto. exists x2. split; auto. *)
(*     destruct H4. destruct H4.  destruct H4. destruct H5. *)
(*     exists x3 x4. split; auto. split; auto. rewrite H6; auto. symmetry; auto. *)
(* Qed. *)

Instance rw_eqC_lc_at : forall n, Proper (eqC ==> iff) (lc_at n).
Proof.
  Admitted.
(*  intros_all. apply lc_at_eqC; trivial. *)
(* Qed. *)

Instance rw_eqC_body : Proper (eqC ==> iff) body.
Proof.
  Admitted.
(*  intros_all. rewrite body_eq_body'. rewrite body_eq_body'. *)
(*  unfold body'. rewrite H. reflexivity. *)
(* Qed. *)

Instance rw_eqC_term : Proper (eqC ==> iff) term.
Proof.
  Admitted.
(*  intros_all. rewrite term_eq_term'. rewrite term_eq_term'. *)
(*  unfold term'. rewrite H. reflexivity. *)
(* Qed. *)

Instance rw_eqC_fv : Proper (eqC ==> VarSet.Equal) fv.
Proof.
  Admitted.
(*  intros_all. apply eqC_fv; trivial. *)
(* Qed. *)

Instance rw_eqC_app : Proper (eqC ==> eqC ==> eqC) pterm_app.
Proof.
  Admitted.
(*     intros_all. apply star_closure_composition with (u:=pterm_app y x0). *)
(*     induction H. constructor. constructor 2.  *)

(*     induction H. *)
(*     constructor. *)
(*     constructor 2. auto. admit. constructor 2 with (pterm_app u x0). *)
(*     constructor 2. auto.  admit. auto. *)

(*     induction H0. constructor. *)
(*     constructor 2. *)
(*     induction H0. *)
(*     constructor. auto. constructor 3; auto. admit. constructor 2 with (pterm_app y u). *)
(*     constructor 3. auto.  admit. auto. *)
(* Qed. *)

Instance rw_eqC_subst_right : forall t, Proper (eqC ++> eqC) (pterm_sub t).
Proof.
  Admitted.
(*  intros_all. induction H. *)
(*  constructor. *)
(*  constructor 2. induction H. constructor 1; auto. constructor 6. auto. admit. *)
(*  constructor 2 with (t [u]). constructor 6; auto. admit. auto. *)
(* Qed. *)

Instance eqC_equiv: Equivalence eqC.
Proof.
Admitted.

(** Lex rules *)

Inductive rule_b : Rel pterm  :=
   reg_rule_b : forall (t u:pterm),  
     rule_b (pterm_app(pterm_abs t) u) (t[u]).

Lemma term_regular_b: term_regular rule_b.
Proof.
  Admitted.

Lemma red_rename_b: red_rename rule_b.
Proof.
  unfold red_rename.
  intros x t t' y Hfv Hfv' Hb.
  unfold open in *.
  inversion Hb; subst.
  assert (Hc: t = (close (pterm_app (pterm_abs t0) u) x)).
  {
    admit.
  }
  assert (Hc': t' = (close (t0 [u]) x)).
  {
    admit.
  }
  rewrite Hc.
  rewrite Hc'.
  unfold open in *.
  simpl.
  
  inversion H0.
Admitted.

Definition b_ctx t u := ES_contextual_closure rule_b t u. 
Notation "t ->_B u" := (b_ctx t u) (at level 66).

Corollary term_regular_b_ctx : term_regular b_ctx.
Proof.
  apply term_regular_ctx.
  apply term_regular_b.
Qed.
  
Inductive sys_x : Rel pterm :=
| reg_rule_var : forall t, sys_x (pterm_bvar 0 [t]) t
| reg_rule_gc : forall t u, sys_x (t[u]) t
| reg_rule_app : forall t1 t2 u, 
  sys_x ((pterm_app t1 t2)[u]) (pterm_app (t1[u]) (t2[u]))
| reg_rule_lamb : forall t u, 
  sys_x ((pterm_abs t)[u]) (pterm_abs ((& t)[u]))
| reg_rule_comp : forall t u v, has_free_index 0 u ->
  sys_x (t[u][v]) (((& t)[v])[ u[ v ] ]).

Lemma term_regular_sys_x: term_regular sys_x.
Proof.
  Admitted.
  
Definition x_ctx t u := ES_contextual_closure sys_x t u. 
Notation "t ->_x u" := (x_ctx t u) (at level 59, left associativity).

Corollary term_regular_x_ctx : term_regular x_ctx.
Proof.
  apply term_regular_ctx.
  apply term_regular_sys_x.
Qed.

Inductive lx: Rel pterm :=
| b_ctx_rule : forall t u, t ->_B u -> lx t u
| x_ctx_rule : forall t u, t ->_x u -> lx t u.
Notation "t ->_Bx u" := (lx t u) (at level 59, left associativity).

Lemma Bx_app_left: forall t t' u, t ->_Bx t' -> pterm_app t u ->_Bx pterm_app t' u. 
Proof.
  intros t t' u HBx.
  inversion HBx; subst; clear HBx.
  - apply b_ctx_rule.
    apply ES_app_left; assumption.
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
Qed.    

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
    apply red_rename_b_ctx.
Admitted.

Lemma Bx_sub_in: forall u u' t, u ->_Bx u' -> (t[u]) ->_Bx (t[u']). 
Proof.
  intros u u' t HBx.
  inversion HBx; subst; clear HBx.
  - apply b_ctx_rule.
    apply ES_sub_in; assumption.
  - apply x_ctx_rule.
    apply ES_sub_in; assumption.
Qed.    

Corollary term_regular_lx: term_regular lx.
Proof.
  unfold term_regular.
  intros t t' HBx.
  induction HBx.
  - apply term_regular_b_ctx; assumption.
  - apply term_regular_x_ctx; assumption.
Qed.
    
Definition trans_x t u := trans x_ctx t u.
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
Qed.    

Lemma x_trans_sub: forall t t' u L, (forall x, x \notin L -> t^x ->_x+ t'^x) -> (t[u]) ->_x+ (t'[u]). 
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
Qed.

Definition ex t u := red_ctx_mod_eqC x_ctx t u.
Notation "t ->_ex u" := (ex t u) (at level 59, left associativity).

Lemma ex_app_left: forall t t' u, t ->_ex t' -> pterm_app t u ->_ex pterm_app t' u. 
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
Qed.

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
    + apply ES_sub_in; assumption.
    + rewrite Heq'.
      apply refl.
Qed.
  
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

Lemma ex_trans_app_left: forall t t' u, t ->_ex+ t' -> pterm_app t u ->_ex+ pterm_app t' u. 
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

Lemma ex_trans_sub: forall t t' u L, (forall x, x \notin L -> t^x ->_ex+ t'^x) -> (t[u]) ->_ex+ (t'[u]). 
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
Qed.
  
Corollary term_regular_trans_ex : term_regular trans_ex.
Proof.
  apply term_regular_trans.
  apply term_regular_ex.
Qed.
  
Lemma full_comp: forall t u, t[u] ->_ex+ (t ^^ u). 
Proof.
Admitted.

Definition lex t u := red_ctx_mod_eqC lx t u.
Notation "t ->_lex u" := (lex t u) (at level 59, left associativity).

Lemma lex_app_left: forall t t' u, t ->_lex t' -> pterm_app t u ->_lex pterm_app t' u. 
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
Qed.

Lemma lex_sub: forall t t' u L, (forall x, x \notin L -> t^x ->_lex t'^x) -> (t[u]) ->_lex (t'[u]). 
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
Qed.      
    
Corollary term_regular_lex : term_regular lex.
Proof.
  apply term_regular_red_ctx_mod_eqC.
  apply term_regular_lx.
Qed.
  
Definition trans_lex t u := trans lex t u.
Notation "t ->_lex+ u" := (trans_lex t u) (at level 59, left associativity).

Lemma lex_trans_app_left: forall t t' u, t ->_lex+ t' -> pterm_app t u ->_lex+ pterm_app t' u. 
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
Qed.

Lemma lex_trans_sub: forall t t' u L, (forall x, x \notin L -> t^x ->_lex+ t'^x) -> (t[u]) ->_lex+ (t'[u]). 
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
Qed.

Corollary term_regular_trans_lex : term_regular trans_lex.
Proof.
  apply term_regular_trans.
  apply term_regular_lex.
Qed.
  
Lemma trans_ex_to_lex: forall t u, t ->_ex+ u -> t ->_lex+ u.
Proof.
Admitted.

Definition refltrans_lex t u := refltrans lex t u.
Notation "t ->_lex* u" := (refltrans_lex t u) (at level 59, left associativity).

Lemma lex_refltrans_app_left: forall t t' u, t ->_lex* t' -> pterm_app t u ->_lex* pterm_app t' u. 
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
Qed.

Lemma lex_refltrans_sub: forall t t' u L, (forall x, x \notin L -> t^x ->_lex* t'^x) -> (t[u]) ->_lex* (t'[u]). 
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
Qed.

(** Superdevelopment function *)
Fixpoint sd (t : pterm) : pterm :=
  match t with
  | pterm_bvar i    => t
  | pterm_fvar x    => t
  | pterm_abs t1    => pterm_abs (sd t1)
  | pterm_app t1 t2 => let t0 := (sd t1) in
                      match t0 with
                      | pterm_abs t' => t' ^^ (sd t2)
                      | _ => pterm_app (sd t1) (sd t2)
                      end 
  | pterm_sub t1 t2 => (sd t1) ^^ (sd t2)
  end.

Lemma sd_term: forall t, term t -> term (sd t).
Proof.
Admitted.

Corollary sd_body: forall t, body t -> body (sd t).
Proof.
Admitted.

Lemma sd_app: forall t u, pterm_app (sd t) (sd u) ->_lex* sd(pterm_app t u). 
Proof.
Admitted.

Lemma lex_refltrans_app: forall t u t' u', t ->_lex* t' -> u ->_lex* u' -> pterm_app t u  ->_lex* pterm_app t' u'.
Proof.
  intros t u t' u' Htt' Huu'.
  apply refltrans_composition with (pterm_app t u').
  - clear Htt'.
    apply lex_refltrans_app_right; assumption.
  - clear Huu'.
    apply lex_refltrans_app_left; assumption.
Qed.

Lemma abs_sd: forall t1 L , (forall x, x \notin L -> t1 ^ x ->_lex* sd (t1 ^ x)) ->  pterm_abs t1 ->_lex* pterm_abs (sd t1).
Proof.
  Admitted.

Lemma lex_refltrans_sd_sub: forall t L u t' u', (forall x, x \notin L -> t ^ x ->_lex* sd (t ^ x)) -> u ->_lex* u' -> (t [ u ])  ->_lex* (t' [ u' ]).
Proof.
  Admitted.

Lemma to_sd: forall t, term t -> t ->_lex* (sd t).
Proof.
  induction 1.
  - apply refl.
  - apply refltrans_composition with (pterm_app (sd t1) (sd t2)).
    + apply lex_refltrans_app; assumption.
    + apply sd_app.
  - clear H.
    generalize dependent L.
    apply abs_sd.
  - simpl.
    apply refltrans_composition with ((sd t1) [(sd t2)]).
    + apply lex_refltrans_sd_sub with L.
      * assumption.
      * assumption.
    + apply trans_to_refltrans.
      apply trans_ex_to_lex.
      apply full_comp.
Qed.

Lemma BxZlex: forall a b, a ->_lex b -> b ->_lex* (sd a) /\ (sd a) ->_lex* (sd b).
Proof.
Admitted.
  
Theorem Zlex: Zprop lex.
Proof.
  unfold Zprop.
  exists sd.
  apply BxZlex.
Qed.

Corollary lex_is_confluent: Confl lex.
Proof.
  apply Zprop_implies_Confl.
  apply Zlex.
Qed.