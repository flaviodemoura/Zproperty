(** Confluence of the Lex-calculus through Z property. *)

Require Import ZtoConfl.
        
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

Lemma notin_union : forall x E F,
  x \notin (E \u F) <-> (x \notin E) /\ (x \notin F).
Proof. Admitted.

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
  - inversion IHl as [x H]. Admitted.
(*     exists (max x l); intros y J; simpl in J. *)
(*     inversion J; subst; auto with arith. *)
(*     destruct J. *)
(*     assert (y <= x); auto using max_lt_l. *)
(*       apply H. *)
(*     +  *)
(* Qed. *)

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
  destruct pf. Admitted.
(*   rewrite elements_iff in a. *)
(*   rewrite InA_alt in a. *)
(*   destruct a as [y [H1 H2]]. *)
(*   subst. *)
(*   assumption. *)
(* Qed. *)

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

Definition body t := exists L, forall x, x \notin L -> term (t ^ x).

(* (** Specialized induction principle for preterms. *) *)
(* Theorem pterm_induction : forall P : pterm -> Prop, *)
(*        (forall n : nat, P (pterm_bvar n)) -> *)
(*        (forall v : var, P (pterm_fvar v)) -> *)
(*        (forall t1, P t1 -> forall t2, P t2 -> P (pterm_app t1 t2)) -> *)
(*        (forall L t, (forall x, x \notin L -> P (t ^ x)) -> P (pterm_abs t)) -> *)
(*        (forall L t1, (forall x, x \notin L -> P (t1 ^ x)) -> forall t2, P t2 -> P (t1 [t2])) -> *)
(*        forall t, P t. *)
(* Proof. *)
(*   intros P Hbvar Hfvar Happ Habs Hsubs t. *)
(*   induction t. *)
(*   - apply Hbvar. *)
(*   - apply Hfvar. *)
(*   - apply Happ; assumption. *)
(*   - apply Habs with (fv t0). *)
(*     intros x Hfv. *)
(*     unfold open. *)
(*     induction t0.     *)
(*     + case n eqn: Hn. *)
(*       * simpl. *)
(*         apply Hfvar. *)
(*       * subst. *)
(*         simpl. *)
(*         assumption. *)
(*     + simpl. *)
(*       apply Hfvar. *)
(*     + simpl. *)
(*       apply Happ. *)
(*       assert (H:  P t0_1). *)
(*       { *)
        
(*       } *)
(*       * apply IHt0_1. *)
(*       * *)
(*     + *)
(*     + *)
(*   - *)

    
(** Local closure of terms *)
Fixpoint lc_at (k:nat) (t:pterm) : Prop :=
  match t with
  | pterm_bvar i    => i < k
  | pterm_fvar x    => True
  | pterm_app t1 t2 => lc_at k t1 /\ lc_at k t2
  | pterm_abs t1    => lc_at (S k) t1
  | pterm_sub t1 t2 => (lc_at (S k) t1) /\ lc_at k t2
  end.

Lemma lc_at_open_rec : forall x t k,
  lc_at k (open_rec k x t) -> lc_at (S k) t.
Proof.
  Admitted.

Lemma lc_at_one_open_rec: forall t x, lc_at 1 t -> term (t ^ x).
Proof.
  intro t; induction t.
  
  Admitted.

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
      apply lc_at_open_rec with (pterm_fvar y).
      apply H0.
      apply notin_union in Fr.
      apply Fr.
    + simpl; split.
      * pick_fresh y.
        unfold open in H0.
        apply lc_at_open_rec with (pterm_fvar y).
        apply H0.
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
      apply lc_at_one_open_rec.
      assumption.
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

Definition b_ctx t u := red_ctx_mod_eqC rule_b t u. 
Notation "t ->_B u" := (b_ctx t u) (at level 66).

Inductive sys_x : Rel pterm :=
| reg_rule_var : forall t, sys_x (pterm_bvar 0 [t]) t
| reg_rule_gc : forall t u, term t -> sys_x (t[u]) t
| reg_rule_app : forall t1 t2 u, 
  sys_x ((pterm_app t1 t2)[u]) (pterm_app (t1[u]) (t2[u]))
| reg_rule_lamb : forall t u, 
  sys_x ((pterm_abs t)[u]) (pterm_abs ((& t)[u]))
| reg_rule_comp : forall t u v, has_free_index 0 u ->
  sys_x (t[u][v]) (((& t)[v])[ u[ v ] ]).

Definition x_ctx t u := red_ctx_mod_eqC sys_x t u. 
Notation "t ->_ex u" := (x_ctx t u) (at level 59, left associativity).

Definition trans_ex t u := trans x_ctx t u.
Notation "t ->_ex+ u" := (trans_ex t u) (at level 59, left associativity).

Lemma full_comp: forall t u, body t -> term u ->  
                t[u] ->_ex+ (t ^^ u). 
Proof.
Admitted.

Inductive lex: Rel pterm :=
| b_ctx_rule : forall t u, t ->_B u -> lex t u
| x_ctx_rule : forall t u, t ->_ex u -> lex t u.
Notation "t ->_lex u" := (lex t u) (at level 59, left associativity).

Definition trans_lex t u := trans lex t u.
Notation "t ->_lex+ u" := (trans_lex t u) (at level 59, left associativity).

Lemma trans_ex_to_lex: forall t u, t ->_ex+ u -> t ->_lex+ u.
Proof.
  Admitted.

Definition refltrans_lex t u := refltrans lex t u.
Notation "t ->_lex* u" := (refltrans_lex t u) (at level 59, left associativity).

Lemma lex_trans: forall t u v, t ->_lex* u -> u ->_lex* v -> t ->_lex* v.
Proof.
  Admitted.
  
Lemma sys_BxEqc: forall a a' b b', a ->_lex b -> a =e a' -> b =e b' -> a' ->_lex b'.
Proof.
Admitted.  

(** Superdevelpment function *)
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

Lemma refltrans_app: forall t u t' u', t ->_lex* t' -> u ->_lex* u' -> pterm_app t u  ->_lex* pterm_app t' u'.
Proof.
  intros t u t' u' Htt' Huu'.
  apply refltrans_composition with (pterm_app t u').
  - clear Htt'.
    inversion Huu'; subst.
    + apply refl.
    + clear Huu'.
      apply rtrans with (pterm_app t b).
      * inversion H; subst.
        ** clear H. clear H0.
           unfold b_ctx in H1.
           unfold red_ctx_mod_eqC in H1.
           destruct H1. destruct H.
           destruct H as [ Heq1 [Hb Heq2]].
           apply b_ctx_rule.
           unfold b_ctx.
           unfold red_ctx_mod_eqC.
           exists (pterm_app t x).
           exists (pterm_app t x0).
           split.
           *** apply ES_app_right.
             
      *
  - 
    
Admitted.

Lemma abs_sd: forall t1 L , (forall x, x \notin L -> t1 ^ x ->_lex* sd (t1 ^ x)) ->  pterm_abs t1 ->_lex* pterm_abs (sd t1).
Proof.
Admitted.

Lemma refltrans_sub: forall t L u t' u', (forall x, x \notin L -> t ^ x ->_lex* sd (t ^ x)) -> u ->_lex* u' -> (t [ u ])  ->_lex* (t' [ u' ]).
Proof.
  Admitted.

Lemma to_sd: forall t, term t -> t ->_lex* (sd t).
Proof.
  induction 1.
  - apply refl.
  - apply refltrans_composition with (pterm_app (sd t1) (sd t2)).
    + apply refltrans_app; assumption.
    + apply sd_app.
  - clear H.
    generalize dependent L.
    apply abs_sd.
  - simpl.
    apply refltrans_composition with ((sd t1) [(sd t2)]).
    + apply refltrans_sub with L.
      * assumption.
      * assumption.
    + apply trans_to_refltrans.
      apply trans_ex_to_lex.
      apply full_comp.
      * pick_fresh y.
        assert (Ht1: term (t1 ^ y)).
        {
          apply H.
          apply notin_union in Fr.
          destruct Fr as [HFr Ht2].
          apply notin_union in HFr.
          apply HFr.
        }
        admit.
      * apply sd_term; assumption.
Admitted.
        
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