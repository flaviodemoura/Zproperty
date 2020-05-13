(** * An application: Proving Confluence of a Calculus with Explicit Substitutions *)

(* begin hide *)

Require Import ZtoConfl infraES.

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
  intros t u H. induction H.
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

(** avaliar *)
Lemma red_out:  forall t t' x n, rule_b ({n ~> pterm_fvar x} t) ({n ~> pterm_fvar x} t') -> rule_b t t'.
Proof.
  induction t0.
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
    Admitted.

(** Focar nesta prova *)
Lemma red_rename_b: red_rename rule_b.
Proof.
  unfold red_rename.
  intros x t t' y Hfv Hfv' Hb.
  unfold open in *.
  apply rule_b_compat_open.


  inversion Hb; subst.
  symmetry in H.
  assert (Hy : t^y = pterm_app ((close (pterm_abs t0) x)^y) (close u x)^y).
  {
    apply open_close_redex; assumption.
  }

  Admitted.
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
    + apply term_sub with (fv t0).
      * intros x Hfv.
        unfold open; simpl.
        apply term_var.
      * assumption.
    + assumption.
  - split.
    + apply term_sub with (fv t0).
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
    + apply term_sub with (fv (pterm_abs t0)).
      * intros x Hnot.
        apply body_to_term.
        **  assumption.
        **  apply body_lc_at.
            apply H.
      * assumption.
    + apply term_abs with (fv (& t0[u])).
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
    + apply term_sub with (fv (t0[u])).
      * intros x Hnot.
        apply body_to_term.
        **  assumption.
        **  apply body_lc_at.
            split; assumption.
      * assumption.
    + apply term_sub with (fv (& t0[v])).
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
