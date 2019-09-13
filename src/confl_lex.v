Require Import lex.
Require Import ZtoConfl.

(** Superdevelopment function *)

Fixpoint sd (t : pterm) : pterm :=
  match t with
  | pterm_abs t1    => pterm_abs (sd t1)
  | pterm_app t1 t2 => let t0 := (sd t1) in
                      match t0 with
                      | pterm_abs t' => t' ^^ (sd t2)
                      | _ => pterm_app (sd t1) (sd t2)
                      end 
  | pterm_sub t1 t2 => (sd t1) ^^ (sd t2)
  | _ => t
  end.
(* begin hide *)
(* Lemma sd_open_rec_preserves_structure: forall t t' k, sd t = t' -> forall x, sd (open_rec k (pterm_fvar x) t) = open_rec k (pterm_fvar x) t'. 
Proof.
  intro t; induction t.
  - intros t k Hsd x.
    generalize dependent Hsd.
    case n.
    + simpl.
      intro H.
      destruct (k === 0).
      * rewrite <- H.
        rewrite e.
        reflexivity.
      * rewrite <- H.
        simpl.
        destruct (k === 0).
        ** contradiction.
        ** reflexivity.
    + intros n' Hsd.
      rewrite <- Hsd.
      simpl.
      destruct (k === S n'); reflexivity.
  - intros t k Hsd x.
    rewrite <- Hsd; reflexivity.
  - intros t k Hsd x.
    rewrite <- Hsd.
    admit.
  - intros t k Hsd x.
    rewrite <- Hsd.
    simpl.
    f_equal.
    apply IHt; reflexivity.
  - Admitted. 
    
Lemma sd_open_preserves_structure: forall t t', sd t = t' -> forall x, sd (t^x) = t'^x. 
Proof.
  intro t; induction t.
  - intros t' H x.
    unfold open.
    generalize dependent H.
    case n.
    + intro H; simpl.
      rewrite <- H.
      reflexivity.
    + intros n' H.
      rewrite <- H.
      reflexivity.
  - intros t H x.
    rewrite <- H.
    reflexivity.
  - intros t H x.
    specialize (IHt2 (sd t2)).
    assert (Hsdt2: forall x : var, sd (t2 ^ x) = sd t2 ^ x).
    {
     apply IHt2.
     reflexivity.
    }
Admitted. 
  
Lemma sd_open_rec:  forall t x i, sd ({i ~> x} t) = {i ~> x} (sd t).
Proof.
Admitted. *)
  
Lemma sd_open:  forall x t, sd (t ^ x) = sd t ^ x.
Proof.
  intros x t.
  generalize dependent x.
  induction t.
  - intros x; simpl.
    unfold open.
    case n; reflexivity.
  - reflexivity.
  - intros x.
    unfold open in *.
    change ({0 ~> pterm_fvar x} pterm_app t1 t2) with (pterm_app ({0 ~> pterm_fvar x} t1) ({0 ~> pterm_fvar x} t2)).
    generalize dependent t1.
    intro t1. case t1.
    + intro n; case n. 
      * intro IH.
        simpl.
        rewrite IHt2; reflexivity.        
      * intros n' IH.
        simpl.
        rewrite IHt2; reflexivity.        
    + intros v IH.
      simpl.
        rewrite IHt2; reflexivity.        
    + intros p1 p2 IH. admit.
    + admit.
    + admit.
  - intros x. simpl.
    admit. 
Admitted.
    
Lemma sd_term: forall t, term t -> term (sd t).
Proof.
  Admitted.
  (* intros t Hterm. *)
  (* induction Hterm.   *)
  (* - admit. *)
  (* - admit. *)
  (* - simpl sd. *)
  (*   apply term_abs with L. *)
  (*   intro x. *)
  (*   (* Lemma sd_open:  forall x : elt, x \notin L ->  term (sd (t1 ^ x)) -> term (sd t1 ^ x) *) *)
  (*   replace (sd t1 ^ x) with (sd (t1 ^ x)). *)
  (*   apply H0. *)
  (*   apply sd_open. *)
  (* - Admitted.  *)

Corollary sd_body: forall t, body t -> body (sd t).
Proof.
Admitted. 

Lemma sd_app_lx: forall t u, pterm_app (sd t) (sd u) ->_lx* sd(pterm_app t u). 
Proof.
Admitted.

Lemma sd_app_lex: forall t u, pterm_app (sd t) (sd u) ->_lex* sd(pterm_app t u). 
Proof.
  intro t; induction t.
  - intro u; simpl.
    apply refl.
  - intro u; simpl.
    apply refl.
  - intro u.
Admitted.
 

(* Lemma lex_refltrans_app: forall t u t' u', t ->_lex* t' -> u ->_lex* u' -> pterm_app t u  ->_lex* pterm_app t' u'.
Proof.
  intros t u t' u' Htt' Huu'.
  apply refltrans_composition with (pterm_app t u').
  - clear Htt'.
    apply lex_refltrans_app_right; assumption.
  - clear Huu'.
    apply lex_refltrans_app_left; assumption.
Qed. *)

Lemma abs_sd: forall t1 L , (forall x, x \notin L -> t1 ^ x ->_lex* sd (t1 ^ x)) ->  pterm_abs t1 ->_lex* pterm_abs (sd t1).
Proof.
  Admitted.

Lemma lex_refltrans_sd_sub: forall t L u t' u', (forall x, x \notin L -> t ^ x ->_lex* sd (t ^ x)) -> u ->_lex* u' -> (t [ u ])  ->_lex* (t' [ u' ]).
Proof.
  Admitted.

Lemma to_sd: forall t, term t -> t ->_lx* (sd t).
Proof.
  intros t Hterm.
  induction Hterm.
  - apply refl.
  - generalize dependent t1.
    intro t1. case t1.
    + intros n Hterm IH.
      inversion Hterm.
    + intros v Hterm IH.
      apply lx_star_app_right; assumption.
    + intros p p0 Hterm IH.
      apply refltrans_composition with (pterm_app (sd (pterm_app p p0)) (sd t2)).
      * apply refltrans_composition with (pterm_app (sd (pterm_app p p0)) t2).
        ** apply lx_star_app_left; assumption.
        ** apply lx_star_app_right.
           *** apply sd_term; assumption.
           *** assumption.
      * apply sd_app_lx.
    + intros p Hterm IH.
      apply refltrans_composition with (pterm_app (sd (pterm_abs p)) (sd t2)).
      * apply refltrans_composition with (pterm_app (sd (pterm_abs p)) t2).
        ** apply lx_star_app_left; assumption.
        ** apply lx_star_app_right.
           *** apply sd_term; assumption.
           *** assumption.
      * apply sd_app_lx.
    + intros p p0 Hterm IH.
      apply refltrans_composition with (pterm_app (sd (p [p0])) (sd t2)).
      * apply refltrans_composition with (pterm_app (sd (p [p0])) t2).
        ** apply lx_star_app_left; assumption.
        ** apply lx_star_app_right.
           *** apply sd_term; assumption.
           *** assumption.
      * apply sd_app_lx.
  - simpl.
    pick_fresh y.
    assert (H' := H0 y).
    apply notin_union in Fr.
    destruct Fr as [Hfv Fr].
    apply H' in Hfv.
    rewrite sd_open in Hfv.
    apply lx_star_abs with y (fv t1); assumption.
    + assert (H3: t1 = sd t1).
      {
        admit.
      }
      rewrite <- H3.
      apply refl.
    + subst.
      clear IHHfv.
      admit.
    - admit.
Admitted.
  
(*Lemma to_sd: forall t, term t -> t ->_lex* (sd t).
(* begin hide *)
Proof.
  induction 1.
  - apply refl.
  - apply refltrans_composition with (pterm_app (sd t1) (sd t2)).
    + admit.
    + apply sd_app.
Admitted.
  (*   apply refltrans_composition with (pterm_app (sd t1) (sd t2)). *)
    
  (*   + apply lex_refltrans_app; assumption. *)
  (*   + apply sd_app. *)
  (* - clear H. *)
  (*   generalize dependent L. *)
  (*   apply abs_sd. *)
  (* - simpl. *)
  (*   apply refltrans_composition with ((sd t1) [(sd t2)]). *)
  (*   + apply lex_refltrans_sd_sub with L. *)
  (*     * assumption. *)
  (*     * assumption. *)
  (*   + apply trans_to_refltrans. *)
  (*     apply trans_ex_to_lex. *)
  (*     apply full_comp. *)
       Admitted. *)
(* end hide *)

Lemma ES_Bx_sub: forall t t' u x, term u -> t^x ->_Bx t'^x -> t[u] ->_Bx (t'[u]).
Proof.
  intros t t' u x Hterm HBx.
  generalize dependent u.
  remember (t^x) as t1.
  remember (t'^x) as t2.
  induction HBx; subst.
  - intros v Hterm.
    apply b_ctx_rule.
    apply ES_sub with (fv t).
    + intros x' Hnotin.
      admit.
    + assumption.
  - intros u Hterm.
    apply x_ctx_rule.
    apply ES_sub with (fv t).
    + intros x' Hnotin.
      admit.
    + assumption.
Admitted.

Lemma ES_Bx_sub_in: forall t u u', body t -> u ->_Bx u' -> t[u] ->_Bx (t[u']).
Proof.
  intros t u u' Hbody HBx.
  generalize dependent t.
  induction HBx.
  - intros t Hbody.
    apply b_ctx_rule.
    apply ES_sub_in; assumption.
  - intros t Hbody.
    apply x_ctx_rule.
    apply ES_sub_in; assumption.
Qed.

Lemma ES_lex_sub: forall t t' u x, term u -> t^x ->_lex* (t')^x -> t[u] ->_lex* (t'[u]).
Proof.
Admitted.

Lemma ES_lex_sub_in: forall t u u', body t -> u ->_lex* u' -> t[u] ->_lex* (t[u']).
Proof.
  intros t u u' Hbody Hlex.
  generalize dependent t.
  induction Hlex.
  - intros t Hbody.
    apply refl.
  - intros t Hbody.
    apply rtrans with (t[b]).
    + unfold lex in *.
      unfold red_ctx_mod_eqC in *.
      destruct H as [a' [b' [H1 [HBx H2]]]].
      exists (t[a']).
      exists (t[b']); split.
      * rewrite H1; reflexivity.
      * split.
        ** apply ES_Bx_sub_in; assumption.
        ** rewrite H2; reflexivity.
    + apply IHHlex; assumption.
Qed.

Lemma eqC_equal: forall a b,  a =c b -> (sd a) = (sd b).
Proof.
Admitted.

Lemma Bx_Z_lex: forall a b, a ->_lx b -> b ->_lex* (sd a) /\ (sd a) ->_lex* (sd b).
(* begin hide *)
Proof.
  intros a b Hlex.
  induction Hlex.
  destruct H as [x' [H1 [HBx H2]]].
  rewrite <- H1 in HBx; clear H1.
  rewrite H2 in HBx; clear H2.
  induction HBx.
  - inversion H; subst; clear H.
    + split.
      * inversion H0; subst.
        simpl sd.
        apply refltrans_composition with (sd t1 [sd u0]).
        ** apply refltrans_composition with (sd t1 [u0]).
           *** pick_fresh y.
               apply ES_lex_sub with y.
               **** assumption.
               **** rewrite <- sd_open.
                    apply to_sd.
                    apply body_to_term.
                    {
                      apply notin_union in Fr.
                      destruct Fr as [Fr Hu0].
                      apply notin_union in Fr.
                      destruct Fr as [Fr Ht1].
                      assumption.
                    }
                    {
                      assumption.
                    }
           *** apply ES_lex_sub_in.
               **** admit.
               **** apply to_sd; assumption.
        ** admit.
      * Admitted.
(* end hide *)

Theorem Z_lex: Z_prop lex.
Proof.
  unfold Z_prop.
  exists sd.
  apply Bx_Z_lex.
Qed.

Corollary lex_is_confluent: Confl lex.
Proof.
  apply Z_prop_implies_Confl.
  apply Z_lex.
Qed.
