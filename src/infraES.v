(** * An application: Proving Confluence of a Calculus with Explicit Substitutions *)

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

Inductive lc: pterm -> Prop :=
  | lc_var: forall x, lc (pterm_fvar x)
  | lc_app: forall t1 t2, lc t1 -> lc t2 -> lc (pterm_app t1 t2)
  | lc_abs: forall t1 L,  (forall x, x \notin L -> lc (t1^x)) -> lc (pterm_abs t1)
  | lc_sub: forall t1 t2 L,  (forall x, x \notin L -> lc (t1^x)) -> lc t2 -> lc (pterm_sub t1 t2).
  
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
  - intros n' Hlc.
    simpl in *.
    destruct (n' === n).
    + apply term_to_lc_at in T.
      apply lc_at_weaken_ind with 0.
      * assumption.
      * auto with arith.
    + simpl.
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
  - intros x y m n Hlc.
    simpl in *.
    destruct Hlc as [H1 H2]; split.
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
    + intro Hlc.
      inversion Hlc.
    + intro Hlc.
      apply term_var.
    + simpl.
      intro Hlc.
      destruct Hlc as [Hlc1 Hlc2].
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
    + intro Hlc. 
      apply term_abs with (fv t0).
      intros x Hfv.
      apply H.
      * rewrite pterm_size_open.
        simpl; auto.
      * simpl in Hlc.
        apply lc_at_open.
        ** apply term_var.
        ** assumption.
    + intro Hlc.
      apply term_sub with (fv t0_1).
      * intros x Hfv.
        apply H.
        ** rewrite pterm_size_open.
           simpl; auto with arith.
        ** simpl in Hlc.
           apply lc_at_open.
           *** apply term_var.
           *** apply Hlc.
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
        ** simpl in Hlc.
           apply Hlc.
Qed.

Lemma lc_equiv_lc_at: forall t, lc t <-> lc_at 0 t.
Proof.
  split.
  - intro Hlc.
    induction Hlc.
    + simpl.
      tauto.
    + simpl.
      split; assumption.
    + simpl.
      pick_fresh x.
      apply notin_union in Fr.
      destruct Fr as [Fr Hfvt1].
      clear Hfvt1 H.
      apply H0 in Fr.
      unfold open in Fr.
      apply lc_at_open_var_rec in Fr; assumption.
    + split.
      * pick_fresh x.
        apply notin_union in Fr.
        destruct Fr as [Fr Hfvt2].
        apply notin_union in Fr.
        destruct Fr as [Fr Hfvt1].
        clear Hfvt1 Hfvt2 H.
        apply H0 in Fr.
        unfold open in Fr.
        apply lc_at_open_var_rec in Fr; assumption.
      * assumption.
  - intro Hlc_at.
    apply term_equiv_lc_at in Hlc_at.
    induction Hlc_at.
    + apply lc_var.
    + apply lc_app; assumption.
    + apply lc_abs with L; assumption.
    + apply lc_sub with L; assumption.
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
  - intros k i Hneq Hlc.
    simpl in *.
    case (i === n).
    + intro.
      inversion e; subst.
      simpl.
      destruct Hlc. 
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
  - intros k i Hneq Hlc.
    simpl in *.
    split.
    + apply IHt1 in Hneq.
      * assumption.
      * apply Hlc.
    + apply IHt2 in Hneq.
      * assumption.
      * apply Hlc.
  - intros k i Hneq  Hlc .
    simpl in *.
    apply IHt.
    + auto.
    + assumption.
  - intros k i Hneq Hlc.
    simpl in *.
    split.
    + assert (HneqS: S k <> S (S i)).
      {
        auto.
      }
      apply IHt1 in HneqS.
      * assumption. 
      * apply Hlc.
    + apply IHt2 in Hneq.
      * assumption.
      * apply Hlc.
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

