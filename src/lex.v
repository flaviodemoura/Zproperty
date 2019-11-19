(** * An application: Proving Confluence of a Calculus with Explicit Substitutions *)

(* begin hide *)
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
(* end hide *)

(** Pre-terms are defined according to the following grammar: *)
Inductive pterm : Set :=
  | pterm_bvar : nat -> pterm
  | pterm_fvar : var -> pterm
  | pterm_app  : pterm -> pterm -> pterm
  | pterm_abs  : pterm -> pterm
  | pterm_sub : pterm -> pterm -> pterm.

Notation "t [ u ]" := (pterm_sub t u) (at level 70).
(* begin hide *)
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

(* end hide *)
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
(* begin hide *)
Hint Constructors term.

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

Lemma lc_at_open_rec_leq : forall n k t u, n <= k -> lc_at n t -> lc_at n (open_rec k u t).
Proof.
  intros n k t0.
  generalize dependent k.
  generalize dependent n.
  induction t0.
  - intros n' k u Hleq Hlc_at. 
    simpl.
    destruct (k === n).
    + subst.
      inversion Hlc_at.
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
    case (k === n).
    + intros Heq Hlc; subst.
      simpl; auto.
    + intros Hneq Hlc.
      simpl; auto.
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

(* end hide *)  
Lemma pterm_size_induction :
 forall P : pterm -> Prop,
 (forall t,
    (forall t', pterm_size t' < pterm_size t ->
    P t') -> P t) ->
 (forall t, P t).
(* begin hide *)
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
      apply lc_rec_open_var_rec in Fr; assumption.
    + split.
      * pick_fresh x.
        apply notin_union in Fr.
        destruct Fr as [Fr Hfvt2].
        apply notin_union in Fr.
        destruct Fr as [Fr Hfvt1].
        clear Hfvt1 Hfvt2 H.
        apply H0 in Fr.
        unfold open in Fr.
        apply lc_rec_open_var_rec in Fr; assumption.
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
Admitted.

(* The next lemma fails if t is not a term: take t = k = 0 *)
Lemma open_rec_close_rec_term': forall t x k, term t ->  open_rec k (pterm_fvar x) (close_rec k x t) = t.
Proof.
  intro t; induction t.
  - intros x k Hterm.
    inversion Hterm.
  - intros x k Hterm.
    simpl.
    destruct (v == x).
    + subst. simpl.
      destruct (k === k).
      * reflexivity.
      * contradiction.
    + reflexivity.
  - intros x k Hterm.
    inversion Hterm; subst; clear Hterm.
    apply (IHt1 x k) in H1.
    apply (IHt2 x k) in H2.
    simpl.
    rewrite H1.
    rewrite H2; reflexivity.
  - intros x k Hterm.
    inversion Hterm; subst.
    simpl.
    admit. (* não conseguimos utilizar a h.i.*)
  - Admitted.

Lemma term_bvar: forall n x, term (pterm_bvar n^x) -> n=0.
Proof.
  Admitted.

Lemma open_rec_close_rec_term: forall t x k, term t ->  open_rec k (pterm_fvar x) (close_rec k x t) = t.
Proof.
  intros t x k Hterm.
  generalize dependent k.
  induction Hterm.
  - intro k.
    simpl.
    destruct (x0 == x).
    + rewrite e.
      simpl.
      destruct (k === k).
     *  reflexivity.
     *  contradiction.
    + reflexivity.
  - intro k.
    simpl.
    rewrite IHHterm1.
    rewrite IHHterm2.
    reflexivity.
  - pick_fresh y.
    apply notin_union in Fr.
    destruct Fr as [Fr Hfv1].
    apply notin_union in Fr.
    destruct Fr as [Fr Hx].
    intro k; simpl.
    unfold open in H0.
    generalize dependent t1.
    intro t1; induction t1.
    + intros.
      change (close_rec (S k) x (pterm_bvar n)) with (pterm_bvar n).
      apply H in Fr.
      apply term_bvar in Fr.
      subst.
      reflexivity.
    + intros.
      simpl.
      destruct (v == x).
      * subst. simpl.
        destruct (k === k).
        ** reflexivity.
        ** contradiction.
      * reflexivity.
    + intros.
      simpl.
      
    +
      * unfold open in H2.
        inversion H2.
      *
      *
      *
      simpl.
    +
    +
    +
    +
      
    clear Hx Hfv1.
    
   (* apply pterm_abs_open with y. *)
    unfold open in *.
    rewrite <- (H0 y) with (S k).
    + apply open_k_Sk.
      apply lt_0_neq.
      apply gt_Sn_O.
    + assumption.
  - pick_fresh y.
    apply notin_union in Fr.
    destruct Fr as [Fr Hfv2].
    apply notin_union in Fr.
    destruct Fr as [Fr Hfv1].
    apply notin_union in Fr.
    destruct Fr as [Fr Hx].
    intro k; simpl.
    rewrite IHHterm.
    assert (H1: {S k ~> pterm_fvar x} close_rec (S k) x (t1 ^ y) = t1 ^ y).
    {
      apply H0; assumption.
    }
    clear Hx Hfv1 Hfv2 Fr H0 Hterm.
Admitted.
  
Corollary open_close_term: forall t x, term t -> (close t x)^x = t.
Proof.
  intros t x.
  apply open_rec_close_rec_term.
Qed.


(** The locally nameless framework manipulates expressions that are a representation of the lambda-terms, and not all pre-terms. In this sense, if t reduces to t' then both t and t' are terms: *)
Definition term_regular (R : Rel pterm) :=
  forall t t', R t t' -> term t /\ term t'.

(* begin hide *)
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

(** The substitution is compositional.
Lemma open_comp: forall t u v, (t ^^ u ) ^^ v  = ((&t) ^^ v) ^^ (u ^^ v).
Proof.
  intro t; induction t.
  - case n.
    + intros u v; unfold open; simpl.
      admit.
    + Admitted.
*)

(** The above notion of substitution is not capture free because it is
defines over pre-terms. Nevertheless it is a capture free substitution
when [u] is a term: *)
(* Lemma open_capture_free: forall t u, term u -> *)

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

(* Lemma term_open_rec_eq: forall t n x u, term (t^x) -> ~(has_free_index 0 t) -> {n ~> u} t ^ x = ({n ~> u} t) ^ x. *)
(* Proof. *)
(*   intro t; induction t. *)
(*   - intros n' x u. *)
(*     unfold open. *)
(*     case n. *)
(*     + intro H. *)
(*       simpl. *)
(* Admitted. *)

(* assert (H': forall (n : nat) (u : pterm), {n ~> u} t1 ^ y = t1 ^ y). *)
(* { *)
(*   apply H0; assumption. *)
(* } *)

(* Lemma open_rec_f_equal:  forall t t' x,  t ^ x = t' ^ x -> t = t'. *)
(* Proof. *)
(* Admitted. *)

(* apply open_rec_f_equal with y. *)
(* rewrite <- term_open_rec_eq. *)
(* + apply H'. *)
(* + apply H; assumption. *)
(* +  *)
(* - Admitted. *)
(* (*       intro t; induction t. *) *)
(* (*   - intros u n' Hterm. *) *)
(* (*     inversion Hterm. *) *)
(* (*   - intros u n' Hterm. *) *)
(* (*     reflexivity. *) *)
(* (*   - intros u n' Hterm; simpl. *) *)
(* (*     inversion Hterm; subst. *) *)
(* (*     clear Hterm. f_equal.     *) *)
(* (*     + apply IHt1; assumption. *) *)
(* (*     + apply IHt2; assumption. *) *)
(* (*   - intros u n' Hterm. simpl. *) *)

    
(* (*   generalize dependent n. *) *)
(* (*   generalize dependent u. *) *)
(* (*     generalize dependent t0. *) *)
(* (*   intro t; induction t. *) *)
(* (*   - intros IH u n' Hterm. *) *)
(* (*     inversion Hterm. *) *)
(* (*   - intros IH u n' Hterm. *) *)
(* (*     reflexivity. *) *)
(* (*   - intros IH u n' Hterm. *) *)
(* (*     inversion Hterm; subst. clear Hterm. *) *)
(* (*     simpl. f_equal. *) *)
(* (*     + apply IHt1. *) *)
(* (*       * intros t Hlt u' n'' Hterm. *) *)
(* (*         apply IH. *) *)
(* (*         apply lt_trans with (pterm_size t1). *) *)
(* (*         ** assumption. *) *)
(* (*         ** simpl. *) *)
(* (*            rewrite <- plus_Sn_m. *) *)
(* (*            apply lt_plus_trans. *) *)
(* (*            auto. *) *)
(* (*         ** assumption. *) *)
(* (*       * assumption. *) *)
(* (*     + apply IHt2. *) *)
(* (*       * intros t Hlt u' n'' Hterm. *) *)
(* (*         apply IH. *) *)
(* (*         apply lt_trans with (pterm_size t2). *) *)
(* (*         ** assumption. *) *)
(* (*         ** simpl. *) *)
(* (*            rewrite plus_n_Sm. *) *)
(* (*            rewrite plus_comm. *) *)
(* (*            apply lt_plus_trans. *) *)
(* (*            auto. *) *)
(* (*         ** assumption. *) *)
(* (*       * assumption. *) *)
(* (*   - intros IH u n' Hterm. *) *)
(* (*     simpl. f_equal. *) *)
(* (*     apply IH. *) *)
(* (*     + auto. *) *)
(* (*     + assumption *) *)
(* (*   Admitted. *) *)

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
  
(* end hide *)
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
      * auto.
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
  
Lemma red_rename_b: red_rename rule_b.
Proof.
  unfold red_rename.
  intros x t t' y Hfv Hfv' Hb.
  inversion Hb; subst.
  symmetry in H.
  assert (Hy : t^y = pterm_app ((close (pterm_abs t0) x)^y) (close u x)^y).
  {
    apply open_close_redex; assumption.
  }
  rewrite Hy.
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
  - unfold body in H.
Admitted.

        
(*         unfold open; simpl. *)
(*         apply term_abs with x. *)
(*         intros x'' Hfv'. *)
(*         unfold open. *)
(*         apply term_equiv_lc_at. *)
(*         apply lc_at_open_rec. *)
(*         ** apply term_var. *)
(*         ** apply H in Hfv. *)
(*            unfold open in Hfv. *)
(*            apply term_equiv_lc_at in Hfv. *)
(*            apply lc_at_weaken_ind with 0. *)
(*            admit. *)
(*       * assumption. *)
(*     + admit. *)
(*   - split. *)
(*     + apply term_sub with (fv t0). *)
(*       * intros x Hfv. *)
(*         unfold open; simpl. *)
(*         apply term_sub with (fv t0). *)
(*         ** intros x' Hfv'. *)
(*            unfold open. *)
(*            apply term_equiv_lc_at. *)
(*            apply lc_at_open_rec. *)
(*            *** apply term_var. *)
(*            *** apply lc_at_open_rec. *)
(*                **** apply term_var. *)
(*                **** assumption. *)
(*         ** apply term_equiv_lc_at. *)
(*            apply lc_at_open_rec. *)
(*            *** apply term_var. *)
(*            *** assumption. *)
(*       * assumption. *)
(*     + apply term_sub with (fv t0). *)
(*       * intros x Hfv. *)
(*         unfold open; simpl. *)
(*         apply term_sub with (fv t0). *)
(*         ** intros x' Hfv'. *)
(*            unfold open. *)
(*            apply term_equiv_lc_at. *)
(*            apply lc_at_open_rec. *)
(*            *** apply term_var. *)
(*            *** apply lc_at_open_rec. *)
(*                **** apply term_var. *)
(*                **** apply lc_at_bswap. *)
(*                     { *)
(*                       auto.                       *)
(*                     } *)
(*                     { *)
(*                       assumption. *)
(*                     } *)
(*         ** rewrite open_rec_term; assumption. *)
(*       * apply term_sub with (fv u). *)
(*         ** intros x Hfv. *)
(*            unfold open. *)
(*            apply term_equiv_lc_at. *)
(*            apply lc_at_open_rec. *)
(*            *** apply term_var. *)
(*            *** assumption. *)
(*         ** assumption. *)
(* Admitted. *)
    
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
Notation "t ->_lx* u" := ((refltrans lx) t u) (at level 59, left associativity).

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
  - admit.
Admitted.

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
  clear Fvt1 Fvt2 Fvt3.
  inversion Fr; subst.
  - apply b_ctx_rule.
    apply ES_sub with L.
    + admit.
    + assumption.
  - apply x_ctx_rule.
    apply ES_sub with L.
    + admit.
    + assumption.
Admitted.

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
  induction Fr.
  - admit.
  - assumption.
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
  induction Fr.
  - admit.
  - assumption.
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
    + admit.
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
           Admitted.
  (*       ** reflexivity. *)
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
Admitted.

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
