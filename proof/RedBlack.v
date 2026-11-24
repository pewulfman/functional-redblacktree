From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
From Coq Require Import Orders.
From Coq Require Import OrdersFacts.
Require Import Lia.

Ltac inv H := inversion H; clear H; subst.

Declare Module X: OrderedType'.
Definition T := X.t.
Definition cmp := X.compare.
Module Facts := OrderedTypeFacts(X).

Lemma inv_order : forall (x y : T),
	cmp x y = Gt <-> cmp y x = Lt.
Proof.
	intros.
	split; intro H.
	- apply Facts.compare_gt_iff in H.
		apply Facts.compare_lt_iff. assumption.
	- apply Facts.compare_lt_iff in H.
		apply Facts.compare_gt_iff. assumption.
Qed.

Lemma order_trans : forall (x y z : T),
	cmp x y = Lt -> cmp y z = Lt -> cmp x z = Lt.
Proof.
	intros x y z H0 H1.
	unfold cmp. apply Facts.compare_lt_iff.
	unfold cmp in H0. apply Facts.compare_lt_iff in H0.
	unfold cmp in H1. apply Facts.compare_lt_iff in H1.
	Facts.order.
Qed.

Corollary order_trans_gt : forall (x y z : T),
	cmp x y = Gt -> cmp y z = Gt -> cmp x z = Gt.
Proof.
	intros x y z H0 H1.
	apply inv_order.
	apply order_trans with y;
	apply inv_order;
	assumption.
Qed.


(* We define a tree as *)
Inductive colour : Type := Red | Black.
Inductive tree (X : Type) :=
	| Leaf
	| Node (c : colour) (l : tree X) (v : X) (r : tree X).

Arguments Leaf {X}.
Arguments Node {X}.

Definition empty_tree (X : Type) : tree X := Leaf.

(* Properties of a red-black tree *)

(* BST properties *)
Fixpoint ForallT {X : Type} (P: X -> Prop) (t: tree X) : Prop :=
  match t with
  | Leaf => True
  | Node c l v r => P v /\ ForallT P l /\ ForallT P r
  end.

Inductive BST {X : Type} {cmp}: tree X -> Prop :=
| BST_Leaf : BST Leaf
| BST_Node : forall c l v r,
    ForallT (fun y => cmp y v = Lt) l ->
    ForallT (fun y => cmp y v = Gt) r ->
    BST l ->
    BST r ->
    BST (Node c l v r).

(** Red-black tree properties **)

(* root is black *)
Inductive IsBlack {X} : tree X -> Prop :=
	| is_black_leaf : IsBlack Leaf
	| is_black_node : forall l r v, IsBlack (Node Black l r v).

Definition isBlack {X} (t : tree X) : bool :=
	match t with
	| Leaf | Node Black _ _ _ => true
	| Node Red _ _ _ => false
	end.

(* no two consecutive red *)
Inductive RedBlack {X} : tree X -> nat -> Prop :=
	| rb_leaf : RedBlack Leaf 0
	| rb_red_node : forall l r v n,
		RedBlack l n ->
		RedBlack r n ->
		IsBlack l ->
		IsBlack r ->
		RedBlack (Node Red l v r) n
	| rb_black_node : forall l r v n,
		RedBlack l n ->
		RedBlack r n ->
		RedBlack (Node Black l v r) (S n).

#[local] Create HintDb db.
#[local] Hint Constructors colour : db.
#[local] Hint Constructors tree : db.
#[local] Hint Constructors IsBlack : db.
#[local] Hint Constructors RedBlack : db.


Example leaf :
	@RedBlack T Leaf 0.
Proof.
	auto with db.
Qed.


Example trio :
	RedBlack (Node Black (Node Black Leaf 1 Leaf) 2 (Node Black Leaf 3 Leaf)) 2.
Proof.
	auto with db.
Qed.

Example red_red : forall X  (x y z : X) n,
	RedBlack (Node Black (Node Red (Node Red Leaf x Leaf) y Leaf) z Leaf) n -> False.
Proof.
	intros.
	inv H.
	inv H4.
	inv H7.
Qed.

(* Insertion algorithm *)
Definition make_black {X} (tr : tree X) : tree X :=
	match tr with
	| Leaf => Leaf
	| Node _ l r v => Node Black l r v
	end.

(* Okasaki's balance fonction *)
Definition balance {X} (tr: tree X) : tree X :=
	match tr with
	| Node Red a x b => Node Red a x b
	| Node Black (Node Red (Node Red a x b) y c) z d
	| Node Black (Node Red a x (Node Red b y c)) z d
	| Node Black a x (Node Red (Node Red b y c) z d)
	| Node Black a x (Node Red b y (Node Red c z d)) =>
		Node Red (Node Black a x b) y (Node Black c z d)
	| Node c a x b => Node c a x b
	| Leaf => Leaf
	end.


Fixpoint insert_util {X} {cmp} (x: X) tr :=
	match tr with
	| Leaf => Node Red Leaf x Leaf
	| Node c l v r =>
		match cmp x v with
		| Lt => balance (Node c (@insert_util X cmp x l) v r)
		| Gt => balance (Node c l v (@insert_util X cmp x r))
		| Eq => Node c l x r
		end
	end.

Definition insertion {X} {cmp} (x : X) (tr : tree X) : tree X :=
	make_black (
		@insert_util X cmp x tr
	).

#[local] Hint Unfold make_black : db.
#[local] Hint Unfold balance : db.
#[local] Hint Unfold insert_util : db.
#[local] Hint Unfold insertion : db.

(* start proving the RB properties *)

(* The first invariant we want to prove is that the inside insertion leave
a red-black tree except the root and is child can be read *)

(* For this we need anoter definition *)

Inductive RRBlack {X} : tree X -> nat -> Prop :=
	| rr_black_node : forall l r v n,
		RedBlack l n ->
		RedBlack r n ->
		RRBlack (Node Red l v r) n
	| rr_black_black_node : forall l r v n,
		RedBlack l n ->
		RedBlack r n ->
		RRBlack (Node Black l v r) (S n).

#[local] Hint Constructors RRBlack : db.

Lemma rr_rb : forall X (l r : tree X) (v : X) (n : nat),
	RRBlack (Node Black l v r) n ->
	RedBlack (Node Black l v r) n.
Proof.
	intros.
	inversion H; subst.
	auto with db.
Qed.

Lemma rrb_non_empty : forall X (n : nat),
	@RRBlack X Leaf n -> False.
Proof.
	intros.
	inversion H.
Qed.

Ltac prove_RB :=
	repeat
		match goal with
		| |- _ (match ?x with Eq => _ | Lt => _ | Gt => _ end) _ => destruct x
		| |- RRBlack _ _ => constructor
		| |- RedBlack _ _ => constructor
		| |- _ (match ?c with Red => _ | Black => _ end) _ => destruct c
		| |- _ (match ?t with Leaf => _ | Node _ _ _ _ => _ end) _ => destruct t
		| H: RRBlack Leaf _ |- _ => inv H
		| H: _ (Node _ _ _ _) _ |- _ => inv H
		| H: RedBlack Leaf _ |- _ => inv H
		| H: IsBlack (Node Red _ _ _) |- _ => inv H
		end;
	auto with db; try lia.

Theorem rr_black : forall (v : T) (t : tree T) (n : nat),
	RedBlack t n ->
		RRBlack (@insert_util T cmp v t) n
  		/\ (IsBlack t -> RedBlack (@insert_util T cmp v t) n).
Proof.
	induction t; intro n; split; try intro; inv H;
	try remember n0 as x; try remember n as x;
	repeat constructor; simpl;
	specialize (IHt1 x); specialize (IHt2 x);
	subst; intuition;
	prove_RB.
Qed.

Corollary ins_RB' : forall (t : tree T) (v : T) (n : nat),
	RedBlack t n ->
	IsBlack t ->
	RedBlack (@insert_util T cmp v t) n.
Proof.
	intros.
	apply rr_black; assumption.
Qed.

Lemma RB_blacken_root : forall (t : tree T) (n : nat),
	RedBlack t n ->
		RedBlack (make_black t) n \/ RedBlack (make_black t) (S n).
Proof.
	intros. inv H; unfold make_black;
	try (left; auto with db; assumption);
	try (right; auto with db).
Qed.

#[local] Hint Constructors BST : db.
#[local] Hint Unfold ForallT : db.
#[local] Hint Unfold make_black : db.

Lemma forall_cmp_trans_lt : forall (t : tree T) (x y : T),
	ForallT (fun v : T => cmp v x = Lt) t ->
	cmp x y  = Lt ->
	ForallT (fun v : T => cmp v y = Lt) t.
Proof.
	intros.
	induction t. simpl. tauto.
	inv H. destruct H2. intuition.
	constructor; auto.
	apply order_trans with x; assumption.
Qed.
Lemma forall_cmp_trans_gt : forall (t : tree T) (x y : T),
	ForallT (fun v : T => cmp v x = Gt) t ->
	cmp x y  = Gt ->
	ForallT (fun v : T => cmp v y = Gt) t.
Proof.
	intros.
	induction t. simpl. tauto.
	inv H. destruct H2. intuition.
	constructor; auto.
	apply order_trans_gt with x; assumption.
Qed.

Lemma forall_cmp_trans_eq : forall (t : tree T) (x y : T) (eq : comparison),
	ForallT (fun v : T => cmp v x = eq) t ->
	cmp x y  = Eq ->
	ForallT (fun v : T => cmp v y = eq) t.
Proof.
	intros.
	induction t. simpl. tauto.
	destruct eq;
	inv H; destruct H2; intuition;
	constructor; auto;
	apply Facts.compare_eq_iff in H0;
	rewrite <- H0; assumption.
Qed.


Ltac prove_BST :=
	repeat
		match goal with
		| H : ForallT _ Leaf |- _ => inv H
		| H : ForallT _ (Node _ _ _ _) |- _ => inv H
		| H : BST Leaf |- _ => inv H
		| H : BST (Node _ _ _ _) |- _ => inv H
		| H : cmp ?x ?y = Lt |- cmp ?y ?x = Gt => apply inv_order
		| H : cmp ?x ?y = Gt |- cmp ?y ?x = Lt => apply inv_order
		| H : _ /\ _ |- _ => destruct H
		| |- BST (match ?t with Leaf => _ | Node _ _ _ _ => _ end) => destruct t
		| |- BST (match ?c with Red => _ | Black => _ end) => destruct c
		| |- BST (Node _ _ _ _) => constructor
		| |- _ /\ _ => split
		| |- ForallT _ (match ?t with Leaf => _ | Node _ _ _ _ => _ end) => destruct t
		| |- ForallT _ (match ?c with Red => _ | Black => _ end) => destruct c
		| |- ForallT _ (Node _ _ _ _) => constructor
		| H: ForallT (fun _ : T => cmp _ ?x = Gt) ?t
			, GMP: cmp ?y ?x = Lt
			|- ForallT (fun _ : T => cmp _ ?y = Gt) ?t => apply (forall_cmp_trans_gt t x y)
		| H: cmp ?x ?y = Lt,
			GMP: cmp ?z ?y = Gt
			|- cmp ?x ?z = Lt => apply (order_trans x y z)
		| H: ForallT (fun _ : T => cmp _ ?x = Lt) ?t
			, GMP: cmp ?y ?x = Gt
			|- ForallT (fun _ : T => cmp _ ?y = Lt) ?t => apply (forall_cmp_trans_lt t x y)
		| H: cmp ?x ?y = Gt,
			GMP: cmp ?z ?y = Lt
			|- cmp ?x ?z = Gt => apply (order_trans_gt x y z)
		end;
	auto with db; try lia.

Theorem BST_balance : forall x (t : tree T),
	@BST T cmp t -> (@BST T cmp (balance t)
	/\ (
		(ForallT (fun y : T => cmp y x = Lt) t ->
		ForallT (fun y: T => cmp y x = Lt) (balance t))
	/\ (ForallT (fun y : T => cmp y x = Gt) t ->
		ForallT (fun y: T => cmp y x = Gt) (balance t))
		)).
Proof.
	intros.
	induction t. auto with db.
	repeat split; intros;
	simpl; prove_BST.
Qed.

Theorem BST_ins : forall (t : tree T) (v : T) (x : T),
	@BST T cmp t -> (@BST T cmp (@insert_util T cmp v t)
	/\ (cmp v x = Lt ->
		ForallT (fun y : T => cmp y x = Lt) t ->
		ForallT (fun y: T => cmp y x = Lt) (@insert_util T cmp v t)
		)
	/\ (
		cmp v x = Gt ->
		ForallT (fun y : T => cmp y x = Gt) t ->
		ForallT (fun y: T => cmp y x = Gt) (@insert_util T cmp v t)
		)
	).

Proof.
	intros.
	generalize dependent x.
	induction t.
	intro.
	simpl. repeat split; auto with db.
	split.
	- unfold insert_util. fold (@insert_util T).
		destruct (cmp v v0) eqn:cmpv.
		+ inv H. constructor; auto with db;
			apply forall_cmp_trans_eq with v0; auto with db;
			apply Facts.compare_eq_iff in cmpv;
			rewrite <- cmpv; unfold cmp; apply Facts.compare_refl.
		+ inv H. intuition.
			set (insert_util v t1) in *.
			specialize (H v0). intuition.
			apply (BST_balance v). constructor; auto with db.
		+ inv H. intuition.
			set (insert_util v t2) in *.
			specialize (H0 v0). intuition.
			apply (BST_balance v). constructor; auto with db.
	- split; intros; unfold insert_util; fold (@insert_util T);
		destruct (cmp v v0) eqn:cmpv.
		+ prove_BST.
		+ inv H. intuition.
			set (insert_util v t1) in *.
			assert (@BST T cmp (Node c t v0 t2)) as Hbst.
			{ specialize (H v0).  prove_BST. }
			specialize (H x).
			intuition.
			pose proof (BST_balance x (Node c t v0 t2)).
			intuition.
			apply H10.
			prove_BST.
		+ inv H. intuition.
			set (insert_util v t2) in *.
			assert (@BST T cmp (Node c t1 v0 t)) as Hbst.
			{ specialize (H2 v0).  prove_BST. }
			specialize (H2 x).
			intuition.
			pose proof (BST_balance x (Node c t1 v0 t)).
			intuition.
			apply H10.
			prove_BST.
		+ prove_BST.
		+ inv H. intuition.
			set (insert_util v t1) in *.
			assert (@BST T cmp (Node c t v0 t2)) as Hbst.
			{ specialize (H v0).  prove_BST. }
			specialize (H x).
			intuition.
			pose proof (BST_balance x (Node c t v0 t2)).
			intuition.
			apply H12.
			prove_BST.
		+ inv H. intuition.
			set (insert_util v t2) in *.
			assert (@BST T cmp (Node c t1 v0 t)) as Hbst.
			{ specialize (H2 v0).  prove_BST. }
			specialize (H2 x).
			intuition.
			pose proof (BST_balance x (Node c t1 v0 t)).
			intuition.
			apply H12.
			prove_BST.
Qed.

Lemma BST_make_black : forall (t : tree T),
	@BST T cmp t -> @BST T cmp (make_black t).
Proof.
	intros.
	induction H.
	- simpl. auto with db.
	- unfold make_black. constructor; auto with db.
Qed.

Theorem BST_insertion : forall (t : tree T) (v : T),
	@BST T cmp t -> @BST T cmp (@insertion T cmp v t).
Proof.
	intros.
	unfold insertion.
	apply BST_make_black.
	apply BST_ins; auto.
Qed.

Definition RedBlacktree {X} {cmp} (t : tree X) : Prop :=
	@BST X cmp t /\
	(exists n, RedBlack t n) /\ IsBlack t.

#[local] Hint Unfold RedBlacktree : db.
#[local] Hint Immediate rr_black : db.
#[local] Hint Immediate ins_RB' : db.
#[local] Hint Immediate RB_blacken_root : db.

Lemma make_black_is_black : forall (t : tree T),
	IsBlack (make_black t).
Proof.
	intros.
	destruct t;
	unfold make_black;
	auto with db.
Qed.

Theorem RB_inv: forall (t : tree T) (v : T),
	@RedBlacktree T cmp t -> @RedBlacktree T cmp (@insertion T cmp v t) .
Proof.
	intros.
	destruct H. destruct H0.
	unfold RedBlacktree.
	repeat split.
	- apply BST_insertion. assumption.
	-	unfold insertion.
		inversion H0.
		apply (ins_RB' t v) in H2.
		apply RB_blacken_root in H2.
		destruct H2.
		+ exists x. assumption.
		+ exists (S x). assumption.
		+ assumption.
	- unfold insertion.
		apply make_black_is_black.
Qed.


(* Deletion algorithm *)
Fixpoint max {X} v (t : tree X) : X :=
	match t with
	| Leaf => v (* only if tree is empty*)
	| Node _ _ x r => max x r
	end.

Definition redden {X} (t : tree X) : tree X :=
	match t with
	| Leaf => Leaf (* impossible *)
	| Node _ a x b => Node Red a x b
	end.

(* Balancing function *)

Definition balance_left {X} (c : colour) (lS : tree X * bool) (v : X) (r : tree X) : (tree X * bool) :=
	match lS with (l, isShorter) =>
		if isShorter then
			match c, l, v, r with
			| Black, a, x,  Node Red (Node Black b y c) z d
			=> (Node Black (Node Black a x b) y (balance (Node Black c z (redden d))),false)
			| k, a, x, Node Black (Node Red b y c) z d
			| k, a, x, Node Black b y (Node Red c z d)
			=> (Node k (Node Black a x b) y (Node Black c z d), false)
			| Black, x, y, Node Black c z d
			=> (Node Black x y (Node Red c z d), true)
			| Red, x, y, Node Black c z d
			=> (Node Black x y (Node Red c z d), false)
			| _, _, _, _ => (Node c l v r, false)
			end
		else
			(Node c l v r, false)
		end.

Definition balance_right {X} (c : colour) (l : tree X) (v : X) (rS : tree X * bool) : (tree X * bool) :=
	match rS with (r, isShorter) =>
		if isShorter then
			match c, l, v, r with
			| Black, Node Red a x (Node Black b y c), z, d
			=> (Node Black (balance (Node Black (redden a) x b)) y (Node Black c z d), false)
			| k, Node Black (Node Red a x b) y c, z, d
			| k, Node Black a x (Node Red b y c), z, d
			=> (Node k (Node Black a x b) y (Node Black c z d), false)
			| Black, Node Black a x b, y, z
			=> (Node Black (Node Red a x b) y z, true)
			| Red, Node Black a x b, y, z
			=> (Node Black (Node Red a x b) y z, false)
			| _, _, _, _ => (Node c l v r, false)
			end
		else
			(Node c l v r, false)
		end.

Fixpoint remove_rightmost {X} (t: tree X) : (tree X * bool) :=
	match t with
	| Leaf => (Leaf, false)
	| Node Red l _ Leaf => (l, false)
	| Node Black l _ Leaf => (make_black l, isBlack l)
	| Node c l v r =>
		balance_right c l v (remove_rightmost r)
	end.

Definition remove {X} (t : tree X) : (tree X * bool) :=
	match t with
	| Leaf => (Leaf, false) (* impossible *)
	| Node Red Leaf _ Leaf => (Leaf, false)
	| Node Black Leaf _ Leaf => (Leaf, true)

	| Node Black (Node Red Leaf v Leaf) _ Leaf
	| Node Black Leaf _ (Node Red Leaf v Leaf)
	=> (Node Black Leaf v Leaf, false)

	| Node c l v r =>
		let v := max v l in
		let l := remove_rightmost l in
		balance_left c l v r
	end.

Fixpoint del (t : tree T) (v : T) : (tree T * bool) :=
	match t with
	| Leaf => (Leaf, false) (* nothing to delete *)
	| Node c l x r =>
		match cmp v x with
		| Lt => let l := del l v in balance_left c l x r
		| Gt => let r := del r v in balance_right c l x r
		| Eq => remove t
		end
	end.

Definition delete t v := match (del t v) with (t, _) => t end.

#[local] Hint Unfold delete : db.
#[local] Hint Unfold del : db.
#[local] Hint Unfold remove : db.
#[local] Hint Unfold remove_rightmost : db.
#[local] Hint Unfold balance_left : db.
#[local] Hint Unfold balance_right : db.
#[local] Hint Unfold max : db.

(* Proving that the deletion preserve BST *)

Lemma BST_redden : forall x (t : tree T),
	@BST T cmp t -> (@BST T cmp (redden t)
	/\ (
		(ForallT (fun y : T => cmp y x = Lt) t ->
		ForallT (fun y: T => cmp y x = Lt) (redden t))
	/\ (ForallT (fun y : T => cmp y x = Gt) t ->
		ForallT (fun y: T => cmp y x = Gt) (redden t))
		)).
Proof.
	intros.
	induction t. auto with db.
	repeat split; intros;
	simpl; prove_BST.
Qed.

Lemma max_gt : forall x y c l v r,
	ForallT (fun y : T => cmp y x = Lt) (Node c l v r) ->
	cmp x (max y (Node c l v r)) = Gt.
Proof.
	intros x y c l v r.
	generalize dependent v.
	generalize dependent l.
	generalize dependent c.
	generalize dependent y.
	generalize dependent x.
	induction r.
	- intros. inv H. apply inv_order in H0. auto with db.
	- intros.
		specialize (IHr2 x v c r1 v).
		simpl in *. intuition.
Qed.


Lemma lmax : forall x y c l v r,
	@BST T cmp (Node c l v r) ->
	cmp x v = Lt ->
	cmp x (max y (Node c l v r)) = Lt .
Proof.
	intros.
	generalize dependent v.
	generalize dependent l.
	generalize dependent c.
	generalize dependent y.
	generalize dependent x.
	induction r.
	- auto with db.
	- intros. simpl.
		inv H. inv H6.
		specialize (IHr2 x y c r1 v). intuition.
		apply inv_order in H. apply (order_trans x v0 v) in H0;
		destruct r2; auto with db.
Qed.

Lemma BST_max_gt : forall x t,
		cmp x (max x t) = Gt ->
		ForallT (fun y : T => cmp y x = Gt) t ->
		ForallT (fun y: T => cmp y (max x t) = Gt) t.
Proof.
	intros.
	apply forall_cmp_trans_gt with x; auto with db.
Qed.

Lemma BST_max_lt : forall x t,
		cmp x (max x t) = Lt ->
		ForallT (fun y : T => cmp y x = Lt) t ->
		ForallT (fun y: T => cmp y (max x t) = Lt) t.
Proof.
	intros.
	apply forall_cmp_trans_lt with x; auto with db.
Qed.


Ltac prove_BST_del :=
	repeat
		match goal with
		| H : ForallT _ Leaf |- _ => inv H
		| H : ForallT _ (Node _ _ _ _) |- _ => inv H
		| H : BST Leaf |- _ => inv H
		| H : BST (Node _ _ _ _) |- _ => inv H
		| H : cmp ?x ?y = Lt |- cmp ?y ?x = Gt => apply inv_order
		| H : cmp ?x ?y = Gt |- cmp ?y ?x = Lt => apply inv_order
		| H : _ /\ _ |- _ => destruct H
		| |- BST (fst (match ?t with Leaf => _ | Node _ _ _ _ => _ end)) => destruct t
		| |- BST (fst (match ?c with Red => _ | Black => _ end)) => destruct c
		| |- BST (fst (if ?b then _ else _ )) => destruct b
		| |- BST (fst (_, _)) => unfold fst
		| |- BST (balance _) => apply BST_balance
		| |- BST (redden _) => apply BST_redden
		| |- BST (Node _ _ _ _) => constructor
		| |- ForallT _ (fst (match ?t with Leaf => _ | Node _ _ _ _ => _ end)) => destruct t
		| |- ForallT _ (fst (match ?c with Red => _ | Black => _ end)) => destruct c
		| |- ForallT _ (fst (if ?b then _ else _ )) => destruct b
		| |- ForallT _ (fst (_, _)) => unfold fst
		| |- ForallT _ (balance _) => apply BST_balance
		| |- ForallT _ (redden _) => apply BST_redden
		| |- ForallT _ (Node _ _ _ _) => constructor
		| |- _ /\ _ => split
		| H: ForallT (fun _ : T => cmp _ ?x = Gt) ?t
			, GMP: cmp ?y ?x = Lt
			|- ForallT (fun _ : T => cmp _ ?y = Gt) ?t => apply (forall_cmp_trans_gt t x y)
		| H: cmp ?x ?y = Lt,
			GMP: cmp ?z ?y = Gt
			|- cmp ?x ?z = Lt => apply (order_trans x y z)
		| H: ForallT (fun _ : T => cmp _ ?x = Lt) ?t
			, GMP: cmp ?y ?x = Gt
			|- ForallT (fun _ : T => cmp _ ?y = Lt) ?t => apply (forall_cmp_trans_lt t x y)
		| H: cmp ?x ?y = Gt,
			GMP: cmp ?z ?y = Lt
			|- cmp ?x ?z = Gt => apply (order_trans_gt x y z)
		end;
	auto with db; try lia.

Theorem BST_bal_right : forall x c l v (rb : tree T * bool),
	@BST T cmp (Node c l v (fst rb)) -> (@BST T cmp (fst (balance_right c l v rb))
	/\ (
		(ForallT (fun y : T => cmp y x = Lt) (Node c l v (fst rb)) ->
		ForallT (fun y: T => cmp y x = Lt) (fst(balance_right c l v rb)))
	/\ (ForallT (fun y : T => cmp y x = Gt) (Node c l v (fst rb)) ->
		ForallT (fun y: T => cmp y x = Gt) (fst(balance_right c l v rb)))
		)).
Proof.
	intros. destruct rb.
	repeat split; intros;
	unfold balance_right; prove_BST_del.
Qed.

Theorem BST_bal_left : forall x c (lb : tree T * bool) v r,
	@BST T cmp (Node c (fst lb) v r) -> (@BST T cmp (fst (balance_left c lb v r))
	/\ (
		(ForallT (fun y : T => cmp y x = Lt) (Node c (fst lb) v r) ->
		ForallT (fun y: T => cmp y x = Lt) (fst (balance_left c lb v r)))
	/\ (ForallT (fun y : T => cmp y x = Gt) (Node c (fst lb) v r) ->
		ForallT (fun y: T => cmp y x = Gt) (fst (balance_left c lb v r)))
		)).
Proof.
	intros. destruct lb.
	repeat split; intros;
	unfold balance_left; prove_BST_del.
Qed.

Theorem BST_make_black_2 : forall x t,
	@BST T cmp t -> (@BST T cmp (make_black t)
	/\
		(ForallT (fun y : T => cmp y x = Lt) t ->
		ForallT (fun y: T => cmp y x = Lt) (make_black t)
		)
	/\ (
		ForallT (fun y : T => cmp y x = Gt) t ->
		ForallT (fun y: T => cmp y x = Gt) (make_black t)
		)).
Proof.
	intros.
	induction H.
	- simpl. auto with db.
	- unfold make_black. constructor; auto with db.
Qed.


Theorem BST_remove_rightmost : forall x (t : tree T) ,
	@BST T cmp t -> (@BST T cmp (fst (remove_rightmost t))
	/\ (
		ForallT (fun y : T => cmp y x = Lt) t ->
		ForallT (fun y: T => cmp y x = Lt) (fst (remove_rightmost t))
		)
	/\ (
		ForallT (fun y : T => cmp y x = Gt) t ->
		ForallT (fun y: T => cmp y x = Gt) (fst (remove_rightmost t))
		)
	).
Proof.
	intros x t.
	generalize dependent x.
	induction t.
	-  simpl. auto with db.
	- repeat split; intros.
		+ simpl. destruct t2.
			* destruct c; simpl; inv H;
				try apply BST_make_black_2; assumption.
			* inv H. specialize (IHt2 v). intuition.
				assert (@BST T cmp( Node c t1 v (fst (remove_rightmost (Node c0 t2_1 v0 t2_2))))).
				{ constructor; auto with db. }
				apply (BST_bal_right x c t1 v (remove_rightmost (Node c0 t2_1 v0 t2_2))) in H2.
				destruct H2. destruct c; assumption.
		+ simpl. destruct t2.
			* destruct c; simpl; inv H; inv H0;
				try apply BST_make_black_2; intuition.
			*	inv H.
				inv H0. intuition.
				assert (@BST T cmp( Node c t1 v (fst (remove_rightmost (Node c0 t2_1 v0 t2_2))))).
				{
					specialize (IHt2 v).
					apply IHt2 in H8.
					inv H8. inv H3.
					constructor; auto with db.
				}
				specialize (IHt2 x). intuition.
				apply (BST_bal_right x c t1 v (remove_rightmost (Node c0 t2_1 v0 t2_2))) in H1.
				inv H1. inv H11.
				destruct c; apply H1; constructor; auto with db.
		+ simpl. destruct t2.
			*	destruct c; simpl; inv H; inv H0;
				try apply BST_make_black_2; intuition.
			*	inv H.
				inv H0. intuition.
				assert (@BST T cmp( Node c t1 v (fst (remove_rightmost (Node c0 t2_1 v0 t2_2))))).
				{
					specialize (IHt2 v).
					apply IHt2 in H8.
					inv H8. inv H3.
					constructor; auto with db.
				}
				specialize (IHt2 x). intuition.
				apply (BST_bal_right x c t1 v (remove_rightmost (Node c0 t2_1 v0 t2_2))) in H1.
				inv H1. inv H11.
				destruct c; apply H12; constructor; auto with db.
Qed.

Lemma forall_inv : forall (x : T) (t : tree T),
	ForallT (fun y : T => cmp x y = Lt) t <->
	ForallT (fun y : T => cmp y x = Gt) t.
Proof.
	intros.
	induction t.
	- intros. simpl. tauto.
	- intros. split.
		+ intros. inv H. inv H1.
			apply IHt1 in H. apply IHt2 in H2.
			apply inv_order in H0.
			constructor; auto with db.
		+ intros. inv H. inv H1.
			apply IHt1 in H. apply IHt2 in H2.
			apply inv_order in H0.
			constructor; auto with db.
Qed.

Inductive NonEmpty {X} : tree X -> Prop :=
	| non_empty_node : forall c l v r, NonEmpty (Node c l v r).

Ltac prove_max_bal :=
	repeat
		match goal with
		| |- _ = max _ (fst (match ?t with Leaf => _ | Node _ _ _ _ => _ end)) => destruct t
		| |- _ = max _ (fst (match ?c with Red => _ | Black => _ end)) => destruct c
		| |- _ = max _ (fst (if ?b then _ else _ )) => destruct b
		| |- _ = max _ (fst (_, _)) => unfold fst
		end;
	auto with db; try lia.

Lemma BST_max_bal_right : forall x c l v (rb : tree T * bool),
	(max v (fst rb)) = (max x (fst (balance_right c l v rb))).
Proof.
	intros.
	generalize dependent v.
	generalize dependent l.
	generalize dependent c.
	generalize dependent x.
	destruct rb as (r,b).
	induction r.
	- intros. simpl. prove_max_bal.
	- intros. specialize (IHr2 x c r1 v). simpl in IHr2.
		simpl. rewrite IHr2. prove_max_bal.
Qed.

Lemma BST_max_remove_rightmost : forall x c l v r,
	@BST T cmp (Node c l v r) ->
	ForallT (fun y : T => cmp x y = Lt) (Node c l v r) ->
	cmp (max x (fst (remove_rightmost (Node c l v r))))
	(max x (Node c l v r)) = Lt.
Proof.
	intros x c l v r.
	generalize dependent v.
	generalize dependent l.
	generalize dependent c.
	generalize dependent x.
	induction r.
	- intros. generalize dependent x.
		induction l; intros.
		+ destruct c; simpl; inv H0; assumption.
		+
		 assert (@BST T cmp (Node c l2 v Leaf)).
			{ prove_BST. }
			apply IHl2 with v0 in H1.
			* simpl. simpl in H1.
				destruct c,c0; auto with db;
				simpl in *; destruct l2; auto with db.
			* inv H. inv H6. inv H8.
			 constructor; auto with db.
			 split; auto with db.
			 apply forall_inv. assumption.
	- intros.
		specialize (IHr2 v0 c r1 v).
			inv H. apply forall_inv in H6. intuition .
			simpl in H1. simpl.
			rewrite (BST_max_bal_right x c0 l) in H1.
			destruct c0; assumption.
Qed.

Lemma forall_max : forall (x : T) (t : tree T),
	@BST T cmp t ->
	ForallT (fun y : T => cmp y (max x t) = Lt) (fst (remove_rightmost t)).
Proof.
	intros. generalize dependent x.
	induction t. intro. simpl. tauto.
	inv H. intuition.
	simpl.
	destruct c, t2.
	- auto with db.
	- apply BST_bal_right.
		* constructor; auto with db;
			 apply (BST_remove_rightmost v) in H7;
			 prove_BST_del.
		*	specialize (H0 v).
			constructor; auto with db.
			apply lmax. assumption.
			inv H5. apply inv_order. assumption.
			split. apply forall_cmp_trans_lt with v.
			assumption. apply lmax. assumption.
			inv H5. apply inv_order. assumption.
			assumption.
	- simpl. apply (BST_make_black_2 v) in H6. intuition.
	- apply BST_bal_right.
		* constructor; auto with db;
			 apply (BST_remove_rightmost v) in H7;
			 prove_BST_del.
		*	specialize (H0 v).
			constructor; auto with db.
			apply lmax. assumption.
			inv H5. apply inv_order. assumption.
			split. apply forall_cmp_trans_lt with v.
			assumption. apply lmax. assumption.
			inv H5. apply inv_order. assumption.
			assumption.
Qed.

Theorem BST_remove : forall x (t : tree T),
	@BST T cmp t -> (@BST T cmp (fst (remove t))
	/\ (
		ForallT (fun y : T => cmp y x = Lt) t ->
		ForallT (fun y: T => cmp y x = Lt) (fst (remove t))
		)
	/\ (
		ForallT (fun y : T => cmp y x = Gt) t ->
		ForallT (fun y: T => cmp y x = Gt) (fst (remove t))
		)
	).
Proof.
	intros. generalize dependent x.
	induction t.
	intros. simpl. auto with db.
	intros. repeat split; intros.
	- unfold remove.
		inversion H; subst. intuition.
		apply (BST_remove_rightmost v t1) in H6. intuition.
		set (max v t1) as a.
		simpl. prove_BST_del.
		+ simpl. auto with db.
		+ apply (BST_bal_left v).
			constructor; auto with db.
			apply forall_max.
			constructor; auto with db.
			apply forall_cmp_trans_gt with v.
			assumption. unfold a. apply max_gt.
			constructor; auto with db.
		+ apply (BST_bal_left v).
			prove_BST_del.
		+ apply (BST_bal_left v).
			prove_BST_del.
		+ apply (BST_bal_left v).
			prove_BST_del.
		+ apply (BST_bal_left v).
			prove_BST_del.
		+ apply (BST_bal_left v).
			constructor; auto with db.
			apply forall_max.
			constructor; auto with db.
			apply forall_cmp_trans_gt with v.
			assumption. unfold a. apply max_gt.
			constructor; auto with db.
		+ apply (BST_bal_left v).
			constructor; auto with db.
			apply forall_max.
			constructor; auto with db.
			apply forall_cmp_trans_gt with v.
			assumption. unfold a. apply max_gt.
			constructor; auto with db.
		+ apply (BST_bal_left v).
			constructor; auto with db.
			apply forall_max.
			constructor; auto with db.
			apply forall_cmp_trans_gt with v.
			assumption. unfold a. apply max_gt.
			constructor; auto with db.
	-	inversion H; subst. intuition.
		simpl.
		apply (BST_remove_rightmost v t1) in H7. intuition.
		set (max v t1) as a.
		simpl. prove_BST_del.
		+ simpl. auto with db.
		+ apply (BST_bal_left x).
			constructor; auto with db.
			apply forall_max.
			constructor; auto with db.
			apply forall_cmp_trans_gt with v.
			assumption. unfold a. apply max_gt.
			constructor; auto with db.
			prove_BST_del.
			apply inv_order. apply max_gt.
			constructor; auto with db.
			apply forall_cmp_trans_lt with v; assumption.
		+ apply (BST_bal_left x);
			prove_BST_del.
		+ apply (BST_bal_left x);
			prove_BST_del.
		+ apply (BST_bal_left x);
			prove_BST_del.
		+ apply (BST_bal_left x);
			constructor; auto with db.
			apply forall_cmp_trans_gt with v.
			constructor; auto with db.
			unfold a. apply max_gt.
			constructor; auto with db.
		+ apply (BST_bal_left x).
			constructor; auto with db.
			apply forall_max.
			constructor; auto with db.
			apply forall_cmp_trans_gt with v.
			assumption. unfold a. apply max_gt.
			constructor; auto with db.
			prove_BST_del.
			apply inv_order. apply max_gt.
			constructor; auto with db.
			apply forall_cmp_trans_lt with v; assumption.
		+ apply (BST_bal_left x).
			constructor; auto with db.
			apply forall_max.
			constructor; auto with db.
			apply forall_cmp_trans_gt with v.
			assumption. unfold a. apply max_gt.
			constructor; auto with db.
			prove_BST_del.
			apply inv_order. apply max_gt.
			constructor; auto with db.
			apply forall_cmp_trans_lt with v; assumption.
		+ apply (BST_bal_left x).
			constructor; auto with db.
			apply forall_max.
			constructor; auto with db.
			apply forall_cmp_trans_gt with v.
			assumption. unfold a. apply max_gt.
			constructor; auto with db.
			prove_BST_del.
			apply inv_order. apply max_gt.
			constructor; auto with db.
			apply forall_cmp_trans_lt with v; assumption.
	-	inversion H; subst. intuition.
		simpl.
		apply (BST_remove_rightmost v t1) in H7. intuition.
		set (max v t1) as a.
		simpl. prove_BST_del.
		+ simpl. auto with db.
		+ apply (BST_bal_left x).
			constructor; auto with db.
			apply forall_max.
			constructor; auto with db.
			apply forall_cmp_trans_gt with v.
			assumption. unfold a. apply max_gt.
			constructor; auto with db.
			prove_BST_del.
			apply inv_order. apply lmax.
			constructor; auto with db.
			apply inv_order. assumption.
			apply BST_remove_rightmost;
			prove_BST_del.
		+ apply (BST_bal_left x);
			prove_BST_del.
		+ apply (BST_bal_left x);
			prove_BST_del.
		+ apply (BST_bal_left x);
			prove_BST_del.
		+ apply (BST_bal_left x);
			constructor; auto with db.
			apply forall_cmp_trans_gt with v.
			constructor; auto with db.
			unfold a. apply max_gt.
			constructor; auto with db.
		+ apply (BST_bal_left x).
			constructor; auto with db.
			apply forall_max.
			constructor; auto with db.
			apply forall_cmp_trans_gt with v.
			assumption. unfold a. apply max_gt.
			constructor; auto with db.
			prove_BST_del.
			apply inv_order. apply lmax.
			constructor; auto with db.
			apply inv_order. assumption.
			apply BST_remove_rightmost;
			prove_BST_del.
		+ apply (BST_bal_left x).
			constructor; auto with db.
			apply forall_max.
			constructor; auto with db.
			apply forall_cmp_trans_gt with v.
			assumption. unfold a. apply max_gt.
			constructor; auto with db.
			prove_BST_del.
			apply inv_order. apply lmax.
			constructor; auto with db.
			apply inv_order. assumption.
			apply BST_remove_rightmost;
			prove_BST_del.
		+ apply (BST_bal_left x).
			constructor; auto with db.
			apply forall_max.
			constructor; auto with db.
			apply forall_cmp_trans_gt with v.
			assumption. unfold a. apply max_gt.
			constructor; auto with db.
			prove_BST_del.
			apply inv_order. apply lmax.
			constructor; auto with db.
			apply inv_order. assumption.
			apply BST_remove_rightmost;
			prove_BST_del.
Qed.


Theorem BST_del : forall u (x : T) (t : tree T),
	@BST T cmp t -> (@BST T cmp (fst (del t x))
	/\ (
		ForallT (fun y : T => cmp y u = Lt) t ->
		ForallT (fun y: T => cmp y u = Lt) (fst (del t x))
		)
	/\ (
		ForallT (fun y : T => cmp y u = Gt) t ->
		ForallT (fun y: T => cmp y u = Gt) (fst (del t x))
		)
	).
Proof.
	intros.
	generalize dependent u.
	generalize dependent x.
	induction t. simpl. auto with db.
	intros.
	unfold del. fold del. destruct (cmp x v).
	- apply (BST_remove u) in H. intuition.
	- repeat split; intros.
		+ prove_BST_del. intuition.
			specialize (H x v). intuition.
			apply (BST_bal_left u c (del t1 x) v t2); prove_BST_del.
		+ prove_BST_del. intuition.
			apply (BST_bal_left u c (del t1 x) v t2); prove_BST_del.
			* specialize (H2 x v). intuition.
			* specialize (H2 x v). intuition.
			* specialize (H2 x u). intuition.
		+ prove_BST_del. intuition.
			apply (BST_bal_left u c (del t1 x) v t2); prove_BST_del.
			* specialize (H2 x v). intuition.
			* specialize (H2 x v). intuition.
			* specialize (H2 x u). intuition.
	- repeat split; intros.
		+ prove_BST_del. intuition.
			specialize (H0 x v). intuition.
			apply (BST_bal_right u c t1 v (del t2 x)); prove_BST_del.
		+ prove_BST_del. intuition.
			apply (BST_bal_right u c t1 v (del t2 x)); prove_BST_del.
			* specialize (H3 x v). intuition.
			* specialize (H3 x v). intuition.
			* specialize (H3 x u). intuition.
		+ prove_BST_del. intuition.
			apply (BST_bal_right u c t1 v (del t2 x)); prove_BST_del.
			* specialize (H3 x v). intuition.
			* specialize (H3 x v). intuition.
			* specialize (H3 x u). intuition.
Qed.

Theorem BST_delete : forall (x : T) (t : tree T),
	@BST T cmp t -> @BST T cmp (delete t x).
Proof.
	intros.
	unfold delete.
	apply BST_del; assumption.
Qed.


(* Proving that RedBlack property are preserved *)
Lemma bal_right_black_false : forall l v r n,
	RedBlack l n ->
	RedBlack r n ->
	let (t, b) := (balance_right Black l v (r,false)) in
	RedBlack t (S n) /\ b = false /\ @IsBlack T t.
Proof.
	intros. simpl. split;
	auto with db.
Qed.

Ltac prove_RB_bal_right :=
	repeat
		match goal with
		| H: RedBlack Leaf _ |- _ => inv H
		| H: RedBlack (Node _ _ _ _) _ |- _ => inv H
		| H: IsBlack (Node ?c _ _ _) |- _ => inv H
		| |- let (_,_) := match ?t with Leaf => _ | Node _ _ _ _ => _ end in _ => destruct t
		| |- let (_,_) := match ?c with Red => _ | Black => _ end in _ => destruct c
		| |- RedBlack _ _ => constructor
		| |- _ /\ _ => split
		| |- RedBlack (match redden ?t with Leaf => _ | Node _ _ _ _ => _ end) _ => destruct t; simpl
		| |- RedBlack (match ?t with Leaf => _ | Node _ _ _ _ => _ end) _ => destruct t
		| |- RedBlack (match ?c with Red => _ | Black => _ end) _ => destruct c
		end;
	auto with db; try lia.

Lemma bal_right_black_true : forall l v r n,
	RedBlack l (S n) ->
	RedBlack r n ->
	let (t, b) := (balance_right Black l v (r,true)) in
	match l with
	| Node Black (Node Black _ _ _ | Leaf) _ (Node Black _ _ _ | Leaf)
		=> RedBlack t (S n) /\ b = true
	| _ => RedBlack t (S (S n)) /\ b = false
	end /\ @IsBlack T t.
Proof.
	intros. simpl.
	prove_RB_bal_right.
Qed.

Corollary bal_right_black : forall l x r (b: bool) n,
	(if b then RedBlack r n else RedBlack r (S n))
	-> RedBlack l (S n)
	-> let (t, short) := balance_right Black l x (r,b) in
	(if short then RedBlack t (S n) else RedBlack t (S (S n))
	)/\ @IsBlack T t.
Proof.
	intros.
	destruct b.
	-	pose proof bal_right_black_true as P.
		specialize (P l x r n).
		intuition.
		destruct (balance_right Black l x (r, true)).
		inv H2. split. 2: assumption.
		destruct l. inv H1; assumption.
		destruct c. inv H1; assumption.
		destruct l1,l2. inv H1; assumption.
		destruct c. inv H1; assumption.
		inv H1; assumption.
		destruct c. inv H1; assumption.
		inv H1; assumption.
		destruct c. inv H1; assumption.
		destruct c0. inv H1; assumption.
		inv H1; assumption.
	-	pose proof bal_right_black_false as P.
		specialize (P l x r (S n)). intuition.
		destruct (balance_right Black l x (r, false)).
		inv H2. inv H3. split; assumption.
Qed.

Lemma bal_right_red_false : forall l v r n,
	RedBlack l n ->
	IsBlack l ->
	RedBlack r n ->
	IsBlack r ->
	let (t, b) := (balance_right Red l v (r,false)) in
	@RedBlack T t n /\ b = false.
Proof.
	intros. simpl.
	prove_RB_bal_right.
Qed.


Lemma bal_right_red_true : forall l v r n,
	RedBlack l (S n) ->
	IsBlack l ->
	RedBlack r n ->
	let (t, b) := (balance_right Red l v (r,true)) in
	@RedBlack T t (S n) /\ b = false.
Proof.
	intros. simpl.
	prove_RB_bal_right.
Qed.

Corollary bal_right_red : forall l x r (b: bool) n,
	(if b then RedBlack r n else RedBlack r (S n))
	-> RedBlack l (S n)
	-> IsBlack l
	-> IsBlack r
	-> let (t, short) := balance_right Red l x (r,b) in
	(if short then RedBlack t n else @RedBlack T t (S n)
	).
Proof.
	intros.
	destruct b.
	- pose proof bal_right_red_true as P.
		specialize (P l x r n).
		intuition.
		destruct (balance_right Red l x (r, true)).
		inv H3. assumption.
	- pose proof bal_right_red_false as P.
		specialize (P l x r (S n)).
		intuition.
		destruct (balance_right Red l x (r, false)).
		inv H4. assumption.
Qed.


Ltac prove_RB_rrm :=
	repeat
	 	match goal with
		| |- RedBlack _ _ => constructor
		| |- _ /\ _ => split
		| |- RedBlack (make_black _) _ => apply make_black_is_black
		| |- _ (match ?x with Eq => _ | Lt => _ | Gt => _ end) _ => destruct x
		| |- _ (match ?c with Red => _ | Black => _ end) _ => destruct c
		| |- _ (match ?t with Leaf => _ | Node _ _ _ _ => _ end) _ => destruct t
		| H: RedBlack (Node _ _ _ _) _ |- _ => inv H
		| H: RedBlack Leaf _ |- _ => inv H
		| H: IsBlack (Node Red _ _ _) |- _ => inv H
		end;
	auto with db; try lia.

Lemma RB_rrm : forall  c (l : tree T) v r (n : nat),
	RedBlack (Node c l v r) (S n) ->
		let (t, short) := remove_rightmost (Node c l v r) in
		(if short then RedBlack t n else RedBlack t (S n))
		/\ (c = Black -> IsBlack t).
Proof.
	intros.
	generalize dependent n.
	generalize dependent v.
	generalize dependent l.
	generalize dependent c.
	induction r as [| c r1 _ vr r2 IH2 ]; intros.
	- simpl. inv H.
		+ split; auto with db.
		+ inv H2; simpl; auto with db.
	- inv H; subst;
		destruct r2.
		+ simpl. inv H6. inv H9. inv H9.
			inv H1; inv H8; inv H4; prove_RB;
			inv H0; inv H2; simpl; split; auto with db;
			intro HF; inv HF.
		+ simpl. inv H8.
			specialize (IH2 Black r1 vr n). intuition.
			simpl in H.
			destruct (balance_right Black r1 vr
			match c0 with
			| Red =>
				 match r2_2 with
				 | Leaf => (r2_1, false)
				 | Node _ _ _ _ => balance_right c0 r2_1 v0 (remove_rightmost r2_2)
				 end
			| Black =>
				 match r2_2 with
				 | Leaf => (make_black r2_1, isBlack r2_1)
				 | Node _ _ _ _ => balance_right c0 r2_1 v0 (remove_rightmost r2_2)
				 end
			end).
			destruct b.
			* pose proof bal_right_red_true as P.
				specialize (P l v t n).
				intuition.
				destruct (balance_right Red l v (t, true)).
				split.
				inv H0; inv H; auto with db.
				intro HF. inv HF.
			* inv H.
				pose proof bal_right_red_false as P.
				specialize (P l v t (S n)).
				intuition.
				destruct (balance_right Red l v (t, false)).
				split.
				inv H1. auto with db.
				intro HF. inv HF.
		+ simpl. inv H6. inv H7. inv H2; inv H4;
			simpl; split; auto with db.
			inv H7; inv H5; unfold make_black; unfold isBlack.
			*	pose proof bal_right_black_true as P.
				specialize (P l v Leaf 0). intuition.
				assert (@RedBlack T Leaf 0) as Ha.
				{ constructor; auto with db. } intuition. clear Ha.
				destruct (balance_right Black l v (Leaf, true));
				inv H2; inv H0.
				inv H2. split; auto with db.
				inv H1; inv H4; inv H; try split; auto with db.
			* pose proof bal_right_black_false as P.
				specialize (P l v (Node Black l0 v0 r) 1). intuition.
				assert (@RedBlack T (Node Black l0 v0 r) 1) as Ha.
				{ constructor; auto with db. } intuition. clear Ha.
				destruct (balance_right Black l v (Node Black l0 v0 r, false)).
				inv H5. inv H6. split; auto with db.
		+ destruct n. inv H6. inv H7. inv H9.
			specialize (IH2 c r1 vr n). intuition.
			simpl in H. simpl.
			destruct ( match c with
			| Red | _ =>
				 balance_right c r1 vr
					match c0 with
					| Red =>
						 match r2_2 with
						 | Leaf => (r2_1, false)
						 | Node _ _ _ _ => balance_right c0 r2_1 v0 (remove_rightmost r2_2)
						 end
					| Black =>
						 match r2_2 with
						 | Leaf => (make_black r2_1, isBlack r2_1)
						 | Node _ _ _ _ => balance_right c0 r2_1 v0 (remove_rightmost r2_2)
						 end
					end
			end).
			destruct b.
			*	pose proof bal_right_black_true as P.
				specialize (P l v t n). intuition.
				destruct (balance_right Black l v (t, true)).
				split.
				inv H2; inv H3; inv H2; auto with db;
				inv H4; inv H7; inv H; auto with db.
				inv H3. intro. assumption.
			* pose proof bal_right_black_false as P.
				specialize (P l v t (S n)). intuition.
				destruct (balance_right Black l v (t, false)).
				inv H3. inv H4. split; auto with db.
Qed.

Lemma bal_left_red : forall l x r (b: bool) n,
	(if b then RedBlack l n else RedBlack l (S n))
	-> RedBlack r (S n)
	-> IsBlack l
	-> IsBlack r
	-> let (t, short) := balance_left Red (l, b) x r in
	(if short then RedBlack t n else @RedBlack T t (S n)
	).
Proof.
	intros.
	destruct b.
	- simpl. prove_RB_bal_right.
	- simpl. auto with db.
Qed.

Lemma bal_left_black : forall l x r (b: bool) n,
	(if b then RedBlack l (n) else RedBlack l (S n))
	-> RedBlack r (S n)
	-> let (t, short) := balance_left Black (l, b) x r in
		(if short then RedBlack t (S n) else @RedBlack T t (S (S n))).
Proof.
	intros.
	destruct b.
	- simpl. prove_RB_bal_right.
	- simpl. auto with db.
Qed.


Ltac prove_RB_del :=
	repeat
		match goal with
		| H: RRBlack Leaf _ |- _ => inv H
		| H: _ (Node _ _ _ _) _ |- _ => inv H
		| H: RedBlack Leaf _ |- _ => inv H
		| H: IsBlack (Node Red _ _ _) |- _ => inv H
		| H: if ?b then _ else _ |- _ => destruct b
		| |- let (_,_) := match ?t with Leaf => _ | Node _ _ _ _ => _ end in _ => destruct t
		| |- let (_,_) := balance_right _ _ _ (_, false) in _  => simpl
		| |- let (_,_) := balance_right _ _ _ (match ?t with Leaf => _ | Node _ _ _ _ => _ end) in _ => destruct t
		| |- RedBlack _ _ => constructor
		(* | |- _ (match ?x with Eq => _ | Lt => _ | Gt => _ end) _ => destruct x
		| |- let (_,_) := (let (_,_) := _ in if ?iS then _ else _) in _ => destruct t
		| |- RRBlack _ _ => constructor
		| |- _ (match ?c with Red => _ | Black => _ end) _ => destruct c
		| |- _ (match ?t with Leaf => _ | Node _ _ _ _ => _ end) _ => destruct t *)
		end;
	auto with db; try lia.

Theorem RB_remove: forall (t : tree T) (n : nat),
	RedBlack t (S n) ->
		let (t, short) := remove t in
		if short then RedBlack t n else RedBlack t (S n).
Proof.
	intros.
	induction t.
	- auto with db.
	- simpl. set (max v t1). inv H; destruct t1, t2.
		+ assumption.
		+ simpl. auto with db.
		+ inv H6.
		+ pose proof RB_rrm as P.
			specialize (P c t1_1 v0 t1_2 n). intuition.
			destruct (remove_rightmost (Node c t1_1 v0 t1_2)).
			set (max v (Node c t1_1 v0 t1_2)).
			inv H7. inv H0. intuition.
			apply bal_left_red; assumption.
		+ assumption.
		+ inv H2. inv H6. inv H3; inv H5; simpl; auto with db.
		+ inv H6. inv H2.  inv H4; inv H6.
			* auto with db.
			* inv H8.
			* inv H7.
			* inv H7.
		+	destruct n.
			* inv H2. inv H4; inv H7; simpl. auto with db.
				inv H9. inv H8. inv H8.
			*
			pose proof RB_rrm as P.
			specialize (P c t1_1 v0 t1_2 n). intuition.
			destruct (remove_rightmost (Node c t1_1 v0 t1_2)).
			inv H.
			inv H2. inv H7. inv H10.
			all : apply bal_left_black; assumption.
Qed.

Theorem RB_black_bal_right : forall (l : tree T) v (r : tree T) (b : bool),
	IsBlack (fst (balance_right Black l v (r,b))).
Proof.
	intros.
	destruct b. 2:simpl; auto with db.
	unfold balance_right.
	destruct l. simpl. auto with db.
	destruct c. 2:destruct l1. all: destruct l2;
	unfold fst; auto with db.
	all: destruct c; auto with db.
	destruct c0; auto with db.
Qed.

Theorem RB_black_bal_left : forall (l : tree T) v (r : tree T) (b : bool),
	IsBlack (fst (balance_left Black (l,b) v r)).
Proof.
	intros. unfold fst.
	destruct b. 2:simpl; auto with db.
	unfold balance_left.
	destruct r. auto with db.
	destruct c; destruct r1;
	try destruct r2;
	try destruct c; auto with db.
	destruct c0; auto with db.
Qed.

Theorem RB_rem_black : forall (t : tree T) (n : nat),
	RedBlack t n ->
	IsBlack t -> IsBlack (fst (remove t)).
Proof.
	intros.
	generalize dependent n.
	induction t; intros. auto with db.
	inv H; intuition.
	inv H0.
	unfold remove.
	destruct t1, t2; auto with db.
	inv H6. inv H7. inv H4. inv H6. simpl. auto with db.
	simpl. auto with db.
	simpl. auto with db.
	all: set (max v (Node c t1_1 v0 t1_2)).
	inv H7. inv H6. inv H4. inv H7. simpl. auto with db.
	destruct (remove_rightmost (Node Red Leaf v0 (Node Red l v1 r))).
	apply RB_black_bal_left.
	destruct (remove_rightmost (Node Red (Node Red l v1 r) v0 t1_2)).
	apply RB_black_bal_left.
	inv H6. destruct t1_1, t1_2.
	simpl. auto with db.
	destruct (remove_rightmost (Node Red Leaf v0 (Node c t1_2_1 v2 t1_2_2))).
	apply RB_black_bal_left.
	destruct (remove_rightmost (Node Red (Node c t1_1_1 v2 t1_1_2) v0 Leaf)).
	apply RB_black_bal_left.
	destruct (remove_rightmost (Node Red (Node c t1_1_1 v2 t1_1_2) v0 (Node c1 t1_2_1 v3 t1_2_2))).
	apply RB_black_bal_left.
	destruct (remove_rightmost (Node Black t1_1 v0 t1_2)).
	apply RB_black_bal_left.
Qed.


Theorem RB_del: forall (t : tree T) (n : nat) (x : T),
	(RedBlack t (S n) ->
		let (t, short) := del t x in
		if short then RedBlack t n else RedBlack t (S n))
	/\ (RedBlack t (S n) -> IsBlack t -> IsBlack (fst (del t x))).
Proof.
	induction t; split; intros. inv H. unfold del. assumption.
	- unfold del. destruct (cmp x v) eqn:cmp0.
		+ apply RB_remove. assumption.
		+ fold del. inv H.
			* specialize (IHt1 n x); intuition.
				destruct (del t1 x).
				apply bal_left_red; assumption.
			* 	destruct n.
				-- inv H2; inv H6; simpl; auto with db.
					++ destruct (cmp x v0) eqn:cmp1.
						** inv H; inv H0; simpl; auto with db; inv H1.
						** inv H; inv H0; simpl; auto with db; inv H1.
						** inv H; inv H0; simpl; auto with db; inv H3.
					++ destruct (cmp x v0) eqn:cmp1.
						** inv H; inv H0; simpl; auto with db; inv H1.
						** inv H; inv H0; simpl; auto with db; inv H1.
						** inv H; inv H0; simpl; auto with db; inv H3.
				-- specialize (IHt1 n x); intuition.
					destruct (del t1 x).
					apply bal_left_black; assumption.
		+ fold del. inv H.
			* specialize (IHt2 n x); intuition.
				destruct (del t2 x).
				apply bal_right_red; assumption.
			* 	destruct n.
				-- inv H2; inv H6; simpl; auto with db.
					++ destruct (cmp x v0) eqn:cmp1.
						** inv H; inv H0; simpl; auto with db; inv H1.
						** inv H; inv H0; simpl; auto with db; inv H1.
						** inv H; inv H0; simpl; auto with db; inv H2.
					++ destruct (cmp x v1) eqn:cmp1.
						** inv H2; inv H4; simpl; auto with db; inv H5.
						** inv H2; inv H4; simpl; auto with db; inv H5.
						** inv H2; inv H4; simpl; auto with db; inv H7.
				-- specialize (IHt2 n x); intuition.
					destruct (del t2 x).
					pose proof bal_right_black as P.
					specialize (P t1 v t b n). intuition.
					destruct (balance_right Black t1 v (t, b)).
					inv H3. assumption.
	- unfold del. destruct (cmp x v) eqn:cmp0.
		+ apply RB_rem_black in H; assumption.
		+ fold del. inv H0.
				destruct (del t1 x). apply RB_black_bal_left.
		+ fold del. inv H0.
				destruct (del t2 x). apply RB_black_bal_right.
Qed.

Corollary C_RB_del_1: forall (t : tree T) (n : nat) (x : T),
	RedBlack t (S n) ->
		let (t, short) := del t x in
		if short then RedBlack t n else RedBlack t (S n).
Proof.
	intros.
	pose proof RB_del as P.
	specialize (P t n x).
	intuition.
Qed.

Corollary C_RB_del_2: forall (t : tree T) (n : nat) (x : T),
	RedBlack t (S n) -> IsBlack t -> IsBlack (fst (del t x)).
Proof.
	intros.
	pose proof RB_del as P.
	specialize (P t n x).
	intuition.
Qed.

Theorem RB_delete: forall (t : tree T) (v : T),
	@RedBlacktree T cmp t -> @RedBlacktree T cmp (delete t v) .
Proof.
	unfold RedBlacktree.
	intros.
	inversion H as [ HB [[n0 H0] Hb]].
	repeat split.
	- apply BST_delete. assumption.
	- unfold delete. pose proof C_RB_del_1 as P.
			inv Hb; inversion H0; subst.
				{ exists 0. simpl. auto with db. }
			specialize (P (Node Black l r v0) n v). intuition.
			destruct (del (Node Black l r v0) v).
			destruct b.
				{ exists n. assumption. }
				{ exists (S n). assumption. }
	- unfold delete. pose proof C_RB_del_2 as P.
		inv Hb. simpl. auto with db.
		inversion H0. subst.
		specialize (P (Node Black l r v0) n v). intuition.
Qed.

