From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.

(* Tree definition *)
Inductive colour : Type := Red | Black.
Inductive tree (X : Type) :=
	| Leaf
	| Node (c : colour) (l : tree X) (v : X) (r : tree X).

Arguments Leaf {X}.
Arguments Node {X}.

(* Total ordering of the node *)
Definition total_order (X : Type) : Type := X -> X -> bool.

(* BST properties *)
Fixpoint ForallT {X : Type} (P: X -> Prop) (t: tree X) : Prop :=
  match t with
  | Leaf => True
  | Node c l v r => P v /\ ForallT P l /\ ForallT P r
  end.


Parameter X: Type.
Parameter cmp : total_order X.

Lemma cmp_trans : forall (a b c : X),
	cmp a b = true -> cmp b c = true -> cmp a c = true.
Proof.
	Admitted.

Lemma cmp_inv : forall (a b : X),
	cmp a b = true <-> cmp b a = false.
Proof. Admitted.

Inductive eq : X -> X -> Prop :=
	| eq_refl : forall x, eq x x.

Inductive eqc : colour -> colour -> Prop :=
	| eqc_refl : forall c, eqc c c.

Inductive eqt : tree X -> tree X -> Prop :=
	| eqt_refl : forall t, eqt t t
	| eqt_node : forall c1 c2 l1 l2 v1 v2 r1 r2,
		eqc c1 c2 -> eqt l1 l2 -> eq v1 v2 -> eqt r1 r2 ->
		eqt (Node c1 l1 v1 r1) (Node c2 l2 v2 r2).


Inductive BST: tree X -> Prop :=
| BST_Leaf : BST Leaf
| BST_Node : forall c l v r,
    ForallT (fun y => cmp y v = true) l ->
    ForallT (fun y => cmp v y = true) r ->
    BST l ->
    BST r ->
    BST (Node c l v r).

(* Red-black tree properties *)
	(* root is black *)
Inductive IsBlack {X} : tree X -> Prop :=
	| is_black_leaf : IsBlack Leaf
	| is_black_node : forall c l r v, c = Black -> IsBlack (Node c l r v).

	(* no two consecutive red *)
Inductive RedProp {X} : tree X -> Prop :=
	| red_prop_leaf : RedProp Leaf
	| red_prop_black_node : forall l r v, RedProp l -> RedProp r -> RedProp (Node Black l v r)
	| red_prop_red_node : forall l r v, RedProp l -> RedProp r -> IsBlack l -> IsBlack r -> RedProp (Node Red l v r).

	(* black height of left and right tree is equal *)
Inductive BlackProp_ {X} : tree X -> nat -> Prop :=
	| black_prop_leaf : forall n, BlackProp_ Leaf n
	| black_prop_black_node : forall l r v n, BlackProp_ l (S n) -> BlackProp_ r (S n) -> BlackProp_ (Node Black l v r) n
	| black_prop_red_node : forall l r v n, BlackProp_ l n -> BlackProp_ r n -> BlackProp_ (Node Red l v r) n.

Lemma black_prop_succ : forall (tr : tree X) n,
	BlackProp_ tr n -> BlackProp_ tr (S n).
Proof.
	intros.
	induction H; constructor; assumption.
Qed.

Lemma black_prop_pred : forall (tr : tree X) n,
	BlackProp_ tr (S n) -> BlackProp_ tr n.
Proof.
	intros.
	induction H; constructor; try apply black_prop_succ; assumption.
Qed.

Lemma black_prop_inv : forall (tr : tree X) n m,
	BlackProp_ tr n -> BlackProp_ tr m.
Proof.
	intros.
	induction n.
	- induction m.
		+ assumption.
		+ apply black_prop_succ. assumption.
	- apply IHn. apply black_prop_pred. assumption.
Qed.

Inductive BlackProp {X} : tree X -> Prop :=
	| black_prop : forall n tr, BlackProp_ tr n -> BlackProp tr.



(* Red-black tree definition *)

Definition red_black (tr : tree X) : Prop :=
	BST tr /\ IsBlack tr /\ RedProp tr /\  BlackProp tr.

#[local] Create HintDb db.
#[local] Hint Constructors colour : db.
#[local] Hint Constructors eqc : db.
#[local] Hint Constructors eq : db.
#[local] Hint Constructors tree : db.
#[local] Hint Constructors eqt : db.
#[local] Hint Unfold ForallT : db.
#[local] Hint Constructors BST : db.
#[local] Hint Constructors IsBlack : db.
#[local] Hint Constructors RedProp : db.
#[local] Hint Constructors BlackProp_ : db.
#[local] Hint Constructors BlackProp : db.
#[local] Hint Unfold red_black : db.

Example leaf : forall X cmp,
	@red_black X cmp Leaf.
Proof.
	auto with db.
Qed.


Example trio :
	@red_black nat ltb (Node Black (Node Black Leaf 1 Leaf) 2 (Node Black Leaf 3 Leaf)).
Proof.
	auto 7 with db.
Qed.

Example red_red : forall X  (x y z : X),
	RedProp (Node Black (Node Red (Node Red Leaf x Leaf) y Leaf) z Leaf) -> False.
Proof.
	intros.
	inversion H. subst.
	inversion H2. subst.
	inversion H7. discriminate.
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


Fixpoint insert_util  {X : Type} (cmp : total_order X) (x: X) tr :=
	match tr with
	| Leaf => Node Red Leaf x Leaf
	| Node c l v r =>
		if cmp x v then balance (Node c (insert_util cmp x l) v r)
		else balance (Node c l v (insert_util cmp x r))
	end.

Definition insertion {X} (cmp : total_order X) (x : X) (tr : tree X) : tree X :=
	make_black (
		insert_util cmp x tr
	).

#[local] Hint Unfold make_black : db.
#[local] Hint Unfold balance : db.
#[local] Hint Unfold insert_util : db.
#[local] Hint Unfold insertion : db.

Lemma make_black_preserve_ordering : forall tr,
	BST tr <-> BST (make_black tr).
Proof.
	intros.
	induction tr.
	- split; auto with db.
	- unfold make_black. split;
		intro H; inversion H; subst;
		constructor; auto with db.
Qed.

(* Helpers *)
Inductive id_when_color_rm {X : Type} : tree X -> tree X -> Prop :=
	| id_when_color_rm_refl : forall t, id_when_color_rm t t
	| id_when_color_rm_node : forall c1 c2 l1 l2 r1 r2 v,
		id_when_color_rm l1 l2 -> id_when_color_rm r1 r2 ->
		id_when_color_rm (Node c1 l1 v r1) (Node c2 l2 v r2).

#[local] Hint Constructors id_when_color_rm : db.

Lemma ForallT_inv_coloring : forall (X : Type) (P : X -> Prop) (t1 t2 : tree X),
	id_when_color_rm t1 t2 -> ForallT P t1 -> ForallT P t2.
Proof.
	intros.
	induction H; auto with db.
	inversion H0; subst.
	inversion H3; subst.
	constructor; auto with db.
Qed.

Lemma BST_inv_coloring : forall (tr1 tr2 : tree X),
	id_when_color_rm tr1 tr2 -> BST tr1 -> BST tr2.
Proof.
	intro.
	induction tr1; auto with db.
	- intros. inversion H; auto with db.
	- intros. inversion H; subst; inversion H0; subst;
		constructor; auto with db.
		+ apply (ForallT_inv_coloring X (fun y0 : X => cmp y0 v = true) tr1_1 l2).
			assumption. assumption.
		+ apply (ForallT_inv_coloring X (fun y0 : X => cmp v y0 = true) tr1_2 r2);
			assumption.
Qed.


Inductive rotation {X: Type} : tree X -> tree X -> Prop :=
	| rot_left : forall cx1 cx2 cy1 cy2 a x b y c,
		rotation (Node cy1 (Node cx1 a x b) y c) (Node cx2 a x (Node cy2 b y c))
	| rot_right : forall cx1 cx2 cy1 cy2 a x b y c,
		rotation (Node cx1 a x (Node cy1 b y c)) (Node cy2 (Node cx2 a x b) y c).

#[local] Hint Constructors rotation : db.
Lemma ForallT_impl : forall (X : Type) (P Q : X -> Prop) (t : tree X),
	ForallT P t -> (forall x, P x -> Q x) -> ForallT Q t.
Proof.
	intros.
	induction t.
	- auto with db.
	- unfold ForallT. fold (@ForallT X0). repeat split.
		+ apply H0. apply H.
		+ apply IHt1. apply H.
		+ apply IHt2. apply H.
Qed.

Lemma ForallT_inv_rot : forall (P : X -> Prop) (t1 t2 : tree X),
	rotation t1 t2 -> ForallT P t1 -> ForallT P t2.
Proof.
	intros.
	inversion H; subst.
	- inversion H0; subst;
	constructor; inversion H2; subst;
	inversion H3; subst; auto with db.
	inversion H6. split; auto with db.
	- inversion H0; subst;
	constructor; inversion H2; subst;
	inversion H4; subst; auto with db.
	inversion H6. split; auto with db.
Qed.

Lemma BST_inv_rot : forall tr1 tr2,
	rotation tr1 tr2 -> BST tr1 -> BST tr2.
Proof.
	intros.
		inversion H; subst; inversion H0; subst.
		try inversion H5; subst.
		inversion H7; subst;
		repeat constructor; auto with db.
		- apply ForallT_impl with (P := (fun y0 : X => cmp y y0 = true));
			try (intro; apply (cmp_trans x y)); assumption.
		- inversion H2. assumption.
		(* other direction *)
		- repeat constructor; auto with db;
			inversion H0; subst; inversion H10; subst; inversion H12; subst;
			inversion H2; subst; try assumption.
			apply ForallT_impl with (P := (fun y0 : X => cmp y0 x = true)).
			assumption. intros. apply (cmp_trans x0 x y); assumption.
Qed.

(* We don't care about colour now (BST doesn't depend on color)*)
Inductive double_rot {X : Type} : tree X -> tree X -> Prop :=
	| rotation_left_left : forall (cx1 cy1 cz1 cx2 cy2 cz2 : colour)
		a x b y c z d,
		double_rot
			(Node cz1 (Node cy1 (Node cx1 a x b) y c) z d)
			(Node cy2 (Node cx2 a x b) y (Node cz2 c z d))
	| rotation_left_right : forall (cx1 cy1 cz1 cx2 cy2 cz2 : colour)
		a x b y c z d,
		double_rot
			(Node cz1 (Node cx1 a x (Node cy1 b y c)) z d)
			(Node cy2 (Node cx2 a x b) y (Node cz2 c z d))
	| rotation_right_left : forall (cx1 cy1 cz1 cx2 cy2 cz2 : colour)
		a x b y c z d,
		double_rot
			(Node cx1 a x (Node cz1 (Node cy1 b y c) z d))
			(Node cy2 (Node cx2 a x b) y (Node cz2 c z d))
	| rotation_right_right : forall (cx1 cy1 cz1 cx2 cy2 cz2 : colour)
		a x b y c z d,
		double_rot
			(Node cx1 a x (Node cy1 b y (Node cz1 c z d)))
			(Node cy2 (Node cx2 a x b) y (Node cz2 c z d))
			.

#[local] Hint Constructors double_rot : db.

Lemma BST_inv_2rot : forall tr1 tr2,
	double_rot tr1 tr2 -> BST tr1 <-> BST tr2.
Proof.
	intros.
	split.
	- intro H1.
		induction H; subst.
		+ apply (BST_inv_rot (Node cz1 (Node cy1 (Node cx2 a x b) y c) z d) (Node cy2 (Node cx2 a x b) y (Node cz2 c z d))).
			constructor. inversion H1; subst.
			apply BST_Node; auto with db.
			apply (BST_inv_coloring (Node cy1 (Node cx1 a x b) y c)); auto with db.
		+ apply (BST_inv_rot (Node cz1 (Node cy1 (Node cx2 a x b) y c) z d) (Node cy2 (Node cx2 a x b) y (Node cz2 c z d))).
			constructor. inversion H1. subst.
			apply BST_Node;
			inversion H1; auto with db.
			* apply (ForallT_inv_rot (fun y0 : X => cmp y0 z = true) (Node cx1 a x (Node cy1 b y c))).
				constructor. assumption.
			* apply (BST_inv_rot (Node cx1 a x (Node cy2 b y c))).
				constructor.
				apply (BST_inv_coloring (Node cx1 a x (Node cy1 b y c))); auto with db.
		+ apply (BST_inv_rot (Node cx1 a x (Node cy1 b y (Node cz2 c z d) )) (Node cy2 (Node cx2 a x b) y (Node cz2 c z d))).
			constructor.
			apply BST_Node;
			try (inversion H1; assumption);
			inversion H1; subst.
			* apply (ForallT_inv_rot (fun y0 : X => cmp x y0 = true) (Node cz1 (Node cy1 b y c) z d)).
				constructor. assumption.
			* apply (BST_inv_rot (Node cz1 (Node cy1 b y c) z d) (Node cy1 b y (Node cz2 c z d))).
				constructor. assumption.
		+ apply (BST_inv_rot (Node cx1 a x (Node cy1 b y (Node cz2 c z d) )) (Node cy2 (Node cx2 a x b) y (Node cz2 c z d)));
			constructor;
			inversion H1; auto with db.
			apply (BST_inv_coloring (Node cy1 b y (Node cz1 c z d))); auto with db.
	- intro H1.
		inversion H; subst.
		+ apply (BST_inv_rot (Node cy1 (Node cx1 a x b) y (Node cz1 c z d))).
			constructor.
			apply (BST_inv_coloring (Node cy2 (Node cx2 a x b) y (Node cz2 c z d))); auto with db.
		+ inversion H1; subst.
			constructor; inversion H5; inversion H6; inversion H7; inversion H8; subst; auto with db.
			* constructor; auto with db.
				apply (cmp_trans x y z); assumption.
				inversion H2; inversion H4; auto with db.
				split; auto with db. apply (ForallT_impl X (fun y0 : X => cmp y0 y = true) (fun y0 : X => cmp y0 z = true)); auto with db.
				intros. apply (cmp_trans x0 y); auto with db.
				constructor; auto with db. split.
				apply (ForallT_impl X (fun y0 : X => cmp y0 y = true)); auto with db.
				intros. apply (cmp_trans x0 y); auto with db.
				apply (ForallT_impl X (fun y0 : X => cmp y0 z = true)); auto with db.
			* constructor; auto with db; constructor;
				inversion H2; inversion H4; auto with db;
				split; auto with db;
				apply (ForallT_impl X (fun y0 : X => cmp y y0 = true)); auto with db;
				intros; apply (cmp_trans x y); auto with db.
		+ inversion H1; subst.
			constructor; inversion H5; inversion H6; inversion H7; inversion H8; subst; auto with db.
			* constructor; auto with db.
				apply (cmp_trans x y); auto with db.
				inversion H2; inversion H4; auto with db.
				split; auto with db;
				try (constructor; try split; auto with db);
				apply (ForallT_impl X (fun y0 : X => cmp y y0 = true)); auto with db;
				intros; apply (cmp_trans x y ); auto with db.
			* constructor; auto with db; constructor;
				inversion H2; inversion H4; auto with db.
				split; auto with db.
				apply (ForallT_impl X (fun y0 : X => cmp y0 y = true)); auto with db.
				intros. apply (cmp_trans x0 y); auto with db.
		+ apply (BST_inv_rot (Node cy1 (Node cx1 a x b) y (Node cz1 c z d))).
			constructor.
			apply (BST_inv_coloring (Node cy2 (Node cx2 a x b) y (Node cz2 c z d))); auto with db.
Qed.

Ltac apply_rotation :=
	match goal with
	H: BST (?tr) |- _ => apply (BST_inv_2rot tr); auto with db
	end.

Lemma balance_preserve_ordering : forall tr,
	BST tr -> BST (balance tr).
Proof.
	induction tr as [| c tr1 HIt1 v tr2 HIt2].
	- auto with db.
	- intro.
		 destruct c. auto with db.
		destruct tr1 as [| c1 tr11 v1 tr12];
		auto with db;
		destruct tr2 as [| c2 tr21 v2 tr22];
		auto with db;
		try destruct tr11 as [| c11 tr111 v11 tr112];
		auto with db;
		try destruct tr12 as [| c12 tr121 v12 tr122];
		auto with db;
		try destruct tr21 as [| c21 tr211 v21 tr212];
		auto with db;
		try destruct tr22 as [| c22 tr221 v22 tr222];
		auto with db;
		try destruct c1; try destruct c2;
		auto with db;
		try destruct c11; try destruct c12;
		auto with db;
		try destruct c21; try destruct c22;
		auto with db;
		unfold balance; auto with db;
		apply_rotation.
Qed.

Lemma ForallT_inv_2rot : forall (P : X -> Prop) (t1 t2 : tree X),
	double_rot t1 t2 -> ForallT P t1 <-> ForallT P t2.
Proof.
	intros.
	split.
	- intro H1.
		induction H; subst.
		+ apply (ForallT_inv_rot P (Node cz1 (Node cy1 (Node cx2 a x b) y c) z d) (Node cy2 (Node cx2 a x b) y (Node cz2 c z d))).
			constructor. inversion H1; subst.
			constructor; auto with db.
		+ apply (ForallT_inv_rot P (Node cz1 (Node cy1 (Node cx2 a x b) y c) z d) (Node cy2 (Node cx2 a x b) y (Node cz2 c z d))).
			constructor. inversion H1. subst.
			constructor.
			inversion H1; auto with db.
			inversion H0; split; auto with db.
			apply (ForallT_inv_rot P (Node cx1 a x (Node cy1 b y c))); auto with db.
		+ apply (ForallT_inv_rot P (Node cx1 a x (Node cy1 b y (Node cz2 c z d) )) (Node cy2 (Node cx2 a x b) y (Node cz2 c z d)));
			constructor.
			try (inversion H1; assumption);
			inversion H1; subst.
			inversion H1; auto with db.
			inversion H0; split; auto with db.
			apply (ForallT_inv_rot P (Node cz1 (Node cy1 b y c) z d)); auto with db.
		+ apply (ForallT_inv_rot P (Node cx1 a x (Node cy1 b y (Node cz2 c z d) )) (Node cy2 (Node cx2 a x b) y (Node cz2 c z d)));
			constructor;
			inversion H1; auto with db.
	- intro H1.
		inversion H; subst.
		+ apply (ForallT_inv_rot P (Node cy1 (Node cx1 a x b) y (Node cz1 c z d))).
			constructor.
			apply (ForallT_inv_coloring X P (Node cy2 (Node cx2 a x b) y (Node cz2 c z d))); auto with db.
		+ inversion H1; subst.
			inversion H2; subst.
			inversion H3; subst.
			inversion H4; subst.
			inversion H6; subst.
			inversion H8; subst.
			constructor; auto with db.
			split; auto with db.
			constructor; auto with db.
		+ inversion H1; subst.
			inversion H2; subst.
			inversion H3; subst.
			inversion H4; subst.
			inversion H6; subst.
			inversion H8; subst.
			constructor; auto with db.
			split; auto with db.
			constructor; auto with db.
		+ apply (ForallT_inv_rot P (Node cy1 (Node cx1 a x b) y (Node cz1 c z d))).
			constructor.
			apply (ForallT_inv_coloring X P (Node cy2 (Node cx2 a x b) y (Node cz2 c z d))); auto with db.
Qed.

Ltac apply_Forall_rotation :=
	match goal with
	| H: ForallT ?P ?tr |- _ => apply (ForallT_inv_2rot P tr); auto with db
	end.


Lemma forall_balance : forall P (tr : tree X),
	ForallT P tr -> ForallT P (balance tr).
Proof.
	intros.
	induction tr as [| c tr1 H1 v tr2 H2]; auto with db.
		 destruct c. auto with db.
		destruct tr1 as [| c1 tr11 v1 tr12];
		auto with db;
		destruct tr2 as [| c2 tr21 v2 tr22];
		auto with db;
		try destruct tr11 as [| c11 tr111 v11 tr112];
		auto with db;
		try destruct tr12 as [| c12 tr121 v12 tr122];
		auto with db;
		try destruct tr21 as [| c21 tr211 v21 tr212];
		auto with db;
		try destruct tr22 as [| c22 tr221 v22 tr222];
		auto with db;
		try destruct c1; try destruct c2;
		auto with db;
		try destruct c11; try destruct c12;
		auto with db;
		try destruct c21; try destruct c22;
		auto with db;
		unfold balance; auto with db;
		apply_Forall_rotation.
Qed.

Lemma forall_inv_insert_util_1 : forall (tr : tree X) x y,
	ForallT (fun z : X => cmp x z = true ) tr ->
	cmp x y = true ->
	ForallT (fun z : X => cmp x z = true) (insert_util cmp y tr).
Proof.
	intros.
	induction tr as [| c tr1 H1 v tr2 H2].
	- unfold insert_util. auto with db.
	- unfold insert_util. auto with db.
		destruct (cmp y v) eqn: Hcmp; fold (insert_util cmp);
		apply forall_balance; auto with db;
		inversion H; subst; auto with db;
		inversion H4; subst; auto with db;
		constructor; auto with db.
Qed.

Lemma forall_inv_insert_util_2 : forall (tr : tree X) x y,
	ForallT (fun z : X => cmp z x = true ) tr ->
	cmp y x = true ->
	ForallT (fun z : X => cmp z x = true) (insert_util cmp y tr).
Proof.
	intros.
	induction tr as [| c tr1 H1 v tr2 H2].
	- unfold insert_util. auto with db.
	- unfold insert_util. auto with db.
		destruct (cmp y v) eqn: Hcmp; fold (insert_util cmp);
		apply forall_balance; auto with db;
		inversion H; subst; auto with db;
		inversion H4; subst; auto with db;
		constructor; auto with db.
Qed.



Lemma insert_util_preserve_ordering : forall tr x,
	BST tr -> BST (insert_util cmp x tr).
Proof.
	intros.
	induction tr as [| c t1 H1 v t2 H2].
	- unfold insert_util. constructor; auto with db.
	- unfold insert_util.
		destruct (cmp x v) eqn: Hcmp; fold (insert_util cmp x);
		apply balance_preserve_ordering; auto with db;
		inversion H; subst; auto with db.
		+ constructor; auto with db.
			apply (forall_inv_insert_util_2 t1 v x); auto with db.
		+ apply cmp_inv in Hcmp. constructor; auto with db.
			apply (forall_inv_insert_util_1 t2 v x); auto with db.
Qed.

Lemma insertion_preserve_ordering :	forall tr x,
	BST tr -> BST (insertion cmp x tr) .
Proof.
	intros.
	unfold insertion.
	apply -> make_black_preserve_ordering.
	apply insert_util_preserve_ordering.
	assumption.
Qed.

Lemma make_black_turn_black : forall tr,
	@IsBlack X (make_black tr).
Proof.
	intros.
	destruct tr; auto with db;
	unfold make_black; auto with db.
Qed.

Lemma pop_make_black: forall (X : Type) (P : tree X -> Prop) c l r v,
	P (make_black (Node c l r v)) -> P (Node Black l r v).
Proof.
	intros.
	destruct c; auto with db.
Qed.

Lemma insertion_preserve_black_root : forall tr x,
	IsBlack tr -> @IsBlack X (insertion cmp x tr).
Proof.
	intros.
	unfold insertion.
	apply make_black_turn_black.
Qed.

Lemma black_inv_rotation : forall tr1 tr2,
	rotation tr1 tr2 -> BlackProp tr1 -> @BlackProp X tr2.
Proof.
	intros.
	inversion H; subst;
	inversion H0 as [n tr H1]; subst;
	inversion H1; subst;
	destruct cx2; destruct cy2; auto with db;
		apply (black_prop n);
		constructor; auto with db;
		inversion H7; subst; auto with db;
		inversion H8; subst; auto with db;
		try constructor; auto with db;
		try (apply (black_prop_inv a n); assumption);
		try (apply (black_prop_inv a (S n)); assumption);
		try (apply (black_prop_inv a (S (S n))); assumption);
		try (apply (black_prop_inv b n); assumption);
		try (apply (black_prop_inv b (S n)); assumption);
		try (apply (black_prop_inv b (S (S n))); assumption);
		try (apply (black_prop_inv c n); assumption);
		try (apply (black_prop_inv c (S n)); assumption);
		try (apply (black_prop_inv c (S (S n))); assumption);
		try (apply (black_prop_inv (Node Black l v r) n); assumption);
		try (apply (black_prop_inv (Node Black l v r) (S n)); assumption);
		try (apply (black_prop_inv (Node Black l v r) (S (S n))); assumption);
		try (apply (black_prop_inv (Node Red l v r) n); assumption);
		try (apply (black_prop_inv (Node Red l v r) (S n)); assumption);
		try (apply (black_prop_inv (Node Red l v r) (S (S n))); assumption);
		auto with db.
Qed.

Ltac apply_black_prop_inv :=
	match goal with
	| H: BlackProp_ ?tr ?n |- _ => apply (black_prop_inv tr n); assumption
	end.

Lemma black_inv_2rot : forall tr1 tr2,
	double_rot tr1 tr2 -> BlackProp tr1 -> @BlackProp X tr2.
Proof.
	intros.
	inversion H; subst; inversion H0 as [n tr H1]; subst;
	auto with db.
	- apply (black_inv_rotation (Node cz1 (Node cy1 (Node cx2 a x b)y c) z d)).
		constructor. apply (black_prop n);
		inversion H1; subst; auto with db;
		constructor; auto with db;
		inversion H7; subst; auto with db;
		constructor; auto with db;
		inversion H10; subst; auto with db;
		destruct cx2;
		constructor; auto with db;
		inversion H9; subst; auto with db;
		apply_black_prop_inv.
	- apply (black_inv_rotation (Node cz1 (Node cy1 (Node cx2 a x b) y c) z d)).
		constructor. auto with db.
		apply (black_prop n);
		inversion H1; subst; auto with db;
		constructor; auto with db;
		inversion H7; subst; auto with db;
		inversion H10; subst; auto with db;
		constructor; auto with db;
		destruct cx2; try constructor; auto with db;
		apply_black_prop_inv.
	- apply (black_inv_rotation (Node cx1 a x (Node cy1 b y (Node cz2 c z d)))).
		constructor. auto with db.
		apply (black_prop n);
		inversion H1; subst; auto with db;
		constructor; auto with db;
		inversion H8; subst; auto with db;
		inversion H9; subst; auto with db;
		constructor; auto with db;
		destruct cz2; try constructor; auto with db;
		apply_black_prop_inv.
	- apply (black_inv_rotation (Node cx1 a x (Node cy1 b y (Node cz2 c z d)))).
		constructor.
		apply (black_prop n);
		inversion H1; subst; auto with db;
		constructor; auto with db;
		inversion H7; subst; auto with db;
		inversion H8; subst; auto with db;
		constructor; auto with db;
		destruct cz2;
		constructor; auto with db;
		try inversion H10; try inversion H12; subst; auto with db;
		apply_black_prop_inv.
Qed.

Ltac apply_black_inv_rotation :=
	match goal with
	| H: BlackProp ?tr |- _ => apply (black_inv_2rot tr); auto with db
	end.


Lemma balance_inv_black : forall tr,
	BlackProp tr -> @BlackProp X (balance tr).
Proof.
	intros.
	induction tr as [| c tr1 H1 v tr2 H2]; auto with db;
		 destruct c; auto with db.
		destruct tr1 as [| c1 tr11 v1 tr12];
		auto with db;
		destruct tr2 as [| c2 tr21 v2 tr22];
		auto with db;
		try destruct tr11 as [| c11 tr111 v11 tr112];
		auto with db;
		try destruct tr12 as [| c12 tr121 v12 tr122];
		auto with db;
		try destruct tr21 as [| c21 tr211 v21 tr212];
		auto with db;
		try destruct tr22 as [| c22 tr221 v22 tr222];
		auto with db;
		try destruct c1; try destruct c2;
		auto with db;
		try destruct c11; try destruct c12;
		auto with db;
		try destruct c21; try destruct c22;
		auto with db;
		unfold balance; auto with db;
		apply_black_inv_rotation; auto with db.
Qed.

Lemma black_inv_make_black : forall tr,
	BlackProp tr <-> @BlackProp X (make_black tr).
Proof.
	intros.
	destruct tr; auto with db;
	unfold make_black; auto with db.
	reflexivity.
	split; intro H;
	inversion H; subst; auto with db;
	inversion H0; subst; auto with db;
	apply (black_prop n);
	try destruct c;
	constructor; auto with db; apply_black_prop_inv.
Qed.

(* Lemma black__inv_insert_util : forall tr x n,
	BlackProp_ tr n -> @BlackProp_ X (insert_util cmp x tr) n.
Proof.
	intros.
	inversion H; subst;
	unfold insertion.
	constructor; auto with db.
	unfold insert_util.
	assumption.	 *)

Lemma insertion_preserve_black : forall tr x,
	BlackProp tr -> BlackProp (insertion cmp x tr).
Proof.
	intros.
	induction tr.
	- unfold insertion. unfold insert_util. unfold make_black.
		apply (black_prop 0); auto with db.
	- unfold insertion. apply -> black_inv_make_black.
		unfold insert_util.
		destruct (cmp x v) eqn: Hcmp; fold (insert_util cmp x).
		+ apply balance_inv_black.
			inversion H; subst; auto with db.
			inversion H0; subst; auto with db;
			apply (black_prop n); auto with db;
			constructor; auto with db;
			try apply (black_prop (n)) in H6;
			try apply (black_prop (S n)) in H6;
			apply IHtr1 in H6;
			unfold insertion in H6;
			apply black_inv_make_black in H6;
			inversion H6;
			apply_black_prop_inv.
		+ apply balance_inv_black.
			inversion H; subst; auto with db;
			inversion H0; subst; auto with db;
			apply (black_prop n); auto with db;
			constructor; auto with db;
			try apply (black_prop (n)) in H7;
			try apply (black_prop (S n)) in H7;
			apply IHtr2 in H7;
			unfold insertion in H7;
			apply black_inv_make_black in H7;
			inversion H7;
			apply_black_prop_inv.
Qed.

Lemma red_inv_black : forall (X : Type) l v r,
	RedProp (Node Red l v r) -> @RedProp X (Node Black l v r).
Proof.
	intros.
	inversion H; subst.
	auto with db.
Qed.

Lemma red_inv_make_black : forall (X : Type) tr,
	RedProp tr -> @RedProp X (make_black tr).
Proof.
	intros.
	destruct tr; auto with db.
	unfold make_black; auto with db.
	inversion H; subst; auto with db.
Qed.

Lemma balance_imp_red : forall (X: Type) tr,
	RedProp tr -> @RedProp X (balance tr).
Proof.
	intros.
	induction tr as [| c tr1 H1 v tr2 H2].
	- unfold balance. auto with db.
	-
		destruct c; auto with db;
		induction tr1 as [| c1 tr11 H11 v1 tr12 H12];
		auto with db;
		induction tr2 as [| c2 tr21 H21 v2 tr22 H22];
		auto with db;
		try destruct tr11 as [| c11 tr111 v11 tr112];
		auto with db;
		try destruct tr12 as [| c12 tr121 v12 tr122];
		auto with db;
		try destruct tr21 as [| c21 tr211 v21 tr212];
		auto with db;
		try destruct tr22 as [| c22 tr221 v22 tr222];
		auto with db;
		try destruct c1; try destruct c2;
		auto with db;
		try destruct c11; try destruct c12;
		auto with db;
		try destruct c21; try destruct c22;
		auto with db;
		unfold balance; auto with db;
		inversion H; subst;
		inversion H4; subst;
		inversion H6; subst;
		constructor; auto with db;
		try (apply pop_make_black with (c := Red); auto with db;
		apply red_inv_make_black; assumption);
		try inversion H6; subst;
		try inversion H8; subst;
		try inversion H10; subst;
		try inversion H13; subst;
		try inversion H15; subst;
		try discriminate;
		constructor; auto with db.
Qed.

Lemma red_inv_bal_black : forall (X : Type) tr v,
	RedProp (tr) -> @RedProp X (make_black (balance (Node Red Leaf v tr))).
Proof.
	intros.
	induction tr as [| c tr1 H1 v1 tr2 H2].
	- unfold balance. unfold make_black. auto with db.
	- unfold balance. unfold make_black.
		constructor; auto with db.
Qed.

Lemma red_merge_red : forall (X : Type) l v r,
	RedProp (l) ->
	RedProp (r) ->
	@RedProp X (Node Black l v r).
Proof.
	auto with db.
Qed.

Ltac redprop_contra :=
	match goal with
	| H: RedProp (Node Red (Node Red _ _ _) _ _)
		|- _ => inversion H as [| | ? ? ? ? ? T];
				inversion T; discriminate
	| H: RedProp (Node Red ?l ?v (Node Red ?rl ?rv ?rr))
		|- _ => inversion H as [| | ? ? ? ? ? ? T ];
				inversion T; discriminate
	end.

Lemma red_merge_is_balance : forall (X : Type) tr,
	RedProp (tr) ->
	@RedProp X (balance tr).
Proof.
	intros.
	induction tr as [| c tr1 H1 v tr2 H2].
	- unfold balance. auto with db.
	- inversion H; subst; auto with db.
		apply H1 in H4 as H3. apply H2 in H7 as H5.
		clear H1 H2. rename H4 into H1. rename H7 into H2.
		rename H5 into H4.
		destruct tr1; destruct tr2.
		+ trivial.
		+ destruct c; auto with db.
			destruct tr2_1; destruct tr2_2.
			* trivial.
			* destruct c.
				redprop_contra.
				trivial.
			* destruct c.
				redprop_contra.
				trivial.
			* destruct c.
				redprop_contra.
				destruct c0.
				redprop_contra.
				trivial.
		+ destruct c; auto with db.
			destruct tr1_1; destruct tr1_2.
			* trivial.
			* destruct c.
				redprop_contra.
				trivial.
			* destruct c.
				redprop_contra.
				trivial.
			* destruct c.
				redprop_contra.
				destruct c0.
				redprop_contra.
				trivial.
		+ destruct c; auto with db;
			destruct c0; auto with db;
			destruct tr1_1; destruct tr1_2;
			destruct tr2_1; destruct tr2_2;
			auto with db;
			destruct c;
			try destruct c0;
			try destruct c1;
			try destruct c2;
			auto with db;
			try redprop_contra.
Qed.

Ltac isblack_contra :=
	match goal with
	| H: IsBlack (Node Red _ _ _)
		|- _ => inversion H; discriminate
	end.

Example test : forall (X : Type) l v r,
	@IsBlack X (Node Red l v r) -> False.
Proof.
	intros.
	isblack_contra.
Qed.


(* Okasaki case 1 *)
Lemma red_inv_balance_1 : forall (X : Type) a x b y c z d,
	RedProp a -> RedProp b -> RedProp c -> RedProp d ->
	@RedProp X (balance
		(Node Black
			(Node Red (Node Red a x b) y c) z d)).
Proof.
	unfold balance.
	auto with db.
Qed.

(* Okasaki case 2 *)
Lemma red_inv_balance_2 : forall (X : Type) a x b y c z d,
	RedProp a -> IsBlack a -> RedProp b -> RedProp c -> RedProp d ->
	@RedProp X (balance
		(Node Black
			(Node Red a x (Node Red b y c)) z d)).
Proof.
	intros.
	destruct a; try destruct c0;
	try isblack_contra;
	unfold balance; auto with db.
Qed.

(* Okasaki case 3 *)
Lemma red_inv_balance_3 : forall (X : Type) a x b y c z d,
	RedProp a -> IsBlack a -> RedProp b -> RedProp c -> RedProp d ->
	@RedProp X (balance
		(Node Black
			a x (Node Red (Node Red b y c) z d))).
Proof.
	intros.
	destruct a; try destruct c0;
	try isblack_contra;
	unfold balance; auto with db.
Qed.

(* Okasaki case 4 *)
Lemma red_inv_balance_4 : forall (X : Type) a x b y c z d,
	RedProp a -> IsBlack a -> RedProp b -> IsBlack b -> RedProp c -> RedProp d ->
	@RedProp X (balance
		(Node Black
			a x (Node Red b y (Node Red c z d)))).
Proof.
	intros.
	destruct a; try destruct c0;
	try isblack_contra;
	destruct b; try destruct c0;
	try isblack_contra;
	unfold balance; auto with db.
Qed.

(* Lemma toto : forall (X : Type) (tr : tree X) v,
	RedProp (Node Red Leaf v (balance tr)) ->
	@RedProp X (make_black (balance (Node Red Leaf v tr))).
Proof.
	intros.
	induction tr as [| c tr1 H1 v1 tr2 H2].
	- unfold balance. unfold make_black. auto with db.
	- destruct tr1; destruct tr2;
		destruct c; try destruct c0; try destruct c1;
		try (unfold balance in H; redprop_contra);
		auto with db;
		unfold balance; unfold make_black; auto with db;
		try destruct tr1_1; try destruct tr1_2;
		try destruct tr2_1; try destruct tr2_2;
		try destruct c; try destruct c0; try destruct c1; try destruct c2;
		try (unfold balance in H; redprop_contra);
		auto with db;
		unfold balance in H;
		inversion H; subst; auto with db.
Qed.


Lemma red_inv_merge : forall (X : Type) tr1 v tr2 v0 tr,
	RedProp tr1 ->
	IsBlack tr1 ->
	RedProp tr2 ->
	IsBlack tr2 ->
	RedProp (balance (Node Black tr1 v0 tr)) ->
	RedProp (balance (Node Black tr2 v0 tr)) ->
	@RedProp X (balance (Node Red (Node Black tr1 v tr2) v0 tr)).
Proof.
	intros.
	induction tr.
		+ destruct tr1; destruct tr2;
			try destruct c; try destruct c0;
			unfold balance; auto with db;
			unfold balance in H; unfold balance in H0;
			auto with db;
			try redprop_contra;
			inversion H; subst; auto with db;
			inversion H0; subst; auto with db;
			inversion H2; subst; discriminate.
		+ unfold balance. constructor; auto with db.
	- destruct c; destruct c0;
		induction tr1; induction tr2;
			induction tr3; induction tr4;
			try destruct c; try destruct c0;
			try destruct c1; try destruct c2;
			try isblack_contra;
			try redprop_contra;
			unfold balance; auto with db;
			unfold balance in H3; unfold balance in H4;
			inversion H3; subst; auto with db;
			inversion H4; subst; auto with db;
			constructor; auto with db.
Qed.

Theorem tata : forall (X : Type) tr1 v c2 tr2_1 v2 tr2_2  ,
	RedProp tr1 ->
	RedProp (balance (Node Black tr2_1 v tr2_2)) ->
	@RedProp X (balance (Node Black tr1 v (balance (Node c2 tr2_1 v2 tr2_2)))).
Proof.
	intros X.
	induction tr1.
	- intros. destruct c2 eqn: Hc2.
		+ 	destruct tr2_1; destruct tr2_2;
			try destruct c; try destruct c0;
			try redprop_contra;
			unfold balance;
			auto with db.
		+ 	destruct tr2_1; destruct tr2_2;
			try destruct tr2_1_1; try destruct tr2_1_2;
			try destruct tr2_2_1; try destruct tr2_2_2;
			try destruct c; try destruct c0; try destruct c1;
			try destruct c2; try destruct c3; try destruct c4;
			try destruct c5;
			try redprop_contra;
			unfold balance; auto with db.
	- intros.
		inversion H; subst;
		apply red_inv_merge; auto with db.
Admitted. *)

Theorem red_inv_insert_until : forall tr1 v tr2 x,
	RedProp (tr1) ->
	RedProp (tr2) ->
	RedProp (insert_util cmp x (Node Black tr1 v tr2)) .
Proof.
	Admitted.

Theorem inversion_preserve_red : forall tr x,
	RedProp tr -> RedProp (insertion cmp x tr) .
Proof.
	intros.
	induction tr as [| c tr1 IH1 v tr2 IH2].
	- unfold insertion. apply red_inv_make_black.
		constructor; auto with db.
	- induction tr1 as [| c1 tr11 H11 v1 tr12 H12].
		(* Left is empty *)
		+ induction tr2 as [| c2 tr21 H21 v2 tr22 H22].
			(* Both are empty *)
			* unfold insertion. unfold insert_util.
				destruct (cmp x v) eqn: Hcmp;
				unfold balance; destruct c;
				auto with db; unfold make_black;
				auto with db.
			(* Right is non empty *)
			* unfold insertion. unfold insert_util.
				fold (insert_util cmp x).
				destruct (cmp x v) eqn: Hcmp.
				(* inserion to the left *)
				-- destruct c.
					++ unfold balance; unfold make_black.
						inversion H.
						constructor; auto with db.
					++ destruct c2;
							destruct tr21; destruct tr22;
							try destruct c; try destruct c0;
							try redprop_contra;
							unfold balance; unfold make_black;
							auto with db;
							inversion H; subst;
							inversion H4; subst;
							try inversion H5; subst;
							inversion H6; subst;
							auto with db.
				(* insertion to the right *)
				-- destruct (cmp x v2) eqn: Hcmp2.
					(*insertion to the left of the right *)
					++ destruct c; destruct c2.
						** destruct tr21; destruct tr22;
							try destruct c; try destruct c0;
							try redprop_contra;
							unfold balance; unfold make_black;
							auto with db;
							inversion H; subst;
							inversion H4; subst;
							try inversion H5; subst;
							inversion H6; subst;
							auto with db.
						** destruct tr21; destruct tr22;
							try destruct c; try destruct c0;
							try redprop_contra;
							try isblack_contra;
							unfold balance at 1.
							auto with db;
							inversion H; subst;
							inversion H4; subst;
							try inversion H5; subst;
							inversion H6; subst;
							auto with db.

						unfold balance; unfold make_black.
						inversion H.
						constructor; auto with db.

					auto with db; unfold make_black;
					auto with db.
				unfold balance; destruct c;
				auto with db; unfold make_black;
				auto with db.
			* unfold insertion.
			* inversion H; subst.
				apply red_inv_balance_1; auto with db.
			(* insert to the right *)
			destruct c; auto with db;
			unfold balance;
			unfold make_black;
			constructor; auto with db.
		+ unfold insertion. unfold insert_util.
			fold (insert_util cmp x).
			destruct (cmp x v) eqn: Hcmp;
			destruct c eqn: HC;
			destruct c2 eqn: HC2.
			*	inversion H; subst; auto with db;
				inversion H6; subst; auto with db;
				discriminate.
			* unfold balance; unfold make_black.
				constructor; auto with db.
				inversion H; subst; auto with db.
			* inversion H; subst; auto with db.
				apply red_inv_make_black.
				apply red_merge_is_balance.
				constructor; auto with db.
			* inversion H; subst; auto with db.
				unfold balance; unfold make_black.
				constructor; auto with db.
			* redprop_contra.
			* unfold balance at 1. unfold make_black.
				apply IH2 in H4.
				unfold insertion in H4.	unfold insert_util in H4.
				fold (insert_util cmp x) in H4.
				destruct (cmp x v2) eqn: Hcmp2;
				apply toto; auto with db.

Qed.


Theorem insertion_preserve_rbtree : forall tr v,
	red_black tr -> red_black (insertion cmp v tr).
Proof.
	intros.
	destruct H.
	destruct H0.
	destruct H1.
	repeat constructor.
	- apply insertion_preserve_ordering. assumption.
	- apply insertion_preserve_black_root. assumption.
	- apply inversion_preserve_red. assumption.
	- apply insertion_preserve_black. assumption.
Qed.
