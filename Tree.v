From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq choice fintype.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
 
Inductive BinaryTree (T : Type) : Type :=
    | Nill : BinaryTree T
    | Node : BinaryTree T -> BinaryTree T -> T -> BinaryTree T -> BinaryTree T
    .

Check (Nill nat).
Check (Node (Nill nat) (Nill nat) 5 (Nill nat)).
Check (Node (Nill nat) (Nill nat) 5 
      (Node (Nill nat) (Nill nat) 7 (Nill nat))).

(* ========================= *)
(* Functions of BinaryTree T *)
(* ========================= *)

Definition Lst {T} (tree : BinaryTree T) : BinaryTree T :=
  match tree with
  | Nill => Nill T
  | Node _ Left _ _ => Left
  end.

Definition Rst {T} (tree : BinaryTree T) : BinaryTree T :=
  match tree with
  | Nill => Nill T
  | Node _ _ _ Right => Right
  end.

Notation null := (Nill nat).
Notation "l -| v |- r" := (Node (Nill nat) l v r) (at level 43, left associativity).
Notation "@ v " := (null -| v |- null) (at level 43, left associativity).

Eval compute in (Lst null).
Eval compute in (Rst null).

Eval compute in (Lst (@5)).
Eval compute in (Rst (@5)).

Eval compute in (Lst ((@3) -| 5 |- (@7))).
Eval compute in (Rst ((@3) -| 5 |- (@7))).

Fixpoint nodes {T} (tree : BinaryTree T) : seq T := 
  match tree with
  | Nill => [::]
  | Node _ Left value Right => value :: (nodes Left ++ nodes Right)
  end.

(* ====================== *)
(* Height of BinaryTree T *)
(* ====================== *)

Fixpoint height {T} (tree : BinaryTree T) : nat :=
    match tree with
    | Nill              => 0
    | Node _ Left _ Right => 1 + maxn (height Left) (height Right)
    end.

Lemma height_nill : forall {T}, height (Nill T) = 0.
Proof. 
  done.
Qed.

Lemma height_empty_tree : forall {T} (tree : BinaryTree T),
  height tree = 0 <-> tree = Nill T.
Proof. 
  by move => T; case.
Qed.

Lemma height_subtrees : forall {T} (tree : BinaryTree T),
  tree <> Nill T <-> height tree = 1 + maxn (height (Lst tree)) (height (Rst tree)).
Proof.
  by move => T; case.
Qed.

(* Count of BinaryTree T *)

Fixpoint count {T} (tree : BinaryTree T) : nat :=
    match tree with
    | Nill              => 0
    | Node _ Left _ Right => 1 + (count Left) + (count Right)
    end.

Eval compute in (height null).
Eval compute in (count null).

Eval compute in (height (@5)).
Eval compute in (count (@5)).

Eval compute in (height ((@3) -| 5 |- (@7))).
Eval compute in (count ((@3) -| 5 |- (@7))).

Eval compute in (height ((@3) -| 5 |- ((@6) -| 7 |- (@8)))).
Eval compute in (count ((@3) -| 5 |- ((@6) -| 7 |- (@8)))).

Lemma count_nill : forall {T}, count (Nill T) = 0.
Proof.
  done.
Qed.

Lemma count_empty_tree : forall {T} (tree : BinaryTree T),
  count tree = 0 <-> tree = Nill T.
Proof.
  by move => T; case.
Qed.

Lemma count_subtrees : forall {T} (tree : BinaryTree T),
  tree <> Nill T <-> count tree = 1 + count (Lst tree) + count (Rst tree).
Proof.
  by move => T; case.
Qed.

(* =================================================== *)
(* Connection between height and count of BinaryTree T *)
(* =================================================== *)

Theorem leq_height_count : forall {T} (tree : BinaryTree T),
  height tree <= count tree.
Proof.
  move => T; elim => [| _ _ Ltree iHl value Rtree iHr] /= //.

    rewrite (leq_add2l 1 _ (_ + _)).

  - suff: forall a b c d, (maxn a b <= maxn c d) 
          -> (maxn a b <= c + d).
    move => L1; apply: L1.

  - suff: forall a b c d, a <= c -> b <= d -> a + b <= c + d
          -> maxn a b <= maxn c d.
    move => L2; apply: L2.
    apply: iHl. apply: iHr.

    by apply: leq_add.

    (* first subgoal *)
    move => a b c d acH bdH H.
    case: (leqP b a) => abH.
    - rewrite maxnC maxnE subnKC => //.
      case: (leqP d c) => cdH.
      - rewrite maxnC maxnE subnKC => //.
      - rewrite maxnE subnKC.
        - apply: ltnW. apply: leq_ltn_trans.
          apply: acH. apply: cdH.
        - by apply: ltnW.
    - rewrite maxnE subnKC.
      case: (leqP d c) => cdH.
      - rewrite maxnC maxnE subnKC => //.
        apply: leq_trans. apply: bdH. 
        apply: cdH.
      - rewrite maxnE subnKC => //.
        - apply: ltnW => //.
        - apply: ltnW => //.

    (* Auxiliary lemma *)
    have: forall x y, maxn x y <= x + y.
    elim => [x | x iHx y] .
    - rewrite max0n => //.
    - case: y => [| y]; first
      rewrite maxn0 addn0 => //.
      - rewrite maxnSS -add1n -(add1n x)
        (leq_add2l 1 _ (_ + _)) addnS.
        by apply: leqW.

    move => leq_maxn_sum.

    (* second subgoal *)
    move => a b c d H.
    apply: leq_trans. apply: H. 
    apply: leq_maxn_sum.
Qed.

Ltac solve :=
  do ![try case: andP => //; case];
  try split => //; try done.

(* ============================================================ *)
(* ### ----- Canonical comparison and eqType for BynaryTree T.  *)
(* ============================================================ *)

Section EqTree.

Variables T : eqType.
Implicit Type t : BinaryTree T.

Fixpoint eqtree t1 t2 {struct t1} := 
  match t1, t2 with
  | Nill, Nill => true
  | Node P1 L1 v1 R1, Node P2 L2 v2 R2 =>
    (v1 == v2) && eqtree P1 P2 && eqtree L1 L2 && eqtree R1 R2
  | _, _ => false
  end.

Lemma eqtreeP : Equality.axiom eqtree.
Proof.
  move; elim => [| tp1 iHtp tl1 iHtl v1 tr1 iHtr] [| tp2 tl2 v2 tr2];
        do [by constructor | simpl].
  - case: andP.
    - case; case: andP => //; case.
      case: andP => //; case => eqv eqtp _ eqtl _ eqtr.
      constructor.
      case: iHtp eqtp => Htp _ //.
      case: iHtl eqtl => Htl _ //.
      case: iHtr eqtr => Htr _ //.
      case: eqP eqv => /= // Hv _.
      by rewrite Htp Htl Hv Htr.
  - move => H. constructor => H'. inversion H'.
     apply: H. solve.
    - case: iHtr H4 => //.
    - case: iHtl H2 => //.
    - case: eqP H3 => //.
    - case: iHtp H1 => //.
Qed.

Canonical tree_eqMixin := EqMixin eqtreeP.
Canonical tree_eqType := Eval hnf in EqType (BinaryTree T) tree_eqMixin.

Lemma eqtreeE : eqtree = eq_op.
Proof.
  elim: eqtree => //; do [by constructor].
Qed.

End EqTree.

Implicit Arguments eqtreeP [T x y].

Eval compute in (null == null).
Eval compute in (null == (@4) -| 5 |- (@6)).
Eval compute in ((@4) -| 5 |- (@6) == (@4) -| 5 |- (@6)).
Eval compute in ((@3) -| 5 |- (@6) == (@4) -| 5 |- (@6)).

(* ================== *)
(* Binary search tree *)
(* ================== *)

Fixpoint Is_cond (s : seq nat) (P : nat -> bool) : bool :=
  match s with 
  | [::]    => true
  | y :: ys => P y && Is_cond ys P 
  end.

Fixpoint Left_cond (tree : BinaryTree nat) : bool := 
  match tree with
  | Nill => true
  | Node _ Left value Right => Is_cond (nodes (Lst tree)) (fun y => y < value)
    && Left_cond Left && Left_cond Right
  end.

Fixpoint Right_cond (tree : BinaryTree nat) : bool := 
  match tree with
  | Nill => true
  | Node _ Left value Right => Is_cond (nodes (Rst tree)) (fun y => value < y)
    && Right_cond Left && Right_cond Right
  end.

Eval compute in (Left_cond (((@1) -| 2 |- (@3)) -| 4 |- (@ 6))).
Eval compute in (Left_cond (((@3) -| 2 |- (@1)) -| 4 |- (@ 6))).
Eval compute in (Right_cond (((@1) -| 2 |- (@3)) -| 4 |- (@ 6))).
Eval compute in (Right_cond (((@3) -| 2 |- (@1)) -| 4 |- (@ 6))).

Inductive BST : BinaryTree nat -> Prop :=
  | bst_nill : BST null
  | bst_node : forall tree, Left_cond tree -> Right_cond tree ->
    BST (Lst tree) -> BST (Rst tree) -> BST tree.

Lemma BST_Nill : BST null.
Proof.
  apply: bst_nill.
Qed.

Lemma BST_Combine : forall tp tl v tr,
  Left_cond (Node tp tl v tr) -> Right_cond (Node tp tl v tr) -> 
  BST tl -> BST tr -> BST (Node tp tl v tr).
Proof.
  move => tp tl value tr Lc Rc lH rH.
  by apply: bst_node.
Qed.

Lemma BST_One : forall y, BST (@ y).
Proof.
  move => y;
  apply: bst_node => //;
  do [apply: BST_Nill]. 
Qed.

Lemma BST_Example_1 : BST ((@3) -| 5 |- (@ 7)).
Proof.
  apply: bst_node => //;
  do [apply: BST_One].
Qed.

Lemma BST_Two_l : forall a b, b < a -> 
  BST ((@ b) -| a |- null).
Proof.
  move => a b cond.
  apply: bst_node => // /=.
  - solve.
  - apply: BST_One.
  - apply: BST_Nill.
Qed.

Lemma BST_Two_r : forall a b, a < b -> 
  BST (null -| a |- (@ b)).
Proof.
  move => a b cond.
  apply: bst_node => // /=.
  - solve.
  - apply: BST_Nill.
  - apply: BST_One.
Qed.

Lemma BST_Tree : forall a b c, b < a < c -> 
  BST ((@ b) -| a |- (@ c)).
Proof.
  move => a b c cond.
  apply: bst_node => /=.
  - solve.
    by case: andP cond => //; case.
  - solve.
    by case: andP cond => //; case.
  - apply: BST_One.
  - apply: BST_One.
Qed.

Lemma BST_Example_2 : BST ((null -| 3 |- (@ 4)) -| 5 |- (@ 7)).
Proof.
  by apply: bst_node => //;
  do [apply: BST_Two_r| apply: BST_One].
Qed.

(* ============= *)
(* Insert in BST *)
(* ============= *) 

Fixpoint BST_insert (value : nat) (tree : BinaryTree nat) : BinaryTree nat :=
    match tree with
    | Nill                => null -| value |- null
    | Node _ Left y Right =>
        if value < y
        then (BST_insert value Left) -| y |- Right
        else if y < value 
        then Left -| y |- (BST_insert value Right)
        else tree
    end. 

Notation "v >> t" := (BST_insert v t) (at level 43, left associativity).

Eval compute in (2 >> null).
Eval compute in (2 >> (@ 3)).
Eval compute in (2 >> (@ 1)).
Eval compute in (1 >> ((@ 2) -| 4 |- (@ 6))).
Eval compute in (3 >> ((@ 2) -| 4 |- (@ 6))).
Eval compute in (5 >> ((@ 2) -| 4 |- (@ 6))).
Eval compute in (7 >> ((@ 2) -| 4 |- (@ 6))).

Axiom Insert_cond : forall value tree, 
  nodes (value >> tree) = value :: (nodes tree).

Lemma Safety_Left_cond : forall tree y, Left_cond tree -> Left_cond (y >> tree).
Proof.
  elim => /= [y _ | tp _ tl iHtl z tr iHtr w H] //.
  - case: andP H => //; case; solve => condL lH _ rH _.
    case: (ltngtP w z) => cond /=; solve.
    - rewrite Insert_cond => /=; solve.
    - apply: iHtl lH.
    - apply: iHtr rH.
Qed.

Lemma Safety_Right_cond : forall tree y, Right_cond tree -> Right_cond (y >> tree).
Proof.
  elim => /= [y _ | tp _ tl iHtl z tr iHtr w H] //.
  - case: andP H => //; case; solve => condR lH _ rH _.
    case: (ltngtP w z) => cond /=; solve.
    - apply: iHtl lH.
    - apply: iHtr rH.
    - rewrite Insert_cond => /=.
      by solve; apply: ltnW.
Qed.

Theorem Safety_BST_insert : forall tree y, BST tree -> BST (y >> tree).
Proof.
  elim => /= [y _ | tp _ tl iHtl z tr iHtr w H] //.
  - apply: BST_One.
    inversion H.
    inversion H0; case: andP H6 => //; case.
    case: andP => //; case => condL lH _ rH _;
    inversion H1; case: andP H6 => //; case.
    case: andP => //; case => condR lH' _ rH' _.
    case: (ltngtP w z) => cond //.
    - apply: BST_Combine => /= //.
      - solve.
        - rewrite Insert_cond => /=; solve.
        - apply: Safety_Left_cond lH.
      - solve.
        apply: Safety_Right_cond lH'.
      - apply: iHtl H2.
    - apply: BST_Combine => /= //.
      - solve; apply: Safety_Left_cond rH.
      - solve.
        - apply: Safety_Right_cond rH'.
        - rewrite Insert_cond => /=.
          by solve; apply: ltnW.
      - apply: iHtr H3.
Qed.

(* ======================== *)
(* BST with bool definition *)
(* ======================== *)

Fixpoint BSTeq (tree : BinaryTree nat) : bool := 
  match tree with
  | Nill => true
  | Node _ Left value Right => 
    Left_cond tree && Right_cond tree &&
    BSTeq Left && BSTeq Right
  end.

Lemma BSTeq_Nill : BSTeq null.
Proof.
  done.
Qed.

Lemma BSTeq_Combine : forall tp tl v tr,
  Left_cond (Node tp tl v tr) -> Right_cond (Node tp tl v tr) -> 
  BSTeq tl -> BSTeq tr -> BSTeq (Node tp tl v tr).
Proof.
  move => /= tp tl value tr Lc Rc lH rH.
  case: andP => //; case.
  case: andP => //; case.
  by case: andP => //; case.
Qed.

Lemma BSTeq_One : forall y, BSTeq (null -| y |- null).
Proof.
  done.
Qed.

Lemma BSTeq_Example_1 : BSTeq ((@ 3) -| 5 |- (@ 7)).
Proof.
  done.
Qed.

Lemma BSTeq_Two_l : forall a b, b < a -> 
  BSTeq ((@ b) -| a |- null).
Proof.
  move => /= a b cond.
  solve.
Qed.

Lemma BSTeq_Two_r : forall a b, a < b -> 
  BSTeq (null -| a |- (@ b)).
Proof.
  move => /= a b cond; solve.
Qed.

Lemma BSTeq_Tree : forall a b c, b < a < c -> 
  BSTeq ((@ b) -| a |- (@ c)).
Proof.
  move => /= a b c cond; solve.
  - by case: andP cond => //; case.
  - by case: andP cond => //; case.
Qed.

Lemma BSTeq_Example_2 : BSTeq ((null -| 3 |- (@ 4)) -| 5 |- (@ 7)).
Proof.
  done.
Qed.

Theorem Safety_BSTeq_insert : forall tree y, BSTeq tree -> BSTeq (y >> tree).
Proof.
  elim => /= [y _ | tp _ tl iHtl z tr iHtr w] //.
  case: andP => //; case.
  case: andP => //; case.
  case: andP => //; case => condL condR _ lH _ rH _.
  case: andP condR => //; case.
  case: andP => //; case => condtR LH _ RH _.
  case: andP condL => //; case.
  case: andP => //; case => condtL LH' _ RH' _.
  case: (ltngtP w z) => cond /= //. 
  - rewrite Insert_cond /=; solve.
    - apply: iHtl lH.
    - apply: Safety_Right_cond LH.
    - apply: Safety_Left_cond LH'.
  - rewrite Insert_cond /=; solve.
    - apply: iHtr rH.
    - apply: Safety_Right_cond RH.
    - apply: Safety_Left_cond RH'.
  solve.
Qed.

(* =========================== *)
(* Reflect betwen BST and BST' *)
(* =========================== *)

Theorem bstP (tree : BinaryTree nat) : reflect (BST tree) (BSTeq tree).
Proof.
  elim: tree => [| tp _ tl iHtl z tr iHtr] /=.
  - constructor; apply: BST_Nill.
  - case: andP.
    - case; case: andP => //; case.
      case; case: andP => //. case => condL condR _ lH _ rH.
      constructor.
      apply: BST_Combine => //.
      - by case: iHtl lH.
      - by case: iHtr rH.
    - move => H1. constructor. move => H2.
      apply: H1. inversion H2.
      case: andP => //; case.
      - solve. move: H3.
        rewrite Rst_elem. case: iHtr => //.
      - case: andP => //; case.
        - split => //. move: H1.
          rewrite Lst_elem; case: iHtl => //.
        - split => //.
Qed.

Lemma BST_Example_3 : BST (((@2) -| 3 |- (@ 4)) -| 5 |- ((@6) -| 7 |- (@ 9))).
Proof.
  by apply: bstP.
Qed.

(* =========================== *)
(* ### ----- Tree with parents *)
(* =========================== *)

Definition Pst {T} (tree : BinaryTree T) : BinaryTree T :=
  match tree with
  | Nill => Nill T
  | Node Parent _ _ _ => Parent
  end.

Fixpoint Parent_cond {T: eqType} (tree : BinaryTree T) : bool := 
  match tree with
  | Nill => true
  | Node P L _ R => 
    (if P == Nill T then true
     else (Lst P == tree) || (Rst P == tree)) &&
    (if L == Nill T then true
     else Pst L == tree) &&
    (if R == Nill T then true
     else Pst R == tree) &&
    Parent_cond P && Parent_cond L && Parent_cond R
  end.

(* =========================== *)
(* ### ------ BST with parents *)
(* =========================== *)

Inductive BSTwP : BinaryTree nat -> Prop :=
  | wP_constr : forall tree, BST tree -> Parent_cond tree -> BSTwP tree.

Definition BSTwPeq (tree : BinaryTree nat) : bool :=
  BSTeq tree && Parent_cond tree.

Lemma bstwpP (tree : BinaryTree nat) : reflect (BSTwP tree) (BSTwPeq tree).
Proof.
  unfold BSTwPeq.
  case: andP => cond; constructor.
  - constructor; case: cond => //;
    case: bstP => //.
  - move => H; apply: cond.
    case: H => t bst_cond parent_cond. split => //.
    by case: bstP.
Qed.

Fixpoint BSTwP_insert (value : nat) (tree : BinaryTree nat) : BinaryTree nat :=
    match tree with
    | Nill                => Node (null -| 5 |- null) null value null
    | Node _ Left y Right =>
        if value < y
        then (BSTwP_insert value Left) -| y |- Right
        else if y < value 
        then Left -| y |- (BSTwP_insert value Right)
        else tree
    end.

Notation "v >>wP t" := (BSTwP_insert v t) (at level 43, left associativity).

Eval compute in (2 >>wP null).
Eval compute in (2 >>wP (@ 3)).
Eval compute in (2 >>wP (@ 1)).
Eval compute in (1 >>wP ((@ 2) -| 4 |- (@ 6))).
Eval compute in (3 >>wP ((@ 2) -| 4 |- (@ 6))).
Eval compute in (5 >>wP ((@ 2) -| 4 |- (@ 6))).
Eval compute in (7 >>wP ((@ 2) -| 4 |- (@ 6))).

Axiom Insert_cond_wP : forall value tree, 
  nodes (value >>wP tree) = value :: (nodes tree).

Lemma bst_insertP (tree : BinaryTree nat) (y : nat) : 
  reflect (BSTeq (y >> tree)) (BSTeq (y >>wP tree)).
Proof.
  elim: tree y => [| tp iHtp tl iHtl v tr iHtr y] /=; 
        do [by constructor|].
  case: (ltngtP y v) => cond /= //.
  - case: andP => //.
    case: andP => //.
    case: andP => //.
    case: andP => //.
    case: andP => //.
    case: andP => //.
    case: andP => //.
    case: andP => //.
    by constructor.
    constructor => /=.
    case: n. solve.
    case: p4 => _.
    case: iHtl => //.
Admitted.


(* =========================== *)
(* ### ------------ Splay tree *)
(* =========================== *)



















