Require Import Arith. 
Open Scope nat_scope. 

Definition key := nat.

Inductive tree (V : Type) : Type :=
| E
| T (l : tree V) (k : key) (v : V) (r : tree V).
Arguments E {V}.
Arguments T {V}. 

(* insert k v t is the map containing all the bindings of t along with a binding of k to v. *)
Fixpoint insert {V : Type} (x : key) (v : V) (t : tree V) : tree V :=
  match t with
  | E => T E x v E
  | T l y v' r => if x <? y then T (insert x v l) y v' r
                 else if y <? x then T l y v' (insert x v r)
                      else T l x v r
  end. 

(* So, let's formalize the BST invariant. Here's one way to do so. 
   First, we define a helper ForallT to express that idea that a predicate
   holds at every node of a tree: *)
Fixpoint ForallT {V : Type} (P: key -> V -> Prop) (t: tree V) : Prop :=
    match t with
    | E => True
    | T l k v r => P k v /\ ForallT P l /\ ForallT P r
    end.

Inductive BST {V : Type} : tree V -> Prop :=
| BST_E : BST E
| BST_T : forall l x v r,
    ForallT (fun y _ => y < x) l ->
    ForallT (fun y _ => x < y) r ->
    BST l ->
    BST r ->
    BST (T l x v r). 

(* [ Base Case: t = E ] ⊢ BST(insert(k, v, E)) *)
Lemma base_case_BST: forall (V : Type) (k : key) (v : V),
    BST (insert k v E).
Proof.
    intros V k v.
    simpl. constructor. 
Admitted. 

(* (1.2) [ Inductive Step: Assume ∀ subtrees u of t, BST(u) ⇒ BST(insert(k', v', u)) ] ⊢ BST(insert(k, v, T l x v' r)) *)
Lemma inductive_BST: forall (V : Type) (k x : key) (v v' : V) (l r t: tree V),
    BST l -> ForallT (fun y _ => y < x) l ->
    BST r -> ForallT (fun y _ => x < y) r ->
    BST (T l x v' r) ->
    BST (insert k v (T l x v' r)).
Proof.
    intros. 
Admitted.

(* └── [Inductive Hypothesis: BST l → BST (insert k v l)]
and [∀ y in insert k v l, y < x] |- BST (T (insert k v l) x v' r) *)
Lemma ind1_help_BST: forall (V : Type) (k x : key) (v v' : V) (l r t: tree V),
    BST l -> ForallT (fun y _ => y < x) l ->
    BST r -> ForallT (fun y _ => x < y) r ->
    BST (T l x v' r) ->
    k < x ->
    (BST l -> BST (insert k v l)) ->
    ForallT (fun y _ => y < x) (insert k v l) ->
    BST (T (insert k v l) x v' r).
Proof.
    intros. 
Admitted.

Lemma inductive1_BST: forall (V : Type) (k x : key) (v v' : V) (l r t: tree V),
    BST l -> ForallT (fun y _ => y < x) l ->
    BST r -> ForallT (fun y _ => x < y) r ->
    BST (T l x v' r) ->
    k < x ->
    BST (insert k v (T l x v' r)).
Proof.
    intros.
Admitted.

(* ├── Case: k > x:
│      └── [Inductive Hypothesis: BST r → BST (insert k v r)]
│             and [∀ y in insert k v r, y > x] |- BST (T l x v' (insert k v r)) *)
Lemma ind2_help_BST: forall (V : Type) (k x : key) (v v' : V) (l r t: tree V),
    BST l -> ForallT (fun y _ => y < x) l ->
    BST r -> ForallT (fun y _ => x < y) r ->
    BST (T l x v' r) ->
    x < k ->
    (BST r -> BST (insert k v r)) ->
    ForallT (fun y _ => x < y) (insert k v r) ->
    BST (T l x v' (insert k v r)).
Proof.
    intros. 
Admitted.


Lemma inductive2_BST: forall (V : Type) (k x : key) (v v' : V) (l r t: tree V),
    BST l -> ForallT (fun y _ => y < x) l ->
    BST r -> ForallT (fun y _ => x < y) r ->
    BST (T l x v' r) ->
    x < k ->
    BST (insert k v (T l x v' r)).
Proof.
    intros.
Admitted.

(* BST is preserved under the change of a value *)
Lemma ind3_help_BST: forall (V : Type) (k: key) (v v': V) (l r t: tree V),
    BST (T l k v r) -> BST (insert k v' (T l k v r)).
Proof.
    intros.
Admitted.

Lemma inductive3_BST: forall (V : Type) (k x : key) (v v' : V) (l r t: tree V),
    BST l -> ForallT (fun y _ => y < x) l ->
    BST r -> ForallT (fun y _ => x < y) r ->
    BST (T l x v' r) ->
    x = k ->
    BST (insert k v (T l x v' r)).
Proof.
    intros.
Admitted.

Theorem insert_BST : forall (V : Type) (k : key) (v : V) (t : tree V),
    BST t -> BST (insert k v t).
Proof.
    intros.
Admitted. 
