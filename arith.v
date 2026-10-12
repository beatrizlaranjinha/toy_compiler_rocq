

From Stdlib Require Import ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From Stdlib Require Import String.

Import ListNotations.

Inductive op : Type :=
| OAdd
| OSub.

Inductive expr : Type := 
| EConst: Z -> expr (* represents an integer as an expression. *)
| EBinOp : expr -> op -> expr -> expr. (* two expressions using an operator. *)

(* Eealuates an arithmetic operation on two integers. *)
Definition eval_op (n1: Z) (o: op) (n2: Z): Z :=
  match o with
  | OAdd => n1 + n2
  | OSub => n1 - n2
  end.


(* single-step reduction *)
Inductive red_expr : expr -> expr -> Prop := 
| Red_Beta : forall (n1 n2 n : Z) (o : op),
                    n = eval_op n1 o n2 ->
                     red_expr (EBinOp (EConst n1) o (EConst n2)) (EConst n)
| Red_Left o e2 : forall e1 e1' : expr, 
                    red_expr e1 e1' ->
                        red_expr (EBinOp e1 o e2) (EBinOp e1' o e2)
| Red_Right o n1 : forall e2 e2' : expr,
                    red_expr e2 e2'->
                        red_expr (EBinOp (EConst n1) o e2) (EBinOp (EConst n1) o e2').


(* reduces an expression in zero or more steps. *)
Inductive red_expr_star : expr -> Z -> Prop := 
| Red_Star_Zero n : red_expr_star (EConst n) n
| Red_Star_Step : forall (e' e : expr) (n : Z),
                    red_expr e e' ->
                        red_expr_star e' n ->
                                red_expr_star e n.

(*instructions for a stack machine LIFO *)
Inductive asm : Type :=
| APush : Z -> asm (* pushes an integer onto the stack. *)
| AAdd : asm (* pops two on top and pushes their sum. *)
| ASub : asm. 

Definition stack : Type := list Z.

Inductive outcome : Type :=
| ORes : stack -> outcome
| OAbort : outcome.


(* machine instruction. *)
Definition red_asm (stack: stack) (a: asm) : outcome := 
match a with
  | APush n => ORes (n :: stack)
  | AAdd =>
    match stack with  
    | n1 :: n2 :: s => ORes ((n2 + n1) % Z :: s)
    | _ => OAbort
    end
  | ASub =>
    match stack with
    | n1 :: n2 :: s => ORes ((n2 - n1) % Z :: s)
    | _ => OAbort
    end
  end.


Definition code : Type := list asm.


(* executes a list of instructions, stop if an error. *)
Fixpoint red_asm_star (s: stack) (c: code) : outcome :=  (* c => list of machine instructions *)
 match c with 
| [] => ORes s
| (a :: c') =>
  match red_asm s a with 
  | OAbort => OAbort
  | ORes s' => red_asm_star s' c'
  end
end.


(* translates arithmetic operators into machine instructions. *)
Definition compile_op (o: op) : asm :=
  match o with
  | OAdd => AAdd
  | OSub => ASub
  end.

(* compiles an expression into a list of machine instructions. *)
Fixpoint compile (e: expr) : code :=  
  match e with
  | EConst n => [APush n]
  | EBinOp e1 o e2 => compile e1 ++ compile e2 ++ [ compile_op o]
  end.

(* Exercise 6: A constant that evaluates to m must be equal to m. *)
Lemma red_expr_star_const_inv : forall n m: Z,
    red_expr_star (EConst n) m -> n = m.
    intros n m.
    intros h.
    inversion h.
    (* case 1: m = m *)
    - reflexivity.
    (* case 2: n = m *)
    - inversion H.
Qed. 


(* A [Parameter] definition in Rocq works like an axiom: some result
   that you can use without proving it. *)
Parameter red_expr_star_middle : forall e1 e2 n op,
    red_expr_star (EBinOp e1 op e2) n ->
    exists n1 n2, red_expr_star e1 n1 /\ red_expr_star e2 n2 /\
             n = eval_op n1 op n2.


Lemma red_asm_compile_op : forall (o: op) (n1 n2: Z) (s: stack),
    red_asm (n2 :: n1 :: s) (compile_op o) = ORes (eval_op n1 o n2 :: s).
    intros o n1 n2 s.
    induction o.
    (* case 1: OAdd *)
    -auto. (*unfold red_asm. reflexivity.*)
    (* cade 2: OSub *)
    -auto.
Qed.


(* exericio 8*)
Lemma comm_red_asm_append : forall (c1 c2: code) (s0 s1: stack),
    red_asm_star s0 c1 = ORes s1 ->
    red_asm_star s0 (c1 ++ c2) = red_asm_star s1 c2.
intros c1 c2.
induction c1. (* induction on the first list of instructions *)
(* case 1: c1 = [] *)
- intros s0 s1 h. simpl. inversion h. reflexivity.
(* case 2: a :: c1 *)
- intros s0 s1 h. simpl. destruct (red_asm s0 a) eqn:IHred. (* ORes s' ou OAbort*)
  (* case 3: red_asm s0 a = ORes s *)
  + apply IHc1. 
    simpl in h.
    rewrite IHred in h.
    assumption. (*the same as h*)
  (* case 4 : red_asm s0 a = OAbort *)
  + simpl in h. 
    rewrite IHred in h. (* h : OAbort = ORes s1 , this is impossible so lets use discriminate *)
    discriminate h. 
Qed.


(* exericio 9 *)
Lemma compile_correct_gen : forall (e: expr) (n: Z) (s: stack),
    red_expr_star e n ->
    red_asm_star s (compile e) = ORes (n :: s).
Proof. (*não fazer indução em todos os casos*)
  intros e.
  induction e.
  (* case 1: e = Econst *)
  - intros n s h. simpl. apply red_expr_star_const_inv in h. rewrite h. reflexivity.
  (* case 2: EBinOp e1 o e2 *)
  - intros n s h. simpl. apply red_expr_star_middle in h. 
    destruct h as (n1 & n2 & h1 & h2 & hn). (*->*)

    apply (IHe1 n1 s) in h1.  (* compiling e1 produces n1 :: s. *)
    apply (IHe2 n2 (n1 :: s)) in h2. (* compiling e2 produces n2 :: n1 :: s. *)
    rewrite (comm_red_asm_append _ _ _ (n1 :: s) h1).  (* execute compile e1 first. *)
    rewrite (comm_red_asm_append _ _ (n1 :: s) (n2 :: n1 :: s) h2). (* execute compile e2. *)
    simpl. rewrite red_asm_compile_op. rewrite hn. reflexivity.
Qed.

(* Exercise 10: Compiler correctness for an initially empty stack.*)
Lemma compile_correct : forall (e: expr) (n: Z),
    red_expr_star e n -> 
    red_asm_star [] (compile e) = ORes [n]. 
Proof.
  intros e n h.
  apply (compile_correct_gen e n []) in h.
  assumption.
Qed.