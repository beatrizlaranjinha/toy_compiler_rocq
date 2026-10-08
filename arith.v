(** Note on Rocq versions: if the [Require Import] section below fails saying
    something like [library XXX is required from root Stdlib and has not been
    found in the loadpath!], then it probably means you are using an older
    version of Rocq. Try changing [Stdlib] everywhere into [Rocq]. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From Stdlib Require Import String.

Import ListNotations.

(** Some words of advice/hints before you even get started on the
    assignment:

    - When you have an hypothesis of the form [H : P /\ Q], you want to
      be able to manipulate, individually, [P] and [Q]. Use [destruct
      H] to split the former hypothesis into two individual hypotheses
      [H1 : P] and [H2 : Q].

    - When you have an hypothesis of the form [H: exists x, P], you know
      indeed that there is an [x] that satisfies property [P]. Use
      [destruct H] to introduce just argument in your context.

    - When faced with a goal of the form [P /\ Q], you want to focus
      first on the proof of [P] and then on the proof of [Q]. In other
      words, you want to generate two cases, one for the proof of [P]
      the other for the proof of [Q]. Use [split] to instruct Rocq to
      generate such cases.

    - When faced with a goal of the form [P <-> Q], this stands for the
      equivalence of [P] with [Q]. This is exactly as if you were
      trying to prove two different lemmas: first that [P -> Q], and
      then that [Q -> P]. Use [split] to instruct Rocq to generate such
      cases.

    - When faced with a goal of the form [exists x, P], you want to find
      out some witness (in other words, a value) that satisfies
      [P]. When you find out such a value, lets call it [y], you just
      need to do [exists y] and the proof will continue with goal [P] where
      every occurrence of [x] has been replaced by [y].

    - From time to time, you find yourself with an hypothesis [H : P]
      where you know [P] is a false statement, i.e., a
      contradiction. That is fine, sometimes this just stands for an
      unreachable point in your implementation or proof. In that case,
      use [discriminate H] in order to instruct Rocq to exploit such a
      contradiction and finish the proof (remember: with a
      contradiction as an hypothesis everything can be proved, so the
      proof finishes immediately as soon as you are able to convince
      Rocq [H] is indeed a contradiction).

    - Do not forget that you can use other Lemmas during your
      proofs. In fact, for some of the exercises, you are supposed to
      use Lemmas that you have already proved. Also, you should be
      able to use some auxiliary Lemmas from the Rocq Standard
      Library. The [Search] command can help you find useful Lemmas
      already proved (either your own or from Rocq). *)

Inductive op : Type :=
| OAdd
| OSub.

Inductive expr : Type := 
| EConst: Z -> expr (*trandormar inteiros em expressões *)
| EBinOp : expr -> op -> expr -> expr. (*expressão operado expressão numa expressão*)

Definition eval_op (n1: Z) (o: op) (n2: Z): Z :=
  match o with
  | OAdd => n1 + n2
  | OSub => n1 - n2
  end.

Inductive red_expr : expr -> expr -> Prop := 
| Red_Beta : forall (n1 n2 n : Z) (o : op),
                    n = eval_op n1 o n2 ->
                     red_expr (EBinOp (EConst n1) o (EConst n2)) (EConst n)
| Red_Left o e2 : forall e1 e1' : expr, (*inferencia de tipo*) 
                    red_expr e1 e1' ->
                        red_expr (EBinOp e1 o e2) (EBinOp e1' o e2)
| Red_Right o n1 : forall e2 e2' : expr,
                    red_expr e2 e2'->
                        red_expr (EBinOp (EConst n1) o e2) (EBinOp (EConst n1) o e2').


Inductive red_expr_star : expr -> Z -> Prop := 
| Red_Star_Zero n : red_expr_star (EConst n) n
| Red_Star_Step : forall (e' e : expr) (n : Z),
                    red_expr e e' ->
                        red_expr_star e' n ->
                                red_expr_star e n.


Inductive asm : Type :=
| APush : Z -> asm (* coloca n no topo *)
| AAdd : asm (* tira os 2 n , soma e coloca na stack *)
| ASub : asm. (* tira os 2 n, subtrai e coloca na stack *)

(*last in first out*)

Definition stack : Type := list Z.

Inductive outcome : Type :=
| ORes : stack -> outcome
| OAbort : outcome.


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

Fixpoint red_asm_star (s: stack) (c: code) : outcome :=  (* c => list of machine instructions *)
 match c with 
| [] => ORes s
| (a :: c') =>
  match red_asm s a with 
  | OAbort => OAbort
  | ORes s' => red_asm_star s' c'
  end
end.



Definition compile_op (o: op) : asm :=
  match o with
  | OAdd => AAdd
  | OSub => ASub
  end.

Fixpoint compile (e: expr) : code :=  (* code é uma lista de instruções *)
  match e with
  | EConst n => [APush n]
  | EBinOp e1 o e2 => compile e1 ++ compile e2 ++ [ compile_op o]
  end.

  (* Se a constante n reduz, em zero ou mais passos, para m, então n = m *)
Lemma red_expr_star_const_inv : forall n m: Z,
    red_expr_star (EConst n) m -> n = m.
    intros n m.
    intros h.
    inversion h.
    - reflexivity.
    - inversion H.
Qed. (*duvida*)



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
    -auto. (*unfold red_asm. reflexivity.*)
    -auto.
Qed.


Lemma comm_red_asm_append : forall (c1 c2: code) (s0 s1: stack),
    red_asm_star s0 c1 = ORes s1 ->
    red_asm_star s0 (c1 ++ c2) = red_asm_star s1 c2.
intros c1 c2.
induction c1. (*colocar primeiro as variaveis que não mudam*)
- intros s0 s1 h. simpl. inversion h. reflexivity.
- intros s0 s1 h. simpl. destruct (red_asm s0 a) eqn:IHred. (*pode dar ORes s' ou OAbort*)
  + apply IHc1. 
    simpl in h.
    rewrite IHred in h.
    assumption. (*igual a hipotese h*)
  + simpl in h. 
    rewrite IHred in h.
    discriminate h.
Qed.


(* exericio 9 *)
Lemma compile_correct_gen : forall (e: expr) (n: Z) (s: stack),
    red_expr_star e n ->
    red_asm_star s (compile e) = ORes (n :: s).
Proof. (*procurar lemma para não fazer indução em todos os casos*)
  intros e.
  induction e.
  (* case 1: e = Econst *)
  - intros n s h. simpl. apply red_expr_star_const_inv in h. rewrite h. reflexivity.
  (* case 2: EBinOp e1 o e2 *)
  - intros n s h. simpl. apply red_expr_star_middle in h. 
    destruct h as (n1 & n2 & h1 & h2 & hn). (*->*)
    apply (IHe1 n1 s) in h1. 
    apply (IHe2 n2 (n1 :: s)) in h2. (* aplicar n2 a stack já existente *) 
    rewrite (comm_red_asm_append _ _ _ (n1 :: s) h1).  (*compile e1 sobre a stack inicial s, o resultado é: n1 :: s*)
    rewrite (comm_red_asm_append _ _ (n1 :: s) (n2 :: n1 :: s) h2).
    simpl. rewrite red_asm_compile_op. rewrite hn. reflexivity.
Qed.



(* https://softwarefoundations.cis.upenn.edu/lf-current/Imp.html *) (* try Exercise: 3 stars, standard (stack_compiler_correct) *)
Lemma compile_correct : forall (e: expr) (n: Z),
    red_expr_star e n -> 
    red_asm_star [] (compile e) = ORes [n]. (* queremos começar com a stack vazia *)
Proof.
  intros e n h.
  apply (compile_correct_gen e n []) in h.
  assumption.
Qed.