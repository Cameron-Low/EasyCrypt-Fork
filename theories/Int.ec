require import Logic.

import why3 "int" "Int" 
  (* Il y a un bug dans ecScope il refuse d'avoir deux operateurs avec des 
     types different et la meme syntaxe *)
  op "prefix -" as "[-]".

theory Abs.

  import why3 "int" "Abs"
    op "abs" as "`|_|".

end Abs.
export Abs.

theory Triangle.
  lemma nosmt triangle_inequality (x y z:int):
     `| x - y | <= `| x - z | + `| y - z |
  by [].
end Triangle.

theory Extrema.
  op min (a b:int) = if (a < b) then a else b.

  lemma nosmt min_is_lb a b:
    min a b <= a /\
    min a b <= b
  by [].

  lemma nosmt min_is_glb x a b:
    x <= a => x <= b =>
    x <= min a b
  by [].

  lemma nosmt min_is_extremum a b:
    min a b = a \/ min a b = b
  by [].

(* This is much more satisfying: it defines the notion,
   and proves that it exists and is unique by giving it a
   functional definition. Still, the above definition
   is---probably---more usable.
   Note that the following could be used for iterated versions,
   for example on sets, with a proof that folding the binary min
   over the set fulfills the axioms. *)
(*op min: int -> int -> int.
  axiom min_is_lb: forall a b, min a b <= a /\ min a b <= b.
  axiom min_is_glb: forall x a b, x <= a => x <= b => x <= min a b.
  lemma min_is_extremum: forall a b, min a b = a \/ min a b = b.

  lemma min_def: forall a b,
    min a b = if (a < b) then a else b. *)

  op max (a b:int) = if (a < b) then b else a.

  lemma nosmt max_is_ub a b:
    a <= max a b /\
    b <= max a b
  by [].

  lemma nosmt max_is_lub x a b:
    a <= x => b <= x =>
    max a b <= x
  by [].

  lemma nosmt max_is_extremum a b:
    max a b = a \/ max a b = b
  by [].
end Extrema.
export Extrema.

theory EuclDiv.
  import why3 "int" "EuclideanDivision"
    op "div" as "/";
    op "mod" as "%%".
end EuclDiv.
export EuclDiv.

theory Induction.
  axiom nosmt induction (p:int -> bool):
    (p 0) =>
    (forall i, 0 <= i => p i => p (i + 1)) =>
    (forall i, 0 <= i => p i).

  lemma nosmt strongInduction (p:int -> bool):
    (forall j, 0 <= j => (forall k, 0 <= k < j => p k) => p j) =>
    (forall i, 0 <= i => p i).
  proof strict.
  by intros hyp i iVal;
     apply (induction (lambda i, forall k, 0 <= k <= i => p k) _ _ i); smt.
  qed.
end Induction.

(* Not sure we should use this one *)
theory Power.
  import why3 "int" "Power"
    op "power" as "^".

  lemma Power_pos (x n:int): 0 <= n => 0 < x => 0 < x ^ n.
  proof.
  by intros n_pos x_pos; elim/Induction.induction n=> //; smt.
  qed.
end Power.
export Power.

