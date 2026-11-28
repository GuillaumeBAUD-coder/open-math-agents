import OMAReductions.R_BoundedBurnsideProblem_bounded_burnside_problem_R1

/-!
The positive cube-free words give an infinite subset of the concrete free
Burnside quotient. The word-separation input is the specialization to positive
words and exponent 667 of Atkarskaya–Rips–Tent, Theorem 8.1 and Remark 8.8.
The existence input is the binary cube-free word theorem.

Source: https://arxiv.org/pdf/2303.15997#page=57
-/

namespace OMA.R_BoundedBurnsideProblem_bounded_burnside_problem_R1_H1_R1

/-- There is a positive binary cube-free word of every finite length. -/
def H1 : Prop :=
  ∀ n : ℕ, ∃ w : List (Fin 2), w.length = n ∧
    ∀ (l u r : List (Fin 2)), u ≠ [] → w ≠ l ++ u ++ u ++ u ++ r

/-- Distinct positive binary cube-free words remain distinct in B(2,667). -/
def H2 : Prop :=
  let N := Subgroup.normalClosure {y : FreeGroup (Fin 2) |
    ∃ x : FreeGroup (Fin 2), y = x ^ 667}
  ∀ a b : List (Fin 2),
    (∀ (l u r : List (Fin 2)), u ≠ [] → a ≠ l ++ u ++ u ++ u ++ r) →
    (∀ (l u r : List (Fin 2)), u ≠ [] → b ≠ l ++ u ++ u ++ u ++ r) →
    QuotientGroup.mk' N (a.map FreeGroup.of).prod =
      QuotientGroup.mk' N (b.map FreeGroup.of).prod → a = b

theorem main : H1 → H2 → OMA.R_BoundedBurnsideProblem_bounded_burnside_problem_R1.H1 := by
  intro hwords hsep
  unfold H1 at hwords
  choose w hlen hfree using hwords
  let N := Subgroup.normalClosure {y : FreeGroup (Fin 2) |
    ∃ x : FreeGroup (Fin 2), y = x ^ 667}
  change Infinite (FreeGroup (Fin 2) ⧸ N)
  refine Infinite.of_injective (fun n : ℕ => QuotientGroup.mk' N ((w n).map FreeGroup.of).prod) ?_
  intro i j hij
  have hw : w i = w j := hsep (w i) (w j) (hfree i) (hfree j) hij
  exact (hlen i).symm.trans ((congrArg List.length hw).trans (hlen j))

end OMA.R_BoundedBurnsideProblem_bounded_burnside_problem_R1_H1_R1
