import FormalConjectures.Wikipedia.TarskiExponentialFunctionProblem

-- Reduction TarskiExponentialFunctionProblem.isDecidable_completeTheory_real_orderedField.R1 of Tarski's decidability theorem
-- Credit: @LordMike
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Decidability of the real ordered field from completeness of real closed fields

Following A. Tarski, *A decision method for elementary algebra and geometry* (1951), in the
form found in textbooks (e.g. D. Marker, *Model Theory: An Introduction*, Corollary 3.3.16 and
Lemma 2.2.8). Let `rcf` be the usual axiom system of real closed ordered fields in the language
`(+, *, -, 0, 1, ≤)`: the field axioms, the axioms of a linear order, compatibility of `≤` with
`+` and `*`, existence of square roots of nonnegative elements, and a root for every monic
polynomial of odd degree. The project format allows no auxiliary definitions, so the explicit
set `rcf` is written out, identically, inside `H1`, `H3` and `H4`. It is built from concrete terms
only (no choice), so that `H3` is a genuine computability statement.

* `H1` (Tarski, the deep input): the theory `rcf` is complete. This is the consequence of
  Tarski–Seidenberg quantifier elimination for real closed fields.
* `H2` (a complete theory with a recursive set of axioms is decidable; this is the
  effective form of Gödel's completeness theorem, stated here for the language of ordered
  rings only).
* `H3` (elementary computability): the set of axioms `rcf` is recursive.
* `H4` (elementary): the real numbers are a model of `rcf`.

`main`: by `H1` and `H4` a sentence holds in `ℝ` iff it is a consequence of `rcf`, so the complete
theory of `ℝ` and `rcf` have the same consequences, and `rcf` is decidable by `H2` and `H3`.
-/

namespace OMA.R_TarskiExponentialFunctionProblem_isDecidable_completeTheory_real_orderedField_R1

open FirstOrder FirstOrder.Language

/-- Tarski: the theory `rcf` of real closed ordered fields is complete. The axioms are: the field
axioms; the axioms of a linear order; `x ≤ y → x + z ≤ y + z`; `0 ≤ x → 0 ≤ y → 0 ≤ x * y`;
`0 ≤ x → ∃ y, y * y = x`; and for every odd `n = 2k + 1` the sentence
`∀ a₀ … aₙ₋₁, ∃ x, a₀ + x (a₁ + x (⋯ + x (aₙ₋₁ + x * 1))) = 0`
(every monic polynomial of odd degree has a root, written in Horner form). -/
def H1 : Prop :=
  let r := fun (n : ℕ) (t : Language.ring.Term (Empty ⊕ Fin n)) =>
    (LHom.sumInl : Language.ring →ᴸ Language.ring.sum Language.order).onTerm t
  let rcf : (Language.ring.sum Language.order).Theory :=
    (LHom.sumInl : Language.ring →ᴸ Language.ring.sum Language.order).onTheory Theory.field ∪
    (Language.ring.sum Language.order).linearOrderTheory ∪
    {∀' ∀' ∀' ((r 3 (&0)).le (r 3 (&1)) ⟹ (r 3 (&0 + &2)).le (r 3 (&1 + &2))),
     ∀' ∀' ((r 2 0).le (r 2 (&0)) ⟹ ((r 2 0).le (r 2 (&1)) ⟹ (r 2 0).le (r 2 (&0 * &1)))),
     ∀' ((r 1 0).le (r 1 (&0)) ⟹ ∃' ((r 2 (&1 * &1)) =' (r 2 (&0))))} ∪
    Set.range fun k : ℕ => (BoundedFormula.alls (∃' ((r (2 * k + 1 + 1)
      ((List.finRange (2 * k + 1)).foldr (fun i t => Term.var (Sum.inr i.castSucc) +
        Term.var (Sum.inr (Fin.last (2 * k + 1))) * t) 1)) =' (r (2 * k + 1 + 1) 0))) :
      (Language.ring.sum Language.order).Sentence)
  rcf.IsComplete

/-- A complete theory with a recursive set of axioms is decidable (language of ordered rings). -/
def H2 : Prop :=
  ∀ T : (Language.ring.sum Language.order).Theory, T.IsRecursive → T.IsComplete → T.IsDecidable

/-- The axiom system `rcf` (the same set of sentences as in the first hypothesis) is a recursive
set of sentences. -/
def H3 : Prop :=
  let r := fun (n : ℕ) (t : Language.ring.Term (Empty ⊕ Fin n)) =>
    (LHom.sumInl : Language.ring →ᴸ Language.ring.sum Language.order).onTerm t
  let rcf : (Language.ring.sum Language.order).Theory :=
    (LHom.sumInl : Language.ring →ᴸ Language.ring.sum Language.order).onTheory Theory.field ∪
    (Language.ring.sum Language.order).linearOrderTheory ∪
    {∀' ∀' ∀' ((r 3 (&0)).le (r 3 (&1)) ⟹ (r 3 (&0 + &2)).le (r 3 (&1 + &2))),
     ∀' ∀' ((r 2 0).le (r 2 (&0)) ⟹ ((r 2 0).le (r 2 (&1)) ⟹ (r 2 0).le (r 2 (&0 * &1)))),
     ∀' ((r 1 0).le (r 1 (&0)) ⟹ ∃' ((r 2 (&1 * &1)) =' (r 2 (&0))))} ∪
    Set.range fun k : ℕ => (BoundedFormula.alls (∃' ((r (2 * k + 1 + 1)
      ((List.finRange (2 * k + 1)).foldr (fun i t => Term.var (Sum.inr i.castSucc) +
        Term.var (Sum.inr (Fin.last (2 * k + 1))) * t) 1)) =' (r (2 * k + 1 + 1) 0))) :
      (Language.ring.sum Language.order).Sentence)
  rcf.IsRecursive

/-- The real numbers are a model of `rcf` (the same set of sentences as in the first
hypothesis): they form a real closed ordered field. -/
def H4 : Prop :=
  let r := fun (n : ℕ) (t : Language.ring.Term (Empty ⊕ Fin n)) =>
    (LHom.sumInl : Language.ring →ᴸ Language.ring.sum Language.order).onTerm t
  let rcf : (Language.ring.sum Language.order).Theory :=
    (LHom.sumInl : Language.ring →ᴸ Language.ring.sum Language.order).onTheory Theory.field ∪
    (Language.ring.sum Language.order).linearOrderTheory ∪
    {∀' ∀' ∀' ((r 3 (&0)).le (r 3 (&1)) ⟹ (r 3 (&0 + &2)).le (r 3 (&1 + &2))),
     ∀' ∀' ((r 2 0).le (r 2 (&0)) ⟹ ((r 2 0).le (r 2 (&1)) ⟹ (r 2 0).le (r 2 (&0 * &1)))),
     ∀' ((r 1 0).le (r 1 (&0)) ⟹ ∃' ((r 2 (&1 * &1)) =' (r 2 (&0))))} ∪
    Set.range fun k : ℕ => (BoundedFormula.alls (∃' ((r (2 * k + 1 + 1)
      ((List.finRange (2 * k + 1)).foldr (fun i t => Term.var (Sum.inr i.castSucc) +
        Term.var (Sum.inr (Fin.last (2 * k + 1))) * t) 1)) =' (r (2 * k + 1 + 1) 0))) :
      (Language.ring.sum Language.order).Sentence)
  (ℝ : Type) ⊨ rcf

/-- A decidable complete theory true in `ℝ` has the same consequences as the complete theory of
`ℝ`, which is therefore decidable. -/
lemma key (T : (Language.ring.sum Language.order).Theory) (hc : T.IsComplete)
    (hd : T.IsDecidable) (hR : (ℝ : Type) ⊨ T) :
    ((Language.ring.sum Language.order).completeTheory ℝ).IsDecidable := by
  refine (Theory.isDecidable_congr fun φ => ?_).2 hd
  constructor
  · intro h
    have hφ : (ℝ : Type) ⊨ φ := h.realize_sentence ℝ
    rcases hc.2 φ with h' | h'
    · exact h'
    · exact absurd hφ (by simpa using h'.realize_sentence ℝ)
  · intro h
    exact Theory.models_sentence_of_mem (mem_completeTheory.2 (h.realize_sentence ℝ))

theorem main : H1 → H2 → H3 → H4 →
    type_of% @TarskiExponentialFunctionProblem.isDecidable_completeTheory_real_orderedField :=
  fun h1 h2 h3 h4 => key _ h1 (h2 _ h3 h1) h4

end OMA.R_TarskiExponentialFunctionProblem_isDecidable_completeTheory_real_orderedField_R1
