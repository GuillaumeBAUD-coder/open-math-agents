import FormalConjectures.Wikipedia.CollatzConjecture

-- Reduction CollatzConjecture.collatz_conjecture.R1 of Collatz conjecture
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

/-!
# Collatz = no divergent trajectory + no nontrivial cycle

The classical decomposition of the Collatz conjecture (see e.g. Lagarias,
*The 3x+1 problem and its generalizations*, 1985): a positive starting value
fails to reach 1 only if its trajectory is unbounded, or if it is bounded and
hence eventually periodic, falling into a cycle other than 1 → 4 → 2 → 1.

* `H1` (no divergent trajectories): every trajectory of a positive integer is bounded.
* `H2` (no nontrivial cycles): every positive periodic point lies on the trivial cycle `{1, 2, 4}`.

Both hypotheses are genuinely open. The proof of `main` is pigeonhole on a
bounded trajectory followed by a walk around the trivial cycle.
-/

namespace OMA.R_CollatzConjecture_collatz_conjecture_R1

open CollatzConjecture

/-- No divergent trajectories: the trajectory of every positive integer is bounded. -/
def H1 : Prop :=
  ∀ n : ℕ, 0 < n → ∃ B : ℕ, ∀ m : ℕ, collatzStep^[m] n ≤ B

/-- No nontrivial cycles: a positive integer that returns to itself lies on `1 → 4 → 2 → 1`. -/
def H2 : Prop :=
  ∀ n k : ℕ, 0 < n → 0 < k → collatzStep^[k] n = n → n = 1 ∨ n = 2 ∨ n = 4

lemma step_pos {n : ℕ} (hn : 0 < n) : 0 < collatzStep n := by
  unfold collatzStep
  split_ifs with h
  · obtain ⟨r, hr⟩ := h
    omega
  · omega

lemma iterate_pos {n : ℕ} (hn : 0 < n) (m : ℕ) : 0 < collatzStep^[m] n := by
  induction m generalizing n with
  | zero => simpa using hn
  | succ m ih =>
    rw [Function.iterate_succ_apply]
    exact ih (step_pos hn)

lemma step_two : collatzStep 2 = 1 := by decide

lemma step_four : collatzStep 4 = 2 := by decide

/-- A bounded trajectory revisits some value. -/
lemma exists_repeat {n B : ℕ} (hB : ∀ m : ℕ, collatzStep^[m] n ≤ B) :
    ∃ i j : ℕ, i < j ∧ collatzStep^[i] n = collatzStep^[j] n := by
  have hmaps : ∀ m ∈ Finset.range (B + 2), collatzStep^[m] n ∈ Finset.range (B + 1) := by
    intro m _
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hB m))
  have hcard : (Finset.range (B + 1)).card < (Finset.range (B + 2)).card := by simp
  obtain ⟨a, ha, b, hb, hab, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  rcases lt_or_gt_of_ne hab with h | h
  · exact ⟨a, b, h, heq⟩
  · exact ⟨b, a, h, heq.symm⟩

theorem main : H1 → H2 → type_of% @CollatzConjecture.collatz_conjecture := by
  intro h1 h2 n hn
  obtain ⟨B, hB⟩ := h1 n hn
  obtain ⟨i, j, hij, heq⟩ := exists_repeat hB
  set x := collatzStep^[i] n with hx
  have hxpos : 0 < x := iterate_pos hn i
  have hcyc : collatzStep^[j - i] x = x := by
    rw [hx, ← Function.iterate_add_apply, Nat.sub_add_cancel hij.le]
    exact heq.symm
  have hcases := h2 x (j - i) hxpos (by omega) hcyc
  rcases hcases with h | h | h
  · exact ⟨i, by rw [← hx, h]⟩
  · refine ⟨1 + i, ?_⟩
    rw [Function.iterate_add_apply, ← hx, h]
    exact step_two
  · refine ⟨2 + i, ?_⟩
    rw [Function.iterate_add_apply, ← hx, h]
    simp [step_four, step_two]

end OMA.R_CollatzConjecture_collatz_conjecture_R1
