import FormalConjectures.ErdosProblems.«504»

/-!
# Reduction of Erdős 504 (Erdős–Szekeres 1960) to its two published halves

- `H1` (known, Szekeres 1941): for every `t > 0` and `ε > 0` there are `2^t` points all of whose
  angles are below `π(1 - 1/t) + ε` (verbatim `erdos_504.variants.szekeres_upper`).
- `H2` (known, Erdős–Szekeres 1960): any `2^n` points, `n ≥ 3`, contain an angle above
  `π(1 - 1/n)` (verbatim `erdos_504.variants.erdos_szekeres_1960`).
- `main` identifies the supremum: `H2` puts `π(1 - 1/n)` in the set, `H1` bounds the set above.
-/
-- Credit: @senamakel

namespace OMA.R_Erdos504_erdos_504_R1

open Real EuclideanGeometry

-- Szekeres (1941), upper-bound construction.
def H1 : Prop :=
  ∀ {t : ℕ}, 0 < t → ∀ {ε : ℝ}, 0 < ε →
    ∃ S : Finset ℂ, S.card = 2 ^ t ∧
      ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → r ≠ q →
        EuclideanGeometry.angle p q r < (1 - 1 / (t : ℝ)) * π + ε

-- Erdős–Szekeres (1960), lower bound.
def H2 : Prop :=
  ∀ {n : ℕ}, 3 ≤ n → ∀ (S : Finset ℂ), S.card = 2 ^ n →
    ∃ p ∈ S, ∃ q ∈ S, ∃ r ∈ S, p ≠ q ∧ r ≠ q ∧
      (1 - 1 / (n : ℝ)) * π < EuclideanGeometry.angle p q r

theorem main : H1 → H2 → type_of% @Erdos504.erdos_504 := by
  intro h1 h2 n hn
  unfold Erdos504.minimaxAngle
  set a0 : ℝ := (1 - 1 / (n : ℝ)) * π with ha0
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hinv : 1 / (n : ℝ) ≤ 1 := by
    rw [div_le_one hn0]; exact_mod_cast (by omega : 1 ≤ n)
  have hinv0 : 0 < 1 / (n : ℝ) := by positivity
  have ha0nn : 0 ≤ a0 := mul_nonneg (by linarith) pi_pos.le
  have ha0le : a0 ≤ π := by nlinarith [pi_pos]
  have hbdd : BddAbove {α : ℝ | α ∈ Set.Icc 0 π ∧
      ∀ S : Finset ℂ, S.card = 2 ^ n →
        ∃ x ∈ S, ∃ z ∈ S, ∃ y ∈ S, x ≠ z ∧ y ≠ z ∧ x ≠ y ∧
          α ≤ EuclideanGeometry.angle x z y} := ⟨π, fun α hα => hα.1.2⟩
  have hmem : a0 ∈ {α : ℝ | α ∈ Set.Icc 0 π ∧
      ∀ S : Finset ℂ, S.card = 2 ^ n →
        ∃ x ∈ S, ∃ z ∈ S, ∃ y ∈ S, x ≠ z ∧ y ≠ z ∧ x ≠ y ∧
          α ≤ EuclideanGeometry.angle x z y} := by
    refine ⟨⟨ha0nn, ha0le⟩, fun S hS => ?_⟩
    obtain ⟨p, hp, q, hq, r, hr, hpq, hrq, hlt⟩ := h2 hn S hS
    refine ⟨p, hp, q, hq, r, hr, hpq, hrq, ?_, hlt.le⟩
    rintro rfl
    rw [EuclideanGeometry.angle_self_of_ne hpq] at hlt
    linarith
  apply le_antisymm
  · apply csSup_le ⟨a0, hmem⟩
    rintro α ⟨_, hα⟩
    by_contra hlt
    replace hlt := lt_of_not_ge hlt
    obtain ⟨S, hS, hang⟩ := h1 (t := n) (by omega) (ε := (α - a0) / 2) (by linarith)
    obtain ⟨x, hx, z, hz, y, hy, hxz, hyz, _, hle⟩ := hα S hS
    have := hang x hx z hz y hy hxz hyz
    linarith
  · exact le_csSup hbdd hmem

end OMA.R_Erdos504_erdos_504_R1
