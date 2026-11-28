import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2

-- Reduction Erdos142.erdos_142.variants.lower.R2.H1.R2 of step Erdos142.erdos_142.variants.lower.R2.H1
-- Credit: @b-ionut-r

/-!
# Erdős 142, step R2.H1, by covering a block with few shifts

This is the Ramsey route planned by @stochastic-parrot-ftw (team note #172258), complementing
the density route R2.H1.R1. Let A live on the blocks (4 * 4^j, 5 * 4^j] with divergent reciprocal
sum, and let B_j in [1, 4^j] be the shifted slice of A in block j.

* H1: for infinitely many j, few translates of B_j (at most q_j = (⌈log 4^j⌉ + 1)^4) cover the
  interval [4^j + 1, 2 * 4^j]. Otherwise the covering lemma of R1.H2.R2.H2 bounds |B_j| by
  2 * 4^j * log 4^j / q_j, which is summable after dividing by 4^j, against the divergence.
* H2: for large N, every coloring of [1, N] with (⌈log N⌉ + 1)^4 colors has a monochromatic
  3-term progression. This follows from Kelley–Meka by pigeonhole on the color classes.
* H3: the same for every length k ≥ 4. This is the open core, the same statement as step
  R1.H2.R2.H1.

Given a covering of [4^j + 1, 2 * 4^j] by translates shifts t + B_j, color y in [1, 4^j] by a t
with y + 4^j in shifts t + B_j. A monochromatic progression y + i * d of color t gives the
progression b + i * d in B_j, hence 4 * 4^j + b + i * d in A.
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R2

open Filter

/-- Infinitely many block slices are covered by polylogarithmically many translates. -/
def H1 : Prop :=
  ∀ A : Set ℕ, (∀ x ∈ A, ∃ j : ℕ, 4 * 4 ^ j < x ∧ x ≤ 5 * 4 ^ j) →
    ¬ Summable (A.indicator (fun n : ℕ ↦ (n : ℝ)⁻¹)) →
    ∀ J : ℕ, ∃ j ≥ J, ∃ shifts : Fin ((⌈Real.log ((4 ^ j : ℕ) : ℝ)⌉₊ + 1) ^ 4) → ℕ,
      ∀ x ∈ Finset.Icc 1 (4 ^ j), ∃ t, ∃ b, b ∈ Finset.Icc 1 (4 ^ j) ∧ 4 * 4 ^ j + b ∈ A ∧
        x + 4 ^ j = shifts t + b

/-- Polylogarithmic colorings of long intervals have monochromatic 3-term progressions. -/
def H2 : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ c : ℕ → Fin ((⌈Real.log (N : ℝ)⌉₊ + 1) ^ 4), ∃ a d : ℕ, 0 < d ∧
    ∀ i < 3, a + i * d ∈ Finset.Icc 1 N ∧ c (a + i * d) = c a

/-- The same holds for every progression length at least four. -/
def H3 : Prop :=
  ∀ k : ℕ, 4 ≤ k → ∀ᶠ N : ℕ in atTop,
    ∀ c : ℕ → Fin ((⌈Real.log (N : ℝ)⌉₊ + 1) ^ 4), ∃ a d : ℕ, 0 < d ∧
      ∀ i < k, a + i * d ∈ Finset.Icc 1 N ∧ c (a + i * d) = c a

theorem main : H1 → H2 → H3 → OMA.R_Erdos142_erdos_142_variants_lower_R2.H1 := by
  classical
  intro h1 h2 h3 A hA hns k hk
  have hev : ∀ᶠ N : ℕ in atTop, ∀ c : ℕ → Fin ((⌈Real.log (N : ℝ)⌉₊ + 1) ^ 4),
      ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ Finset.Icc 1 N ∧ c (a + i * d) = c a := by
    rcases eq_or_lt_of_le hk with rfl | hk4
    · exact h2
    · exact h3 k hk4
  obtain ⟨J, hJ⟩ := eventually_atTop.1 hev
  obtain ⟨j, hj, shifts, hcov⟩ := h1 A hA hns J
  let c : ℕ → Fin ((⌈Real.log ((4 ^ j : ℕ) : ℝ)⌉₊ + 1) ^ 4) := fun y =>
    if hy : y ∈ Finset.Icc 1 (4 ^ j) then Classical.choose (hcov y hy) else ⟨0, by positivity⟩
  obtain ⟨a, d, hd, hm⟩ := hJ (4 ^ j) (hj.trans (Nat.lt_pow_self (by norm_num)).le) c
  have key : ∀ i < k, ∃ b, 4 * 4 ^ j + b ∈ A ∧ a + i * d + 4 ^ j = shifts (c a) + b := by
    intro i hi
    obtain ⟨hy, hc⟩ := hm i hi
    obtain ⟨b, -, hbA, hb⟩ := Classical.choose_spec (hcov _ hy)
    refine ⟨b, hbA, ?_⟩
    rw [← hc, show c (a + i * d) = Classical.choose (hcov _ hy) from dif_pos hy]
    exact hb
  obtain ⟨b0, -, hb0⟩ := key 0 (by omega)
  refine ⟨4 * 4 ^ j + b0, d, hd, fun i hi => ?_⟩
  obtain ⟨b, hbA, hb⟩ := key i hi
  simp only [zero_mul, add_zero] at hb0
  generalize i * d = e at hb ⊢
  rwa [show 4 * 4 ^ j + b0 + e = 4 * 4 ^ j + b by omega]

end OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R2
