import OMAReductions.R_Erdos142_erdos_142_variants_lower_R3_H2_R1
import Mathlib

-- Reduction Erdos142.erdos_142.variants.lower.R3.H2.R1.H2.R3 of step Erdos142.erdos_142.variants.lower.R3.H2.R1.H2
-- Credit: @Carson1903

/-!
# Sublinear power-law progression increment split by k = 4 and k >= 5

We reduce the abstract sublinear potential descent step `R3.H2.R1.H2` to concrete
power-law density increments `F(x) = A * x ^ β` (with `0 < β < 1`) along arithmetic
progressions `a + (i - 1) * q`:
- `H1`: arithmetic-progression density increment for 4-term progressions (`k = 4`),
  corresponding to the Gowers `U^3` / quadratic Fourier regime;
- `H2`: arithmetic-progression density increment for `k >= 5`, corresponding to the
  higher-order `U^(k-1)` nilsequence regime;
- `H3`: the analytic sublinear comparison showing `A * x ^ β <= x / 2 + D` for `x >= 2`.

The glue verifies that pulling back a k-AP-free set along a positive-step arithmetic
progression preserves k-AP-freeness and transfers the progression increment to the
abstract potential `F(x) = A * x ^ β`.
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R3_H2_R1_H2_R3

open Filter Real

/-- Arithmetic-progression density increment with power-law potential for k = 4. -/
def H1 : Prop :=
  ∃ (β A T Cmin : ℝ), 0 < β ∧ β < 1 ∧ 0 < A ∧
    let p := fun (N : ℕ) (S : Finset ℕ) => max 2 (log (2 * (N : ℝ) / (S.card : ℝ)))
    ∀ C ≥ Cmin, ∀ (N : ℕ) (S : Finset ℕ),
      1 < N → S.Nonempty → S ⊆ Finset.Icc 1 N →
      (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < 4, a + i * d ∈ S) →
      T < p N S → A * (p N S) ^ β + C ≤ log (log (N : ℝ)) →
      ∃ (a q M : ℕ), 0 < q ∧ 1 < M ∧
        (∀ i ∈ Finset.Icc 1 M, a + (i - 1) * q ∈ Finset.Icc 1 N) ∧
        let U := (Finset.Icc 1 M).filter (fun i => a + (i - 1) * q ∈ S)
        U.Nonempty ∧ A * (p M U) ^ β + C ≤ log (log (M : ℝ)) ∧ p M U + 1 ≤ p N S

/-- Arithmetic-progression density increment with power-law potential for all k >= 5. -/
def H2 : Prop :=
  ∀ k : ℕ, 5 ≤ k → ∃ (β A T Cmin : ℝ), 0 < β ∧ β < 1 ∧ 0 < A ∧
    let p := fun (N : ℕ) (S : Finset ℕ) => max 2 (log (2 * (N : ℝ) / (S.card : ℝ)))
    ∀ C ≥ Cmin, ∀ (N : ℕ) (S : Finset ℕ),
      1 < N → S.Nonempty → S ⊆ Finset.Icc 1 N →
      (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S) →
      T < p N S → A * (p N S) ^ β + C ≤ log (log (N : ℝ)) →
      ∃ (a q M : ℕ), 0 < q ∧ 1 < M ∧
        (∀ i ∈ Finset.Icc 1 M, a + (i - 1) * q ∈ Finset.Icc 1 N) ∧
        let U := (Finset.Icc 1 M).filter (fun i => a + (i - 1) * q ∈ S)
        U.Nonempty ∧ A * (p M U) ^ β + C ≤ log (log (M : ℝ)) ∧ p M U + 1 ≤ p N S

/-- Any sublinear power A * x ^ β (0 < β < 1) is bounded by x / 2 + D on [2, ∞). -/
def H3 : Prop :=
  ∀ (β A : ℝ), 0 < β → β < 1 → 0 < A →
    ∃ D : ℝ, ∀ x : ℝ, 2 ≤ x → A * x ^ β ≤ x / 2 + D

lemma pullback_ap_free {k a q M : ℕ} {S : Finset ℕ}
    (hk : 1 ≤ k) (hq : 0 < q)
    (hfree : ¬ ∃ b d : ℕ, 0 < d ∧ ∀ i < k, b + i * d ∈ S) :
    ¬ ∃ b d : ℕ, 0 < d ∧ ∀ i < k,
      b + i * d ∈ (Finset.Icc 1 M).filter (fun j => a + (j - 1) * q ∈ S) := by
  rintro ⟨b, d, hd, hAP⟩
  have hb_mem : b ∈ Finset.Icc 1 M := by
    simpa only [zero_mul, add_zero] using (Finset.mem_filter.mp (hAP 0 (by omega))).1
  have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb_mem).1
  refine hfree ⟨a + (b - 1) * q, d * q, Nat.mul_pos hd hq, fun i hi => ?_⟩
  have hmem := (Finset.mem_filter.mp (hAP i hi)).2
  have heq : b + i * d - 1 = b - 1 + i * d := by omega
  rw [heq] at hmem
  simpa only [add_mul, Nat.add_assoc, Nat.mul_assoc] using hmem

lemma lift_power_increment {k : ℕ} (hk : 4 ≤ k)
    (h3 : H3)
    (hinc : ∃ (β A T Cmin : ℝ), 0 < β ∧ β < 1 ∧ 0 < A ∧
      let p := fun (N : ℕ) (S : Finset ℕ) => max 2 (log (2 * (N : ℝ) / (S.card : ℝ)))
      ∀ C ≥ Cmin, ∀ (N : ℕ) (S : Finset ℕ),
        1 < N → S.Nonempty → S ⊆ Finset.Icc 1 N →
        (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S) →
        T < p N S → A * (p N S) ^ β + C ≤ log (log (N : ℝ)) →
        ∃ (a q M : ℕ), 0 < q ∧ 1 < M ∧
          (∀ i ∈ Finset.Icc 1 M, a + (i - 1) * q ∈ Finset.Icc 1 N) ∧
          let U := (Finset.Icc 1 M).filter (fun i => a + (i - 1) * q ∈ S)
          U.Nonempty ∧ A * (p M U) ^ β + C ≤ log (log (M : ℝ)) ∧ p M U + 1 ≤ p N S) :
    ∃ (F : ℝ → ℝ) (T D Cmin : ℝ),
      (∀ x ≥ 2, 0 ≤ F x ∧ F x ≤ x / 2 + D) ∧
      let p := fun (N : ℕ) (S : Finset ℕ) => max 2 (log (2 * (N : ℝ) / (S.card : ℝ)))
      let valid := fun (N : ℕ) (S : Finset ℕ) => 1 < N ∧ S.Nonempty ∧ S ⊆ Finset.Icc 1 N ∧
        ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S
      ∀ C ≥ Cmin, ∀ (N : ℕ) (S : Finset ℕ), valid N S → T < p N S →
        F (p N S) + C ≤ log (log (N : ℝ)) → ∃ (M : ℕ) (B : Finset ℕ),
          valid M B ∧ F (p M B) + C ≤ log (log (M : ℝ)) ∧ p M B + 1 ≤ p N S := by
  obtain ⟨β, A, T, Cmin, hβ0, hβ1, hA, hstep⟩ := hinc
  obtain ⟨D, hD⟩ := h3 β A hβ0 hβ1 hA
  refine ⟨fun x => A * x ^ β, T, D, Cmin, ?_, ?_⟩
  · intro x hx
    exact ⟨mul_nonneg hA.le (Real.rpow_nonneg (by linarith) β), hD x hx⟩
  · dsimp only
    intro C hC N S ⟨hN, hne, hsub, hfree⟩ hT hbud
    obtain ⟨a, q, M, hq, hM, _, hUne, hUbud, hUdrop⟩ :=
      hstep C hC N S hN hne hsub hfree hT hbud
    refine ⟨M, (Finset.Icc 1 M).filter (fun i => a + (i - 1) * q ∈ S), ?_, hUbud, hUdrop⟩
    exact ⟨hM, hUne, Finset.filter_subset _ _, pullback_ap_free (by omega) hq hfree⟩

theorem main : H1 → H2 → H3 → OMA.R_Erdos142_erdos_142_variants_lower_R3_H2_R1.H2 := by
  intro h1 h2 h3 k hk
  rcases eq_or_lt_of_le hk with rfl | h5
  · exact lift_power_increment le_rfl h3 h1
  · exact lift_power_increment hk h3 (h2 k h5)

end OMA.R_Erdos142_erdos_142_variants_lower_R3_H2_R1_H2_R3
