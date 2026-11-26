import FormalConjectures.ErdosProblems.«30»

-- Reduction Erdos30.erdos_30.variants.O_one.R1 of Erdős Problem 30 — O one
-- Credit: @shipmas

namespace OMA.R_Erdos30_erdos_30_variants_O_one_R1

open Erdos30

/-- A Sidon set with k marks requires an interval of length at least k² − ck. -/
def H1 : Prop :=
  ∃ c : ℕ, ∀ (N : ℕ) (A : Finset ℕ), A ⊆ Finset.Icc 1 N → IsSidon (A : Set ℕ) →
    A.card ^ 2 ≤ N + c * A.card

/-- For each k one can construct k Sidon marks in an interval of length k² + dk. -/
def H2 : Prop :=
  ∃ d : ℕ, ∀ k : ℕ, ∃ A : Finset ℕ,
    A ⊆ Finset.Icc 1 (k ^ 2 + d * k) ∧ IsSidon (A : Set ℕ) ∧ A.card = k

lemma card_le_max {A : Finset ℕ} {N : ℕ}
    (hA : A ⊆ Finset.Icc 1 N) (hS : IsSidon (A : Set ℕ)) : A.card ≤ h N := by
  unfold h Finset.maxSidonSubsetCard
  exact Finset.le_sup (f := Finset.card) (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hA, hS⟩)

lemma max_sq_bound (h₁ : H1) :
    ∃ c : ℕ, ∀ N : ℕ, (h N) ^ 2 ≤ N + c * h N := by
  obtain ⟨c, hc⟩ := h₁
  refine ⟨c, fun N ↦ ?_⟩
  obtain ⟨A, hA, heq⟩ := Finset.exists_mem_eq_sup
    ((Finset.Icc 1 N).powerset.filter fun B : Finset ℕ ↦ IsSidon (B : Set ℕ))
    ⟨∅, by simp [IsSidon]⟩ Finset.card
  simp only [Finset.mem_filter, Finset.mem_powerset] at hA
  change h N = A.card at heq
  rw [heq]
  exact hc N A hA.1 hA.2

lemma next_card_bound (h₂ : H2) :
    ∃ d : ℕ, ∀ N : ℕ, N < (h N + 1) ^ 2 + d * (h N + 1) := by
  obtain ⟨d, hd⟩ := h₂
  refine ⟨d, fun N ↦ ?_⟩
  obtain ⟨A, hA, hS, hcard⟩ := hd (h N + 1)
  by_contra! hlen
  have hsub : A ⊆ Finset.Icc 1 N := by
    intro x hx
    obtain ⟨hx₁, hx₂⟩ := Finset.mem_Icc.mp (hA hx)
    exact Finset.mem_Icc.mpr ⟨hx₁, hx₂.trans hlen⟩
  have hle := card_le_max hsub hS
  omega

theorem main : H1 → H2 → type_of% @Erdos30.erdos_30.variants.O_one := by
  intro h₁ h₂
  obtain ⟨c, hc⟩ := max_sq_bound h₁
  obtain ⟨d, hd⟩ := next_card_bound h₂
  apply Asymptotics.IsBigO.of_bound ((c : ℝ) + d + 1)
  apply Filter.Eventually.of_forall
  intro N
  simp only [Real.norm_eq_abs, abs_one, mul_one]
  have hu : (h N : ℝ) ^ 2 ≤ (N : ℝ) + (c : ℝ) * h N := by exact_mod_cast hc N
  have hl : (N : ℝ) < ((h N : ℝ) + 1) ^ 2 + (d : ℝ) * (h N + 1 : ℝ) := by
    exact_mod_cast hd N
  have hs := Real.sqrt_nonneg (N : ℝ)
  have hs₂ := Real.sq_sqrt (show (0 : ℝ) ≤ N by positivity)
  have hc₀ : 0 ≤ (c : ℝ) := by positivity
  have hd₀ : 0 ≤ (d : ℝ) := by positivity
  have hu' : (h N : ℝ) ≤ (N : ℝ).sqrt + c := by
    by_contra! hh
    have hpos : 0 < (h N : ℝ) := by linarith
    have hdiff : (N : ℝ).sqrt ≤ h N := by linarith
    nlinarith [mul_pos (sub_pos.mpr hh) hpos, mul_nonneg (sub_nonneg.mpr hdiff) hs]
  have hl' : (N : ℝ).sqrt ≤ (h N : ℝ) + 1 + d := by
    calc
      (N : ℝ).sqrt ≤ Real.sqrt (((h N : ℝ) + 1 + d) ^ 2) := by
        apply Real.sqrt_le_sqrt
        nlinarith [mul_nonneg hd₀ (show 0 ≤ (h N : ℝ) + 1 by positivity), sq_nonneg (d : ℝ)]
      _ = _ := Real.sqrt_sq (by positivity)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end OMA.R_Erdos30_erdos_30_variants_O_one_R1
