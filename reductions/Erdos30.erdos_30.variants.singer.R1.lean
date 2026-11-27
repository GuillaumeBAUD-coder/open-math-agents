import FormalConjectures.ErdosProblems.«30»

-- Reduction Erdos30.erdos_30.variants.singer.R1 of Erdős Problem 30 — singer
-- Credit: @ldy985
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The lower bound h(N) ≥ (1 - o(1)) √N needs two independent ingredients:
--   H1  primes in short intervals: for every δ > 0 and all large n there is a prime in (n, (1+δ)n].
--       This is the analytic part; it follows from the prime number theorem (or from p_{n+1}/p_n → 1).
--   H2  a dense Sidon set for every prime: p - 1 elements inside {1, …, p(p-1)}.
--       This is the algebraic part (Ruzsa's construction from a primitive root mod p and the
--       Chinese remainder theorem; Singer's and Bose–Chowla's constructions give the same density).
-- `main` is the interpolation: for large N pick a prime p with (1 - ε)√N < p - 1 and p ≤ √N.

namespace OMA.R_Erdos30_erdos_30_variants_singer_R1

def H1 : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∃ p : ℕ, p.Prime ∧ n < p ∧ (p : ℝ) ≤ (1 + δ) * (n : ℝ)

def H2 : Prop :=
  ∀ p : ℕ, p.Prime → ∃ A : Finset ℕ,
    A ⊆ Finset.Icc 1 (p * (p - 1)) ∧ IsSidon (A : Set ℕ) ∧ A.card = p - 1

lemma card_le_h {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hS : IsSidon (A : Set ℕ)) :
    A.card ≤ Erdos30.h N := by
  show A.card ≤ Finset.maxSidonSubsetCard (Finset.Icc 1 N)
  unfold Finset.maxSidonSubsetCard
  exact Finset.le_sup (f := Finset.card)
    (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hA, hS⟩)

theorem main : H1 → H2 → type_of% @Erdos30.erdos_30.variants.singer := by
  intro h1 h2 ε hε
  rw [Filter.eventually_atTop]
  have hδpos : 0 < ε / 2 := by positivity
  obtain ⟨n₀, hn₀⟩ := h1 (ε / 2) hδpos
  have hS0 : 0 ≤ max ((1 + ε / 2) * (n₀ : ℝ)) (2 / ε) := le_max_of_le_right (by positivity)
  refine ⟨⌈(max ((1 + ε / 2) * (n₀ : ℝ)) (2 / ε)) ^ 2⌉₊, fun N hN => ?_⟩
  have hNS : (max ((1 + ε / 2) * (n₀ : ℝ)) (2 / ε)) ^ 2 ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have hs0 : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have hSs : max ((1 + ε / 2) * (n₀ : ℝ)) (2 / ε) ≤ Real.sqrt (N : ℝ) := by
    have := Real.sqrt_le_sqrt hNS
    rwa [Real.sqrt_sq hS0] at this
  have hss : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = N := Real.mul_self_sqrt (Nat.cast_nonneg N)
  have h1δ : 0 < 1 + ε / 2 := by linarith
  have hq0 : 0 ≤ Real.sqrt (N : ℝ) / (1 + ε / 2) := div_nonneg hs0 h1δ.le
  have hn_le : ((⌊Real.sqrt (N : ℝ) / (1 + ε / 2)⌋₊ : ℕ) : ℝ) ≤ Real.sqrt (N : ℝ) / (1 + ε / 2) :=
    Nat.floor_le hq0
  have hn_lt : Real.sqrt (N : ℝ) / (1 + ε / 2) <
      ((⌊Real.sqrt (N : ℝ) / (1 + ε / 2)⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  have hn₀n : n₀ ≤ ⌊Real.sqrt (N : ℝ) / (1 + ε / 2)⌋₊ := by
    apply Nat.le_floor
    rw [le_div_iff₀ h1δ]
    calc (n₀ : ℝ) * (1 + ε / 2) = (1 + ε / 2) * n₀ := mul_comm _ _
      _ ≤ max ((1 + ε / 2) * (n₀ : ℝ)) (2 / ε) := le_max_left _ _
      _ ≤ Real.sqrt (N : ℝ) := hSs
  obtain ⟨p, hp, hnp, hpn⟩ := hn₀ _ hn₀n
  obtain ⟨A, hA, hSid, hcard⟩ := h2 p hp
  have hps : (p : ℝ) ≤ Real.sqrt (N : ℝ) := by
    calc (p : ℝ) ≤ (1 + ε / 2) * ((⌊Real.sqrt (N : ℝ) / (1 + ε / 2)⌋₊ : ℕ) : ℝ) := hpn
      _ ≤ (1 + ε / 2) * (Real.sqrt (N : ℝ) / (1 + ε / 2)) :=
          mul_le_mul_of_nonneg_left hn_le h1δ.le
      _ = Real.sqrt (N : ℝ) := by field_simp
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hpp : p * p ≤ N := by
    have h : (p : ℝ) * p ≤ N := by
      calc (p : ℝ) * p ≤ Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) :=
            mul_le_mul hps hps hp0 hs0
        _ = N := hss
    exact_mod_cast h
  have hpN : p * (p - 1) ≤ N := (Nat.mul_le_mul_left p (Nat.sub_le p 1)).trans hpp
  have hAN : A ⊆ Finset.Icc 1 N := hA.trans (Finset.Icc_subset_Icc_right hpN)
  have hh := card_le_h hAN hSid
  rw [hcard] at hh
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hpn1 : ((⌊Real.sqrt (N : ℝ) / (1 + ε / 2)⌋₊ : ℕ) : ℝ) + 1 ≤ p := by
    exact_mod_cast hnp
  have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub hp1]
    simp
  have hεs : 2 / ε ≤ Real.sqrt (N : ℝ) := (le_max_right _ _).trans hSs
  have h2εs : 2 ≤ Real.sqrt (N : ℝ) * ε := by rwa [div_le_iff₀ hε] at hεs
  have hdiv : (1 - ε / 2) * Real.sqrt (N : ℝ) ≤ Real.sqrt (N : ℝ) / (1 + ε / 2) := by
    rw [le_div_iff₀ h1δ]
    nlinarith [mul_nonneg hs0 (sq_nonneg (ε / 2))]
  have key : (1 - ε) * Real.sqrt (N : ℝ) ≤ ((p - 1 : ℕ) : ℝ) := by
    rw [hcast]
    have e : (1 - ε) * Real.sqrt (N : ℝ) =
        (1 - ε / 2) * Real.sqrt (N : ℝ) - Real.sqrt (N : ℝ) * ε / 2 := by ring
    linarith
  calc (1 - ε) * Real.sqrt (N : ℝ) ≤ ((p - 1 : ℕ) : ℝ) := key
    _ ≤ (Erdos30.h N : ℝ) := by exact_mod_cast hh

end OMA.R_Erdos30_erdos_30_variants_singer_R1
