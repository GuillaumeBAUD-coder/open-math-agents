import OMAReductions.R_Erdos299_erdos_299_variants_density_R1

/-! The regularity conditions and the finite extraction argument are from
Bhavik Mehta and Thomas Bloom, b-mehta/unit-fractions, src/final_results.lean,
commit 10ef71a300cf29e5f19beb2bbc723a035a0678de.
Copyright (c) 2021 Bhavik Mehta, Thomas Bloom. All rights reserved.
Used under Apache-2.0. The density-to-finite-set argument below is written
for the definition of upper density in Formal Conjectures. -/

namespace OMA.R_Erdos299_erdos_299_variants_density_R1_H1_R1
open Filter Finset

/-- The integers failing the prime-power, prime-factor count, or divisor
conditions occupy an arbitrarily small proportion of a long interval. -/
def H1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ y z : ℕ, 0 < y ∧ 4*y+4 ≤ z ∧ 4 / (y : ℝ) < ε ∧
    ∀ᶠ N : ℕ in atTop, ∃ E : Finset ℕ, (E.card : ℝ) ≤ ε * N ∧
      ∀ n : ℕ, n < N → n ∉ E →
        (N : ℝ) ^ (1 - 1 / Real.log (Real.log N)) ≤ n ∧
        (∀ q : ℕ, IsPrimePow q → q ∣ n →
          (q : ℝ) ≤ (N : ℝ) ^ (1 - 8 / Real.log (Real.log N))) ∧
        (99 / 100 : ℝ) * Real.log (Real.log N) ≤ n.primeFactors.card ∧
        (n.primeFactors.card : ℝ) ≤ 2 * Real.log (Real.log N) ∧
        ∃ u v : ℕ, u ∣ n ∧ v ∣ n ∧ y ≤ u ∧ 4 * u ≤ v ∧ v ≤ z

/-- Extraction of a reciprocal from a finite arithmetically regular set
with sufficient reciprocal mass. -/
def H2 : Prop :=
  ∀ y z : ℕ, 0 < y → 4*y+4 ≤ z →
    ∀ᶠ N : ℕ in atTop, ∀ B : Finset ℕ, 0 ∉ B → B ⊆ range N →
      (∀ n ∈ B, (N : ℝ) ^ (1 - 1 / Real.log (Real.log N)) ≤ n ∧
        (∀ q : ℕ, IsPrimePow q → q ∣ n →
          (q : ℝ) ≤ (N : ℝ) ^ (1 - 8 / Real.log (Real.log N))) ∧
        (99 / 100 : ℝ) * Real.log (Real.log N) ≤ n.primeFactors.card ∧
        (n.primeFactors.card : ℝ) ≤ 2 * Real.log (Real.log N) ∧
        ∃ u v : ℕ, u ∣ n ∧ v ∣ n ∧ y ≤ u ∧ 4 * u ≤ v ∧ v ≤ z) →
      4 / (y : ℝ) ≤ ∑ n ∈ B, (1 : ℝ) / n →
      ∃ d ∈ Icc y z, ∃ S ⊆ B, ∑ n ∈ S, (1 : ℚ) / n = 1 / d

theorem main : H1 → H2 → OMA.R_Erdos299_erdos_299_variants_density_R1.H1 := by
  classical
  intro sieve extract A hzero hdens
  let ε := A.upperDensity / 4
  have he : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨y,z,hy,hyz,hyε,hsieve⟩ := sieve ε he
  refine ⟨Icc y z, fun d hd => hy.trans_le (mem_Icc.mp hd).1, ?_⟩
  intro M
  have hf : ∃ᶠ N : ℕ in atTop, 3*ε < A.partialDensity Set.univ N := by
    apply frequently_lt_of_lt_limsup
    · exact isCoboundedUnder_le_of_eventually_le _ (Eventually.of_forall fun n =>
        show 0 ≤ A.partialDensity Set.univ n from div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    · change 3*ε < A.upperDensity
      dsimp [ε]
      linarith
  have hm : ∀ᶠ N : ℕ in atTop, (M : ℝ) ≤ ε * N := by
    obtain ⟨T, hT⟩ := exists_nat_ge ((M : ℝ) / ε)
    filter_upwards [eventually_ge_atTop T] with N hN
    have hh := (div_le_iff₀ he).mp (hT.trans (Nat.cast_le.mpr hN))
    linarith
  obtain ⟨N, hprop⟩ := (hf.and_eventually
    (hsieve.and ((extract y z hy hyz).and (hm.and (eventually_gt_atTop 0))))).exists
  obtain ⟨hd, ⟨E,hE,hgood⟩, hrec, hM, hN⟩ := hprop
  let U := (range N).filter (· ∈ A)
  have hc : (↑U : Set ℕ) = A ∩ Set.Iio N := by
    ext k
    simp [U, and_comm]
  have hd' : 3 * ε * N < U.card := by
    apply (lt_div_iff₀ (Nat.cast_pos.mpr hN : (0 : ℝ) < N)).mp
    simpa [Set.partialDensity, Nat.ncard_Iio, ← hc] using hd
  let B := U \ (E ∪ range M)
  have hb (n) (hn : n ∈ B) := mem_sdiff.mp hn
  have hU (n) (hn : n ∈ B) := mem_filter.mp (hb n hn).1
  have hBN : B ⊆ range N := fun n hn => (hU n hn).1
  have hsub : (↑B : Set ℕ) ⊆ A ∩ Set.Ici M := by
    intro n hn
    refine ⟨(hU n hn).2, ?_⟩
    have h := (hb n hn).2
    simpa [not_or] using (show n ∉ range M from fun hh => h (mem_union_right _ hh))
  have hsize : ε * N ≤ B.card := by
    have h₁ := le_card_sdiff (E ∪ range M) U
    have h₂ := card_union_le E (range M)
    simp only [card_range] at h₂
    have h₃ : U.card ≤ B.card + E.card + M := by dsimp [B]; omega
    have h₄ : (U.card : ℝ) ≤ B.card + E.card + M := by exact_mod_cast h₃
    linarith
  have hmass : 4 / (y : ℝ) ≤ ∑ n ∈ B, (1 : ℝ)/n := by
    calc
      4 / (y : ℝ) ≤ (B.card : ℝ)/N :=
        hyε.le.trans ((le_div_iff₀ (Nat.cast_pos.mpr hN)).mpr hsize)
      _ = ∑ _n ∈ B, (1 : ℝ)/N := by simp [div_eq_mul_inv]
      _ ≤ _ := sum_le_sum fun n hn => by
        have hp : 0 < n := Nat.pos_of_ne_zero fun hz => hzero (hz ▸ (hU n hn).2)
        exact one_div_le_one_div_of_le (Nat.cast_pos.mpr hp)
          (Nat.cast_le.mpr (mem_range.mp (hBN hn)).le)
  obtain ⟨d,hd,S,hSB,hS⟩ := hrec B (fun h => hzero (hU 0 h).2) hBN
    (fun n hn => hgood n (mem_range.mp (hBN hn))
      (fun h => (hb n hn).2 (mem_union_left _ h))) hmass
  refine ⟨d,hd,S,fun _ hn => hsub (hSB hn), ?_⟩
  have hh := congrArg (fun t : ℚ => (t : ℝ)) hS
  simpa using hh

end OMA.R_Erdos299_erdos_299_variants_density_R1_H1_R1
