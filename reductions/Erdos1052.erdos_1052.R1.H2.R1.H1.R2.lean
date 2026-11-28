import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1

/-! A cardinality bound and fixed repeated-prime bounds suffice for the non-admissible family.
The sufficient threshold was proposed by @alanaut24 in note #194370. -/

open scoped BigOperators

open Finset

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R2

/-- A sufficient minimum-element threshold for admissibility in Erdős #1052. -/
private theorem admissible_of_min_threshold (S : Finset ℕ)
    (h : ∀ z ∈ S, 2101 * S.card * (S.card + 3) ≤ 4 * (z + 1)) :
    (∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) ∧
      ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097 := by
  by_cases he : S = ∅
  · subst S
    norm_num
  have hcard : 1 ≤ S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he)
  have hcardQ : (0 : ℚ) < (S.card : ℚ) := by exact_mod_cast hcard
  have hlarge (z : ℕ) (hz : z ∈ S) : 128 ≤ z ∧ S.card + 3 ≤ z := by
    have hm : S.card + 3 ≤ S.card * (S.card + 3) := by
      simpa using Nat.mul_le_mul_right (S.card + 3) hcard
    have hstep : 2101 * (S.card + 3) ≤ 4 * (z + 1) :=
      (Nat.mul_le_mul_left 2101 hm).trans (by simpa [Nat.mul_assoc] using h z hz)
    constructor <;> omega
  refine ⟨hlarge, ?_⟩
  let x : ℕ → ℚ := fun z => ((S.card : ℚ) + 3) / ((z : ℚ) + 1)
  have hxBound (z : ℕ) (hz : z ∈ S) : x z ≤ 4 / (2101 * (S.card : ℚ)) := by
    have hQ : 2101 * (S.card : ℚ) * ((S.card : ℚ) + 3) ≤ 4 * ((z : ℚ) + 1) := by
      exact_mod_cast h z hz
    dsimp [x]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith only [hQ]
  let c : ℚ := 4 / (2101 * (S.card : ℚ))
  have hc : 0 ≤ 1 - c := by
    have hcardQ' : (1 : ℚ) ≤ S.card := by exact_mod_cast hcard
    apply sub_nonneg.mpr
    dsimp [c]
    exact (div_le_one (by positivity)).mpr (by linarith)
  have hprod : (2097 : ℚ) / 2101 ≤ ∏ z ∈ S, (1 - x z) := by
    calc
      (2097 : ℚ) / 2101 = 1 + (S.card : ℚ) * ((1 - c) - 1) := by
        dsimp [c]
        field_simp [hcardQ.ne'] <;> ring
      _ ≤ (1 - c) ^ S.card :=
        one_add_mul_sub_le_pow (by linarith : (-1 : ℚ) ≤ 1 - c) S.card
      _ = ∏ _z ∈ S, (1 - c) := by rw [Finset.prod_const]
      _ ≤ ∏ z ∈ S, (1 - x z) :=
        Finset.prod_le_prod (fun _ _ => hc) (fun z hz => sub_le_sub_left (hxBound z hz) 1)
  calc
    ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) =
        ∏ z ∈ S, (1 - x z)⁻¹ := by
      apply Finset.prod_congr rfl
      intro z hz
      have hzp : 0 < (z : ℚ) + 1 := by positivity
      dsimp [x]
      have hdiff : (1 : ℚ) - ((S.card : ℚ) + 3) / ((z : ℚ) + 1) =
          ((z : ℚ) - 2 - (S.card : ℚ)) / ((z : ℚ) + 1) := by
        field_simp
        ring
      rw [hdiff, inv_div]
    _ = (∏ z ∈ S, (1 - x z))⁻¹ := by rw [Finset.prod_inv_distrib]
    _ ≤ 2101 / 2097 := by
      have hpos : (0 : ℚ) < 2097 / 2101 := by norm_num
      calc
        _ ≤ ((2097 : ℚ) / 2101)⁻¹ := (inv_le_inv₀ (hpos.trans_le hprod) hpos).mpr hprod
        _ = _ := by norm_num

/-- Non-admissibility forces an element below the cardinality-dependent threshold. -/
private theorem exists_below_admissible_threshold (S : Finset ℕ)
    (h : ¬ ((∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) ∧
      ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097)) :
    ∃ z ∈ S, 4 * (z + 1) < 2101 * S.card * (S.card + 3) := by
  by_contra! hh
  exact h (admissible_of_min_threshold S hh)

/-- Bound the number of repeated odd primes in the non-admissible family. -/
def H1 : Prop :=
  ∃ K : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    ¬ Squarefree (n / 2 ^ padicValNat 2 n) →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) →
    ¬ ((∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) ∧
      ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097) →
    S.card ≤ K

/-- Bound the valuation with a bounded repeated-prime count and one fixed repeated prime. -/
def H2 : Prop :=
  ∀ K z : ℕ, ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    ¬ Squarefree (n / 2 ^ padicValNat 2 n) →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) →
    ¬ ((∀ q ∈ S, 128 ≤ q ∧ S.card + 3 ≤ q) ∧
      ∏ q ∈ S, (((q : ℚ) + 1) / ((q : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097) →
    S.card ≤ K → z ∈ S → padicValNat 2 n ≤ A

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1.H1 := by
  classical
  rintro ⟨K, hK⟩ hfixed
  let bound : ℕ → ℕ := fun z => Classical.choose (hfixed K z)
  refine ⟨(range (2101 * K * (K + 3) / 4)).sup bound, ?_⟩
  intro n hunit hnonsq S hS hnot
  obtain ⟨z, hz, hsmall⟩ := exists_below_admissible_threshold S hnot
  have hcard := hK n hunit hnonsq S hS hnot
  have hthreshold : 2101 * S.card * (S.card + 3) ≤ 2101 * K * (K + 3) := by
    gcongr
  have hmem : z ∈ range (2101 * K * (K + 3) / 4) := mem_range.mpr (by omega)
  have hzbound : padicValNat 2 n ≤ bound z :=
    Classical.choose_spec (hfixed K z) n hunit hnonsq S hS hnot hcard hz
  exact hzbound.trans (le_sup (f := bound) hmem)

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R2
