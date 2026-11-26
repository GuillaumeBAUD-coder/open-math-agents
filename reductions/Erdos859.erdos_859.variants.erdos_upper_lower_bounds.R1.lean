import FormalConjectures.ErdosProblems.«859»
import Mathlib.Data.Nat.Periodic

/-! The natural density is exactly the fraction of one factorial period satisfying the
divisor sum condition. This leaves separate finite counting bounds. -/

-- Reduction Erdos859.erdos_859.variants.erdos_upper_lower_bounds.R1 of Erdős Problem 859 — erdos upper lower bounds
-- Credit: @dk8827
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_Erdos859_erdos_859_variants_erdos_upper_lower_bounds_R1

open Erdos859 Filter
open scoped Classical Topology

-- One period is the interval of positive integers from 1 through t!.
def H1 : Prop :=
  ∃ c > (0 : ℝ), ∀ᶠ t : ℕ in atTop,
    1 / Real.log t ^ c <
      (Nat.count (fun n => n + 1 ∈ DivisorSumSet t) t.factorial : ℝ) / t.factorial

def H2 : Prop :=
  ∃ c > (0 : ℝ), ∀ᶠ t : ℕ in atTop,
    (Nat.count (fun n => n + 1 ∈ DivisorSumSet t) t.factorial : ℝ) / t.factorial <
      1 / Real.log t ^ c

lemma successor_mem_periodic (t : ℕ) :
    Function.Periodic (fun n => n + 1 ∈ DivisorSumSet t) t.factorial := by
  intro n
  apply propext
  change n + t.factorial + 1 ∈ DivisorSumSet t ↔ n + 1 ∈ DivisorSumSet t
  rw [show n + t.factorial + 1 = n + 1 + t.factorial by omega]
  have dvd_shift {s : Finset ℕ} (hs : t = ∑ i ∈ s, i) {i : ℕ} (hi : i ∈ s)
      (hipos : 0 < i) : i ∣ n + 1 + t.factorial ↔ i ∣ n + 1 := by
    have hle : i ≤ t := hs ▸ Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _) hi
    exact (Nat.dvd_add_iff_left (Nat.dvd_factorial hipos hle)).symm
  constructor
  · rintro ⟨s, hs, hsum⟩
    refine ⟨s, fun i hi => ?_, hsum⟩
    have hdiv := (Nat.mem_divisors.mp (hs hi)).1
    have hipos := Nat.pos_of_dvd_of_pos hdiv (by omega)
    exact Nat.mem_divisors.mpr ⟨(dvd_shift hsum hi hipos).mp hdiv, by omega⟩
  · rintro ⟨s, hs, hsum⟩
    refine ⟨s, fun i hi => ?_, hsum⟩
    have hdiv := (Nat.mem_divisors.mp (hs hi)).1
    have hipos := Nat.pos_of_dvd_of_pos hdiv (by omega)
    exact Nat.mem_divisors.mpr ⟨(dvd_shift hsum hi hipos).mpr hdiv, by omega⟩

lemma periodic_count_ratio (p : ℕ → Prop) (d : ℕ)
    (hd : 0 < d) (hp : Function.Periodic p d) :
    Tendsto (fun n : ℕ => (Nat.count p n : ℝ) / n) atTop
      (𝓝 ((Nat.count p d : ℝ) / d)) := by
  let c : ℝ := Nat.count p d
  have hc : 0 ≤ c := by positivity
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hshift (k : ℕ) : Nat.count (fun i => p (i + d)) k = Nat.count p k := by
    simp only [Nat.count_eq_card_filter_range]
    congr 1
    ext i
    simp only [Finset.mem_filter, hp i]
  have hblocks (q : ℕ) : Nat.count p (q * d) = q * Nat.count p d := by
    induction q with
    | zero => simp
    | succ q ih => rw [Nat.succ_mul, Nat.count_add', hshift, ih, Nat.succ_mul]
  have herror : ∀ᶠ n : ℕ in atTop,
      c / d - c / n ≤ (Nat.count p n : ℝ) / n ∧
      (Nat.count p n : ℝ) / n ≤ c / d + c / n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    let q := n / d
    have hsplit : q * d + n % d = n := by simpa [q, Nat.mul_comm] using Nat.div_add_mod n d
    have hrem := Nat.mod_lt n hd
    have hlo : q * d ≤ n := by omega
    have hhi : n ≤ (q + 1) * d := by rw [Nat.add_mul, one_mul]; omega
    have hloR : (q : ℝ) * d ≤ n := by exact_mod_cast hlo
    have hhiR : (n : ℝ) ≤ ((q : ℝ) + 1) * d := by exact_mod_cast hhi
    have hclo := (Nat.count_monotone p) hlo
    have hchi := (Nat.count_monotone p) hhi
    rw [hblocks] at hclo hchi
    have hcloR : (q : ℝ) * c ≤ Nat.count p n := by
      dsimp [c]
      exact_mod_cast hclo
    have hchiR : (Nat.count p n : ℝ) ≤ ((q : ℝ) + 1) * c := by
      dsimp [c]
      exact_mod_cast hchi
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hloRatio : (q : ℝ) ≤ (n : ℝ) / d := (le_div_iff₀ hdR).mpr hloR
    have hhiRatio : (n : ℝ) / d ≤ (q : ℝ) + 1 := (div_le_iff₀ hdR).mpr hhiR
    have hloScaled := mul_le_mul_of_nonneg_right hloRatio hc
    have hhiScaled := mul_le_mul_of_nonneg_right hhiRatio hc
    constructor
    · apply (le_div_iff₀ hnR).2
      calc
        (c / d - c / n) * n = (n / d) * c - c := by field_simp
        _ ≤ Nat.count p n := by linarith
    · apply (div_le_iff₀ hnR).2
      calc
        (Nat.count p n : ℝ) ≤ (n / d) * c + c := by linarith
        _ = (c / d + c / n) * n := by field_simp
  have hcOverN := tendsto_const_div_atTop_nhds_zero_nat c
  have hconst : Tendsto (fun _ : ℕ => c / d) atTop (𝓝 (c / d)) := tendsto_const_nhds
  have hlower := hconst.sub hcOverN
  have hupper := hconst.add hcOverN
  rw [sub_zero] at hlower
  rw [add_zero] at hupper
  exact hlower.squeeze' hupper (herror.mono fun _ hn => hn.1) (herror.mono fun _ hn => hn.2)

lemma divisor_sum_density (t : ℕ) :
    (DivisorSumSet t).HasDensity
      ((Nat.count (fun n => n + 1 ∈ DivisorSumSet t) t.factorial : ℝ) / t.factorial) := by
  let S := DivisorSumSet t
  let p (n : ℕ) := n ∈ S
  let c : ℝ := if p 0 then 1 else 0
  have hratio := periodic_count_ratio (fun n => p (n + 1)) t.factorial
    (Nat.factorial_pos _) (successor_mem_periodic t)
  have hsmall := (tendsto_const_div_atTop_nhds_zero_nat c).comp (tendsto_add_atTop_nat 1)
  have hscale : Tendsto (fun n : ℕ => (n : ℝ) / (n + 1)) atTop (𝓝 1) := by
    have hu := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hlim := (tendsto_const_nhds (x := (1 : ℝ))).sub hu
    rw [sub_zero] at hlim
    refine hlim.congr fun n => ?_
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  have hl := (hratio.mul hscale).add hsmall
  simp only [mul_one, add_zero] at hl
  unfold Set.HasDensity
  apply (tendsto_add_atTop_iff_nat 1).1
  refine hl.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hcount (k : ℕ) : (S ∩ Set.Iio k).ncard = Nat.count p k := by
    rw [Nat.count_eq_card_filter_range, ← Set.ncard_coe_finset]
    congr 1
    ext i
    simp [p, and_comm]
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Set.ncard_Iio_nat]
  rw [hcount, Nat.count_succ']
  push_cast
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hnext : (n : ℝ) + 1 ≠ 0 := by positivity
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one, c]
  split_ifs <;> field_simp

theorem main : H1 → H2 → type_of% @Erdos859.erdos_859.variants.erdos_upper_lower_bounds := by
  rintro ⟨c₁, hc₁, hlower⟩ ⟨c₂, hc₂, hupper⟩
  refine ⟨c₁, hc₁, c₂, hc₂, 0, ?_⟩
  filter_upwards [hlower, hupper] with t ht₁ ht₂
  exact ⟨_, divisor_sum_density t, ht₁, ht₂⟩

end OMA.R_Erdos859_erdos_859_variants_erdos_upper_lower_bounds_R1
