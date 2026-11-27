import OMAReductions.R_OeisA7406_conjecture_R1
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

/-! Prime-adic pruning for sums of reciprocal squares. -/

open Finset

namespace WolstenholmeSquare

private def term (j : ℕ) : ℚ := 1 / ((j : ℚ) + 1)^2

private def H₂ (m : ℕ) : ℚ := ∑ j ∈ range m, term j

private theorem H₂_succ (m : ℕ) : H₂ (m+1) = H₂ m + term m :=
  sum_range_succ _ _

private def unitPart (p m : ℕ) : ℚ :=
  ∑ j ∈ range m, if p ∣ j+1 then 0 else term j

theorem split_multiples (p m : ℕ) (_hp : 0 < p) :
    H₂ m = H₂ (m/p) / (p : ℚ)^2 + unitPart p m := by
  induction m with
  | zero => simp [H₂, unitPart]
  | succ m ih =>
    rw [H₂, unitPart, sum_range_succ, sum_range_succ]
    change H₂ m + term m =
      H₂ ((m+1)/p) / (p : ℚ)^2 + (unitPart p m + _)
    rw [ih]
    by_cases h : p ∣ m+1
    · rw [Nat.succ_div_of_dvd h, if_pos h, add_zero, H₂_succ]
      have heq : p * (m/p+1) = m+1 := by
        rw [← Nat.succ_div_of_dvd h, Nat.mul_div_cancel' h]
      have hc : (p : ℚ) * ((m/p : ℕ) + 1) = (m : ℚ) + 1 := by exact_mod_cast heq
      have hterm : term m = term (m/p) / (p : ℚ)^2 := by
        unfold term
        rw [← hc, mul_pow, div_div, mul_comm ((p : ℚ)^2)]
      rw [hterm, add_div]
      ring
    · rw [Nat.succ_div_of_not_dvd h, if_neg h]
      ring

private theorem unitPart_nonneg_val (p : ℕ) [Fact p.Prime] (m : ℕ) :
    0 ≤ padicValRat p (unitPart p m) := by
  induction m with
  | zero => simp [unitPart]
  | succ m ih =>
    rw [unitPart, sum_range_succ]
    change 0 ≤ padicValRat p (unitPart p m + if p ∣ m+1 then 0 else term m)
    by_cases hd : p ∣ m+1
    · simpa [hd] using ih
    rw [if_neg hd]
    by_cases hz : unitPart p m + term m = 0
    · simp [hz]
    have hval : padicValRat p (term m) = 0 := by
      have h0 : ((m : ℚ) + 1)^2 ≠ 0 := by positivity
      rw [term, padicValRat.div one_ne_zero h0, padicValRat.one, padicValRat.pow]
      have hm : padicValRat p ((m : ℚ)+1) = 0 := by
        rw [← Nat.cast_succ, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hd, Nat.cast_zero]
      rw [hm]
      norm_num
    exact le_trans (le_min ih (by simp [hval])) (padicValRat.min_le_padicValRat_add hz)

theorem val_of_low_prefix (p m : ℕ) [Fact p.Prime] (hm : 0 < m/p)
    (hbelow : padicValRat p (H₂ (m/p)) < 2) :
    padicValRat p (H₂ m) = padicValRat p (H₂ (m/p)) - 2 := by
  have hp := (Fact.out : p.Prime)
  have Hpos {n : ℕ} (hn : 0 < n) : 0 < H₂ n := by
    unfold H₂
    exact sum_pos (fun j _ => by unfold term; positivity) ⟨0, mem_range.mpr hn⟩
  have hpQ : (0 : ℚ) < p := by exact_mod_cast hp.pos
  have hx : 0 < H₂ (m/p) / (p : ℚ)^2 := div_pos (Hpos hm) (pow_pos hpQ 2)
  have hm' : 0 < m := hm.trans_le (Nat.div_le_self m p)
  have hval : padicValRat p (H₂ (m/p) / (p : ℚ)^2) =
      padicValRat p (H₂ (m/p)) - 2 := by
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    rw [padicValRat.div (Hpos hm).ne' (pow_ne_zero _ hp0), padicValRat.pow,
      padicValRat.self hp.one_lt]
    norm_num
  rw [split_multiples p m hp.pos]
  by_cases hzero : unitPart p m = 0
  · simpa [hzero] using hval
  have hne : H₂ (m/p) / (p : ℚ)^2 + unitPart p m ≠ 0 := by
    rw [← split_multiples p m hp.pos]
    exact (Hpos hm').ne'
  have hlt : padicValRat p (H₂ (m/p) / (p : ℚ)^2) < padicValRat p (unitPart p m) := by
    have hle := unitPart_nonneg_val p m
    omega
  rw [padicValRat.add_eq_of_lt hne hx.ne' hzero hlt, hval]

end WolstenholmeSquare

namespace WolstenholmeSquare

private theorem small_prefix_certificate :
    ([2,3,5,7,11,13,17,19,23,29,31] : List ℕ).all (fun p =>
      (List.range 32).all fun q =>
        decide (32 / p ≤ q → padicValRat p (H₂ q) < 2)) = true := by
  decide +kernel

theorem val_negative_of_small_prime {p m : ℕ} [Fact p.Prime] (hp31 : p ≤ 31)
    (hm32 : 32 ≤ m) : padicValRat p (H₂ m) < 0 := by
  have hp := (Fact.out : p.Prime)
  have hpmem : p ∈ ([2,3,5,7,11,13,17,19,23,29,31] : List ℕ) := by
    have h2 := hp.two_le
    interval_cases p <;> first | decide | (exfalso; revert hp; decide)
  have hbase := List.all_eq_true.mp small_prefix_certificate p hpmem
  induction m using Nat.strong_induction_on with
  | h m ih =>
    have hqpos : 0 < m/p := Nat.div_pos (by omega) hp.pos
    have hqm : m/p < m := Nat.div_lt_self (by omega) hp.one_lt
    have hq : padicValRat p (H₂ (m/p)) < 2 := by
      by_cases hq32 : 32 ≤ m/p
      · exact (ih (m/p) hqm hq32).trans (by decide)
      · have hqmem : m/p ∈ List.range 32 := List.mem_range.mpr (by omega)
        have hval := List.all_eq_true.mp hbase (m/p) hqmem
        have hle : 32/p ≤ m/p := Nat.div_le_div_right hm32
        exact of_decide_eq_true hval hle
    rw [val_of_low_prefix p m hqpos hq]
    omega

end WolstenholmeSquare

namespace WolstenholmeSquare

private theorem sum_eq_Icc (m : ℕ) :
    H₂ m = ∑ k ∈ Icc 1 m, (1 : ℚ) / (k : ℚ)^2 := by
  induction m with
  | zero => simp [H₂]
  | succ m ih =>
    rw [H₂_succ, ih, sum_Icc_succ_top (by omega : 1 ≤ m+1)]
    simp [term]

private theorem not_dvd_num_of_negative {p : ℕ} {x : ℚ}
    (hp : p.Prime) (h : padicValRat p x < 0) : ¬ p ∣ x.num.natAbs := by
  intro hnum
  have hden : ¬ p ∣ x.den := by
    intro hd
    exact hp.not_dvd_one (x.reduced.gcd_eq_one ▸ Nat.dvd_gcd hnum hd)
  rw [padicValRat_def, padicValNat.eq_zero_of_not_dvd hden] at h
  omega

private theorem small_n_certificate :
    ([2,3,5,7,11,13,17,19,23,29,31] : List ℕ).all (fun p =>
      (List.range 33).all fun n =>
        decide (3 < n → ¬ n.Prime → p ∣ n → ¬ p ∣ OeisA7406.a (n-1))) = true := by
  decide +kernel

theorem small_prime_not_dvd_numerator {p n : ℕ} (hp : p.Prime) (hp31 : p ≤ 31)
    (hn : 3 < n) (hnp : ¬ n.Prime) (hd : p ∣ n) :
    ¬ p ∣ OeisA7406.a (n-1) := by
  by_cases h : 33 ≤ n
  · have hv := @val_negative_of_small_prime p (n-1) ⟨hp⟩ hp31 (by omega)
    unfold OeisA7406.a
    rw [← sum_eq_Icc]
    exact not_dvd_num_of_negative hp hv
  · have hp2 := hp.two_le
    have hpList : p ∈ ([2,3,5,7,11,13,17,19,23,29,31] : List ℕ) := by
      interval_cases p <;> first | decide | (exfalso; revert hp; decide)
    have hcert := List.all_eq_true.mp (List.all_eq_true.mp small_n_certificate p hpList)
      n (List.mem_range.mpr (by omega))
    exact of_decide_eq_true hcert hn hnp hd

end WolstenholmeSquare

namespace OMA.R_OeisA7406_conjecture_R1_H2_R1

/-- Exclusion for the remaining prime factors up to the square root. -/
def H1 : Prop :=
  ∀ n p : ℕ, 3 < n → ¬ n.Prime → p.Prime → 31 < p →
    p ∣ n → p*p ≤ n → ¬ p ∣ OeisA7406.a (n-1)

/-- Exclusion for the remaining prime factors above the square root. -/
def H2 : Prop :=
  ∀ n p : ℕ, 3 < n → ¬ n.Prime → p.Prime → 31 < p →
    p ∣ n → n < p*p → ¬ p ∣ OeisA7406.a (n-1)

theorem main : H1 → H2 → OMA.R_OeisA7406_conjecture_R1.H2 := by
  intro hsmall hlarge n hn hnprime
  rw [OeisA89026.a, if_neg hnprime, ← Nat.coprime_iff_gcd_eq_one]
  by_contra h
  obtain ⟨p, hp, hpn, hpnum⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  by_cases hp31 : p ≤ 31
  · exact WolstenholmeSquare.small_prime_not_dvd_numerator hp hp31 hn hnprime hpn hpnum
  · by_cases hsq : p*p ≤ n
    · exact hsmall n p hn hnprime hp (by omega) hpn hsq hpnum
    · exact hlarge n p hn hnprime hp (by omega) hpn (by omega) hpnum

end OMA.R_OeisA7406_conjecture_R1_H2_R1
