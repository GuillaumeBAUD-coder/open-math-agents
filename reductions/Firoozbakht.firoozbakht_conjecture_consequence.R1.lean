import FormalConjectures.Wikipedia.Firoozbakht
import Mathlib.Analysis.Complex.ExponentialBounds

-- Reduction of Firoozbakht.firoozbakht_conjecture_consequence
-- Credit: @mrmario2202

namespace OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1

open Real

/-- Large-input prime counting bound. This follows from inequalities (4) and (5)
in Kourbatov, J. Integer Seq. 18 (2015), Article 15.11.2. -/
def H1 : Prop :=
  ∀ p : ℕ, 1772201 ≤ p →
    (p : ℝ) + log (p : ℝ) ^ 2 ≤ (Nat.primeCounting p : ℝ) * (log (p : ℝ) - 1)

/-- Finite rational check. Range reduction by a power of two makes two terms of the
logarithm series sufficient for every prime in the finite range. -/
def H2 : Prop :=
  ∀ i : Fin 1772201, 11 ≤ (i : ℕ) → (i : ℕ).Prime →
    let p : ℕ := i
    let k := Nat.log 2 p
    let b : ℕ := 2 ^ k
    let t : ℚ := ((p : ℚ) - b) / ((p : ℚ) + b)
    let a : ℚ := (693 / 1000) * k + 2 * (t + t ^ 3 / 3)
    1 ≤ a ∧ ∃ g : Fin 256, 0 < (g : ℕ) ∧ (p + (g : ℕ)).Prime ∧
      ((g : ℕ) : ℚ) < a ^ 2 - a

lemma dyadic_log_lower (p k : ℕ) (hb : 2 ^ k ≤ p) :
    let b : ℕ := 2 ^ k
    let t : ℚ := ((p : ℚ) - b) / ((p : ℚ) + b)
    (((693 / 1000 : ℚ) * k + 2 * (t + t ^ 3 / 3) : ℚ) : ℝ) ≤ log (p : ℝ) := by
  dsimp only
  push_cast
  let b : ℝ := (2 : ℝ) ^ k
  let t : ℝ := ((p : ℝ) - b) / ((p : ℝ) + b)
  change (693 / 1000 : ℝ) * k + 2 * (t + t ^ 3 / 3) ≤ log (p : ℝ)
  have hb0 : 0 < b := by positivity
  have hbp : b ≤ (p : ℝ) := by
    dsimp [b]
    exact_mod_cast hb
  have hp : 0 < (p : ℝ) := hb0.trans_le hbp
  have hden : 0 < (p : ℝ) + b := add_pos hp hb0
  have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hbp) hden.le
  have ht1 : t < 1 := (div_lt_one hden).mpr (by linarith)
  have harg : (1 + t) / (1 - t) = (p : ℝ) / b := by
    apply (div_eq_div_iff (sub_pos.mpr ht1).ne' hb0.ne').2
    dsimp only [t]
    field_simp [hden.ne']
    <;> ring
  have hseries := Real.sum_range_le_log_div ht0 ht1 2
  rw [harg, Real.log_div hp.ne' hb0.ne'] at hseries
  have hseries' : t + t ^ 3 / 3 ≤ 1 / 2 * (log (p : ℝ) - log b) := by
    norm_num [Finset.sum_range_succ] at hseries ⊢
    linarith only [hseries]
  have hb_log : log b = (k : ℝ) * log 2 := Real.log_pow 2 k
  have hbase : (693 / 1000 : ℝ) * k ≤ log b := by
    rw [hb_log, mul_comm (693 / 1000 : ℝ)]
    exact mul_le_mul_of_nonneg_left (by linarith [Real.log_two_gt_d9]) (by positivity)
  linarith

lemma prime_index (n : ℕ) : Nat.primeCounting (Nat.nth Nat.Prime n) = n + 1 := by
  rw [Nat.primeCounting_eq_primeCounting'_succ]
  change Nat.count Nat.Prime (Nat.nth Nat.Prime n + 1) = n + 1
  rw [Nat.count_succ, if_pos (Nat.prime_nth_prime n)]
  change Nat.primeCounting' (Nat.nth Nat.Prime n) + 1 = n + 1
  rw [Nat.primeCounting'_nth_eq]

lemma nat_prime_predicate : (_root_.Prime : ℕ → Prop) = Nat.Prime := by
  funext p
  exact propext (Nat.prime_iff (p := p)).symm

theorem main : H1 → H2 → type_of% @Firoozbakht.firoozbakht_conjecture_consequence := by
  intro hcount hfinite n hn hconj
  let p : ℕ := Nat.nth Nat.Prime n
  let q : ℕ := Nat.nth Nat.Prime (n + 1)
  have hmono_primes := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  have hpq : p < q := hmono_primes (Nat.lt_succ_self n)
  have hp11 : 11 ≤ p := by
    rw [← Nat.nth_prime_four_eq_eleven]
    exact hmono_primes.monotone (show 4 ≤ n by omega)
  have hp : 0 < (p : ℝ) := by exact_mod_cast (show 0 < p by omega)
  have hq : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hgap : 0 ≤ (q : ℝ) - p := sub_nonneg.mpr (by exact_mod_cast hpq.le)
  suffices h : (q : ℝ) - (p : ℝ) < log (p : ℝ) ^ 2 - log (p : ℝ) by
    simpa only [p, q, nat_prime_predicate] using h
  by_cases hlarge : 1772201 ≤ p
  · have hpc := hcount p hlarge
    change (p : ℝ) + log (p : ℝ) ^ 2 ≤
      (Nat.primeCounting (Nat.nth Nat.Prime n) : ℝ) * (log (p : ℝ) - 1) at hpc
    rw [prime_index, Nat.cast_add, Nat.cast_one] at hpc
    have hlog : 1 < log (p : ℝ) := by
      have h4 : (4 : ℝ) ≤ p := by exact_mod_cast (show 4 ≤ p by omega)
      have hm := Real.log_le_log (by norm_num : (0 : ℝ) < 4) h4
      rw [Real.log_four_eq] at hm
      linarith [Real.log_two_gt_d9]
    have hr : (q : ℝ) ^ (1 / ((n : ℝ) + 1 + 1)) <
        (p : ℝ) ^ (1 / ((n : ℝ) + 1)) := by
      simpa only [Firoozbakht.firoozbakhtSeq, nat_prime_predicate, p, q,
        Nat.cast_add, Nat.cast_one] using hconj n
    have hlogs := Real.log_lt_log (Real.rpow_pos_of_pos hq _) hr
    rw [Real.log_rpow hq, Real.log_rpow hp] at hlogs
    have hdiv : log (q : ℝ) / ((n : ℝ) + 1 + 1) <
        log (p : ℝ) / ((n : ℝ) + 1) := by
      simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using hlogs
    have hn1 : 0 < (n : ℝ) + 1 := by positivity
    have hn2 : 0 < (n : ℝ) + 1 + 1 := by positivity
    have hcross := (div_lt_div_iff₀ hn2 hn1).mp hdiv
    have hdiff : ((n : ℝ) + 1) * (log (q : ℝ) - log (p : ℝ)) < log (p : ℝ) := by
      nlinarith only [hcross]
    have hfrac : ((q : ℝ) - p) / q ≤ log (q : ℝ) - log (p : ℝ) := by
      have h := Real.one_sub_inv_le_log_of_pos (div_pos hq hp)
      rw [Real.log_div hq.ne' hp.ne', inv_div] at h
      simpa only [sub_div, div_self hq.ne'] using h
    have hscaled := (mul_le_mul_of_nonneg_left hfrac hn1.le).trans_lt hdiff
    rw [← mul_div_assoc] at hscaled
    have hprod := (div_lt_iff₀ hq).mp hscaled
    have hgap_bound : ((p : ℝ) + log (p : ℝ) ^ 2) * ((q : ℝ) - p) <
        log (p : ℝ) * q * (log (p : ℝ) - 1) := calc
      _ ≤ (((n : ℝ) + 1) * (log (p : ℝ) - 1)) * ((q : ℝ) - p) :=
        mul_le_mul_of_nonneg_right hpc hgap
      _ = (((n : ℝ) + 1) * ((q : ℝ) - p)) * (log (p : ℝ) - 1) := by ring
      _ < _ := mul_lt_mul_of_pos_right hprod (sub_pos.mpr hlog)
    by_contra! hbad
    have hnonneg := mul_nonneg hp.le (sub_nonneg.mpr hbad)
    have hnonneg' := mul_nonneg hgap (by linarith only [hlog] : 0 ≤ log (p : ℝ))
    nlinarith only [hgap_bound, hnonneg, hnonneg']
  · let k := Nat.log 2 p
    let b : ℕ := 2 ^ k
    let t : ℚ := ((p : ℚ) - b) / ((p : ℚ) + b)
    let a : ℚ := (693 / 1000) * k + 2 * (t + t ^ 3 / 3)
    have h := hfinite ⟨p, lt_of_not_ge hlarge⟩ hp11 (Nat.prime_nth_prime n)
    change 1 ≤ a ∧ ∃ g : Fin 256, 0 < (g : ℕ) ∧ (p + (g : ℕ)).Prime ∧
      ((g : ℕ) : ℚ) < a ^ 2 - a at h
    obtain ⟨ha_rat, g, hg, hgprime, hg_rat⟩ := h
    have hq_le : q ≤ p + (g : ℕ) := by
      apply (Nat.isLeast_nth_of_infinite Nat.infinite_setOfPred_prime (n + 1)).2
      refine ⟨hgprime, fun j hj => ?_⟩
      have hjp : Nat.nth Nat.Prime j ≤ p := hmono_primes.monotone (show j ≤ n by omega)
      exact hjp.trans_lt (show p < p + (g : ℕ) by omega)
    have hq_gap : (q : ℝ) - p ≤ ((g : ℕ) : ℝ) := by
      have hq_cast : (q : ℝ) ≤ (p : ℝ) + ((g : ℕ) : ℝ) := by exact_mod_cast hq_le
      linarith
    have ha : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha_rat
    have hg_real : ((g : ℕ) : ℝ) < (a : ℝ) ^ 2 - a := by exact_mod_cast hg_rat
    have hfinite_gap := hq_gap.trans_lt hg_real
    have hp0 : p ≠ 0 := by omega
    have halog : (a : ℝ) ≤ log (p : ℝ) :=
      dyadic_log_lower p k (Nat.pow_log_le_self 2 hp0)
    have hmono : (a : ℝ) ^ 2 - a ≤ log (p : ℝ) ^ 2 - log (p : ℝ) := by
      have hfactor : 0 ≤ log (p : ℝ) + (a : ℝ) - 1 := by linarith
      nlinarith only [mul_nonneg (sub_nonneg.mpr halog) hfactor]
    exact hfinite_gap.trans_le hmono

end OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1
