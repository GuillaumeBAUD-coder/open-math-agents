import OMAStatements.S_oeis_a323695
import Mathlib

namespace A323695P

open PowerSeries OMA.S_oeis_a323695

/-- indicator of divisibility, as a power series over `ZMod 2` -/
noncomputable def g (d : ℕ) : PowerSeries (ZMod 2) := mk fun j => if d ∣ j then 1 else 0

lemma one_add_mul_g (d : ℕ) (hd : 1 ≤ d) : (1 + X ^ d) * g d = 1 := by
  ext j
  rw [add_mul, one_mul, map_add, coeff_X_pow_mul', g, coeff_mk, coeff_mk, coeff_one]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp; omega
  · have hj0 : j ≠ 0 := by omega
    by_cases hdj : d ∣ j
    · have hle : d ≤ j := Nat.le_of_dvd hj hdj
      have hdj' : d ∣ j - d := (Nat.dvd_sub_iff_left hle (dvd_refl d)).2 hdj
      simp only [hdj, hle, hdj', hj0, if_true, if_false]
      decide
    · by_cases hle : d ≤ j
      · have hdj' : ¬ d ∣ j - d := fun h => hdj ((Nat.dvd_sub_iff_left hle (dvd_refl d)).1 h)
        simp only [hdj, hle, hdj', hj0, if_true, if_false, add_zero]
      · simp only [hdj, hle, hj0, if_false, add_zero]

lemma isUnit_pow (n : ℕ) : IsUnit ((1 + X ^ (n + 1) : PowerSeries ℤ) ^ (n + 1)) := by
  apply IsUnit.pow
  rw [isUnit_iff_constantCoeff]
  simp

lemma map_summand (n : ℕ) :
    map (Int.castRingHom (ZMod 2)) (summand n) = X ^ n * g (n + 1) := by
  set φ := map (Int.castRingHom (ZMod 2))
  have hw : (1 + X ^ (n + 1) : PowerSeries ℤ) ^ (n + 1) *
      Ring.inverse ((1 + X ^ (n + 1)) ^ (n + 1)) = 1 :=
    Ring.mul_inverse_cancel _ (isUnit_pow n)
  set v := φ (Ring.inverse ((1 + X ^ (n + 1) : PowerSeries ℤ) ^ (n + 1)))
  have hv : (1 + X ^ (n + 1) : PowerSeries (ZMod 2)) ^ (n + 1) * v = 1 := by
    have := congrArg φ hw
    simpa [φ, v, map_mul, map_pow, map_add, map_one, map_X] using this
  have hg := one_add_mul_g (n + 1) (by omega)
  have hsub : (1 - X ^ (n + 1) : PowerSeries (ZMod 2)) = 1 + X ^ (n + 1) := by
    have h2 : (2 : PowerSeries (ZMod 2)) = 0 := by
      have e : (2 : PowerSeries (ZMod 2)) = 1 + 1 := one_add_one_eq_two.symm
      rw [e]
      ext j
      rw [map_add, map_zero, coeff_one]
      split_ifs <;> decide
    have hneg : -(X ^ (n + 1) : PowerSeries (ZMod 2)) = X ^ (n + 1) := by
      rw [neg_eq_iff_add_eq_zero, ← two_mul, h2, zero_mul]
    rw [sub_eq_add_neg, hneg]
  unfold summand
  rw [map_mul, map_mul, map_pow, map_pow, map_sub, map_one, map_pow, map_X]
  change X ^ n * (1 - X ^ (n + 1)) ^ n * v = X ^ n * g (n + 1)
  rw [hsub]
  calc X ^ n * (1 + X ^ (n + 1)) ^ n * v
      = X ^ n * (1 + X ^ (n + 1)) ^ n * v * ((1 + X ^ (n + 1)) * g (n + 1)) := by
        rw [hg, mul_one]
    _ = X ^ n * ((1 + X ^ (n + 1)) ^ (n + 1) * v) * g (n + 1) := by ring
    _ = X ^ n * g (n + 1) := by rw [hv, mul_one]

lemma a_mod_two (m : ℕ) : ((a m : ℤ) : ZMod 2) =
    (((Finset.range (m + 1)).filter fun n => (n + 1) ∣ (m + 1)).card : ZMod 2) := by
  have h := coeff_map (Int.castRingHom (ZMod 2)) m (∑ n ∈ Finset.range (m + 1), summand n)
  rw [eq_intCast] at h
  unfold a
  rw [← h, map_sum, map_sum, Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mem_range] at hn
  rw [map_summand, coeff_X_pow_mul', if_pos (by omega), g, coeff_mk]
  have : (n + 1 ∣ m - n) ↔ (n + 1 ∣ m + 1) := by
    rw [show m + 1 = (m - n) + (n + 1) by omega]
    exact (Nat.dvd_add_self_right).symm
  by_cases hd : n + 1 ∣ m + 1
  · rw [if_pos (this.2 hd), if_pos hd]; simp
  · rw [if_neg (fun h => hd (this.1 h)), if_neg hd]; simp


lemma card_T (N : ℕ) (hN : N ≠ 0) :
    ((Finset.range N).filter fun n => (n + 1) ∣ N).card = N.divisors.card := by
  apply Finset.card_bij (fun n _ => n + 1)
  · intro n hn
    rw [Finset.mem_filter] at hn
    rw [Nat.mem_divisors]
    exact ⟨hn.2, hN⟩
  · intro a _ b _ h
    omega
  · intro d hd
    rw [Nat.mem_divisors] at hd
    have hpos : 0 < d := Nat.pos_of_dvd_of_pos hd.1 (Nat.pos_of_ne_zero hN)
    have hle : d ≤ N := Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hd.1
    refine ⟨d - 1, ?_, by omega⟩
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, by rw [show d - 1 + 1 = d by omega]; exact hd.1⟩

lemma card_divisors_eq (N : ℕ) : N.divisors.card = N.divisorsAntidiagonal.card := by
  rw [← Nat.image_fst_divisorsAntidiagonal, Finset.card_image_of_injOn]
  intro p hp q hq h
  simp only [Finset.mem_coe, Nat.mem_divisorsAntidiagonal] at hp hq
  have h1 : p.1 = q.1 := h
  have hpos : 0 < p.1 := by
    rcases Nat.eq_zero_or_pos p.1 with h0 | h0
    · rw [h0, zero_mul] at hp; exact absurd hp.1.symm hp.2
    · exact h0
  have h2 : p.2 = q.2 := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [hp.1]; rw [h1, hq.1]
  exact Prod.ext h1 h2

lemma card_antidiag_mod_two (N : ℕ) (hN : N ≠ 0) :
    (N.divisorsAntidiagonal.card : ZMod 2) = 1 ↔ ∃ d, d * d = N := by
  classical
  set D := N.divisorsAntidiagonal
  have hsplit : D.card = (D.filter fun p => p.1 < p.2).card + (D.filter fun p => p.2 < p.1).card +
      (D.filter fun p => p.1 = p.2).card := by
    have e : ∀ p : ℕ × ℕ, (1 : ℕ) = (if p.1 < p.2 then 1 else 0) + (if p.2 < p.1 then 1 else 0) +
        (if p.1 = p.2 then 1 else 0) := by
      intro p; split_ifs <;> omega
    rw [Finset.card_eq_sum_ones, Finset.sum_congr rfl (fun p _ => e p), Finset.sum_add_distrib,
      Finset.sum_add_distrib, Finset.card_filter, Finset.card_filter, Finset.card_filter]
  have hswap : (D.filter fun p => p.2 < p.1).card = (D.filter fun p => p.1 < p.2).card := by
    apply Finset.card_bij (fun p _ => p.swap)
    · intro p hp
      rw [Finset.mem_filter] at hp ⊢
      exact ⟨Nat.swap_mem_divisorsAntidiagonal.2 hp.1, hp.2⟩
    · intro p _ q _ h
      exact Prod.swap_injective h
    · intro q hq
      rw [Finset.mem_filter] at hq
      exact ⟨q.swap, by
        rw [Finset.mem_filter]
        exact ⟨Nat.swap_mem_divisorsAntidiagonal.2 hq.1, hq.2⟩, Prod.swap_swap q⟩
  have hdiag : (D.filter fun p => p.1 = p.2).card = if ∃ d, d * d = N then 1 else 0 := by
    split_ifs with hex
    · obtain ⟨d, hd⟩ := hex
      rw [Finset.card_eq_one]
      refine ⟨(d, d), ?_⟩
      ext p
      rw [Finset.mem_filter, Nat.mem_divisorsAntidiagonal, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨hp, _⟩, he⟩
        have : p.1 = d := by
          rw [he] at hp
          rw [← hd] at hp
          rw [he]; exact Nat.mul_self_inj.1 hp
        exact Prod.ext this (by rw [← he]; exact this)
      · rintro rfl
        exact ⟨⟨hd, hN⟩, rfl⟩
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro p hp he
      rw [Nat.mem_divisorsAntidiagonal] at hp
      exact hex ⟨p.1, by rw [he] at hp ⊢; exact hp.1⟩
  rw [hsplit, hswap, hdiag]
  have h2 : (2 : ZMod 2) = 0 := by decide
  split_ifs with hex
  · simp only [hex, iff_true]
    push_cast
    rw [← two_mul, h2, zero_mul, zero_add]
  · simp only [hex, iff_false]
    push_cast
    rw [← two_mul, h2, zero_mul, add_zero]
    decide

end A323695P

open A323695P OMA.S_oeis_a323695 in
theorem OMA.solution : type_of% @OMA.S_oeis_a323695.main := by
  intro m
  rw [← ZMod.intCast_eq_one_iff_odd, a_mod_two, card_T (m + 1) (by omega), card_divisors_eq,
    card_antidiag_mod_two (m + 1) (by omega)]
  constructor
  · rintro ⟨d, hd⟩
    obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by
      rcases Nat.eq_zero_or_pos d with h | h
      · rw [h] at hd; omega
      · omega⟩
    refine ⟨k, ?_⟩
    ring_nf at hd ⊢
    omega
  · rintro ⟨k, rfl⟩
    exact ⟨k + 1, by ring⟩
