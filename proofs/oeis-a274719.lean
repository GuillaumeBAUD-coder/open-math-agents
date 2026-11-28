import OMAStatements.S_oeis_a274719
import Mathlib
import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries


namespace OMA.S_oeis_a274719

open PowerSeries

noncomputable def P (K : ℕ) : PowerSeries ℤ := ∏ k ∈ Finset.range K, (1 - PowerSeries.X ^ (k + 1))

lemma stable (m K1 : ℕ) (h : m ≤ K1) : ∀ d : ℕ,
    PowerSeries.coeff m (P (K1 + d)) = PowerSeries.coeff m (P K1) := by
  intro d
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [← ih]
    unfold P at *
    rw [← add_assoc, Finset.prod_range_succ, mul_sub, mul_one, map_sub, PowerSeries.coeff_mul_X_pow' ]
    · have : ¬ (K1 + d + 1 ≤ m) := by omega
      simp [this]

lemma pent_coeff (m : ℕ) : ∃ K0, ∀ K ≥ K0, PowerSeries.coeff m (P K) =
    PowerSeries.coeff m (pentagonalSeries ℤ) := by
  have h := coeff_prod_one_sub_X_pow_eventually_eq ℤ m
  rw [Filter.eventually_atTop] at h
  obtain ⟨s0, hs0⟩ := h
  refine ⟨s0.sup id + 1, fun K hK => ?_⟩
  apply hs0
  intro x hx
  simp only [Finset.mem_range]
  have : x ≤ s0.sup id := Finset.le_sup (f := id) hx
  omega

lemma a_eq (n : ℕ) : a n = if 2 ∣ n then PowerSeries.coeff (n / 2) (pentagonalSeries ℤ) else 0 := by
  have h1 : (∏ k ∈ Finset.range n, (1 - PowerSeries.X ^ (2 * (k + 1)) : PowerSeries ℤ)) =
      ((Polynomial.expand ℤ 2 (∏ k ∈ Finset.range n, (1 - Polynomial.X ^ (k + 1) : Polynomial ℤ)) : Polynomial ℤ) : PowerSeries ℤ) := by
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_prod, map_prod]
    apply Finset.prod_congr rfl
    intro k _
    simp [pow_mul']
    ring
  unfold a
  rw [h1, Polynomial.coeff_coe, Polynomial.coeff_expand (by norm_num)]
  split_ifs with h2
  · obtain ⟨K0, hK0⟩ := pent_coeff (n / 2)
    rw [← hK0 (K0 + n) (by omega)]
    have hdum : K0 + n = n + K0 := add_comm _ _
    have h3 := stable (n / 2) n (by omega) K0
    rw [add_comm n K0] at h3
    rw [h3]
    unfold P
    rw [← Polynomial.coeff_coe]
    congr 1
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
    apply Finset.prod_congr rfl
    intro k _
    simp
  · rfl

lemma b_sq (n : ℕ) : b (12 * n + 1) = if IsSquare (12 * n + 1) then 1 else 0 := by
  split_ifs with hs
  · obtain ⟨s, hs⟩ := hs
    have hs2 : 12 * n + 1 = s ^ 2 := by rw [hs]; ring
    unfold b
    rw [hs2, Nat.primeFactors_pow _ (by norm_num)]
    apply Finset.prod_eq_one
    intro p hp
    have hp3 : p ≠ 3 := by
      rintro rfl
      have : 3 ∣ s := Nat.dvd_of_mem_primeFactors hp
      have : 3 ∣ 12 * n + 1 := by rw [hs2]; exact Dvd.dvd.pow this (by norm_num)
      omega
    rw [if_neg hp3, Nat.factorization_pow]
    simp
  · by_contra hne
    unfold b at hne
    have hne : ∀ p ∈ (12 * n + 1).primeFactors, (if p = 3 then 0 ^ (12 * n + 1).factorization p else (1 + (-1) ^ (12 * n + 1).factorization p) / 2 : ℤ) ≠ 0 :=
      fun p hp h => hne (Finset.prod_eq_zero hp h)
    apply hs
    set m := 12 * n + 1 with hm
    have hev : ∀ p ∈ m.primeFactors, Even (m.factorization p) := by
      intro p hp
      have := hne p hp
      by_cases hp3 : p = 3
      · rw [if_pos hp3] at this
        have hpos : 0 < m.factorization p := by
          have := Nat.prime_of_mem_primeFactors hp
          exact Nat.Prime.factorization_pos_of_dvd this (by omega) (Nat.dvd_of_mem_primeFactors hp)
        exact absurd (zero_pow hpos.ne') this
      · rw [if_neg hp3] at this
        by_contra hodd
        rw [Nat.not_even_iff_odd] at hodd
        rw [hodd.neg_one_pow] at this
        simp at this
    refine ⟨∏ p ∈ m.primeFactors, p ^ (m.factorization p / 2), ?_⟩
    have hm0 : m ≠ 0 := by omega
    have := Nat.factorization_prod_pow_eq_self hm0
    conv_lhs => rw [← this]
    rw [Finsupp.prod, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    rw [← pow_add]
    congr 1
    have := hev p hp
    obtain ⟨r, hr⟩ := this
    omega

theorem sol : ∀ n : ℕ, |a n| = A089806 n := by
  intro n
  unfold A089806
  rw [b_sq, a_eq]
  by_cases hsq : IsSquare (12 * n + 1)
  · rw [if_pos hsq]
    obtain ⟨s, hs⟩ := hsq
    have hs2 : 12 * n + 1 = s ^ 2 := by rw [hs]; ring
    -- s = 6k-1 or 6k+1
    have hodd : s % 6 = 1 ∨ s % 6 = 5 := by
      have : s ^ 2 % 12 = 1 := by omega
      have h6 : s % 12 = 1 ∨ s % 12 = 5 ∨ s % 12 = 7 ∨ s % 12 = 11 := by
        have := Nat.mod_lt s (show 12 > 0 by norm_num)
        have h : s ^ 2 % 12 = (s % 12) ^ 2 % 12 := Nat.pow_mod _ _ _
        interval_cases hh : s % 12 <;> simp_all
      omega
    obtain ⟨k, hk⟩ : ∃ k : ℤ, (s : ℤ) = 6 * k - 1 ∨ (s : ℤ) = -(6 * k - 1) := by
      rcases hodd with h | h
      · refine ⟨-((s : ℤ) - 1) / 6, Or.inr ?_⟩
        omega
      · refine ⟨((s : ℤ) + 1) / 6, Or.inl ?_⟩
        omega
    have hnk : (n : ℤ) = k * (3 * k - 1) := by
      have h3 : ((12 * n + 1 : ℕ) : ℤ) = (s : ℤ) ^ 2 := by rw [hs2]; push_cast; ring
      push_cast at h3
      rcases hk with hk | hk <;> rw [hk] at h3 <;> nlinarith
    have h2 : 2 ∣ n := by
      have : (n : ℤ) % 2 = 0 := by
        rw [hnk]
        rcases Int.emod_two_eq_zero_or_one k with h | h
        · simp [Int.mul_emod, h]
        · have : (3 * k - 1) % 2 = 0 := by omega
          simp [Int.mul_emod, this]
      omega
    rw [if_pos h2]
    have hpe : n / 2 = pentagonal k := by
      have := two_mul_natCast_pentagonal k
      omega
    rw [hpe, coeff_pentagonalSeries_pentagonal]
    rcases Int.units_eq_one_or (Int.negOnePow k) with h | h <;> rw [h] <;> simp
  · rw [if_neg hsq]
    split_ifs with h2
    · have hz : PowerSeries.coeff (n / 2) (pentagonalSeries ℤ) = 0 := by
        rw [coeff_pentagonalSeries_eq_zero_iff]
        rintro ⟨k, hk⟩
        apply hsq
        have := two_mul_natCast_pentagonal k
        refine ⟨(6 * k - 1).natAbs, ?_⟩
        have h5 : (12 * n + 1 : ℤ) = (6 * k - 1) * (6 * k - 1) := by
          have : (n : ℤ) = 2 * (pentagonal k) := by omega
          nlinarith
        have h6 : ((12 * n + 1 : ℕ) : ℤ) = (((6 * k - 1).natAbs * (6 * k - 1).natAbs : ℕ) : ℤ) := by
          push_cast
          rw [abs_mul_abs_self]
          linarith
        exact_mod_cast h6
      rw [hz]; simp
    · simp

end OMA.S_oeis_a274719

theorem OMA.solution : type_of% @OMA.S_oeis_a274719.main := OMA.S_oeis_a274719.sol
