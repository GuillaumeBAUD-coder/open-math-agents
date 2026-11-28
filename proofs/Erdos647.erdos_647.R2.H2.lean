import OMAReductions.R_Erdos647_erdos_647_R2

/-!
# Proof of `Erdos647.erdos_647.R2.H2`

Proves that for every `t > 0` and `k ∈ {1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 16, 18, 20, 24}`, if
`q = (720720 / k) * t - 1` is prime then `σ 0 (720720 * t - k) ≤ k + 2`.

Every listed `k` divides `720720`, so `720720 * t - k = k * q`. Submultiplicativity of the divisor
counting function `σ 0` gives `σ 0 (k * q) ≤ σ 0 k * σ 0 q = 2 * σ 0 k`, and direct evaluation
verifies `2 * σ 0 k ≤ k + 2` for all 14 values of `k`.
-/

open ArithmeticFunction.sigma

namespace Erdos647R2H2Proof

private lemma sigma_zero_mul_le (a b : ℕ) : σ 0 (a * b) ≤ σ 0 a * σ 0 b := by
  rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply,
    ArithmeticFunction.sigma_zero_apply]
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  have hsub : (a * b).divisors ⊆ (a.divisors ×ˢ b.divisors).image (fun p => p.1 * p.2) := by
    intro d hd
    rw [Nat.mem_divisors] at hd
    obtain ⟨u, v, hu, hv, rfl⟩ := Nat.dvd_mul.mp hd.1
    refine Finset.mem_image.mpr ⟨(u, v), Finset.mem_product.mpr ?_, rfl⟩
    exact ⟨Nat.mem_divisors.mpr ⟨hu, ha.ne'⟩, Nat.mem_divisors.mpr ⟨hv, hb.ne'⟩⟩
  calc (a * b).divisors.card
      ≤ ((a.divisors ×ˢ b.divisors).image (fun p => p.1 * p.2)).card := Finset.card_le_card hsub
    _ ≤ (a.divisors ×ˢ b.divisors).card := Finset.card_image_le
    _ = a.divisors.card * b.divisors.card := Finset.card_product _ _

private lemma two_mul_sigma_zero_le :
    ∀ k ∈ ({1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 16, 18, 20, 24} : Finset ℕ),
      k ∣ 720720 ∧ 2 * k.divisors.card ≤ k + 2 := by
  decide

end Erdos647R2H2Proof

theorem OMA.solution : OMA.R_Erdos647_erdos_647_R2.H2 := by
  intro t k ht hk hq
  obtain ⟨hdvd, hbound⟩ := Erdos647R2H2Proof.two_mul_sigma_zero_le k hk
  have hmul : 720720 * t - k = k * ((720720 / k) * t - 1) := by
    have hk_eq : k * (720720 / k) = 720720 := Nat.mul_div_cancel' hdvd
    have hpos : 1 ≤ (720720 / k) * t := by
      have h1 : 1 ≤ 720720 / k := Nat.div_pos (Nat.le_of_dvd (by norm_num) hdvd) (by
        rcases Finset.mem_insert.mp hk with rfl | hk <;>
          simp only [Finset.mem_insert, Finset.mem_singleton] at hk <;> omega)
      exact Nat.mul_pos h1 ht
    rw [Nat.mul_sub_left_distrib, mul_one, ← mul_assoc, hk_eq]
  rw [hmul]
  have hsub := Erdos647R2H2Proof.sigma_zero_mul_le k ((720720 / k) * t - 1)
  have hq2 : σ 0 ((720720 / k) * t - 1) = 2 := by
    rw [ArithmeticFunction.sigma_zero_apply, hq.divisors, Finset.card_pair hq.ne_one.symm]
  rw [hq2, ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply] at hsub
  rw [ArithmeticFunction.sigma_zero_apply]
  omega
