import OMAReductions.R_SolitaryNumber_is_ten_solitary_R1

-- The only even number with abundancy 9/5 is 10.
-- Original Lean proof of a classical observation: 10 sigma(m) = 18 m forces 5 to divide m, so an even m is 10k,
-- and for k > 1 the divisors k*d of 10k (d dividing 10) together with the divisor 1 already sum to more than
-- 18k, so the abundancy of 10k exceeds 9/5.
-- A classical first step, not progress on the question whether 10 is solitary.

namespace OMA.Solitary1

open ArithmeticFunction Finset

lemma sigma_mul_gt (a k : ℕ) (ha : 0 < a) (hk : 1 < k) : k * sigma 1 a < sigma 1 (k * a) := by
  rw [sigma_one_apply, sigma_one_apply]
  have hsub : insert 1 ((a.divisors).image (fun d => k * d)) ⊆ (k * a).divisors := by
    intro d hd
    rw [Finset.mem_insert, Finset.mem_image] at hd
    rcases hd with rfl | ⟨e, he, rfl⟩
    · exact Nat.one_mem_divisors.mpr (Nat.mul_pos (by omega) ha).ne'
    · rw [Nat.mem_divisors] at he ⊢
      exact ⟨Nat.mul_dvd_mul_left k he.1, (Nat.mul_pos (by omega) ha).ne'⟩
  have h1 : (1 : ℕ) ∉ (a.divisors).image (fun d => k * d) := by
    intro h
    obtain ⟨e, -, he⟩ := Finset.mem_image.mp h
    have h2 := Nat.le_of_dvd Nat.one_pos (Dvd.intro e he)
    omega
  have himg : ∑ d ∈ (a.divisors).image (fun d => k * d), d = k * ∑ d ∈ a.divisors, d := by
    rw [Finset.sum_image, Finset.mul_sum]
    intro x _ y _ h
    exact Nat.eq_of_mul_eq_mul_left (by omega) h
  calc k * ∑ d ∈ a.divisors, d
      < ∑ d ∈ insert 1 ((a.divisors).image (fun d => k * d)), d := by
        rw [Finset.sum_insert h1, himg]
        omega
    _ ≤ ∑ d ∈ (k * a).divisors, d := Finset.sum_le_sum_of_subset hsub

theorem even_friend (m : ℕ) (hm : 0 < m) (he : Even m) (h : sigma 1 m * 10 = 18 * m) : m = 10 := by
  obtain ⟨c, hc⟩ := he
  obtain ⟨k, rfl⟩ : ∃ k, m = k * 10 := ⟨m / 10, by omega⟩
  by_contra hne
  have hk : 1 < k := by omega
  have h18 : sigma 1 10 = 18 := by decide
  have hgt := sigma_mul_gt 10 k (by norm_num) hk
  rw [h18] at hgt
  omega

end OMA.Solitary1

theorem OMA.solution : OMA.R_SolitaryNumber_is_ten_solitary_R1.H1 := by
  intro m hm he h
  exact OMA.Solitary1.even_friend m hm he h
