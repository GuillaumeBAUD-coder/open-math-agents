import OMAStatements.S_oeis_a343502
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a343502.main := by
  intro k h1 h2 hk2 hk3
  unfold OMA.S_oeis_a343502.tau at h1 h2
  have hk1 : 1 < k := by
    by_contra hle
    have h01 : k = 0 ∨ k = 1 := by omega
    rcases h01 with rfl | rfl
    · simp at h1
      exact Nat.not_prime_zero h1
    · simp at h1
      exact Nat.not_prime_one h1
  refine ⟨hk1, fun hp => ?_⟩
  have hk5 : 5 ≤ k := by
    by_contra h
    have h4 : k = 4 := by omega
    subst h4
    exact absurd hp (by norm_num)
  have hodd : k % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  obtain ⟨e, u, hu, hku⟩ := Nat.exists_eq_two_pow_mul_odd (n := k + 1) (by omega)
  have hcop : Nat.Coprime (2 ^ e) u := Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr hu)
  have hcard : (k + 1).divisors.card = (e + 1) * u.divisors.card := by
    rw [hku, hcop.card_divisors_mul, Nat.divisors_prime_pow Nat.prime_two, Finset.card_map,
      Finset.card_range]
  rw [hcard] at h2
  have he : 1 ≤ e := by
    by_contra h0
    have he0 : e = 0 := by omega
    subst he0
    rw [pow_zero, one_mul] at hku
    obtain ⟨c, hc⟩ := hu
    omega
  have hu1 : u = 1 := by
    by_contra hne
    have hu0 : u ≠ 0 := by
      rintro rfl
      simp at hku
    have h2le : 2 ≤ u.divisors.card := by
      have hsub : ({1, u} : Finset ℕ) ⊆ u.divisors := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact Nat.one_mem_divisors.mpr hu0
        · exact Nat.mem_divisors_self _ hu0
      have hc := Finset.card_le_card hsub
      rw [Finset.card_pair (Ne.symm hne)] at hc
      exact hc
    exact Nat.not_prime_mul (by omega) (by omega) h2
  subst hu1
  rw [mul_one] at hku
  rw [Nat.divisors_one, Finset.card_singleton, mul_one] at h2
  have hk' : k = 2 ^ e - 1 := by omega
  have he1 : e ≠ 1 := by
    rintro rfl
    norm_num at hku
    omega
  have hep := (Nat.prime_of_pow_sub_one_prime he1 (hk' ▸ hp)).2
  have he2 : e = 2 := by
    rcases hep.eq_two_or_odd with h | h
    · exact h
    · rcases h2.eq_two_or_odd with h' | h'
      · omega
      · omega
  subst he2
  norm_num at hku
  omega
