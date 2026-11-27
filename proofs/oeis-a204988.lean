import OMAStatements.S_oeis_a204988

-- Problem: A204988, a(n) = v2(n) + [n odd].
-- Credit: @bnb9001

namespace OMA_A204988_Proof

open OMA.S_oeis_a204988

lemma pow_sub_pow (j k : ℕ) (h : j ≤ k) : 2 ^ k - 2 ^ j = 2 ^ j * (2 ^ (k - j) - 1) := by
  rw [Nat.mul_sub_one, ← pow_add, Nat.add_sub_cancel' h]

lemma odd_pow_sub_one (d : ℕ) (hd : 1 ≤ d) : ¬ 2 ∣ 2 ^ d - 1 := by
  have : 2 ∣ 2 ^ d := dvd_pow_self 2 (by omega)
  have : 1 ≤ 2 ^ d := Nat.one_le_two_pow
  omega

end OMA_A204988_Proof

open OMA_A204988_Proof OMA.S_oeis_a204988 in
theorem OMA.solution : type_of% @OMA.S_oeis_a204988.main := by
  intro n hn
  obtain ⟨e, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd (show n ≠ 0 by omega)
  have hm0 : 0 < m := hm.pos
  have hv : padicValNat 2 n = e := by
    rw [hnm, padicValNat.mul (by positivity) hm0.ne', padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by rwa [← even_iff_two_dvd, Nat.not_even_iff_odd])]
    simp
  have hJval : padicValNat 2 n + (if n % 2 = 1 then 1 else 0) = max 1 e := by
    rw [hv]
    rcases Nat.eq_zero_or_pos e with he | he
    · subst he
      have h1 : n % 2 = 1 := by rw [hnm]; simpa using Nat.odd_iff.mp hm
      simp [h1]
    · have h2 : 2 ∣ n := hnm ▸ dvd_mul_of_dvd_left (dvd_pow_self 2 he.ne') m
      have h3 : ¬ n % 2 = 1 := by omega
      rw [if_neg h3]
      omega
  rw [hJval]
  set J := max 1 e with hJ
  have hcop : ∀ t, Nat.Coprime (2 ^ t) m := fun t =>
    Nat.Coprime.pow_left t (Nat.coprime_two_left.2 hm)
  have h2e : 2 ^ e ∣ n := Dvd.intro m hnm.symm
  have hmn : m ∣ n := Dvd.intro_left (2 ^ e) hnm.symm
  have L : ∀ j k, 1 ≤ j → j < k → n ∣ 2 ^ k - 2 ^ j → J ≤ j := by
    intro j k hj hjk hd
    rw [pow_sub_pow j k hjk.le] at hd
    have h1 : 2 ^ e ∣ 2 ^ j * (2 ^ (k - j) - 1) := h2e.trans hd
    have hodd : Nat.Coprime (2 ^ e) (2 ^ (k - j) - 1) :=
      Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2
        (odd_pow_sub_one _ (by omega)))
    have h2 : 2 ^ e ∣ 2 ^ j := hodd.dvd_of_dvd_mul_right h1
    have : e ≤ j := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h2
    omega
  have hφ : m ∣ 2 ^ Nat.totient m - 1 := by
    have := Nat.ModEq.pow_totient (Nat.coprime_two_left.2 hm)
    exact (Nat.modEq_iff_dvd' Nat.one_le_two_pow).1 this.symm
  have htot : 1 ≤ Nat.totient m := Nat.totient_pos.2 hm0
  have hmem : J + Nat.totient m ∈ {k : ℕ | ∃ j, 1 ≤ j ∧ j < k ∧ n ∣ 2 ^ k - 2 ^ j} := by
    refine ⟨J, by omega, by omega, ?_⟩
    rw [pow_sub_pow J _ (by omega), Nat.add_sub_cancel_left, hnm]
    exact mul_dvd_mul (Nat.pow_dvd_pow 2 (by omega)) hφ
  have hK : kmin n = sInf {k : ℕ | ∃ j, 1 ≤ j ∧ j < k ∧ n ∣ 2 ^ k - 2 ^ j} := rfl
  obtain ⟨j0, hj01, hj0K, hj0d⟩ := Nat.sInf_mem ⟨_, hmem⟩
  rw [← hK] at hj0K hj0d
  have M : ∀ j, 1 ≤ j → j < kmin n → n ∣ 2 ^ kmin n - 2 ^ j → j ≤ J := by
    intro j hj hjK hd
    by_contra hcon
    rw [not_le] at hcon
    have hdm : m ∣ 2 ^ (kmin n - j) - 1 := by
      rw [pow_sub_pow j _ hjK.le] at hd
      exact (hcop j).symm.dvd_of_dvd_mul_left (hmn.trans hd)
    have hmem' : kmin n - 1 ∈ {k : ℕ | ∃ j, 1 ≤ j ∧ j < k ∧ n ∣ 2 ^ k - 2 ^ j} := by
      refine ⟨j - 1, by omega, by omega, ?_⟩
      rw [pow_sub_pow (j - 1) _ (by omega), show kmin n - 1 - (j - 1) = kmin n - j by omega]
      have : 2 ^ e * m ∣ 2 ^ (j - 1) * (2 ^ (kmin n - j) - 1) :=
        mul_dvd_mul (Nat.pow_dvd_pow 2 (by omega)) hdm
      rwa [← hnm] at this
    have := Nat.sInf_le hmem'
    rw [← hK] at this
    omega
  have hj0 : j0 = J := le_antisymm (M j0 hj01 hj0K hj0d) (L j0 _ hj01 hj0K hj0d)
  rw [hj0] at hj01 hj0K hj0d
  apply le_antisymm
  · exact Nat.sInf_le ⟨hj01, hj0K, hj0d⟩
  · unfold a
    refine le_csInf ⟨J, hj01, hj0K, hj0d⟩ ?_
    rintro j ⟨hj1, hjK, hjd⟩
    exact L j _ hj1 hjK hjd
