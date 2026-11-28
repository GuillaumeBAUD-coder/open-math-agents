import OMAStatements.S_oeis_a079491

namespace BC079491

theorem ch2 (a b : ℕ) : (a + b).choose 2 = a.choose 2 + b.choose 2 + a * b := by
  induction b with
  | zero =>
    rw [show Nat.choose 0 2 = 0 from rfl]
    simp
  | succ b ih =>
    have h1 : (a + (b + 1)).choose 2 = (a + b).choose 1 + (a + b).choose 2 :=
      Nat.choose_succ_succ (a + b) 1
    have h2 : (b + 1).choose 2 = b.choose 1 + b.choose 2 := Nat.choose_succ_succ b 1
    rw [h1, h2, ih, Nat.choose_one_right, Nat.choose_one_right]
    ring

theorem expo (n k : ℕ) (hk : k ≤ n) :
    n.choose 2 - k.choose 2 = (n - k) * (n - (n - k)) + (n - k).choose 2 := by
  obtain ⟨j, rfl⟩ : ∃ j, n = k + j := ⟨n - k, by omega⟩
  rw [show k + j - k = j by omega, show k + j - j = k by omega, ch2 k j, Nat.mul_comm j k]
  omega

end BC079491

theorem OMA.solution : type_of% @OMA.S_oeis_a079491.main := by
  intro n
  set N := (∑ k ∈ Finset.range (n + 1), Nat.choose n k * 2 ^ (k * (n - k) + Nat.choose k 2) : ℕ)
    with hN
  have hA : OMA.S_oeis_a079491.ratSum n = (N : ℚ) / (2 : ℚ) ^ (n.choose 2) := by
    rw [eq_div_iff (pow_ne_zero _ two_ne_zero)]
    unfold OMA.S_oeis_a079491.ratSum
    rw [Finset.sum_mul, hN]
    push_cast
    conv_rhs => rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ n := by
      have := Finset.mem_range.mp hk
      omega
    rw [show n + 1 - 1 - k = n - k by omega, Nat.choose_symm hk', ← BC079491.expo n k hk',
      ← Nat.choose_two_right]
    have hc : k.choose 2 ≤ n.choose 2 := Nat.choose_le_choose 2 hk'
    obtain ⟨e, he⟩ : ∃ e, n.choose 2 = k.choose 2 + e := ⟨n.choose 2 - k.choose 2, by omega⟩
    rw [show n.choose 2 - k.choose 2 = e by omega, he, pow_add]
    first
    | (field_simp; done)
    | (field_simp; ring)
  have hcop : Nat.Coprime N (2 ^ (n.choose 2)) := by
    rcases Nat.lt_or_ge n 2 with hn | hn
    · rw [Nat.choose_eq_zero_of_lt hn, pow_zero]
      exact Nat.coprime_one_right N
    · have h2 : 2 ∣ ∑ k ∈ Finset.range n,
          n.choose (k + 1) * 2 ^ ((k + 1) * (n - (k + 1)) + (k + 1).choose 2) := by
        apply Finset.dvd_sum
        intro k hk
        have hk' : k < n := Finset.mem_range.mp hk
        apply Dvd.dvd.mul_left
        apply dvd_pow_self
        rcases Nat.lt_or_ge (k + 1) n with h | h
        · have : 0 < (k + 1) * (n - (k + 1)) := Nat.mul_pos (by omega) (by omega)
          omega
        · have hkn : k + 1 = n := by omega
          rw [hkn]
          have : 0 < n.choose 2 := Nat.choose_pos hn
          omega
      have h0 : n.choose 0 * 2 ^ (0 * (n - 0) + Nat.choose 0 2) = 1 := by
        rw [Nat.choose_zero_right, show Nat.choose 0 2 = 0 from rfl]
        simp
      have hodd : N % 2 = 1 := by
        rw [hN, Finset.sum_range_succ', h0]
        omega
      exact Nat.Coprime.pow_right _
        (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)))
  rw [hA]
  have key := Rat.num_div_eq_of_coprime (a := (N : ℤ)) (b := ((2 ^ (n.choose 2) : ℕ) : ℤ))
    (by positivity) (by simpa using hcop)
  push_cast at key ⊢
  exact key
