import OMAStatements.S_oeis_a103821
import Mathlib

namespace OMA.S_oeis_a103821

lemma chr (N m : ℕ) : (Nat.choose N (m + 1) : ℚ) * ((m : ℚ) + 1) = ((N : ℚ) - m) * Nat.choose N m := by
  rcases Nat.lt_or_ge N m with h | h
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt h]; simp
  · have h1 := Nat.choose_succ_right_eq N m
    have h2 : ((Nat.choose N (m + 1) * (m + 1) : ℕ) : ℚ) = ((Nat.choose N m * (N - m) : ℕ) : ℚ) := by rw [h1]
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub h] at h2
    push_cast at h2; linarith

lemma pas (k n : ℕ) : (Nat.choose (2 * (k + 1)) (n + 2) : ℚ)
    = Nat.choose (2 * k) n + 2 * Nat.choose (2 * k) (n + 1) + Nat.choose (2 * k) (n + 2) := by
  have e : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
  rw [e]
  simp only [Nat.choose_succ_succ']
  push_cast; ring

lemma ch_succ (N k : ℕ) (hk : k ≤ N + 1) :
    (Nat.choose N k : ℚ) * ((N : ℚ) + 1) = Nat.choose (N + 1) k * (((N : ℚ) + 1) - k) := by
  have h := Nat.choose_mul_succ_eq N k
  have h' : ((Nat.choose N k * (N + 1) : ℕ) : ℚ) = ((Nat.choose (N + 1) k * (N + 1 - k) : ℕ) : ℚ) := by
    rw [h]
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hk] at h'
  push_cast at h'
  exact h'

lemma ch_up (N k : ℕ) :
    ((Nat.choose (N + 1) (k + 1) : ℚ)) * ((k : ℚ) + 1) = ((N : ℚ) + 1) * Nat.choose N k := by
  have h := Nat.add_one_mul_choose_eq N k
  have h' : (((N + 1) * Nat.choose N k : ℕ) : ℚ) = ((Nat.choose (N + 1) (k + 1) * (k + 1) : ℕ) : ℚ) := by
    rw [h]
  push_cast at h'
  linarith

noncomputable def F (n k : ℕ) : ℚ := (Nat.choose n k : ℚ) * Nat.choose (2 * k) n
noncomputable def G (n k : ℕ) : ℚ := ((n : ℚ) + 2) * (Nat.choose (n + 2) k : ℚ) * Nat.choose (2 * k) (n + 2)

lemma term (n k : ℕ) :
    4 * ((n : ℚ) + 1) * F n k + 2 * (2 * (n : ℚ) + 3) * F (n + 1) k - ((n : ℚ) + 2) * F (n + 2) k
      = G n (k + 1) - G n k := by
  unfold F G
  have hB := chr (2 * k) n
  have hD := chr (2 * k) (n + 1)
  have hE := pas k n
  push_cast at hB hD hE
  set A : ℚ := (Nat.choose (2 * k) n : ℚ) with hA
  set B : ℚ := (Nat.choose (2 * k) (n + 1) : ℚ) with hBd
  set D : ℚ := (Nat.choose (2 * k) (n + 2) : ℚ) with hDd
  have hn1 : ((n : ℚ) + 1) ≠ 0 := by positivity
  have hn2 : ((n : ℚ) + 2) ≠ 0 := by positivity
  have hB' : B = ((2 * (k : ℚ)) - n) * A / ((n : ℚ) + 1) := by
    rw [eq_div_iff hn1]; push_cast at hB; linarith
  have hD' : D = ((2 * (k : ℚ)) - (n + 1)) * B / ((n : ℚ) + 2) := by
    rw [eq_div_iff hn2]; push_cast at hD; linarith
  rw [hE]
  rcases Nat.lt_or_ge n k with h | h
  · -- k > n
    rcases Nat.lt_or_ge (n + 1) k with h1 | h1
    · rcases Nat.lt_or_ge (n + 2) k with h2 | h2
      · rw [Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt h1, Nat.choose_eq_zero_of_lt h2,
          Nat.choose_eq_zero_of_lt (show n + 2 < k + 1 by omega)]
        simp
      · have hk : k = n + 2 := by omega
        subst hk
        rw [Nat.choose_eq_zero_of_lt (show n < n + 2 by omega), Nat.choose_eq_zero_of_lt (show n + 1 < n + 2 by omega),
          Nat.choose_self, Nat.choose_eq_zero_of_lt (show n + 2 < n + 2 + 1 by omega)]
        have hr := hD'; have hb := hB'
        rw [hb] at hr
        push_cast
        rw [hr, hb]; push_cast; field_simp; ring
    · have hk : k = n + 1 := by omega
      subst hk
      have e1 : Nat.choose (n + 2) (n + 1) = n + 2 := by simpa using Nat.choose_succ_self_right (n + 1)
      rw [Nat.choose_eq_zero_of_lt (show n < n + 1 by omega), Nat.choose_self, e1,
        show n + 1 + 1 = n + 2 from rfl, Nat.choose_self]
      have hr := hD'; have hb := hB'
      rw [hb] at hr
      push_cast
      rw [hr, hb]; push_cast; field_simp; ring
  · have hk1 : k ≤ n + 1 := by omega
    have c1 := ch_succ n k hk1
    have c2 := ch_succ (n + 1) k (by omega)
    have c3 := ch_up (n + 1) k
    push_cast at c1 c2 c3
    set X : ℚ := (Nat.choose n k : ℚ) with hX
    set Y : ℚ := (Nat.choose (n + 1) k : ℚ) with hY
    set Z : ℚ := (Nat.choose (n + 1 + 1) k : ℚ) with hZ
    have hkk : (0 : ℚ) < (k : ℚ) + 1 := by positivity
    have hk' : (k : ℚ) ≤ n := by exact_mod_cast h
    have p1 : ((n : ℚ) + 1 - k) ≠ 0 := by linarith
    have p2 : ((n : ℚ) + 1 + 1 - k) ≠ 0 := by linarith
    have hY' : Y = X * ((n : ℚ) + 1) / ((n : ℚ) + 1 - k) := by
      rw [eq_div_iff p1]; linarith
    have hZ' : Z = Y * ((n : ℚ) + 1 + 1) / ((n : ℚ) + 1 + 1 - k) := by
      rw [eq_div_iff p2]; linarith
    have hW : (Nat.choose (n + 1 + 1) (k + 1) : ℚ) = ((n : ℚ) + 1 + 1) * Y / ((k : ℚ) + 1) := by
      rw [eq_div_iff hkk.ne']; linarith
    have e2 : n + 2 = n + 1 + 1 := rfl
    rw [e2, hW, hZ', hY', hD', hB']
    push_cast
    field_simp
    ring

noncomputable def S (n : ℕ) : ℚ := ∑ k ∈ Finset.range (n + 1), F n k

lemma F_zero (n k : ℕ) (h : n < k) : F n k = 0 := by
  unfold F; rw [Nat.choose_eq_zero_of_lt h]; simp

lemma S_ext (n N : ℕ) (hN : n + 1 ≤ N) : ∑ k ∈ Finset.range N, F n k = S n := by
  unfold S
  symm
  apply Finset.sum_subset (Finset.range_subset_range.mpr hN)
  intro k _ hk
  exact F_zero n k (by simpa using hk)

lemma rec_S (m : ℕ) :
    4 * ((m : ℚ) + 1) * S m + 2 * (2 * (m : ℚ) + 3) * S (m + 1) - ((m : ℚ) + 2) * S (m + 2) = 0 := by
  rw [← S_ext m (m + 3) (by omega), ← S_ext (m + 1) (m + 3) (by omega), ← S_ext (m + 2) (m + 3) (by omega)]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl (fun k _ => term m k)]
  rw [Finset.sum_range_sub (fun k => G m k)]
  have h0 : G m 0 = 0 := by simp [G]
  have h1 : G m (m + 3) = 0 := by
    simp [G, Nat.choose_eq_zero_of_lt (show m + 2 < m + 3 by omega)]
  rw [h0, h1]; ring

def cf (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), ((2 * k).choose k : ℤ) * (k.choose (n - k) : ℤ)

lemma sw (n k : ℕ) (hk : k ≤ n) : ((2 * k).choose k : ℕ) * k.choose (n - k) = n.choose k * (2 * k).choose n := by
  have := Nat.choose_mul (n := 2 * k) (k := n) (s := k) hk
  rw [show 2 * k - k = k by omega] at this
  rw [mul_comm (n.choose k), this]

lemma S_cf (n : ℕ) : S n = (cf n : ℚ) := by
  unfold S cf
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  have hk := Finset.mem_range.mp hk
  have := sw n k (by omega)
  unfold F
  have h2 : (((2 * k).choose k : ℕ) : ℚ) * (k.choose (n - k) : ℕ) = (n.choose k : ℕ) * ((2 * k).choose n : ℕ) := by
    exact_mod_cast this
  rw [← h2]

lemma a_diff (n : ℕ) : a (n + 1) - a n = cf (n + 1) := by
  unfold a cf
  rw [Finset.sum_range_succ, Finset.sum_range_succ (fun k => ((2 * k).choose k : ℤ) * (k.choose (n + 1 - k) : ℤ))]
  have h : ∀ k ∈ Finset.range (n + 1), ((2 * k).choose k : ℤ) * ∑ i ∈ Finset.Icc k (n + 1), (k.choose (i - k) : ℤ)
      = ((2 * k).choose k : ℤ) * ∑ i ∈ Finset.Icc k n, (k.choose (i - k) : ℤ) + ((2 * k).choose k : ℤ) * (k.choose (n + 1 - k) : ℤ) := by
    intro k hk
    have hk := Finset.mem_range.mp hk
    rw [Finset.sum_Icc_succ_top (by omega), mul_add]
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib]
  simp
  ring

end OMA.S_oeis_a103821

theorem OMA.solution : type_of% @OMA.S_oeis_a103821.main := by
  intro n hn
  open OMA.S_oeis_a103821 in
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have h := rec_S (m + 1)
  rw [S_cf, S_cf, S_cf] at h
  have d1 := a_diff (m + 2)
  have d2 := a_diff (m + 1)
  have d3 := a_diff m
  have h' : (4 * ((m : ℤ) + 2) * cf (m + 1) + 2 * (2 * ((m : ℤ) + 1) + 3) * cf (m + 1 + 1) - ((m : ℤ) + 1 + 2) * cf (m + 1 + 2) : ℤ) = 0 := by
    have : ((4 * ((m : ℤ) + 2) * cf (m + 1) + 2 * (2 * ((m : ℤ) + 1) + 3) * cf (m + 1 + 1) - ((m : ℤ) + 1 + 2) * cf (m + 1 + 2) : ℤ) : ℚ) = 0 := by
      push_cast at h ⊢
      linarith
    exact_mod_cast this
  have e1 : m + 3 - 1 = m + 2 := rfl
  have e2 : m + 3 - 2 = m + 1 := rfl
  have e3 : m + 3 - 3 = m := rfl
  rw [e1, e2, e3]
  have f1 : cf (m + 1 + 2) = a (m + 3) - a (m + 2) := by rw [← d1]
  have f2 : cf (m + 1 + 1) = a (m + 2) - a (m + 1) := by rw [← d2]
  have f3 : cf (m + 1) = a (m + 1) - a m := by rw [← d3]
  rw [f1, f2, f3] at h'
  push_cast
  linear_combination (-1 : ℤ) * h'
