import OMAStatements.S_oeis_a127905
import Mathlib

namespace OMA.S_oeis_a127905

/- Ratio lemmas for creative-telescoping term proofs (paste inside the helper namespace; needs `import Mathlib`).
   All in ℚ.  Atoms: x = C(N,k).  Typical use: express every binomial of the sum as (rational function)*x, then field_simp; ring. -/
lemma ch_succ (N k : ℕ) (hk : k ≤ N + 1) :   -- C(N,k)*(N+1) = C(N+1,k)*(N+1-k)
    (Nat.choose N k : ℚ) * ((N : ℚ) + 1) = Nat.choose (N + 1) k * (((N : ℚ) + 1) - k) := by
  have h := Nat.choose_mul_succ_eq N k
  have h' : ((Nat.choose N k * (N + 1) : ℕ) : ℚ) = ((Nat.choose (N + 1) k * (N + 1 - k) : ℕ) : ℚ) := by rw [h]
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hk] at h'
  push_cast at h'
  exact h'

lemma ch_up (N k : ℕ) :                      -- C(N+1,k+1)*(k+1) = (N+1)*C(N,k)
    ((Nat.choose (N + 1) (k + 1) : ℚ)) * ((k : ℚ) + 1) = ((N : ℚ) + 1) * Nat.choose N k := by
  have h := Nat.add_one_mul_choose_eq N k
  have h' : (((N + 1) * Nat.choose N k : ℕ) : ℚ) = ((Nat.choose (N + 1) (k + 1) * (k + 1) : ℕ) : ℚ) := by rw [h]
  push_cast at h'
  linarith

lemma ch_right (N k : ℕ) (hk : k ≤ N) :      -- C(N,k+1)*(k+1) = (N-k)*C(N,k)
    (Nat.choose N (k + 1) : ℚ) * ((k : ℚ) + 1) = ((N : ℚ) - k) * (Nat.choose N k : ℚ) := by
  have h := Nat.choose_succ_right_eq N k
  have h' : ((Nat.choose N (k + 1) * (k + 1) : ℕ) : ℚ) = ((Nat.choose N k * (N - k) : ℕ) : ℚ) := by rw [h]
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hk] at h'
  push_cast at h'
  linarith

/-- C(N,k) = C(N+1,k)*(N+1-k)/(N+1), for all k (both sides vanish for k > N+1). -/
lemma ch_down (N k : ℕ) :
    (Nat.choose N k : ℚ) = (Nat.choose (N + 1) k : ℚ) * (((N : ℚ) + 1) - k) / ((N : ℚ) + 1) := by
  rw [eq_div_iff (by positivity)]
  rcases Nat.lt_or_ge (N + 1) k with h | h
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt (by omega)]; simp
  · have := ch_succ N k h
    linarith

/-- C(N,k+1) = (N-k)*C(N,k)/(k+1), for all k. -/
lemma ch_next (N k : ℕ) :
    (Nat.choose N (k + 1) : ℚ) = ((N : ℚ) - k) * (Nat.choose N k : ℚ) / ((k : ℚ) + 1) := by
  rw [eq_div_iff (by positivity)]
  rcases Nat.lt_or_ge N k with h | h
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt (by omega)]; simp
  · exact ch_right N k h

/-- C(N+1,k) = C(N,k)*(N+1)/(N+1-k) for k ≤ N. -/
lemma ch_upN (N k : ℕ) (hk : k ≤ N) :
    (Nat.choose (N + 1) k : ℚ) = (Nat.choose N k : ℚ) * ((N : ℚ) + 1) / (((N : ℚ) + 1) - k) := by
  have : ((N : ℚ) + 1) - k ≠ 0 := by
    have : (k : ℚ) ≤ N := by exact_mod_cast hk
    linarith
  rw [eq_div_iff this]
  have := ch_succ N k (by omega)
  linarith

/-- support extension: sum over range N of a term that vanishes for k > n equals the sum over range (n+1). -/
lemma sum_ext {f : ℕ → ℚ} (n N : ℕ) (hN : n + 1 ≤ N) (hf : ∀ k, n < k → f k = 0) :
    ∑ k ∈ Finset.range N, f k = ∑ k ∈ Finset.range (n + 1), f k := by
  symm
  apply Finset.sum_subset (Finset.range_subset_range.mpr hN)
  intro k _ hk
  exact hf k (by simpa using hk)

noncomputable def Fq (m k : ℕ) : ℚ :=
  (3 * (k : ℚ) + 1) * (m.choose (3 * k + 1) : ℚ) * ((3 * k).choose k : ℚ) / (2 * (k : ℚ) + 1)
noncomputable def GG (m k : ℕ) : ℚ := -54 * (k : ℚ) ^ 2 * (2 * (k : ℚ) + 1) * Fq (m + 3) k

lemma cb3 (k : ℕ) : (((3 * (k + 1)).choose (k + 1) : ℕ) : ℚ) =
    ((3 * k).choose k : ℚ) * ((3 * (k : ℚ) + 3) * (3 * (k : ℚ) + 2) * (3 * (k : ℚ) + 1))
      / (((k : ℚ) + 1) * (2 * (k : ℚ) + 2) * (2 * (k : ℚ) + 1)) := by
  have h1 := ch_up (3 * k + 2) k
  have h2 := ch_down (3 * k + 1) k
  have h3 := ch_down (3 * k) k
  have e : 3 * (k + 1) = 3 * k + 2 + 1 := by ring
  rw [e]
  push_cast at h1 h2 h3 ⊢
  have hk : ((k : ℚ) + 1) ≠ 0 := by positivity
  have hk2 : (2 * (k : ℚ) + 2) ≠ 0 := by positivity
  have hk3 : (2 * (k : ℚ) + 1) ≠ 0 := by positivity
  have hk5 : (3 * (k : ℚ) + 1) ≠ 0 := by positivity
  have hk6 : (3 * (k : ℚ) + 2) ≠ 0 := by positivity
  have hu : (((3 * k + 1).choose k : ℕ) : ℚ) = ((3 * k).choose k : ℚ) * (3 * (k : ℚ) + 1) / (2 * (k : ℚ) + 1) := by
    rw [h3]; field_simp; ring
  have hv : (((3 * k + 2).choose k : ℕ) : ℚ) = (((3 * k + 1).choose k : ℕ) : ℚ) * (3 * (k : ℚ) + 2) / (2 * (k : ℚ) + 2) := by
    rw [h2]; field_simp; ring
  have hw : (((3 * k + 2 + 1).choose (k + 1) : ℕ) : ℚ) = (3 * (k : ℚ) + 2 + 1) * (((3 * k + 2).choose k : ℕ) : ℚ) / ((k : ℚ) + 1) := by
    rw [eq_div_iff hk]; exact h1
  rw [hw, hv, hu]
  field_simp
  ring

set_option maxRecDepth 100000 in
lemma term (m k : ℕ) :
    (-31 * ((m : ℚ) + 1) * ((m : ℚ) + 2) * ((m : ℚ) + 3)) * Fq m k
    + (6 * ((m : ℚ) + 2) * ((m : ℚ) + 3) * (2 * (m : ℚ) + 3)) * Fq (m + 1) k
    + (-2 * ((m : ℚ) + 3) * (6 * (m : ℚ) ^ 2 + 24 * (m : ℚ) + 23)) * Fq (m + 2) k
    + (2 * ((m : ℚ) + 2) ^ 2 * (2 * (m : ℚ) + 7)) * Fq (m + 3) k
    = GG m (k + 1) - GG m k := by
  have a2 : (((m + 2).choose (3 * k + 1) : ℕ) : ℚ) = (((m + 3).choose (3 * k + 1) : ℕ) : ℚ) * ((((m + 2 : ℕ) : ℚ) + 1) - ((3 * k + 1 : ℕ) : ℚ)) / (((m + 2 : ℕ) : ℚ) + 1) := ch_down (m + 2) (3 * k + 1)
  have a1 : (((m + 1).choose (3 * k + 1) : ℕ) : ℚ) = (((m + 2).choose (3 * k + 1) : ℕ) : ℚ) * ((((m + 1 : ℕ) : ℚ) + 1) - ((3 * k + 1 : ℕ) : ℚ)) / (((m + 1 : ℕ) : ℚ) + 1) := ch_down (m + 1) (3 * k + 1)
  have a0 : ((m.choose (3 * k + 1) : ℕ) : ℚ) = (((m + 1).choose (3 * k + 1) : ℕ) : ℚ) * (((m : ℚ) + 1) - ((3 * k + 1 : ℕ) : ℚ)) / ((m : ℚ) + 1) := ch_down m (3 * k + 1)
  have n1 := ch_next (m + 3) (3 * k + 1)
  have n2 := ch_next (m + 3) (3 * k + 1 + 1)
  have n3 := ch_next (m + 3) (3 * k + 1 + 1 + 1)
  have cb := cb3 k
  have e3 : 3 * (k + 1) + 1 = 3 * k + 1 + 1 + 1 + 1 := by ring
  unfold GG Fq
  rw [e3, n3, n2, n1, cb, a0, a1, a2]
  push_cast
  generalize (((m + 3).choose (3 * k + 1) : ℕ) : ℚ) = x
  generalize (((3 * k).choose k : ℕ) : ℚ) = B
  have hm1 : ((m : ℚ) + 1) ≠ 0 := by positivity
  have hm2 : ((m : ℚ) + 2) ≠ 0 := by positivity
  have hm3 : ((m : ℚ) + 3) ≠ 0 := by positivity
  have hk : ((k : ℚ) + 1) ≠ 0 := by positivity
  have hk1 : (2 * (k : ℚ) + 1) ≠ 0 := by positivity
  have hk2 : (2 * (k : ℚ) + 3) ≠ 0 := by positivity
  have hk3 : (3 * (k : ℚ) + 1 + 1) ≠ 0 := by positivity
  have hk4 : (3 * (k : ℚ) + 1 + 1 + 1) ≠ 0 := by positivity
  have hk5 : (3 * (k : ℚ) + 1 + 1 + 1 + 1) ≠ 0 := by positivity
  have hk6 : (2 * (k : ℚ) + 2) ≠ 0 := by positivity
  have hk7 : (3 * (k : ℚ) + 1) ≠ 0 := by positivity
  field_simp
  ring

lemma ext_a (m i : ℕ) (hi : i ≤ 3) : a (m + i) = ∑ k ∈ Finset.range (m + 4), Fq (m + i) k := by
  unfold a Fq
  symm
  apply sum_ext (f := fun k => (3 * (k : ℚ) + 1) * ((m + i).choose (3 * k + 1) : ℚ) * ((3 * k).choose k : ℚ) / (2 * (k : ℚ) + 1)) ((m + i - 1) / 3) (m + 4) (by omega)
  intro k hk
  have : (m + i) < 3 * k + 1 := by omega
  simp [Nat.choose_eq_zero_of_lt this]

lemma rec_S (m : ℕ) :
    (-31 * ((m : ℚ) + 1) * ((m : ℚ) + 2) * ((m : ℚ) + 3)) * a m
    + (6 * ((m : ℚ) + 2) * ((m : ℚ) + 3) * (2 * (m : ℚ) + 3)) * a (m + 1)
    + (-2 * ((m : ℚ) + 3) * (6 * (m : ℚ) ^ 2 + 24 * (m : ℚ) + 23)) * a (m + 2)
    + (2 * ((m : ℚ) + 2) ^ 2 * (2 * (m : ℚ) + 7)) * a (m + 3) = 0 := by
  have s0 := ext_a m 0 (by omega)
  simp only [Nat.add_zero] at s0
  rw [s0, ext_a m 1 (by omega), ext_a m 2 (by omega), ext_a m 3 (by omega)]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun k _ => term m k)]
  rw [Finset.sum_range_sub (fun k => GG m k)]
  have h0 : GG m 0 = 0 := by simp [GG]
  have h1 : GG m (m + 4) = 0 := by
    simp [GG, Fq, Nat.choose_eq_zero_of_lt (show m + 3 < 3 * (m + 4) + 1 by omega)]
  rw [h0, h1]; ring

end OMA.S_oeis_a127905

theorem OMA.solution : type_of% @OMA.S_oeis_a127905.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have h := OMA.S_oeis_a127905.rec_S m
  rw [show m + 3 - 1 = m + 2 from rfl, show m + 3 - 2 = m + 1 from rfl, show m + 3 - 3 = m from rfl]
  push_cast
  linear_combination h
