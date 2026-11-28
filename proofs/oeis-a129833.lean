import OMAStatements.S_oeis_a129833
import Mathlib

namespace OMA.S_oeis_a129833

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

noncomputable def Fq (m k : ℕ) : ℚ := ((m + 1).choose (k + 1) : ℚ) * (m.choose k : ℚ) * (k.factorial : ℚ)
noncomputable def GG (m k : ℕ) : ℚ := (-((k:ℚ))^5*((m:ℚ))^2 - 4*((k:ℚ))^5*((m:ℚ)) - 2*((k:ℚ))^5 + 4*((k:ℚ))^4*((m:ℚ))^3 + 24*((k:ℚ))^4*((m:ℚ))^2 + 40*((k:ℚ))^4*((m:ℚ)) + 16*((k:ℚ))^4 - 5*((k:ℚ))^3*((m:ℚ))^4 - 38*((k:ℚ))^3*((m:ℚ))^3 - 97*((k:ℚ))^3*((m:ℚ))^2 - 100*((k:ℚ))^3*((m:ℚ)) - 43*((k:ℚ))^3 + 2*((k:ℚ))^2*((m:ℚ))^5 + 15*((k:ℚ))^2*((m:ℚ))^4 + 32*((k:ℚ))^2*((m:ℚ))^3 + 9*((k:ℚ))^2*((m:ℚ))^2 - 10*((k:ℚ))^2*((m:ℚ)) + 26*((k:ℚ))^2 + 2*((k:ℚ))*((m:ℚ))^5 + 20*((k:ℚ))*((m:ℚ))^4 + 74*((k:ℚ))*((m:ℚ))^3 + 131*((k:ℚ))*((m:ℚ))^2 + 134*((k:ℚ))*((m:ℚ)) + 87*((k:ℚ))) / ((((m:ℚ)) + 3)^2*(((m:ℚ)) + 4)) * Fq (m + 3) k

set_option maxRecDepth 100000 in
lemma term (m k : ℕ) :
    (-(((m:ℚ)) + 1)*(((m:ℚ)) + 2)^2*(((m:ℚ))^2 + 4*((m:ℚ)) + 2)) * Fq m k + ((((m:ℚ)) + 2)*(((m:ℚ)) + 3)*(((m:ℚ))^3 + 7*((m:ℚ))^2 + 13*((m:ℚ)) + 1)) * Fq (m + 1) k + (-(((m:ℚ)) + 3)*(2*((m:ℚ))^3 + 13*((m:ℚ))^2 + 18*((m:ℚ)) - 6)) * Fq (m + 2) k + ((((m:ℚ)) + 4)*(((m:ℚ))^2 + 2*((m:ℚ)) - 1)) * Fq (m + 3) k
    = GG m (k + 1) - GG m k := by
  have a2 : (((m + 2).choose k : ℕ) : ℚ) = (((m + 3).choose k : ℕ) : ℚ) * ((((m + 2 : ℕ) : ℚ) + 1) - (k : ℚ)) / (((m + 2 : ℕ) : ℚ) + 1) := ch_down (m + 2) k
  have a1 : (((m + 1).choose k : ℕ) : ℚ) = (((m + 2).choose k : ℕ) : ℚ) * ((((m + 1 : ℕ) : ℚ) + 1) - (k : ℚ)) / (((m + 1 : ℕ) : ℚ) + 1) := ch_down (m + 1) k
  have a0 : ((m.choose k : ℕ) : ℚ) = (((m + 1).choose k : ℕ) : ℚ) * (((m : ℚ) + 1) - (k : ℚ)) / ((m : ℚ) + 1) := ch_down m k
  have b2 : (((m + 2).choose (k + 1) : ℕ) : ℚ) = (((m + 3).choose (k + 1) : ℕ) : ℚ) * ((((m + 2 : ℕ) : ℚ) + 1) - ((k + 1 : ℕ) : ℚ)) / (((m + 2 : ℕ) : ℚ) + 1) := ch_down (m + 2) (k + 1)
  have b1 : (((m + 1).choose (k + 1) : ℕ) : ℚ) = (((m + 2).choose (k + 1) : ℕ) : ℚ) * ((((m + 1 : ℕ) : ℚ) + 1) - ((k + 1 : ℕ) : ℚ)) / (((m + 1 : ℕ) : ℚ) + 1) := ch_down (m + 1) (k + 1)
  have n1 := ch_next (m + 4) (k + 1)
  have n2 := ch_next (m + 3) k
  have hk : ((k : ℚ) + 1) ≠ 0 := by positivity
  have hy : (((m + 4).choose (k + 1) : ℕ) : ℚ) = ((m : ℚ) + 4) * (((m + 3).choose k : ℕ) : ℚ) / ((k : ℚ) + 1) := by
    rw [eq_div_iff hk]
    have h' : (((m + 3 + 1).choose (k + 1) : ℕ) : ℚ) * ((k : ℚ) + 1) = (((m + 3 : ℕ) : ℚ) + 1) * (((m + 3).choose k : ℕ) : ℚ) := ch_up (m + 3) k
    push_cast at h'
    have e4 : m + 3 + 1 = m + 4 := rfl
    rw [e4] at h'
    linarith
  have f1 : ((k + 1).factorial : ℚ) = ((k : ℚ) + 1) * (k.factorial : ℚ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  unfold GG Fq
  rw [show m + 1 + 1 = m + 2 from rfl, show m + 2 + 1 = m + 3 from rfl, show m + 3 + 1 = m + 4 from rfl]
  rw [n1, hy, f1, b1, b2, n2, a0, a1, a2]
  push_cast
  generalize (((m + 3).choose k : ℕ) : ℚ) = x
  generalize (k.factorial : ℚ) = w
  have hm1 : ((m : ℚ) + 1) ≠ 0 := by positivity
  have hm2 : ((m : ℚ) + 2) ≠ 0 := by positivity
  have hm3 : ((m : ℚ) + 3) ≠ 0 := by positivity
  have hm4 : ((m : ℚ) + 4) ≠ 0 := by positivity
  have hm21 : ((m : ℚ) + 2 + 1) ≠ 0 := by positivity
  have hm11 : ((m : ℚ) + 1 + 1) ≠ 0 := by positivity
  have hm31 : ((m : ℚ) + 3 + 1) ≠ 0 := by positivity
  have hk2 : ((k : ℚ) + 1 + 1) ≠ 0 := by positivity
  field_simp
  ring

lemma ext_a (m i : ℕ) (hi : i ≤ 3) : a (m + i) = ∑ k ∈ Finset.range (m + 4), Fq (m + i) k := by
  unfold a Fq
  symm
  apply sum_ext (f := fun k => ((m + i + 1).choose (k + 1) : ℚ) * ((m + i).choose k : ℚ) * (k.factorial : ℚ)) (m + i) (m + 4) (by omega)
  intro k hk
  simp [Nat.choose_eq_zero_of_lt hk]

lemma rec_S (m : ℕ) :
    (-(((m:ℚ)) + 1)*(((m:ℚ)) + 2)^2*(((m:ℚ))^2 + 4*((m:ℚ)) + 2)) * a m + ((((m:ℚ)) + 2)*(((m:ℚ)) + 3)*(((m:ℚ))^3 + 7*((m:ℚ))^2 + 13*((m:ℚ)) + 1)) * a (m + 1) + (-(((m:ℚ)) + 3)*(2*((m:ℚ))^3 + 13*((m:ℚ))^2 + 18*((m:ℚ)) - 6)) * a (m + 2) + ((((m:ℚ)) + 4)*(((m:ℚ))^2 + 2*((m:ℚ)) - 1)) * a (m + 3) = 0 := by
  have s0 := ext_a m 0 (by omega)
  simp only [Nat.add_zero] at s0
  rw [s0, ext_a m 1 (by omega), ext_a m 2 (by omega), ext_a m 3 (by omega)]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun k _ => term m k)]
  rw [Finset.sum_range_sub (fun k => GG m k)]
  have h0 : GG m 0 = 0 := by simp [GG]
  have h1 : GG m (m + 4) = 0 := by
    simp [GG, Fq, Nat.choose_eq_zero_of_lt (show m + 4 < m + 4 + 1 by omega)]
  rw [h0, h1]; ring

lemma rec_S' (m : ℕ) (x : ℚ) (hx : x = (m : ℚ)) :
    (-(x + 1) * (x + 2) ^ 2 * (x ^ 2 + 4 * x + 2)) * a m + ((x + 2) * (x + 3) * (x ^ 3 + 7 * x ^ 2 + 13 * x + 1)) * a (m + 1)
      + (-(x + 3) * (2 * x ^ 3 + 13 * x ^ 2 + 18 * x - 6)) * a (m + 2) + ((x + 4) * (x ^ 2 + 2 * x - 1)) * a (m + 3) = 0 := by
  subst hx; exact rec_S m

end OMA.S_oeis_a129833

theorem OMA.solution : type_of% @OMA.S_oeis_a129833.main := by
  refine ⟨fun n hn => ?_, fun n hn => ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    have h0 := OMA.S_oeis_a129833.rec_S' m (m : ℚ) rfl
    have h1 := OMA.S_oeis_a129833.rec_S' (m + 1) ((m : ℚ) + 1) (by push_cast; ring)
    have h2 := OMA.S_oeis_a129833.rec_S' (m + 2) ((m : ℚ) + 2) (by push_cast; ring)
    rw [show m + 1 + 1 = m + 2 from rfl, show m + 1 + 2 = m + 3 from rfl, show m + 1 + 3 = m + 4 from rfl] at h1
    rw [show m + 2 + 1 = m + 3 from rfl, show m + 2 + 2 = m + 4 from rfl, show m + 2 + 3 = m + 5 from rfl] at h2
    rw [show m + 5 - 1 = m + 4 from rfl, show m + 5 - 2 = m + 3 from rfl, show m + 5 - 3 = m + 2 from rfl,
      show m + 5 - 4 = m + 1 from rfl, show m + 5 - 5 = m from rfl]
    dsimp only
    push_cast
    have hd0 : ((m : ℚ) ^ 2 + 4 * m + 2) ≠ 0 := by positivity
    have hd1 : ((m : ℚ) ^ 2 + 6 * m + 7) ≠ 0 := by positivity
    apply mul_left_cancel₀ (mul_ne_zero hd0 hd1)
    linear_combination ((m : ℚ) ^ 2 + 6 * m + 7) * h0 - (2 * (m : ℚ) ^ 2 + 10 * m + 7) * h1 + ((m : ℚ) ^ 2 + 4 * m + 2) * h2
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    have h := OMA.S_oeis_a129833.rec_S m
    rw [show m + 3 - 1 = m + 2 from rfl, show m + 3 - 2 = m + 1 from rfl, show m + 3 - 3 = m from rfl]
    dsimp only
    push_cast
    linear_combination h
