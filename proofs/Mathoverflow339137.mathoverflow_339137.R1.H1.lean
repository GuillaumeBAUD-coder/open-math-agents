import OMAReductions.R_Mathoverflow339137_mathoverflow_339137_R1

-- Step Mathoverflow339137.mathoverflow_339137.R1.H1: hypothesis H1 of reduction Mathoverflow339137.mathoverflow_339137.R1
-- Credit: @marcusbuffett
--
-- If P = X + a (or P = 1) is monic with a nonnegative and (X + a) Q is a 0-1 polynomial with Q
-- monic and nonnegative, then a is 0 or 1 and Q is a 0-1 polynomial. Coefficients:
-- r_0 = a q_0 and r_(k+1) = q_k + a q_(k+1). For a positive, the coefficient at the degree d
-- of Q is at least a, so a is at most 1; at the first nonzero coefficient q_k0 of Q,
-- a q_k0 = 1 and q_k0 is at most r_(k0+1), so a is at least 1. With a = 1, induction on k
-- gives q_k in {0, 1}. The case where Q is the small factor follows by commutativity.
-- Written for this step.

open Polynomial Mathoverflow339137

namespace OMA.S_Mathoverflow339137_mathoverflow_339137_R1_H1

theorem isZeroOne_iff (p : ℝ[X]) : IsZeroOne p ↔ ∀ k, p.coeff k = 0 ∨ p.coeff k = 1 := by
  unfold IsZeroOne
  constructor
  · intro h k
    by_cases hk : p.coeff k = 0
    · exact Or.inl hk
    · exact Or.inr (Finset.mem_singleton.mp (h (coeff_mem_coeffs hk)))
  · intro h c hc
    obtain ⟨n, hn, rfl⟩ := mem_coeffs_iff.mp hc
    rcases h n with h0 | h1
    · exact absurd h0 (mem_support_iff.mp hn)
    · exact Finset.mem_singleton.mpr h1

theorem nonneg_coeff (p : ℝ[X]) (hp : ∀ c ∈ p.coeffs, 0 ≤ c) (k : ℕ) : 0 ≤ p.coeff k := by
  by_cases hk : p.coeff k = 0
  · rw [hk]
  · exact hp _ (coeff_mem_coeffs hk)

/-- Core case: `(X + a) Q` with `Q` monic and nonnegative is a `0,1` polynomial only if
`a ∈ {0, 1}` and `Q` is a `0,1` polynomial. -/
theorem linear_core (a : ℝ) (Q : ℝ[X]) (hQ : Q.Monic) (ha : 0 ≤ a)
    (hq : ∀ k, 0 ≤ Q.coeff k) (hR : ∀ k, ((X + C a) * Q).coeff k = 0 ∨ ((X + C a) * Q).coeff k = 1) :
    (a = 0 ∨ a = 1) ∧ ∀ k, Q.coeff k = 0 ∨ Q.coeff k = 1 := by
  have r0 : ((X + C a) * Q).coeff 0 = a * Q.coeff 0 := by
    simp [add_mul]
  have rs : ∀ k, ((X + C a) * Q).coeff (k + 1) = Q.coeff k + a * Q.coeff (k + 1) := by
    intro k; simp [add_mul, coeff_X_mul]
  -- the case `a = 0`
  rcases eq_or_lt_of_le ha with ha0 | hapos
  · subst ha0
    refine ⟨Or.inl rfl, fun k => ?_⟩
    have := hR (k + 1); rw [rs] at this; simpa using this
  -- `a ≤ 1`: the coefficient of `X ^ d` is at least `a`
  set d := Q.natDegree with hd
  have hqd : Q.coeff d = 1 := hQ.coeff_natDegree
  have ha1 : a ≤ 1 := by
    rcases Nat.eq_zero_or_pos d with h0 | h1
    · have := hR 0; rw [r0, ← h0, hqd] at this
      rcases this with h | h <;> linarith
    · obtain ⟨e, he⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
      have hr := hR (e + 1); rw [rs, ← he, hqd] at hr
      have := hq e
      rcases hr with h | h <;> nlinarith
  -- `a ≥ 1`: look at the first nonzero coefficient of `Q`
  have hex : ∃ k, Q.coeff k ≠ 0 := ⟨d, by rw [hqd]; norm_num⟩
  classical
  set k0 := Nat.find hex with hk0
  have hk0ne : Q.coeff k0 ≠ 0 := Nat.find_spec hex
  have hbelow : ∀ j < k0, Q.coeff j = 0 := fun j hj => by
    exact not_not.mp (Nat.find_min hex hj)
  have hpos : 0 < Q.coeff k0 := lt_of_le_of_ne (hq k0) (Ne.symm hk0ne)
  have hrk0 : ((X + C a) * Q).coeff k0 = a * Q.coeff k0 := by
    rcases Nat.eq_zero_or_pos k0 with h0 | h1
    · rw [h0, r0]
    · obtain ⟨e, he⟩ : ∃ e, k0 = e + 1 := ⟨k0 - 1, by omega⟩
      rw [he, rs, ← he, hbelow e (by omega)]; ring
  have hak : a * Q.coeff k0 = 1 := by
    have := hR k0; rw [hrk0] at this
    rcases this with h | h
    · exact absurd h (by positivity)
    · exact h
  have hqk1 : Q.coeff k0 ≤ 1 := by
    have hr := hR (k0 + 1); rw [rs] at hr
    have := hq (k0 + 1)
    rcases hr with h | h <;> nlinarith
  have ha_eq : a = 1 := by
    apply le_antisymm ha1
    nlinarith
  subst ha_eq
  refine ⟨Or.inr rfl, fun k => ?_⟩
  induction k with
  | zero => have := hR 0; rw [r0] at this; simpa using this
  | succ k ih =>
    have h := hR (k + 1); rw [rs] at h
    have := hq (k + 1)
    rcases ih with h0 | h1
    · rw [h0] at h; simpa using h
    · rw [h1] at h
      left; rcases h with h | h <;> linarith

theorem linear_case (P Q R : ℝ[X]) (hP : P.Monic) (hQ : Q.Monic)
    (hp : ∀ c ∈ P.coeffs, 0 ≤ c) (hq : ∀ c ∈ Q.coeffs, 0 ≤ c)
    (h : R = P * Q) (hR : IsZeroOne R) (hdeg : P.natDegree ≤ 1) :
    IsZeroOne P ∧ IsZeroOne Q := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hdeg with h0 | h1
  · have hP1 : P = 1 := eq_one_of_monic_natDegree_zero hP h0
    subst hP1
    rw [one_mul] at h; subst h
    refine ⟨?_, hR⟩
    rw [isZeroOne_iff]; intro k
    rw [coeff_one]; split_ifs <;> simp
  · have hPe := hP.eq_X_add_C h1
    set a := P.coeff 0
    have ha : 0 ≤ a := nonneg_coeff P hp 0
    rw [hPe] at h; subst h
    rw [isZeroOne_iff] at hR
    obtain ⟨hav, hQv⟩ := linear_core a Q hQ ha (nonneg_coeff Q hq) hR
    refine ⟨?_, (isZeroOne_iff Q).mpr hQv⟩
    rw [hPe, isZeroOne_iff]; intro k
    rcases k with _ | _ | k
    · simp only [coeff_add, coeff_X_zero, coeff_C_zero, zero_add]; exact hav
    · simp
    · simp [coeff_X]

end OMA.S_Mathoverflow339137_mathoverflow_339137_R1_H1

open OMA.S_Mathoverflow339137_mathoverflow_339137_R1_H1 in
theorem OMA.solution : OMA.R_Mathoverflow339137_mathoverflow_339137_R1.H1 := by
  intro P Q R hP hQ hp hq h hR hdeg
  rcases hdeg with hd | hd
  · exact linear_case P Q R hP hQ hp hq h hR hd
  · exact (linear_case Q P R hQ hP hq hp (by rw [h, mul_comm]) hR hd).symm
