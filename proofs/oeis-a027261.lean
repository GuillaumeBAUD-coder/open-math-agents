import OMAStatements.S_oeis_a027261
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: T(n,k) are the coefficients of (1+x^2)(1+x+x^2)^(n-1). With S0 = sum T and S1 = sum k T (support lemma T(n+1,k)=0 for k>2n+2, index shifts via sum_range_succ'), S0(m+2)=3S0(m+1), S1(m+2)=3S1(m+1)+3S0(m+1), so a(m+1)=S1+S0=2(m+2)3^m; recurrence and g.f. follow (coefficient comparison).

namespace OMA.P_oeis_a027261

open OMA.S_oeis_a027261

lemma T_succ_zero (n k : ℕ) (hk : 2 * n + 2 < k) : T (n + 1) k = 0 := by
  induction n generalizing k with
  | zero => simp [T]; omega
  | succ m ih =>
    simp only [T]
    rw [ih (k - 2) (by omega), ih (k - 1) (by omega), ih k (by omega)]
    simp

lemma shift2 (f : ℕ → ℤ) (N : ℕ) :
    ∑ k ∈ Finset.range (N + 2), (if 2 ≤ k then f (k - 2) else 0) = ∑ j ∈ Finset.range N, f j := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp

lemma shift1 (f : ℕ → ℤ) (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1), (if 1 ≤ k then f (k - 1) else 0) = ∑ j ∈ Finset.range N, f j := by
  rw [Finset.sum_range_succ']
  simp

def S0 (n : ℕ) : ℤ := ∑ k ∈ Finset.range (2 * n + 1), T n k
def S1 (n : ℕ) : ℤ := ∑ k ∈ Finset.range (2 * n + 1), (k : ℤ) * T n k

lemma S0_succ (m : ℕ) : S0 (m + 2) = 3 * S0 (m + 1) := by
  have z1 := T_succ_zero m (2 * m + 3) (by omega)
  have z2 := T_succ_zero m (2 * m + 4) (by omega)
  have h : ∀ k, T (m + 2) k = (if 2 ≤ k then T (m + 1) (k - 2) else 0) +
      (if 1 ≤ k then T (m + 1) (k - 1) else 0) + T (m + 1) k := fun k => by simp only [T]
  unfold S0
  simp only [h, Finset.sum_add_distrib]
  rw [show 2 * (m + 2) + 1 = (2 * (m + 1) + 1) + 2 by ring, shift2,
    show 2 * (m + 1) + 1 + 2 = (2 * (m + 1) + 1 + 1) + 1 by ring, shift1]
  simp only [Finset.sum_range_succ]
  rw [show 2 * (m + 1) + 1 = 2 * m + 3 by ring, z1]
  simp only [show 2 * (m + 1) + 2 = 2 * m + 4 by ring, z2]
  ring

lemma S1_succ (m : ℕ) : S1 (m + 2) = 3 * S1 (m + 1) + 3 * S0 (m + 1) := by
  have z1 := T_succ_zero m (2 * m + 3) (by omega)
  have z2 := T_succ_zero m (2 * m + 4) (by omega)
  have h : ∀ k : ℕ, (k : ℤ) * T (m + 2) k =
      (if 2 ≤ k then ((k - 2 : ℕ) + 2 : ℤ) * T (m + 1) (k - 2) else 0) +
      (if 1 ≤ k then ((k - 1 : ℕ) + 1 : ℤ) * T (m + 1) (k - 1) else 0) + (k : ℤ) * T (m + 1) k := by
    intro k
    simp only [T]
    split_ifs with h1 h2 h2
    · push_cast [Nat.cast_sub h1, Nat.cast_sub h2]; ring
    · omega
    · push_cast [Nat.cast_sub h2]; ring
    · have : k = 0 := by omega
      subst this; simp
  unfold S1 S0
  simp only [h, Finset.sum_add_distrib]
  rw [show 2 * (m + 2) + 1 = (2 * (m + 1) + 1) + 2 by ring,
    shift2 (fun j => ((j : ℕ) + 2 : ℤ) * T (m + 1) j),
    show 2 * (m + 1) + 1 + 2 = (2 * (m + 1) + 1 + 1) + 1 by ring,
    shift1 (fun j => ((j : ℕ) + 1 : ℤ) * T (m + 1) j)]
  simp only [Finset.sum_range_succ, add_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [show 2 * (m + 1) + 1 = 2 * m + 3 by ring, z1]
  simp only [show 2 * (m + 1) + 2 = 2 * m + 4 by ring, z2]
  ring

lemma closed (m : ℕ) : S0 (m + 1) = 2 * 3 ^ m ∧ S1 (m + 1) = 2 * ((m : ℤ) + 1) * 3 ^ m := by
  induction m with
  | zero =>
    refine ⟨?_, ?_⟩ <;> simp only [S0, S1, Finset.sum_range_succ, Finset.sum_range_zero] <;> simp [T]
  | succ k ih =>
    rw [S0_succ, S1_succ, ih.1, ih.2]
    constructor <;> push_cast <;> ring

lemma a_eq (n : ℕ) : a n = S1 n + S0 n := by
  unfold a S1 S0
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _; ring

lemma a_closed (m : ℕ) : a (m + 1) = 2 * ((m : ℤ) + 2) * 3 ^ m := by
  rw [a_eq, (closed m).1, (closed m).2]; ring

end OMA.P_oeis_a027261

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a027261.main := by
  have hc := OMA.P_oeis_a027261.a_closed
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [hc m, show m + 1 - 1 = m by omega]; push_cast; ring
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    rw [show m + 3 - 1 = (m + 1) + 1 by omega, show m + 3 - 2 = m + 1 by omega,
      show m + 3 = (m + 2) + 1 by omega, hc, hc, hc]
    push_cast; ring
  · have e1 : PowerSeries.mk OMA.S_oeis_a027261.a * (1 - 3 * X) ^ 2 =
        PowerSeries.mk OMA.S_oeis_a027261.a - C 6 * (PowerSeries.mk OMA.S_oeis_a027261.a * X ^ 1)
          + C 9 * (PowerSeries.mk OMA.S_oeis_a027261.a * X ^ 2) := by
      simp only [map_ofNat]; ring
    have e2 : (1 - 2 * X + 3 * X ^ 2 : PowerSeries ℤ) = 1 - C 2 * X ^ 1 + C 3 * X ^ 2 := by
      simp only [map_ofNat]; ring
    rw [e1, e2]
    ext n
    simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, coeff_one, coeff_mk, coeff_C]
    rcases n with _ | _ | _ | n
    · simp [OMA.S_oeis_a027261.a, OMA.S_oeis_a027261.T]
    · rw [show (0 + 1 : ℕ) = 0 + 1 from rfl, hc 0]
      simp [OMA.S_oeis_a027261.a, OMA.S_oeis_a027261.T]
    · rw [show (2 : ℕ) = 1 + 1 by rfl, hc 1]
      simp [OMA.S_oeis_a027261.a, OMA.S_oeis_a027261.T, Finset.sum_range_succ]
    · simp only [show n + 1 + 1 + 1 - 1 = (n + 1) + 1 by omega,
        show n + 1 + 1 + 1 - 2 = n + 1 by omega, show n + 1 + 1 + 1 = (n + 2) + 1 by omega]
      simp only [hc]
      simp
      push_cast; ring
