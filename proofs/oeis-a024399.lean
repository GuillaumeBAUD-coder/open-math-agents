import OMAStatements.S_oeis_a024399
import Mathlib

-- Problem: A024399: a(n) = [ (3rd elementary symmetric function of S(n))/(first elementary symmetric function of S(n)) ], where S(n) = {first n+2 positive integers congruent to 2 mod 3}.
-- Upstream: formal-conjectures statements/oeis-a024399.lean:0 (declaration OMA.S_oeis_a024399.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Adding the element x = 3 n + 8 to S(n) gives e_k(S(n+1)) = e_k(S(n)) + x e_(k-1)(S(n)), so by
induction 2 e_1 = 3n^2 + 13n + 14 and 48 e_3 = W (2 e_1) with W = 9n^4 + 42n^3 + 55n^2 + 22n.
Hence e_3/e_1 = W/24 exactly and a(n) = floor(W/24). Since W(n+3) - W(n) is a cubic polynomial
divisible by 24, a(n+3) - a(n) = K(n) with 24 K(n) cubic, and the fourth difference of K
vanishes; this is the recurrence. The generating function identity is the recurrence together
with a(0), ..., a(6) = 0, 5, 31, 101, 248, 515, 952. -/

namespace A024399Aux

open PowerSeries OMA.S_oeis_a024399

theorem esymm_cons (x : ℤ) (s : Multiset ℤ) (k : ℕ) :
    (x ::ₘ s).esymm (k + 1) = s.esymm (k + 1) + x * s.esymm k := by
  unfold Multiset.esymm
  rw [Multiset.powersetCard_cons, Multiset.map_add, Multiset.sum_add, Multiset.map_map]
  congr 1
  rw [← Multiset.sum_map_mul_left]
  congr 1
  apply Multiset.map_congr rfl
  intro t _
  simp

theorem esymm_zero' (s : Multiset ℤ) : s.esymm 0 = 1 := by
  simp [Multiset.esymm, Multiset.powersetCard_zero_left]

theorem esymm_nil (k : ℕ) : (0 : Multiset ℤ).esymm (k + 1) = 0 := by
  simp [Multiset.esymm, Multiset.powersetCard_zero_right]

theorem S_succ (n : ℕ) : S (n + 1) = (3 * ((n : ℤ) + 2) + 2) ::ₘ S n := by
  unfold S
  rw [Multiset.range_succ, Multiset.map_cons]
  push_cast
  rfl

theorem S_zero : S 0 = (5 : ℤ) ::ₘ (2 : ℤ) ::ₘ 0 := by
  unfold S
  rw [show (0 + 2 : ℕ) = Nat.succ (Nat.succ 0) from rfl, Multiset.range_succ, Multiset.range_succ,
    Multiset.range_zero, Multiset.map_cons, Multiset.map_cons, Multiset.map_zero]
  norm_num

theorem closed (n : ℕ) :
    2 * (S n).esymm 1 = 3 * (n : ℤ) ^ 2 + 13 * n + 14 ∧
    8 * (S n).esymm 2 = 9 * (n : ℤ) ^ 4 + 66 * n ^ 3 + 175 * n ^ 2 + 198 * n + 80 ∧
    48 * (S n).esymm 3 = 27 * (n : ℤ) ^ 6 + 243 * n ^ 5 + 837 * n ^ 4 + 1369 * n ^ 3 +
      1056 * n ^ 2 + 308 * n := by
  induction n with
  | zero =>
    rw [S_zero]
    simp only [esymm_cons, esymm_zero', esymm_nil]
    norm_num
  | succ n ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [S_succ]
    simp only [esymm_cons, esymm_zero']
    push_cast
    refine ⟨?_, ?_, ?_⟩
    · linear_combination h1
    · linear_combination h2 + 4 * (3 * ((n : ℤ) + 2) + 2) * h1
    · linear_combination h3 + 6 * (3 * ((n : ℤ) + 2) + 2) * h2

/-- The closed form floor(W/24), W = 9n^4 + 42n^3 + 55n^2 + 22n. -/
theorem a_closed (n : ℕ) : a n = (9 * (n : ℤ) ^ 4 + 42 * n ^ 3 + 55 * n ^ 2 + 22 * n) / 24 := by
  obtain ⟨h1, _, h3⟩ := closed n
  set e1 : ℤ := (S n).esymm 1 with he1
  set e3 : ℤ := (S n).esymm 3 with he3
  set W : ℤ := 9 * (n : ℤ) ^ 4 + 42 * n ^ 3 + 55 * n ^ 2 + 22 * n with hW
  set F : ℤ := W / 24 with hF
  have hP : (0 : ℤ) < 3 * (n : ℤ) ^ 2 + 13 * n + 14 := by positivity
  have he1pos : (0 : ℤ) < e1 := by linarith
  have hdm := Int.emod_add_mul_ediv W 24
  have hr0 := Int.emod_nonneg W (by norm_num : (24 : ℤ) ≠ 0)
  have hr24 := Int.emod_lt_of_pos W (by norm_num : (0 : ℤ) < 24)
  have hrho0 : 0 ≤ W - 24 * F := by omega
  have hrho1 : 0 < 24 * F + 24 - W := by omega
  have hN : 48 * e3 = W * (2 * e1) := by
    rw [h3, h1, hW]
    ring
  have hlow : F * e1 ≤ e3 := by
    nlinarith [mul_nonneg hrho0 he1pos.le]
  have hhigh : e3 < (F + 1) * e1 := by
    nlinarith [mul_pos hrho1 he1pos]
  unfold a
  rw [← he1, ← he3, Int.floor_eq_iff]
  have he1q : (0 : ℚ) < (e1 : ℚ) := by exact_mod_cast he1pos
  constructor
  · rw [le_div_iff₀ he1q]
    exact_mod_cast hlow
  · rw [div_lt_iff₀ he1q]
    exact_mod_cast hhigh

/-- The cubic 24 (a(n+3) - a(n)). -/
def P (x : ℤ) : ℤ := 108 * x ^ 3 + 864 * x ^ 2 + 2436 * x + 2424

theorem d4 (x : ℤ) : P (x + 4) - 4 * P (x + 3) + 6 * P (x + 2) - 4 * P (x + 1) + P x = 0 := by
  unfold P
  ring

theorem a_add_three (n : ℕ) : ∃ K : ℤ, a (n + 3) = a n + K ∧ 24 * K = P (n : ℤ) := by
  obtain ⟨c, hc⟩ := Int.even_mul_succ_self (n : ℤ)
  refine ⟨4 * (n : ℤ) ^ 3 + 36 * n ^ 2 + 101 * n + 101 + c * ((n : ℤ) - 1) + n, ?_, ?_⟩
  · rw [a_closed (n + 3), a_closed n]
    have e : 9 * ((n + 3 : ℕ) : ℤ) ^ 4 + 42 * ((n + 3 : ℕ) : ℤ) ^ 3 + 55 * ((n + 3 : ℕ) : ℤ) ^ 2 +
        22 * ((n + 3 : ℕ) : ℤ) =
        (9 * (n : ℤ) ^ 4 + 42 * n ^ 3 + 55 * n ^ 2 + 22 * n) +
          (4 * (n : ℤ) ^ 3 + 36 * n ^ 2 + 101 * n + 101 + c * ((n : ℤ) - 1) + n) * 24 := by
      push_cast
      linear_combination (12 * ((n : ℤ) - 1)) * hc
    rw [e, Int.add_mul_ediv_right _ _ (by norm_num : (24 : ℤ) ≠ 0)]
  · unfold P
    linear_combination (-12 * ((n : ℤ) - 1)) * hc

theorem rec (m : ℕ) :
    a (m + 7) = 4 * a (m + 6) - 6 * a (m + 5) + 5 * a (m + 4) - 5 * a (m + 3) + 6 * a (m + 2) -
      4 * a (m + 1) + a m := by
  obtain ⟨K0, h0, k0⟩ := a_add_three m
  obtain ⟨K1, h1, k1⟩ := a_add_three (m + 1)
  obtain ⟨K2, h2, k2⟩ := a_add_three (m + 2)
  obtain ⟨K3, h3, k3⟩ := a_add_three (m + 3)
  obtain ⟨K4, h4, k4⟩ := a_add_three (m + 4)
  have e1 : m + 1 + 3 = m + 4 := by ring
  have e2 : m + 2 + 3 = m + 5 := by ring
  have e3 : m + 3 + 3 = m + 6 := by ring
  have e4 : m + 4 + 3 = m + 7 := by ring
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  rw [e4] at h4
  have c1 : ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
  have c2 : ((m + 2 : ℕ) : ℤ) = (m : ℤ) + 2 := by push_cast; ring
  have c3 : ((m + 3 : ℕ) : ℤ) = (m : ℤ) + 3 := by push_cast; ring
  have c4 : ((m + 4 : ℕ) : ℤ) = (m : ℤ) + 4 := by push_cast; ring
  rw [c1] at k1
  rw [c2] at k2
  rw [c3] at k3
  rw [c4] at k4
  have d := d4 (m : ℤ)
  linarith

theorem a_zero : a 0 = 0 := by
  rw [a_closed 0]
  norm_num

theorem c_succ (f : ℤ⟦X⟧) (c : ℤ) (m : ℕ) :
    coeff (m + 1) (f * (1 - C c * X)) = coeff (m + 1) f - c * coeff m f := by
  rw [mul_sub, mul_one, map_sub, mul_comm (C c) X, ← mul_assoc, PowerSeries.coeff_mul_C,
    PowerSeries.coeff_succ_mul_X]
  ring

theorem c_zero (f : ℤ⟦X⟧) (c : ℤ) : coeff 0 (f * (1 - C c * X)) = coeff 0 f := by
  rw [mul_sub, mul_one, map_sub, mul_comm (C c) X, ← mul_assoc, PowerSeries.coeff_mul_C,
    PowerSeries.coeff_zero_mul_X]
  ring

theorem c_cube (f : ℤ⟦X⟧) (m : ℕ) :
    coeff m (f * (1 - X ^ 3)) = coeff m f - if 3 ≤ m then coeff (m - 3) f else 0 := by
  rw [mul_sub, mul_one, map_sub, PowerSeries.coeff_mul_X_pow']

theorem coeff_quintic (u0 u1 u2 u3 u4 u5 : ℤ) (m : ℕ) :
    coeff m (C u0 + C u1 * X + C u2 * X * X + C u3 * X * X * X + C u4 * X * X * X * X +
        C u5 * X * X * X * X * X : ℤ⟦X⟧) =
      if m = 0 then u0 else if m = 1 then u1 else if m = 2 then u2 else if m = 3 then u3
        else if m = 4 then u4 else if m = 5 then u5 else 0 := by
  rcases m with _ | _ | _ | _ | _ | _ | m
  · simp only [map_add, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_zero_C, add_zero, if_true]
  · simp only [map_add, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X,
      PowerSeries.coeff_C]
    simp
  · simp only [map_add, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X,
      PowerSeries.coeff_C]
    simp
  · simp only [map_add, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X,
      PowerSeries.coeff_C]
    simp
  · simp only [map_add, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X,
      PowerSeries.coeff_C]
    simp
  · simp only [map_add, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_C]
    simp
  · simp only [map_add, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_C]
    simp

theorem G4 (f : ℕ → ℤ) (k : ℕ) :
    coeff (k + 1 + 1 + 1 + 1)
      (PowerSeries.mk f * (1 - C 1 * X) * (1 - C 1 * X) * (1 - C 1 * X) * (1 - C 1 * X)) =
      f (k + 1 + 1 + 1 + 1) - 4 * f (k + 1 + 1 + 1) + 6 * f (k + 1 + 1) - 4 * f (k + 1) + f k := by
  simp only [c_succ, PowerSeries.coeff_mk]
  ring

theorem G3 (f : ℕ → ℤ) :
    coeff (0 + 1 + 1 + 1)
      (PowerSeries.mk f * (1 - C 1 * X) * (1 - C 1 * X) * (1 - C 1 * X) * (1 - C 1 * X)) =
      f (0 + 1 + 1 + 1) - 4 * f (0 + 1 + 1) + 6 * f (0 + 1) - 4 * f 0 := by
  simp only [c_succ, c_zero, PowerSeries.coeff_mk]
  ring

theorem G2 (f : ℕ → ℤ) :
    coeff (0 + 1 + 1)
      (PowerSeries.mk f * (1 - C 1 * X) * (1 - C 1 * X) * (1 - C 1 * X) * (1 - C 1 * X)) =
      f (0 + 1 + 1) - 4 * f (0 + 1) + 6 * f 0 := by
  simp only [c_succ, c_zero, PowerSeries.coeff_mk]
  ring

theorem G1 (f : ℕ → ℤ) :
    coeff (0 + 1)
      (PowerSeries.mk f * (1 - C 1 * X) * (1 - C 1 * X) * (1 - C 1 * X) * (1 - C 1 * X)) =
      f (0 + 1) - 4 * f 0 := by
  simp only [c_succ, c_zero, PowerSeries.coeff_mk]
  ring

theorem G0 (f : ℕ → ℤ) :
    coeff 0
      (PowerSeries.mk f * (1 - C 1 * X) * (1 - C 1 * X) * (1 - C 1 * X) * (1 - C 1 * X)) = f 0 := by
  simp only [c_zero, PowerSeries.coeff_mk]

theorem gf :
    PowerSeries.mk a * ((1 + X + X ^ 2) * (X - 1) ^ 5) =
      X * (-5 - 11 * X - 7 * X ^ 2 - 5 * X ^ 3 + X ^ 4) := by
  have h1 : (C 1 : ℤ⟦X⟧) = 1 := map_one C
  have hm1 : (C (-1) : ℤ⟦X⟧) = -1 := by rw [map_neg, map_one]
  have h0 : (C 0 : ℤ⟦X⟧) = 0 := map_zero C
  have h5 : (C 5 : ℤ⟦X⟧) = 5 := map_ofNat C 5
  have h7 : (C 7 : ℤ⟦X⟧) = 7 := map_ofNat C 7
  have h11 : (C 11 : ℤ⟦X⟧) = 11 := map_ofNat C 11
  have hl : PowerSeries.mk a * ((1 + X + X ^ 2) * (X - 1) ^ 5) =
      -(PowerSeries.mk a * (1 - C 1 * X) * (1 - C 1 * X) * (1 - C 1 * X) * (1 - C 1 * X) *
        (1 - X ^ 3)) := by
    rw [h1]
    ring
  have hr : (X * (-5 - 11 * X - 7 * X ^ 2 - 5 * X ^ 3 + X ^ 4) : ℤ⟦X⟧) =
      -(C 0 + C 5 * X + C 11 * X * X + C 7 * X * X * X + C 5 * X * X * X * X +
        C (-1) * X * X * X * X * X) := by
    rw [h5, h7, h11, hm1, h0]
    ring
  rw [hl, hr, neg_inj]
  ext m
  rw [coeff_quintic, c_cube]
  have v0 := a_zero
  have v1 : a 1 = 5 := by rw [a_closed 1]; norm_num
  have v2 : a 2 = 31 := by rw [a_closed 2]; norm_num
  have v3 : a 3 = 101 := by rw [a_closed 3]; norm_num
  have v4 : a 4 = 248 := by rw [a_closed 4]; norm_num
  have v5 : a 5 = 515 := by rw [a_closed 5]; norm_num
  have v6 : a 6 = 952 := by rw [a_closed 6]; norm_num
  rcases m with _ | _ | _ | _ | _ | _ | _ | m
  · rw [if_neg (show ¬ (3 ≤ 0) by norm_num), G0]
    simp [v0]
  · rw [if_neg (show ¬ (3 ≤ 0 + 1) by norm_num), G1]
    simp [v0, v1]
  · rw [if_neg (show ¬ (3 ≤ 0 + 1 + 1) by norm_num), G2]
    simp [v0, v1, v2]
  · rw [if_pos (show 3 ≤ 0 + 1 + 1 + 1 by norm_num), show 0 + 1 + 1 + 1 - 3 = 0 from rfl, G3, G0]
    simp [v0, v1, v2, v3]
  · rw [if_pos (show 3 ≤ 0 + 1 + 1 + 1 + 1 by norm_num),
      show 0 + 1 + 1 + 1 + 1 - 3 = 0 + 1 from rfl, G4, G1]
    simp [v0, v1, v2, v3, v4]
  · rw [if_pos (show 3 ≤ 0 + 1 + 1 + 1 + 1 + 1 by norm_num),
      show 0 + 1 + 1 + 1 + 1 + 1 - 3 = 0 + 1 + 1 from rfl, G4, G2]
    simp [v0, v1, v2, v3, v4, v5]
  · rw [if_pos (show 3 ≤ 0 + 1 + 1 + 1 + 1 + 1 + 1 by norm_num),
      show 0 + 1 + 1 + 1 + 1 + 1 + 1 - 3 = 0 + 1 + 1 + 1 from rfl, G4, G3]
    simp [v0, v1, v2, v3, v4, v5, v6]
  · have hr7 := rec m
    rw [if_pos (show 3 ≤ m + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega),
      show m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 + 1 + 1 from by omega, G4, G4]
    have e7 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 = m + 7 := by ring
    have e6 : m + 1 + 1 + 1 + 1 + 1 + 1 = m + 6 := by ring
    have e5 : m + 1 + 1 + 1 + 1 + 1 = m + 5 := by ring
    have e4 : m + 1 + 1 + 1 + 1 = m + 4 := by ring
    have e3' : m + 1 + 1 + 1 = m + 3 := by ring
    have e2 : m + 1 + 1 = m + 2 := by ring
    rw [e7, e6, e5, e4, e3', e2]
    simp
    linarith

end A024399Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a024399.main := by
  refine ⟨?_, A024399Aux.gf⟩
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
  have e1 : m + 7 - 1 = m + 6 := by omega
  have e2 : m + 7 - 2 = m + 5 := by omega
  have e3 : m + 7 - 3 = m + 4 := by omega
  have e4 : m + 7 - 4 = m + 3 := by omega
  have e5 : m + 7 - 5 = m + 2 := by omega
  have e6 : m + 7 - 6 = m + 1 := by omega
  rw [e1, e2, e3, e4, e5, e6, Nat.add_sub_cancel]
  exact A024399Aux.rec m
