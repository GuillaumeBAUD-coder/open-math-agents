import OMAStatements.S_oeis_a192431
import Mathlib

open OMA.S_oeis_a192431 Polynomial

theorem P192431.rec2 (n : ℕ) : p (n + 2) = 2 * X * p (n + 1) - (X ^ 2 - X - 2) * p n := by
  simp only [p, pq]
  ring

theorem P192431.E (n : ℕ) :
    p (n + 4) - (2 : ℤ) • p (n + 3) - (6 : ℤ) • p (n + 2) + (2 : ℤ) • p (n + 1) + p n =
      (X ^ 2 - X - 1) * ((4 * X + 2) * p (n + 1) + (-3 * X ^ 2 + 3 * X + 7) * p n) := by
  have h4 : p (n + 4) = 2 * X * p (n + 3) - (X ^ 2 - X - 2) * p (n + 2) := P192431.rec2 (n + 2)
  have h3 : p (n + 3) = 2 * X * p (n + 2) - (X ^ 2 - X - 2) * p (n + 1) := P192431.rec2 (n + 1)
  have h2 : p (n + 2) = 2 * X * p (n + 1) - (X ^ 2 - X - 2) * p n := P192431.rec2 n
  simp only [zsmul_eq_mul, Int.cast_ofNat]
  rw [h4, h3, h2]
  ring

theorem OMA.solution : type_of% @OMA.S_oeis_a192431.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
    show m + 4 - 3 = m + 1 by omega, show m + 4 - 4 = m by omega]
  have hq : (X ^ 2 - X - 1 : ℤ[X]).Monic := by
    have e : (X ^ 2 - X - 1 : ℤ[X]) = X ^ 2 - (X + 1) := by ring
    rw [e]
    apply monic_X_pow_sub
    compute_degree!
  let L : ℤ[X] →ₗ[ℤ] ℤ := (Polynomial.lcoeff ℤ 1).comp (Polynomial.modByMonicHom (X ^ 2 - X - 1))
  have ha : ∀ k, a k = L (p k) := fun k => rfl
  have h0 : L ((X ^ 2 - X - 1) * ((4 * X + 2) * p (m + 1) + (-3 * X ^ 2 + 3 * X + 7) * p m)) = 0 := by
    show ((X ^ 2 - X - 1) * ((4 * X + 2) * p (m + 1) + (-3 * X ^ 2 + 3 * X + 7) * p m) %ₘ
      (X ^ 2 - X - 1)).coeff 1 = 0
    rw [(modByMonic_eq_zero_iff_dvd hq).2 (dvd_mul_right _ _)]
    simp
  rw [← P192431.E m] at h0
  simp only [map_add, map_sub, map_smul, smul_eq_mul] at h0
  rw [ha, ha, ha, ha, ha]
  linarith
