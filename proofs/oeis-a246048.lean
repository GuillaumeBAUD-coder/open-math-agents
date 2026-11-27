import OMAStatements.S_oeis_a246048
import Mathlib

namespace A246048aux

lemma key (p : ℕ) (hp : p.Prime) (c m : ℕ) :
    (p - 1) * padicValNat p (p ^ m * c).factorial
      = (p - 1) * padicValNat p c.factorial + c * (p ^ m - 1) := by
  have hf : Fact p.Prime := ⟨hp⟩
  induction m with
  | zero => simp
  | succ m ih =>
    have e : p ^ (m + 1) * c = p * (p ^ m * c) := by ring
    rw [e, padicValNat_factorial_mul, Nat.mul_add, ih]
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.pos; omega⟩
    have h1 : 1 ≤ (q + 1) ^ m := Nat.one_le_pow _ _ (by omega)
    obtain ⟨t, ht⟩ : ∃ t, (q + 1) ^ m = t + 1 := ⟨(q + 1) ^ m - 1, by omega⟩
    have ht2 : (q + 1) ^ (m + 1) = (t + 1) * (q + 1) := by rw [pow_succ, ht]
    rw [ht2, ht]
    have h3 : (t + 1) * (q + 1) - 1 = t * q + t + q := by
      have h4 : (t + 1) * (q + 1) = t * q + t + q + 1 := by ring
      omega
    rw [h3]
    simp only [Nat.add_sub_cancel]
    ring

end A246048aux

theorem OMA.solution : type_of% @OMA.S_oeis_a246048.main := by
  intro p k hp hterm
  unfold OMA.S_oeis_a246048.isTerm at hterm
  have hf : Fact p.Prime := ⟨hp⟩
  have hA2 : 2 ≤ p ^ (k + 1) := by
    calc 2 ≤ p := hp.two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ (k + 1) := Nat.pow_le_pow_right hp.pos (by omega)
  have k1 := A246048aux.key p hp 1 (k + 1)
  have k2 := A246048aux.key p hp 2 (k + 1)
  have k3 := A246048aux.key p hp 1 (2 * (k + 1))
  rw [mul_one] at k1 k3
  rw [show p ^ (2 * (k + 1)) = (p ^ (k + 1)) ^ 2 by rw [mul_comm, pow_mul]] at k3
  rw [show p ^ (k + 1) * 2 = 2 * p ^ (k + 1) by ring] at k2
  have v1 : padicValNat p (Nat.factorial 1) = 0 := by simp
  rw [v1] at k1 k3
  generalize p ^ (k + 1) = A at hA2 k1 k2 k3 hterm
  have hle : padicValNat p (A.factorial ^ A * (2 * A).factorial)
      ≤ padicValNat p (A ^ 2).factorial := by
    rw [← padicValNat_dvd_iff_le (Nat.factorial_ne_zero _)]
    exact dvd_trans pow_padicValNat_dvd hterm
  rw [padicValNat.mul (pow_ne_zero _ (Nat.factorial_ne_zero _)) (Nat.factorial_ne_zero _),
    padicValNat.pow] at hle
  have hmul := Nat.mul_le_mul_left (p - 1) hle
  rw [Nat.mul_add, ← mul_assoc, mul_comm (p - 1) A, mul_assoc, k1, k2, k3] at hmul
  obtain ⟨a, rfl⟩ : ∃ a, A = a + 2 := ⟨A - 2, by omega⟩
  have e1 : (a + 2) ^ 2 - 1 = a * a + 4 * a + 3 := by
    have : (a + 2) ^ 2 = a * a + 4 * a + 4 := by ring
    omega
  have e2 : (a + 2) * ((p - 1) * 0 + 1 * (a + 2 - 1)) = a * a + 3 * a + 2 := by
    rw [show a + 2 - 1 = a + 1 by omega]
    ring
  rw [e1, e2] at hmul
  omega
