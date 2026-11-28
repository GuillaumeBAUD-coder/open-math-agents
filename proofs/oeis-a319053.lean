import OMAStatements.S_oeis_a319053
import Mathlib

namespace A319053

open OMA.S_oeis_a319053 in
lemma pow_formula (k : ℕ) :
    M ^ (k + 1) =
      !![2 ^ k * (3 * (Nat.fib (k + 1) : ℤ) + 2 * Nat.fib k), 2 ^ k * (Nat.fib (k + 1) : ℤ);
         2 ^ k * (Nat.fib (k + 1) : ℤ), 2 ^ k * (2 * (Nat.fib k : ℤ) - Nat.fib (k + 1))] := by
  induction k with
  | zero =>
    ext i j
    fin_cases i <;> fin_cases j <;> simp [M]
  | succ k ih =>
    rw [pow_succ, ih]
    have hf : (Nat.fib (k + 1 + 1) : ℤ) = Nat.fib k + Nat.fib (k + 1) := by
      rw [Nat.fib_add_two]; push_cast; ring
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [M, Matrix.mul_apply, Fin.sum_univ_two, hf, pow_succ] <;> ring

lemma val_two_pow_mul_odd (k : ℕ) (c : ℤ) (hc : Odd c) : padicValInt 2 (2 ^ k * c) = k := by
  have hc0 : c.natAbs ≠ 0 := by
    intro h
    have : c = 0 := Int.natAbs_eq_zero.mp h
    subst this
    exact absurd hc (by decide)
  have hodd : ¬ 2 ∣ c.natAbs := by
    intro h
    have h2 : (2 : ℤ) ∣ c := Int.natCast_dvd.mpr h
    obtain ⟨m, hm⟩ := hc
    omega
  unfold padicValInt
  rw [Int.natAbs_mul, Int.natAbs_pow]
  have : (2 : ℤ).natAbs = 2 := rfl
  rw [this]
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [padicValNat.mul (by positivity) hc0, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hodd, add_zero]

lemma fib_odd (n : ℕ) (h : ¬ 3 ∣ n) : Odd (Nat.fib n) := by
  have hg : Nat.gcd n 3 = 1 := by
    have : Nat.Coprime 3 n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h
    exact this.symm
  have h1 := Nat.fib_gcd n 3
  rw [hg] at h1
  have h2 : Nat.gcd (Nat.fib n) 2 = 1 := by
    have : Nat.fib 3 = 2 := by decide
    rw [this] at h1
    simpa using h1.symm
  exact Nat.coprime_two_right.mp h2

end A319053

theorem OMA.solution : type_of% @OMA.S_oeis_a319053.main := by
  intro n hn h3
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hodd := A319053.fib_odd (k + 1) h3
  obtain ⟨m, hm⟩ := hodd
  have ho1 : Odd (3 * (Nat.fib (k + 1) : ℤ) + 2 * Nat.fib k) :=
    ⟨3 * m + 1 + Nat.fib k, by rw [hm]; push_cast; ring⟩
  have ho2 : Odd (Nat.fib (k + 1) : ℤ) := ⟨m, by rw [hm]; push_cast; ring⟩
  have ho3 : Odd (2 * (Nat.fib k : ℤ) - Nat.fib (k + 1)) :=
    ⟨(Nat.fib k : ℤ) - m - 1, by rw [hm]; push_cast; ring⟩
  have hconst : ∀ ij : Fin 2 × Fin 2,
      padicValInt 2 ((OMA.S_oeis_a319053.M ^ (k + 1)) ij.1 ij.2) = k := by
    rintro ⟨i, j⟩
    rw [A319053.pow_formula]
    fin_cases i <;> fin_cases j
    · simpa using A319053.val_two_pow_mul_odd k _ ho1
    · simpa using A319053.val_two_pow_mul_odd k _ ho2
    · simpa using A319053.val_two_pow_mul_odd k _ ho2
    · simpa using A319053.val_two_pow_mul_odd k _ ho3
  unfold OMA.S_oeis_a319053.a
  rw [Finset.sup_congr rfl (fun ij _ => hconst ij), Finset.sup_const Finset.univ_nonempty]
  omega
