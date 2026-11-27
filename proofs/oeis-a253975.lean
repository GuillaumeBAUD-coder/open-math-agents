import OMAStatements.S_oeis_a253975
import Mathlib

namespace OMA.A253975Proof

theorem key (N x y : ℕ) : x * y + x + y = 2 ^ N - 1 ↔ (x + 1) * (y + 1) = 2 ^ N := by
  have h1 : (x + 1) * (y + 1) = x * y + x + y + 1 := by ring
  have h2 : 1 ≤ 2 ^ N := Nat.one_le_two_pow
  omega

abbrev R (k : ℕ) := {p : ℕ × ℕ // 1 < p.2 ∧ p.2 ≤ p.1 ∧ p.1 * p.2 + p.1 + p.2 = k}

def rep (n : ℕ) (i : Fin n) : R (2 ^ (2 * n + 3) - 1) :=
  ⟨(2 ^ (2 * n + 1 - (i : ℕ)) - 1, 2 ^ ((i : ℕ) + 2) - 1), by
    have hi := i.isLt
    have a1 : 1 ≤ 2 ^ (2 * n + 1 - (i : ℕ)) := Nat.one_le_two_pow
    have a2 : 4 ≤ 2 ^ ((i : ℕ) + 2) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ ((i : ℕ) + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have a3 : 2 ^ ((i : ℕ) + 2) ≤ 2 ^ (2 * n + 1 - (i : ℕ)) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    refine ⟨by omega, by omega, ?_⟩
    rw [key, Nat.sub_add_cancel a1, Nat.sub_add_cancel (by omega), ← pow_add]
    congr 1
    omega⟩

theorem rep_bij (n : ℕ) : Function.Bijective (rep n) := by
  constructor
  · intro i j hij
    have h := congrArg (fun r => r.1.2) hij
    simp only [rep] at h
    have b1 : 1 ≤ 2 ^ ((i : ℕ) + 2) := Nat.one_le_two_pow
    have b2 : 1 ≤ 2 ^ ((j : ℕ) + 2) := Nat.one_le_two_pow
    have h' : 2 ^ ((i : ℕ) + 2) = 2 ^ ((j : ℕ) + 2) := by omega
    have := Nat.pow_right_injective (le_refl 2) h'
    exact Fin.ext (by omega)
  · rintro ⟨⟨x, y⟩, hy, hyx, he⟩
    simp only at hy hyx he
    rw [key] at he
    obtain ⟨j, hjle, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (Dvd.intro_left _ he)
    have hx : x + 1 = 2 ^ (2 * n + 3 - j) := by
      have hpos : 0 < 2 ^ j := by positivity
      apply Nat.eq_of_mul_eq_mul_right hpos
      rw [← pow_add, ← hj, he]
      congr 1
      omega
    have hj2 : 2 ≤ j := by
      by_contra hc
      push Not at hc
      interval_cases j <;> simp at hj <;> omega
    have hjn : j ≤ n + 1 := by
      have : 2 ^ j ≤ 2 ^ (2 * n + 3 - j) := by omega
      have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 this
      omega
    refine ⟨⟨j - 2, by omega⟩, ?_⟩
    apply Subtype.ext
    simp only [rep]
    have e1 : 2 * n + 1 - (j - 2) = 2 * n + 3 - j := by omega
    have e2 : j - 2 + 2 = j := by omega
    rw [e1, e2]
    ext <;> simp <;> omega

end OMA.A253975Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a253975.main := by
  intro n _
  exact ⟨2 ^ (2 * n + 3) - 1,
    ⟨Equiv.ofBijective (OMA.A253975Proof.rep n) (OMA.A253975Proof.rep_bij n)⟩⟩
