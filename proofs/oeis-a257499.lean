import OMAStatements.S_oeis_a257499
import Mathlib

namespace A257499Proof

open OMA.S_oeis_a257499

lemma pow_form (n : ℕ) : ∃ c : ℤ, (2 : ℤ) ^ n = 3 * c + (-1) ^ n := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨c, hc⟩ := ih
    exact ⟨2 * c + (-1) ^ n, by rw [pow_succ, pow_succ, hc]; ring⟩

lemma sign (n : ℕ) : ((-1 : ℤ)) ^ n = 1 ∨ ((-1 : ℤ)) ^ n = -1 := neg_one_pow_eq_or ℤ n

lemma three_mul (n k : ℕ) :
    ∃ t : ℤ, 1 + 2 ^ n * (6 * (k : ℤ) - 3 + 2 * (-1) ^ n) = 3 * t := by
  obtain ⟨c, hc⟩ := pow_form n
  have he : ((-1 : ℤ)) ^ n * (-1) ^ n = 1 := by
    rcases sign n with h | h <;> rw [h] <;> norm_num
  refine ⟨1 + c * (6 * (k : ℤ) - 3 + 2 * (-1) ^ n) + 2 * k * (-1) ^ n - (-1) ^ n, ?_⟩
  rw [hc]
  linear_combination 2 * he

lemma A_eq_iff (n k : ℕ) (v : ℤ) :
    A n k = v ↔ 2 ^ n * (6 * (k : ℤ) - 3 + 2 * (-1) ^ n) = 3 * v - 1 := by
  obtain ⟨t, ht⟩ := three_mul n k
  unfold A
  rw [ht]
  generalize (2 : ℤ) ^ n * (6 * (k : ℤ) - 3 + 2 * (-1) ^ n) = x at ht ⊢
  omega

lemma pow_cancel (a b : ℕ) (q q' : ℤ) (hq : q % 2 = 1)
    (h : (2 : ℤ) ^ a * q = 2 ^ b * q') : b ≤ a := by
  by_contra hlt
  obtain ⟨d, rfl⟩ : ∃ d, b = a + d + 1 := ⟨b - a - 1, by omega⟩
  have h2 : (2 : ℤ) ^ a * q = 2 ^ a * (2 * (2 ^ d * q')) := by rw [h]; ring
  have h3 := mul_left_cancel₀ (pow_ne_zero a (two_ne_zero : (2 : ℤ) ≠ 0)) h2
  omega

lemma uniq (n k n' k' : ℕ) (hk : 1 ≤ k) (hk' : 1 ≤ k')
    (h : (2 : ℤ) ^ n * (6 * (k : ℤ) - 3 + 2 * (-1) ^ n) =
      2 ^ n' * (6 * (k' : ℤ) - 3 + 2 * (-1) ^ n')) : n = n' ∧ k = k' := by
  have hq : (6 * (k : ℤ) - 3 + 2 * (-1) ^ n) % 2 = 1 := by
    rcases sign n with e | e <;> rw [e] <;> omega
  have hq' : (6 * (k' : ℤ) - 3 + 2 * (-1) ^ n') % 2 = 1 := by
    rcases sign n' with e | e <;> rw [e] <;> omega
  have h1 := pow_cancel n n' _ _ hq h
  have h2 := pow_cancel n' n _ _ hq' h.symm
  have hn : n = n' := le_antisymm h2 h1
  subst hn
  have h3 := mul_left_cancel₀ (pow_ne_zero n (two_ne_zero : (2 : ℤ) ≠ 0)) h
  refine ⟨rfl, ?_⟩
  omega

lemma exist (m : ℕ) : ∃ n k : ℕ, 1 ≤ n ∧ 1 ≤ k ∧
    (2 : ℤ) ^ n * (6 * (k : ℤ) - 3 + 2 * (-1) ^ n) = 6 * (m : ℤ) + 2 := by
  obtain ⟨n, q, hq, hN⟩ := Nat.exists_eq_two_pow_mul_odd (n := 6 * m + 2) (by omega)
  obtain ⟨r, rfl⟩ := hq
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp at hN; omega
    · exact h0
  have hZ : (2 : ℤ) ^ n * (2 * (r : ℤ) + 1) = 6 * (m : ℤ) + 2 := by
    have := congrArg (fun x : ℕ => (x : ℤ)) hN
    push_cast at this
    linarith
  obtain ⟨c, hc⟩ := pow_form n
  rcases sign n with e | e
  · -- 2^n = 3c+1, q = 2 mod 3, q = 6k-1
    rw [e] at hc
    have hx : (3 * c + 1) * (2 * (r : ℤ) + 1) = 6 * (m : ℤ) + 2 := by rw [← hc]; exact hZ
    have hx' : 3 * (c * (2 * (r : ℤ) + 1)) + (2 * (r : ℤ) + 1) = 6 * (m : ℤ) + 2 := by
      linarith
    generalize c * (2 * (r : ℤ) + 1) = x at hx'
    obtain ⟨j, hj⟩ : ∃ j : ℕ, r = 3 * j + 2 := ⟨(r - 2) / 3, by omega⟩
    refine ⟨n, j + 1, hn, by omega, ?_⟩
    rw [e, ← hZ, hj]
    push_cast
    ring
  · rw [e] at hc
    have hx : (3 * c + -1) * (2 * (r : ℤ) + 1) = 6 * (m : ℤ) + 2 := by rw [← hc]; exact hZ
    have hx' : 3 * (c * (2 * (r : ℤ) + 1)) - (2 * (r : ℤ) + 1) = 6 * (m : ℤ) + 2 := by
      linarith
    generalize c * (2 * (r : ℤ) + 1) = x at hx'
    obtain ⟨j, hj⟩ : ∃ j : ℕ, r = 3 * j := ⟨r / 3, by omega⟩
    refine ⟨n, j + 1, hn, by omega, ?_⟩
    rw [e, ← hZ, hj]
    push_cast
    ring

theorem result :
    (∀ n k : ℕ, 1 ≤ n → 1 ≤ k → (3 : ℤ) ∣ 1 + 2 ^ n * (6 * (k : ℤ) - 3 + 2 * (-1) ^ n)) ∧
    (∀ n k : ℕ, 1 ≤ n → 1 ≤ k → ∃ m : ℕ, A n k = 2 * (m : ℤ) + 1) ∧
    (∀ m : ℕ, ∃! p : ℕ × ℕ, 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ A p.1 p.2 = 2 * (m : ℤ) + 1) := by
  refine ⟨fun n k _ _ => ?_, fun n k hn hk => ?_, fun m => ?_⟩
  · obtain ⟨t, ht⟩ := three_mul n k
    exact ⟨t, ht⟩
  · obtain ⟨t, ht⟩ := three_mul n k
    have hA : A n k = t := by
      rw [A_eq_iff]; linarith
    obtain ⟨d, rfl⟩ : ∃ d, n = d + 1 := ⟨n - 1, by omega⟩
    have hp : (0 : ℤ) < 2 ^ d := by positivity
    have hq : (1 : ℤ) ≤ 6 * (k : ℤ) - 3 + 2 * (-1) ^ (d + 1) := by
      rcases sign (d + 1) with e | e <;> rw [e] <;> omega
    have hpos : (0 : ℤ) < 2 ^ d * (6 * (k : ℤ) - 3 + 2 * (-1) ^ (d + 1)) := by positivity
    have ht' : 1 + 2 * (2 ^ d * (6 * (k : ℤ) - 3 + 2 * (-1) ^ (d + 1))) = 3 * t := by
      rw [← ht]; ring
    generalize (2 : ℤ) ^ d * (6 * (k : ℤ) - 3 + 2 * (-1) ^ (d + 1)) = y at ht' hpos
    refine ⟨((t - 1) / 2).toNat, ?_⟩
    rw [hA]
    omega
  · obtain ⟨n, k, hn, hk, h⟩ := exist m
    refine ⟨(n, k), ⟨hn, hk, ?_⟩, ?_⟩
    · rw [A_eq_iff]; linarith
    · rintro ⟨n', k'⟩ ⟨hn', hk', h'⟩
      rw [A_eq_iff] at h'
      have := uniq n' k' n k hk' hk (by rw [h', h]; ring)
      exact Prod.ext this.1 this.2

end A257499Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a257499.main := A257499Proof.result
