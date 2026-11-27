import OMAStatements.S_oeis_a100311
import Mathlib

/-!
All base-8 digits of a(n) are 0 or 1. For digit families d, e with values in {0, 1},
(Sum d_k 8^k) XOR (Sum e_k 8^k) = Sum ((d_k + e_k) mod 2) 8^k, by induction on the number of
digits using testBit (8x + b) j = if j < 3 then testBit b j else testBit x (j - 3) for b < 8.
With d_k = binomial(n, k-1) mod 2 (the digits of 8 a(n)) and e_k = binomial(n, k) mod 2, Pascal's
rule gives the digits binomial(n+1, k) mod 2 of a(n+1).
-/

namespace R100311
open OMA.S_oeis_a100311

def D (m : ℕ) (d : ℕ → ℕ) : ℕ := ∑ k ∈ Finset.range m, d k * 8 ^ k

theorem D_succ (m : ℕ) (d : ℕ → ℕ) :
    D (m + 1) d = 2 ^ 3 * D m (fun k => d (k + 1)) + d 0 := by
  unfold D
  rw [Finset.sum_range_succ', Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro k _
    ring
  · ring

theorem xor_step (x y b c : ℕ) (hb : b < 2 ^ 3) (hc : c < 2 ^ 3) :
    (2 ^ 3 * x + b) ^^^ (2 ^ 3 * y + c) = 2 ^ 3 * (x ^^^ y) + (b ^^^ c) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow_mul_add _ hb, Nat.testBit_two_pow_mul_add _ hc,
    Nat.testBit_two_pow_mul_add _ (Nat.xor_lt_two_pow hb hc)]
  split_ifs <;> simp [Nat.testBit_xor]

theorem D_xor (m : ℕ) : ∀ d e : ℕ → ℕ, (∀ k, d k ≤ 1) → (∀ k, e k ≤ 1) →
    D m d ^^^ D m e = D m (fun k => (d k + e k) % 2) := by
  induction m with
  | zero => intro d e _ _; simp [D]
  | succ m ih =>
    intro d e hd he
    have h1 := hd 0
    have h2 := he 0
    rw [D_succ, D_succ, D_succ, xor_step _ _ _ _ (by omega) (by omega),
      ih (fun k => d (k + 1)) (fun k => e (k + 1)) (fun k => hd (k + 1)) (fun k => he (k + 1))]
    congr 1
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h1 with h | h <;>
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h2 with h' | h' <;> simp [h, h']

def sh (n k : ℕ) : ℕ := if k = 0 then 0 else n.choose (k - 1) % 2

theorem solve : a 0 = 1 ∧ ∀ n : ℕ, a (n + 1) = (a n * 8) ^^^ a n := by
  refine ⟨by simp [a], fun n => ?_⟩
  have h0 : a n = D (n + 1) (fun k => n.choose k % 2) := rfl
  have h1 : a n = D (n + 2) (fun k => n.choose k % 2) := by
    rw [h0]
    unfold D
    rw [Finset.sum_range_succ _ (n + 1)]
    simp
  have h2 : a n * 8 = D (n + 2) (sh n) := by
    rw [D_succ, h0]
    simp [sh] <;> ring
  have hd : ∀ k, sh n k ≤ 1 := fun k => by unfold sh; split_ifs <;> omega
  have he : ∀ k, (fun k => n.choose k % 2) k ≤ 1 :=
    fun k => Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
  rw [h2, h1, D_xor (n + 2) (sh n) (fun k => n.choose k % 2) hd he]
  show D (n + 2) (fun k => (n + 1).choose k % 2) = _
  unfold D
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  rcases k with _ | k
  · simp [sh]
  · simp only [sh, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, Nat.choose_succ_succ']
    omega

end R100311

theorem OMA.solution : type_of% @OMA.S_oeis_a100311.main := R100311.solve
