import OMAStatements.S_oeis_a075989
import Mathlib

/-!
Credit: @ivillar
Proof: for 1 <= k <= n, {n/k} = (n mod k)/k, so {n/k} >= 1/2 iff k <= 2 (n mod k); this fails
for k = n. For 1 <= k < n put d = n - k > 0. Then |n - k| = d, n = k + d gives
n mod d = k mod d, and (n + k) mod d = (n mod d + k mod d) mod d, which differs from
n mod d + k mod d exactly when d <= n mod d + k mod d = 2 (n mod d). So f(n, k) = 1 iff
d <= 2 (n mod d), and the substitution k -> n - k maps {1, ..., n-1} onto itself.
-/

namespace OMAA075989Helpers
open OMA.S_oeis_a075989

theorem frac_cond (n k : ℕ) (hk : 0 < k) :
    (1 : ℚ) / 2 ≤ Int.fract ((n : ℚ) / k) ↔ k ≤ 2 * (n % k) := by
  have hk' : (0 : ℚ) < k := by exact_mod_cast hk
  rw [Int.fract_div_natCast_eq_div_natCast_mod, le_div_iff₀ hk']
  constructor
  · intro h
    have : (k : ℚ) ≤ 2 * ((n % k : ℕ) : ℚ) := by linarith
    exact_mod_cast this
  · intro h
    have : (k : ℚ) ≤ 2 * ((n % k : ℕ) : ℚ) := by exact_mod_cast h
    linarith

theorem mod_cond (n k d : ℕ) (hd : 0 < d) (h : n = k + d) :
    (n + k) % d ≠ n % d + k % d ↔ d ≤ 2 * (n % d) := by
  have e1 : n % d = k % d := by rw [h, Nat.add_mod_right]
  have e2 : (n + k) % d = (n % d + k % d) % d := Nat.add_mod _ _ _
  rw [e2, ← e1]
  constructor
  · intro hne
    by_contra hc
    exact hne (Nat.mod_eq_of_lt (by omega))
  · intro hle heq
    have := Nat.mod_lt (n % d + n % d) hd
    omega

theorem f_eq (n k : ℕ) (hk : k < n) :
    f n k = if n - k ≤ 2 * (n % (n - k)) then 1 else 0 := by
  unfold f
  have hd : |(n : ℤ) - k| = ((n - k : ℕ) : ℤ) := by
    rw [abs_of_pos (show (0 : ℤ) < (n : ℤ) - k by omega), Nat.cast_sub hk.le]
  rw [hd]
  have key : ((n : ℤ) + k) % ((n - k : ℕ) : ℤ) ≠
      (n : ℤ) % ((n - k : ℕ) : ℤ) + (k : ℤ) % ((n - k : ℕ) : ℤ) ↔
      (n + k) % (n - k) ≠ n % (n - k) + k % (n - k) := by
    norm_cast
  rw [if_congr (key.trans (mod_cond n k (n - k) (by omega) (by omega))) rfl rfl]

end OMAA075989Helpers

open OMAA075989Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a075989.main := by
  intro n hn
  have hA : OMA.S_oeis_a075989.a n =
      ∑ j ∈ Finset.Ico 1 n, (if j ≤ 2 * (n % j) then 1 else 0) := by
    unfold OMA.S_oeis_a075989.a
    rw [Finset.card_filter, ← Finset.Ico_insert_right hn, Finset.sum_insert (by simp)]
    have h0 : ¬ ((1 : ℚ) / 2 ≤ Int.fract ((n : ℚ) / n)) := by
      rw [frac_cond n n (by omega), Nat.mod_self]
      omega
    rw [if_neg h0, zero_add]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_Ico] at hj
    exact if_congr (frac_cond n j (by omega)) rfl rfl
  have hB : ∑ k ∈ Finset.Ico 1 n, OMA.S_oeis_a075989.f n k =
      ∑ k ∈ Finset.Ico 1 n, (if n - k ≤ 2 * (n % (n - k)) then 1 else 0) :=
    Finset.sum_congr rfl (fun k hk => f_eq n k (Finset.mem_Ico.mp hk).2)
  rw [hA, hB]
  exact Finset.sum_nbij' (fun j => n - j) (fun k => n - k)
    (fun j hj => by simp only [Finset.mem_Ico] at hj ⊢; omega)
    (fun k hk => by simp only [Finset.mem_Ico] at hk ⊢; omega)
    (fun j hj => by simp only [Finset.mem_Ico] at hj; omega)
    (fun k hk => by simp only [Finset.mem_Ico] at hk; omega)
    (fun j hj => by
      simp only [Finset.mem_Ico] at hj
      rw [show n - (n - j) = j by omega])
