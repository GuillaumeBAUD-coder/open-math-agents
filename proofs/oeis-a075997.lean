import OMAStatements.S_oeis_a075997
import Mathlib.Tactic

/-!
The two summands have the same remainder modulo 2k. Adding them
produces a carry precisely when floor(n/k) is even. Interchanging
the sums over pairs with product at most n transforms the alternating
floor sum into the count of these carries.
-/
-- Credit: @dk8827

namespace OMA.A075997

open Finset OMA.S_oeis_a075997

private theorem remainder_of_decomposition {r d q : ℤ} (h0 : 0 ≤ r) (hlt : r < d) :
    (r + d * q) % d = r := by
  rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt h0 hlt]

private theorem carry (n k : ℕ) (hk : 0 < k) :
    f ((n : ℤ) + k) ((n : ℤ) - k) = if Even (n / k) then 1 else 0 := by
  let q := n / k
  let r := n % k
  have hk' : (0 : ℤ) < k := by exact_mod_cast hk
  have hr0 : (0 : ℤ) ≤ r := Int.natCast_nonneg _
  have hr : (r : ℤ) < k := by exact_mod_cast Nat.mod_lt n hk
  have hn : (n : ℤ) = (k : ℤ) * q + r := by exact_mod_cast (Nat.div_add_mod n k).symm
  have hmod : |((n : ℤ) + k) - ((n : ℤ) - k)| = 2 * (k : ℤ) := by
    rw [show ((n : ℤ) + k) - ((n : ℤ) - k) = 2 * (k : ℤ) by ring, abs_of_pos (by omega)]
  have hsum : (((n : ℤ) + k) + ((n : ℤ) - k)) % (2 * (k : ℤ)) = 2 * (r : ℤ) := by
    rw [show ((n : ℤ) + k) + ((n : ℤ) - k) = 2 * (r : ℤ) + (2 * (k : ℤ)) * q by
      rw [hn]
      ring]
    exact remainder_of_decomposition (by omega) (by omega)
  have hmatch : ((n : ℤ) - k) % (2 * (k : ℤ)) = ((n : ℤ) + k) % (2 * (k : ℤ)) := by
    conv_rhs => rw [show (n : ℤ) + k = ((n : ℤ) - k) + (2 * (k : ℤ)) * 1 by ring]
    rw [Int.add_mul_emod_self_left]
  unfold f
  rw [hmod, hsum, hmatch]
  change (if 2 * (r : ℤ) ≠ _ then (1 : ℤ) else 0) = if Even q then 1 else 0
  rcases Nat.even_or_odd q with he | ho
  · rw [if_pos he]
    obtain ⟨u, hu⟩ := he
    have hq : (q : ℤ) = 2 * (u : ℤ) := by exact_mod_cast (show q = 2 * u by omega)
    have hr' : ((n : ℤ) + k) % (2 * (k : ℤ)) = (r : ℤ) + k := by
      rw [show (n : ℤ) + k = (r : ℤ) + k + (2 * (k : ℤ)) * u by
        rw [hn, hq]
        ring]
      exact remainder_of_decomposition (by omega) (by omega)
    rw [hr', if_pos (by omega)]
  · rw [if_neg (Nat.not_even_iff_odd.mpr ho)]
    obtain ⟨u, hu⟩ := ho
    have hq : (q : ℤ) = 2 * (u : ℤ) + 1 := by exact_mod_cast (show q = 2 * u + 1 by omega)
    have hr' : ((n : ℤ) + k) % (2 * (k : ℤ)) = r := by
      rw [show (n : ℤ) + k = (r : ℤ) + (2 * (k : ℤ)) * ((u : ℤ) + 1) by
        rw [hn, hq]
        ring]
      exact remainder_of_decomposition hr0 (by omega)
    rw [hr', show 2 * (r : ℤ) = r + r by ring]
    simp

private theorem filter_floor (n d l : ℕ) (hd : 0 < d) :
    (Icc l n).filter (fun k => k * d ≤ n) = Icc l (n / d) := by
  ext k
  simp only [mem_filter, mem_Icc, ← Nat.le_div_iff_mul_le hd]
  have hdiv := Nat.div_le_self n d
  omega

private theorem alternating (m : ℕ) (hm : 1 ≤ m) :
    ∑ k ∈ Icc 2 m, (-1 : ℤ) ^ k = if Even m then 1 else 0 := by
  have h := sum_range_add_sum_Ico (fun k : ℕ => (-1 : ℤ) ^ k) (show 2 ≤ m + 1 by omega)
  rw [Ico_add_one_right_eq_Icc, show (∑ k ∈ range 2, (-1 : ℤ) ^ k) = 0 by decide,
    zero_add, neg_one_geom_sum] at h
  rw [h]
  rcases Nat.even_or_odd m with he | ho
  · have hn : ¬ Even (m + 1) := fun h => (Nat.even_add_one.mp h) he
    simp [he, hn]
  · have hn := Nat.not_even_iff_odd.mpr ho
    simp [Nat.even_add_one.mpr hn, hn]

private theorem floor_count (n : ℕ) :
    a n = ∑ j ∈ Icc 1 n, if Even (n / j) then (1 : ℤ) else 0 := by
  unfold a
  calc
    _ = ∑ k ∈ Icc 2 n, ∑ j ∈ Icc 1 n, if j * k ≤ n then (-1 : ℤ) ^ k else 0 := by
      apply sum_congr rfl
      intro k hk
      have hk' : 0 < k := by have := (mem_Icc.mp hk).1; omega
      rw [← sum_filter, filter_floor _ _ _ hk']
      simp [Nat.card_Icc, mul_comm]
    _ = ∑ j ∈ Icc 1 n, ∑ k ∈ Icc 2 n, if j * k ≤ n then (-1 : ℤ) ^ k else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro j hj
      obtain ⟨hj1, hjn⟩ := mem_Icc.mp hj
      have hj' : 0 < j := by omega
      simp_rw [mul_comm j]
      rw [← sum_filter, filter_floor _ _ _ hj', alternating _ (Nat.le_div_iff_mul_le hj' |>.mpr (by simpa using hjn))]

theorem solution_aux (n : ℕ) :
    a n = ∑ k ∈ Icc 1 (n - 1), f ((n : ℤ) + k) ((n : ℤ) - k) := by
  by_cases hn : n = 0
  · subst n
    simp [a]
  rw [floor_count]
  have hI : Icc 1 n = insert n (Icc 1 (n - 1)) := by
    ext k
    simp only [mem_Icc, mem_insert]
    omega
  rw [hI, sum_insert (by rw [mem_Icc]; omega), Nat.div_self (by omega : 0 < n)]
  simp only [Nat.not_even_one, if_false, zero_add]
  apply sum_congr rfl
  intro k hk
  exact (carry n k (by have := (mem_Icc.mp hk).1; omega)).symm

end OMA.A075997

theorem OMA.solution : type_of% @OMA.S_oeis_a075997.main := OMA.A075997.solution_aux
