import OMAStatements.S_oeis_a191668

namespace OMA.A191668

open OMA.S_oeis_a191668
open Function

private def values (i : ℕ) : ℕ := (4*i+5)/3

private theorem values_mono : StrictMono values := by
  intro i j hij
  unfold values
  omega

private theorem inT_iff (x : ℕ) : InT x ↔ 0 < x ∧ x % 4 ≠ 2 := by
  constructor
  · rintro ⟨hx, h⟩
    refine ⟨hx, ?_⟩
    intro hr
    exact h (x/4+1) (by omega) (by omega)
  · rintro ⟨hx, hr⟩
    refine ⟨hx, ?_⟩
    intro m hm he
    exact hr (by omega)

private theorem values_range : Set.range values = Set.ofPred InT := by
  ext x
  rw [Set.mem_ofPred_eq, inT_iff]
  constructor
  · rintro ⟨i, rfl⟩
    unfold values
    omega
  · rintro ⟨hx, hr⟩
    have hc : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 3 := by omega
    rcases hc with h0 | h1 | h3
    · refine ⟨3*(x/4)-1, ?_⟩
      unfold values
      rw [show 4*(3*(x/4)-1)+5 = 3*x+1 by omega]
      omega
    · refine ⟨3*(x/4), ?_⟩
      unfold values
      rw [show 4*(3*(x/4))+5 = 3*x+2 by omega]
      omega
    · refine ⟨3*(x/4)+1, ?_⟩
      unfold values
      rw [show 4*(3*(x/4)+1)+5 = 3*x by omega]
      omega

private theorem nth_values : Nat.nth InT = values := by
  have infinite : (Set.ofPred InT).Infinite := by
    rw [← values_range]
    exact Set.infinite_range_of_injective values_mono.injective
  exact ((Nat.nth_strictMono infinite).range_inj values_mono).mp
    ((Nat.range_nth_of_infinite infinite).trans values_range.symm)

private theorem first_column (n : ℕ) (hn : 1 ≤ n) : t n = (4*n+1)/3 := by
  rw [t, nth_values]
  unfold values
  omega

private theorem iterate_s (x j : ℕ) (hx : 0 < x) :
    (0 < s^[j] x) ∧ 3 * ((s^[j] x : ℕ) : ℤ) - 2 = (3 * (x : ℤ) - 2) * 4^j := by
  induction j with
  | zero => simpa using hx
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      have hy : 0 < s^[j] x := ih.1
      have hs : ((s (s^[j] x) : ℕ) : ℤ) = 4 * ((s^[j] x : ℕ) : ℤ) - 2 := by
        change ((4 * (s^[j] x) - 2 : ℕ) : ℤ) = _
        rw [Int.natCast_sub (by omega)]
        simp only [Nat.cast_mul, Nat.cast_ofNat]
      constructor
      · change 0 < 4 * (s^[j] x) - 2
        omega
      · rw [hs, pow_succ, ← mul_assoc, ← ih.2]
        ring

theorem formula (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    (D n k : ℤ) = (8 + (3 * (((4 * n + 1) / 3 : ℕ) : ℤ) - 2) * 4 ^ k) / 12 := by
  rw [← first_column n hn]
  have ht : 0 < t n := by rw [first_column n hn]; omega
  have hi := (iterate_s (t n) (k-1) ht).2
  have hpow : (4 : ℤ)^k = 4^(k-1) * 4 := by
    conv_lhs => rw [show k = (k-1)+1 by omega]
    rw [pow_succ]
  have he : 8 + (3 * (t n : ℤ) - 2) * 4^k = 12 * (D n k : ℤ) := by
    unfold D
    rw [hpow, ← mul_assoc, ← hi]
    ring
  rw [he, Int.mul_ediv_cancel_left _ (by decide : (12 : ℤ) ≠ 0)]

end OMA.A191668

theorem OMA.solution : type_of% @OMA.S_oeis_a191668.main := OMA.A191668.formula