import OMAStatements.S_oeis_a105596

open OMA.S_oeis_a105596
open scoped BigOperators

private theorem b_odd (n : ℕ) : b n % 2 = 1 := by
  apply (ZMod.natCast_eq_natCast_iff' (b n) 1 2).mp
  unfold b T
  simp only [Nat.cast_sum, Nat.cast_mul, ZMod.natCast_mod]
  rw [Finset.sum_comm]
  have hchoose (j : ℕ) (hj : j < n+1) :
      (∑ k ∈ Finset.range (n+1), (j.choose k : ZMod 2)) = (2 : ZMod 2)^j := by
    have h : (∑ k ∈ Finset.range (n+1), j.choose k) = 2^j := by
      rw [← Nat.sum_range_choose]
      symm
      apply Finset.sum_subset (Finset.range_mono hj)
      intro k _ hk
      exact Nat.choose_eq_zero_of_lt (by simpa using hk)
    simpa only [Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat] using
      congrArg (fun x : ℕ => (x : ZMod 2)) h
  have hsum :
      (∑ j ∈ Finset.range (n+1), ∑ k ∈ Finset.range (n+1),
        ((ArithmeticFunction.moebius (n.choose j)).natAbs : ZMod 2) * (j.choose k : ZMod 2)) =
      ∑ j ∈ Finset.range (n+1),
        ((ArithmeticFunction.moebius (n.choose j)).natAbs : ZMod 2) * (2 : ZMod 2)^j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [← Finset.mul_sum, hchoose j (Finset.mem_range.mp hj)]
  rw [hsum, Finset.sum_eq_single 0]
  · simp
  · intro j _ hj
    rw [show (2 : ZMod 2) = 0 by decide, zero_pow hj, mul_zero]
  · simp

private def summand (m k : ℕ) : ℤ := (b k : ℤ) * (-1)^k * (b (m-k) : ℤ)

private theorem reflected (m k : ℕ) (hk : k ≤ m) :
    summand m (m-k) = (-1 : ℤ)^m * summand m k := by
  have hsign : (-1 : ℤ)^(m-k) = (-1 : ℤ)^m * (-1 : ℤ)^k := by
    rw [← pow_add]
    apply neg_one_pow_congr
    rw [Nat.even_iff, Nat.even_iff]
    omega
  unfold summand
  rw [Nat.sub_sub_self hk, hsign]
  ring

private theorem split_center (f : ℕ → ℤ) (n : ℕ) :
    (∑ k ∈ Finset.range (2*n+1), f k) =
      (∑ k ∈ Finset.range n, (f k + f (2*n-k))) + f n := by
  rw [show 2*n+1=n+(n+1) by omega, Finset.sum_range_add, Finset.sum_range_succ',
    Nat.add_zero, Finset.sum_add_distrib, add_assoc]
  rw [← Finset.sum_range_reflect (fun i => f (n + (i+1))) n]
  congr 2
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  congr 1
  omega

private theorem square_odd (x : ℕ) (hx : x%2=1) : (x : ZMod 4)^2 = 1 := by
  have h : x = 2*(x/2)+1 := by omega
  conv_lhs => rw [h]
  push_cast
  calc
    (2 * (↑(x/2) : ZMod 4) + 1)^2 =
        4 * ((↑(x/2) : ZMod 4)^2 + ↑(x/2)) + 1 := by ring
    _ = 1 := by rw [show (4 : ZMod 4)=0 by decide, zero_mul, zero_add]

private theorem twice_odd (x : ℕ) (hx : x%2=1) : 2 * (x : ZMod 4) = 2 := by
  have h : x = 2*(x/2)+1 := by omega
  conv_lhs => rw [h]
  push_cast
  calc
    2 * (2 * (↑(x/2) : ZMod 4) + 1) = 4 * (↑(x/2) : ZMod 4) + 2 := by ring
    _ = 2 := by rw [show (4 : ZMod 4)=0 by decide, zero_mul, zero_add]

private theorem twice_sign (k : ℕ) : 2 * (-1 : ZMod 4)^k = 2 := by
  rcases neg_one_pow_eq_or (R := ZMod 4) k with h | h <;> rw [h] <;> decide

private theorem even_convolution (n : ℕ) : (c (2*n) : ZMod 4) = 1 := by
  change ((∑ k ∈ Finset.range (2*n+1), summand (2*n) k : ℤ) : ZMod 4) = 1
  rw [split_center]
  push_cast
  have hp (k : ℕ) (hk : k ∈ Finset.range n) :
      (summand (2*n) k : ZMod 4) + (summand (2*n) (2*n-k) : ZMod 4) = 2 := by
    have hn : k ≤ 2*n := by have := Finset.mem_range.mp hk; omega
    rw [reflected _ _ hn, show (-1 : ℤ)^(2*n)=1 by simp [pow_mul], one_mul, ← two_mul]
    unfold summand
    push_cast
    rw [← mul_assoc, ← mul_assoc, twice_odd _ (b_odd _), twice_sign, twice_odd _ (b_odd _)]
  rw [Finset.sum_congr rfl hp, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  unfold summand
  rw [show 2*n-n=n by omega]
  push_cast
  rw [mul_comm (b n : ZMod 4) ((-1 : ZMod 4)^n), mul_assoc,
    ← sq, square_odd _ (b_odd _), mul_one]
  by_cases hn : n % 2 = 0
  · have h : Even n := Nat.even_iff.mpr hn
    have h₂ : (n : ZMod 4) * 2 = 0 := by
      obtain ⟨k,hk⟩ := h
      rw [hk]
      push_cast
      calc
        ((k : ZMod 4) + k) * 2 = 4 * k := by ring
        _ = 0 := by rw [show (4 : ZMod 4)=0 by decide, zero_mul]
    rw [h₂, h.neg_one_pow, zero_add]
  · have h : Odd n := Nat.odd_iff.mpr (by omega)
    rw [mul_comm (n : ZMod 4) 2, twice_odd n (by omega), h.neg_one_pow]
    decide

private theorem odd_convolution (n : ℕ) : c (2*n+1) = 0 := by
  change (∑ k ∈ Finset.range (2*n+1+1), summand (2*n+1) k) = 0
  let m := 2*n+1
  change (∑ k ∈ Finset.range (m+1), summand m k) = 0
  have href := Finset.sum_range_reflect (summand m) (m+1)
  simp only [Nat.add_sub_cancel] at href
  have hs : (∑ k ∈ Finset.range (m+1), summand m (m-k)) =
      -(∑ k ∈ Finset.range (m+1), summand m k) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [reflected _ _ (by have := Finset.mem_range.mp hk; omega)]
    simp [m, pow_add, pow_mul]
  rw [hs] at href
  linarith

theorem OMA.solution : type_of% @OMA.S_oeis_a105596.main := by
  intro n
  refine ⟨?_, odd_convolution n⟩
  have h := congrArg (fun z : ZMod 4 => (z.val : ℤ)) (even_convolution n)
  change (((c (2*n) : ZMod 4).val : ℕ) : ℤ) = 1 at h
  rwa [ZMod.val_intCast] at h