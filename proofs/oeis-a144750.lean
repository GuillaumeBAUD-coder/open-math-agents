import OMAStatements.S_oeis_a144750
import Mathlib

namespace OMA.S_oeis_a144750_proof

open OMA.S_oeis_a144750

lemma sum_choose_succ (n : ℕ) (f : ℕ → ZMod 3) :
    ∑ k ∈ Finset.range (n + 2), ((n + 1).choose k : ZMod 3) * f k =
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ZMod 3) * (f k + f (k + 1)) := by
  rw [Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul]
  have hsplit :
      ∑ k ∈ Finset.range (n + 1), ((n + 1).choose (k + 1) : ZMod 3) * f (k + 1) =
      (∑ k ∈ Finset.range (n + 1), (n.choose k : ZMod 3) * f (k + 1)) +
      ∑ k ∈ Finset.range (n + 1), (n.choose (k + 1) : ZMod 3) * f (k + 1) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [Nat.choose_succ_succ, Nat.cast_add, add_mul]
  rw [hsplit]
  have hshift :
      (∑ k ∈ Finset.range (n + 1), (n.choose (k + 1) : ZMod 3) * f (k + 1)) + f 0 =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ZMod 3) * f k := by
    have h1 :
        ∑ k ∈ Finset.range (n + 2), (n.choose k : ZMod 3) * f k =
        (∑ k ∈ Finset.range (n + 1), (n.choose (k + 1) : ZMod 3) * f (k + 1)) + f 0 := by
      rw [Finset.sum_range_succ']
      simp
    have h2 :
        ∑ k ∈ Finset.range (n + 2), (n.choose k : ZMod 3) * f k =
        ∑ k ∈ Finset.range (n + 1), (n.choose k : ZMod 3) * f k := by
      rw [Finset.sum_range_succ, Nat.choose_succ_self]
      simp
    rw [← h1, h2]
  calc
    (∑ k ∈ Finset.range (n + 1), (n.choose k : ZMod 3) * f (k + 1)) +
        (∑ k ∈ Finset.range (n + 1), (n.choose (k + 1) : ZMod 3) * f (k + 1)) + f 0
      = (∑ k ∈ Finset.range (n + 1), (n.choose k : ZMod 3) * f (k + 1)) +
          ((∑ k ∈ Finset.range (n + 1), (n.choose (k + 1) : ZMod 3) * f (k + 1)) + f 0) := by ring
    _ = (∑ k ∈ Finset.range (n + 1), (n.choose k : ZMod 3) * f (k + 1)) +
          ∑ k ∈ Finset.range (n + 1), (n.choose k : ZMod 3) * f k := by rw [hshift]
    _ = ∑ k ∈ Finset.range (n + 1), (n.choose k : ZMod 3) * (f k + f (k + 1)) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro k _
          ring

def A (n : ℕ) : ZMod 3 :=
  ∑ k ∈ Finset.range (n + 1), (n.choose k : ZMod 3) * (if k % 3 = 0 then 1 else 0)

def B (n : ℕ) : ZMod 3 :=
  ∑ k ∈ Finset.range (n + 1), (n.choose k : ZMod 3) * (if k % 3 = 1 then 1 else 0)

def C (n : ℕ) : ZMod 3 :=
  ∑ k ∈ Finset.range (n + 1), (n.choose k : ZMod 3) * (if k % 3 = 2 then 1 else 0)

def S (n : ℕ) : ZMod 3 :=
  ∑ k ∈ Finset.range (n + 1), (n.choose k : ZMod 3) * (((k + 1) / 3 : ℕ) : ZMod 3)

lemma A_succ (n : ℕ) : A (n + 1) = A n + C n := by
  unfold A C
  rw [sum_choose_succ, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  have hmod : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hmod with h | h | h <;> simp [h, Nat.add_mod]

lemma B_succ (n : ℕ) : B (n + 1) = B n + A n := by
  unfold B A
  rw [sum_choose_succ, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  have hmod : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hmod with h | h | h <;> simp [h, Nat.add_mod]

lemma C_succ (n : ℕ) : C (n + 1) = C n + B n := by
  unfold C B
  rw [sum_choose_succ, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  have hmod : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hmod with h | h | h <;> simp [h, Nat.add_mod]

lemma S_succ (n : ℕ) : S (n + 1) = 2 * S n + B n := by
  unfold S B
  rw [sum_choose_succ, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  have hdiv : ((k + 1 + 1) / 3 : ℕ) = (k + 1) / 3 + if k % 3 = 1 then 1 else 0 := by
    have hq : k = 3 * (k / 3) + k % 3 := (Nat.div_add_mod k 3).symm
    rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h | h | h
    · rw [h] at hq
      have h1 : (k + 1) / 3 = k / 3 := by omega
      have h2 : (k + 1 + 1) / 3 = k / 3 := by omega
      simp [h, h1, h2]
    · rw [h] at hq
      have h1 : (k + 1) / 3 = k / 3 := by omega
      have h2 : (k + 1 + 1) / 3 = k / 3 + 1 := by omega
      simp [h, h1, h2]
    · rw [h] at hq
      have h1 : (k + 1) / 3 = k / 3 + 1 := by omega
      have h2 : (k + 1 + 1) / 3 = k / 3 + 1 := by omega
      simp [h, h1, h2]
  rw [hdiv, Nat.cast_add]
  split_ifs <;> ring

def step4 (t : ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3) : ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 :=
  (t.1 + t.2.2.1, t.2.1 + t.1, t.2.2.1 + t.2.1, 2 * t.2.2.2 + t.2.1)

lemma tuple_eq (n : ℕ) : (A n, B n, C n, S n) = step4^[n] (1, 0, 0, 0) := by
  induction n with
  | zero =>
    simp [A, B, C, S]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ← ih]
    ext <;> simp [step4, A_succ, B_succ, C_succ, S_succ]

lemma step4_18 : step4^[18] (1, 0, 0, 0) = (1, 0, 0, 0) := by
  decide

lemma S_mod18 (n : ℕ) : S n = S (n % 18) := by
  have h : step4^[n] (1, 0, 0, 0) = step4^[n % 18] (1, 0, 0, 0) := by
    conv_lhs => rw [← Nat.div_add_mod n 18, add_comm, Function.iterate_add_apply]
    have hq : ∀ q, step4^[18 * q] (1, 0, 0, 0) = (1, 0, 0, 0) := by
      intro q
      induction q with
      | zero => simp
      | succ q ihq =>
        rw [mul_add, mul_one, Function.iterate_add_apply, step4_18, ihq]
    rw [hq]
  have h1 : S n = (step4^[n] (1, 0, 0, 0)).2.2.2 := congrArg (fun p => p.2.2.2) (tuple_eq n)
  have h2 : S (n % 18) = (step4^[n % 18] (1, 0, 0, 0)).2.2.2 := congrArg (fun p => p.2.2.2) (tuple_eq (n % 18))
  rw [h1, h2, h]

lemma three_mul_cast_mod3 (x : ℕ) : (3 : ZMod 9) * (x : ZMod 9) = 3 * ((x : ZMod 3).val : ZMod 9) := by
  have hx : (x : ZMod 3).val = x % 3 := ZMod.val_natCast (n := 3) x
  rw [hx]
  have hdiv : x = 3 * (x / 3) + x % 3 := (Nat.div_add_mod x 3).symm
  conv_lhs => rw [hdiv, Nat.cast_add, Nat.cast_mul]
  have h9 : (3 : ZMod 9) * (3 : ZMod 9) = 0 := by decide
  calc
    (3 : ZMod 9) * ((3 : ZMod 9) * ((x / 3 : ℕ) : ZMod 9) + ((x % 3 : ℕ) : ZMod 9))
      = (3 * 3) * ((x / 3 : ℕ) : ZMod 9) + 3 * ((x % 3 : ℕ) : ZMod 9) := by ring
    _ = 3 * ((x % 3 : ℕ) : ZMod 9) := by rw [h9, zero_mul, zero_add]

lemma three_mul_mod3 (x y : ℕ) (h : x % 3 = y % 3) :
    (3 : ZMod 9) * (x : ZMod 9) = 3 * (y : ZMod 9) := by
  have hx := three_mul_cast_mod3 x
  have hy := three_mul_cast_mod3 y
  rw [hx, hy]
  simp only [ZMod.val_natCast, h]

lemma three_mul_S (n : ℕ) :
    (3 : ZMod 9) * (∑ k ∈ Finset.range (n + 1), (n.choose k : ZMod 9) * (((k + 1) / 3 : ℕ) : ZMod 9)) =
    3 * ((S n).val : ZMod 9) := by
  rw [Finset.mul_sum]
  have hLHS :
      ∑ k ∈ Finset.range (n + 1), (3 : ZMod 9) * ((n.choose k : ZMod 9) * (((k + 1) / 3 : ℕ) : ZMod 9)) =
      3 * ((∑ k ∈ Finset.range (n + 1), (n.choose k : ℕ) * ((k + 1) / 3) : ℕ) : ZMod 9) := by
    rw [Nat.cast_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    push_cast
    ring
  rw [hLHS, three_mul_cast_mod3]
  congr 2
  unfold S
  simp only [Nat.cast_sum, Nat.cast_mul]

lemma pf_formula (n : ℕ) :
    (pseudoFactorial n : ZMod 9) = (-1 : ZMod 9) ^ n * (1 - 3 * (((n + 1) / 3 : ℕ) : ZMod 9)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | n
    · simp [pseudoFactorial]
    · rw [pseudoFactorial]
      rw [Fin.sum_univ_eq_sum_range (fun k => (n.choose k : ℤ) * pseudoFactorial k * pseudoFactorial (n - k))]
      push_cast
      have hsum :
          ∑ k ∈ Finset.range (n + 1), (n.choose k : ZMod 9) * (pseudoFactorial k : ZMod 9) * (pseudoFactorial (n - k) : ZMod 9) =
          (-1 : ZMod 9) ^ n *
            ((2 : ZMod 9) ^ n - 6 * ∑ k ∈ Finset.range (n + 1), (n.choose k : ZMod 9) * (((k + 1) / 3 : ℕ) : ZMod 9)) := by
        have hterm :
            ∀ k ∈ Finset.range (n + 1),
              (n.choose k : ZMod 9) * (pseudoFactorial k : ZMod 9) * (pseudoFactorial (n - k) : ZMod 9) =
              (-1 : ZMod 9) ^ n *
                ((n.choose k : ZMod 9) - 3 * (n.choose k : ZMod 9) * (((k + 1) / 3 : ℕ) : ZMod 9) -
                  3 * (n.choose k : ZMod 9) * (((n - k + 1) / 3 : ℕ) : ZMod 9)) := by
          intro k hk
          have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
          rw [ih k (by omega), ih (n - k) (by omega)]
          have hpow : (-1 : ZMod 9) ^ k * (-1 : ZMod 9) ^ (n - k) = (-1 : ZMod 9) ^ n := by
            rw [← pow_add, Nat.add_sub_cancel' hk_le]
          have h9 : (9 : ZMod 9) = 0 := by decide
          calc
            (n.choose k : ZMod 9) * ((-1 : ZMod 9) ^ k * (1 - 3 * (((k + 1) / 3 : ℕ) : ZMod 9))) *
                ((-1 : ZMod 9) ^ (n - k) * (1 - 3 * (((n - k + 1) / 3 : ℕ) : ZMod 9)))
              = ((-1 : ZMod 9) ^ k * (-1 : ZMod 9) ^ (n - k)) * (n.choose k : ZMod 9) *
                  (1 - 3 * (((k + 1) / 3 : ℕ) : ZMod 9) - 3 * (((n - k + 1) / 3 : ℕ) : ZMod 9) +
                    9 * (((k + 1) / 3 : ℕ) : ZMod 9) * (((n - k + 1) / 3 : ℕ) : ZMod 9)) := by ring
            _ = (-1 : ZMod 9) ^ n * ((n.choose k : ZMod 9) -
                  3 * (n.choose k : ZMod 9) * (((k + 1) / 3 : ℕ) : ZMod 9) -
                  3 * (n.choose k : ZMod 9) * (((n - k + 1) / 3 : ℕ) : ZMod 9)) := by
                  rw [hpow, h9]
                  ring
        rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
        congr 1
        simp only [Finset.sum_sub_distrib]
        simp_rw [mul_assoc, ← Finset.mul_sum]
        have h2n : ∑ k ∈ Finset.range (n + 1), (n.choose k : ZMod 9) = (2 : ZMod 9) ^ n := by
          rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]
        have hsymm :
            ∑ k ∈ Finset.range (n + 1), (n.choose k : ZMod 9) * (((n - k + 1) / 3 : ℕ) : ZMod 9) =
            ∑ k ∈ Finset.range (n + 1), (n.choose k : ZMod 9) * (((k + 1) / 3 : ℕ) : ZMod 9) := by
          let g : ℕ → ZMod 9 := fun k => (n.choose k : ZMod 9) * (((k + 1) / 3 : ℕ) : ZMod 9)
          have hr := Finset.sum_range_reflect g (n + 1)
          have hL :
              ∑ k ∈ Finset.range (n + 1), (n.choose k : ZMod 9) * (((n - k + 1) / 3 : ℕ) : ZMod 9) =
              ∑ k ∈ Finset.range (n + 1), g (n + 1 - 1 - k) := by
            apply Finset.sum_congr rfl
            intro k hk
            have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
            have hidx : n + 1 - 1 - k = n - k := by omega
            rw [hidx]
            simp only [g, Nat.choose_symm hk_le]
          rw [hL, hr]
        rw [h2n, hsymm]
        ring
      rw [hsum]
      have hsign : (-1 : ZMod 9) ^ (n + 1) * (-1 : ZMod 9) ^ n = -1 := by
        rw [← pow_add]
        have hodd : Odd (n + 1 + n) := ⟨n, by omega⟩
        rw [hodd.neg_one_pow]
      have h6 : (-1 : ZMod 9) * -6 = -3 := by decide
      calc
        (-1 : ZMod 9) ^ (n + 1) * ((-1 : ZMod 9) ^ n * ((2 : ZMod 9) ^ n -
            6 * ∑ k ∈ Finset.range (n + 1), (n.choose k : ZMod 9) * (((k + 1) / 3 : ℕ) : ZMod 9)))
          = ((-1 : ZMod 9) ^ (n + 1) * (-1 : ZMod 9) ^ n) * ((2 : ZMod 9) ^ n -
              6 * ∑ k ∈ Finset.range (n + 1), (n.choose k : ZMod 9) * (((k + 1) / 3 : ℕ) : ZMod 9)) := by ring
        _ = -(2 : ZMod 9) ^ n - 3 * ∑ k ∈ Finset.range (n + 1), (n.choose k : ZMod 9) * (((k + 1) / 3 : ℕ) : ZMod 9) := by
              rw [hsign]
              calc
                -1 * ((2 : ZMod 9) ^ n - 6 * _) = -(2 : ZMod 9) ^ n + (-1 * -6) * _ := by ring
                _ = -(2 : ZMod 9) ^ n + -3 * _ := by rw [h6]
                _ = -(2 : ZMod 9) ^ n - 3 * _ := by ring
      rw [three_mul_S, S_mod18]
      have h2_18 : (2 : ZMod 9) ^ n = (2 : ZMod 9) ^ (n % 18) := by
        conv_lhs => rw [← Nat.div_add_mod n 18]
        rw [pow_add, pow_mul]
        have h2_18_eq : (2 : ZMod 9) ^ 18 = 1 := by decide
        rw [h2_18_eq, one_pow, one_mul]
      have hm1_18 : (-1 : ZMod 9) ^ (n + 1) = (-1 : ZMod 9) ^ (n % 18 + 1) := by
        conv_lhs => rw [← Nat.div_add_mod n 18]
        rw [show 18 * (n / 18) + n % 18 + 1 = 18 * (n / 18) + (n % 18 + 1) by omega]
        rw [pow_add, pow_mul]
        have hm1_18_eq : (-1 : ZMod 9) ^ 18 = 1 := by decide
        rw [hm1_18_eq, one_pow, one_mul]
      have hdiv_18 :
          (3 : ZMod 9) * (((n + 1 + 1) / 3 : ℕ) : ZMod 9) =
          (3 : ZMod 9) * (((n % 18 + 1 + 1) / 3 : ℕ) : ZMod 9) :=
        three_mul_mod3 _ _ (by omega)
      rw [h2_18, hm1_18, hdiv_18]
      set r := n % 18
      have hr : r < 18 := Nat.mod_lt n (by norm_num)
      interval_cases r <;> decide

def tbl (r : ℕ) : ℤ :=
  ((((-1 : ZMod 9) ^ r * (1 - 3 * (((r + 1) / 3 : ℕ) : ZMod 9))) : ZMod 9).val : ℤ)

lemma a_eq_tbl (n : ℕ) : a n = tbl (n % 18) := by
  unfold a tbl
  have hz : pseudoFactorial n % 9 = (((pseudoFactorial n : ZMod 9).val : ℤ)) := by
    rw [ZMod.val_intCast]
    norm_num
  rw [hz, pf_formula]
  have hm1 : (-1 : ZMod 9) ^ n = (-1 : ZMod 9) ^ (n % 18) := by
    conv_lhs => rw [← Nat.div_add_mod n 18]
    rw [pow_add, pow_mul]
    have h : (-1 : ZMod 9) ^ 18 = 1 := by decide
    rw [h, one_pow, one_mul]
  have hdiv :
      (3 : ZMod 9) * (((n + 1) / 3 : ℕ) : ZMod 9) =
      (3 : ZMod 9) * (((n % 18 + 1) / 3 : ℕ) : ZMod 9) :=
    three_mul_mod3 _ _ (by omega)
  rw [hm1, hdiv]

lemma main_rec (n : ℕ) (hn : 7 < n) :
    a n = a (n - 2) + a (n - 3) - a (n - 5) - a (n - 6) + a (n - 8) := by
  simp only [a_eq_tbl]
  have h2 : (n - 2) % 18 = (n % 18 + 16) % 18 := by omega
  have h3 : (n - 3) % 18 = (n % 18 + 15) % 18 := by omega
  have h5 : (n - 5) % 18 = (n % 18 + 13) % 18 := by omega
  have h6 : (n - 6) % 18 = (n % 18 + 12) % 18 := by omega
  have h8 : (n - 8) % 18 = (n % 18 + 10) % 18 := by omega
  rw [h2, h3, h5, h6, h8]
  set r := n % 18
  have hr : r < 18 := Nat.mod_lt n (by norm_num)
  interval_cases r <;> decide

end OMA.S_oeis_a144750_proof

theorem OMA.solution : type_of% @OMA.S_oeis_a144750.main := by
  open OMA.S_oeis_a144750 OMA.S_oeis_a144750_proof in
  refine ⟨main_rec, ?_⟩
  dsimp only
  have hpoly :
      ((PowerSeries.X - 1) * (PowerSeries.X + 1) * (PowerSeries.X ^ 6 - PowerSeries.X ^ 3 + 1) : PowerSeries ℤ) =
      PowerSeries.X ^ 8 - PowerSeries.X ^ 6 - PowerSeries.X ^ 5 + PowerSeries.X ^ 3 + PowerSeries.X ^ 2 - 1 := by
    ring
  rw [hpoly]
  ext n
  have hX : ∀ k : ℕ, PowerSeries.coeff n (PowerSeries.mk a * (PowerSeries.X : PowerSeries ℤ) ^ k) =
      if k ≤ n then a (n - k) else 0 := by
    intro k
    rw [mul_comm, PowerSeries.coeff_X_pow_mul']
    split_ifs <;> simp
  have hRHS :
      ((-8 * PowerSeries.X ^ 7 - 4 * PowerSeries.X ^ 6 + 3 * PowerSeries.X ^ 5 +
        8 * PowerSeries.X ^ 4 + 7 * PowerSeries.X ^ 3 - 6 * PowerSeries.X ^ 2 -
        8 * PowerSeries.X - 1) : PowerSeries ℤ) =
      PowerSeries.C (-8) * PowerSeries.X ^ 7 + PowerSeries.C (-4) * PowerSeries.X ^ 6 +
        PowerSeries.C 3 * PowerSeries.X ^ 5 + PowerSeries.C 8 * PowerSeries.X ^ 4 +
        PowerSeries.C 7 * PowerSeries.X ^ 3 + PowerSeries.C (-6) * PowerSeries.X ^ 2 +
        PowerSeries.C (-8) * PowerSeries.X ^ 1 + PowerSeries.C (-1) * PowerSeries.X ^ 0 := by
    simp only [pow_one, pow_zero, mul_one, map_neg, map_one, map_ofNat]
    ring
  rw [hRHS]
  simp only [mul_sub, mul_add, mul_one, map_sub, map_add, hX, PowerSeries.coeff_mk]
  simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
  rcases Nat.lt_or_ge n 8 with hn | hn
  · interval_cases n <;> simp [a_eq_tbl, tbl] <;> decide
  · have hrec := main_rec n (by omega)
    have hne : n ≠ 7 ∧ n ≠ 6 ∧ n ≠ 5 ∧ n ≠ 4 ∧ n ≠ 3 ∧ n ≠ 2 ∧ n ≠ 1 ∧ n ≠ 0 := by omega
    simp only [hn, (by omega : 6 ≤ n), (by omega : 5 ≤ n), (by omega : 3 ≤ n), (by omega : 2 ≤ n),
      ↓reduceIte, hne.1, hne.2.1, hne.2.2.1, hne.2.2.2.1, hne.2.2.2.2.1, hne.2.2.2.2.2.1,
      hne.2.2.2.2.2.2.1, hne.2.2.2.2.2.2.2, mul_zero, add_zero]
    rw [hrec]
    ring
