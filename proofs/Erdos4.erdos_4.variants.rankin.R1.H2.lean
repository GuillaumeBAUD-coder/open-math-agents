import OMAReductions.R_Erdos4_erdos_4_variants_rankin_R1

/-!
Step `Erdos4.erdos_4.variants.rankin.R1.H2`:
weak Chebyshev lower bound `x ≤ Nat.primeCounting x ^ 2` for all sufficiently large `x`.
-/

-- Step Erdos4.erdos_4.variants.rankin.R1.H2: hypothesis H2 of reduction Erdos4.erdos_4.variants.rankin.R1
-- Credit: @ronak14p
-- H2 := ∃ N : ℕ, ∀ x : ℕ, N ≤ x → x ≤ Nat.primeCounting x ^ 2

private lemma centralBinom_le_pow_primeCounting {n : ℕ} (hn : 0 < n) :
    n.centralBinom ≤ (2 * n) ^ Nat.primeCounting (2 * n) := by
  let S := (Finset.range (2 * n + 1)).filter Nat.Prime
  have hprod : ∏ p ∈ S, p ^ n.centralBinom.factorization p =
      ∏ p ∈ Finset.range (2 * n + 1), p ^ n.centralBinom.factorization p := by
    refine Finset.prod_filter_of_ne fun p _ h => ?_
    contrapose h
    rw [Nat.factorization_eq_zero_of_not_prime n.centralBinom h, pow_zero]
  have hcard : S.card = Nat.primeCounting (2 * n) := by
    simp [S, Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  calc
    n.centralBinom
        = ∏ p ∈ Finset.range (2 * n + 1), p ^ n.centralBinom.factorization p :=
          n.prod_pow_factorization_centralBinom.symm
    _ = ∏ p ∈ S, p ^ n.centralBinom.factorization p := hprod.symm
    _ ≤ ∏ _p ∈ S, (2 * n) := by
          refine Finset.prod_le_prod' fun p _ => ?_
          rw [Nat.centralBinom_eq_two_mul_choose]
          exact Nat.pow_factorization_choose_le (by omega)
    _ = (2 * n) ^ S.card := Finset.prod_const _
    _ = (2 * n) ^ Nat.primeCounting (2 * n) := by rw [hcard]

private lemma ten_mul_sq_le_four_pow {r : ℕ} (hr : 4 ≤ r) :
    10 * (r + 1) ^ 2 ≤ 4 ^ r := by
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    calc
      10 * (k + 1 + 1) ^ 2 ≤ 4 * (10 * (k + 1) ^ 2) := by nlinarith
      _ ≤ 4 * 4 ^ k := Nat.mul_le_mul_left 4 ih
      _ = 4 ^ (k + 1) := by ring

theorem OMA.solution : OMA.R_Erdos4_erdos_4_variants_rankin_R1.H2 := by
  refine ⟨160, fun x hx => ?_⟩
  by_contra hlt
  have hlt : Nat.primeCounting x ^ 2 < x := Nat.lt_of_not_ge hlt
  set n := x / 2
  set s := Nat.primeCounting x
  have hn80 : 80 ≤ n := by omega
  have h2n_le : 2 * n ≤ x := Nat.mul_div_le x 2
  have hs2 : s ^ 2 ≤ 2 * n := by omega
  have hcb_lo : 4 ^ n < n * n.centralBinom :=
    Nat.four_pow_lt_mul_centralBinom n (by omega)
  have hcb_hi : n.centralBinom ≤ (2 * n) ^ Nat.primeCounting (2 * n) :=
    centralBinom_le_pow_primeCounting (by omega)
  have hpi : Nat.primeCounting (2 * n) ≤ s :=
    Nat.monotone_primeCounting h2n_le
  have hpow_hi : 4 ^ n < (2 * n) ^ (s + 1) := by
    calc
      4 ^ n < n * n.centralBinom := hcb_lo
      _ ≤ (2 * n) * (2 * n) ^ Nat.primeCounting (2 * n) :=
          Nat.mul_le_mul (by omega) hcb_hi
      _ ≤ (2 * n) * (2 * n) ^ s :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hpi)
      _ = (2 * n) ^ (s + 1) := by rw [pow_succ']
  set r := n / (s + 1)
  have hr_mul_le : r * (s + 1) ≤ n := Nat.div_mul_le_self n (s + 1)
  have hn_lt : n < (r + 1) * (s + 1) := by
    have hdm : (s + 1) * r + n % (s + 1) = n := Nat.div_add_mod n (s + 1)
    have hmod : n % (s + 1) < s + 1 := Nat.mod_lt n (Nat.succ_pos s)
    nlinarith
  have h2s : 2 * s ≤ s ^ 2 + 1 := by
    rcases s with _ | s'
    · omega
    · nlinarith
  have hs1_sq : (s + 1) ^ 2 ≤ 5 * n := by nlinarith
  have hn_sq : n ^ 2 < (r + 1) ^ 2 * (s + 1) ^ 2 := by
    have h1 : n ^ 2 < ((r + 1) * (s + 1)) ^ 2 := Nat.pow_lt_pow_left hn_lt (by norm_num)
    rwa [mul_pow] at h1
  have hn_bound : n < 5 * (r + 1) ^ 2 := by
    have : n * n < n * (5 * (r + 1) ^ 2) := by nlinarith
    exact Nat.lt_of_mul_lt_mul_left this
  have hr4 : 4 ≤ r := by
    by_contra hr_lt
    have hr_lt : r < 4 := Nat.lt_of_not_ge hr_lt
    have : (r + 1) ^ 2 ≤ 16 := by nlinarith
    omega
  have h2n_le_4r : 2 * n ≤ 4 ^ r := by
    have h10 := ten_mul_sq_le_four_pow hr4
    omega
  have hpow_le : (2 * n) ^ (s + 1) ≤ 4 ^ n := by
    calc
      (2 * n) ^ (s + 1) ≤ (4 ^ r) ^ (s + 1) := Nat.pow_le_pow_left h2n_le_4r _
      _ = 4 ^ (r * (s + 1)) := (pow_mul 4 r (s + 1)).symm
      _ ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) hr_mul_le
  omega

