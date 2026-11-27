import OMAStatements.S_oeis_a096127
import Mathlib

namespace A096127Aux

/-- Digit sum of `m` in base `p`. -/
def ds (p m : ℕ) : ℕ := (p.digits m).sum

lemma legendre (p : ℕ) (hp : p.Prime) (m : ℕ) :
    (p - 1) * (m.factorial).factorization p = m - ds p m := by
  have h : Fact p.Prime := ⟨hp⟩
  rw [Nat.factorization_def _ hp]
  exact sub_one_mul_padicValNat_factorial m

lemma ds_le (p m : ℕ) : ds p m ≤ m := Nat.digit_sum_le p m

lemma ds_zero (p : ℕ) : ds p 0 = 0 := by simp [ds]

lemma ds_add (p : ℕ) (hp : p.Prime) (a b : ℕ) : ds p (a + b) ≤ ds p a + ds p b := by
  have h1 := legendre p hp a
  have h2 := legendre p hp b
  have h3 := legendre p hp (a + b)
  have hdvd : a.factorial * b.factorial ∣ (a + b).factorial :=
    Nat.factorial_mul_factorial_dvd_factorial_add a b
  have hle := (Nat.factorization_le_iff_dvd
    (mul_ne_zero (Nat.factorial_ne_zero a) (Nat.factorial_ne_zero b))
    (Nat.factorial_ne_zero (a + b))).mpr hdvd p
  rw [Nat.factorization_mul (Nat.factorial_ne_zero a) (Nat.factorial_ne_zero b)] at hle
  simp only [Finsupp.coe_add, Pi.add_apply] at hle
  have h4 : (p - 1) * ((a.factorial).factorization p + (b.factorial).factorization p)
      ≤ (p - 1) * ((a + b).factorial).factorization p := Nat.mul_le_mul_left _ hle
  rw [Nat.mul_add, h1, h2, h3] at h4
  have := ds_le p a
  have := ds_le p b
  have := ds_le p (a + b)
  omega

lemma ds_step (p : ℕ) (hp : 1 < p) (m : ℕ) (hm : 0 < m) :
    ds p m = m % p + ds p (m / p) := by
  unfold ds
  rw [Nat.digits_def' hp hm, List.sum_cons]

lemma ds_base_mul (p : ℕ) (hp : 1 < p) (m : ℕ) : ds p (p * m) = ds p m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · unfold ds
    rw [Nat.digits_base_mul hp hm, List.sum_cons, zero_add]

lemma ds_mul_le (p : ℕ) (hp : p.Prime) (d a : ℕ) : ds p (d * a) ≤ d * ds p a := by
  induction d with
  | zero => simp [ds_zero]
  | succ d ih =>
    have h := ds_add p hp (d * a) a
    have e : (d + 1) * a = d * a + a := by ring
    have e2 : (d + 1) * ds p a = d * ds p a + ds p a := by ring
    rw [e, e2]
    omega

lemma ds_mul (p : ℕ) (hp : p.Prime) (a : ℕ) :
    ∀ b : ℕ, ds p (a * b) ≤ ds p a * ds p b := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp [ds_zero]
    · have hp1 : 1 < p := hp.one_lt
      have hlt : b / p < b := Nat.div_lt_self hb hp1
      have ih' := ih (b / p) hlt
      have hstep := ds_step p hp1 b hb
      have hdecomp : a * b = p * (a * (b / p)) + (b % p) * a := by
        have hdm := Nat.div_add_mod b p
        calc a * b = a * (p * (b / p) + b % p) := by rw [hdm]
          _ = p * (a * (b / p)) + (b % p) * a := by ring
      have h1 := ds_add p hp (p * (a * (b / p))) ((b % p) * a)
      have h2 := ds_base_mul p hp1 (a * (b / p))
      have h3 := ds_mul_le p hp (b % p) a
      have e : ds p a * (b % p + ds p (b / p))
          = (b % p) * ds p a + ds p a * ds p (b / p) := by ring
      rw [hdecomp, hstep, e]
      omega

lemma ds_one (p : ℕ) (hp : 1 < p) :
    ∀ n : ℕ, 0 < n → 1 ≤ ds p n ∧ (ds p n = 1 → ∃ k : ℕ, n = p ^ k) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    have hstep := ds_step p hp n hn
    have hdm := Nat.div_add_mod n p
    rcases Nat.eq_zero_or_pos (n / p) with h0 | hpos
    · rw [h0, ds_zero] at hstep
      rw [h0] at hdm
      constructor
      · omega
      · intro h1
        refine ⟨0, ?_⟩
        rw [pow_zero]
        omega
    · have hlt : n / p < n := Nat.div_lt_self hn hp
      have ih1 : 1 ≤ ds p (n / p) := (ih (n / p) hlt hpos).1
      constructor
      · omega
      · intro h1
        have hm0 : n % p = 0 := by omega
        have hd1 : ds p (n / p) = 1 := by omega
        obtain ⟨k, hk⟩ := (ih (n / p) hlt hpos).2 hd1
        refine ⟨k + 1, ?_⟩
        rw [pow_succ, ← hk]
        rw [hm0] at hdm
        linarith [Nat.mul_comm p (n / p)]

lemma two_le_ds (p n : ℕ) (hp : p.Prime) (hn : 2 ≤ n) (hnpp : ¬ IsPrimePow n) :
    2 ≤ ds p n := by
  have h1 : 1 ≤ ds p n := (ds_one p hp.one_lt n (by omega)).1
  by_contra hlt
  have h2 : ds p n = 1 := by omega
  obtain ⟨k, hk⟩ := (ds_one p hp.one_lt n (by omega)).2 h2
  apply hnpp
  rw [isPrimePow_nat_iff]
  refine ⟨p, k, hp, ?_, hk.symm⟩
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · rw [hk0, pow_zero] at hk
    omega
  · exact hk0

lemma arith (n s sq t : ℕ) (hs2 : 2 ≤ s) (ht : n = s + t) (hsq : sq ≤ s * s) :
    (n + 2) * t + sq ≤ n ^ 2 := by
  have e3 : n ^ 2 = s * s + 2 * (s * t) + t * t := by rw [ht]; ring
  have e4 : (n + 2) * t = s * t + t * t + 2 * t := by rw [ht]; ring
  have e5 : 2 * t ≤ s * t := Nat.mul_le_mul_right t hs2
  rw [e3, e4]
  omega

end A096127Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a096127.main := by
  intro n hn _h1 h2
  by_contra hnpp
  apply h2
  have hd : n.factorial ^ (n + 2) ≠ 0 := pow_ne_zero _ (Nat.factorial_ne_zero n)
  have hN : (n ^ 2).factorial ≠ 0 := Nat.factorial_ne_zero _
  rw [← Nat.factorization_prime_le_iff_dvd hd hN]
  intro p hp
  rw [Nat.factorization_pow]
  simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  have hp1 : 1 < p := hp.one_lt
  have hL1 := A096127Aux.legendre p hp n
  have hL2 := A096127Aux.legendre p hp (n ^ 2)
  have hs_le := A096127Aux.ds_le p n
  have hsq : A096127Aux.ds p (n ^ 2) ≤ A096127Aux.ds p n * A096127Aux.ds p n := by
    rw [pow_two]
    exact A096127Aux.ds_mul p hp n n
  have hs2 : 2 ≤ A096127Aux.ds p n := A096127Aux.two_le_ds p n hp hn hnpp
  have hpp : 0 < p - 1 := Nat.sub_pos_of_lt hp1
  refine Nat.le_of_mul_le_mul_left ?_ hpp
  have e1 : (p - 1) * ((n + 2) * (n.factorial).factorization p)
      = (n + 2) * ((p - 1) * (n.factorial).factorization p) := by ring
  rw [e1, hL1, hL2]
  apply Nat.le_sub_of_add_le
  exact A096127Aux.arith n (A096127Aux.ds p n) (A096127Aux.ds p (n ^ 2))
    (n - A096127Aux.ds p n) hs2 (Nat.add_sub_cancel' hs_le).symm hsq
