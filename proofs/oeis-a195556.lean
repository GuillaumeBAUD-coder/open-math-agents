import OMAStatements.S_oeis_a195556
import Mathlib

namespace OMA.S_oeis_a195556

def Sstep (q : ℕ) (p : ℕ × ℕ) : ℕ × ℕ := (q * p.1 + p.2, p.1)

def S (q0 q1 q2 : ℕ) : ℕ → (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)
  | 0 => ((1, 0), (1, 0), (1, 0))
  | n + 1 => (Sstep q0 (S q0 q1 q2 n).2.1, Sstep q1 (S q0 q1 q2 n).2.2, Sstep q2 (S q0 q1 q2 n).1)

lemma conv_S (x0 x1 x2 : ℝ) (q0 q1 q2 : ℕ) (f0 : ⌊x0⌋₊ = q0) (f1 : ⌊x1⌋₊ = q1)
    (f2 : ⌊x2⌋₊ = q2) (r0 : (x0 - (⌊x0⌋₊ : ℝ))⁻¹ = x1) (r1 : (x1 - (⌊x1⌋₊ : ℝ))⁻¹ = x2)
    (r2 : (x2 - (⌊x2⌋₊ : ℝ))⁻¹ = x0) :
    ∀ n, conv x0 n = (S q0 q1 q2 n).1 ∧ conv x1 n = (S q0 q1 q2 n).2.1 ∧
      conv x2 n = (S q0 q1 q2 n).2.2 := by
  intro n
  induction n with
  | zero => simp [conv, S]
  | succ n ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · rw [conv, r0, h1, f0]; simp [S, Sstep]
    · rw [conv, r1, h2, f1]; simp [S, Sstep]
    · rw [conv, r2, h0, f2]; simp [S, Sstep]

def Inv (p : ℕ × ℕ) : Prop := Nat.Coprime p.1 p.2 ∧ p.2 ≤ p.1

lemma Inv_step (q : ℕ) (hq : 1 ≤ q) (p : ℕ × ℕ) (h : Inv p) : Inv (Sstep q p) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, by simp only [Sstep]; nlinarith [Nat.zero_le p.2]⟩
  simp only [Sstep, Nat.Coprime] at h1 ⊢
  rw [Nat.gcd_comm, add_comm, Nat.gcd_add_mul_right_right]
  exact h1

lemma S_inv (q0 q1 q2 : ℕ) (h0 : 1 ≤ q0) (h1 : 1 ≤ q1) (h2 : 1 ≤ q2) : ∀ n, Inv (S q0 q1 q2 n).1 ∧ Inv (S q0 q1 q2 n).2.1 ∧
    Inv (S q0 q1 q2 n).2.2 := by
  intro n
  induction n with
  | zero => simp [S, Inv]
  | succ n ih =>
    obtain ⟨i0, i1, i2⟩ := ih
    exact ⟨Inv_step _ h0 _ i1, Inv_step _ h1 _ i2, Inv_step _ h2 _ i0⟩

lemma red_eq (u v : ℕ) (cop : Nat.Coprime u v) (hle : v ≤ u) :
    2 * (u * v) / Nat.gcd (2 * (u * v)) (u ^ 2 - v ^ 2) =
      if (u + v) % 2 = 1 then 2 * (u * v) else u * v := by
  have hsq : v ^ 2 ≤ u ^ 2 := Nat.pow_le_pow_left hle 2
  have cu : Nat.Coprime u (u ^ 2 - v ^ 2) := by
    apply Nat.eq_one_of_dvd_one
    have h1 : Nat.gcd u (u ^ 2 - v ^ 2) ∣ u := Nat.gcd_dvd_left _ _
    have h2 : Nat.gcd u (u ^ 2 - v ^ 2) ∣ u ^ 2 - v ^ 2 := Nat.gcd_dvd_right _ _
    have h3 : Nat.gcd u (u ^ 2 - v ^ 2) ∣ v ^ 2 := by
      have h4 : Nat.gcd u (u ^ 2 - v ^ 2) ∣ u ^ 2 := Dvd.dvd.pow h1 (by norm_num)
      have := Nat.dvd_sub h4 h2
      rwa [Nat.sub_sub_self hsq] at this
    have h5 := Nat.dvd_gcd h1 h3
    rwa [(cop.pow_right 2 : Nat.Coprime u (v ^ 2)).gcd_eq_one] at h5
  have cv : Nat.Coprime v (u ^ 2 - v ^ 2) := by
    apply Nat.eq_one_of_dvd_one
    have h1 : Nat.gcd v (u ^ 2 - v ^ 2) ∣ v := Nat.gcd_dvd_left _ _
    have h2 : Nat.gcd v (u ^ 2 - v ^ 2) ∣ u ^ 2 - v ^ 2 := Nat.gcd_dvd_right _ _
    have h3 : Nat.gcd v (u ^ 2 - v ^ 2) ∣ u ^ 2 := by
      have h4 : Nat.gcd v (u ^ 2 - v ^ 2) ∣ v ^ 2 := Dvd.dvd.pow h1 (by norm_num)
      have := Nat.dvd_add h2 h4
      rwa [Nat.sub_add_cancel hsq] at this
    have h5 := Nat.dvd_gcd h1 h3
    rwa [(cop.symm.pow_right 2 : Nat.Coprime v (u ^ 2)).gcd_eq_one] at h5
  have cuv : Nat.Coprime (u * v) (u ^ 2 - v ^ 2) := Nat.Coprime.mul_left cu cv
  rw [Nat.Coprime.gcd_mul_right_cancel 2 cuv]
  have pu : u ^ 2 % 2 = u % 2 := by rw [Nat.pow_mod]; rcases Nat.mod_two_eq_zero_or_one u with h | h <;> simp [h]
  have pv : v ^ 2 % 2 = v % 2 := by rw [Nat.pow_mod]; rcases Nat.mod_two_eq_zero_or_one v with h | h <;> simp [h]
  by_cases hp : (u + v) % 2 = 1
  · have hw : (u ^ 2 - v ^ 2) % 2 = 1 := by omega
    have : Nat.gcd 2 (u ^ 2 - v ^ 2) = 1 := by rw [Nat.gcd_rec, hw]; rfl
    rw [this, if_pos hp]; simp
  · have hw : (u ^ 2 - v ^ 2) % 2 = 0 := by omega
    have : Nat.gcd 2 (u ^ 2 - v ^ 2) = 2 := by rw [Nat.gcd_rec, hw]; simp
    rw [this, if_neg hp]; omega


lemma fl (x : ℝ) (q : ℕ) (h1 : (q : ℝ) ≤ x) (h2 : x < q + 1) : ⌊x⌋₊ = q :=
  (Nat.floor_eq_iff (le_trans (Nat.cast_nonneg q) h1)).2 ⟨h1, h2⟩

lemma conv_inst : ∀ n, conv ((1+Real.sqrt 10)/3) n = (S 1 2 1 n).1 ∧ conv ((2+Real.sqrt 10)/2) n = (S 1 2 1 n).2.1 ∧
    conv ((2+Real.sqrt 10)/3) n = (S 1 2 1 n).2.2 := by
  have h := Real.sq_sqrt (show (0:ℝ) ≤ 10 by norm_num)
  have hl : (3:ℝ) < Real.sqrt 10 := by nlinarith [Real.sqrt_nonneg (10:ℝ)]
  have hh : Real.sqrt 10 < 4 := by nlinarith [Real.sqrt_nonneg (10:ℝ)]
  have f0 : ⌊((1+Real.sqrt 10)/3)⌋₊ = 1 := fl _ _ (by push_cast; linarith) (by push_cast; linarith)
  have f1 : ⌊((2+Real.sqrt 10)/2)⌋₊ = 2 := fl _ _ (by push_cast; linarith) (by push_cast; linarith)
  have f2 : ⌊((2+Real.sqrt 10)/3)⌋₊ = 1 := fl _ _ (by push_cast; linarith) (by push_cast; linarith)
  apply conv_S _ _ _ 1 2 1 f0 f1 f2
  · rw [f0]; apply inv_eq_of_mul_eq_one_right; push_cast; linear_combination (1/6) * h
  · rw [f1]; apply inv_eq_of_mul_eq_one_right; push_cast; linear_combination (1/6) * h
  · rw [f2]; apply inv_eq_of_mul_eq_one_right; push_cast; linear_combination (1/9) * h

def aS (n : ℕ) : ℕ :=
  if n = 0 then 0 else
    (2 * ((S 1 2 1 n).1.1 * (S 1 2 1 n).1.2)) /
      Nat.gcd (2 * ((S 1 2 1 n).1.1 * (S 1 2 1 n).1.2))
        ((S 1 2 1 n).1.1 ^ 2 - (S 1 2 1 n).1.2 ^ 2)

lemma aS_eq (n : ℕ) (hn : 1 ≤ n) :
    aS n = if ((S 1 2 1 n).1.1 + (S 1 2 1 n).1.2) % 2 = 1 then
      2 * ((S 1 2 1 n).1.1 * (S 1 2 1 n).1.2) else (S 1 2 1 n).1.1 * (S 1 2 1 n).1.2 := by
  unfold aS
  rw [if_neg (by omega)]
  have := (S_inv 1 2 1 (by norm_num) (by norm_num) (by norm_num) n).1
  exact red_eq _ _ this.1 this.2

lemma S3 (n : ℕ) :
    (S 1 2 1 (n + 3)).1.1 = 4 * (S 1 2 1 n).1.1 + 3 * (S 1 2 1 n).1.2 ∧
    (S 1 2 1 (n + 3)).1.2 = 3 * (S 1 2 1 n).1.1 + 2 * (S 1 2 1 n).1.2 := by
  simp only [S, Sstep]
  constructor <;> ring

lemma par3 (n : ℕ) : ((S 1 2 1 (n + 3)).1.1 + (S 1 2 1 (n + 3)).1.2) % 2 =
    ((S 1 2 1 n).1.1 + (S 1 2 1 n).1.2) % 2 := by
  obtain ⟨a, b⟩ := S3 n
  omega

lemma rec9 (n : ℕ) (hn : 1 ≤ n) : aS (n + 9) + aS n = 37 * aS (n + 6) + 37 * aS (n + 3) := by
  rw [aS_eq _ (by omega), aS_eq _ (by omega), aS_eq _ (by omega), aS_eq _ (by omega)]
  obtain ⟨a3, b3⟩ := S3 n
  obtain ⟨a6, b6⟩ := S3 (n + 3)
  obtain ⟨a9, b9⟩ := S3 (n + 6)
  have c3 := par3 n
  have c6 := par3 (n + 3)
  have c9 := par3 (n + 6)
  have e6 : n + 3 + 3 = n + 6 := rfl
  have e9 : n + 6 + 3 = n + 9 := rfl
  rw [e6] at a6 b6 c6
  rw [e9] at a9 b9 c9
  rw [c9, c6, c3]
  by_cases hp : ((S 1 2 1 n).1.1 + (S 1 2 1 n).1.2) % 2 = 1
  · rw [if_pos hp, if_pos hp, if_pos hp, if_pos hp, a9, b9, a6, b6, a3, b3]; ring
  · rw [if_neg hp, if_neg hp, if_neg hp, if_neg hp, a9, b9, a6, b6, a3, b3]; ring

lemma aS_vals : aS 0 = 0 ∧ aS 1 = 1 ∧ aS 2 = 12 ∧ aS 3 = 24 ∧ aS 4 = 35 ∧ aS 5 = 468 ∧ aS 6 = 900 ∧ aS 7 = 1333 ∧ aS 8 = 17760 ∧ aS 9 = 34188 := by decide +kernel

lemma a_eq (n : ℕ) : a n = (aS n : ℤ) := by
  unfold a aS
  by_cases h : n = 0
  · simp [h]
  · simp only [if_neg h]
    rw [(conv_inst n).1]

lemma rec_ok : ∀ n : ℕ, 10 ≤ n → a n = 37*a (n-3)+37*a (n-6)-a (n-9) := by
  intro n hn
  have h := rec9 (n - 9) (by omega)
  rw [show n - 9 + 9 = n by omega, show n - 9 + 6 = n - 3 by omega, show n - 9 + 3 = n - 6 by omega] at h
  simp only [a_eq]
  have h' : (aS n : ℤ) + aS (n - 9) = 37 * aS (n - 3) + 37 * aS (n - 6) := by exact_mod_cast h
  omega

open PowerSeries in
lemma gf_ok' : (X^9-37*X^6-37*X^3+1 : PowerSeries ℤ)*PowerSeries.mk a =
       X*(X^6+12*X^5+24*X^4-2*X^3+24*X^2+12*X+1) := by
  have h2 : ((X^9-37*X^6-37*X^3+1) : PowerSeries ℤ) * PowerSeries.mk a
      = PowerSeries.mk a - PowerSeries.C (37:ℤ) * (X^3 * PowerSeries.mk a)
        - PowerSeries.C (37:ℤ) * (X^6 * PowerSeries.mk a)
        + X^9 * PowerSeries.mk a := by
    rw [map_ofNat PowerSeries.C 37]; ring
  have h3 : (X * (X^6+12*X^5+24*X^4-2*X^3+24*X^2+12*X+1) : PowerSeries ℤ)
      = X + PowerSeries.C (12:ℤ) * X^2 + PowerSeries.C (24:ℤ) * X^3 - PowerSeries.C (2:ℤ) * X^4
        + PowerSeries.C (24:ℤ) * X^5 + PowerSeries.C (12:ℤ) * X^6 + X^7 := by
    rw [map_ofNat PowerSeries.C 12, map_ofNat PowerSeries.C 24, map_ofNat PowerSeries.C 2]; ring
  rw [h2, h3]
  ext n
  have hr := rec_ok
  have hs := aS_vals
  simp only [map_add, map_sub, PowerSeries.coeff_mk, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_X_pow, PowerSeries.coeff_X, PowerSeries.coeff_C_mul]
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9⟩ := hs
  by_cases hn : n ≤ 9
  · simp only [a_eq]
    interval_cases n <;> simp [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9]
  · have h := hr n (by omega)
    clear s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 hr
    split_ifs <;> omega

lemma gf_ok : (let X : PowerSeries ℤ := PowerSeries.X
     (X^9-37*X^6-37*X^3+1)*PowerSeries.mk a =
       X*(X^6+12*X^5+24*X^4-2*X^3+24*X^2+12*X+1)) := gf_ok'

end OMA.S_oeis_a195556

theorem OMA.solution : type_of% @OMA.S_oeis_a195556.main :=
  ⟨OMA.S_oeis_a195556.rec_ok, OMA.S_oeis_a195556.gf_ok⟩
