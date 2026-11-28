import OMAStatements.S_oeis_a395429
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Order.Interval.Set.Defs

open OMA.S_oeis_a395429

private theorem leading_lt_ten (x : ℕ) : leading x < 10 := by
  apply (Nat.div_lt_iff_lt_mul (by positivity : 0 < 10 ^ Nat.log 10 x)).mpr
  simpa [pow_succ, Nat.mul_comm] using Nat.lt_pow_succ_log_self (by decide : 1 < 10) x

private theorem leading_pos {x : ℕ} (hx : 0 < x) : 0 < leading x := by
  exact Nat.div_pos (Nat.pow_log_le_self 10 hx.ne') (by positivity)

private theorem leading_bounds (x : ℕ) :
    leading x * 10 ^ Nat.log 10 x ≤ x ∧ x < (leading x + 1) * 10 ^ Nat.log 10 x :=
  ⟨Nat.div_mul_le_self x _, (by simpa [leading,Nat.mul_comm] using (Nat.lt_mul_div_succ x (by positivity : 0 < 10 ^ Nat.log 10 x)))⟩

private theorem leading_eq_from_bounds {x d a : ℕ} (hd : 1 ≤ d) (hd' : d ≤ 9)
    (lo : d * 10^a ≤ x) (hi : x < (d+1) * 10^a) : leading x = d := by
  have he : Nat.log 10 x = a := Nat.log_eq_of_pow_le_of_lt_pow
    (by calc 10^a = 1 * 10^a := by simp
             _ ≤ d * 10^a := Nat.mul_le_mul_right _ hd
             _ ≤ x := lo)
    (by rw [pow_succ']; exact hi.trans_le (Nat.mul_le_mul_right _ (by omega)))
  rw [leading, he]
  exact Nat.div_eq_of_lt_le (by simpa [Nat.mul_comm] using lo)
    (by simpa [Nat.mul_comm] using hi)

private theorem same_lead_forbids_three {x s : ℕ} (hx : 0 < x)
    (h : leading x = leading (x*s)) : leading s ≠ 3 := by
  intro hs
  let d := leading x
  let a := Nat.log 10 x
  let b := Nat.log 10 (x*s)
  let c := Nat.log 10 s
  have hd : 1 ≤ d := leading_pos hx
  obtain ⟨xl,xu⟩ := leading_bounds x
  obtain ⟨sl,su⟩ := leading_bounds s
  obtain ⟨pl,pu⟩ := leading_bounds (x*s)
  rw [hs] at sl su
  rw [← h] at pl pu
  change d * 10^a ≤ x at xl
  change x < (d+1) * 10^a at xu
  change 3 * 10^c ≤ s at sl
  change s < 4 * 10^c at su
  change d * 10^b ≤ x*s at pl
  change x*s < (d+1)*10^b at pu
  by_cases hb : b ≤ a+c
  · have hpow : (10:ℕ)^b ≤ 10^(a+c) := Nat.pow_le_pow_right (by decide) hb
    have hl : (d+1)*10^b ≤ x*s := calc
      _ ≤ (d*3)*10^(a+c) := Nat.mul_le_mul (by omega) hpow
      _ = (d*10^a)*(3*10^c) := by rw [pow_add]; ring
      _ ≤ x*s := Nat.mul_le_mul xl sl
    omega
  · have hpow : (10:ℕ)^(a+c+1) ≤ 10^b := Nat.pow_le_pow_right (by decide) (by omega)
    have hl : x*s < d*10^b := calc
      _ < ((d+1)*10^a)*(4*10^c) := Nat.mul_lt_mul_of_lt_of_lt xu su
      _ = ((d+1)*4)*10^(a+c) := by rw [pow_add]; ring
      _ ≤ (10*d)*10^(a+c) := Nat.mul_le_mul_right _ (by omega)
      _ = d*10^(a+c+1) := by rw [pow_succ]; ring
      _ ≤ d*10^b := Nat.mul_le_mul_left _ hpow
    omega

theorem A395429_no_uniform_bound : ¬ boundedPrefix := by
  rintro ⟨C, hb⟩
  let digits (j : ℕ) (i : Fin (C+1)) : Fin 10 :=
    ⟨leading (i.val ^ j), leading_lt_ten _⟩
  obtain ⟨i,j,hne,heq⟩ := Finite.exists_ne_map_eq_of_infinite digits
  obtain ⟨i,j,hlt,heq⟩ : ∃ i j : ℕ, i<j ∧ digits i = digits j := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨i,j,h,heq⟩
    · exact ⟨j,i,h,heq.symm⟩
  obtain ⟨k,hk,hC,h3⟩ := hb (j-i) (by omega) 3 (by decide) (by decide)
  have hkEq := congrArg Fin.val (congrFun heq (⟨k,by omega⟩ : Fin (C+1)))
  change leading (k^i) = leading (k^j) at hkEq
  apply same_lead_forbids_three (x:=k^i) (s:=k^(j-i)) (by positivity) _ h3
  simpa [← pow_add, Nat.add_sub_of_le hlt.le] using hkEq

private theorem digit_scaled {z e d : ℕ} {y : ℚ} (hd : 1 ≤ d) (h9 : d ≤ 9)
    (scale : (z : ℚ) = y * 10^e) (lo : (d : ℚ) ≤ y) (hi : y < (d : ℚ)+1) :
    leading z = d := by
  apply leading_eq_from_bounds hd h9 (a:=e)
  · exact_mod_cast (show (d : ℚ)*10^e ≤ (z : ℚ) by rw [scale]; gcongr)
  · exact_mod_cast (show (z : ℚ) < ((d : ℚ)+1)*10^e by rw [scale]; gcongr)

private theorem digit_scaled_tens {z e d : ℕ} {y : ℚ} (hd : 1 ≤ d) (h9 : d ≤ 9)
    (scale : (z : ℚ) = y * 10^e) (lo : (d : ℚ)*10 ≤ y) (hi : y < ((d : ℚ)+1)*10) :
    leading z = d := by
  apply digit_scaled (e:=e+1) (y:=y/10) hd h9 _ (by linarith) (by linarith)
  rw [scale, pow_succ]
  ring

theorem A395429_no_distinct_nine : ¬nineDistinct := by
  rintro ⟨n,hn,hinj⟩
  let a := Nat.log 10 (2^n)
  let b := n-a-1
  let x : ℚ := (2:ℚ)^n/10^a
  have ha : a < n := Nat.log_lt_of_lt_pow (by positivity) (Nat.pow_lt_pow_left (by decide : 2 < 10) (by omega))
  have hab : a+(b+1) = n := by dsimp [b]; omega
  have h10 : (0:ℚ)<10^a := by positivity
  have hxrep : (2:ℚ)^n = x * 10^a := by dsimp [x]; field_simp
  have hx1 : 1 ≤ x := by
    apply (le_div_iff₀ h10).2
    simpa only [one_mul] using (show (10:ℚ)^a ≤ 2^n by exact_mod_cast Nat.pow_log_le_self 10 (by positivity : 2^n ≠ 0))
  have hx10 : x < 10 := by
    apply (div_lt_iff₀ h10).2
    exact_mod_cast (by simpa [a,pow_succ'] using Nat.lt_pow_succ_log_self (by decide : 1 < 10) (2^n) : 2^n < 10*10^a)
  have hxp : 0<x := by linarith
  have hnot : x ≠ 2 := by
    intro h
    have hZ : 2^n = 2*10^a := by exact_mod_cast (hxrep.trans (by rw [h]) : (2:ℚ)^n=2*10^a)
    cases k : a with
    | zero =>
      rw [k] at hZ
      have hpow : 2^(1:ℕ) < 2^n := Nat.pow_lt_pow_right (by decide) hn
      simp at hZ hpow
      omega
    | succ j =>
      have hdvd : 5 ∣ 2^n := by rw [hZ,k,pow_succ]; exact ⟨2*10^j*2,by ring⟩
      have : 5 ∣ 2 := Nat.prime_five.dvd_of_dvd_pow hdvd
      omega
  have h5 : (((5:ℕ)^n:ℕ):ℚ) = (10/x)*10^b := by
    push_cast
    apply (mul_right_cancel₀ (ne_of_gt hxp))
    have h25 : (2:ℚ)^n*5^n = 10^n := by rw [← mul_pow]; norm_num
    have hnt : (10:ℚ)^n = 10^a*(10^b*10) := by rw [← hab,pow_add,pow_succ]
    rw [hxrep,hnt] at h25
    have hp : (5:ℚ)^n*x=10^b*10 := by
      apply (mul_right_cancel₀ (ne_of_gt h10))
      linear_combination h25
    rw [hp]
    field_simp
  have h2 : (((2:ℕ)^n:ℕ):ℚ) = x*10^a := by push_cast; exact hxrep
  have h4 : (((4:ℕ)^n:ℕ):ℚ) = x^2*10^(a*2) := by
    push_cast
    calc
      _ = ((2:ℚ)^n)^2 := by rw [←pow_mul, mul_comm, pow_mul]; norm_num
      _ = _ := by rw [hxrep,mul_pow,pow_mul]
  have h8 : (((8:ℕ)^n:ℕ):ℚ) = x^3*10^(a*3) := by
    push_cast
    calc
      _ = ((2:ℚ)^n)^3 := by rw [←pow_mul, mul_comm, pow_mul]; norm_num
      _ = _ := by rw [hxrep,mul_pow,pow_mul]
  have h1 : leading ((1:ℕ)^n) = 1 := by simp [leading]
  have collision {i j d : ℕ} (hi : i ∈ Set.Icc 1 9) (hj : j ∈ Set.Icc 1 9)
      (hne : i≠j) (ei : leading (i^n)=d) (ej : leading (j^n)=d) : False :=
    hne (hinj hi hj (ei.trans ej.symm))
  by_cases c2 : x<2
  · exact collision (by decide) (by decide) (by decide : (1:ℕ)≠2) h1
      (digit_scaled (by decide) (by decide) h2 hx1 (by norm_num; linarith))
  have x2 : 2<x := lt_of_le_of_ne (le_of_not_gt c2) (Ne.symm hnot)
  by_cases c22 : x ≤ 11/5
  · apply collision (by decide) (by decide) (by decide : (4:ℕ)≠5)
      (digit_scaled (d:=4) (by decide) (by decide) h4
        (by norm_num; nlinarith [mul_self_le_mul_self (by norm_num : (0:ℚ) ≤ 2) x2.le])
        (by norm_num; nlinarith [mul_self_le_mul_self hxp.le c22]))
    apply digit_scaled (by decide) (by decide) h5
    · apply (le_div_iff₀ hxp).2; norm_num; linarith
    · apply (div_lt_iff₀ hxp).2; norm_num; linarith
  by_cases c3 : x<3
  · have cubeLo : (10:ℚ) ≤ x^3 := by
      have t := pow_le_pow_left₀ (by norm_num : (0:ℚ) ≤ 11/5) (le_of_not_ge c22) 3
      norm_num at t; linarith
    have cubeHi : x^3 < 27 := by
      have t := pow_lt_pow_left₀ c3 hxp.le (by decide : 3≠0)
      norm_num at t; linarith
    by_cases c20 : x^3<20
    · exact collision (by decide) (by decide) (by decide : (1:ℕ)≠8) h1
        (digit_scaled_tens (by decide) (by decide) h8 (by norm_num; linarith) (by norm_num; linarith))
    · apply collision (by decide) (by decide) (by decide : (2:ℕ)≠8)
        (digit_scaled (d:=2) (by decide) (by decide) h2 (by norm_num; linarith) (by norm_num; linarith))
      exact digit_scaled_tens (by decide) (by decide) h8 (by norm_num; linarith) (by norm_num; linarith)
  by_cases c33 : x ≤ 10/3
  · apply collision (by decide) (by decide) (by decide : (2:ℕ)≠5)
      (digit_scaled (d:=3) (by decide) (by decide) h2 (by norm_num; linarith) (by norm_num; linarith))
    apply digit_scaled (by decide) (by decide) h5
    · apply (le_div_iff₀ hxp).2; norm_num; linarith
    · apply (div_lt_iff₀ hxp).2; norm_num; linarith
  by_cases c5 : x ≤ 5
  · have sqLo : (10:ℚ) ≤ x^2 := by
      nlinarith [mul_self_le_mul_self (by norm_num : (0:ℚ) ≤ 10/3) (le_of_not_ge c33)]
    have sqHi : x^2 ≤25 := by norm_num; nlinarith [mul_self_le_mul_self hxp.le c5]
    by_cases c20 : x^2<20
    · exact collision (by decide) (by decide) (by decide : (1:ℕ)≠4) h1
        (digit_scaled_tens (by decide) (by decide) h4 (by norm_num; linarith) (by norm_num; linarith))
    · apply collision (by decide) (by decide) (by decide : (4:ℕ)≠5)
        (digit_scaled_tens (d:=2) (by decide) (by decide) h4 (by norm_num; linarith) (by norm_num; linarith))
      apply digit_scaled (by decide) (by decide) h5
      · apply (le_div_iff₀ hxp).2; norm_num; linarith
      · apply (div_lt_iff₀ hxp).2; norm_num; linarith
  apply collision (by decide) (by decide) (by decide : (1:ℕ)≠5) h1
  apply digit_scaled (by decide) (by decide) h5
  · apply (le_div_iff₀ hxp).2; norm_num; linarith
  · apply (div_lt_iff₀ hxp).2; norm_num; linarith

/-- Each conjecture in the catalogue entry fails individually. -/
theorem A395429_both_refuted : ¬nineDistinct ∧ ¬boundedPrefix :=
  ⟨A395429_no_distinct_nine, A395429_no_uniform_bound⟩

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a395429.main) := by
  intro h
  exact A395429_both_refuted.1 h.1
