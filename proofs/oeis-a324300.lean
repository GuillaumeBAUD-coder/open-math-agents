import OMAStatements.S_oeis_a324300
import Mathlib

/-!
OEIS A324300: a(m) is odd exactly when m = k (k + 2).

Reduce modulo 2: send the Gaussian integers to the dual numbers over the field with two elements
by i ↦ ι = 1 + ε (ι² = 1 = -1 there). The parity of the real part of z is then fst + snd of the
image of z. In the image, x^(n+1) + ι = ι (1 + ι x^(n+1)), so the n-th summand S_n satisfies
  S_n * (1 + ι x^(n+1)) = ι^n x^n,
which gives the coefficient of x^j in S_n: it is ι^(n + e - 1) if j + 1 = (n + 1) e, and 0 if
n + 1 does not divide j + 1. Its "real part" is 1 exactly when n + 1 and e have the same parity.
So a(m) is congruent modulo 2 to the number of divisors d of m + 1 with d + (m + 1) / d even.
Pairing d with (m + 1) / d shows that this number is odd exactly when m + 1 is a square, and
m + 1 = (k + 1)^2 means m = k (k + 2).
-/

namespace OMA.A324300

open OMA.S_oeis_a324300 PowerSeries

abbrev S := DualNumber (ZMod 2)

lemma add_self (s : S) : s + s = 0 := by
  apply TrivSqZeroExt.ext
  · simp [CharTwo.add_self_eq_zero]
  · simp [CharTwo.add_self_eq_zero]

lemma eq_of_add_eq_zero {s t : S} (h : s + t = 0) : s = t := by
  have h2 := add_self t
  have : s + t = t + t := by rw [h, h2]
  exact add_right_cancel this

noncomputable def iota : S := 1 + DualNumber.eps

lemma iota_mul_iota : iota * iota = 1 := by
  unfold iota
  have h : (1 + DualNumber.eps : S) * (1 + DualNumber.eps) =
      1 + (DualNumber.eps + DualNumber.eps) + DualNumber.eps * DualNumber.eps := by ring
  rw [h, add_self, DualNumber.eps_mul_eps, add_zero, add_zero]

lemma iota_pow (k : ℕ) : iota ^ k = if k % 2 = 0 then 1 else iota := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    by_cases hk : k % 2 = 0
    · have hk1 : ¬ (k + 1) % 2 = 0 := by omega
      rw [if_pos hk, if_neg hk1, one_mul]
    · have hk1 : (k + 1) % 2 = 0 := by omega
      rw [if_neg hk, if_pos hk1, iota_mul_iota]

noncomputable def phi : GaussianInt →+* S :=
  Zsqrtd.lift ⟨iota, by
    rw [iota_mul_iota]
    have h := add_self 1
    push_cast
    exact (neg_eq_of_add_eq_zero_right h).symm⟩

lemma phi_apply (z : GaussianInt) : phi z = (z.re : S) + (z.im : S) * iota := rfl

lemma phi_gi : phi gi = iota := by
  rw [phi_apply]
  simp [gi]

def rho (s : S) : ZMod 2 := TrivSqZeroExt.fst s + TrivSqZeroExt.snd s

lemma rho_add (s t : S) : rho (s + t) = rho s + rho t := by
  unfold rho
  simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add]
  ring

lemma rho_zero : rho 0 = 0 := by
  unfold rho
  simp

lemma rho_sum (s : Finset ℕ) (f : ℕ → S) : rho (∑ n ∈ s, f n) = ∑ n ∈ s, rho (f n) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rho_zero]
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, rho_add, ih]

lemma rho_one : rho 1 = 1 := by
  unfold rho
  simp

lemma rho_iota : rho iota = 0 := by
  unfold rho iota
  simp
  decide

lemma rho_phi (z : GaussianInt) : rho (phi z) = ((z.re : ℤ) : ZMod 2) := by
  rw [phi_apply]
  unfold rho iota
  simp
  have h : ((z.im : ℤ) : ZMod 2) + (z.im : ZMod 2) = 0 := CharTwo.add_self_eq_zero _
  linear_combination h

lemma summand_mul (n : ℕ) :
    summand n * (1 + C gi * X ^ (n + 1)) ^ (n + 1) =
      (X : PowerSeries GaussianInt) ^ n * (X ^ (n + 1) + C gi) ^ n := by
  have hu : IsUnit ((1 + C gi * (X : PowerSeries GaussianInt) ^ (n + 1)) ^ (n + 1)) := by
    apply IsUnit.pow
    rw [PowerSeries.isUnit_iff_constantCoeff]
    simp
  unfold summand
  rw [mul_assoc, Ring.inverse_mul_cancel _ hu, mul_one]

lemma T_mul (n : ℕ) :
    PowerSeries.map phi (summand n) * (1 + C iota * X ^ (n + 1)) = C (iota ^ n) * X ^ n := by
  have h := congrArg (PowerSeries.map phi) (summand_mul n)
  simp only [map_mul, map_pow, map_add, map_one, PowerSeries.map_X, PowerSeries.map_C,
    phi_gi] at h
  have hCC : (C iota : PowerSeries S) * C iota = 1 := by
    rw [← map_mul, iota_mul_iota, map_one]
  have hu : IsUnit (1 + C iota * (X : PowerSeries S) ^ (n + 1)) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    simp
  have hB : (X : PowerSeries S) ^ (n + 1) + C iota = C iota * (1 + C iota * X ^ (n + 1)) := by
    rw [mul_add, mul_one, ← mul_assoc, hCC, one_mul, add_comm]
  rw [hB] at h
  generalize (1 + C iota * (X : PowerSeries S) ^ (n + 1)) = W at h hu ⊢
  generalize PowerSeries.map phi (summand n) = T at h ⊢
  have h2 : (T * W) * W ^ n = (C (iota ^ n) * X ^ n) * W ^ n := by
    rw [map_pow]
    linear_combination h
  exact (hu.pow n).mul_left_inj.mp h2

lemma coeff_T (n j : ℕ) :
    coeff j (PowerSeries.map phi (summand n)) =
      if (n + 1) ∣ (j + 1) then iota ^ (n + (j + 1) / (n + 1) - 1) else 0 := by
  have hrec : ∀ i, coeff i (PowerSeries.map phi (summand n)) +
      (if n + 1 ≤ i then coeff (i - (n + 1)) (PowerSeries.map phi (summand n)) * iota else 0) =
      iota ^ n * (if i = n then 1 else 0) := by
    intro i
    have h := congrArg (coeff i) (T_mul n)
    rw [mul_add, mul_one, map_add, ← mul_assoc, coeff_mul_X_pow', coeff_C_mul, coeff_X_pow] at h
    simp only [coeff_mul_C] at h
    exact h
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    have h := hrec j
    by_cases hj : n + 1 ≤ j
    · have hjn : j ≠ n := by omega
      rw [if_pos hj, if_neg hjn, mul_zero] at h
      have hc := eq_of_add_eq_zero h
      rw [hc, ih (j - (n + 1)) (by omega)]
      have hdvd : (n + 1 ∣ j - (n + 1) + 1) ↔ (n + 1 ∣ j + 1) := by
        have e : j + 1 = (j - (n + 1) + 1) + (n + 1) := by omega
        rw [e]
        exact Nat.dvd_add_self_right.symm
      by_cases hd : n + 1 ∣ j + 1
      · rw [if_pos hd, if_pos (hdvd.mpr hd)]
        obtain ⟨e, he⟩ := hd
        have he2 : 2 ≤ e := by
          rcases Nat.lt_or_ge e 2 with h2 | h2
          · have : e = 0 ∨ e = 1 := by omega
            rcases this with rfl | rfl
            · omega
            · omega
          · exact h2
        have q1 : (j + 1) / (n + 1) = e := by
          rw [he]
          exact Nat.mul_div_cancel_left e (Nat.succ_pos n)
        have q2 : (j - (n + 1) + 1) / (n + 1) = e - 1 := by
          have : j - (n + 1) + 1 = (n + 1) * (e - 1) := by
            have h3 : (n + 1) * (e - 1) + (n + 1) = (n + 1) * e := by
              obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
              simp only [Nat.add_sub_cancel]
              ring
            omega
          rw [this]
          exact Nat.mul_div_cancel_left (e - 1) (Nat.succ_pos n)
        rw [q1, q2, ← pow_succ]
        congr 1
        omega
      · rw [if_neg hd, if_neg (fun h' => hd (hdvd.mp h')), zero_mul]
    · rw [if_neg hj, add_zero] at h
      rw [h]
      by_cases hjn : j = n
      · subst hjn
        rw [if_pos rfl, mul_one, if_pos (dvd_refl _), Nat.div_self (Nat.succ_pos j)]
        congr 1
      · rw [if_neg hjn, mul_zero, if_neg]
        intro hd
        have hle := Nat.le_of_dvd (by omega) hd
        omega

lemma rho_coeff_T (n j : ℕ) :
    rho (coeff j (PowerSeries.map phi (summand n))) =
      if (n + 1) ∣ (j + 1) ∧ ((n + 1) + (j + 1) / (n + 1)) % 2 = 0 then 1 else 0 := by
  rw [coeff_T]
  by_cases hd : n + 1 ∣ j + 1
  · rw [if_pos hd, iota_pow]
    have hpos : 1 ≤ (j + 1) / (n + 1) := Nat.div_pos (Nat.le_of_dvd (Nat.succ_pos j) hd) (Nat.succ_pos n)
    by_cases hp : ((n + 1) + (j + 1) / (n + 1)) % 2 = 0
    · have hp' : (n + (j + 1) / (n + 1) - 1) % 2 = 0 := by omega
      rw [if_pos hp', if_pos ⟨hd, hp⟩, rho_one]
    · have hp' : ¬ (n + (j + 1) / (n + 1) - 1) % 2 = 0 := by omega
      rw [if_neg hp', if_neg (fun h => hp h.2), rho_iota]
  · rw [if_neg hd, if_neg (fun h => hd h.1), rho_zero]

lemma count_mod2 (N : ℕ) (hN : 0 < N) :
    (∑ d ∈ N.divisors, (if (d + N / d) % 2 = 0 then (1 : ZMod 2) else 0)) =
      if IsSquare N then 1 else 0 := by
  rw [← Finset.sum_filter_add_sum_filter_not N.divisors (fun d => d * d = N)]
  have h2 : ∑ d ∈ N.divisors.filter (fun d => ¬ d * d = N),
      (if (d + N / d) % 2 = 0 then (1 : ZMod 2) else 0) = 0 := by
    apply Finset.sum_involution (fun d _ => N / d)
    · intro d hd
      rw [Finset.mem_filter, Nat.mem_divisors] at hd
      rw [Nat.div_div_self hd.1.1 hd.1.2, add_comm (N / d) d]
      exact CharTwo.add_self_eq_zero _
    · intro d hd _ h
      rw [Finset.mem_filter, Nat.mem_divisors] at hd
      apply hd.2
      have := Nat.mul_div_cancel' hd.1.1
      rw [h] at this
      exact this
    · intro d hd
      rw [Finset.mem_filter, Nat.mem_divisors] at hd ⊢
      refine ⟨⟨Nat.div_dvd_of_dvd hd.1.1, hd.1.2⟩, ?_⟩
      intro hsq
      apply hd.2
      have hmul := Nat.mul_div_cancel' hd.1.1
      have hpos : 0 < N / d := by
        rcases Nat.eq_zero_or_pos (N / d) with h0 | h0
        · rw [h0] at hsq
          omega
        · exact h0
      have hdd : d = N / d := by
        apply Nat.eq_of_mul_eq_mul_right hpos
        rw [hmul, hsq]
      rw [← hdd] at hmul
      exact hmul
    · intro d hd
      rw [Finset.mem_filter, Nat.mem_divisors] at hd
      exact Nat.div_div_self hd.1.1 hd.1.2
  rw [h2, add_zero]
  by_cases hsq : IsSquare N
  · obtain ⟨r, rfl⟩ := hsq
    rw [if_pos ⟨r, rfl⟩]
    have hr : 0 < r := by
      rcases Nat.eq_zero_or_pos r with h0 | h0
      · subst h0
        omega
      · exact h0
    have hset : (r * r).divisors.filter (fun d => d * d = r * r) = {r} := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_singleton]
      constructor
      · rintro ⟨-, h⟩
        exact Nat.mul_self_inj.mp h
      · rintro rfl
        exact ⟨⟨Dvd.intro _ rfl, hN.ne'⟩, rfl⟩
    rw [hset, Finset.sum_singleton, Nat.mul_div_cancel _ hr]
    have : (r + r) % 2 = 0 := by omega
    rw [if_pos this]
  · rw [if_neg hsq]
    have hset : N.divisors.filter (fun d => d * d = N) = ∅ := by
      ext d
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro _ h
      exact hsq ⟨d, h.symm⟩
    rw [hset]
    simp

lemma cast_a (m : ℕ) : ((a m : ℤ) : ZMod 2) = if IsSquare (m + 1) then 1 else 0 := by
  unfold a
  rw [← rho_phi]
  have h1 : phi (coeff m (∑ n ∈ Finset.range (m + 1), summand n)) =
      coeff m (PowerSeries.map phi (∑ n ∈ Finset.range (m + 1), summand n)) := by
    rw [PowerSeries.coeff_map]
  rw [h1, map_sum, map_sum, rho_sum]
  simp only [rho_coeff_T]
  rw [← count_mod2 (m + 1) (Nat.succ_pos m)]
  rw [Nat.divisors, Finset.sum_filter, Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr
  · simp
  · intro n _
    by_cases hd : n + 1 ∣ m + 1
    · have hd' : 1 + n ∣ m + 1 := by rwa [add_comm]
      rw [if_pos hd']
      simp only [hd, true_and, add_comm 1 n]
    · have hd' : ¬ (1 + n ∣ m + 1) := by rwa [add_comm]
      rw [if_neg hd', if_neg (fun h => hd h.1)]

end OMA.A324300

open OMA.S_oeis_a324300 OMA.A324300 in
theorem OMA.solution : type_of% @OMA.S_oeis_a324300.main := by
  intro m
  rw [← ZMod.intCast_eq_one_iff_odd, cast_a]
  constructor
  · intro h
    by_cases hsq : IsSquare (m + 1)
    · obtain ⟨r, hr⟩ := hsq
      have hr1 : 1 ≤ r := by
        rcases Nat.eq_zero_or_pos r with h0 | h0
        · subst h0
          simp at hr
        · exact h0
      obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
      refine ⟨k, ?_⟩
      have e : (k + 1) * (k + 1) = k * (k + 2) + 1 := by ring
      omega
    · rw [if_neg hsq] at h
      exact absurd h (by decide)
  · rintro ⟨k, rfl⟩
    rw [if_pos]
    exact ⟨k + 1, by ring⟩
