import OMAStatements.S_oeis_a022894
import Mathlib

/-!
Reserve a small positive fraction of the odd primes. Their subset sums contain
an interval that covers every remaining imbalance of moderate size. The exact
second moment shows that at least half of all assignments on the other primes
have moderate imbalance. The reserved fraction can then be taken arbitrarily
small, yielding the claimed exponential growth.
-/

namespace OMA.PrimeSignGrowth

open Finset Filter Asymptotics
open scoped Classical Topology

private noncomputable def P (i : ℕ) : ℕ := Nat.nth Nat.Prime (i+1)
private noncomputable def primeSum (m : ℕ) : ℕ := ∑ i ∈ range m, P i

private theorem P_prime (i : ℕ) : (P i).Prime := Nat.prime_nth_prime _

private theorem P_mono : StrictMono P := by
  intro i j h
  exact Nat.nth_strictMono Nat.infinite_setOfPred_prime (Nat.succ_lt_succ h)

private theorem P_lower (i : ℕ) : i + 3 ≤ P i := Nat.add_two_le_nth_prime (i+1)

private theorem P_odd (i : ℕ) : Odd (P i) := by
  exact (P_prime i).odd_of_ne_two (by have := P_lower i; omega)

private theorem P_next (i : ℕ) : P (i+1) ≤ 2 * P i := by
  obtain ⟨q, hq, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (P i) (P_prime i).ne_zero
  have hidx : i+2 ≤ Nat.count Nat.Prime q := by
    by_contra! h
    have hn := Nat.nth_monotone Nat.infinite_setOfPred_prime (show Nat.count Nat.Prime q ≤ i+1 by omega)
    rw [Nat.nth_count hq] at hn
    exact hlt.not_ge hn
  have H := Nat.nth_monotone Nat.infinite_setOfPred_prime hidx
  rw [Nat.nth_count hq] at H
  exact H.trans hle

private def seeds (i : ℕ) : ℕ := ([3, 5, 7, 11, 13, 17, 19] : List ℕ)[i]?.getD 0

private theorem P_seeds (i : ℕ) (hi : i < 7) : P i = seeds i := by
  have p13 : Nat.nth Nat.Prime 5 = 13 := Nat.nth_count (by decide : Nat.Prime 13)
  have p17 : Nat.nth Nat.Prime 6 = 17 := Nat.nth_count (by decide : Nat.Prime 17)
  have p19 : Nat.nth Nat.Prime 7 = 19 := Nat.nth_count (by decide : Nat.Prime 19)
  interval_cases i <;> simp [P, seeds, p13, p17, p19]

private theorem primeSum_seven : primeSum 7 = 75 := by
  calc
    _ = ∑ i ∈ range 7, seeds i := sum_congr rfl fun i hi => P_seeds i (mem_range.mp hi)
    _ = _ := by decide

private def seedWitness (t : Fin 56) : Finset ℕ :=
  let mask := ([5, 8, 6, 16, 9, 7, 10, 32, 12, 11, 20, 13, 34, 14,
    24, 22, 15, 25, 23, 26, 48, 28, 27, 42, 29, 44, 30, 52,
    45, 31, 46, 56, 54, 47, 57, 55, 58, 87, 60, 59, 92, 61,
    106, 62, 108, 94, 63, 109, 95, 110, 120, 118, 111, 121, 119, 122] : List ℕ)[t.val]?.getD 0
  (range 7).filter (fun i => mask.testBit i = true)

set_option maxRecDepth 4000 in
private theorem seedWitness_sum : ∀ t : Fin 56, ∑ i ∈ seedWitness t, seeds i = t.val + 10 := by
  decide

private theorem seed_cover (t : Fin 56) :
    ∃ s ∈ (range 7).powerset, ∑ i ∈ s, seeds i = t.val + 10 :=
  ⟨seedWitness t, mem_powerset.mpr (filter_subset _ _), seedWitness_sum t⟩

private theorem subset_sum_interval (m : ℕ) (hm : 7 ≤ m) :
    20 + 2 * P (m-1) ≤ primeSum m ∧
      ∀ t : ℕ, 10 ≤ t → t + 10 ≤ primeSum m → ∃ s ⊆ range m, ∑ i ∈ s, P i = t := by
  induction m, hm using Nat.le_induction with
  | base =>
    rw [primeSum_seven, show P (7-1) = 19 from P_seeds 6 (by decide)]
    refine ⟨by decide, fun t ht htu => ?_⟩
    obtain ⟨s, hs, hv⟩ := seed_cover ⟨t-10, by omega⟩
    have hsub := mem_powerset.mp hs
    refine ⟨s, hsub, ?_⟩
    calc
      _ = ∑ i ∈ s, seeds i := sum_congr rfl fun i hi => P_seeds i (mem_range.mp (hsub hi))
      _ = _ := by simp only at hv; omega
  | succ m hm ih =>
    have heq : primeSum (m+1) = primeSum m + P m := sum_range_succ _ _
    rw [heq, Nat.add_sub_cancel]
    have hnext : P m ≤ 2 * P (m-1) := by
      simpa only [show m-1+1=m by omega] using P_next (m-1)
    have hw : 20 + P m ≤ primeSum m := by omega
    refine ⟨by omega, fun t ht htu => ?_⟩
    by_cases h : t + 10 ≤ primeSum m
    · obtain ⟨s, hs, hv⟩ := ih.2 t ht h
      exact ⟨s, hs.trans (range_mono (Nat.le_succ m)), hv⟩
    · obtain ⟨s, hs, hv⟩ := ih.2 (t-P m) (by omega) (by omega)
      have hms : m ∉ s := fun hmem => (notMem_range_self) (hs hmem)
      refine ⟨insert m s, insert_subset (mem_range.mpr (Nat.lt_succ_self _))
        (hs.trans (range_mono (Nat.le_succ m))), ?_⟩
      rw [sum_insert hms, hv]
      omega

private theorem primeSum_lower (m : ℕ) : m * (m+5) ≤ 2 * primeSum m := by
  induction m with
  | zero => simp [primeSum]
  | succ m ih =>
    have hp := P_lower m
    change (m+1)*(m+1+5) ≤ 2 * ∑ i ∈ range (m+1), P i
    rw [sum_range_succ]
    change _ ≤ 2 * (primeSum m + P m)
    nlinarith

private def coeff (b : Bool) : ℤ := if b then 1 else -1

private def signed {n : ℕ} (w : Fin n → ℤ) (c : Fin n → Bool) : ℤ :=
  ∑ i, coeff (c i) * w i

private theorem coeff_flip (b : Bool) : coeff (!b) = -coeff b := by cases b <;> decide

private theorem crossMoment {n : ℕ} (w : Fin n → ℤ) (i j : Fin n) :
    (∑ c : Fin n → Bool, (coeff (c i) * w i) * (coeff (c j) * w j)) =
      if i = j then (2 : ℤ)^n * (w i)^2 else 0 := by
  by_cases hij : i = j
  · subst j
    have hp (b : Bool) : (coeff b * w i) * (coeff b * w i) = (w i)^2 := by
      cases b <;> simp [coeff, pow_two]
    simp [hp]
  · rw [if_neg hij]
    let swap (c : Fin n → Bool) := Function.update c i (!(c i))
    have hinv : Function.Involutive swap := by
      intro c
      funext j
      by_cases hj : j = i
      · subst j; simp [swap]
      · simp [swap, Function.update_of_ne hj]
    let e := hinv.toPerm swap
    let f (c : Fin n → Bool) := (coeff (c i) * w i) * (coeff (c j) * w j)
    have hf (c : Fin n → Bool) : f (e c) = -f c := by
      change f (swap c) = -f c
      simp [f, swap, Function.update_of_ne (Ne.symm hij), coeff_flip]
    have hs := Equiv.sum_comp e f
    simp only [hf, sum_neg_distrib] at hs
    change (∑ c, f c) = 0
    linarith

private theorem variance {n : ℕ} (w : Fin n → ℤ) :
    (∑ c : Fin n → Bool, (signed w c)^2) = (2 : ℤ)^n * ∑ i, (w i)^2 := by
  calc
    _ = ∑ c : Fin n → Bool, ∑ i : Fin n, ∑ j : Fin n,
          (coeff (c i) * w i) * (coeff (c j) * w j) := by
      simp only [signed, pow_two, sum_mul, mul_sum]
      exact sum_congr rfl fun _ _ => sum_comm
    _ = ∑ i : Fin n, ∑ j : Fin n, ∑ c : Fin n → Bool,
          (coeff (c i) * w i) * (coeff (c j) * w j) := by
      rw [sum_comm]
      exact sum_congr rfl fun _ _ => sum_comm
    _ = _ := by
      simp only [crossMoment, mul_sum, sum_ite_eq, mem_univ, if_true]

private noncomputable def good {n : ℕ} (w : Fin n → ℤ) (r : ℕ) : Finset (Fin n → Bool) :=
  univ.filter (fun c => |signed w c| ≤ (r : ℤ))

private theorem good_many {n : ℕ} (w : Fin n → ℤ) (r : ℕ) (hr : 0 < r)
    (hv : 2 * ∑ i, (w i)^2 ≤ (r : ℤ)^2) : 2^n ≤ 2 * (good w r).card := by
  let bad := univ.filter (fun c : Fin n → Bool => ¬ |signed w c| ≤ (r : ℤ))
  have hbad : (bad.card : ℤ) * (r : ℤ)^2 ≤ (2 : ℤ)^n * ∑ i, (w i)^2 := by
    calc
      _ = ∑ c ∈ bad, (r : ℤ)^2 := by simp [sum_const]
      _ ≤ ∑ c ∈ bad, (signed w c)^2 := by
        apply sum_le_sum
        intro c hc
        have h := (mem_filter.mp hc).2
        rw [← sq_abs (signed w c)]
        exact pow_le_pow_left₀ (by positivity) (le_of_lt (lt_of_not_ge h)) _
      _ ≤ ∑ c : Fin n → Bool, (signed w c)^2 :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun c _ _ => sq_nonneg _)
      _ = _ := variance w
  have hr' : (0 : ℤ) < (r : ℤ)^2 := by positivity
  have hbad' : 2 * (bad.card : ℤ) ≤ (2 : ℤ)^n := by
    apply (mul_le_mul_iff_left₀ hr').mp
    calc
      _ = 2 * ((bad.card : ℤ) * (r : ℤ)^2) := by ring
      _ ≤ 2 * ((2 : ℤ)^n * ∑ i, (w i)^2) := by gcongr
      _ = (2 : ℤ)^n * (2 * ∑ i, (w i)^2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hv (by positivity)
  have hparts : (good w r).card + bad.card = 2^n := by
    change (univ.filter (fun c : Fin n → Bool => |signed w c| ≤ (r : ℤ))).card +
      (univ.filter (fun c : Fin n → Bool => ¬ |signed w c| ≤ (r : ℤ))).card = _
    rw [card_filter_add_card_filter_not]
    simp
  have hbadNat : 2 * bad.card ≤ 2^n := by exact_mod_cast hbad'
  omega

private theorem primeSum_mod (m : ℕ) : (primeSum m : ℤ) % 2 = (m : ℤ) % 2 := by
  induction m with
  | zero => simp [primeSum]
  | succ m ih =>
    have hp : ((P m : ℕ) : ℤ) % 2 = 1 := by
      obtain ⟨k, hk⟩ := P_odd m
      have hk' : ((P m : ℕ) : ℤ) = 2 * (k : ℤ) + 1 := by exact_mod_cast hk
      omega
    have hs : primeSum (m+1) = primeSum m + P m := sum_range_succ _ _
    rw [hs, Nat.cast_add, Nat.cast_succ]
    omega

private theorem signed_subsets {b : ℕ} (w : Fin b → ℤ) (c : Fin b → Bool) :
    signed w c = 2 * ∑ i ∈ univ.filter (fun i => c i), w i - ∑ i, w i := by
  rw [signed, sum_filter, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  cases c i
  · simp [coeff]
  · simp [coeff]
    ring

private theorem reserve_signed {m : ℕ} {S : Finset ℕ} (hS : S ⊆ range m) :
    signed (fun i : Fin m => (P i : ℤ)) (fun i => decide ((i : ℕ) ∈ S)) =
      2 * (∑ i ∈ S, (P i : ℤ)) - primeSum m := by
  have hf : (range m).filter (· ∈ S) = S := by
    ext i
    simp only [mem_filter, and_iff_right_iff_imp]
    exact fun hi => hS hi
  simp only [signed_subsets, sum_filter, decide_eq_true_eq]
  rw [Fin.sum_univ_eq_sum_range (fun i => if i ∈ S then (P i : ℤ) else 0),
    ← sum_filter, hf, Fin.sum_univ_eq_sum_range (fun i => (P i : ℤ))]
  simp only [primeSum, Nat.cast_sum]

private theorem repair {m b : ℕ} (hm : 7 ≤ m) (htot : Even (m+b))
    (c : Fin b → Bool) (hc : |signed (fun j => (P (m + j) : ℤ)) c| ≤ (primeSum m : ℤ) - 22) :
    ∃ d : Fin (m+b) → Bool, (∀ i : Fin b, d (Fin.natAdd m i) = c i) ∧
      2 + signed (fun i => (P i : ℤ)) d = 0 := by
  let w : Fin b → ℤ := fun j => P (m + j)
  let u : ℤ := ∑ j ∈ univ.filter (fun j => c j), w j
  let t : ℤ := (primeSum (m+b) - 2 : ℤ) / 2 - u
  have hpar : ((primeSum (m+b) : ℕ) : ℤ) % 2 = 0 := by
    rw [primeSum_mod]
    obtain ⟨k, hk⟩ := htot
    have hk' : ((m+b : ℕ) : ℤ) = (k : ℤ) + (k : ℤ) := by exact_mod_cast hk
    omega
  have hprimeSum : (primeSum (m+b) : ℤ) = primeSum m + ∑ j, w j := by
    simp only [primeSum, sum_range_add, Nat.cast_add, Nat.cast_sum, w]
    rw [Fin.sum_univ_eq_sum_range (fun j => (P (m+j) : ℤ))]
  have hS := signed_subsets w c
  change signed w c = 2 * u - ∑ j, w j at hS
  have ht : 2*t = (primeSum m : ℤ) - 2 - signed w c := by
    dsimp only [t]
    omega
  change |signed w c| ≤ _ at hc
  obtain ⟨hl, hu⟩ := abs_le.mp hc
  have htn : 0 ≤ t := by omega
  have hcast := Int.toNat_of_nonneg htn
  obtain ⟨S, hSsub, hSv⟩ := (subset_sum_interval m hm).2 t.toNat (by omega) (by omega)
  let d : Fin (m+b) → Bool := Fin.addCases (fun i : Fin m => decide ((i : ℕ) ∈ S)) c
  refine ⟨d, fun i => by simp [d], ?_⟩
  have hres := reserve_signed hSsub
  have hv : (∑ i ∈ S, (P i : ℤ)) = t := by
    rw [← Nat.cast_sum, hSv]
    exact hcast
  have hsplit : signed (fun i : Fin (m+b) => (P i : ℤ)) d =
      signed (fun i : Fin m => (P i : ℤ)) (fun i => decide ((i : ℕ) ∈ S)) + signed w c := by
    simp [signed, Fin.sum_univ_add, d, w]
  rw [hsplit, hres, hv]
  omega

private theorem a_formula (n : ℕ) : OMA.S_oeis_a022894.a n =
    (univ.filter fun d : Fin (2*n) → Bool => 2 + signed (fun i => (P i : ℤ)) d = 0).card := by
  unfold OMA.S_oeis_a022894.a
  apply congrArg Finset.card
  ext d
  simp [signed, coeff, P, OMA.S_oeis_a022894.prime,
    show ∀ j : ℕ, j + 2 - 1 = j + 1 from fun j => by omega]

private theorem countMany {m b : ℕ} (hm : 7 ≤ m) (hM : 22 < primeSum m) (htot : Even (m+b))
    (hv : 2 * ∑ j : Fin b, ((P (m+j) : ℤ))^2 ≤ ((primeSum m : ℤ) - 22)^2) :
    2^b ≤ 2 * (univ.filter fun d : Fin (m+b) → Bool =>
      2 + signed (fun i => (P i : ℤ)) d = 0).card := by
  let w : Fin b → ℤ := fun j => P (m + j)
  have hr : ((primeSum m - 22 : ℕ) : ℤ) = (primeSum m : ℤ) - 22 := by omega
  have hcard := good_many w (primeSum m - 22) (by omega) (by rwa [hr])
  let G := good w (primeSum m - 22)
  let D := univ.filter fun d : Fin (m+b) → Bool => 2 + signed (fun i => (P i : ℤ)) d = 0
  have ext (c : G) : ∃ d : D, ∀ i : Fin b, (d : Fin (m+b) → Bool) (Fin.natAdd m i) = c.val i := by
    have hc := (mem_filter.mp c.2).2
    change |signed w c.val| ≤ ((primeSum m - 22 : ℕ) : ℤ) at hc
    rw [hr] at hc
    obtain ⟨d, hd, hz⟩ := repair hm htot c.val hc
    exact ⟨⟨d, mem_filter.mpr ⟨mem_univ _, hz⟩⟩, hd⟩
  have hinj : Function.Injective (fun c : G => (ext c).choose) := by
    intro c e h
    apply Subtype.ext
    funext j
    have hc := (ext c).choose_spec j
    have he := (ext e).choose_spec j
    change (ext c).choose = (ext e).choose at h
    rw [h] at hc
    exact hc.symm.trans he
  have hGD := Fintype.card_le_of_injective _ hinj
  have hGD' : G.card ≤ D.card := by simpa using hGD
  exact hcard.trans (Nat.mul_le_mul_left 2 hGD')

private theorem primeSquare_small (C : ℝ) (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, (P (2*n) : ℝ)^2 ≤ C * (n : ℝ)^3 := by
  let k : ℝ := min 1 C
  have hk : 0 < k := lt_min zero_lt_one hC
  have hkC : k^3 ≤ C := by
    calc
      k^3 = k*k*k := by ring
      _ ≤ 1*1*k := by gcongr <;> exact min_le_left 1 C
      _ ≤ C := by simpa only [mul_one, one_mul] using (show k ≤ C from min_le_right 1 C)
  let y (n : ℕ) : ℝ := P (2*n)
  have log2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hy : Tendsto y atTop atTop := by
    apply tendsto_atTop_mono (f := fun n : ℕ => (n : ℝ)) _ tendsto_natCast_atTop_atTop
    intro n
    have hp := P_lower (2*n)
    change (n : ℝ) ≤ (P (2*n) : ℝ)
    exact_mod_cast (show n ≤ P (2*n) by omega)
  have hy1 : Tendsto (fun n => y n + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => le_add_of_nonneg_right zero_le_one) hy
  have h1 := hy1.eventually
    (Real.isLittleO_log_id_atTop.bound (show 0 < Real.log 2/4 by positivity))
  have h2 := hy.eventually ((isLittleO_log_rpow_atTop (r := 1/3) (by norm_num)).bound
    (show 0 < k * Real.log 2 / 8 by positivity))
  filter_upwards [h1, h2, eventually_ge_atTop 1] with n hlog1 hlog2 hn
  have hyp : 1 < y n := by
    change (1 : ℝ) < (P (2*n) : ℝ)
    exact_mod_cast (show 1 < P (2*n) by have := P_lower (2*n); omega)
  have hyn : 0 < y n := by linarith
  have hlog : 0 < Real.log (y n) := Real.log_pos hyp
  have hm1 : Real.log (y n + 1) ≤ Real.log 2 / 4 * (y n + 1) := by
    exact (show Real.log (y n + 1) ≤ ‖Real.log (y n + 1)‖ by rw [Real.norm_eq_abs]; exact le_abs_self _).trans
      (by simpa [Real.norm_of_nonneg (by positivity : 0 ≤ y n + 1)] using hlog1)
  have hm2 : Real.log (y n) ≤ k * Real.log 2 / 8 * (y n)^(1/3 : ℝ) := by
    exact (show Real.log (y n) ≤ ‖Real.log (y n)‖ by rw [Real.norm_eq_abs]; exact le_abs_self _).trans
      (by simpa [Real.norm_of_nonneg (Real.rpow_nonneg hyn.le _)] using hlog2)
  have hcnt : Nat.primeCounting (P (2*n)) = 2*n+2 := by
    change Nat.count Nat.Prime (Nat.nth Nat.Prime (2*n+1) + 1) = _
    exact Nat.count_nth_succ_of_infinite Nat.infinite_setOfPred_prime _
  have hg := Chebyshev.pi_ge (P (2*n))
  rw [hcnt] at hg
  change (y n * Real.log 2 - Real.log (y n + 1)) / Real.log (y n) ≤ ↑(2*n+2) at hg
  rw [div_le_iff₀ hlog] at hg
  have hg1 : Real.log 2 / 2 * y n ≤ (2*(n:ℝ)+2) * Real.log (y n) := by push_cast at hg; nlinarith
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hg2 : Real.log 2 / 2 * y n ≤ Real.log 2 / 2 * (k * n * (y n)^(1/3 : ℝ)) := by
    calc
      _ ≤ _ := hg1
      _ ≤ 4*(n:ℝ) * (k * Real.log 2 / 8 * (y n)^(1/3 : ℝ)) := by
        gcongr
        linarith
      _ = _ := by ring
  have hyK := (mul_le_mul_iff_right₀ (show 0 < Real.log 2 / 2 by positivity)).mp hg2
  have hyP : y n ^ (2/3 : ℝ) ≤ k * n := by
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hyn (1/3))).mp
    rw [← Real.rpow_add hyn, show (2/3 : ℝ) + 1/3 = 1 by norm_num, Real.rpow_one]
    exact hyK
  change (y n)^2 ≤ C * (n:ℝ)^3
  calc
    _ = ((y n) ^ (2/3 : ℝ))^3 := by
      rw [← Real.rpow_mul_natCast hyn.le]
      norm_num [Real.rpow_natCast]
    _ ≤ (k*(n:ℝ))^3 := by gcongr
    _ ≤ _ := by rw [mul_pow]; gcongr

private theorem eventually_count (K : ℕ) (hK : 0 < K) :
    ∀ᶠ n : ℕ in atTop, 2^(2*n - n/K) ≤ 2*OMA.S_oeis_a022894.a n := by
  let c : ℝ := 1 / (16 * (K : ℝ)^2)
  have hC : 0 < c := by dsimp [c]; positivity
  filter_upwards [primeSquare_small (c^2/4) (by positivity), eventually_ge_atTop (14*K)] with n hnSq hn
  let m := n/K
  let b := 2*n-m
  have hm : 14 ≤ m := (Nat.le_div_iff_mul_le hK).mpr hn
  have hm_le : m ≤ n := Nat.div_le_self _ _
  have hmb : m+b=2*n := by dsimp [b]; omega
  have hmt : n ≤ 2*K*m := by
    have hdiv := Nat.mod_add_div n K
    have hmod := Nat.mod_lt n hK
    have hkM : K ≤ K*m := by
      simpa only [mul_one] using Nat.mul_le_mul_left K (show 1 ≤ m by omega)
    change n % K + K*m = n at hdiv
    change n ≤ _
    rw [mul_assoc, two_mul]
    omega
  have hM := primeSum_lower m
  have hM' : ((m : ℝ) * ((m : ℝ) + 5)) ≤ 2 * (primeSum m : ℝ) := by exact_mod_cast hM
  have hm14 : (14 : ℝ) ≤ m := by exact_mod_cast hm
  have hRp : (0 : ℝ) < (primeSum m : ℝ) - 22 := by nlinarith
  have hRes : c*(n : ℝ)^2 ≤ (primeSum m : ℝ) - 22 := by
    have hRs : (m : ℝ)^2 / 4 ≤ (primeSum m : ℝ) - 22 := by nlinarith
    have hmt' : (n : ℝ) ≤ 2*(K : ℝ)*(m : ℝ) := by exact_mod_cast hmt
    calc
      _ ≤ c*(2*(K : ℝ)*(m : ℝ))^2 := by gcongr
      _ = (m : ℝ)^2 / 4 := by dsimp [c]; field_simp; ring
      _ ≤ _ := hRs
  have hV : 2 * ∑ j : Fin b, ((P (m+j) : ℤ))^2 ≤ ((primeSum m : ℤ) - 22)^2 := by
    suffices hV : (2 : ℝ) * ∑ j : Fin b, ((P (m+j) : ℝ))^2 ≤ ((primeSum m : ℝ) - 22)^2 by
      exact_mod_cast hV
    have hsum : (∑ j : Fin b, ((P (m+j) : ℝ))^2) ≤ (b : ℝ) * ((P (2*n) : ℝ))^2 := by
      calc
        _ ≤ ∑ _ : Fin b, ((P (2*n) : ℝ))^2 := by
          apply sum_le_sum
          intro j hj
          have hj' := j.isLt
          have hp := P_mono.monotone (show m+(j : ℕ) ≤ 2*n by omega)
          gcongr
        _ = _ := by simp
    have hb : (b : ℝ) ≤ 2*(n : ℝ) := by exact_mod_cast (show b≤2*n by omega)
    calc
      _ ≤ 2*((b : ℝ)*((P (2*n) : ℝ))^2) := by gcongr
      _ ≤ 4*(n : ℝ)*((P (2*n) : ℝ))^2 := by nlinarith [mul_le_mul_of_nonneg_right hb (sq_nonneg (P (2*n) : ℝ))]
      _ ≤ 4*(n : ℝ)*(c^2/4*(n : ℝ)^3) := by gcongr
      _ = (c*(n : ℝ)^2)^2 := by ring
      _ ≤ _ := by gcongr
  have hM22 : 22 < primeSum m := by exact_mod_cast (show (22 : ℝ) < primeSum m by linarith)
  have hmany := countMany (m := m) (b := b) (by omega) hM22 (hmb.symm ▸ even_two_mul n) hV
  change 2^b ≤ 2*OMA.S_oeis_a022894.a n
  rw [a_formula, ← hmb]
  exact hmany

private theorem rate_lower (K : ℕ) (hK : 0 < K) : ∀ᶠ n : ℕ in atTop,
    (2:ℝ)^(2 - (K:ℝ)⁻¹ - (n:ℝ)⁻¹) ≤ (OMA.S_oeis_a022894.a n : ℝ)^((1:ℝ)/n) := by
  filter_upwards [eventually_count K hK, eventually_ge_atTop 1] with n hc hn
  let m := n/K
  let b := 2*n-m
  have hn' : (0:ℝ) < n := by exact_mod_cast (show 0<n by omega)
  have hK' : (0:ℝ) < K := by exact_mod_cast hK
  have hb : ((b:ℕ):ℝ) = 2*(n:ℝ)-(m:ℝ) := by
    have hm : m ≤ n := Nat.div_le_self _ _
    simpa only [b, Nat.cast_mul, Nat.cast_ofNat] using
      (Nat.cast_sub (R := ℝ) (show m≤2*n by omega))
  have hmul : (m:ℝ)*(K:ℝ) ≤ n := by exact_mod_cast Nat.div_mul_le_self n K
  have hdiv : (m:ℝ)/(n:ℝ) ≤ (K:ℝ)⁻¹ := by
    rw [div_le_iff₀ hn']
    simpa [div_eq_mul_inv, mul_comm] using (le_div_iff₀ hK').mpr hmul
  have hExp : 2 - (K:ℝ)⁻¹ - (n:ℝ)⁻¹ ≤ ((b:ℝ)-1)*((1:ℝ)/n) := by
    rw [hb]
    have hh : (2*(n:ℝ)-(m:ℝ)-1)*((1:ℝ)/n) = 2 - (m:ℝ)/n - (n:ℝ)⁻¹ := by
      field_simp
    linarith
  have hvalue : (2:ℝ)^((b:ℝ)-1) ≤ (OMA.S_oeis_a022894.a n : ℝ) := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_one, Real.rpow_natCast, div_le_iff₀ (by norm_num)]
    exact_mod_cast (mul_comm 2 (OMA.S_oeis_a022894.a n) ▸ hc)
  calc
    _ ≤ (2:ℝ)^(((b:ℝ)-1)*((1:ℝ)/n)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hExp
    _ = ((2:ℝ)^((b:ℝ)-1))^((1:ℝ)/n) := Real.rpow_mul (by norm_num) _ _
    _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) hvalue (by positivity)

private theorem rate_upper : ∀ᶠ n : ℕ in atTop,
    (OMA.S_oeis_a022894.a n : ℝ)^((1:ℝ)/n) ≤ 4 := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  have ha : OMA.S_oeis_a022894.a n ≤ 2^(2*n) := by
    unfold OMA.S_oeis_a022894.a
    exact (card_filter_le _ _).trans_eq (by simp)
  have hn' : (0:ℝ) < n := by exact_mod_cast (show 0<n by omega)
  calc
    _ ≤ ((2:ℝ)^(2*n:ℕ))^((1:ℝ)/n) := Real.rpow_le_rpow (by positivity) (by exact_mod_cast ha) (by positivity)
    _ = 4 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      rw [show (((2*n : ℕ) : ℝ))*((1:ℝ)/n)=2 by push_cast; field_simp, Real.rpow_two]
      norm_num

private theorem power_approach (u : ℝ) : Tendsto
    (fun n : ℕ => (2:ℝ)^(u-(n:ℝ)⁻¹)) atTop (𝓝 ((2:ℝ)^u)) := by
  have hinv : Tendsto (fun n : ℕ => ((n:ℝ)⁻¹)) atTop (𝓝 0) :=
    tendsto_natCast_atTop_atTop.inv_tendsto_atTop
  have hc : Tendsto (fun _ : ℕ => u) atTop (𝓝 u) := tendsto_const_nhds
  have hsub : Tendsto (fun n : ℕ => u-(n:ℝ)⁻¹) atTop (𝓝 u) := by
    simpa only [sub_zero] using hc.sub hinv
  have hcont := (Real.continuous_const_rpow (show (2:ℝ) ≠ 0 by norm_num)).tendsto u
  exact hcont.comp hsub

set_option maxHeartbeats 600000 in
private theorem solution : type_of% @OMA.S_oeis_a022894.main := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro l hl
    have hL : Tendsto (fun K : ℕ => (2:ℝ)^(2-(K:ℝ)⁻¹)) atTop (𝓝 4) := by
      have hp : (2:ℝ)^(2:ℝ) = 4 := by norm_num [Real.rpow_two]
      simpa only [hp] using power_approach 2
    obtain ⟨K, hK, hK'⟩ := (((tendsto_order.1 hL).1 l hl).and (eventually_ge_atTop 1)).exists
    have ht := power_approach (2-(K:ℝ)⁻¹)
    filter_upwards [(tendsto_order.1 ht).1 l hK, rate_lower K (by omega)] with n h0 h1
    exact h0.trans_le h1
  · intro u hu
    filter_upwards [rate_upper] with n h
    exact h.trans_lt hu

end OMA.PrimeSignGrowth

theorem OMA.solution : type_of% @OMA.S_oeis_a022894.main := OMA.PrimeSignGrowth.solution
