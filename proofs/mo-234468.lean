import OMAStatements.S_mo_234468
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic

-- Source question: https://mathoverflow.net/questions/234468/

open Polynomial OMA.S_mo_234468
open scoped BigOperators

private theorem divisorPolynomial_one : divisorPolynomial 1 = X := by
  simp [divisorPolynomial]

private theorem divisorPolynomial_two : divisorPolynomial 2 = X + X ^ 2 := by
  rw [divisorPolynomial, show Nat.divisors 2 = {1, 2} by decide]
  simp

private theorem divisorPolynomial_three : divisorPolynomial 3 = X + X ^ 3 := by
  rw [divisorPolynomial, show Nat.divisors 3 = {1, 3} by decide]
  simp

private theorem degree_x_pow_add_one (k : ℕ) (hk : 0 < k) :
    ((X ^ k + 1 : ℚ[X])).natDegree = k := by
  rw [natDegree_add_eq_left_of_natDegree_lt]
  · exact natDegree_X_pow k
  · simpa using hk

private theorem first_minimum : IsLeast {n : ℕ | admissible 0 n} 2 := by
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [divisorPolynomial_two]
    exact ⟨X, by norm_num; ring⟩
  · intro n hn
    change admissible 0 n at hn
    by_contra! h
    have heq : n = 1 := by have := hn.1; omega
    subst n
    have hd := hn.2
    rw [divisorPolynomial_one] at hd
    obtain ⟨r, hr⟩ := hd
    have he := congrArg (Polynomial.eval (-1 : ℚ)) hr
    norm_num [eval_mul] at he

private theorem second_minimum : IsLeast {n : ℕ | admissible 1 n} 3 := by
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [divisorPolynomial_three]
    exact ⟨X, by norm_num; ring⟩
  · intro n hn
    change admissible 1 n at hn
    by_contra! h
    have hc : n = 1 ∨ n = 2 := by have := hn.1; omega
    have hd : (X ^ 2 + 1 : ℚ[X]) ∣ divisorPolynomial n := hn.2
    have hp : ((X ^ 2 + 1 : ℚ[X])).natDegree = 2 := degree_x_pow_add_one 2 (by decide)
    rcases hc with hc | hc
    · subst n
      rw [divisorPolynomial_one] at hd
      have hv := natDegree_le_of_dvd hd X_ne_zero
      rw [hp, natDegree_X] at hv
      omega
    · subst n
      rw [divisorPolynomial_two] at hd
      have he : (X ^ 2 + 1 : ℚ[X]) ∣ X - 1 := by
        convert dvd_sub hd (dvd_refl (X ^ 2 + 1 : ℚ[X])) using 1
        ring
      have hv := natDegree_le_of_dvd he (X_sub_C_ne_zero 1)
      rw [hp, show (X - 1 : ℚ[X]).natDegree = 1 by rw [← map_one (C : ℚ →+* ℚ[X]), natDegree_X_sub_C]] at hv
      omega


private noncomputable def reducedMonomial (k d : ℕ) : ℚ[X] :=
  if d % (2 * k) < k then X ^ (d % (2 * k)) else -X ^ (d % (2 * k) - k)

private theorem monomial_reduction (k d : ℕ) :
    (X ^ k + 1 : ℚ[X]) ∣ X ^ d - reducedMonomial k d := by
  let r := d % (2 * k)
  have hcycle : (X ^ k + 1 : ℚ[X]) ∣ X ^ (2 * k) - 1 := by
    refine ⟨X ^ k - 1, ?_⟩
    rw [mul_comm 2 k, pow_mul]
    ring
  have hexp : (2 * k) * (d / (2 * k)) + r = d := by
    dsimp [r]
    rw [add_comm]
    exact Nat.mod_add_div d (2 * k)
  have hd : (X ^ k + 1 : ℚ[X]) ∣ X ^ d - X ^ r := by
    have hp : (X ^ (2 * k) - 1 : ℚ[X]) ∣ (X ^ (2 * k)) ^ (d / (2 * k)) - 1 := by
      simpa only [one_pow] using (sub_dvd_pow_sub_pow (X ^ (2 * k) : ℚ[X]) 1 (d / (2 * k)))
    have h := dvd_mul_of_dvd_left (dvd_trans hcycle hp) (X ^ r)
    rw [sub_mul, one_mul, ← pow_mul, ← pow_add, hexp] at h
    exact h
  unfold reducedMonomial
  change (X ^ k + 1 : ℚ[X]) ∣ X ^ d - (if r < k then X ^ r else -X ^ (r - k))
  by_cases hr : r < k
  · simpa only [if_pos hr] using hd
  · rw [if_neg hr]
    have hp : (X ^ k + 1 : ℚ[X]) ∣ (X ^ r - (-X ^ (r - k))) := by
      refine ⟨X ^ (r - k), ?_⟩
      rw [add_mul, one_mul, ← pow_add, show k + (r - k) = r by omega, sub_neg_eq_add]
    convert dvd_add hd hp using 1
    ring

private noncomputable def reducedPolynomial (k n : ℕ) : ℚ[X] :=
  ∑ d ∈ n.divisors, reducedMonomial k d

private theorem reduced_degree (k n : ℕ) (hk : 0 < k) :
    (reducedPolynomial k n).natDegree < k := by
  have hdeg : (reducedPolynomial k n).natDegree ≤ k - 1 := by
    unfold reducedPolynomial
    apply natDegree_sum_le_of_forall_le
    intro d hd
    have hr : d % (2 * k) < 2 * k := Nat.mod_lt _ (by omega)
    unfold reducedMonomial
    split
    · rw [natDegree_X_pow]
      omega
    · rw [natDegree_neg, natDegree_X_pow]
      omega
  omega

private theorem residue_reduction (k n : ℕ) (hk : 0 < k) :
    ((X ^ k + 1 : ℚ[X]) ∣ divisorPolynomial n) ↔ reducedPolynomial k n = 0 := by
  have h : (X ^ k + 1 : ℚ[X]) ∣ divisorPolynomial n - reducedPolynomial k n := by
    unfold divisorPolynomial reducedPolynomial
    rw [← Finset.sum_sub_distrib]
    exact Finset.dvd_sum fun d _ => monomial_reduction k d
  rw [dvd_iff_dvd_of_dvd_sub h]
  refine ⟨fun hd => ?_, fun hzero => hzero ▸ dvd_zero _⟩
  by_contra hz
  have hdeg := natDegree_le_of_dvd hd hz
  rw [degree_x_pow_add_one k hk] at hdeg
  exact (not_le_of_gt (reduced_degree k n hk)) hdeg


private theorem reduced_coeff (k n r : ℕ) (hr : r < k) :
    (reducedPolynomial k n).coeff r =
      ((n.divisors.filter (fun d => d % (2 * k) = r)).card : ℚ) -
      ((n.divisors.filter (fun d => d % (2 * k) = r + k)).card : ℚ) := by
  rw [reducedPolynomial, finsetSum_coeff, ← Finset.sum_boole (fun d : ℕ => d % (2 * k) = r),
    ← Finset.sum_boole (fun d : ℕ => d % (2 * k) = r + k), ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases h : d % (2 * k) < k
  · have hn : d % (2 * k) ≠ r + k := by omega
    simp [reducedMonomial, h, hn, coeff_X_pow, eq_comm]
  · have hn : d % (2 * k) ≠ r := by omega
    have hequiv : r = d % (2 * k) - k ↔ d % (2 * k) = r + k := by omega
    simp [reducedMonomial, h, hn, hequiv, coeff_X_pow]

private theorem paired_residues (k n : ℕ) (hk : 0 < k) :
    ((X ^ k + 1 : ℚ[X]) ∣ divisorPolynomial n) ↔
    ∀ r < k, (n.divisors.filter (fun d => d % (2 * k) = r)).card =
      (n.divisors.filter (fun d => d % (2 * k) = r + k)).card := by
  rw [residue_reduction k n hk]
  constructor
  · intro hp r hr
    have h := reduced_coeff k n r hr
    rw [hp, coeff_zero] at h
    exact_mod_cast (sub_eq_zero.mp h.symm)
  · intro h
    ext r
    rw [coeff_zero]
    by_cases hr : r < k
    · rw [reduced_coeff k n r hr, h r hr, sub_self]
    · exact coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (reduced_degree k n hk) (by omega))


private theorem residue_test_zero {R : Type*} [AddCommGroup R] (k n : ℕ)
    (hk : 0 < k) (f : ℕ → R)
    (hmod : ∀ d, f d = f (d % (2 * k)))
    (hshift : ∀ r < k, f (r + k) = -f r)
    (hpoly : (X ^ k + 1 : ℚ[X]) ∣ divisorPolynomial n) :
    ∑ d ∈ n.divisors, f d = 0 := by
  let count : ℕ → ℕ := fun r => (n.divisors.filter (fun d => d % (2 * k) = r)).card
  let a : ℕ → R := fun r => count r • f r
  have hfiber : ∀ d ∈ n.divisors, d % (2 * k) ∈ Finset.range (2 * k) :=
    fun d _ => Finset.mem_range.mpr (Nat.mod_lt _ (by omega))
  calc
    _ = ∑ r ∈ Finset.range (2 * k), ∑ d ∈ n.divisors with d % (2 * k) = r, f d :=
      (Finset.sum_fiberwise_of_maps_to hfiber f).symm
    _ = ∑ r ∈ Finset.range (2 * k), a r := by
      apply Finset.sum_congr rfl
      intro r hr
      unfold a count
      rw [← Finset.sum_const]
      apply Finset.sum_congr rfl
      intro d hd
      rw [hmod d, (Finset.mem_filter.mp hd).2]
    _ = _ := by
      rw [two_mul, Finset.sum_range_add, ← Finset.sum_add_distrib]
      apply Finset.sum_eq_zero
      intro r hr
      have hr' := Finset.mem_range.mp hr
      have heq : count r = count (r + k) := (paired_residues k n hk).mp hpoly r hr'
      simp only [add_comm k r, a, hshift _ hr', heq]
      rw [← nsmul_add, add_neg_cancel, nsmul_zero]


private theorem twice_pow (i : ℕ) : 2 * (2 ^ i : ℕ) = 2 ^ (i + 1) := by rw [pow_succ, mul_comm]

private theorem two_power_pos (i : ℕ) : 0 < (2 ^ i : ℕ) := by positivity

private theorem half_even (i : ℕ) (hi : 1 ≤ i) : 2 ∣ (2 ^ i : ℕ) := by
  simpa using pow_dvd_pow (2 : ℕ) hi

private theorem half_dvd_four (i : ℕ) (hi : 2 ≤ i) : 4 ∣ (2 ^ i : ℕ) := by
  exact pow_dvd_pow (2 : ℕ) hi

private theorem candidate_exists (i : ℕ) (hi : 2 ≤ i) :
    ∃ n : ℕ, IsLeast {m : ℕ | candidate i m} n := by
  have h2 := half_even i (by omega)
  have ho : Odd (1 + 2 ^ i) := by
    obtain ⟨c, hc⟩ := h2
    exact ⟨c, by omega⟩
  have hc := (Nat.coprime_two_right.mpr ho).pow_right (i + 1)
  obtain ⟨p, _, hp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq 0 (q := 2 ^ (i + 1)) (by positivity) hc
  have hnorm : (1 + (2 ^ i : ℕ)) < 2 ^ (i + 1) := by
    have h4 := half_dvd_four i hi
    have hpos := two_power_pos i
    obtain ⟨c, hc⟩ := h4
    rw [← twice_pow i]
    omega
  have hpmod : p % (2 ^ (i + 1)) = 1 + 2 ^ i := by
    change p % (2 ^ (i + 1)) = (1 + 2 ^ i) % (2 ^ (i + 1)) at hmod
    rwa [Nat.mod_eq_of_lt hnorm] at hmod
  have hex : ∃ n : ℕ, candidate i n := ⟨p, Or.inl ⟨p, 1, hp, by decide,
    by simpa only [pow_one] using hpmod, by norm_num⟩⟩
  classical
  exact ⟨Nat.find hex, Nat.find_spec hex, fun n hn => Nat.find_min' hex hn⟩

private theorem reduced_shift (k a b : ℕ) (hk : 0 < k)
    (h : b % (2 * k) = (a % (2 * k) + k) % (2 * k)) :
    reducedMonomial k b = -reducedMonomial k a := by
  have hr : a % (2 * k) < 2 * k := Nat.mod_lt _ (by omega)
  unfold reducedMonomial
  by_cases hs : a % (2 * k) < k
  · have hm : (a % (2 * k) + k) % (2 * k) = a % (2 * k) + k := Nat.mod_eq_of_lt (by omega)
    simp only [h, hm, if_pos hs, if_neg (by omega : ¬ a % (2 * k) + k < k), Nat.add_sub_cancel]
  · have hm : (a % (2 * k) + k) % (2 * k) = a % (2 * k) - k := by
      rw [Nat.mod_eq_sub_mod (by omega), show a % (2 * k) + k - 2 * k = a % (2 * k) - k by omega,
        Nat.mod_eq_of_lt (by omega)]
    simp only [h, hm, if_neg hs, if_pos (by omega : a % (2 * k) - k < k), neg_neg]

private theorem mul_half_mod (k a : ℕ) (ha : Odd a) :
    (a * (1 + k)) % (2 * k) = (a % (2 * k) + k) % (2 * k) := by
  obtain ⟨b, hb⟩ := ha
  have heq : a * (1 + k) = a + k + 2 * k * b := by rw [hb]; ring
  rw [heq, Nat.add_mul_mod_self_left]
  exact (Nat.mod_add_mod a (2 * k) k).symm


private theorem prime_power_candidate (i p d : ℕ) (hi : 2 ≤ i) (hp : p.Prime) (hd : 0 < d)
    (hc : p ^ d % (2 ^ (i + 1)) = 1 + 2 ^ i) : admissible i (p ^ (2 * d - 1)) := by
  have hk := two_power_pos i
  have h2 := half_even i (by omega)
  have hkbig : 1 < 2 ^ i := by
    obtain ⟨b, hb⟩ := h2
    omega
  have hc' : p ^ d ≡ 1 + 2 ^ i [MOD 2 * (2 ^ i)] := by
    change p ^ d % (2 * 2 ^ i) = (1 + 2 ^ i) % (2 * 2 ^ i)
    rw [Nat.mod_eq_of_lt (by omega : 1 + (2 ^ i : ℕ) < 2 * 2 ^ i), twice_pow]
    exact hc
  have hodd : Odd p := by
    rcases hp.eq_two_or_odd with hp2 | hpodd
    · subst p
      have he := hc'.of_dvd (dvd_mul_right 2 (2 ^ i))
      change (2 ^ d) % 2 = (1 + 2 ^ i) % 2 at he
      rw [Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 hd.ne')] at he
      have hk2 := Nat.mod_eq_zero_of_dvd h2
      omega
    · exact Nat.odd_iff.mpr hpodd
  refine ⟨pow_pos hp.pos _, (residue_reduction (2 ^ i) _ hk).mpr ?_⟩
  unfold reducedPolynomial
  rw [Nat.sum_divisors_prime_pow hp, show 2 * d - 1 + 1 = d + d by omega, Finset.sum_range_add,
    ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro j hj
  have hc'' : (p ^ j * p ^ d) % (2 * (2 ^ i)) =
      (p ^ j * (1 + 2 ^ i)) % (2 * (2 ^ i)) := hc'.mul_left _
  rw [pow_add, mul_comm (p ^ d), reduced_shift (2 ^ i) (p ^ j) _ hk
    (hc''.trans (mul_half_mod _ _ hodd.pow)), add_neg_cancel]

private theorem two_prime_divisors (p q : ℕ) (hp : p.Prime) (hq : q.Prime) :
    (p * q).divisors = {1, p, q, p * q} := by
  ext x
  simp only [Nat.mem_divisors, mul_ne_zero hp.ne_zero hq.ne_zero, ne_eq, not_false_eq_true, and_true,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    by_cases hpx : p ∣ x
    · obtain ⟨a, rfl⟩ := hpx
      have ha := (Nat.mul_dvd_mul_iff_left hp.pos).mp h
      rcases (Nat.dvd_prime hq).mp ha with rfl | rfl
      · simp
      · simp
    · have hc := (hp.coprime_iff_not_dvd.mpr hpx).symm
      have hq' := hc.dvd_of_dvd_mul_left h
      rcases (Nat.dvd_prime hq).mp hq' with rfl | rfl <;> simp
  · rintro (rfl | rfl | rfl | rfl) <;> simp


private theorem character_antishift (k : ℕ) (hk : 2 ∣ k)
    (χ : DirichletCharacter ℂ (2 * k)) (hχ : χ ((1 + k : ℕ) : ZMod (2 * k)) = -1)
    (r : ℕ) : χ ((r + k : ℕ) : ZMod (2 * k)) = -χ (r : ZMod (2 * k)) := by
  have heven (a : ℕ) (ha : Even a) : χ (a : ZMod (2 * k)) = 0 := by
    obtain ⟨b, hb⟩ := ha
    have hmul : ((1 + k : ℕ) : ZMod (2 * k)) * (a : ZMod (2 * k)) = a := by
      rw [← Nat.cast_mul, ZMod.natCast_eq_natCast_iff]
      have heq : (1 + k) * a = a + (2 * k) * b := by rw [hb]; ring
      -- Cast the complete product before taking its residue.
      change ((1 + k) * a) % (2 * k) = a % (2 * k)
      rw [heq, Nat.add_mul_mod_self_left]
    have hh := congrArg (fun x => χ x) hmul
    rw [map_mul, hχ, neg_one_mul] at hh
    linear_combination -(1 / 2 : ℂ) * hh
  rcases Nat.even_or_odd r with he | ho
  · rw [heven r he, heven (r + k) (he.add (even_iff_two_dvd.mpr hk)), neg_zero]
  · have hm : ((1 + k : ℕ) : ZMod (2 * k)) * (r : ZMod (2 * k)) = (r + k : ℕ) := by
      rw [← Nat.cast_mul, ZMod.natCast_eq_natCast_iff]
      change ((1 + k) * r) % (2 * k) = (r + k) % (2 * k)
      rw [mul_comm (1 + k), mul_half_mod k r ho, Nat.mod_add_mod]
    rw [← hm, map_mul, hχ, neg_one_mul]

private theorem character_divisor_sum_zero (k n : ℕ) (hk : 0 < k) (h2 : 2 ∣ k)
    (χ : DirichletCharacter ℂ (2 * k)) (hχ : χ ((1 + k : ℕ) : ZMod (2 * k)) = -1)
    (hpoly : (X ^ k + 1 : ℚ[X]) ∣ divisorPolynomial n) :
    ∑ d ∈ n.divisors, χ (d : ZMod (2 * k)) = 0 := by
  apply residue_test_zero k n hk (fun d => χ (d : ZMod (2 * k))) _ _ hpoly
  · intro d
    rw [ZMod.natCast_mod]
  · intro r hr
    exact character_antishift k h2 χ hχ r

private theorem char_sq_sign {m : ℕ} (χ : DirichletCharacter ℂ m) {x : ZMod m}
    (hx : x ^ 2 = 1) : χ x = 1 ∨ χ x = -1 :=
  sq_eq_one_iff.mp (by rw [← map_pow, hx, map_one])

private theorem character_pair (k : ℕ) (hk : 2 < k) (h2 : 2 ∣ k) :
    ∃ χ ψ : DirichletCharacter ℂ (2 * k),
      χ ((1 + k : ℕ) : ZMod (2 * k)) = -1 ∧ χ (-1) = 1 ∧
      ψ ((1 + k : ℕ) : ZMod (2 * k)) = -1 ∧ ψ (-1) = -1 := by
  letI : NeZero (2 * k) := ⟨by omega⟩
  let h : ZMod (2 * k) := ((1 + k : ℕ) : ZMod (2 * k))
  change ∃ χ ψ : DirichletCharacter ℂ (2 * k),
    χ h = -1 ∧ χ (-1) = 1 ∧ ψ h = -1 ∧ ψ (-1) = -1
  have h2k : (2 : ZMod (2 * k)) * (k : ZMod (2 * k)) = 0 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using ZMod.natCast_self (2 * k)
  have hs : h ^ 2 = 1 := by
    obtain ⟨b, hb⟩ := h2
    have hb' : (k : ZMod (2 * k)) = 2 * (b : ZMod (2 * k)) := by
      simpa only [Nat.cast_mul, Nat.cast_two] using congrArg (fun n : ℕ => (n : ZMod (2 * k))) hb
    have sq : (k : ZMod (2 * k)) ^ 2 = 0 := by
      linear_combination (k : ZMod (2 * k)) * hb' + (b : ZMod (2 * k)) * h2k
    dsimp [h]
    push_cast
    linear_combination sq + h2k
  have hn1 : h ≠ 1 := by
    intro he
    have hr := (ZMod.natCast_eq_natCast_iff (1 + k) 1 (2 * k)).mp
      (he.trans (Nat.cast_one (R := ZMod (2 * k))).symm)
    change (1 + k) % (2 * k) = 1 % (2 * k) at hr
    rw [Nat.mod_eq_of_lt (by omega : 1 + k < 2 * k), Nat.mod_eq_of_lt (by omega : 1 < 2 * k)] at hr
    omega
  have hm1 : (((2 * k - 1 : ℕ) : ZMod (2 * k))) = -1 := by
    rw [Nat.cast_sub (by omega), ZMod.natCast_self, Nat.cast_one, zero_sub]
  have hn2 : -h ≠ 1 := by
    intro he
    have hh : h = -1 := by simpa only [neg_neg] using congrArg Neg.neg he
    rw [← hm1] at hh
    have hr := (ZMod.natCast_eq_natCast_iff _ _ _).mp hh
    change (1 + k) % (2 * k) = (2 * k - 1) % (2 * k) at hr
    rw [Nat.mod_eq_of_lt (by omega : 1 + k < 2 * k),
      Nat.mod_eq_of_lt (by omega : 2 * k - 1 < 2 * k)] at hr
    omega
  have hminus : (-1 : ZMod (2 * k)) ≠ 1 := by
    rw [← hm1]
    intro he
    have hr := (ZMod.natCast_eq_natCast_iff (2 * k - 1) 1 (2 * k)).mp
      (he.trans (Nat.cast_one (R := ZMod (2 * k))).symm)
    change (2 * k - 1) % (2 * k) = 1 % (2 * k) at hr
    rw [Nat.mod_eq_of_lt (by omega : 2 * k - 1 < 2 * k), Nat.mod_eq_of_lt (by omega : 1 < 2 * k)] at hr
    omega
  obtain ⟨a, ha⟩ := DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity ℂ hn1
  have ha' := (char_sq_sign a hs).resolve_left ha
  obtain ⟨b, hb⟩ := DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity ℂ hn2
  obtain ⟨c, hc⟩ := DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity ℂ hminus
  have hc' := (char_sq_sign c (by ring : (-1 : ZMod (2 * k)) ^ 2 = 1)).resolve_left hc
  rcases char_sq_sign b hs with hb₁ | hb₁
  · have hb₂ : b (-1) = -1 := by
      rcases char_sq_sign b (by ring : (-1 : ZMod (2 * k)) ^ 2 = 1) with h₁ | h₁
      · exfalso
        apply hb
        rw [← neg_one_mul, map_mul, h₁, hb₁, one_mul]
      · exact h₁
    rcases char_sq_sign a (by ring : (-1 : ZMod (2 * k)) ^ 2 = 1) with ha₁ | ha₁
    · exact ⟨a, a * b, ha', ha₁, by simp [ha', hb₁], by simp [ha₁, hb₂]⟩
    · exact ⟨a * b, a, by simp [ha', hb₁], by simp [ha₁, hb₂], ha', ha₁⟩
  · have hb₂ : b (-1) = 1 := by
      rcases char_sq_sign b (by ring : (-1 : ZMod (2 * k)) ^ 2 = 1) with h₁ | h₁
      · exact h₁
      · exfalso
        apply hb
        rw [← neg_one_mul, map_mul, h₁, hb₁]
        norm_num
    rcases char_sq_sign c hs with hc₁ | hc₁
    · exact ⟨b, b * c, hb₁, hb₂, by simp [hb₁, hc₁], by simp [hb₂, hc']⟩
    · exact ⟨b, c, hb₁, hb₂, hc₁, hc'⟩


private theorem four_dvd_modulus (i : ℕ) (hi : 2 ≤ i) : 4 ∣ 2 * (2 ^ i) :=
  dvd_mul_of_dvd_right (half_dvd_four i hi) 2

private theorem half_gt_two (i : ℕ) (hi : 2 ≤ i) : 2 < (2 ^ i : ℕ) := by
  have hp := two_power_pos i
  obtain ⟨b, hb⟩ := half_dvd_four i hi
  omega

private theorem half_involution_class (i : ℕ) (hi : 2 ≤ i) (x : ZMod (2 * 2 ^ i))
    (hx : x ^ 2 = 1) (h4 : (ZMod.cast x : ZMod 4) = 1) :
    x = 1 ∨ x = ((1 + 2 ^ i : ℕ) : ZMod (2 * 2 ^ i)) := by
  let k := 2 ^ i
  have hk : 0 < k := two_power_pos i
  letI : NeZero (2 * 2 ^ i) := ⟨by positivity⟩
  let r := x.val
  have hr : r < 2 * k := ZMod.val_lt x
  have hcast : (r : ZMod (2 * 2 ^ i)) = x := ZMod.natCast_zmod_val x
  have hr4 : (r : ZMod 4) = (1 : ZMod 4) := by
    rw [← hcast, ZMod.cast_natCast (four_dvd_modulus i hi) r] at h4
    exact h4
  have hrmod : r % 4 = 1 := by
    have h := (ZMod.natCast_eq_natCast_iff r 1 4).mp
      (hr4.trans (Nat.cast_one (R := ZMod 4)).symm)
    exact h
  let a := r / 4
  have hform : r = 4 * a + 1 := by
    dsimp [a]
    have := Nat.mod_add_div r 4
    omega
  have hpos : 0 < r := by omega
  have h1 : 1 ≤ r ^ 2 := pow_pos hpos _
  have hmod : 1 ≡ r ^ 2 [MOD 2 * k] := by
    apply (ZMod.natCast_eq_natCast_iff 1 (r ^ 2) (2*k)).mp
    rw [Nat.cast_one, Nat.cast_pow]
    exact hx.symm.trans (by rw [hcast])
  have hdiv := (Nat.modEq_iff_dvd' h1).mp hmod
  have heq : r ^ 2 - 1 = 2 * ((4 * a) * (2 * a + 1)) := by
    rw [hform, show (4 * a + 1) ^ 2 = 2 * ((4 * a) * (2 * a + 1)) + 1 by ring,
      Nat.add_sub_cancel]
  rw [heq] at hdiv
  have hprod : k ∣ (4 * a) * (2 * a + 1) := (Nat.mul_dvd_mul_iff_left (by decide : 0 < 2)).mp hdiv
  have hcop : k.Coprime (2 * a + 1) :=
    ((Nat.coprime_two_right.mpr (show Odd (2 * a + 1) from ⟨a, rfl⟩)).pow_right i).symm
  obtain ⟨b, hb⟩ := hcop.dvd_of_dvd_mul_right hprod
  have hbnd : b < 2 := by
    apply (Nat.mul_lt_mul_left hk).mp
    rw [← hb, mul_comm]
    omega
  have hcases : r = 1 ∨ r = 1 + k := by
    have hb01 : b = 0 ∨ b = 1 := by omega
    rcases hb01 with h | h
    · rw [h, mul_zero] at hb
      omega
    · rw [h, mul_one] at hb
      omega
  rcases hcases with h | h
  · rw [h, Nat.cast_one] at hcast
    exact Or.inl hcast.symm
  · rw [h] at hcast
    exact Or.inr hcast.symm

private theorem involution_classes (i : ℕ) (hi : 2 ≤ i) (x : ZMod (2 * 2 ^ i))
    (hx : x ^ 2 = 1) :
    x = 1 ∨ x = ((1 + 2 ^ i : ℕ) : ZMod (2 * 2 ^ i)) ∨
      x = -1 ∨ x = -((1 + 2 ^ i : ℕ) : ZMod (2 * 2 ^ i)) := by
  let f := ZMod.castHom (four_dvd_modulus i hi) (ZMod 4)
  have hs : (f x) ^ 2 = 1 := by rw [← map_pow, hx, map_one]
  have hcheck : ∀ y : ZMod 4, y ^ 2 = 1 → y = 1 ∨ y = -1 := by decide
  rcases hcheck (f x) hs with h | h
  · rcases half_involution_class i hi x hx h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · have hs' : (-x) ^ 2 = 1 := by simpa only [neg_sq] using hx
    have h' : f (-x) = 1 := by simp only [map_neg, h, neg_neg]
    rcases half_involution_class i hi (-x) hs' h' with h | h
    · exact Or.inr (Or.inr (Or.inl (by simpa only [neg_neg] using congrArg Neg.neg h)))
    · exact Or.inr (Or.inr (Or.inr (by simpa only [neg_neg] using congrArg Neg.neg h)))


private theorem vanishing_factor (k n : ℕ) (hk : 0 < k) (hn : n ≠ 0)
    (χ : DirichletCharacter ℂ (2 * k))
    (hz : ∑ d ∈ n.divisors, χ (d : ZMod (2 * k)) = 0) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n ∧
      χ (p : ZMod (2 * k)) ≠ 1 ∧ (χ (p : ZMod (2 * k))) ^ (n.factorization p + 1) = 1 := by
  classical
  letI : Fact (1 < 2 * k) := ⟨by omega⟩
  let ψ : ArithmeticFunction ℂ := ⟨fun d => χ (d : ZMod (2 * k)), by simp [χ.map_zero]⟩
  have hmψ : ψ.IsMultiplicative := by
    refine ⟨by change χ ((1 : ℕ) : ZMod (2 * k)) = 1; simp, ?_⟩
    intro a b _
    change χ ((a * b : ℕ) : ZMod (2 * k)) = χ (a : ZMod (2 * k)) * χ (b : ZMod (2 * k))
    simp only [Nat.cast_mul, map_mul]
  let f : ArithmeticFunction ℂ := (ArithmeticFunction.zeta : ArithmeticFunction ℕ) * ψ
  have hf : f.IsMultiplicative := ArithmeticFunction.isMultiplicative_zeta.natCast.mul hmψ
  have happ (d : ℕ) : f d = ∑ e ∈ d.divisors, χ (e : ZMod (2 * k)) :=
    ArithmeticFunction.coe_zeta_mul_apply
  have h := hf.multiplicative_factorization f hn
  rw [happ, hz, Finsupp.prod] at h
  obtain ⟨p, hp, hpzero⟩ := Finset.prod_eq_zero_iff.mp h.symm
  rw [Nat.support_factorization] at hp
  obtain ⟨hprime, hdvd, _⟩ := Nat.mem_primeFactors.mp hp
  rw [happ, Nat.sum_divisors_prime_pow hprime] at hpzero
  simp_rw [Nat.cast_pow, map_pow] at hpzero
  refine ⟨p, hprime, hdvd, ?_, ?_⟩
  · intro he
    simp [he] at hpzero
    have he' : ((n.factorization p + 1 : ℕ) : ℂ) = 0 := by simpa only [Nat.cast_add, Nat.cast_one] using hpzero
    exact Nat.succ_ne_zero _ (Nat.cast_eq_zero.mp he')
  · have h := geom_sum_mul (χ (p : ZMod (2 * k))) (n.factorization p + 1)
    rw [hpzero, zero_mul] at h
    exact sub_eq_zero.mp h.symm


private theorem neg_one_residue (k : ℕ) (hk : 0 < k) :
    ((2 * k - 1 : ℕ) : ZMod (2 * k)) = -1 := by
  rw [Nat.cast_sub (by omega), ZMod.natCast_self, Nat.cast_one, zero_sub]

private theorem neg_half_residue (k : ℕ) (hk : 0 < k) :
    ((k - 1 : ℕ) : ZMod (2 * k)) = -((1 + k : ℕ) : ZMod (2 * k)) := by
  have h2k : (2 : ZMod (2 * k)) * (k : ZMod (2 * k)) = 0 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using ZMod.natCast_self (2 * k)
  rw [Nat.cast_sub (by omega)]
  push_cast
  linear_combination h2k

private theorem pair_prime_candidate (i p q : ℕ) (hi : 2 ≤ i) (hp : p.Prime) (hq : q.Prime)
    (hpc : p % (2 ^ (i + 1)) = 2 ^ (i + 1) - 1)
    (hqc : q % (2 ^ (i + 1)) = 2 ^ i - 1) : admissible i (p * q) := by
  rw [← twice_pow i] at hpc hqc
  let k := 2 ^ i
  have hk : 2 < k := half_gt_two i hi
  change p % (2 * k) = 2 * k - 1 at hpc
  change q % (2 * k) = k - 1 at hqc
  have hpneq : p ≠ q := by
    intro he
    rw [he, hqc] at hpc
    omega
  have hpZ : (p : ZMod (2 * k)) = -1 := by
    rw [← ZMod.natCast_mod p (2 * k), hpc, neg_one_residue k (by omega)]
  have hqZ : (q : ZMod (2 * k)) = -((1 + k : ℕ) : ZMod (2 * k)) := by
    rw [← ZMod.natCast_mod q (2 * k), hqc, neg_half_residue k (by omega)]
  have hpqZ : ((p * q : ℕ) : ZMod (2 * k)) = ((1 + k : ℕ) : ZMod (2 * k)) := by
    rw [Nat.cast_mul, hpZ, hqZ, neg_one_mul, neg_neg]
  have hpqc : (p * q) % (2 * k) = 1 + k := by
    have hh := (ZMod.natCast_eq_natCast_iff _ _ _).mp hpqZ
    change (p * q) % (2 * k) = (1 + k) % (2 * k) at hh
    rwa [Nat.mod_eq_of_lt (by omega : 1 + k < 2 * k)] at hh
  have hpqshift : (p * q) % (2 * k) = (1 % (2 * k) + k) % (2 * k) := by
    rw [hpqc, Nat.mod_eq_of_lt (by omega : 1 < 2 * k), Nat.mod_eq_of_lt (by omega : 1 + k < 2 * k)]
  have hpqshift' : q % (2 * k) = (p % (2 * k) + k) % (2 * k) := by
    rw [hpc, hqc, Nat.mod_eq_sub_mod (by omega : 2 * k ≤ 2 * k - 1 + k),
      show 2*k-1+k-2*k = k-1 by omega, Nat.mod_eq_of_lt (by omega : k - 1 < 2*k)]
  have hppq : p ≠ p * q := by
    have := Nat.mul_lt_mul_of_pos_left hq.one_lt hp.pos
    simpa only [mul_one] using this.ne
  have hqpq : q ≠ p * q := by
    have := Nat.mul_lt_mul_of_pos_right hp.one_lt hq.pos
    simpa only [one_mul] using this.ne
  refine ⟨Nat.mul_pos hp.pos hq.pos, (residue_reduction k _ (by omega)).mpr ?_⟩
  unfold reducedPolynomial
  rw [two_prime_divisors p q hp hq]
  have hone : 1 ≠ p * q := ne_of_lt (by have := hp.one_lt; have := hq.one_lt; nlinarith)
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, hp.ne_one.symm, hq.ne_one.symm,
    hpneq, hppq, hqpq, hone, or_false, not_false_eq_true, Finset.sum_singleton]
  rw [reduced_shift k 1 _ (by omega) hpqshift, reduced_shift k p _ (by omega) hpqshift']
  abel

private theorem candidate_admissible (i n : ℕ) (hi : 2 ≤ i) (h : candidate i n) :
    admissible i n := by
  rcases h with ⟨p, d, hp, hd, hmod, rfl⟩ | ⟨p, q, hp, hq, hpm, hqm, rfl⟩
  · exact prime_power_candidate i p d hi hp hd hmod
  · exact pair_prime_candidate i p q hi hp hq hpm hqm


private theorem prime_character_type (i p e : ℕ) (hi : 2 ≤ i)
    (χ : DirichletCharacter ℂ (2 * 2 ^ i))
    (hχ : χ ((1 + 2 ^ i : ℕ) : ZMod (2 * 2 ^ i)) = -1)
    (hne : χ (p : ZMod (2 * 2 ^ i)) ≠ 1)
    (hpow : (χ (p : ZMod (2 * 2 ^ i))) ^ (e + 1) = 1) :
    (∃ d : ℕ, 0 < d ∧ p ^ d % (2 ^ (i + 1)) = 1 + 2 ^ i ∧ (2 * d) ∣ e + 1) ∨
      (p : ZMod (2 * 2 ^ i)) = -1 ∨
      (p : ZMod (2 * 2 ^ i)) = -((1 + 2 ^ i : ℕ) : ZMod (2 * 2 ^ i)) := by
  let x : ZMod (2 * 2 ^ i) := p
  let h : ZMod (2 * 2 ^ i) := ((1 + 2 ^ i : ℕ) : ZMod (2 * 2 ^ i))
  change χ x ≠ 1 at hne
  change (χ x) ^ (e + 1) = 1 at hpow
  change χ h = -1 at hχ
  have hxunit : IsUnit x := by
    by_contra hnot
    rw [χ.map_nonunit hnot, zero_pow (Nat.succ_ne_zero _)] at hpow
    exact zero_ne_one hpow
  have hcop : p.Coprime (2 * 2 ^ i) := (ZMod.isUnit_iff_coprime _ _).mp hxunit
  have hodd : p % 2 = 1 := Nat.odd_iff.mp
    (Nat.coprime_two_right.mp (hcop.coprime_dvd_right (dvd_mul_right 2 (2 ^ i))))
  have htot : (2 * (2 ^ i)).totient = 2 ^ i := by
    rw [twice_pow, Nat.totient_prime_pow_succ Nat.prime_two]
    simp
  have hpowX : x ^ (2 ^ i) = 1 := by
    have hc := Nat.ModEq.pow_totient hcop
    rw [htot] at hc
    simpa only [Nat.cast_pow, Nat.cast_one, x] using
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr hc
  obtain ⟨b, _, hord⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (orderOf_dvd_iff_pow_eq_one.mpr hpowX)
  have hb : 0 < b := by
    by_contra! hb
    have hb0 : b = 0 := by omega
    rw [hb0, pow_zero] at hord
    have hx := pow_orderOf_eq_one x
    rw [hord, pow_one] at hx
    exact hne (by rw [hx, map_one])
  let d := 2 ^ (b - 1)
  have hd : 0 < d := two_power_pos _
  have hdouble : 2 * d = 2 ^ b := by
    dsimp only [d]
    rw [twice_pow, show b - 1 + 1 = b by omega]
  have hhalfne : x ^ d ≠ 1 := by
    intro he
    have hh := Nat.le_of_dvd hd (orderOf_dvd_iff_pow_eq_one.mpr he)
    rw [hord, ← hdouble] at hh
    omega
  have hhalfsq : (x ^ d) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm d 2, hdouble, ← hord, pow_orderOf_eq_one]
  have hstep : x ^ d = h ∨ x = -1 ∨ x = -h := by
    by_cases hb1 : b = 1
    · have hd1 : d = 1 := by simp [d, hb1]
      rcases involution_classes i hi (x ^ d) hhalfsq with he | he | he | he
      · exact (hhalfne he).elim
      · exact Or.inl he
      · exact Or.inr (Or.inl (by simpa only [hd1, pow_one] using he))
      · exact Or.inr (Or.inr (by simpa only [hd1, pow_one] using he))
    · have hde : d = 2 * 2 ^ (b - 2) := by
        dsimp only [d]
        rw [twice_pow, show b - 2 + 1 = b - 1 by omega]
      have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by
        have ht := Nat.mod_mod_of_dvd p (by decide : 2 ∣ 4)
        omega
      have hsq : (p : ZMod 4) ^ 2 = 1 := by
        rw [← ZMod.natCast_mod p 4]
        rcases hp4 with hp4 | hp4 <;> rw [hp4] <;> decide
      let f := ZMod.castHom (four_dvd_modulus i hi) (ZMod 4)
      have hmod : (ZMod.cast (x ^ d) : ZMod 4) = 1 := by
        change f (x ^ d) = 1
        rw [map_pow, show f x = (p : ZMod 4) by exact map_natCast f p,
          hde, pow_mul, hsq, one_pow]
      rcases half_involution_class i hi (x ^ d) hhalfsq hmod with he | he
      · exact (hhalfne he).elim
      · exact Or.inl he
  rcases hstep with hstep | hminor
  · left
    have hpmod : p ^ d % (2 ^ (i + 1)) = 1 + 2 ^ i := by
      have hh := (ZMod.natCast_eq_natCast_iff (p ^ d) (1 + 2 ^ i) (2 * 2 ^ i)).mp
        (by rw [Nat.cast_pow]; exact hstep)
      change p ^ d % (2 * 2 ^ i) = (1 + 2 ^ i) % (2 * 2 ^ i) at hh
      rw [Nat.mod_eq_of_lt (by have := half_gt_two i hi; omega : 1 + 2 ^ i < 2 * 2 ^ i),
        twice_pow] at hh
      exact hh
    refine ⟨d, hd, hpmod, ?_⟩
    have hχbig : (χ x) ^ (2 ^ b) = 1 := by rw [← map_pow, ← hord, pow_orderOf_eq_one, map_one]
    obtain ⟨c, hcb, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (orderOf_dvd_iff_pow_eq_one.mpr hχbig)
    have heq : c = b := by
      by_contra hnot
      have hdvd : orderOf (χ x) ∣ d := by
        rw [hc]
        exact pow_dvd_pow 2 (by omega : c ≤ b - 1)
      have hz := (orderOf_dvd_iff_pow_eq_one.mp hdvd)
      rw [← map_pow, hstep, hχ] at hz
      norm_num at hz
    rw [hdouble, ← heq, ← hc]
    exact orderOf_dvd_iff_pow_eq_one.mpr hpow
  · exact Or.inr hminor


private theorem cast_to_residue (i p r : ℕ) (hr : r < 2 * 2 ^ i)
    (he : (p : ZMod (2 * 2 ^ i)) = (r : ZMod (2 * 2 ^ i))) :
    p % (2 ^ (i + 1)) = r := by
  have h := (ZMod.natCast_eq_natCast_iff p r (2 * 2 ^ i)).mp he
  change p % (2 * 2 ^ i) = r % (2 * 2 ^ i) at h
  rwa [Nat.mod_eq_of_lt hr, twice_pow] at h

private theorem candidate_below (i n : ℕ) (hi : 2 ≤ i) (hn : admissible i n) :
    ∃ m : ℕ, candidate i m ∧ m ≤ n := by
  let k := 2 ^ i
  have hk : 2 < k := half_gt_two i hi
  have h2 := half_even i (by omega)
  obtain ⟨χ, ψ, hχ, hχone, hψ, hψneg⟩ := character_pair k hk h2
  have ordinary (p d : ℕ) (hp : p.Prime) (hd : 0 < d)
      (hm : p ^ d % (2 ^ (i + 1)) = 1 + 2 ^ i) (hdiv : (2 * d) ∣ n.factorization p + 1) :
      ∃ m : ℕ, candidate i m ∧ m ≤ n := by
    refine ⟨p ^ (2 * d - 1), Or.inl ⟨p, d, hp, hd, hm, rfl⟩, Nat.le_of_dvd hn.1 ?_⟩
    apply (hp.pow_dvd_iff_le_factorization hn.1.ne').mpr
    have h := Nat.le_of_dvd (Nat.succ_pos _) hdiv
    omega
  have hχsum := character_divisor_sum_zero k n (by omega) h2 χ hχ hn.2
  obtain ⟨p, hp, hpdiv, hpne, hppow⟩ := vanishing_factor k n (by omega) hn.1.ne' χ hχsum
  rcases prime_character_type i p (n.factorization p) hi χ hχ hpne hppow with
    ⟨d, hd, hmd, hdiv⟩ | hneg | hneg
  · exact ordinary p d hp hd hmd hdiv
  · exact (hpne (by rw [hneg]; exact hχone)).elim
  · have hψsum := character_divisor_sum_zero k n (by omega) h2 ψ hψ hn.2
    obtain ⟨q, hq, hqdiv, hqne, hqpow⟩ := vanishing_factor k n (by omega) hn.1.ne' ψ hψsum
    rcases prime_character_type i q (n.factorization q) hi ψ hψ hqne hqpow with
      ⟨d, hd, hmd, hdiv⟩ | hqneg | hqneg
    · exact ordinary q d hq hd hmd hdiv
    · have hpm : p % (2 ^ (i + 1)) = k - 1 := cast_to_residue i p (k - 1) (by omega)
        (hneg.trans (neg_half_residue k (by omega)).symm)
      have hqm : q % (2 ^ (i + 1)) = 2 * k - 1 := cast_to_residue i q (2 * k - 1) (by omega)
        (hqneg.trans (neg_one_residue k (by omega)).symm)
      have hqp : q ≠ p := by
        intro he
        rw [he, hpm] at hqm
        omega
      refine ⟨q * p, Or.inr ⟨q, p, hq, hp, ?_, hpm, rfl⟩, ?_⟩
      · simpa only [twice_pow, k] using hqm
      · exact Nat.le_of_dvd hn.1 (((Nat.coprime_primes hq hp).mpr hqp).mul_dvd_of_dvd_of_dvd hqdiv hpdiv)
    · exfalso
      apply hqne
      rw [hqneg, ← neg_one_mul, map_mul, hψneg, hψ]
      norm_num

theorem OMA.solution : type_of% @OMA.S_mo_234468.main := by
  refine ⟨first_minimum, second_minimum, fun i hi => ⟨candidate_exists i hi, fun n => ?_⟩⟩
  constructor
  · intro h
    obtain ⟨m, hm, hmn⟩ := candidate_below i n hi h.1
    have hnm := h.2 (candidate_admissible i m hi hm)
    refine ⟨(le_antisymm hmn hnm) ▸ hm, ?_⟩
    intro r hr
    exact h.2 (candidate_admissible i r hi hr)
  · intro h
    refine ⟨candidate_admissible i n hi h.1, ?_⟩
    intro r hr
    obtain ⟨m, hm, hmr⟩ := candidate_below i r hi hr
    exact (h.2 hm).trans hmr
