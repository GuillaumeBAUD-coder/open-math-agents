import OMAStatements.S_mo_140378

-- Problem: Recurrence relation for coefficients of product of generating functions for partition numbers
-- Upstream: formal-conjectures statements/mo-140378.lean:0 (declaration OMA.S_mo_140378.main)
-- Credit: @marcusbuffett (the owner of the agent is credited as the solver)
-- Proof: logarithmic differentiation. The weighted operator th f = sum n a_n X^n is a derivation;
-- each factor g = 1/(1 - T^s X^e) satisfies th g = g * (e T^s X^e g), so th P = P * H with
-- H the sum of these terms, and comparing coefficients gives the recurrence.

namespace OMA.P_mo_140378
open PowerSeries OMA.S_mo_140378
noncomputable section

/-- The weighted operator `f ↦ ∑ n aₙ Xⁿ`. -/
def th (f : PS) : PS := mk fun n => (n : LP) * coeff n f

lemma coeff_th (f : PS) (n : ℕ) : coeff n (th f) = (n : LP) * coeff n f := by
  simp [th]

lemma th_mul (f g : PS) : th (f * g) = th f * g + f * th g := by
  ext n : 1
  rw [coeff_th, map_add, coeff_mul, coeff_mul, coeff_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  rw [coeff_th, coeff_th]
  have : (n : LP) = (p.1 : LP) + (p.2 : LP) := by rw [← hp]; push_cast; ring
  rw [this]; ring

lemma th_sub (f g : PS) : th (f - g) = th f - th g := by
  ext n : 1; simp [coeff_th, mul_sub]

lemma th_one : th (1 : PS) = 0 := by
  ext n : 1; rw [coeff_th, coeff_one, map_zero]; split_ifs with h <;> simp [h]

lemma th_C_mul_X_pow (c : LP) (e : ℕ) :
    th (C c * X ^ e) = C ((e : LP) * c) * X ^ e := by
  ext n : 1
  rw [coeff_th, coeff_C_mul_X_pow, coeff_C_mul_X_pow]
  split_ifs with h
  · subst h; ring
  · simp

lemma coeff_geom (d : ℕ) (s : ℤ) (n : ℕ) :
    coeff n (geom d s) =
      if (d + 1) ∣ n then LaurentPolynomial.T (s * ((n / (d + 1) : ℕ) : ℤ)) else 0 := by
  rw [geom, coeff_expand, coeff_mk]

lemma geom_eq (d : ℕ) (s : ℤ) :
    geom d s = 1 + C (LaurentPolynomial.T s) * X ^ (d + 1) * geom d s := by
  ext n : 1
  rw [map_add, mul_assoc, coeff_C_mul, coeff_X_pow_mul', coeff_one, coeff_geom]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [if_neg (show ¬ n = 0 by omega), zero_add]
    by_cases hle : d + 1 ≤ n
    · rw [if_pos hle, coeff_geom]
      obtain ⟨q, rfl⟩ | hnd := em ((d + 1) ∣ n)
      · obtain ⟨q', hq'⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by
          rcases q with _ | q
          · simp at hn
          · simp⟩
        subst hq'
        have h1 : (d + 1) * (q' + 1) - (d + 1) = (d + 1) * q' := by
          rw [Nat.mul_succ]; omega
        rw [h1, if_pos (dvd_mul_right (d + 1) (q' + 1)), if_pos (dvd_mul_right (d + 1) q'),
          Nat.mul_div_cancel_left _ (by omega),
          Nat.mul_div_cancel_left _ (by omega), ← LaurentPolynomial.T_add]
        congr 1; push_cast; ring
      · rw [if_neg hnd, if_neg]
        · simp
        · intro h; apply hnd
          have := Nat.dvd_add h (dvd_refl (d + 1))
          rwa [Nat.sub_add_cancel hle] at this
    · rw [if_neg hle, if_neg, mul_zero]
      intro h; exact hle (Nat.le_of_dvd hn h)

/-- The logarithmic-derivative term of one factor. -/
def h (d : ℕ) (s : ℤ) : PS :=
  C (((d + 1 : ℕ) : LP) * LaurentPolynomial.T s) * X ^ (d + 1) * geom d s

lemma th_geom (d : ℕ) (s : ℤ) : th (geom d s) = geom d s * h d s := by
  set g := geom d s
  set t : LP := LaurentPolynomial.T s
  have hu : (1 - C t * X ^ (d + 1)) * g = 1 := by
    have := geom_eq d s
    calc (1 - C t * X ^ (d + 1)) * g = g - C t * X ^ (d + 1) * g := by ring
      _ = 1 := by linear_combination this
  have hth := congrArg th hu
  rw [th_mul, th_one, th_sub, th_one, th_C_mul_X_pow] at hth
  have key : (1 - C t * X ^ (d + 1)) * th g = C (((d + 1 : ℕ) : LP) * t) * X ^ (d + 1) * g := by
    linear_combination hth
  calc th g = ((1 - C t * X ^ (d + 1)) * g) * th g := by rw [hu, one_mul]
    _ = g * ((1 - C t * X ^ (d + 1)) * th g) := by ring
    _ = g * h d s := by rw [key]; rfl

/-- The sum of the logarithmic-derivative terms of the first `m` factor pairs. -/
def H (m : ℕ) : PS := ∑ d ∈ Finset.range m, (h d 1 + h d (-1))

lemma th_partitionProduct (m : ℕ) : th (partitionProduct m) = partitionProduct m * H m := by
  induction m with
  | zero =>
    simp [partitionProduct, H, th_one]
  | succ m ih =>
    rw [partitionProduct, Finset.prod_range_succ, ← partitionProduct, H,
      Finset.sum_range_succ, ← H, th_mul, th_mul, ih, th_geom, th_geom]
    ring

lemma coeff_h (d : ℕ) (s : ℤ) (j : ℕ) :
    coeff j (h d s) = if (d + 1) ∣ j ∧ 0 < j then
      ((d + 1 : ℕ) : LP) * LaurentPolynomial.T (s * ((j / (d + 1) : ℕ) : ℤ)) else 0 := by
  rw [h, mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  by_cases hle : d + 1 ≤ j
  · rw [if_pos hle, coeff_geom]
    by_cases hdj : (d + 1) ∣ j
    · obtain ⟨q, rfl⟩ := hdj
      have hq : 1 ≤ q := by
        rcases q with _ | q
        · simp at hle
        · omega
      have h1 : (d + 1) * q - (d + 1) = (d + 1) * (q - 1) := by
        rw [Nat.mul_sub, mul_one]
      rw [h1, if_pos (dvd_mul_right (d + 1) (q - 1)),
        if_pos (⟨dvd_mul_right (d + 1) q, by positivity⟩ : (d + 1) ∣ (d + 1) * q ∧ 0 < (d + 1) * q),
        Nat.mul_div_cancel_left _ (by omega), Nat.mul_div_cancel_left _ (by omega), mul_assoc,
        ← LaurentPolynomial.T_add]
      congr 2
      have : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by omega
      rw [this]; ring
    · rw [if_neg, if_neg]
      · simp
      · exact fun h => hdj h.1
      · intro h; apply hdj
        have := Nat.dvd_add h (dvd_refl (d + 1))
        rwa [Nat.sub_add_cancel hle] at this
  · rw [if_neg hle, if_neg, mul_zero]
    rintro ⟨hd, hj⟩; exact hle (Nat.le_of_dvd hj hd)

lemma dvd_geom_sub_one (k d : ℕ) (hkd : k ≤ d) (s : ℤ) : X ^ (k + 1) ∣ geom d s - 1 := by
  have : geom d s - 1 = X ^ (k + 1) * (X ^ (d - k) * C (LaurentPolynomial.T s) * geom d s) := by
    conv_lhs => rw [geom_eq d s]
    rw [← mul_assoc, ← mul_assoc, ← pow_add, show k + 1 + (d - k) = d + 1 by omega]
    ring
  rw [this]; exact dvd_mul_right _ _

lemma dvd_prod_sub_one (k : ℕ) (S : Finset ℕ) (hS : ∀ d ∈ S, k ≤ d) :
    X ^ (k + 1) ∣ (∏ d ∈ S, (geom d 1 * geom d (-1))) - 1 := by
  refine Finset.prod_induction _ (fun f : PS => X ^ (k + 1) ∣ f - 1) ?_ ?_ ?_
  · intro a b ha hb
    have : a * b - 1 = (a - 1) * b + (b - 1) := by ring
    rw [this]; exact dvd_add (dvd_mul_of_dvd_left ha _) hb
  · simp
  · intro d hd
    have h1 := dvd_geom_sub_one k d (hS d hd) 1
    have h2 := dvd_geom_sub_one k d (hS d hd) (-1)
    have : geom d 1 * geom d (-1) - 1 = (geom d 1 - 1) * geom d (-1) + (geom d (-1) - 1) := by
      ring
    rw [this]; exact dvd_add (dvd_mul_of_dvd_left h1 _) h2

lemma coeff_partitionProduct_trunc (k M : ℕ) (hkM : k ≤ M) :
    coeff k (partitionProduct M) = coeff k (partitionProduct k) := by
  rw [partitionProduct, ← Finset.prod_range_mul_prod_Ico _ hkM, ← partitionProduct]
  set Q := ∏ d ∈ Finset.Ico k M, (geom d 1 * geom d (-1))
  have hQ : X ^ (k + 1) ∣ Q - 1 :=
    dvd_prod_sub_one k _ (fun d hd => (Finset.mem_Ico.1 hd).1)
  have hz : coeff k (partitionProduct k * (Q - 1)) = 0 :=
    (X_pow_dvd_iff.1 (dvd_mul_of_dvd_right hQ _)) k (by omega)
  have : partitionProduct k * Q = partitionProduct k + partitionProduct k * (Q - 1) := by ring
  rw [this, map_add, hz, add_zero]

lemma coeff_H (m j : ℕ) : coeff j (H m) = ∑ d ∈ Finset.range m,
    if (d + 1) ∣ j ∧ 0 < j then ((d + 1 : ℕ) : LP) * (LaurentPolynomial.T ((j / (d + 1) : ℕ) : ℤ) +
      LaurentPolynomial.T (-((j / (d + 1) : ℕ) : ℤ))) else 0 := by
  rw [H, map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [map_add, coeff_h, coeff_h]
  split_ifs <;> simp [mul_add]

lemma lcoeff_sum {ι : Type*} (S : Finset ι) (f : ι → LP) (z : ℤ) :
    (∑ i ∈ S, f i).coeff z = ∑ i ∈ S, (f i).coeff z := by
  induction S using Finset.cons_induction with
  | empty => simp
  | cons a S ha ih => rw [Finset.sum_cons, Finset.sum_cons, AddMonoidAlgebra.coeff_add,
      Finsupp.add_apply, ih]

lemma lcoeff_T_mul (j z : ℤ) (f : LP) :
    (LaurentPolynomial.T j * f).coeff z = f.coeff (z - j) := by
  rw [LaurentPolynomial.T, AddMonoidAlgebra.coeff_single_mul_apply, one_mul]
  congr 1; ring

lemma lcoeff_natCast_mul (n : ℕ) (f : LP) (z : ℤ) :
    (((n : ℕ) : LP) * f).coeff z = (n : ℤ) * f.coeff z := by
  rw [← nsmul_eq_mul, AddMonoidAlgebra.coeff_smul_apply, nsmul_eq_mul]

lemma lcoeff_term (m r : ℕ) (c : LP) (z : ℤ) :
    (coeff (r + 1) (H m) * c).coeff z = ∑ d ∈ Finset.range m,
      if d + 1 ∣ r + 1 then ((d + 1 : ℕ) : ℤ) * (c.coeff (z - ((r + 1) / (d + 1) : ℕ)) +
        c.coeff (z + ((r + 1) / (d + 1) : ℕ))) else 0 := by
  rw [coeff_H, Finset.sum_mul, lcoeff_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases hd : d + 1 ∣ r + 1
  · rw [if_pos ⟨hd, Nat.succ_pos r⟩, if_pos hd, mul_assoc, lcoeff_natCast_mul, add_mul,
      AddMonoidAlgebra.coeff_add, Finsupp.add_apply, lcoeff_T_mul, lcoeff_T_mul, sub_neg_eq_add]
  · rw [if_neg (fun h => hd h.1), if_neg hd, zero_mul]; rfl

end
end OMA.P_mo_140378

open PowerSeries OMA.S_mo_140378 OMA.P_mo_140378 in
theorem OMA.solution : type_of% @OMA.S_mo_140378.main := by
  refine ⟨?_, ?_⟩
  · simp [count, partitionProduct]
  · intro m z hm
    have key : ((m : ℕ) : LP) * coeff m (partitionProduct m) = ∑ r ∈ Finset.range m,
        coeff (r + 1) (H m) * coeff (m - (r + 1)) (partitionProduct (m - (r + 1))) := by
      rw [← coeff_th, th_partitionProduct, mul_comm, coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i j => coeff i (H m) * coeff j (partitionProduct m)), Finset.sum_range_succ']
      have h0 : coeff 0 (H m) = 0 := by rw [coeff_H]; simp
      rw [h0, zero_mul, add_zero]
      refine Finset.sum_congr rfl fun r hr => ?_
      rw [coeff_partitionProduct_trunc _ _ (by omega)]
    have := congrArg (fun f : LP => f.coeff z) key
    rw [count, ← lcoeff_natCast_mul, this, lcoeff_sum]
    simp_rw [lcoeff_term]
    rw [Finset.sum_comm]
    rfl
