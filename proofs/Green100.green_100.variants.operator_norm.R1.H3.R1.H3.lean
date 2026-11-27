import OMAReductions.R_Green100_green_100_variants_operator_norm_R1_H3_R1

-- Step Green100.green_100.variants.operator_norm.R1.H3.R1.H3: hypothesis H3 of reduction Green100.green_100.variants.operator_norm.R1.H3.R1
-- Credit: @luciusacarr
-- With v = u⁻¹, a = p v + (1 - q) and b = u p + (1 - q) satisfy b a = 1 and a b = p + (1 - q);
-- direct finiteness forces p + (1 - q) = 1, i.e. p = q.

theorem OMA.solution : OMA.R_Green100_green_100_variants_operator_norm_R1_H3_R1.H3 := by
  intro A _ fin p q u pp pq qp hq
  have vu : (↑u⁻¹ : A) * u = 1 := u.inv_mul
  have qu : q * u = u * p := by
    rw [hq, mul_assoc, vu, mul_one]
  have vq : (↑u⁻¹ : A) * q = p * ↑u⁻¹ := by
    rw [hq, ← mul_assoc, ← mul_assoc, vu, one_mul]
  have qq : q * q = q := by
    nth_rewrite 2 [hq]
    rw [← mul_assoc, ← mul_assoc, qu, mul_assoc (u : A) p p, pp, ← hq]
  have qp' : (1 - q) * p = 0 := by rw [sub_mul, one_mul, qp, sub_self]
  have pq' : p * (1 - q) = 0 := by rw [mul_sub, mul_one, pq, sub_self]
  have q1 : (1 - q) * (1 - q) = 1 - q := by
    rw [mul_sub, mul_one, sub_mul, one_mul, qq, sub_self, sub_zero]
  have hba : ((u : A) * p + (1 - q)) * (p * ↑u⁻¹ + (1 - q)) = 1 := by
    rw [add_mul, mul_add, mul_add]
    have t1 : (u : A) * p * (p * ↑u⁻¹) = q := by
      rw [hq, ← mul_assoc, mul_assoc (u : A) p p, pp]
    have t2 : (u : A) * p * (1 - q) = 0 := by rw [mul_assoc, pq', mul_zero]
    have t3 : (1 - q) * (p * ↑u⁻¹) = 0 := by rw [← mul_assoc, qp', zero_mul]
    rw [t1, t2, t3, q1]
    abel
  have hab := fin _ _ hba
  have hab' : (p * ↑u⁻¹ + (1 - q)) * ((u : A) * p + (1 - q)) = p + (1 - q) := by
    rw [add_mul, mul_add, mul_add]
    have s1 : p * ↑u⁻¹ * ((u : A) * p) = p := by
      rw [← mul_assoc, mul_assoc p, vu, mul_one, pp]
    have s2 : p * ↑u⁻¹ * (1 - q) = 0 := by
      rw [mul_sub, mul_one, mul_assoc, vq, ← mul_assoc, pp, sub_self]
    have s3 : (1 - q) * ((u : A) * p) = 0 := by
      rw [sub_mul, one_mul, ← mul_assoc, qu, mul_assoc, pp, sub_self]
    rw [s1, s2, s3, q1]
    abel
  rw [hab'] at hab
  rw [← sub_eq_zero]
  have e : p - q = p + (1 - q) - 1 := by abel
  rw [e, hab, sub_self]
