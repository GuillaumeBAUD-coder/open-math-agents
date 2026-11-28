import OMAStatements.S_mo_168514

-- Problem: MathOverflow 168514: gcd(p(n), q(n)) is bounded for relatively prime p, q ∈ ℤ[X].
-- Proof: relatively prime in ℤ[X] gives coprime in ℚ[X] (Gauss's lemma); clearing denominators
-- in a Bezout identity gives A p + B q = C d with d ≠ 0, so gcd(p(n), q(n)) ∣ d.

open Polynomial

namespace OMA.Proof_mo_168514

lemma coprime_map (p q : ℤ[X]) (hp : p ≠ 0) (h : IsRelPrime p q) :
    IsCoprime (p.map (Int.castRingHom ℚ)) (q.map (Int.castRingHom ℚ)) := by
  rw [← isRelPrime_iff_isCoprime]
  intro d hdp hdq
  have hp' : p.map (Int.castRingHom ℚ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (RingHom.injective_int (Int.castRingHom ℚ))).mpr hp
  have hd0 : d ≠ 0 := by rintro rfl; exact hp' (zero_dvd_iff.mp hdp)
  obtain ⟨b, hb, hbd⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) d
  set D := IsLocalization.integerNormalization (nonZeroDivisors ℤ) d
  rw [algebraMap_int_eq] at hbd
  have hb0 : (b : ℤ) ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbq : ((b : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hb0
  have hD : D.map (Int.castRingHom ℚ) = C ((b : ℤ) : ℚ) * d := by
    rw [hbd, ← smul_eq_C_mul]; rfl
  have hD0 : D ≠ 0 := by
    intro h0; rw [h0, Polynomial.map_zero] at hD
    exact (mul_ne_zero (by simpa using hbq) hd0) hD.symm
  have hdvd : ∀ r : ℤ[X], d ∣ r.map (Int.castRingHom ℚ) →
      D.primPart ∣ r := by
    intro r hr
    rw [IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast _ _ (isPrimitive_primPart D)]
    have h1 : D.primPart.map (Int.castRingHom ℚ) ∣ D.map (Int.castRingHom ℚ) :=
      Polynomial.map_dvd _ (primPart_dvd D)
    rw [hD] at h1
    exact h1.trans ((mul_dvd_mul_left _ hr).trans
      (by exact ⟨C ((b : ℤ) : ℚ)⁻¹, by rw [mul_comm, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hbq, C_1, one_mul]⟩))
  have hu : IsUnit D.primPart := h (hdvd p hdp) (hdvd q hdq)
  have hum : IsUnit (D.primPart.map (Int.castRingHom ℚ)) := hu.map (mapRingHom _)
  have hc : (D.content : ℚ) ≠ 0 := by
    exact_mod_cast (mt content_eq_zero_iff.mp hD0)
  have hDeq : D.map (Int.castRingHom ℚ) = C (D.content : ℚ) * D.primPart.map (Int.castRingHom ℚ) := by
    conv_lhs => rw [eq_C_content_mul_primPart D]
    rw [Polynomial.map_mul, map_C]; rfl
  rw [isUnit_iff_degree_eq_zero] at hum ⊢
  have e1 := congrArg Polynomial.degree hD
  rw [hDeq, degree_C_mul hc, degree_C_mul hbq, hum] at e1
  exact e1.symm

end OMA.Proof_mo_168514

theorem OMA.solution : type_of% @OMA.S_mo_168514.main := by
  intro p q hp hq hpq
  have hp0 : p ≠ 0 := hp.ne_zero
  obtain ⟨a, b', hab⟩ := OMA.Proof_mo_168514.coprime_map p q hp0 hpq
  obtain ⟨u, hu, hA⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) a
  obtain ⟨v, hv, hB⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) b'
  set A := IsLocalization.integerNormalization (nonZeroDivisors ℤ) a
  set B := IsLocalization.integerNormalization (nonZeroDivisors ℤ) b'
  rw [algebraMap_int_eq] at hA hB
  have hu0 : (u : ℤ) ≠ 0 := nonZeroDivisors.ne_zero hu
  have hv0 : (v : ℤ) ≠ 0 := nonZeroDivisors.ne_zero hv
  have key : C (v : ℤ) * A * p + C (u : ℤ) * B * q = C ((u : ℤ) * v) := by
    apply Polynomial.map_injective (Int.castRingHom ℚ) (RingHom.injective_int _)
    simp only [Polynomial.map_add, Polynomial.map_mul, map_C, hA, hB]
    have : C (((u : ℤ) : ℚ)) * C (((v : ℤ) : ℚ)) * (a * p.map (Int.castRingHom ℚ) +
        b' * q.map (Int.castRingHom ℚ)) = C ((Int.castRingHom ℚ) ((u : ℤ) * v)) := by
      rw [hab, mul_one, ← C_mul]; simp
    rw [← this]; simp only [eq_intCast, Polynomial.C_eq_intCast]; ring
  refine ⟨((u : ℤ) * v).natAbs, fun n => ?_⟩
  have e := congrArg (Polynomial.eval n) key
  simp only [eval_add, eval_mul, eval_C] at e
  have hdvd : ((Int.gcd (p.eval n) (q.eval n) : ℕ) : ℤ) ∣ (u : ℤ) * v := by
    rw [← e]
    exact dvd_add (dvd_mul_of_dvd_right (Int.gcd_dvd_left _ _) _)
      (dvd_mul_of_dvd_right (Int.gcd_dvd_right _ _) _)
  exact Nat.le_of_dvd (Int.natAbs_pos.mpr (mul_ne_zero hu0 hv0)) (Int.ofNat_dvd_left.mp hdvd)
