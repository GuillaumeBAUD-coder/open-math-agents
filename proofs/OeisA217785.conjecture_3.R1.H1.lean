import OMAReductions.R_OeisA217785_conjecture_3_R1

-- Credit: @jagong-cmu

open Polynomial

namespace OMA.A217785H1

/-- Closed form: (X - 1)^2 * s_n = (n+1) X^(n+2) - (n+2) X^(n+1) + 1. -/
lemma closed_form (n : ℕ) :
    (X - 1) ^ 2 * OeisA217785.polyS n =
      C ((n : ℤ) + 1) * X ^ (n + 2) - C ((n : ℤ) + 2) * X ^ (n + 1) + 1 := by
  induction n with
  | zero => simp [OeisA217785.polyS]; ring
  | succ n ih =>
    rw [OeisA217785.polyS, Finset.sum_range_succ, mul_add, ← OeisA217785.polyS, ih]
    simp only [map_add, map_natCast, map_one, map_ofNat, Nat.cast_add, Nat.cast_one]
    ring

/-- The shifted polynomial g = s_n(X + 1). -/
noncomputable abbrev g (n : ℕ) : ℤ[X] := taylor (1 : ℤ) (OeisA217785.polyS n)

lemma g_closed (n : ℕ) :
    g n * X ^ 2 =
      C ((n : ℤ) + 1) * (X + 1) ^ (n + 2) - C ((n : ℤ) + 2) * (X + 1) ^ (n + 1) + 1 := by
  have h := congrArg (taylor (1 : ℤ)) (closed_form n)
  simp only [taylor_mul, taylor_pow, map_sub, map_add, taylor_C, taylor_X,
    taylor_one, C_1, add_sub_cancel_right] at h
  rw [mul_comm]
  simp only [map_add, map_one]
  exact h

lemma g_coeff (n j : ℕ) :
    (g n).coeff j = ((n : ℤ) + 1) * ((n + 2).choose (j + 2) : ℤ)
      - ((n : ℤ) + 2) * ((n + 1).choose (j + 2) : ℤ) := by
  have h := congrArg (fun q => q.coeff (j + 2)) (g_closed n)
  simp only [coeff_mul_X_pow, coeff_add, coeff_sub, coeff_C_mul, coeff_X_add_one_pow,
    coeff_one] at h
  rw [h]
  simp

theorem h1 : ∀ n : ℕ, 1 ≤ n → (n + 2).Prime →
    Irreducible (Polynomial.map (Int.castRingHom ℚ) (OeisA217785.polyS n)) := by
  intro n hn hp
  have hcn : (g n).coeff n = (n : ℤ) + 1 := by
    rw [g_coeff]
    rw [Nat.choose_self, Nat.choose_eq_zero_of_lt (by omega)]
    simp
  have hhi : ∀ j, n < j → (g n).coeff j = 0 := by
    intro j hj
    rw [g_coeff, Nat.choose_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt (by omega)]
    simp
  have hdeg : (g n).natDegree = n := by
    apply natDegree_eq_of_le_of_coeff_ne_zero
    · rw [natDegree_le_iff_coeff_eq_zero]
      intro j hj
      exact hhi j (by exact_mod_cast hj)
    · rw [hcn]; omega
  have hlead : (g n).leadingCoeff = (n : ℤ) + 1 := by
    rw [leadingCoeff, hdeg, hcn]
  have hndvd : ¬ ((n : ℤ) + 2) ∣ ((n : ℤ) + 1) := by
    intro h
    have := Int.le_of_dvd (by omega) h
    omega
  -- primitivity of g
  have hprim : (g n).IsPrimitive := by
    intro r hr
    rw [C_dvd_iff_dvd_coeff] at hr
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have h1 := hr (m + 1)
    have h2 := hr m
    rw [hcn] at h1
    rw [g_coeff] at h2
    rw [show m + 1 + 2 = (m + 2) + 1 by ring, Nat.choose_succ_self_right,
      show m + 1 + 1 = m + 2 by ring, Nat.choose_self] at h2
    push_cast at h1 h2
    have h3 : r ∣ ((m : ℤ) + 2) * ((m : ℤ) + 2) := Dvd.dvd.mul_left h1 _
    have h4 : r ∣ 1 := by
      have := dvd_sub h3 h2
      ring_nf at this ⊢
      convert this using 1
    exact isUnit_of_dvd_one h4
  have hpZ : Prime ((n : ℤ) + 2) := by
    have := Nat.prime_iff_prime_int.mp hp
    exact_mod_cast this
  have hP : (Ideal.span {((n : ℤ) + 2)}).IsPrime :=
    (Ideal.span_singleton_prime hpZ.ne_zero).mpr hpZ
  have heis : (g n).IsEisensteinAt (Ideal.span {((n : ℤ) + 2)}) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hlead, Ideal.mem_span_singleton]
      exact hndvd
    · intro j hj
      rw [hdeg] at hj
      rw [Ideal.mem_span_singleton, g_coeff]
      apply dvd_sub
      · apply Dvd.dvd.mul_left
        have := hp.dvd_choose_self (k := j + 2) (by omega) (by omega)
        exact_mod_cast this
      · exact Dvd.dvd.mul_right (dvd_refl _) _
    · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, g_coeff]
      intro h
      have e1 := Nat.add_one_mul_choose_eq (n + 1) 1
      have e2 := Nat.add_one_mul_choose_eq n 1
      simp only [Nat.choose_one_right] at e1 e2
      have key : ((n : ℤ) + 2) ^ 2 ∣ ((n : ℤ) + 2) * ((n : ℤ) + 1) := by
        have : ((n : ℤ) + 2) * ((n : ℤ) + 1) =
            2 * (((n : ℤ) + 1) * ((n + 2).choose (0 + 2) : ℤ)
              - ((n : ℤ) + 2) * ((n + 1).choose (0 + 2) : ℤ)) := by
          have e1' : ((n + 1 + 1 : ℕ) : ℤ) * ((n + 1 : ℕ) : ℤ) =
              (((n + 1 + 1).choose (1 + 1) : ℕ) : ℤ) * ((1 + 1 : ℕ) : ℤ) := by
            exact_mod_cast e1
          have e2' : ((n + 1 : ℕ) : ℤ) * (n : ℤ) =
              (((n + 1).choose (1 + 1) : ℕ) : ℤ) * ((1 + 1 : ℕ) : ℤ) := by
            exact_mod_cast e2
          push_cast at e1' e2' ⊢
          linear_combination ((n : ℤ) + 1) * e1' - ((n : ℤ) + 2) * e2'
        rw [this]
        exact Dvd.dvd.mul_left h _
      rw [pow_two] at key
      have := (mul_dvd_mul_iff_left (show ((n : ℤ) + 2) ≠ 0 by omega)).mp key
      exact hndvd this
  have hgirr : Irreducible (g n) := heis.irreducible hP hprim (by omega)
  have hsirr : Irreducible (OeisA217785.polyS n) :=
    (MulEquiv.irreducible_iff (taylorEquiv (1 : ℤ)).toMulEquiv).mp (by exact hgirr)
  have hsprim : (OeisA217785.polyS n).IsPrimitive := by
    intro r hr
    apply hprim r
    have := map_dvd (taylorEquiv (1 : ℤ)) hr
    rw [show (taylorEquiv (1 : ℤ)) (C r) = C r from taylor_C _ _] at this
    exact this
  exact (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hsprim).mp hsirr

end OMA.A217785H1

theorem OMA.solution : OMA.R_OeisA217785_conjecture_3_R1.H1 := OMA.A217785H1.h1
