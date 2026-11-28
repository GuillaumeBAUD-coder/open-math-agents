import OMAStatements.S_oeis_a375948

open PowerSeries OMA.S_oeis_a375948

namespace OMA.P_oeis_a375948

private noncomputable def D (f : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => ((n + 1 : ℕ) : ℚ) * coeff (n + 1) f

private lemma coeff_D (f : PowerSeries ℚ) (n : ℕ) :
    coeff n (D f) = ((n + 1 : ℕ) : ℚ) * coeff (n + 1) f :=
  coeff_mk n _

private lemma D_add (f g : PowerSeries ℚ) : D (f + g) = D f + D g := by
  ext n; simp [coeff_D, mul_add]

private lemma D_sub (f g : PowerSeries ℚ) : D (f - g) = D f - D g := by
  ext n; simp [coeff_D, mul_sub]

private lemma D_const (c : ℚ) : D (C c) = 0 := by
  ext n; simp [coeff_D]

private lemma D_one : D (1 : PowerSeries ℚ) = 0 := by
  ext n; simp [coeff_D, coeff_one]

private lemma D_C_mul (c : ℚ) (f : PowerSeries ℚ) : D (C c * f) = C c * D f := by
  ext n; simp [coeff_D]; ring

private lemma D_mul (f g : PowerSeries ℚ) : D (f * g) = D f * g + f * D g := by
  ext n
  rw [coeff_D, map_add, coeff_mul, coeff_mul, coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i f * coeff j g)]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i (D f) * coeff j g)]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i f * coeff j (D g))]
  have hsplit :
      ((n + 1 : ℕ) : ℚ) * ∑ k ∈ Finset.range (n + 2), coeff k f * coeff (n + 1 - k) g =
      (∑ k ∈ Finset.range (n + 2), (k : ℚ) * coeff k f * coeff (n + 1 - k) g) +
      (∑ k ∈ Finset.range (n + 2), coeff k f * (((n + 1 - k : ℕ) : ℚ) * coeff (n + 1 - k) g)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ n + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hadd : (k : ℚ) + ((n + 1 - k : ℕ) : ℚ) = ((n + 1 : ℕ) : ℚ) := by
      exact_mod_cast Nat.add_sub_of_le hk'
    calc
      ((n + 1 : ℕ) : ℚ) * (coeff k f * coeff (n + 1 - k) g)
          = ((k : ℚ) + ((n + 1 - k : ℕ) : ℚ)) * (coeff k f * coeff (n + 1 - k) g) := by
              rw [hadd]
      _ = (k : ℚ) * coeff k f * coeff (n + 1 - k) g +
          coeff k f * (((n + 1 - k : ℕ) : ℚ) * coeff (n + 1 - k) g) := by ring
  rw [hsplit]
  congr 1
  · rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, add_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [coeff_D, Nat.succ_sub_succ]
  · rw [Finset.sum_range_succ]
    simp only [Nat.sub_self, Nat.cast_zero, zero_mul, mul_zero, add_zero]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hsub : n + 1 - k = (n - k) + 1 := by omega
    rw [hsub, coeff_D]

private lemma coeff_exp_rat (n : ℕ) : coeff n (PowerSeries.exp ℚ) = 1 / (n.factorial : ℚ) := by
  rw [coeff_exp]
  rfl

private lemma D_exp : D (PowerSeries.exp ℚ) = PowerSeries.exp ℚ := by
  ext n
  rw [coeff_D, coeff_exp_rat, coeff_exp_rat]
  simp only [Nat.factorial_succ, Nat.cast_mul]
  field_simp

private lemma coeff_exp_mul (f : PowerSeries ℚ) (n : ℕ) :
    (n.factorial : ℚ) * coeff n (PowerSeries.exp ℚ * f) =
      ∑ j ∈ Finset.range (n + 1),
        (n.choose j : ℚ) * ((j.factorial : ℚ) * coeff j f) := by
  rw [mul_comm (PowerSeries.exp ℚ) f, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun j i => coeff j f * coeff i (PowerSeries.exp ℚ)),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [coeff_exp_rat]
  have hchQ : (n.choose j : ℚ) * (j.factorial : ℚ) * ((n - j).factorial : ℚ) = (n.factorial : ℚ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hj'
  have hfac1 : ((n - j).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  calc
    (n.factorial : ℚ) * (coeff j f * (1 / ((n - j).factorial : ℚ)))
        = ((n.choose j : ℚ) * (j.factorial : ℚ) * ((n - j).factorial : ℚ)) *
          (coeff j f * (1 / ((n - j).factorial : ℚ))) := by rw [hchQ]
    _ = (n.choose j : ℚ) * ((j.factorial : ℚ) * coeff j f) := by
          field_simp

end OMA.P_oeis_a375948

open OMA.P_oeis_a375948 in
theorem OMA.solution : type_of% @OMA.S_oeis_a375948.main := by
  intro a b ⟨ha0, hGeq⟩ hb0 hbrec
  set G : PowerSeries ℚ := PowerSeries.mk fun n => a n / (n.factorial : ℚ)
  set E : PowerSeries ℚ := PowerSeries.exp ℚ
  set U : PowerSeries ℚ := 3 - 2 * E
  have hC2 : (2 : PowerSeries ℚ) = C (2 : ℚ) := (map_ofNat C 2).symm
  have hC3 : (3 : PowerSeries ℚ) = C (3 : ℚ) := (map_ofNat C 3).symm
  have hcoeffG : ∀ k : ℕ, (k.factorial : ℚ) * coeff k G = a k := by
    intro k
    have hfac : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    simp [G, coeff_mk, mul_div_cancel₀ _ hfac]
  have hcoeffDG : ∀ k : ℕ, (k.factorial : ℚ) * coeff k (D G) = a (k + 1) := by
    intro k
    rw [coeff_D]
    have h1 : (k.factorial : ℚ) * (((k + 1 : ℕ) : ℚ) * coeff (k + 1) G) =
        (((k + 1).factorial : ℚ) * coeff (k + 1) G) := by
      rw [Nat.factorial_succ, Nat.cast_mul]; ring
    rw [h1, hcoeffG]
  have hDU : D U = -2 * E := by
    change D (3 - 2 * E) = -2 * E
    rw [D_sub, hC3, D_const, hC2, D_C_mul, D_exp]
    rw [← hC2]; ring
  have hD_eq : D (G ^ 2 * U ^ 3) = 0 := by
    rw [hGeq, D_one]
  have hDG_sq : D (G ^ 2) = 2 * G * D G := by
    rw [sq, D_mul]; ring
  have hDU_cu : D (U ^ 3) = 3 * U ^ 2 * D U := by
    have hpow : U ^ 3 = U * (U * U) := by ring
    rw [hpow, D_mul, D_mul]; ring
  have hdiff : 2 * G * U ^ 2 * (U * D G - 3 * E * G) = 0 := by
    have h := hD_eq
    rw [D_mul, hDG_sq, hDU_cu, hDU] at h
    calc
      2 * G * U ^ 2 * (U * D G - 3 * E * G)
          = 2 * G * D G * U ^ 3 + G ^ 2 * (3 * U ^ 2 * (-2 * E)) := by ring
      _ = 0 := h
  have hG_ne : G ≠ 0 := by
    intro h0
    have h1 := congr_arg (coeff 0) h0
    simp [G, coeff_mk, ha0] at h1
  have hU_ne : U ≠ 0 := by
    intro h0
    have h1 := congr_arg (coeff 0) h0
    have hE0 : coeff 0 E = 1 := by simp [E, coeff_exp]
    have hU0 : coeff 0 U = 3 - 2 * coeff 0 E := by
      change coeff 0 ((3 : PowerSeries ℚ) - (2 : PowerSeries ℚ) * E) = _
      rw [hC3, hC2, map_sub, coeff_zero_C, coeff_C_mul]
    rw [hU0, hE0] at h1
    norm_num at h1
  have h2GU2_ne : (2 : PowerSeries ℚ) * G * U ^ 2 ≠ 0 := by
    have h2ne : (2 : PowerSeries ℚ) ≠ 0 := by
      intro h0
      have h1 := congr_arg (coeff 0) h0
      rw [hC2, coeff_zero_C] at h1
      norm_num at h1
    exact mul_ne_zero (mul_ne_zero h2ne hG_ne) (pow_ne_zero 2 hU_ne)
  have hODE : U * D G = 3 * E * G := by
    rcases mul_eq_zero.mp hdiff with h | h
    · exact absurd h h2GU2_ne
    · exact sub_eq_zero.mp h
  set F : PowerSeries ℚ := U * G
  set H : PowerSeries ℚ := E * G
  have hDF : D F = H := by
    change D (U * G) = E * G
    rw [D_mul, hDU, hODE]
    ring
  have hDH : D H = H + E * D G := by
    change D (E * G) = E * G + E * D G
    rw [D_mul, D_exp]
  have hb_eq : ∀ k : ℕ, b k = (k.factorial : ℚ) * coeff k H := by
    intro k
    induction k with
    | zero =>
      have hE0 : coeff 0 E = 1 := by simp [E, coeff_exp]
      rw [hb0]
      have hH0 : coeff 0 H = coeff 0 E * coeff 0 G := by
        change coeff 0 (E * G) = _
        rw [coeff_mul, Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
      rw [hH0, hE0]
      simp [G, coeff_mk, ha0]
    | succ m ih =>
      rw [hbrec (m + 1) (Nat.succ_pos m)]
      simp only [Nat.add_sub_cancel]
      rw [ih]
      have hstep := congr_arg (fun P => (m.factorial : ℚ) * coeff m P) hDH
      rw [coeff_D, map_add, mul_add] at hstep
      have hlhs : (m.factorial : ℚ) * (((m + 1 : ℕ) : ℚ) * coeff (m + 1) H) =
          ((m + 1).factorial : ℚ) * coeff (m + 1) H := by
        rw [Nat.factorial_succ, Nat.cast_mul]; ring
      rw [hlhs, coeff_exp_mul (D G) m] at hstep
      have hsum :
          ∑ j ∈ Finset.range (m + 1), (m.choose j : ℚ) * ((j.factorial : ℚ) * coeff j (D G)) =
          ∑ j ∈ Finset.range (m + 1), (m.choose j : ℚ) * a (j + 1) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hcoeffDG]
      rw [hsum] at hstep
      exact hstep.symm
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)
  have hstep := congr_arg (fun P => (m.factorial : ℚ) * coeff m P) hDF
  rw [coeff_D] at hstep
  have hlhs : (m.factorial : ℚ) * (((m + 1 : ℕ) : ℚ) * coeff (m + 1) F) =
      ((m + 1).factorial : ℚ) * coeff (m + 1) F := by
    rw [Nat.factorial_succ, Nat.cast_mul]; ring
  rw [hlhs, ← hb_eq m] at hstep
  have hF_coeff : ((m + 1).factorial : ℚ) * coeff (m + 1) F =
      3 * a (m + 1) - 2 * ∑ j ∈ Finset.range (m + 2), ((m + 1).choose j : ℚ) * a j := by
    have hFdef : F = C (3 : ℚ) * G - C (2 : ℚ) * (E * G) := by
      change (3 - 2 * E) * G = _
      rw [← hC3, ← hC2]; ring
    rw [hFdef, map_sub, coeff_C_mul, coeff_C_mul, mul_sub]
    have h1 : ((m + 1).factorial : ℚ) * (3 * coeff (m + 1) G) = 3 * a (m + 1) := by
      calc
        ((m + 1).factorial : ℚ) * (3 * coeff (m + 1) G)
            = 3 * (((m + 1).factorial : ℚ) * coeff (m + 1) G) := by ring
        _ = 3 * a (m + 1) := by rw [hcoeffG]
    have h2 : ((m + 1).factorial : ℚ) * (2 * coeff (m + 1) (E * G)) =
        2 * ∑ j ∈ Finset.range (m + 2), ((m + 1).choose j : ℚ) * a j := by
      calc
        ((m + 1).factorial : ℚ) * (2 * coeff (m + 1) (E * G))
            = 2 * (((m + 1).factorial : ℚ) * coeff (m + 1) (E * G)) := by ring
        _ = 2 * ∑ j ∈ Finset.range (m + 2),
              ((m + 1).choose j : ℚ) * ((j.factorial : ℚ) * coeff j G) := by
              rw [coeff_exp_mul]
        _ = 2 * ∑ j ∈ Finset.range (m + 2), ((m + 1).choose j : ℚ) * a j := by
              congr 1
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [hcoeffG]
    rw [h1, h2]
  rw [hF_coeff, Finset.sum_range_succ, Nat.choose_self, Nat.cast_one, one_mul] at hstep
  change a (m + 1) = b ((m + 1) - 1) + 2 * ∑ j ∈ Finset.range (m + 1), ((m + 1).choose j : ℚ) * a j
  rw [Nat.add_sub_cancel]
  linarith
