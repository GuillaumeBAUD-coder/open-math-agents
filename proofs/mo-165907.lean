import OMAStatements.S_mo_165907

open scoped BigOperators

private lemma sum_Icc_sub (G : ℕ → ℝ) (N : ℕ) :
    ∑ j ∈ Finset.Icc 1 N, (G j - G (j + 1)) = G 1 - G (N + 1) := by
  induction N with
  | zero => simp
  | succ n ih =>
    have hsplit : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnot : n + 1 ∉ Finset.Icc 1 n := by
      simp only [Finset.mem_Icc]
      omega
    rw [hsplit, Finset.sum_insert hnot, ih]
    ring

private lemma sum_Icc_sub_pred (G : ℕ → ℝ) (N : ℕ) :
    ∑ j ∈ Finset.Icc 1 N, (G j - G (j - 1)) = G N - G 0 := by
  induction N with
  | zero => simp
  | succ n ih =>
    have hsplit : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnot : n + 1 ∉ Finset.Icc 1 n := by
      simp only [Finset.mem_Icc]
      omega
    rw [hsplit, Finset.sum_insert hnot, ih, Nat.add_sub_cancel]
    ring

private lemma sum_Icc_swap (N : ℕ) (f : ℕ → ℕ → ℝ) :
    ∑ j ∈ Finset.Icc 1 N, ∑ i ∈ Finset.Icc j N, f i j =
      ∑ i ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 i, f i j := by
  have hL : ∑ j ∈ Finset.Icc 1 N, ∑ i ∈ Finset.Icc j N, f i j =
      ∑ j ∈ Finset.Icc 1 N, ∑ i ∈ Finset.Icc 1 N, if j ≤ i then f i j else 0 := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← Finset.sum_filter]
    congr 1
    ext i
    simp only [Finset.mem_Icc, Finset.mem_filter]
    have hj1 := (Finset.mem_Icc.mp hj).1
    omega
  have hR : ∑ i ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 i, f i j =
      ∑ i ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N, if j ≤ i then f i j else 0 := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp only [Finset.mem_Icc, Finset.mem_filter]
    have hi2 := (Finset.mem_Icc.mp hi).2
    omega
  rw [hL, hR, Finset.sum_comm]

private lemma sum_Icc_swap_strict (j N : ℕ) (_hj : 1 ≤ j) (g : ℕ → ℕ → ℝ) :
    ∑ i ∈ Finset.Icc j N, ∑ k ∈ Finset.Icc (j + 1) i, g i k =
      ∑ k ∈ Finset.Icc (j + 1) N, ∑ i ∈ Finset.Icc k N, g i k := by
  have hL : ∑ i ∈ Finset.Icc j N, ∑ k ∈ Finset.Icc (j + 1) i, g i k =
      ∑ i ∈ Finset.Icc j N, ∑ k ∈ Finset.Icc (j + 1) N, if k ≤ i then g i k else 0 := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← Finset.sum_filter]
    congr 1
    ext k
    simp only [Finset.mem_Icc, Finset.mem_filter]
    have hi2 := (Finset.mem_Icc.mp hi).2
    omega
  have hR : ∑ k ∈ Finset.Icc (j + 1) N, ∑ i ∈ Finset.Icc k N, g i k =
      ∑ k ∈ Finset.Icc (j + 1) N, ∑ i ∈ Finset.Icc j N, if k ≤ i then g i k else 0 := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [← Finset.sum_filter]
    congr 1
    ext i
    simp only [Finset.mem_Icc, Finset.mem_filter]
    have hk1 := (Finset.mem_Icc.mp hk).1
    omega
  rw [hL, hR, Finset.sum_comm]

private lemma young_ineq_nonneg {a b p q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hp : 1 < p) (hq : 1 < q) (hpq : 1 / p + 1 / q = 1) :
    a * b ≤ a ^ p / p + b ^ q / q := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  rcases eq_or_lt_of_le ha with rfl | ha_pos
  · rw [zero_mul, Real.zero_rpow hp0.ne', zero_div, zero_add]
    exact div_nonneg (Real.rpow_nonneg hb q) hq0.le
  rcases eq_or_lt_of_le hb with rfl | hb_pos
  · rw [mul_zero, Real.zero_rpow hq0.ne', zero_div, add_zero]
    exact div_nonneg (Real.rpow_nonneg ha_pos.le p) hp0.le
  set s := a ^ p
  set t := b ^ q
  have hs : 0 < s := Real.rpow_pos_of_pos ha_pos p
  have ht : 0 < t := Real.rpow_pos_of_pos hb_pos q
  set m := s / p + t / q
  have hm : 0 < m := add_pos (div_pos hs hp0) (div_pos ht hq0)
  have hlog1 : Real.log (s / m) ≤ s / m - 1 := Real.log_le_sub_one_of_pos (div_pos hs hm)
  have hlog2 : Real.log (t / m) ≤ t / m - 1 := Real.log_le_sub_one_of_pos (div_pos ht hm)
  have hcomb : 1 / p * Real.log (s / m) + 1 / q * Real.log (t / m) ≤ 0 := by
    have h1 := mul_le_mul_of_nonneg_left hlog1 (div_nonneg zero_le_one hp0.le)
    have h2 := mul_le_mul_of_nonneg_left hlog2 (div_nonneg zero_le_one hq0.le)
    have hsum : 1 / p * (s / m - 1) + 1 / q * (t / m - 1) = 0 := by
      have hm_eq : s / p + t / q = m := rfl
      calc
        1 / p * (s / m - 1) + 1 / q * (t / m - 1)
            = (s / p + t / q) / m - (1 / p + 1 / q) := by ring
        _ = m / m - 1 := by rw [hm_eq, hpq]
        _ = 0 := by rw [div_self hm.ne', sub_self]
    linarith
  have hexp := Real.exp_le_exp.mpr hcomb
  rw [Real.exp_zero, Real.exp_add] at hexp
  have ha_eq : (s / m) ^ (1 / p) = a / m ^ (1 / p) := by
    rw [Real.div_rpow hs.le hm.le, ← Real.rpow_mul ha_pos.le]
    have hpp : p * (1 / p) = 1 := mul_one_div_cancel hp0.ne'
    rw [hpp, Real.rpow_one]
  have hb_eq : (t / m) ^ (1 / q) = b / m ^ (1 / q) := by
    rw [Real.div_rpow ht.le hm.le, ← Real.rpow_mul hb_pos.le]
    have hqq : q * (1 / q) = 1 := mul_one_div_cancel hq0.ne'
    rw [hqq, Real.rpow_one]
  have hexp1 : Real.exp (1 / p * Real.log (s / m)) = a / m ^ (1 / p) := by
    rw [← ha_eq, Real.rpow_def_of_pos (div_pos hs hm), mul_comm]
  have hexp2 : Real.exp (1 / q * Real.log (t / m)) = b / m ^ (1 / q) := by
    rw [← hb_eq, Real.rpow_def_of_pos (div_pos ht hm), mul_comm]
  rw [hexp1, hexp2] at hexp
  have hm_prod : m ^ (1 / p) * m ^ (1 / q) = m := by
    rw [← Real.rpow_add hm, hpq, Real.rpow_one]
  have hmul_pos : 0 < m ^ (1 / p) * m ^ (1 / q) :=
    mul_pos (Real.rpow_pos_of_pos hm _) (Real.rpow_pos_of_pos hm _)
  have hfinal := mul_le_mul_of_nonneg_right hexp hmul_pos.le
  rw [one_mul] at hfinal
  calc
    a * b = (a / m ^ (1 / p)) * (b / m ^ (1 / q)) * (m ^ (1 / p) * m ^ (1 / q)) := by
      have hp_ne : m ^ (1 / p) ≠ 0 := (Real.rpow_pos_of_pos hm _).ne'
      have hq_ne : m ^ (1 / q) ≠ 0 := (Real.rpow_pos_of_pos hm _).ne'
      field_simp [hp_ne, hq_ne]
    _ ≤ m ^ (1 / p) * m ^ (1 / q) := hfinal
    _ = m := hm_prod

private lemma rpow_sub_rpow_le {p a b : ℝ} (hp : 1 < p) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ p - b ^ p ≤ p * a ^ (p - 1) * (a - b) := by
  set q := p / (p - 1)
  have hp1 : 0 < p - 1 := sub_pos.mpr hp
  have hp0 : 0 < p := by linarith
  have hq : 1 < q := by
    rw [lt_div_iff₀ hp1]
    linarith
  have hpq : 1 / p + 1 / q = 1 := by
    dsimp [q]
    field_simp [hp0.ne', hp1.ne']
    ring
  have hy := young_ineq_nonneg (Real.rpow_nonneg ha (p - 1)) hb hq hp (by linarith)
  have hsub_mul : (p - 1) * q = p := by
    dsimp [q]
    field_simp [hp1.ne']
  have hmul : (a ^ (p - 1)) ^ q = a ^ p := by
    rw [← Real.rpow_mul ha, hsub_mul]
  have hp_mul : p * (a ^ (p - 1) * b) ≤ p * (a ^ p / q + b ^ p / p) := by
    rw [← hmul]
    exact mul_le_mul_of_nonneg_left hy hp0.le
  have h1 : p * (a ^ p / q + b ^ p / p) = (p - 1) * a ^ p + b ^ p := by
    dsimp [q]
    field_simp [hp0.ne', hp1.ne']
  have h2 : a ^ (p - 1) * a = a ^ p := by
    rcases eq_or_lt_of_le ha with rfl | ha_pos
    · rw [Real.zero_rpow hp1.ne', zero_mul, Real.zero_rpow hp0.ne']
    · conv_lhs => rhs; rw [← Real.rpow_one a]
      rw [← Real.rpow_add ha_pos, sub_add_cancel]
  nlinarith

private lemma hardy_reduction {p c : ℝ} (hp : 1 < p) (hc : 0 < c) {s : Finset ℕ}
    {S A : ℕ → ℝ} (hS : ∀ j ∈ s, 0 ≤ S j) (hA : ∀ j ∈ s, 0 ≤ A j)
    (hineq : c * ∑ j ∈ s, S j ^ p ≤ p * ∑ j ∈ s, S j ^ (p - 1) * A j) :
    ∑ j ∈ s, S j ^ p ≤ (p / c) ^ p * ∑ j ∈ s, A j ^ p := by
  set q := p / (p - 1)
  have hp1 : 0 < p - 1 := sub_pos.mpr hp
  have hp0 : 0 < p := by linarith
  have hq : 1 < q := by
    rw [lt_div_iff₀ hp1]
    linarith
  have hpq : 1 / q + 1 / p = 1 := by
    dsimp [q]
    field_simp [hp0.ne', hp1.ne']
    ring
  have hsub_mul : (p - 1) * q = p := by
    dsimp [q]
    field_simp [hp1.ne']
  have hq_inv : q⁻¹ = (p - 1) / p := by
    dsimp [q]
    rw [inv_div]
  have hterm : ∀ j ∈ s, p * (S j ^ (p - 1) * A j) ≤
      c * ((p - 1) / p * S j ^ p) + (c / p) * ((p / c) ^ p * A j ^ p) := by
    intro j hj
    have hy := young_ineq_nonneg
      (Real.rpow_nonneg (hS j hj) (p - 1))
      (mul_nonneg (div_nonneg hp0.le hc.le) (hA j hj))
      hq hp hpq
    have hpowS : (S j ^ (p - 1)) ^ q = S j ^ p := by
      rw [← Real.rpow_mul (hS j hj), hsub_mul]
    have hpowA : ((p / c) * A j) ^ p = (p / c) ^ p * A j ^ p :=
      Real.mul_rpow (div_nonneg hp0.le hc.le) (hA j hj)
    rw [hpowS, hpowA] at hy
    have hyc : c * (S j ^ (p - 1) * (p / c * A j)) ≤
        c * (S j ^ p / q + (p / c) ^ p * A j ^ p / p) :=
      mul_le_mul_of_nonneg_left hy hc.le
    have hlhs : c * (S j ^ (p - 1) * (p / c * A j)) = p * (S j ^ (p - 1) * A j) := by
      field_simp [hc.ne']
    have hrhs : c * (S j ^ p / q + (p / c) ^ p * A j ^ p / p) =
        c * ((p - 1) / p * S j ^ p) + (c / p) * ((p / c) ^ p * A j ^ p) := by
      rw [div_eq_mul_inv, hq_inv, mul_add]
      ring
    linarith
  have hsum : p * ∑ j ∈ s, S j ^ (p - 1) * A j ≤
      c * ((p - 1) / p * ∑ j ∈ s, S j ^ p) + (c / p) * ((p / c) ^ p * ∑ j ∈ s, A j ^ p) := by
    rw [Finset.mul_sum]
    calc
      ∑ j ∈ s, p * (S j ^ (p - 1) * A j)
          ≤ ∑ j ∈ s, (c * ((p - 1) / p * S j ^ p) + (c / p) * ((p / c) ^ p * A j ^ p)) :=
            Finset.sum_le_sum hterm
      _ = ∑ j ∈ s, c * ((p - 1) / p * S j ^ p) + ∑ j ∈ s, (c / p) * ((p / c) ^ p * A j ^ p) :=
            Finset.sum_add_distrib
      _ = c * ((p - 1) / p * ∑ j ∈ s, S j ^ p) + (c / p) * ((p / c) ^ p * ∑ j ∈ s, A j ^ p) := by
            simp only [← Finset.mul_sum]
  have hcomb : (c / p) * ∑ j ∈ s, S j ^ p ≤ (c / p) * ((p / c) ^ p * ∑ j ∈ s, A j ^ p) := by
    have h1 : c * ∑ j ∈ s, S j ^ p - c * ((p - 1) / p * ∑ j ∈ s, S j ^ p) =
        (c / p) * ∑ j ∈ s, S j ^ p := by
      field_simp [hp0.ne']
      ring
    linarith
  exact le_of_mul_le_mul_left hcomb (div_pos hc hp0)

private lemma dual_hardy_ineq {p : ℝ} (hp : 1 < p) (N : ℕ) {A : ℕ → ℝ}
    (hA : ∀ k ∈ Finset.Icc 1 N, 0 ≤ A k) :
    ∑ j ∈ Finset.Icc 1 N, (∑ k ∈ Finset.Icc j N, A k / (k : ℝ)) ^ p ≤
      p ^ p * ∑ k ∈ Finset.Icc 1 N, A k ^ p := by
  let R : ℕ → ℝ := fun j => ∑ k ∈ Finset.Icc j N, A k / (k : ℝ)
  have hR_nonneg : ∀ j ∈ Finset.Icc 1 (N + 1), 0 ≤ R j := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    apply Finset.sum_nonneg
    intro k hk
    rw [Finset.mem_Icc] at hk
    exact div_nonneg (hA k (Finset.mem_Icc.mpr ⟨le_trans hj1 hk.1, hk.2⟩)) (Nat.cast_nonneg k)
  have hR_end : R (N + 1) = 0 := by
    simp [R]
  have hstep : ∀ j ∈ Finset.Icc 1 N,
      (j : ℝ) * (R j ^ p - R (j + 1) ^ p) ≤ p * (R j ^ (p - 1) * A j) := by
    intro j hj
    have hj_mem := Finset.mem_Icc.mp hj
    have hj_pos : (0 : ℝ) < j := Nat.cast_pos.mpr (by omega)
    have hRj : 0 ≤ R j := hR_nonneg j (Finset.mem_Icc.mpr ⟨hj_mem.1, by omega⟩)
    have hRj1 : 0 ≤ R (j + 1) := hR_nonneg (j + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    have hdiff : R j - R (j + 1) = A j / (j : ℝ) := by
      have hinsert : Finset.Icc j N = insert j (Finset.Icc (j + 1) N) := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnot : j ∉ Finset.Icc (j + 1) N := by
        simp only [Finset.mem_Icc]
        omega
      simp only [R, hinsert, Finset.sum_insert hnot]
      ring
    have hle := rpow_sub_rpow_le hp hRj hRj1
    rw [hdiff] at hle
    calc
      (j : ℝ) * (R j ^ p - R (j + 1) ^ p)
          ≤ (j : ℝ) * (p * R j ^ (p - 1) * (A j / (j : ℝ))) :=
            mul_le_mul_of_nonneg_left hle hj_pos.le
      _ = p * (R j ^ (p - 1) * A j) := by
            field_simp [hj_pos.ne']
  have hsum_parts : ∑ j ∈ Finset.Icc 1 N, (j : ℝ) * (R j ^ p - R (j + 1) ^ p) =
      ∑ j ∈ Finset.Icc 1 N, R j ^ p := by
    let G : ℕ → ℝ := fun j => ((j - 1 : ℕ) : ℝ) * R j ^ p
    have htelescope : ∑ j ∈ Finset.Icc 1 N, (G j - G (j + 1)) = 0 := by
      rw [sum_Icc_sub G N]
      have hp0 : p ≠ 0 := by linarith
      simp [G, hR_end, Real.zero_rpow hp0]
    have hrewrite : ∀ j ∈ Finset.Icc 1 N,
        (j : ℝ) * (R j ^ p - R (j + 1) ^ p) = (G j - G (j + 1)) + R j ^ p := by
      intro j hj
      have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
      simp only [G, Nat.add_sub_cancel]
      rw [Nat.cast_sub hj1, Nat.cast_one]
      ring
    rw [Finset.sum_congr rfl hrewrite, Finset.sum_add_distrib, htelescope, zero_add]
  have hineq : 1 * ∑ j ∈ Finset.Icc 1 N, R j ^ p ≤
      p * ∑ j ∈ Finset.Icc 1 N, R j ^ (p - 1) * A j := by
    rw [one_mul, ← hsum_parts, Finset.mul_sum]
    exact Finset.sum_le_sum hstep
  have hres := hardy_reduction hp zero_lt_one
    (fun j hj => hR_nonneg j (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hj).1, Nat.le_succ_of_le (Finset.mem_Icc.mp hj).2⟩))
    hA hineq
  simpa [div_one] using hres

private lemma hardy_ineq {p : ℝ} (hp : 1 < p) (N : ℕ) {A : ℕ → ℝ}
    (hA : ∀ k ∈ Finset.Icc 1 N, 0 ≤ A k) :
    ∑ j ∈ Finset.Icc 1 N, ((∑ k ∈ Finset.Icc 1 j, A k) / (j : ℝ)) ^ p ≤
      (p / (p - 1)) ^ p * ∑ k ∈ Finset.Icc 1 N, A k ^ p := by
  let S : ℕ → ℝ := fun j => if j = 0 then 0 else (∑ k ∈ Finset.Icc 1 j, A k) / (j : ℝ)
  have hS_nonneg : ∀ j ∈ Finset.Icc 0 N, 0 ≤ S j := by
    intro j hj
    rcases eq_or_ne j 0 with rfl | hj0
    · simp [S]
    · simp only [S, hj0, ↓reduceIte]
      refine div_nonneg (Finset.sum_nonneg fun k hk => ?_) (Nat.cast_nonneg j)
      have hjN := (Finset.mem_Icc.mp hj).2
      have hk_mem := Finset.mem_Icc.mp hk
      exact hA k (Finset.mem_Icc.mpr ⟨hk_mem.1, le_trans hk_mem.2 hjN⟩)
  have hstep : ∀ j ∈ Finset.Icc 1 N,
      (p - 1) * S j ^ p + ((j : ℝ) * S j ^ p - ((j - 1 : ℕ) : ℝ) * S (j - 1) ^ p) ≤
        p * (S j ^ (p - 1) * A j) := by
    intro j hj
    have hj_mem := Finset.mem_Icc.mp hj
    have hj1 : 1 ≤ j := hj_mem.1
    have hj0 : j ≠ 0 := by omega
    have hSj : 0 ≤ S j := hS_nonneg j (Finset.mem_Icc.mpr ⟨by omega, hj_mem.2⟩)
    have hSj1 : 0 ≤ S (j - 1) := hS_nonneg (j - 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    have hle := rpow_sub_rpow_le hp hSj hSj1
    have hmul : ((j - 1 : ℕ) : ℝ) * (S j ^ p - S (j - 1) ^ p) ≤
        ((j - 1 : ℕ) : ℝ) * (p * S j ^ (p - 1) * (S j - S (j - 1))) :=
      mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg (j - 1))
    have hlin : ((j - 1 : ℕ) : ℝ) * (S j - S (j - 1)) = A j - S j := by
      have hj_pos : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hj0
      have hsum_j : (j : ℝ) * S j = ∑ k ∈ Finset.Icc 1 j, A k := by
        simp only [S, hj0, ↓reduceIte]
        field_simp [hj_pos]
      have hsum_pred : ((j - 1 : ℕ) : ℝ) * S (j - 1) = ∑ k ∈ Finset.Icc 1 (j - 1), A k := by
        rcases eq_or_lt_of_le hj1 with rfl | hj2
        · simp [S]
        · have hj1_ne : j - 1 ≠ 0 := by omega
          have hj1_pos : ((j - 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hj1_ne
          simp only [S, hj1_ne, ↓reduceIte]
          field_simp [hj1_pos]
      have hsplit : Finset.Icc 1 j = insert j (Finset.Icc 1 (j - 1)) := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnot : j ∉ Finset.Icc 1 (j - 1) := by
        simp only [Finset.mem_Icc]
        omega
      have hdiff_sum : (j : ℝ) * S j - ((j - 1 : ℕ) : ℝ) * S (j - 1) = A j := by
        rw [hsum_j, hsum_pred, hsplit, Finset.sum_insert hnot]
        ring
      rw [Nat.cast_sub hj1, Nat.cast_one] at hdiff_sum ⊢
      linarith
    have hrpow : S j ^ (p - 1) * S j = S j ^ p := by
      rcases eq_or_lt_of_le hSj with h0 | hpos
      · have hp1 : p - 1 ≠ 0 := by linarith
        have hp0 : p ≠ 0 := by linarith
        rw [← h0, Real.zero_rpow hp1, zero_mul, Real.zero_rpow hp0]
      · conv_lhs => rhs; rw [← Real.rpow_one (S j)]
        rw [← Real.rpow_add hpos, sub_add_cancel]
    have hrhs_eq : ((j - 1 : ℕ) : ℝ) * (p * S j ^ (p - 1) * (S j - S (j - 1))) =
        p * (S j ^ (p - 1) * A j) - p * S j ^ p := by
      calc
        ((j - 1 : ℕ) : ℝ) * (p * S j ^ (p - 1) * (S j - S (j - 1)))
            = p * S j ^ (p - 1) * (((j - 1 : ℕ) : ℝ) * (S j - S (j - 1))) := by ring
        _ = p * S j ^ (p - 1) * (A j - S j) := by rw [hlin]
        _ = p * (S j ^ (p - 1) * A j) - p * (S j ^ (p - 1) * S j) := by ring
        _ = p * (S j ^ (p - 1) * A j) - p * S j ^ p := by rw [hrpow]
    have hlhs_eq : ((j - 1 : ℕ) : ℝ) * (S j ^ p - S (j - 1) ^ p) =
        ((j : ℝ) * S j ^ p - ((j - 1 : ℕ) : ℝ) * S (j - 1) ^ p) - S j ^ p := by
      rw [Nat.cast_sub hj1, Nat.cast_one]
      ring
    linarith
  have htelescope_nonneg : 0 ≤ ∑ j ∈ Finset.Icc 1 N,
      ((j : ℝ) * S j ^ p - ((j - 1 : ℕ) : ℝ) * S (j - 1) ^ p) := by
    let G : ℕ → ℝ := fun j => (j : ℝ) * S j ^ p
    have heq : ∑ j ∈ Finset.Icc 1 N, (G j - G (j - 1)) = G N - G 0 := sum_Icc_sub_pred G N
    change 0 ≤ ∑ j ∈ Finset.Icc 1 N, (G j - G (j - 1))
    rw [heq]
    have hG0 : G 0 = 0 := by simp [G]
    rw [hG0, sub_zero]
    exact mul_nonneg (Nat.cast_nonneg N)
      (Real.rpow_nonneg (hS_nonneg N (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)) p)
  have hineq : (p - 1) * ∑ j ∈ Finset.Icc 1 N, S j ^ p ≤
      p * ∑ j ∈ Finset.Icc 1 N, S j ^ (p - 1) * A j := by
    have hsum := Finset.sum_le_sum hstep
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
    linarith
  have hres := hardy_reduction hp (sub_pos.mpr hp)
    (fun j hj => hS_nonneg j (Finset.mem_Icc.mpr ⟨by omega, (Finset.mem_Icc.mp hj).2⟩))
    hA hineq
  have hcongr : ∑ j ∈ Finset.Icc 1 N, S j ^ p =
      ∑ j ∈ Finset.Icc 1 N, ((∑ k ∈ Finset.Icc 1 j, A k) / (j : ℝ)) ^ p := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj0 : j ≠ 0 := by
      have := (Finset.mem_Icc.mp hj).1
      omega
    simp [S, hj0]
  rwa [← hcongr]

theorem OMA.solution : type_of% @OMA.S_mo_165907.main := by
  intro p hp
  rcases eq_or_lt_of_le hp with rfl | hp_gt
  · refine ⟨1, zero_lt_one, fun N u => ?_⟩
    rw [one_mul]
    calc
      ∑ j ∈ Finset.Icc 1 N, |∑ i ∈ Finset.Icc j N, (∑ k ∈ Finset.Icc 1 i, u i k) / (i : ℝ)| ^ (1 : ℝ)
          = ∑ j ∈ Finset.Icc 1 N, |∑ i ∈ Finset.Icc j N, (∑ k ∈ Finset.Icc 1 i, u i k) / (i : ℝ)| := by
            refine Finset.sum_congr rfl fun j _ => Real.rpow_one _
      _ ≤ ∑ j ∈ Finset.Icc 1 N, ∑ i ∈ Finset.Icc j N, (∑ k ∈ Finset.Icc 1 i, |u i k|) / (i : ℝ) := by
            refine Finset.sum_le_sum fun j _ => ?_
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
            have hi_abs : |(i : ℝ)| = (i : ℝ) := abs_of_nonneg (Nat.cast_nonneg i)
            rw [abs_div, hi_abs]
            exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg i)
      _ = ∑ i ∈ Finset.Icc 1 N, ∑ _j ∈ Finset.Icc 1 i, (∑ k ∈ Finset.Icc 1 i, |u i k|) / (i : ℝ) :=
            sum_Icc_swap N (fun i _ => (∑ k ∈ Finset.Icc 1 i, |u i k|) / (i : ℝ))
      _ = ∑ i ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 i, |u i k| := by
            refine Finset.sum_congr rfl fun i hi => ?_
            have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
            have hi_ne : (i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
            rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
            field_simp [hi_ne]
      _ = ∑ k ∈ Finset.Icc 1 N, ∑ i ∈ Finset.Icc k N, |u i k| :=
            (sum_Icc_swap N (fun i k => |u i k|)).symm
      _ = ∑ j ∈ Finset.Icc 1 N, (∑ i ∈ Finset.Icc j N, |u i j|) ^ (1 : ℝ) := by
            refine Finset.sum_congr rfl fun j _ => (Real.rpow_one _).symm
  · refine ⟨(2 : ℝ) ^ p * ((p / (p - 1)) ^ p + p ^ p), by positivity, fun N u => ?_⟩
    let A : ℕ → ℝ := fun k => ∑ i ∈ Finset.Icc k N, |u i k|
    have hA_nonneg : ∀ k ∈ Finset.Icc 1 N, 0 ≤ A k := fun k _ =>
      Finset.sum_nonneg fun i _ => abs_nonneg (u i k)
    have hp_nonneg : 0 ≤ p := by linarith
    have hpoint : ∀ j ∈ Finset.Icc 1 N,
        |∑ i ∈ Finset.Icc j N, (∑ k ∈ Finset.Icc 1 i, u i k) / (i : ℝ)| ^ p ≤
          (2 : ℝ) ^ p * (((∑ k ∈ Finset.Icc 1 j, A k) / (j : ℝ)) ^ p +
            (∑ k ∈ Finset.Icc j N, A k / (k : ℝ)) ^ p) := by
      intro j hj
      have hj_mem := Finset.mem_Icc.mp hj
      have hj1 : 1 ≤ j := hj_mem.1
      have hj_pos : (0 : ℝ) < j := Nat.cast_pos.mpr (by omega)
      set S_j := (∑ k ∈ Finset.Icc 1 j, A k) / (j : ℝ)
      set R_j := ∑ k ∈ Finset.Icc j N, A k / (k : ℝ)
      have hS_nonneg : 0 ≤ S_j := by
        refine div_nonneg (Finset.sum_nonneg fun k hk => ?_) hj_pos.le
        have hk_mem := Finset.mem_Icc.mp hk
        exact hA_nonneg k (Finset.mem_Icc.mpr ⟨hk_mem.1, le_trans hk_mem.2 hj_mem.2⟩)
      have hR_nonneg : 0 ≤ R_j := by
        refine Finset.sum_nonneg fun k hk => ?_
        have hk_mem := Finset.mem_Icc.mp hk
        exact div_nonneg (hA_nonneg k (Finset.mem_Icc.mpr ⟨le_trans hj1 hk_mem.1, hk_mem.2⟩))
          (Nat.cast_nonneg k)
      have hsplit_inner : ∀ i ∈ Finset.Icc j N,
          ∑ k ∈ Finset.Icc 1 i, |u i k| =
            ∑ k ∈ Finset.Icc 1 j, |u i k| + ∑ k ∈ Finset.Icc (j + 1) i, |u i k| := by
        intro i hi
        have hji : j ≤ i := (Finset.mem_Icc.mp hi).1
        have hunion : Finset.Icc 1 i = Finset.Icc 1 j ∪ Finset.Icc (j + 1) i := by
          ext k
          simp only [Finset.mem_Icc, Finset.mem_union]
          omega
        have hdisj : Disjoint (Finset.Icc 1 j) (Finset.Icc (j + 1) i) := by
          rw [Finset.disjoint_left]
          intro k hk1 hk2
          simp only [Finset.mem_Icc] at hk1 hk2
          omega
        rw [hunion, Finset.sum_union hdisj]
      have hfirst : ∑ i ∈ Finset.Icc j N, (∑ k ∈ Finset.Icc 1 j, |u i k|) / (i : ℝ) ≤ S_j := by
        calc
          ∑ i ∈ Finset.Icc j N, (∑ k ∈ Finset.Icc 1 j, |u i k|) / (i : ℝ)
              = ∑ i ∈ Finset.Icc j N, ∑ k ∈ Finset.Icc 1 j, |u i k| / (i : ℝ) := by
                refine Finset.sum_congr rfl fun i _ => ?_
                simp only [div_eq_mul_inv, Finset.sum_mul]
          _ = ∑ k ∈ Finset.Icc 1 j, ∑ i ∈ Finset.Icc j N, |u i k| / (i : ℝ) := Finset.sum_comm
          _ ≤ ∑ k ∈ Finset.Icc 1 j, ∑ i ∈ Finset.Icc j N, |u i k| / (j : ℝ) := by
                refine Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun i hi => ?_
                have hji : (j : ℝ) ≤ (i : ℝ) := Nat.cast_le.mpr (Finset.mem_Icc.mp hi).1
                exact div_le_div_of_nonneg_left (abs_nonneg _) hj_pos hji
          _ = (∑ k ∈ Finset.Icc 1 j, ∑ i ∈ Finset.Icc j N, |u i k|) / (j : ℝ) := by
                simp only [div_eq_mul_inv, Finset.sum_mul]
          _ ≤ S_j := by
                refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun k hk => ?_) hj_pos.le
                have hkj : k ≤ j := (Finset.mem_Icc.mp hk).2
                refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => abs_nonneg _)
                intro i hi
                simp only [Finset.mem_Icc] at hi ⊢
                omega
      have hsecond : ∑ i ∈ Finset.Icc j N, (∑ k ∈ Finset.Icc (j + 1) i, |u i k|) / (i : ℝ) ≤ R_j := by
        calc
          ∑ i ∈ Finset.Icc j N, (∑ k ∈ Finset.Icc (j + 1) i, |u i k|) / (i : ℝ)
              = ∑ i ∈ Finset.Icc j N, ∑ k ∈ Finset.Icc (j + 1) i, |u i k| / (i : ℝ) := by
                refine Finset.sum_congr rfl fun i _ => ?_
                simp only [div_eq_mul_inv, Finset.sum_mul]
          _ = ∑ k ∈ Finset.Icc (j + 1) N, ∑ i ∈ Finset.Icc k N, |u i k| / (i : ℝ) :=
                sum_Icc_swap_strict j N hj1 (fun i k => |u i k| / (i : ℝ))
          _ ≤ ∑ k ∈ Finset.Icc (j + 1) N, ∑ i ∈ Finset.Icc k N, |u i k| / (k : ℝ) := by
                refine Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun i hi => ?_
                have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (by have := (Finset.mem_Icc.mp hk).1; omega)
                have hki : (k : ℝ) ≤ (i : ℝ) := Nat.cast_le.mpr (Finset.mem_Icc.mp hi).1
                exact div_le_div_of_nonneg_left (abs_nonneg _) hk_pos hki
          _ = ∑ k ∈ Finset.Icc (j + 1) N, A k / (k : ℝ) := by
                refine Finset.sum_congr rfl fun k _ => ?_
                simp only [A, div_eq_mul_inv, Finset.sum_mul]
          _ ≤ R_j := by
                refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k hk _ => ?_)
                · intro k hk
                  simp only [Finset.mem_Icc] at hk ⊢
                  omega
                · have hk_mem := Finset.mem_Icc.mp hk
                  exact div_nonneg (hA_nonneg k (Finset.mem_Icc.mpr ⟨le_trans hj1 hk_mem.1, hk_mem.2⟩))
                    (Nat.cast_nonneg k)
      have hbound : |∑ i ∈ Finset.Icc j N, (∑ k ∈ Finset.Icc 1 i, u i k) / (i : ℝ)| ≤ S_j + R_j := by
        calc
          |∑ i ∈ Finset.Icc j N, (∑ k ∈ Finset.Icc 1 i, u i k) / (i : ℝ)|
              ≤ ∑ i ∈ Finset.Icc j N, (∑ k ∈ Finset.Icc 1 i, |u i k|) / (i : ℝ) := by
                refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
                have hi_abs : |(i : ℝ)| = (i : ℝ) := abs_of_nonneg (Nat.cast_nonneg i)
                rw [abs_div, hi_abs]
                exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg i)
          _ = ∑ i ∈ Finset.Icc j N,
                ((∑ k ∈ Finset.Icc 1 j, |u i k|) / (i : ℝ) +
                  (∑ k ∈ Finset.Icc (j + 1) i, |u i k|) / (i : ℝ)) := by
                refine Finset.sum_congr rfl fun i hi => ?_
                rw [hsplit_inner i hi, add_div]
          _ = (∑ i ∈ Finset.Icc j N, (∑ k ∈ Finset.Icc 1 j, |u i k|) / (i : ℝ)) +
                (∑ i ∈ Finset.Icc j N, (∑ k ∈ Finset.Icc (j + 1) i, |u i k|) / (i : ℝ)) :=
                Finset.sum_add_distrib
          _ ≤ S_j + R_j := add_le_add hfirst hsecond
      have hpow1 : |∑ i ∈ Finset.Icc j N, (∑ k ∈ Finset.Icc 1 i, u i k) / (i : ℝ)| ^ p ≤
          (S_j + R_j) ^ p := Real.rpow_le_rpow (abs_nonneg _) hbound hp_nonneg
      have hpow2 : (S_j + R_j) ^ p ≤ (2 : ℝ) ^ p * (S_j ^ p + R_j ^ p) := by
        have hmax : S_j + R_j ≤ 2 * max S_j R_j := by linarith [le_max_left S_j R_j, le_max_right S_j R_j]
        have hmax_nonneg : 0 ≤ max S_j R_j := le_max_of_le_left hS_nonneg
        calc
          (S_j + R_j) ^ p ≤ (2 * max S_j R_j) ^ p :=
            Real.rpow_le_rpow (add_nonneg hS_nonneg hR_nonneg) hmax hp_nonneg
          _ = (2 : ℝ) ^ p * (max S_j R_j) ^ p := Real.mul_rpow (by norm_num) hmax_nonneg
          _ ≤ (2 : ℝ) ^ p * (S_j ^ p + R_j ^ p) := by
            refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by norm_num) p)
            rcases le_total S_j R_j with h | h
            · rw [max_eq_right h]
              linarith [Real.rpow_nonneg hS_nonneg p]
            · rw [max_eq_left h]
              linarith [Real.rpow_nonneg hR_nonneg p]
      exact hpow1.trans hpow2
    calc
      ∑ j ∈ Finset.Icc 1 N, |∑ i ∈ Finset.Icc j N, (∑ k ∈ Finset.Icc 1 i, u i k) / (i : ℝ)| ^ p
          ≤ ∑ j ∈ Finset.Icc 1 N,
              (2 : ℝ) ^ p * (((∑ k ∈ Finset.Icc 1 j, A k) / (j : ℝ)) ^ p +
                (∑ k ∈ Finset.Icc j N, A k / (k : ℝ)) ^ p) :=
            Finset.sum_le_sum hpoint
      _ = (2 : ℝ) ^ p * (∑ j ∈ Finset.Icc 1 N, ((∑ k ∈ Finset.Icc 1 j, A k) / (j : ℝ)) ^ p +
            ∑ j ∈ Finset.Icc 1 N, (∑ k ∈ Finset.Icc j N, A k / (k : ℝ)) ^ p) := by
            rw [← Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ (2 : ℝ) ^ p * ((p / (p - 1)) ^ p * ∑ k ∈ Finset.Icc 1 N, A k ^ p +
            p ^ p * ∑ k ∈ Finset.Icc 1 N, A k ^ p) := by
            refine mul_le_mul_of_nonneg_left
              (add_le_add (hardy_ineq hp_gt N hA_nonneg) (dual_hardy_ineq hp_gt N hA_nonneg))
              (Real.rpow_nonneg (by norm_num) p)
      _ = (2 : ℝ) ^ p * ((p / (p - 1)) ^ p + p ^ p) *
            ∑ j ∈ Finset.Icc 1 N, (∑ i ∈ Finset.Icc j N, |u i j|) ^ p := by
            simp only [A]
            ring
