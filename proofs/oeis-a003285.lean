import OMAStatements.S_oeis_a003285

namespace Antigravity2_oeis_a003285

open OMA.S_oeis_a003285 Matrix

lemma sqrt_ne_rat {d : ℕ} (hd : ¬ IsSquare d) (p q : ℤ) (hq : q ≠ 0) :
    Real.sqrt d ≠ (p : ℝ) / (q : ℝ) := by
  intro h
  have hqR : (q : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hq
  have hmul : Real.sqrt d * (q : ℝ) = (p : ℝ) := by
    rw [h, div_mul_cancel₀ _ hqR]
  have hsqR : (d : ℝ) * (q : ℝ) ^ 2 = (p : ℝ) ^ 2 := by
    have := congrArg (fun t : ℝ => t ^ 2) hmul
    simp only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)] at this
    exact this
  have hsqZ : (d : ℤ) * q ^ 2 = p ^ 2 := by
    exact_mod_cast hsqR
  have hsqN : d * q.natAbs ^ 2 = p.natAbs ^ 2 := by
    have : ((d * q.natAbs ^ 2 : ℕ) : ℤ) = ((p.natAbs ^ 2 : ℕ) : ℤ) := by
      push_cast
      rw [sq_abs, sq_abs]
      exact hsqZ
    exact_mod_cast this
  have hqpos : 0 < q.natAbs := Int.natAbs_pos.mpr hq
  have hdvd : q.natAbs ^ 2 ∣ p.natAbs ^ 2 := ⟨d, by rw [mul_comm]; exact hsqN.symm⟩
  have hdvd1 : q.natAbs ∣ p.natAbs := (Nat.pow_dvd_pow_iff (by norm_num : 2 ≠ 0)).mp hdvd
  obtain ⟨r, hr⟩ := hdvd1
  have hsq2 : d * q.natAbs ^ 2 = r ^ 2 * q.natAbs ^ 2 := by
    rw [hsqN, hr]
    ring
  have hd_eq : d = r ^ 2 := Nat.eq_of_mul_eq_mul_right (pow_pos hqpos 2) hsq2
  exact hd ⟨r, by rw [hd_eq, sq]⟩

lemma sqrt_quad_ne_int {d : ℕ} (hd : ¬ IsSquare d) (P Q : ℤ) (hQ : Q ≠ 0) (m : ℤ) :
    (Real.sqrt d + (P : ℝ)) / (Q : ℝ) ≠ (m : ℝ) := by
  intro h
  have hQR : (Q : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hQ
  have h1 : Real.sqrt d + (P : ℝ) = (m : ℝ) * (Q : ℝ) := (div_eq_iff hQR).mp h
  have h2 : Real.sqrt d = ((m * Q - P : ℤ) : ℝ) / ((1 : ℤ) : ℝ) := by
    push_cast
    linarith
  exact sqrt_ne_rat hd (m * Q - P) 1 one_ne_zero h2

noncomputable def pqSeq (d : ℕ) : ℕ → ℤ × ℤ
  | 0 => (0, 1)
  | k + 1 =>
    let P := (pqSeq d k).1
    let Q := (pqSeq d k).2
    let a := ⌊(Real.sqrt d + (P : ℝ)) / (Q : ℝ)⌋
    let P' := a * Q - P
    let Q' := ((d : ℤ) - P' ^ 2) / Q
    (P', Q')

lemma pqSeq_props {d : ℕ} (hd : ¬ IsSquare d) :
    ∀ k : ℕ,
      let P := (pqSeq d k).1
      let Q := (pqSeq d k).2
      0 < Q ∧
      Q ∣ ((d : ℤ) - P ^ 2) ∧
      Nat.iterate cfStep k (Real.sqrt d) = (Real.sqrt d + (P : ℝ)) / (Q : ℝ) ∧
      (1 ≤ k → (P : ℝ) < Real.sqrt d ∧ Real.sqrt d - (P : ℝ) < (Q : ℝ) ∧
        1 < (Real.sqrt d + (P : ℝ)) / (Q : ℝ)) := by
  intro k
  induction k with
  | zero =>
    refine ⟨by simp [pqSeq], one_dvd _, ?_, fun h => absurd h (by omega)⟩
    simp [pqSeq]
  | succ k ih =>
    obtain ⟨hQpos, hQdvd, hiter, hred⟩ := ih
    set P := (pqSeq d k).1
    set Q := (pqSeq d k).2
    set x : ℝ := (Real.sqrt d + (P : ℝ)) / (Q : ℝ)
    set a : ℤ := ⌊x⌋
    set P' : ℤ := a * Q - P
    set Q' : ℤ := ((d : ℤ) - P' ^ 2) / Q
    have hP'_eq : (pqSeq d (k + 1)).1 = P' := rfl
    have hQ'_eq : (pqSeq d (k + 1)).2 = Q' := rfl
    have hQR : (0 : ℝ) < (Q : ℝ) := Int.cast_pos.mpr hQpos
    have hx_ne : x ≠ (a : ℝ) := sqrt_quad_ne_int hd P Q hQpos.ne' a
    have hxa_pos : 0 < x - (a : ℝ) :=
      sub_pos.mpr (lt_of_le_of_ne (Int.floor_le x) hx_ne.symm)
    have hxa_lt : x - (a : ℝ) < 1 := by
      have := Int.lt_floor_add_one x
      linarith
    have hxa_eq : x - (a : ℝ) = (Real.sqrt d - (P' : ℝ)) / (Q : ℝ) := by
      have hP'R : (P' : ℝ) = (a : ℝ) * (Q : ℝ) - (P : ℝ) := by
        simp only [P']
        push_cast
        ring
      rw [hP'R]
      simp only [x]
      field_simp [hQR.ne']
      ring
    have hP'_lt : (P' : ℝ) < Real.sqrt d := by
      have : 0 < (Real.sqrt d - (P' : ℝ)) / (Q : ℝ) := hxa_eq ▸ hxa_pos
      have : 0 < Real.sqrt d - (P' : ℝ) := (div_pos_iff_of_pos_right hQR).mp this
      linarith
    have hd_sub_P'_dvd : Q ∣ (d : ℤ) - P' ^ 2 := by
      have hident : (d : ℤ) - P' ^ 2 = ((d : ℤ) - P ^ 2) + Q * (2 * a * P - a ^ 2 * Q) := by
        simp only [P']
        ring
      rw [hident]
      exact dvd_add hQdvd (dvd_mul_right Q _)
    have hQ'_mul : Q' * Q = (d : ℤ) - P' ^ 2 := Int.ediv_mul_cancel hd_sub_P'_dvd
    have hQ'_mulR : (Q' : ℝ) * (Q : ℝ) = (d : ℝ) - (P' : ℝ) ^ 2 := by
      exact_mod_cast hQ'_mul
    have hQ'_pos_and_red : 0 < Q' ∧ Real.sqrt d - (P' : ℝ) < (Q' : ℝ) := by
      have hsum_gt : (Q : ℝ) < Real.sqrt d + (P' : ℝ) := by
        cases k with
        | zero =>
          have hP0 : P = 0 := rfl
          have hQ0 : Q = 1 := rfl
          have ha0 : 1 ≤ a := by
            have hd1 : (1 : ℝ) ≤ Real.sqrt d := by
              have hdpos : 1 ≤ d := by
                by_contra h0
                have : d = 0 := by omega
                exact hd ⟨0, by simp [this]⟩
              have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdpos
              exact Real.one_le_sqrt.mpr this
            have hx1 : (1 : ℝ) ≤ x := by simp [x, hP0, hQ0, hd1]
            exact Int.le_floor.mpr (by exact_mod_cast hx1)
          have hP'ge1 : (1 : ℝ) ≤ (P' : ℝ) := by
            have : 1 ≤ P' := by simp only [P', hP0, hQ0]; omega
            exact_mod_cast this
          have hQ0R : (Q : ℝ) = 1 := by simp [hQ0]
          rw [hQ0R]
          have : 0 < Real.sqrt d := by linarith
          linarith
        | succ k' =>
          obtain ⟨hPk_lt, hQk_gt, hxk_gt⟩ := hred (Nat.succ_pos k')
          have ha_ge1 : (1 : ℝ) ≤ (a : ℝ) := by
            have : 1 ≤ a := Int.le_floor.mpr (by exact_mod_cast hxk_gt.le)
            exact_mod_cast this
          have hP'R : (P' : ℝ) = (a : ℝ) * (Q : ℝ) - (P : ℝ) := by
            simp only [P']; push_cast; ring
          nlinarith
      have hprod_pos : 0 < (Real.sqrt d + (P' : ℝ)) * (Real.sqrt d - (P' : ℝ)) :=
        mul_pos (by linarith) (by linarith)
      have hdiff_sq : (Real.sqrt d + (P' : ℝ)) * (Real.sqrt d - (P' : ℝ)) =
          (d : ℝ) - (P' : ℝ) ^ 2 := by
        have hsq : Real.sqrt d ^ 2 = (d : ℝ) := Real.sq_sqrt (Nat.cast_nonneg d)
        nlinarith
      have hQ'R_pos : 0 < (Q' : ℝ) := by
        have : 0 < (Q' : ℝ) * (Q : ℝ) := by rw [hQ'_mulR, ← hdiff_sq]; exact hprod_pos
        exact (mul_pos_iff_of_pos_right hQR).mp this
      have hQ'pos : 0 < Q' := by exact_mod_cast hQ'R_pos
      have hQ'gt : Real.sqrt d - (P' : ℝ) < (Q' : ℝ) := by
        have h1 : (Q : ℝ) * (Real.sqrt d - (P' : ℝ)) <
            (Real.sqrt d + (P' : ℝ)) * (Real.sqrt d - (P' : ℝ)) :=
          mul_lt_mul_of_pos_right hsum_gt (by linarith)
        rw [hdiff_sq, ← hQ'_mulR] at h1
        nlinarith
      exact ⟨hQ'pos, hQ'gt⟩
    have hQ'pos : 0 < Q' := hQ'_pos_and_red.1
    have hQ'R : (0 : ℝ) < (Q' : ℝ) := Int.cast_pos.mpr hQ'pos
    have hQ'_dvd : Q' ∣ (d : ℤ) - P' ^ 2 := ⟨Q, hQ'_mul.symm⟩
    have hiter_succ : Nat.iterate cfStep (k + 1) (Real.sqrt d) =
        (Real.sqrt d + (P' : ℝ)) / (Q' : ℝ) := by
      rw [Function.iterate_succ_apply', hiter]
      simp only [cfStep]
      have hne_fl : x ≠ (⌊x⌋ : ℝ) := hx_ne
      rw [if_neg hne_fl]
      change 1 / (x - (a : ℝ)) = (Real.sqrt d + (P' : ℝ)) / (Q' : ℝ)
      rw [hxa_eq]
      have hden_ne : Real.sqrt d - (P' : ℝ) ≠ 0 := by linarith
      have hsq : Real.sqrt d ^ 2 = (d : ℝ) := Real.sq_sqrt (Nat.cast_nonneg d)
      field_simp [hQR.ne', hQ'R.ne', hden_ne]
      nlinarith [hQ'_mulR, hsq]
    have hx'_gt1 : 1 < (Real.sqrt d + (P' : ℝ)) / (Q' : ℝ) := by
      have : (Real.sqrt d + (P' : ℝ)) / (Q' : ℝ) = 1 / (x - (a : ℝ)) := by
        rw [← hiter_succ, Function.iterate_succ_apply', hiter]
        simp only [cfStep]
        have hne_fl : x ≠ (⌊x⌋ : ℝ) := hx_ne
        rw [if_neg hne_fl]
      rw [this]
      exact one_lt_one_div hxa_pos hxa_lt
    refine ⟨hQ'pos, hQ'_dvd, hiter_succ, fun _ => ⟨hP'_lt, hQ'_pos_and_red.2, hx'_gt1⟩⟩

lemma pqSeq_bounds {d : ℕ} (hd : ¬ IsSquare d) {k : ℕ} (hk : 1 ≤ k) :
    0 < (pqSeq d k).1 ∧ (pqSeq d k).1 ≤ ⌊Real.sqrt d⌋ ∧
    0 < (pqSeq d k).2 ∧ (pqSeq d k).2 ≤ 2 * ⌊Real.sqrt d⌋ + 1 := by
  obtain ⟨hQpos, _, _, hred⟩ := pqSeq_props hd k
  obtain ⟨hPlt, hQgt, hxgt⟩ := hred hk
  set P := (pqSeq d k).1
  set Q := (pqSeq d k).2
  have hQR : (0 : ℝ) < (Q : ℝ) := Int.cast_pos.mpr hQpos
  have hsum : (Q : ℝ) < Real.sqrt d + (P : ℝ) := (one_lt_div hQR).mp hxgt
  have hPR_pos : (0 : ℝ) < (P : ℝ) := by linarith
  have hPpos : 0 < P := by exact_mod_cast hPR_pos
  have hPle : P ≤ ⌊Real.sqrt d⌋ := Int.le_floor.mpr hPlt.le
  have hfl : Real.sqrt d < (⌊Real.sqrt d⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have hQlt : (Q : ℝ) < 2 * (⌊Real.sqrt d⌋ : ℝ) + 2 := by
    have hPleR : (P : ℝ) ≤ (⌊Real.sqrt d⌋ : ℝ) := by exact_mod_cast hPle
    linarith
  have hQle : Q ≤ 2 * ⌊Real.sqrt d⌋ + 1 := by
    have : Q < 2 * ⌊Real.sqrt d⌋ + 2 := by exact_mod_cast hQlt
    omega
  exact ⟨hPpos, hPle, hQpos, hQle⟩

lemma pqSeq_step_injective {d : ℕ} (hd : ¬ IsSquare d) {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l)
    (heq : pqSeq d (k + 1) = pqSeq d (l + 1)) :
    pqSeq d k = pqSeq d l := by
  have recover : ∀ m : ℕ, 1 ≤ m →
      let Pm := (pqSeq d m).1
      let Qm := (pqSeq d m).2
      let P1 := (pqSeq d (m + 1)).1
      let Q1 := (pqSeq d (m + 1)).2
      Qm = ((d : ℤ) - P1 ^ 2) / Q1 ∧
      Pm = ⌊(Q1 : ℝ) / (Real.sqrt d - (P1 : ℝ))⌋ * Qm - P1 := by
    intro m hm
    obtain ⟨hQpos, hQdvd, _, hred⟩ := pqSeq_props hd m
    obtain ⟨hPmlt, hQmgt, _⟩ := hred hm
    obtain ⟨hQ1pos, _, _, hred1⟩ := pqSeq_props hd (m + 1)
    obtain ⟨hP1lt, _, _⟩ := hred1 (Nat.succ_pos m)
    set Pm := (pqSeq d m).1
    set Qm := (pqSeq d m).2
    set am : ℤ := ⌊(Real.sqrt d + (Pm : ℝ)) / (Qm : ℝ)⌋
    set P1 : ℤ := am * Qm - Pm
    set Q1 : ℤ := ((d : ℤ) - P1 ^ 2) / Qm
    have hP1def : (pqSeq d (m + 1)).1 = P1 := rfl
    have hQ1def : (pqSeq d (m + 1)).2 = Q1 := rfl
    rw [hQ1def] at hQ1pos
    rw [hP1def] at hP1lt
    have hdvd : Qm ∣ (d : ℤ) - P1 ^ 2 := by
      have hident : (d : ℤ) - P1 ^ 2 = ((d : ℤ) - Pm ^ 2) + Qm * (2 * am * Pm - am ^ 2 * Qm) := by
        simp only [P1]; ring
      rw [hident]
      exact dvd_add hQdvd (dvd_mul_right Qm _)
    have hmul : Q1 * Qm = (d : ℤ) - P1 ^ 2 := Int.ediv_mul_cancel hdvd
    have hQm_eq : Qm = ((d : ℤ) - P1 ^ 2) / Q1 := by
      rw [← hmul, Int.mul_ediv_cancel_left _ hQ1pos.ne']
    have hratio : (Q1 : ℝ) / (Real.sqrt d - (P1 : ℝ)) =
        (am : ℝ) + (Real.sqrt d - (Pm : ℝ)) / (Qm : ℝ) := by
      have hmulR : (Q1 : ℝ) * (Qm : ℝ) = (d : ℝ) - (P1 : ℝ) ^ 2 := by exact_mod_cast hmul
      have hP1R : (P1 : ℝ) = (am : ℝ) * (Qm : ℝ) - (Pm : ℝ) := by
        simp only [P1]; push_cast; ring
      have hQmR : (0 : ℝ) < (Qm : ℝ) := Int.cast_pos.mpr hQpos
      have hden : Real.sqrt d - (P1 : ℝ) ≠ 0 := by linarith
      have hsq : Real.sqrt d ^ 2 = (d : ℝ) := Real.sq_sqrt (Nat.cast_nonneg d)
      field_simp [hQmR.ne', hden]
      have halg : (Real.sqrt d - (P1 : ℝ)) * ((am : ℝ) * (Qm : ℝ) + (Real.sqrt d - (Pm : ℝ))) =
          (d : ℝ) - (P1 : ℝ) ^ 2 := by
        nlinarith [hP1R, hsq]
      linarith [hmulR, halg]
    have hfrac_pos : 0 ≤ (Real.sqrt d - (Pm : ℝ)) / (Qm : ℝ) :=
      div_nonneg (by linarith) (Int.cast_pos.mpr hQpos).le
    have hfrac_lt : (Real.sqrt d - (Pm : ℝ)) / (Qm : ℝ) < 1 :=
      (div_lt_one (Int.cast_pos.mpr hQpos)).mpr hQmgt
    have ham_eq : ⌊(Q1 : ℝ) / (Real.sqrt d - (P1 : ℝ))⌋ = am := by
      rw [hratio, Int.floor_eq_iff]
      exact ⟨by linarith, by linarith⟩
    have hPm_eq : Pm = am * Qm - P1 := by simp only [P1]; ring
    rw [hP1def, hQ1def]
    exact ⟨hQm_eq, by rw [ham_eq]; exact hPm_eq⟩
  obtain ⟨hQk, hPk⟩ := recover k hk
  obtain ⟨hQl, hPl⟩ := recover l hl
  ext
  · rw [hPk, hPl, hQk, hQl, heq]
  · rw [hQk, hQl, heq]

lemma exists_cf_period {d : ℕ} (hd : ¬ IsSquare d) :
    ∃ m : ℕ, 0 < m ∧ ∀ k : ℕ, 1 ≤ k →
      cfCoeff (Real.sqrt d) (k + m) = cfCoeff (Real.sqrt d) k := by
  set B : ℤ := 2 * ⌊Real.sqrt d⌋ + 1
  set box : Finset (ℤ × ℤ) := Finset.Icc 0 B ×ˢ Finset.Icc 0 B
  have hmaps : ∀ n : ℕ, pqSeq d (n + 1) ∈ box := by
    intro n
    obtain ⟨hPpos, hPle, hQpos, hQle⟩ := pqSeq_bounds hd (by omega : 1 ≤ n + 1)
    have hfl0 : 0 ≤ ⌊Real.sqrt d⌋ := Int.floor_nonneg.mpr (Real.sqrt_nonneg _)
    simp only [box, Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨by omega, by omega⟩, ⟨by omega, hQle⟩⟩
  have hcard : box.card < (Finset.range (box.card + 1)).card := by simp
  obtain ⟨i, hi, j, hj, hij, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard
      (fun n _ => hmaps n)
  have hex : ∃ a b : ℕ, a < b ∧ pqSeq d (a + 1) = pqSeq d (b + 1) := by
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact ⟨i, j, hlt, heq⟩
    · exact ⟨j, i, hgt, heq.symm⟩
  obtain ⟨a, b, hab, heqab⟩ := hex
  set m := b - a
  have hm_pos : 0 < m := Nat.sub_pos_of_lt hab
  have hbase : pqSeq d 1 = pqSeq d (1 + m) := by
    have hshift : ∀ t : ℕ, pqSeq d (t + 1) = pqSeq d (t + 1 + m) → pqSeq d 1 = pqSeq d (1 + m) := by
      intro t
      induction t with
      | zero => intro h; simpa using h
      | succ t iht =>
        intro h
        apply iht
        apply pqSeq_step_injective hd (Nat.succ_pos t) (by omega)
        have h1 : t + 1 + m + 1 = t + 1 + 1 + m := by omega
        rw [h1]
        exact h
    apply hshift a
    have hb : a + 1 + m = b + 1 := by omega
    rw [hb]
    exact heqab
  have hper_pq : ∀ k : ℕ, 1 ≤ k → pqSeq d (k + m) = pqSeq d k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact hbase.symm
    | succ k _ ih =>
      have h1 : k + 1 + m = (k + m) + 1 := by omega
      rw [h1]
      change (let P := (pqSeq d (k + m)).1; let Q := (pqSeq d (k + m)).2
        let a := ⌊(Real.sqrt d + (P : ℝ)) / (Q : ℝ)⌋
        let P' := a * Q - P; let Q' := ((d : ℤ) - P' ^ 2) / Q; (P', Q')) =
        (let P := (pqSeq d k).1; let Q := (pqSeq d k).2
        let a := ⌊(Real.sqrt d + (P : ℝ)) / (Q : ℝ)⌋
        let P' := a * Q - P; let Q' := ((d : ℤ) - P' ^ 2) / Q; (P', Q'))
      rw [ih]
  refine ⟨m, hm_pos, ?_⟩
  intro k hk
  unfold cfCoeff
  rw [(pqSeq_props hd (k + m)).2.2.1, (pqSeq_props hd k).2.2.1, hper_pq k hk]

def stepMat (a : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![a, 1; 1, 0]

noncomputable def convMat (x : ℝ) : ℕ → Matrix (Fin 2) (Fin 2) ℤ
  | 0 => !![cfCoeff x 0, 1; 1, 0]
  | k + 1 => convMat x k * stepMat (cfCoeff x (k + 1))

noncomputable def prodMat (x : ℝ) (k : ℕ) : ℕ → Matrix (Fin 2) (Fin 2) ℤ
  | 0 => 1
  | r + 1 => prodMat x k r * stepMat (cfCoeff x (k + r + 1))

lemma mul_stepMat_entries (M : Matrix (Fin 2) (Fin 2) ℤ) (a : ℤ) :
    (M * stepMat a) 0 0 = M 0 0 * a + M 0 1 ∧
    (M * stepMat a) 0 1 = M 0 0 ∧
    (M * stepMat a) 1 0 = M 1 0 * a + M 1 1 ∧
    (M * stepMat a) 1 1 = M 1 0 := by
  simp [stepMat, Matrix.mul_apply, Fin.sum_univ_two]

lemma convMat_entries (x : ℝ) :
    ∀ k : ℕ,
      convMat x k 0 0 = convNum x k ∧
      convMat x k 1 0 = convDen x k ∧
      convMat x (k + 1) 0 0 = convNum x (k + 1) ∧
      convMat x (k + 1) 1 0 = convDen x (k + 1) ∧
      convMat x (k + 1) 0 1 = convNum x k ∧
      convMat x (k + 1) 1 1 = convDen x k := by
  intro k
  induction k with
  | zero =>
    have h00 : convMat x 0 0 0 = convNum x 0 := by simp [convMat, convNum]
    have h10 : convMat x 0 1 0 = convDen x 0 := by simp [convMat, convDen]
    have h01 : convMat x 0 0 1 = 1 := by simp [convMat]
    have h11 : convMat x 0 1 1 = 0 := by simp [convMat]
    refine ⟨h00, h10, ?_, ?_, ?_, ?_⟩
    · change (convMat x 0 * stepMat (cfCoeff x 1)) 0 0 = convNum x 1
      rw [(mul_stepMat_entries _ _).1, h00, h01]
      simp [convNum]; ring
    · change (convMat x 0 * stepMat (cfCoeff x 1)) 1 0 = convDen x 1
      rw [(mul_stepMat_entries _ _).2.2.1, h10, h11]
      simp [convDen]
    · change (convMat x 0 * stepMat (cfCoeff x 1)) 0 1 = convNum x 0
      rw [(mul_stepMat_entries _ _).2.1, h00]
    · change (convMat x 0 * stepMat (cfCoeff x 1)) 1 1 = convDen x 0
      rw [(mul_stepMat_entries _ _).2.2.2, h10]
  | succ k ih =>
    obtain ⟨_, _, h00, h10, h01, h11⟩ := ih
    refine ⟨h00, h10, ?_, ?_, ?_, ?_⟩
    · change (convMat x (k + 1) * stepMat (cfCoeff x (k + 2))) 0 0 = convNum x (k + 2)
      rw [(mul_stepMat_entries _ _).1, h00, h01]
      simp only [convNum]; ring
    · change (convMat x (k + 1) * stepMat (cfCoeff x (k + 2))) 1 0 = convDen x (k + 2)
      rw [(mul_stepMat_entries _ _).2.2.1, h10, h11]
      simp only [convDen]; ring
    · change (convMat x (k + 1) * stepMat (cfCoeff x (k + 2))) 0 1 = convNum x (k + 1)
      rw [(mul_stepMat_entries _ _).2.1, h00]
    · change (convMat x (k + 1) * stepMat (cfCoeff x (k + 2))) 1 1 = convDen x (k + 1)
      rw [(mul_stepMat_entries _ _).2.2.2, h10]

lemma convMat_add (x : ℝ) (k r : ℕ) :
    convMat x (k + r) = convMat x k * prodMat x k r := by
  induction r with
  | zero => simp [prodMat]
  | succ r ih =>
    rw [show k + (r + 1) = (k + r) + 1 by omega]
    simp only [convMat, prodMat]
    rw [ih, Matrix.mul_assoc]

lemma det_stepMat (a : ℤ) : (stepMat a).det = -1 := by
  simp [stepMat, Matrix.det_fin_two]

lemma det_prodMat (x : ℝ) (k r : ℕ) : (prodMat x k r).det = (-1 : ℤ) ^ r := by
  induction r with
  | zero => simp [prodMat]
  | succ r ih =>
    simp only [prodMat, Matrix.det_mul, ih, det_stepMat, pow_succ]

lemma prodMat_shift_left (x : ℝ) (k r : ℕ) :
    prodMat x k (r + 1) = stepMat (cfCoeff x (k + 1)) * prodMat x (k + 1) r := by
  induction r with
  | zero => simp [prodMat]
  | succ r ih =>
    change prodMat x k (r + 1) * stepMat (cfCoeff x (k + (r + 1) + 1)) =
      stepMat (cfCoeff x (k + 1)) * (prodMat x (k + 1) r * stepMat (cfCoeff x (k + 1 + r + 1)))
    rw [ih, Matrix.mul_assoc]
    rw [show k + (r + 1) + 1 = k + 1 + r + 1 by omega]

lemma prodMat_periodic (x : ℝ) (m : ℕ) (hper : ∀ j : ℕ, 1 ≤ j → cfCoeff x (j + m) = cfCoeff x j)
    (k r : ℕ) :
    prodMat x (k + m) r = prodMat x k r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [prodMat, ih]
    congr 2
    have h1 : k + m + r + 1 = (k + r + 1) + m := by omega
    rw [h1]
    exact hper (k + r + 1) (by omega)

lemma trace_prodMat_const (x : ℝ) (m : ℕ) (hm : 0 < m)
    (hper : ∀ j : ℕ, 1 ≤ j → cfCoeff x (j + m) = cfCoeff x j) (k : ℕ) :
    (prodMat x k m).trace = (prodMat x 0 m).trace := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← ih]
    obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
    have hL : prodMat x k (m' + 1) = stepMat (cfCoeff x (k + 1)) * prodMat x (k + 1) m' :=
      prodMat_shift_left x k m'
    have hR : prodMat x (k + 1) (m' + 1) =
        prodMat x (k + 1) m' * stepMat (cfCoeff x (k + 1)) := by
      simp only [prodMat]
      congr 2
      have h1 : k + 1 + m' + 1 = (k + 1) + (m' + 1) := by omega
      rw [h1]
      exact hper (k + 1) (by omega)
    rw [hL, hR, Matrix.trace_mul_comm]

lemma cayley_hamilton_fin2 (M : Matrix (Fin 2) (Fin 2) ℤ) :
    M * M = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.trace, Matrix.diag, Matrix.det_fin_two, Fin.sum_univ_two, smul_eq_mul,
      Fin.isValue, ite_true, ite_false, Fin.zero_eta, Fin.mk_one, Fin.reduceEq] <;> ring

lemma solve_main :
    ∀ d : ℕ, ¬ IsSquare d →
      ∃ C : ℤ,
        let m := cfPeriod d
        (∀ k : ℕ, convDen (Real.sqrt d) (k + 2 * m) =
          C * convDen (Real.sqrt d) (k + m) - (-1 : ℤ) ^ m * convDen (Real.sqrt d) k) ∧
        (∀ k : ℕ, convNum (Real.sqrt d) (k + 2 * m) =
          C * convNum (Real.sqrt d) (k + m) - (-1 : ℤ) ^ m * convNum (Real.sqrt d) k) := by
  intro d hd
  have hne : {m : ℕ | 0 < m ∧ ∀ k : ℕ, 1 ≤ k →
      cfCoeff (Real.sqrt d) (k + m) = cfCoeff (Real.sqrt d) k}.Nonempty :=
    exists_cf_period hd
  have hspec := Nat.sInf_mem hne
  set m := cfPeriod d
  have hm_pos : 0 < m := hspec.1
  have hper : ∀ k : ℕ, 1 ≤ k → cfCoeff (Real.sqrt d) (k + m) = cfCoeff (Real.sqrt d) k := hspec.2
  set C : ℤ := (prodMat (Real.sqrt d) 0 m).trace
  refine ⟨C, ?_, ?_⟩
  · intro k
    have hmat : convMat (Real.sqrt d) (k + 2 * m) =
        C • convMat (Real.sqrt d) (k + m) - (-1 : ℤ) ^ m • convMat (Real.sqrt d) k := by
      have h2m : k + 2 * m = (k + m) + m := by omega
      rw [h2m, convMat_add, convMat_add, prodMat_periodic _ m hper k m, Matrix.mul_assoc,
        cayley_hamilton_fin2, trace_prodMat_const _ m hm_pos hper k, det_prodMat,
        Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one]
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 1 0) hmat
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at h
    rw [(convMat_entries _ _).2.1, (convMat_entries _ _).2.1, (convMat_entries _ _).2.1] at h
    exact h
  · intro k
    have hmat : convMat (Real.sqrt d) (k + 2 * m) =
        C • convMat (Real.sqrt d) (k + m) - (-1 : ℤ) ^ m • convMat (Real.sqrt d) k := by
      have h2m : k + 2 * m = (k + m) + m := by omega
      rw [h2m, convMat_add, convMat_add, prodMat_periodic _ m hper k m, Matrix.mul_assoc,
        cayley_hamilton_fin2, trace_prodMat_const _ m hm_pos hper k, det_prodMat,
        Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one]
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 0) hmat
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at h
    rw [(convMat_entries _ _).1, (convMat_entries _ _).1, (convMat_entries _ _).1] at h
    exact h

end Antigravity2_oeis_a003285

theorem OMA.solution : type_of% @OMA.S_oeis_a003285.main :=
  Antigravity2_oeis_a003285.solve_main
