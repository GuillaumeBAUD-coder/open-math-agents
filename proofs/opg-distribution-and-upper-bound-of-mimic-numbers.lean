import OMAStatements.S_opg_distribution_and_upper_bound_of_mimic_numbers

namespace OMA.P_opg_distribution_and_upper_bound_of_mimic_numbers

open OMA.S_opg_distribution_and_upper_bound_of_mimic_numbers
open scoped Polynomial

private lemma step_zero (M D : ℕ) : step M D 0 = 0 := by
  simp [step]

private lemma step_of_lt {M D n : ℕ} (hM : 1 < M) (hn : n < M) : step M D n = n := by
  unfold step
  by_cases hn0 : n = 0
  · subst hn0; simp
  · rw [Nat.digits_of_lt M n hn0 hn]
    simp [Nat.ofDigits]

private lemma step_mul_add {M D q r : ℕ} (hM : 1 < M) (hr : r < M) :
    step M D (M * q + r) = (M - D) * step M D q + r := by
  by_cases hq : q = 0
  · subst hq
    simp [step_zero, step_of_lt hM hr]
  · unfold step
    have hdig : M.digits (M * q + r) = r :: M.digits q := by
      rw [add_comm]
      exact Nat.digits_add M hM r q hr (Or.inr hq)
    rw [hdig, Nat.ofDigits_cons]
    ring

private lemma step_le {M D : ℕ} (hM : 1 < M) (hDle : D ≤ M) : ∀ n : ℕ, step M D n ≤ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hlt : n < M
    · rw [step_of_lt hM hlt]
    · have hdiv_lt : n / M < n := Nat.div_lt_self (by omega) hM
      have hdecomp : n = M * (n / M) + n % M := (Nat.div_add_mod n M).symm
      have hmod_lt : n % M < M := Nat.mod_lt n (by omega)
      conv_lhs => rw [hdecomp]
      rw [step_mul_add hM hmod_lt]
      have h1 : step M D (n / M) ≤ n / M := ih (n / M) hdiv_lt
      have h2 : (M - D) * step M D (n / M) ≤ M * (n / M) :=
        Nat.mul_le_mul (Nat.sub_le M D) h1
      omega

private lemma step_lt_of_ge {M D n : ℕ} (hM : 1 < M) (hDpos : 0 < D) (hDle : D ≤ M)
    (hn : M ≤ n) : step M D n < n := by
  have hdecomp : n = M * (n / M) + n % M := (Nat.div_add_mod n M).symm
  have hmod_lt : n % M < M := Nat.mod_lt n (by omega)
  have hq_pos : 0 < n / M := Nat.div_pos hn (by omega)
  have hq_le := step_le hM hDle (n / M)
  conv_lhs => rw [hdecomp]
  rw [step_mul_add hM hmod_lt]
  by_cases hs0 : step M D (n / M) = 0
  · rw [hs0, mul_zero, zero_add]; omega
  · have h1 : (M - D) * step M D (n / M) < M * step M D (n / M) :=
      Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    have h2 : M * step M D (n / M) ≤ M * (n / M) := Nat.mul_le_mul_left M hq_le
    omega

private lemma step_pos {M D : ℕ} (hM : 1 < M) (hDM : D < M) :
    ∀ n : ℕ, 0 < n → 0 < step M D n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hlt : n < M
    · rw [step_of_lt hM hlt]; exact hn
    · have hdecomp : n = M * (n / M) + n % M := (Nat.div_add_mod n M).symm
      have hmod_lt : n % M < M := Nat.mod_lt n (by omega)
      have hdiv_lt : n / M < n := Nat.div_lt_self hn hM
      have hdiv_pos : 0 < n / M := Nat.div_pos (not_lt.mp hlt) (by omega)
      have hih := ih (n / M) hdiv_lt hdiv_pos
      rw [hdecomp, step_mul_add hM hmod_lt]
      have hB : 1 ≤ M - D := by omega
      have : 1 ≤ (M - D) * step M D (n / M) := Nat.mul_pos hB hih
      omega

private lemma step_modEq {M D : ℕ} (hM : 1 < M) (hDle : D ≤ M) :
    ∀ n : ℕ, Nat.ModEq D (step M D n) n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hlt : n < M
    · rw [step_of_lt hM hlt]
    · have hdecomp : n = M * (n / M) + n % M := (Nat.div_add_mod n M).symm
      have hmod_lt : n % M < M := Nat.mod_lt n (by omega)
      have hdiv_lt : n / M < n := Nat.div_lt_self (by omega) hM
      have hih := ih (n / M) hdiv_lt
      have hMB : Nat.ModEq D (M - D) M := by
        show (M - D) % D = M % D
        have h1 : M = (M - D) + D := by omega
        conv_rhs => rw [h1]
        rw [Nat.add_mod_right]
      conv_lhs => rw [hdecomp]
      conv_rhs => rw [hdecomp]
      rw [step_mul_add hM hmod_lt]
      exact (hMB.mul hih).add_right (n % M)

private lemma iterate_step_modEq {M D : ℕ} (hM : 1 < M) (hDle : D ≤ M) :
    ∀ j n : ℕ, Nat.ModEq D ((step M D)^[j] n) n := by
  intro j
  induction j with
  | zero => intro n; rfl
  | succ j ih =>
    intro n
    rw [Function.iterate_succ_apply]
    exact (ih (step M D n)).trans (step_modEq hM hDle n)

private lemma iterate_step_zero (M D : ℕ) : ∀ j : ℕ, (step M D)^[j] 0 = 0 := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply, step_zero, ih]

private lemma first_succ_iff {M D h n : ℕ} :
    First M D (h + 1) n ↔ n ≠ D ∧ First M D h (step M D n) := by
  unfold First
  constructor
  · rintro ⟨heq, hne⟩
    refine ⟨by simpa using hne 0 (Nat.succ_pos h), ?_, ?_⟩
    · rwa [Function.iterate_succ_apply] at heq
    · intro j hj
      have := hne (j + 1) (Nat.succ_lt_succ hj)
      rwa [Function.iterate_succ_apply] at this
  · rintro ⟨hnD, heq, hne⟩
    refine ⟨by rwa [Function.iterate_succ_apply], ?_⟩
    intro j hj
    cases j with
    | zero => simpa using hnD
    | succ j =>
      rw [Function.iterate_succ_apply]
      exact hne j (Nat.lt_of_succ_lt_succ hj)

private lemma first_zero_iff {M D n : ℕ} : First M D 0 n ↔ n = D := by
  unfold First
  simp

private lemma windowPoly_tail {M D q r : ℕ} (hM : 1 < M) (hr : r ≤ M) :
    windowPoly M D (M * q + r) =
      windowPoly M D (M * q) + Polynomial.X ^ ((M - D) * step M D q) * digitPoly r := by
  unfold windowPoly digitPoly
  rw [Finset.sum_range_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hiM : i < M := lt_of_lt_of_le (Finset.mem_range.mp hi) hr
  rw [step_mul_add hM hiM, pow_add]

private lemma windowPoly_mul {M D : ℕ} (hM : 1 < M) :
    ∀ q : ℕ, windowPoly M D (M * q) =
      (windowPoly M D q).comp (Polynomial.X ^ (M - D)) * digitPoly M := by
  intro q
  induction q with
  | zero => simp [windowPoly]
  | succ q ih =>
    have hmul : M * (q + 1) = M * q + M := by ring
    rw [hmul, windowPoly_tail hM le_rfl, ih]
    unfold windowPoly
    rw [Finset.sum_range_succ, Polynomial.add_comp, Polynomial.X_pow_comp, ← pow_mul, add_mul]

private lemma windowPoly_coeff (M D N t : ℕ) :
    (windowPoly M D N).coeff t =
      ((Finset.range N).filter (fun n => step M D n = t)).card := by
  unfold windowPoly
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_X_pow]
  rw [Finset.sum_boole, Nat.cast_id]
  congr 1
  ext n
  simp [eq_comm]

private lemma histogramLaw_proof {M D : ℕ} (hM : 1 < M) (hDle : D ≤ M) :
    HistogramLaw M D := by
  classical
  constructor
  · intro q r hr
    rw [windowPoly_tail hM hr, windowPoly_mul hM q]
  · intro N h
    simp only [windowPoly_coeff]
    let A : Finset ℕ := (Finset.range N).filter (fun n => First M D h (step M D n))
    have hsum_eq : ∑ t ∈ (Finset.range N).filter (First M D h),
        ((Finset.range N).filter (fun n => step M D n = t)).card = A.card := by
      have hfib := Finset.card_eq_sum_card_fiberwise
        (s := A) (t := (Finset.range N).filter (First M D h)) (f := step M D) (by
          intro n hn
          simp only [A, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hn ⊢
          exact ⟨lt_of_le_of_lt (step_le hM hDle n) hn.1, hn.2⟩)
      rw [hfib]
      refine Finset.sum_congr rfl fun t ht => ?_
      congr 1
      ext n
      rw [Finset.mem_filter] at ht
      simp only [A, Finset.mem_filter]
      constructor
      · rintro ⟨hn, hst⟩
        exact ⟨⟨hn, hst ▸ ht.2⟩, hst⟩
      · rintro ⟨⟨hn, _⟩, hst⟩
        exact ⟨hn, hst⟩
    rw [hsum_eq]
    have herase : (Finset.range N).filter (First M D (h + 1)) = A.erase D := by
      ext n
      simp only [A, Finset.mem_erase, Finset.mem_filter, first_succ_iff]
      tauto
    rw [herase]
    by_cases hDA : D ∈ A
    · have hcond : D < N ∧ First M D h (step M D D) := by
        simpa [A, Finset.mem_filter, Finset.mem_range] using hDA
      rw [if_pos hcond, Finset.card_erase_of_mem hDA]
    · have hcond : ¬ (D < N ∧ First M D h (step M D D)) := by
        simpa [A, Finset.mem_filter, Finset.mem_range] using hDA
      rw [if_neg hcond, Finset.erase_eq_of_notMem hDA, Nat.sub_zero]

private lemma first_pos_and_dvd {M D : ℕ} (hM : 1 < M) (hDpos : 0 < D) (hDle : D ≤ M) :
    ∀ n h, First M D h n → 0 < n ∧ D ∣ n := by
  intro n h ⟨heq, _⟩
  constructor
  · by_contra h0
    have hn0 : n = 0 := by omega
    subst hn0
    rw [iterate_step_zero] at heq
    omega
  · have hmod := iterate_step_modEq hM hDle h n
    rw [heq] at hmod
    exact Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_refl D)))

private lemma first_rigid_case {M D : ℕ} (hM : 1 < M) (hDpos : 0 < D) (hDle : D ≤ M)
    (hcase : D = M ∨ D < M - D) :
    ∀ n h, D ∣ n → (First M D h n ↔ n = D ∧ h = 0) := by
  intro n h hDn
  constructor
  · intro hf
    rcases hcase with hDM | hDlt
    · -- D = M: step M M n = n % M = 0 since M ∣ n
      subst hDM
      have hstep0 : step D D n = 0 := by
        have hdecomp : n = D * (n / D) + n % D := (Nat.div_add_mod n D).symm
        have hmod_lt : n % D < D := Nat.mod_lt n (by omega)
        conv_lhs => rw [hdecomp]
        rw [step_mul_add hM hmod_lt, Nat.sub_self, zero_mul, zero_add]
        exact Nat.mod_eq_zero_of_dvd hDn
      cases h with
      | zero => exact ⟨first_zero_iff.mp hf, rfl⟩
      | succ h =>
        exfalso
        have heq := hf.1
        rw [Function.iterate_succ_apply, hstep0, iterate_step_zero] at heq
        omega
    · -- D < M - D: every x > D has step M D x > D
      have hgt_step : ∀ x : ℕ, D < x → D < step M D x := by
        intro x hx
        by_cases hxM : x < M
        · rw [step_of_lt hM hxM]; exact hx
        · have hdecomp : x = M * (x / M) + x % M := (Nat.div_add_mod x M).symm
          have hmod_lt : x % M < M := Nat.mod_lt x (by omega)
          have hq_pos : 0 < x / M := Nat.div_pos (not_lt.mp hxM) (by omega)
          have hs_pos : 0 < step M D (x / M) := step_pos hM (by omega) (x / M) hq_pos
          rw [hdecomp, step_mul_add hM hmod_lt]
          have : M - D ≤ (M - D) * step M D (x / M) := Nat.le_mul_of_pos_right _ hs_pos
          omega
      have hgt_iter : ∀ j x : ℕ, D < x → D < (step M D)^[j] x := by
        intro j
        induction j with
        | zero => intro x hx; exact hx
        | succ j ih =>
          intro x hx
          rw [Function.iterate_succ_apply]
          exact ih _ (hgt_step x hx)
      have hn_pos : 0 < n := (first_pos_and_dvd hM hDpos hDle n h hf).1
      have hn_ge : D ≤ n := Nat.le_of_dvd hn_pos hDn
      have hn_eq : n = D := by
        by_contra hne
        have hlt := hgt_iter h n (by omega)
        have heq := hf.1
        omega
      subst hn_eq
      cases h with
      | zero => exact ⟨rfl, rfl⟩
      | succ h =>
        exfalso
        exact hf.2 0 (Nat.succ_pos h) rfl
  · rintro ⟨rfl, rfl⟩
    exact first_zero_iff.mpr rfl

private def repOnes (M : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => M * repOnes M k + 1

private lemma step_repOnes {M D : ℕ} (hM : 1 < M) (hB1 : M - D = 1) :
    ∀ k : ℕ, step M D (repOnes M k) = k := by
  intro k
  induction k with
  | zero => exact step_zero M D
  | succ k ih =>
    unfold repOnes
    rw [step_mul_add hM hM, hB1, one_mul, ih]

private lemma repOnes_pos (M : ℕ) : ∀ k : ℕ, 0 < k → 0 < repOnes M k := by
  intro k hk
  cases k with
  | zero => omega
  | succ k => unfold repOnes; omega

private def liftBase (M B : ℕ) (hB : 2 ≤ B) (y : ℕ) : ℕ :=
  if y = 0 then 0 else M * liftBase M B hB (y / B) + y % B
termination_by y
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero ‹_›) (by omega)

private lemma step_liftBase {M D : ℕ} (hM : 1 < M) (hB : 2 ≤ M - D) :
    ∀ y : ℕ, step M D (liftBase M (M - D) hB y) = y := by
  intro y
  induction y using Nat.strong_induction_on with
  | h y ih =>
    unfold liftBase
    split_ifs with hy0
    · subst hy0; exact step_zero M D
    · have hmod_lt : y % (M - D) < M := lt_of_lt_of_le (Nat.mod_lt y (by omega)) (Nat.sub_le M D)
      have hdiv_lt : y / (M - D) < y := Nat.div_lt_self (Nat.pos_of_ne_zero hy0) (by omega)
      rw [step_mul_add hM hmod_lt, ih (y / (M - D)) hdiv_lt]
      exact Nat.div_add_mod y (M - D)

private lemma liftBase_ge_M {M B : ℕ} (hM : 1 < M) (hB : 2 ≤ B) (y : ℕ) (hy : B ≤ y) :
    M ≤ liftBase M B hB y := by
  unfold liftBase
  rw [if_neg (by omega)]
  have hq_pos : 0 < y / B := Nat.div_pos hy (by omega)
  have hpos : 0 < liftBase M B hB (y / B) := by
    have haux : ∀ z : ℕ, 0 < z → 0 < liftBase M B hB z := by
      intro z
      induction z using Nat.strong_induction_on with
      | h z ih =>
        intro hz
        unfold liftBase
        rw [if_neg hz.ne']
        by_cases hzB : z < B
        · rw [Nat.mod_eq_of_lt hzB]; omega
        · have h1 := ih (z / B) (Nat.div_lt_self hz (by omega)) (Nat.div_pos (not_lt.mp hzB) (by omega))
          have : 0 < M * liftBase M B hB (z / B) := Nat.mul_pos (by omega) h1
          omega
    exact haux (y / B) hq_pos
  have : M ≤ M * liftBase M B hB (y / B) := Nat.le_mul_of_pos_right M hpos
  omega

private lemma exists_preimage_ge_M {M D : ℕ} (hM : 1 < M) (hDpos : 0 < D) (hDM : D < M)
    (hBD : M - D ≤ D) (y : ℕ) (hy : D ≤ y) :
    ∃ x : ℕ, M ≤ x ∧ step M D x = y := by
  by_cases hB1 : M - D = 1
  · refine ⟨M * repOnes M y, ?_, ?_⟩
    · have hpos : 0 < repOnes M y := repOnes_pos M y (by omega)
      exact Nat.le_mul_of_pos_right M hpos
    · have h0 : 0 < M := by omega
      have := step_mul_add (M := M) (D := D) (q := repOnes M y) (r := 0) hM h0
      simpa [hB1, step_repOnes hM hB1 y] using this
  · have hB2 : 2 ≤ M - D := by omega
    refine ⟨liftBase M (M - D) hB2 y, ?_, step_liftBase hM hB2 y⟩
    exact liftBase_ge_M hM hB2 y (le_trans hBD hy)

private lemma hitting_and_attainment {M D : ℕ} (hM : 1 < M) (hDpos : 0 < D)
    (hDM : D < M) (hBD : M - D ≤ D) :
    (∀ n, 0 < n → D ∣ n → ∃ h, First M D h n) ∧
    (∀ h, ∃ n, D ≤ n ∧ D ∣ n ∧ First M D h n) := by
  constructor
  · intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn_pos hDn
      by_cases hnD : n = D
      · exact ⟨0, first_zero_iff.mpr hnD⟩
      · obtain ⟨k, rfl⟩ := hDn
        have hk2 : 2 ≤ k := by
          by_contra hlt
          rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
          · simp at hn_pos
          · simp at hnD
        have hgeM : M ≤ D * k := by
          have : D * 2 ≤ D * k := Nat.mul_le_mul_left D hk2
          omega
        have hlt : step M D (D * k) < D * k := step_lt_of_ge hM hDpos hDM.le hgeM
        have hpos : 0 < step M D (D * k) := step_pos hM hDM (D * k) hn_pos
        have hdvd : D ∣ step M D (D * k) := by
          have hmod := step_modEq hM hDM.le (D * k)
          exact Nat.modEq_zero_iff_dvd.mp (hmod.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right D k)))
        obtain ⟨h, hh⟩ := ih (step M D (D * k)) hlt hpos hdvd
        exact ⟨h + 1, first_succ_iff.mpr ⟨hnD, hh⟩⟩
  · intro h
    induction h with
    | zero => exact ⟨D, le_rfl, dvd_refl D, first_zero_iff.mpr rfl⟩
    | succ h ih =>
      obtain ⟨y, hyD, hDy, hfy⟩ := ih
      obtain ⟨x, hxM, hstep⟩ := exists_preimage_ge_M hM hDpos hDM hBD y hyD
      have hxD : D ≤ x := by omega
      have hx_ne : x ≠ D := by omega
      have hDx : D ∣ x := by
        have hmod := step_modEq hM hDM.le x
        rw [hstep] at hmod
        exact Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hDy))
      exact ⟨x, hxD, hDx, first_succ_iff.mpr ⟨hx_ne, hstep ▸ hfy⟩⟩

private lemma step_gt_of_pow_le {M D : ℕ} (hM : 1 < M) (hB2 : 2 ≤ M - D) :
    ∀ L n : ℕ, M ^ L ≤ n → L < step M D n := by
  intro L
  induction L with
  | zero =>
    intro n hn
    have h1 : 1 ≤ n := by simpa using hn
    exact step_pos hM (by omega) n (by omega)
  | succ L ih =>
    intro n hn
    have hq_ge : M ^ L ≤ n / M := by
      have hmul : M * M ^ L ≤ n := by rwa [pow_succ'] at hn
      exact (Nat.le_div_iff_mul_le (by omega)).mpr (by rwa [mul_comm])
    have hih := ih (n / M) hq_ge
    have hdecomp : n = M * (n / M) + n % M := (Nat.div_add_mod n M).symm
    have hmod_lt : n % M < M := Nat.mod_lt n (by omega)
    rw [hdecomp, step_mul_add hM hmod_lt]
    have h2 : 2 * (L + 1) ≤ (M - D) * step M D (n / M) := Nat.mul_le_mul hB2 hih
    omega

private lemma bounded_of_ge_two {M D : ℕ} (hM : 1 < M) (hB2 : 2 ≤ M - D) :
    ∀ h, ∃ N, ∀ n, First M D h n → n < N := by
  intro h
  induction h with
  | zero =>
    refine ⟨D + 1, fun n hn => ?_⟩
    rw [first_zero_iff] at hn
    omega
  | succ h ih =>
    obtain ⟨N, hN⟩ := ih
    refine ⟨M ^ N, fun n hn => ?_⟩
    have hsn : step M D n < N := hN (step M D n) (first_succ_iff.mp hn).2
    by_contra hge
    have := step_gt_of_pow_le hM hB2 N n (not_lt.mp hge)
    omega

private lemma step_mul_pow_of_B_eq_one {M D : ℕ} (hM : 1 < M) (hB1 : M - D = 1) :
    ∀ r z : ℕ, step M D (M ^ r * z) = step M D z := by
  intro r
  induction r with
  | zero => intro z; simp
  | succ r ih =>
    intro z
    rw [pow_succ', mul_assoc]
    have h1 := step_mul_add (M := M) (D := D) (q := M ^ r * z) (r := 0) hM (by omega)
    simpa [hB1, ih z] using h1

private lemma unbounded_of_eq_one {M D : ℕ} (hM : 1 < M) (hDpos : 0 < D) (hB1 : M - D = 1) :
    ∀ h K, ∃ n, K < n ∧ D ∣ n ∧ First M D (h + 1) n := by
  intro h K
  have hDM : D < M := by omega
  have hBD : M - D ≤ D := by omega
  obtain ⟨y, hyD, hDy, hfy⟩ := (hitting_and_attainment hM hDpos hDM hBD).2 h
  let n : ℕ := M ^ (K + 1) * repOnes M y
  have hstep_n : step M D n = y := by
    dsimp only [n]
    rw [step_mul_pow_of_B_eq_one hM hB1, step_repOnes hM hB1]
  have hrep_pos : 0 < repOnes M y := repOnes_pos M y (by omega)
  have hpow_gt : K < M ^ (K + 1) := by
    have h1 : 2 ^ (K + 1) ≤ M ^ (K + 1) := Nat.pow_le_pow_left hM (K + 1)
    have h2 : K + 1 < 2 ^ (K + 1) := Nat.lt_two_pow_self
    omega
  have hKn : K < n := by
    have : M ^ (K + 1) ≤ n := Nat.le_mul_of_pos_right _ hrep_pos
    omega
  have hn_ge_M : M ≤ n := by
    have h1 : M ^ 1 ≤ M ^ (K + 1) := Nat.pow_le_pow_right (by omega) (Nat.succ_pos K)
    have h2 : M ^ (K + 1) ≤ n := Nat.le_mul_of_pos_right _ hrep_pos
    simp only [pow_one] at h1
    omega
  have hDn : D ∣ n := by
    have hmod := step_modEq hM hDM.le n
    rw [hstep_n] at hmod
    exact Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hDy))
  exact ⟨n, hKn, hDn, first_succ_iff.mpr ⟨by omega, hstep_n ▸ hfy⟩⟩

private theorem prove_main : ∀ M D : ℕ, 1 < M → 0 < D → D ≤ M →
    HistogramLaw M D ∧
    (∀ n h, First M D h n → 0 < n ∧ D ∣ n) ∧
    ((D = M ∨ D < M-D) → ∀ n h, D ∣ n → (First M D h n ↔ n = D ∧ h = 0)) ∧
    ((D < M ∧ M-D ≤ D) →
      (∀ n, 0 < n → D ∣ n → ∃ h, First M D h n) ∧
      (∀ h, ∃ n, D ≤ n ∧ D ∣ n ∧ First M D h n)) ∧
    (2 ≤ M-D → ∀ h, ∃ N, ∀ n, First M D h n → n < N) ∧
    (M-D = 1 → ∀ h K, ∃ n, K < n ∧ D ∣ n ∧ First M D (h+1) n) := by
  intro M D hM hDpos hDle
  refine ⟨histogramLaw_proof hM hDle,
    first_pos_and_dvd hM hDpos hDle,
    fun hcase => first_rigid_case hM hDpos hDle hcase,
    fun ⟨hDM, hBD⟩ => hitting_and_attainment hM hDpos hDM hBD,
    fun hB2 => bounded_of_ge_two hM hB2,
    fun hB1 => unbounded_of_eq_one hM hDpos hB1⟩

end OMA.P_opg_distribution_and_upper_bound_of_mimic_numbers

theorem OMA.solution :
    type_of% @OMA.S_opg_distribution_and_upper_bound_of_mimic_numbers.main :=
  OMA.P_opg_distribution_and_upper_bound_of_mimic_numbers.prove_main
