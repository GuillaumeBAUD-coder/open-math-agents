import OMAReductions.R_LonelyRunnerConjecture_lonely_runner_conjecture_R1

/-!
Reduction `LonelyRunnerConjecture.lonely_runner_conjecture.R1.H2.R2` of step `R1.H2`
(primitive, non-lacunary integer Lonely Runner Conjecture for `3 ≤ k ≤ 7`).

Unconditionally proved sorry-free in-file:
1. Full 4-runner (`k = 3`, Betke-Wills 1972) and 5-runner (`k = 4`, Cusick-Pomerance 1984 /
   Bienia-Goddyn-Gvozdjak-Sebo-Tarsi 1998) integer Lonely Runner theorems (`lrc_pos_three`,
   `lrc_nat_four`), together with `k = 1, 2` (`lrc_pos_one`, `lrc_pos_two`).
2. General small-modulus divisibility and parity sieves (`lrc_nat_not_dvd_le`):
   every modulus `1 ≤ d ≤ k + 1` divides at least one speed `w i`.
3. Inductive top-speed gap bound (`lrc_nat_last_speed_bound`): `w (k - 1) < k * w (k - 2)`.
4. General `s`-subset prime-coset shifting sieve (`lrc_nat_prime_coset_sieve`), establishing:
   - `(k - 1)`-subset coprimality for all primes `p`,
   - `(k - 2)`-subset coprimality for all odd primes `p ≥ 3` (`k ≥ 5`),
   - `3`-subset coprimality for `p = 7` and all primes `p ≥ 13` at `k = 6`,
   - `4`-subset coprimality for all primes `p ≥ 7` at `k = 7`.

Remaining three discrete sieved regimes:
- `H1`: 6 runners (`k = 5`, Bohman-Holzman-Kleitman 2001 / Renault 2004).
- `H2`: 7 runners (`k = 6`, Barajas-Serra 2008).
- `H3`: 8 runners (`k = 7`, Rosenfeld 2025).
-/

-- Reduction LonelyRunnerConjecture.lonely_runner_conjecture.R1.H2.R2 of step LonelyRunnerConjecture.lonely_runner_conjecture.R1.H2
-- Credit: @Pampasgras

namespace OMA.R_LonelyRunnerConjecture_lonely_runner_conjecture_R1_H2_R2

def H1 : Prop :=
  ∀ (w : Fin 5 → ℕ),
    (∀ i : Fin 5, 0 < w i) →
    StrictMono w →
    Finset.univ.gcd w = 1 →
    (∀ i₀ : Fin 5, (Finset.univ.erase i₀).gcd w = 1) →
    (∀ S : Finset (Fin 5), S.card = 3 → ∀ p : ℕ, Nat.Prime p → 3 ≤ p → ¬ p ∣ S.gcd w) →
    (∀ d : ℕ, 1 ≤ d → d ≤ 6 → ∃ i : Fin 5, d ∣ w i) →
    w 4 < 5 * w 3 →
    (∃ i j : Fin 5, i.val + 1 = j.val ∧ j.val + 1 < 5 ∧ 4 * w j < 10 * w i) →
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin 5, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((5 + 1 : ℕ) : ℝ)

def H2 : Prop :=
  ∀ (w : Fin 6 → ℕ),
    (∀ i : Fin 6, 0 < w i) →
    StrictMono w →
    Finset.univ.gcd w = 1 →
    (∀ i₀ : Fin 6, (Finset.univ.erase i₀).gcd w = 1) →
    (∀ S : Finset (Fin 6), S.card = 4 → ∀ p : ℕ, Nat.Prime p → 3 ≤ p → ¬ p ∣ S.gcd w) →
    (∀ S : Finset (Fin 6), S.card = 3 → ∀ p : ℕ, Nat.Prime p → (p = 7 ∨ 13 ≤ p) → ¬ p ∣ S.gcd w) →
    (∀ d : ℕ, 1 ≤ d → d ≤ 7 → ∃ i : Fin 6, d ∣ w i) →
    w 5 < 6 * w 4 →
    (∃ i j : Fin 6, i.val + 1 = j.val ∧ j.val + 1 < 6 ∧ 5 * w j < 12 * w i) →
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin 6, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((6 + 1 : ℕ) : ℝ)

def H3 : Prop :=
  ∀ (w : Fin 7 → ℕ),
    (∀ i : Fin 7, 0 < w i) →
    StrictMono w →
    Finset.univ.gcd w = 1 →
    (∀ i₀ : Fin 7, (Finset.univ.erase i₀).gcd w = 1) →
    (∀ S : Finset (Fin 7), S.card = 5 → ∀ p : ℕ, Nat.Prime p → 3 ≤ p → ¬ p ∣ S.gcd w) →
    (∀ S : Finset (Fin 7), S.card = 4 → ∀ p : ℕ, Nat.Prime p → 7 ≤ p → ¬ p ∣ S.gcd w) →
    (∀ d : ℕ, 1 ≤ d → d ≤ 8 → ∃ i : Fin 7, d ∣ w i) →
    w 6 < 7 * w 5 →
    (∃ i j : Fin 7, i.val + 1 = j.val ∧ j.val + 1 < 7 ∧ 6 * w j < 14 * w i) →
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin 7, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((7 + 1 : ℕ) : ℝ)

section ReductionProofs

noncomputable section

private lemma unitAddCircle_dist_ge_of_Icc (x δ : ℝ) (k : ℤ)
    (h1 : (k : ℝ) + δ ≤ x) (h2 : x ≤ (k : ℝ) + 1 - δ) :
    dist (x : UnitAddCircle) 0 ≥ δ := by
  rw [ge_iff_le, dist_zero_right, UnitAddCircle.norm_eq]
  set m : ℤ := round x
  rcases le_or_gt m k with hmk | hkm
  · have hmk' : (m : ℝ) ≤ (k : ℝ) := Int.cast_le.mpr hmk
    have hle : δ ≤ x - (m : ℝ) := by linarith
    exact hle.trans (le_abs_self _)
  · have hkm1 : k + 1 ≤ m := Int.add_one_le_iff.mpr hkm
    have hkm' : (k : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hkm1
    have hle : δ ≤ -(x - (m : ℝ)) := by linarith
    exact hle.trans (neg_le_abs _)

private lemma unitAddCircle_dist_ge_of_Icc_zero (x δ : ℝ)
    (h1 : δ ≤ x) (h2 : x ≤ 1 - δ) :
    dist (x : UnitAddCircle) 0 ≥ δ := by
  refine unitAddCircle_dist_ge_of_Icc x δ 0 ?_ ?_
  · simp [h1]
  · simp [h2]

private lemma unitAddCircle_add_int (x : ℝ) (z : ℤ) :
    ((x + (z : ℝ) : ℝ) : UnitAddCircle) = (x : UnitAddCircle) := by
  rw [QuotientAddGroup.mk_add]
  have h1 : ((1 : ℝ) : UnitAddCircle) = 0 :=
    (QuotientAddGroup.eq_zero_iff (1 : ℝ)).mpr (AddSubgroup.mem_zmultiples (1 : ℝ))
  have hz : (((z : ℤ) : ℝ) : UnitAddCircle) = 0 := by
    rw [← zsmul_one z, QuotientAddGroup.mk_zsmul, h1, smul_zero]
  rw [hz, add_zero]

private lemma unitAddCircle_add_nat (x : ℝ) (n : ℕ) :
    ((x + (n : ℝ) : ℝ) : UnitAddCircle) = (x : UnitAddCircle) := by
  have h : (n : ℝ) = ((n : ℤ) : ℝ) := (Int.cast_natCast n).symm
  rw [h]
  exact unitAddCircle_add_int x (n : ℤ)

private lemma unitAddCircle_norm_le_abs (u : ℝ) :
    ‖(u : UnitAddCircle)‖ ≤ |u| := by
  rw [UnitAddCircle.norm_eq]
  rcases le_or_gt (1 / 2 : ℝ) |u| with hbig | hsmall
  · exact le_trans (abs_sub_round u) hbig
  · have hu_bounds := abs_lt.mp hsmall
    have hr0 : round u = 0 := by
      rw [round_eq]
      exact Int.floor_eq_iff.mpr ⟨by linarith [hu_bounds.1], by linarith [hu_bounds.2]⟩
    rw [hr0, Int.cast_zero, sub_zero]

private lemma unitAddCircle_dist_le_abs_sub (x y : ℝ) :
    dist (x : UnitAddCircle) (y : UnitAddCircle) ≤ |x - y| := by
  rw [dist_eq_norm, ← QuotientAddGroup.mk_sub]
  exact unitAddCircle_norm_le_abs (x - y)

private lemma exists_subinterval_dist_ge (A B δ L : ℝ)
    (hδ : 0 ≤ δ) (hL : 0 ≤ L) (hLδ : L + 2 * δ ≤ 1) (hBA : 2 * L + 2 * δ ≤ B - A) :
    ∃ C D : ℝ, ∃ m : ℤ,
      A ≤ C ∧ D ≤ B ∧ D - C = L ∧ (m : ℝ) + δ ≤ C ∧ D ≤ (m : ℝ) + 1 - δ := by
  set k : ℤ := ⌊A⌋
  have hk1 : (k : ℝ) ≤ A := Int.floor_le A
  have hk2 : A < (k : ℝ) + 1 := Int.lt_floor_add_one A
  rcases le_or_gt A ((k : ℝ) + δ) with hA1 | hA1
  · refine ⟨(k : ℝ) + δ, (k : ℝ) + δ + L, k, hA1, ?_, by ring, le_rfl, ?_⟩
    · linarith
    · linarith
  · rcases le_or_gt (A + L) ((k : ℝ) + 1 - δ) with hA2 | hA2
    · refine ⟨A, A + L, k, le_rfl, ?_, by ring, hA1.le, hA2⟩
      linarith
    · refine ⟨(k : ℝ) + 1 + δ, (k : ℝ) + 1 + δ + L, k + 1, ?_, ?_, by ring, ?_, ?_⟩
      · linarith
      · linarith
      · push_cast; linarith
      · push_cast; linarith

private lemma lrc_pos_one (v : Fin 1 → ℝ) (hv : ∀ i : Fin 1, 0 < v i) :
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin 1, dist ((t * v i : ℝ) : UnitAddCircle) 0 ≥ 1 / ((1 + 1 : ℕ) : ℝ) := by
  have hv0 : 0 < v 0 := hv 0
  refine ⟨1 / (2 * v 0), by positivity, fun i => ?_⟩
  have hi : i = 0 := Subsingleton.elim i 0
  rw [hi]
  have hmul : 1 / (2 * v 0) * v 0 = (1 : ℝ) / 2 := by field_simp [ne_of_gt hv0]
  rw [hmul]
  have hcast : (1 : ℝ) / ((1 + 1 : ℕ) : ℝ) = 1 / 2 := by norm_num
  rw [hcast]
  exact unitAddCircle_dist_ge_of_Icc_zero (1 / 2) (1 / 2) (by norm_num) (by norm_num)

private lemma lrc_pos_two (v : Fin 2 → ℝ) (hv : ∀ i : Fin 2, 0 < v i) (hmono : StrictMono v) :
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin 2, dist ((t * v i : ℝ) : UnitAddCircle) 0 ≥ 1 / ((2 + 1 : ℕ) : ℝ) := by
  have hv0 : 0 < v 0 := hv 0
  have hv1 : 0 < v 1 := hv 1
  have hv01 : v 0 < v 1 := hmono (by decide)
  have hcast : (1 : ℝ) / ((2 + 1 : ℕ) : ℝ) = 1 / 3 := by norm_num
  rw [hcast]
  rcases lt_or_ge (v 1) (2 * v 0) with hlt | hge
  · refine ⟨1 / (3 * v 0), by positivity, fun i => ?_⟩
    fin_cases i
    · change dist ((1 / (3 * v 0) * v 0 : ℝ) : UnitAddCircle) 0 ≥ 1 / 3
      have hmul : 1 / (3 * v 0) * v 0 = (1 : ℝ) / 3 := by field_simp [ne_of_gt hv0]
      rw [hmul]
      exact unitAddCircle_dist_ge_of_Icc_zero (1 / 3) (1 / 3) (by norm_num) (by norm_num)
    · change dist ((1 / (3 * v 0) * v 1 : ℝ) : UnitAddCircle) 0 ≥ 1 / 3
      have h_eq : 1 / (3 * v 0) * v 1 = v 1 / (3 * v 0) := one_div_mul_eq_div (3 * v 0) (v 1)
      rw [h_eq]
      have hlo : (1 : ℝ) / 3 ≤ v 1 / (3 * v 0) := by rw [le_div_iff₀ (by positivity)]; linarith
      have hhi : v 1 / (3 * v 0) ≤ 1 - 1 / 3 := by rw [div_le_iff₀ (by positivity)]; linarith
      exact unitAddCircle_dist_ge_of_Icc_zero _ (1 / 3) hlo hhi
  · have hlen : 2 * (0 : ℝ) + 2 * (1 / 3 : ℝ) ≤
        (2 * v 1) / (3 * v 0) - v 1 / (3 * v 0) := by
      have hsub : (2 * v 1) / (3 * v 0) - v 1 / (3 * v 0) = v 1 / (3 * v 0) := by ring
      rw [hsub, le_div_iff₀ (by positivity)]
      linarith
    obtain ⟨C, D, m, hAC, hDB, hDC, hm1, hm2⟩ :=
      exists_subinterval_dist_ge (v 1 / (3 * v 0)) ((2 * v 1) / (3 * v 0)) (1 / 3) 0
        (by norm_num) le_rfl (by norm_num) hlen
    have hCD : C = D := by linarith
    have hC_nonneg : 0 ≤ C := le_trans (by positivity) hAC
    refine ⟨C / v 1, by positivity, fun i => ?_⟩
    fin_cases i
    · change dist ((C / v 1 * v 0 : ℝ) : UnitAddCircle) 0 ≥ 1 / 3
      have h1 : v 1 ≤ C * (3 * v 0) := (div_le_iff₀ (by positivity)).mp hAC
      have h2 : C * (3 * v 0) ≤ 2 * v 1 := (le_div_iff₀ (by positivity)).mp (hCD.symm ▸ hDB)
      rw [div_mul_eq_mul_div C (v 1) (v 0)]
      have hlo : (1 : ℝ) / 3 ≤ (C * v 0) / v 1 := by rw [le_div_iff₀ hv1]; linarith
      have hhi : (C * v 0) / v 1 ≤ 1 - 1 / 3 := by rw [div_le_iff₀ hv1]; linarith
      exact unitAddCircle_dist_ge_of_Icc_zero _ (1 / 3) hlo hhi
    · change dist ((C / v 1 * v 1 : ℝ) : UnitAddCircle) 0 ≥ 1 / 3
      rw [div_mul_cancel₀ C (ne_of_gt hv1)]
      exact unitAddCircle_dist_ge_of_Icc C (1 / 3) m hm1 (hCD ▸ hm2)

private lemma lrc_lacunary (k : ℕ) (hk : 3 ≤ k) (v : Fin k → ℝ)
    (hv_pos : ∀ i : Fin k, 0 < v i) (hv_mono : StrictMono v)
    (hlac : ∀ i j : Fin k, i.val + 1 = j.val → j.val + 1 < k →
      ((k : ℝ) - 1) * v j ≥ 2 * (k : ℝ) * v i) :
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin k, dist ((t * v i : ℝ) : UnitAddCircle) 0 ≥ 1 / ((k + 1 : ℕ) : ℝ) := by
  let δ : ℝ := 1 / ((k + 1 : ℕ) : ℝ)
  let L : ℝ := ((k : ℝ) - 1) / ((k + 1 : ℕ) : ℝ)
  have hk_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hδ_nonneg : 0 ≤ δ := by positivity
  have hL_nonneg : 0 ≤ L := by
    refine div_nonneg ?_ hk_pos.le
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
    linarith
  have hLδ_sum : L + 2 * δ ≤ 1 := by
    have heq : L + 2 * δ = 1 := by dsimp [L, δ]; push_cast; field_simp [ne_of_gt hk_pos]; ring
    exact heq.le
  have h_nested : ∀ (j : ℕ) (hj : j + 1 < k),
      ∃ a b : ℝ, 0 ≤ a ∧
        b - a = L / v ⟨j, by omega⟩ ∧
        ∀ (m : Fin k), m.val ≤ j → ∀ t : ℝ, a ≤ t → t ≤ b →
          dist ((t * v m : ℝ) : UnitAddCircle) 0 ≥ δ := by
    intro j
    induction j with
    | zero =>
      intro hj
      let i0 : Fin k := ⟨0, by omega⟩
      have hv0 : 0 < v i0 := hv_pos i0
      refine ⟨δ / v i0, (1 - δ) / v i0, by positivity, ?_, ?_⟩
      · have h1 : (1 - δ) / v i0 - δ / v i0 = (1 - 2 * δ) / v i0 := by ring
        rw [h1]; congr 1; dsimp [L, δ]; push_cast; field_simp [ne_of_gt hk_pos]; ring
      · intro m hm t hta htb
        have hm_eq : m = i0 := Fin.ext (by dsimp [i0]; omega)
        rw [hm_eq]
        have hlo : δ ≤ t * v i0 := by have := (div_le_iff₀ hv0).mp hta; linarith
        have hhi : t * v i0 ≤ 1 - δ := by have := (le_div_iff₀ hv0).mp htb; linarith
        exact unitAddCircle_dist_ge_of_Icc_zero (t * v i0) δ hlo hhi
    | succ j ih =>
      intro hj_succ
      obtain ⟨a, b, ha0, hba, h_safe⟩ := ih (by omega)
      let ij : Fin k := ⟨j, by omega⟩
      let ij1 : Fin k := ⟨j + 1, by omega⟩
      have hvj : 0 < v ij := hv_pos ij
      have hvj1 : 0 < v ij1 := hv_pos ij1
      have hlac_step : ((k : ℝ) - 1) * v ij1 ≥ 2 * (k : ℝ) * v ij := hlac ij ij1 rfl hj_succ
      have hBA : 2 * L + 2 * δ ≤ v ij1 * b - v ij1 * a := by
        have h1 : v ij1 * b - v ij1 * a = v ij1 * (L / v ij) := by rw [← mul_sub, hba]
        have h2 : 2 * L + 2 * δ = (2 * (k : ℝ)) / ((k + 1 : ℕ) : ℝ) := by
          dsimp [L, δ]; push_cast; field_simp [ne_of_gt hk_pos]; ring
        have h3 : v ij1 * (L / v ij) = (((k : ℝ) - 1) * v ij1) / (((k + 1 : ℕ) : ℝ) * v ij) := by
          dsimp [L]; ring
        rw [h1, h2, h3, div_le_div_iff₀ hk_pos (by positivity)]
        nlinarith
      obtain ⟨C, D, z, hAC, hDB, hDC, hz1, hz2⟩ :=
        exists_subinterval_dist_ge (v ij1 * a) (v ij1 * b) δ L hδ_nonneg hL_nonneg hLδ_sum hBA
      have ha_le : a ≤ C / v ij1 := (le_div_iff₀ hvj1).mpr (by linarith)
      have hb_le : D / v ij1 ≤ b := (div_le_iff₀ hvj1).mpr (by linarith)
      refine ⟨C / v ij1, D / v ij1, le_trans ha0 ha_le, ?_, ?_⟩
      · rw [← sub_div, hDC]
      · intro m hm t hta htb
        rcases Nat.of_le_succ hm with hm_le | hm_eq
        · exact h_safe m hm_le t (le_trans ha_le hta) (le_trans htb hb_le)
        · have hm_fin : m = ij1 := Fin.ext hm_eq
          rw [hm_fin]
          have hCt : C ≤ t * v ij1 := (div_le_iff₀ hvj1).mp hta
          have htD : t * v ij1 ≤ D := (le_div_iff₀ hvj1).mp htb
          exact unitAddCircle_dist_ge_of_Icc (t * v ij1) δ z (le_trans hz1 hCt) (le_trans htD hz2)
  obtain ⟨a, b, ha0, hba, h_safe⟩ := h_nested (k - 2) (by omega)
  let iprev : Fin k := ⟨k - 2, by omega⟩
  let ilast : Fin k := ⟨k - 1, by omega⟩
  have hv_prev : 0 < v iprev := hv_pos iprev
  have hv_last : 0 < v ilast := hv_pos ilast
  have hv_lt : v iprev < v ilast := hv_mono (by rw [Fin.lt_def]; dsimp [iprev, ilast]; omega)
  have h2δ_le_1 : 0 + 2 * δ ≤ 1 := by linarith
  have hBA_last : 2 * (0 : ℝ) + 2 * δ ≤ v ilast * b - v ilast * a := by
    have h1 : v ilast * b - v ilast * a = (v ilast / v iprev) * L := by rw [← mul_sub, hba]; ring
    have h_ratio : 1 ≤ v ilast / v iprev := (one_le_div hv_prev).mpr hv_lt.le
    have hL_le : 1 * L ≤ (v ilast / v iprev) * L := mul_le_mul_of_nonneg_right h_ratio hL_nonneg
    have h2δ_le_L : 2 * δ ≤ L := by
      dsimp [δ, L]; rw [mul_one_div]
      refine div_le_div_of_nonneg_right ?_ hk_pos.le
      have hk3' : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      linarith
    linarith
  obtain ⟨C, D, z, hAC, hDB, hDC, hz1, hz2⟩ :=
    exists_subinterval_dist_ge (v ilast * a) (v ilast * b) δ 0 hδ_nonneg le_rfl h2δ_le_1 hBA_last
  have hCD : C = D := by linarith
  have ha_t : a ≤ C / v ilast := (le_div_iff₀ hv_last).mpr (by linarith)
  have ht_b : C / v ilast ≤ b := (div_le_iff₀ hv_last).mpr (by linarith)
  refine ⟨C / v ilast, le_trans ha0 ha_t, fun m => ?_⟩
  rcases le_or_gt m.val (k - 2) with hm_le | hm_gt
  · exact h_safe m hm_le (C / v ilast) ha_t ht_b
  · have hm_eq : m = ilast := Fin.ext (by dsimp [ilast]; omega)
    rw [hm_eq, div_mul_cancel₀ C (ne_of_gt hv_last)]
    exact unitAddCircle_dist_ge_of_Icc C δ z hz1 (hCD ▸ hz2)

-- Betke-Wills (1972) unconditional solution for 4 total runners (k = 3).
private lemma lrc_pos_three (v : Fin 3 → ℝ) (hv : ∀ i : Fin 3, 0 < v i) (hmono : StrictMono v) :
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin 3, dist ((t * v i : ℝ) : UnitAddCircle) 0 ≥ 1 / ((3 + 1 : ℕ) : ℝ) := by
  have hv0 : 0 < v 0 := hv 0
  have hv1 : 0 < v 1 := hv 1
  have hv2 : 0 < v 2 := hv 2
  have h01 : v 0 < v 1 := hmono (by decide)
  have h12 : v 1 < v 2 := hmono (by decide)
  rcases le_or_gt (3 * v 0) (v 1) with hlac01 | hlt3
  · refine lrc_lacunary 3 (by omega) v hv hmono ?_
    intro i j hij hj_lt
    have hi0 : i = 0 := Fin.ext (by omega)
    have hj1 : j = 1 := Fin.ext (by omega)
    rw [hi0, hj1]; push_cast; linarith
  · have hcast : (1 : ℝ) / ((3 + 1 : ℕ) : ℝ) = 1 / 4 := by norm_num
    rw [hcast]
    rcases le_or_gt (7 * v 0) (3 * v 1) with hge7 | hlt7
    · have hlen : 2 * (0 : ℝ) + 2 * (1 / 4 : ℝ) ≤
          v 2 * (7 / (4 * v 1)) - v 2 * (5 / (4 * v 1)) := by
        have hsub : v 2 * (7 / (4 * v 1)) - v 2 * (5 / (4 * v 1)) = v 2 / (2 * v 1) := by ring
        rw [hsub, le_div_iff₀ (by positivity)]; linarith
      obtain ⟨C, D, z, hAC, hDB, hDC, hz1, hz2⟩ :=
        exists_subinterval_dist_ge (v 2 * (5 / (4 * v 1))) (v 2 * (7 / (4 * v 1))) (1 / 4) 0
          (by norm_num) le_rfl (by norm_num) hlen
      have hCD : C = D := by linarith
      have ha_t : 5 / (4 * v 1) ≤ C / v 2 := (le_div_iff₀ hv2).mpr (by linarith)
      have ht_b : C / v 2 ≤ 7 / (4 * v 1) := (div_le_iff₀ hv2).mpr (by linarith)
      refine ⟨C / v 2, le_trans (by positivity) ha_t, fun i => ?_⟩
      fin_cases i
      · change dist ((C / v 2 * v 0 : ℝ) : UnitAddCircle) 0 ≥ 1 / 4
        have hlo : (1 : ℝ) / 4 ≤ C / v 2 * v 0 := by
          have h1 : 5 * v 0 / (4 * v 1) ≤ C / v 2 * v 0 := by
            have := mul_le_mul_of_nonneg_right ha_t hv0.le
            linarith [show 5 / (4 * v 1) * v 0 = 5 * v 0 / (4 * v 1) by ring]
          have h2 : (1 : ℝ) / 4 ≤ 5 * v 0 / (4 * v 1) := by
            rw [div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
          exact le_trans h2 h1
        have hhi : C / v 2 * v 0 ≤ 1 - 1 / 4 := by
          have h1 : C / v 2 * v 0 ≤ 7 * v 0 / (4 * v 1) := by
            have := mul_le_mul_of_nonneg_right ht_b hv0.le
            linarith [show 7 / (4 * v 1) * v 0 = 7 * v 0 / (4 * v 1) by ring]
          have h2 : 7 * v 0 / (4 * v 1) ≤ 1 - 1 / 4 := by
            rw [div_le_iff₀ (by positivity)]; linarith
          exact le_trans h1 h2
        exact unitAddCircle_dist_ge_of_Icc_zero _ (1 / 4) hlo hhi
      · change dist ((C / v 2 * v 1 : ℝ) : UnitAddCircle) 0 ≥ 1 / 4
        have hlo : ((1 : ℤ) : ℝ) + 1 / 4 ≤ C / v 2 * v 1 := by
          have := (div_le_iff₀ (by positivity)).mp ha_t; push_cast; linarith
        have hhi : C / v 2 * v 1 ≤ ((1 : ℤ) : ℝ) + 1 - 1 / 4 := by
          have := (le_div_iff₀ (by positivity)).mp ht_b; push_cast; linarith
        exact unitAddCircle_dist_ge_of_Icc _ (1 / 4) 1 hlo hhi
      · change dist ((C / v 2 * v 2 : ℝ) : UnitAddCircle) 0 ≥ 1 / 4
        rw [div_mul_cancel₀ C (ne_of_gt hv2)]
        exact unitAddCircle_dist_ge_of_Icc C (1 / 4) z hz1 (hCD ▸ hz2)
    · rcases le_or_gt (v 2) (3 * v 0) with hle3 | hgt3
      · refine ⟨1 / (4 * v 0), by positivity, fun i => ?_⟩
        fin_cases i
        · change dist ((1 / (4 * v 0) * v 0 : ℝ) : UnitAddCircle) 0 ≥ 1 / 4
          have hmul : 1 / (4 * v 0) * v 0 = (1 : ℝ) / 4 := by field_simp [ne_of_gt hv0]
          rw [hmul]
          exact unitAddCircle_dist_ge_of_Icc_zero (1 / 4) (1 / 4) (by norm_num) (by norm_num)
        · change dist ((1 / (4 * v 0) * v 1 : ℝ) : UnitAddCircle) 0 ≥ 1 / 4
          rw [one_div_mul_eq_div]
          exact unitAddCircle_dist_ge_of_Icc_zero _ (1 / 4)
            ((div_le_div_iff₀ (by norm_num) (by positivity)).mpr (by linarith))
            ((div_le_iff₀ (by positivity)).mpr (by linarith))
        · change dist ((1 / (4 * v 0) * v 2 : ℝ) : UnitAddCircle) 0 ≥ 1 / 4
          rw [one_div_mul_eq_div]
          exact unitAddCircle_dist_ge_of_Icc_zero _ (1 / 4)
            ((div_le_div_iff₀ (by norm_num) (by positivity)).mpr (by linarith))
            ((div_le_iff₀ (by positivity)).mpr (by linarith))
      · rcases le_or_gt (2 * v 0 * v 1) (v 2 * (3 * v 0 - v 1)) with hI1_long | hI1_short
        · have hlen : 2 * (0 : ℝ) + 2 * (1 / 4 : ℝ) ≤
              v 2 * (3 / (4 * v 1)) - v 2 * (1 / (4 * v 0)) := by
            have hsub : v 2 * (3 / (4 * v 1)) - v 2 * (1 / (4 * v 0)) =
                v 2 * (3 * v 0 - v 1) / (4 * v 0 * v 1) := by
              field_simp [ne_of_gt hv0, ne_of_gt hv1]
            rw [hsub, le_div_iff₀ (by positivity)]; linarith
          obtain ⟨C, D, z, hAC, hDB, hDC, hz1, hz2⟩ :=
            exists_subinterval_dist_ge (v 2 * (1 / (4 * v 0))) (v 2 * (3 / (4 * v 1))) (1 / 4) 0
              (by norm_num) le_rfl (by norm_num) hlen
          have hCD : C = D := by linarith
          have ha_t : 1 / (4 * v 0) ≤ C / v 2 := (le_div_iff₀ hv2).mpr (by linarith)
          have ht_b : C / v 2 ≤ 3 / (4 * v 1) := (div_le_iff₀ hv2).mpr (by linarith)
          refine ⟨C / v 2, le_trans (by positivity) ha_t, fun i => ?_⟩
          fin_cases i
          · change dist ((C / v 2 * v 0 : ℝ) : UnitAddCircle) 0 ≥ 1 / 4
            have hlo : (1 : ℝ) / 4 ≤ C / v 2 * v 0 := by
              have := (div_le_iff₀ (by positivity)).mp ha_t; linarith
            have hhi : C / v 2 * v 0 ≤ 1 - 1 / 4 := by
              have h1 := mul_le_mul_of_nonneg_right ht_b hv0.le
              have h2 : 3 / (4 * v 1) * v 0 ≤ 3 / 4 := by
                rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
              linarith
            exact unitAddCircle_dist_ge_of_Icc_zero _ (1 / 4) hlo hhi
          · change dist ((C / v 2 * v 1 : ℝ) : UnitAddCircle) 0 ≥ 1 / 4
            have hlo : (1 : ℝ) / 4 ≤ C / v 2 * v 1 := by
              have h1 := mul_le_mul_of_nonneg_right ha_t hv1.le
              have h2 : (1 : ℝ) / 4 ≤ 1 / (4 * v 0) * v 1 := by
                rw [one_div_mul_eq_div, div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
              exact le_trans h2 h1
            have hhi : C / v 2 * v 1 ≤ 1 - 1 / 4 := by
              have := (le_div_iff₀ (by positivity)).mp ht_b; linarith
            exact unitAddCircle_dist_ge_of_Icc_zero _ (1 / 4) hlo hhi
          · change dist ((C / v 2 * v 2 : ℝ) : UnitAddCircle) 0 ≥ 1 / 4
            rw [div_mul_cancel₀ C (ne_of_gt hv2)]
            exact unitAddCircle_dist_ge_of_Icc C (1 / 4) z hz1 (hCD ▸ hz2)
        · rcases le_or_gt (5 * v 1) (3 * v 2) with hge5 | hlt5
          · rcases le_or_gt (3 * v 2) (7 * v 1) with hle7' | hgt7'
            · refine ⟨3 / (4 * v 1), by positivity, fun i => ?_⟩
              fin_cases i
              · change dist ((3 / (4 * v 1) * v 0 : ℝ) : UnitAddCircle) 0 ≥ 1 / 4
                rw [div_mul_eq_mul_div]
                exact unitAddCircle_dist_ge_of_Icc_zero _ (1 / 4)
                  ((div_le_div_iff₀ (by norm_num) (by positivity)).mpr (by linarith))
                  ((div_le_iff₀ (by positivity)).mpr (by linarith))
              · change dist ((3 / (4 * v 1) * v 1 : ℝ) : UnitAddCircle) 0 ≥ 1 / 4
                have hmul : 3 / (4 * v 1) * v 1 = (3 : ℝ) / 4 := by field_simp [ne_of_gt hv1]
                rw [hmul]
                exact unitAddCircle_dist_ge_of_Icc_zero (3 / 4) (1 / 4) (by norm_num) (by norm_num)
              · change dist ((3 / (4 * v 1) * v 2 : ℝ) : UnitAddCircle) 0 ≥ 1 / 4
                rw [div_mul_eq_mul_div]
                refine unitAddCircle_dist_ge_of_Icc _ (1 / 4) 1 ?_ ?_
                · rw [le_div_iff₀ (by positivity)]; push_cast; linarith
                · rw [div_le_iff₀ (by positivity)]; push_cast; linarith
            · have hv2_lt7 : v 2 < 7 * v 0 := by nlinarith
              refine ⟨7 / (4 * v 2), by positivity, fun i => ?_⟩
              fin_cases i
              · change dist ((7 / (4 * v 2) * v 0 : ℝ) : UnitAddCircle) 0 ≥ 1 / 4
                rw [div_mul_eq_mul_div]
                exact unitAddCircle_dist_ge_of_Icc_zero _ (1 / 4)
                  ((div_le_div_iff₀ (by norm_num) (by positivity)).mpr (by linarith))
                  ((div_le_iff₀ (by positivity)).mpr (by nlinarith))
              · change dist ((7 / (4 * v 2) * v 1 : ℝ) : UnitAddCircle) 0 ≥ 1 / 4
                rw [div_mul_eq_mul_div]
                exact unitAddCircle_dist_ge_of_Icc_zero _ (1 / 4)
                  ((div_le_div_iff₀ (by norm_num) (by positivity)).mpr (by nlinarith))
                  ((div_le_iff₀ (by positivity)).mpr (by linarith))
              · change dist ((7 / (4 * v 2) * v 2 : ℝ) : UnitAddCircle) 0 ≥ 1 / 4
                have hmul : 7 / (4 * v 2) * v 2 = (7 : ℝ) / 4 := by field_simp [ne_of_gt hv2]
                rw [hmul]
                exact unitAddCircle_dist_ge_of_Icc (7 / 4) (1 / 4) 1
                  (by push_cast; norm_num) (by push_cast; norm_num)
          · refine ⟨9 / (4 * v 2), by positivity, fun i => ?_⟩
            fin_cases i
            · change dist ((9 / (4 * v 2) * v 0 : ℝ) : UnitAddCircle) 0 ≥ 1 / 4
              rw [div_mul_eq_mul_div]
              exact unitAddCircle_dist_ge_of_Icc_zero _ (1 / 4)
                ((div_le_div_iff₀ (by norm_num) (by positivity)).mpr (by linarith))
                ((div_le_iff₀ (by positivity)).mpr (by linarith))
            · change dist ((9 / (4 * v 2) * v 1 : ℝ) : UnitAddCircle) 0 ≥ 1 / 4
              rw [div_mul_eq_mul_div]
              refine unitAddCircle_dist_ge_of_Icc _ (1 / 4) 1 ?_ ?_
              · rw [le_div_iff₀ (by positivity)]; push_cast; linarith
              · rw [div_le_iff₀ (by positivity)]; push_cast; linarith
            · change dist ((9 / (4 * v 2) * v 2 : ℝ) : UnitAddCircle) 0 ≥ 1 / 4
              have hmul : 9 / (4 * v 2) * v 2 = (9 : ℝ) / 4 := by field_simp [ne_of_gt hv2]
              rw [hmul]
              exact unitAddCircle_dist_ge_of_Icc (9 / 4) (1 / 4) 2
                (by push_cast; norm_num) (by push_cast; norm_num)

private lemma lrc_lacunary_nat (m : ℕ) (hm3 : 3 ≤ m) (u : Fin m → ℕ)
    (hu_pos : ∀ i : Fin m, 0 < u i) (hu_mono : StrictMono u)
    (h_not_nonlac : ¬ ∃ i j : Fin m, i.val + 1 = j.val ∧ j.val + 1 < m ∧
      (m - 1) * u j < 2 * m * u i) :
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin m, dist ((t * (u i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((m + 1 : ℕ) : ℝ) := by
  refine lrc_lacunary m hm3 (fun i => (u i : ℝ))
    (fun i => Nat.cast_pos.mpr (hu_pos i))
    (fun i j hij => Nat.cast_lt.mpr (hu_mono hij)) ?_
  intro i j hij hj_lt
  have h_ge : 2 * m * u i ≤ (m - 1) * u j := by
    by_contra hlt; exact h_not_nonlac ⟨i, j, hij, hj_lt, Nat.lt_of_not_le hlt⟩
  have h_cast : ((2 * m * u i : ℕ) : ℝ) ≤ (((m - 1) * u j : ℕ) : ℝ) := by exact_mod_cast h_ge
  have hm_sub : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
  push_cast at h_cast; rw [hm_sub] at h_cast; exact h_cast

private lemma lrc_nat_gcd_reduction (m : ℕ) (hm : 1 ≤ m) (w : Fin m → ℕ)
    (hw_pos : ∀ i : Fin m, 0 < w i) (hw_mono : StrictMono w)
    (h_prim : ∀ (w' : Fin m → ℕ), (∀ i : Fin m, 0 < w' i) → StrictMono w' →
      Finset.univ.gcd w' = 1 →
      ∃ t : ℝ, t ≥ 0 ∧
        ∀ i : Fin m, dist ((t * (w' i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((m + 1 : ℕ) : ℝ)) :
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin m, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((m + 1 : ℕ) : ℝ) := by
  let g : ℕ := Finset.univ.gcd w
  have i0_mem : (⟨0, by omega⟩ : Fin m) ∈ (Finset.univ : Finset (Fin m)) := Finset.mem_univ _
  have hg_ne : g ≠ 0 := fun hg0 =>
    Nat.ne_of_gt (hw_pos ⟨0, by omega⟩) ((Finset.gcd_eq_zero_iff.mp hg0) _ i0_mem)
  let w' : Fin m → ℕ := fun i => w i / g
  have hw_mul : ∀ i : Fin m, g * w' i = w i :=
    fun i => Nat.mul_div_cancel' (Finset.gcd_dvd (Finset.mem_univ i))
  have hw'_pos : ∀ i : Fin m, 0 < w' i := by
    intro i
    rcases Nat.eq_zero_or_pos (w' i) with hw'0 | hpos
    · exfalso; exact Nat.ne_of_gt (hw_pos i) (by rw [← hw_mul i, hw'0, mul_zero])
    · exact hpos
  have hw'_mono : StrictMono w' := fun i j hij =>
    lt_of_mul_lt_mul_left' (by rw [hw_mul i, hw_mul j]; exact hw_mono hij)
  have hw'_gcd : Finset.univ.gcd w' = 1 := by
    apply Nat.dvd_one.mp
    have hdvd_g : g * Finset.univ.gcd w' ∣ g * 1 := by
      rw [mul_one]; refine Finset.dvd_gcd fun i hi => ?_
      rw [← hw_mul i]; exact mul_dvd_mul_left g (Finset.gcd_dvd hi)
    exact (mul_dvd_mul_iff_left hg_ne).mp hdvd_g
  obtain ⟨t', ht'0, ht'⟩ := h_prim w' hw'_pos hw'_mono hw'_gcd
  refine ⟨t' / (g : ℝ), by positivity, fun i => ?_⟩
  have hwi_cast : (w i : ℝ) = (g : ℝ) * (w' i : ℝ) := by exact_mod_cast (hw_mul i).symm
  have h_scale : t' / (g : ℝ) * (w i : ℝ) = t' * (w' i : ℝ) := by
    rw [hwi_cast]; field_simp [Nat.cast_ne_zero.mpr hg_ne]
  rw [h_scale]; exact ht' i

private lemma lrc_nat_not_dvd (m : ℕ) (w : Fin m → ℕ)
    (h_ndvd : ∀ i : Fin m, ¬ (m + 1) ∣ w i) :
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin m, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((m + 1 : ℕ) : ℝ) := by
  have hm_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  refine ⟨1 / ((m + 1 : ℕ) : ℝ), by positivity, fun i => ?_⟩
  let q : ℕ := w i / (m + 1)
  let r : ℕ := w i % (m + 1)
  have hdiv : (m + 1) * q + r = w i := Nat.div_add_mod (w i) (m + 1)
  have hr_ge : 1 ≤ r :=
    Nat.one_le_iff_ne_zero.mpr (fun hr0 => h_ndvd i (Nat.dvd_of_mod_eq_zero hr0))
  have hr_le : r ≤ m := Nat.le_of_lt_succ (Nat.mod_lt (w i) (Nat.succ_pos m))
  have h_eq : 1 / ((m + 1 : ℕ) : ℝ) * (w i : ℝ) =
      ((q : ℤ) : ℝ) + (r : ℝ) / ((m + 1 : ℕ) : ℝ) := by
    have hwi_cast : (w i : ℝ) = ((m + 1 : ℕ) : ℝ) * (q : ℝ) + (r : ℝ) := by exact_mod_cast hdiv.symm
    rw [hwi_cast, Int.cast_natCast]; field_simp [ne_of_gt hm_pos]
  rw [h_eq]
  have hlo : ((q : ℤ) : ℝ) + 1 / ((m + 1 : ℕ) : ℝ) ≤
      ((q : ℤ) : ℝ) + (r : ℝ) / ((m + 1 : ℕ) : ℝ) := by
    have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr_ge
    linarith [div_le_div_of_nonneg_right hr1 hm_pos.le]
  have hhi : ((q : ℤ) : ℝ) + (r : ℝ) / ((m + 1 : ℕ) : ℝ) ≤
      ((q : ℤ) : ℝ) + 1 - 1 / ((m + 1 : ℕ) : ℝ) := by
    have hrm : (r : ℝ) ≤ (m : ℝ) := by exact_mod_cast hr_le
    have hdiv_le : (r : ℝ) / ((m + 1 : ℕ) : ℝ) ≤ 1 - 1 / ((m + 1 : ℕ) : ℝ) := by
      rw [div_le_iff₀ hm_pos]
      have hm1 : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
      have h_rhs : (1 - 1 / ((m + 1 : ℕ) : ℝ)) * ((m + 1 : ℕ) : ℝ) = (m : ℝ) := by
        field_simp [ne_of_gt hm_pos]; linarith
      linarith
    linarith
  exact unitAddCircle_dist_ge_of_Icc _ (1 / ((m + 1 : ℕ) : ℝ)) (q : ℤ) hlo hhi


/- Core `k = 4` (Five-Runner) Lemmas -/

private lemma mod_mul_eq_mul_mod (a b n : ℕ) : ((a % n) * b) % n = (a * b) % n := by
  rw [Nat.mul_mod (a % n) b n, Nat.mod_mod, ← Nat.mul_mod]

private lemma mul_mod_eq_mul_mod (a b n : ℕ) : (a * (b % n)) % n = (a * b) % n := by
  rw [Nat.mul_mod a (b % n) n, Nat.mod_mod, ← Nat.mul_mod]

private lemma mod5_pow4_eq_one (m : ℕ) (hm : m % 5 ≠ 0) : (m * m * m * m) % 5 = 1 := by
  have hlt : m % 5 < 5 := Nat.mod_lt m (by omega)
  have h4 : (m * m * m * m) % 5 = ((m % 5) * (m % 5) * (m % 5) * (m % 5)) % 5 := by
    rw [← mod_mul_eq_mul_mod (m * m * m) m 5, ← mod_mul_eq_mul_mod (m * m) m 5,
      Nat.mul_mod m m 5]
    simp [Nat.mul_mod]
  rw [h4]
  rcases (by omega : m % 5 = 1 ∨ m % 5 = 2 ∨ m % 5 = 3 ∨ m % 5 = 4) with h | h | h | h <;>
    simp [h]

private lemma mul_pow3_cancel_mod5 (a m : ℕ) (hm : m % 5 ≠ 0) :
    (((a * (m * m * m)) % 5) * m) % 5 = a % 5 := by
  rw [mod_mul_eq_mul_mod]
  have hassoc : a * (m * m * m) * m = a * (m * m * m * m) := by ring
  rw [hassoc, ← mul_mod_eq_mul_mod a (m * m * m * m) 5, mod5_pow4_eq_one m hm, mul_one]

private lemma dist_rat_ge_one_fifth (n D : ℕ) (hD : 0 < D)
    (hlo : D ≤ 5 * (n % D)) (hhi : 5 * (n % D) ≤ 4 * D) :
    dist (((n : ℝ) / (D : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / 5 := by
  have hD_pos : (0 : ℝ) < (D : ℝ) := by positivity
  let q : ℕ := n / D
  let rem : ℕ := n % D
  have hdiv : D * q + rem = n := Nat.div_add_mod n D
  have h_eq : (n : ℝ) / (D : ℝ) = ((q : ℤ) : ℝ) + (rem : ℝ) / (D : ℝ) := by
    have hn_cast : (n : ℝ) = (D : ℝ) * (q : ℝ) + (rem : ℝ) := by exact_mod_cast hdiv.symm
    rw [hn_cast, Int.cast_natCast]
    field_simp [ne_of_gt hD_pos]
  rw [h_eq]
  have hlo_r : (D : ℝ) ≤ 5 * (rem : ℝ) := by exact_mod_cast hlo
  have hhi_r : 5 * (rem : ℝ) ≤ 4 * (D : ℝ) := by exact_mod_cast hhi
  refine unitAddCircle_dist_ge_of_Icc _ (1 / 5) (q : ℤ) ?_ ?_
  · have : (1 : ℝ) / 5 ≤ (rem : ℝ) / (D : ℝ) := by
      rw [div_le_div_iff₀ (by norm_num) hD_pos]; linarith
    linarith
  · have : (rem : ℝ) / (D : ℝ) ≤ 1 - 1 / 5 := by
      rw [div_le_iff₀ hD_pos]; linarith
    linarith

private lemma nat_extract_two_pow :
    ∀ (n : ℕ), 0 < n → ∃ e m : ℕ, n = 2 ^ e * m ∧ m % 2 = 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    rcases eq_or_ne (n % 2) 1 with hodd | heven
    · exact ⟨0, n, by simp, hodd⟩
    · have hmod0 : n % 2 = 0 := by omega
      have hhalf_pos : 0 < n / 2 := by omega
      have hhalf_lt : n / 2 < n := Nat.div_lt_self hn one_lt_two
      obtain ⟨e, m, hm_eq, hm_odd⟩ := ih (n / 2) hhalf_lt hhalf_pos
      refine ⟨e + 1, m, ?_, hm_odd⟩
      have hn2 : 2 * (n / 2) = n := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hmod0)
      rw [pow_succ, mul_comm (2 ^ e) 2, mul_assoc, ← hm_eq, hn2]

private lemma coset_mod5_lonely (c M r u : ℕ) (hM : 0 < M)
    (hs1 : (((c + r * M) % 5) * u) % 5 ≠ ((c * u) % M) % 5)
    (hs2 : (((c + r * M) % 5) * u) % 5 ≠ (((c * u) % M) + 4 * M) % 5) :
    dist ((((c + r * M : ℝ) / (5 * M : ℝ)) * (u : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / 5 := by
  let n : ℕ := (c + r * M) * u
  let D : ℕ := 5 * M
  have h_rewrite : ((c + r * M : ℝ) / (5 * M : ℝ)) * (u : ℝ) = (n : ℝ) / (D : ℝ) := by
    dsimp [n, D]; push_cast; ring
  rw [h_rewrite]
  let rem : ℕ := n % D
  let a : ℕ := (c * u) % M
  have ha_lt : a < M := Nat.mod_lt _ hM
  have hrem_lt : rem < 5 * M := Nat.mod_lt n (by omega)
  have hrem_mod_M : rem % M = a := by
    have h1 : n % M = a := by
      have hn_eq : n = c * u + M * (r * u) := by dsimp [n]; ring
      rw [hn_eq, Nat.add_mul_mod_self_left]
    exact (Nat.mod_mod_of_dvd n (dvd_mul_left M 5)).trans h1
  have hrem_mod_5 : rem % 5 = (((c + r * M) % 5) * u) % 5 := by
    have h2 : rem % 5 = n % 5 := Nat.mod_mod_of_dvd n (dvd_mul_right 5 M)
    rw [h2]
    exact (mod_mul_eq_mul_mod (c + r * M) u 5).symm
  obtain ⟨j, hj_eq⟩ : ∃ j : ℕ, M * j + a = rem :=
    ⟨rem / M, by have := Nat.div_add_mod rem M; rwa [hrem_mod_M] at this⟩
  have hj_lt : j < 5 := by
    by_contra hge
    have h5M : M * 5 ≤ M * j := Nat.mul_le_mul_left M (by omega)
    omega
  have hj_ne0 : j ≠ 0 := by
    intro hj0
    rw [hj0, mul_zero, zero_add] at hj_eq
    exact hs1 (by rw [← hrem_mod_5, ← hj_eq])
  have h_bounds : M ≤ rem ∧ rem ≤ 4 * M := by
    rcases eq_or_ne j 4 with hj4 | hj_ne4
    · rcases eq_or_ne a 0 with ha0 | ha_pos
      · rw [hj4, ha0, add_zero] at hj_eq
        omega
      · exfalso
        rw [hj4] at hj_eq
        have hrem4 : rem = a + 4 * M := by linarith
        exact hs2 (by rw [← hrem_mod_5, hrem4])
    · have h1 : M * 1 ≤ M * j := Nat.mul_le_mul_left M (by omega)
      have h2 : M * j ≤ M * 3 := Nat.mul_le_mul_left M (by omega)
      omega
  refine dist_rat_ge_one_fifth n D (by omega) ?_ ?_
  · change D ≤ 5 * rem; dsimp [D]; omega
  · change 5 * rem ≤ 4 * D; dsimp [D]; omega

set_option maxHeartbeats 600000 in
private lemma fin5_four_zone_all
    (z0 z1 z2 : Fin 4) (k0 k1 k2 : Fin 5) (u0 u1 u2 : Fin 4) :
    ∃ (c : Fin 3) (s : Fin 5),
      let chk (cv z k u sv : ℕ) : Prop :=
        let su := (sv * u) % 5
        if cv = 0 then
          let b := if z < 2 then k else k + 4
          su ≠ b % 5 ∧ su ≠ (b + 4) % 5
        else if cv = 1 then
          su ≠ k % 5 ∧ su ≠ (k + 3) % 5
        else
          let b := if z = 0 then 3 * k else if z < 3 then 3 * k + 3 else 3 * k + 1
          su ≠ b % 5 ∧ su ≠ (b + 3) % 5
      chk c.val z0.val k0.val (u0.val + 1) s.val ∧
      chk c.val z1.val k1.val (u1.val + 1) s.val ∧
      chk c.val z2.val k2.val (u2.val + 1) s.val := by
  let ok (cv z k u sv : ℕ) : Bool :=
    let su := (sv * u) % 5
    if cv = 0 then
      let b := if z < 2 then k else k + 4
      (su != b % 5) && (su != (b + 4) % 5)
    else if cv = 1 then
      (su != k % 5) && (su != (k + 3) % 5)
    else
      let b := if z = 0 then 3 * k else if z < 3 then 3 * k + 3 else 3 * k + 1
      (su != b % 5) && (su != (b + 3) % 5)
  have h_sym_u : ∀ (c : Fin 3) (z : Fin 4) (k u s : Fin 5),
      ok c.val z.val k.val ((5 - u.val) % 5) s.val =
        ok c.val (3 - z.val) ((7 - k.val) % 5) u.val s.val := by decide
  have h_sym_s : ∀ (c : Fin 3) (z : Fin 4) (k u s : Fin 5),
      ok c.val z.val k.val u.val ((5 - s.val) % 5) =
        ok c.val (3 - z.val) ((7 - k.val) % 5) u.val s.val := by decide
  have h_scale : ∀ (c : Fin 3) (z : Fin 4) (k u w s : Fin 5),
      ok c.val z.val k.val ((u.val * w.val) % 5) s.val =
        ok c.val z.val k.val u.val ((s.val * w.val) % 5) := by
    intro c z k u w s
    have hmul : (s.val * ((u.val * w.val) % 5)) % 5 = (((s.val * w.val) % 5) * u.val) % 5 := by
      rw [mul_mod_eq_mul_mod, mod_mul_eq_mul_mod]
      congr 1; ring
    dsimp [ok]
    rw [hmul]
  let H : List ℕ :=
    [321, 642, 292, 584, 176, 69, 521, 138, 50, 276, 8352, 4384, 2368, 1600, 17024,
     8227, 1553, 2118, 16524, 4376, 18465, 20546, 5252, 9480, 10768, 16480, 2592, 4288,
     1408, 8960, 2179, 16645, 8265, 8273, 16646, 4618, 2194, 4620, 1076, 1080, 2083,
     8721, 16454, 4236, 1304]
  have h_step1 : ∀ (z0' : Fin 2) (k0' : Fin 5)
      (z1' : Fin 4) (k1' : Fin 5) (v1' : Fin 2),
      ∃ h ∈ H, ∀ cs : Fin 15, h.testBit cs.val = true →
        ok (cs.val / 5) z0'.val k0'.val 1 (cs.val % 5) = true ∧
        ok (cs.val / 5) z1'.val k1'.val (v1'.val + 1) (cs.val % 5) = true := by decide
  have h_step2 : ∀ h ∈ H, ∀ (z2' : Fin 4) (k2' : Fin 5) (v2' : Fin 2),
      ∃ cs : Fin 15, h.testBit cs.val = true ∧
        ok (cs.val / 5) z2'.val k2'.val (v2'.val + 1) (cs.val % 5) = true := by decide
  let u0v : ℕ := u0.val + 1
  have hu0_nz : u0v % 5 ≠ 0 := by omega
  let inv0 : Fin 5 := ⟨(u0v * u0v * u0v) % 5, by omega⟩
  let w1 : Fin 5 := ⟨((u1.val + 1) * inv0.val) % 5, by omega⟩
  let w2 : Fin 5 := ⟨((u2.val + 1) * inv0.val) % 5, by omega⟩
  have hw1_recover : (w1.val * u0v) % 5 = u1.val + 1 := by
    have h := mul_pow3_cancel_mod5 (u1.val + 1) u0v hu0_nz
    dsimp [w1, inv0]
    rw [mul_mod_eq_mul_mod (u1.val + 1) (u0v * u0v * u0v) 5, h, Nat.mod_eq_of_lt (by omega)]
  have hw2_recover : (w2.val * u0v) % 5 = u2.val + 1 := by
    have h := mul_pow3_cancel_mod5 (u2.val + 1) u0v hu0_nz
    dsimp [w2, inv0]
    rw [mul_mod_eq_mul_mod (u2.val + 1) (u0v * u0v * u0v) 5, h, Nat.mod_eq_of_lt (by omega)]
  have hw1_pos : 1 ≤ w1.val := by
    by_contra h0
    have hw1_0 : w1.val = 0 := by omega
    rw [hw1_0, zero_mul, Nat.zero_mod] at hw1_recover
    omega
  have hw2_pos : 1 ≤ w2.val := by
    by_contra h0
    have hw2_0 : w2.val = 0 := by omega
    rw [hw2_0, zero_mul, Nat.zero_mod] at hw2_recover
    omega
  let z1a : Fin 4 := if w1.val ≤ 2 then z1 else ⟨3 - z1.val, by omega⟩
  let k1a : Fin 5 := if w1.val ≤ 2 then k1 else ⟨(7 - k1.val) % 5, by omega⟩
  let v1a : Fin 2 := if hw12 : w1.val ≤ 2 then ⟨w1.val - 1, by omega⟩ else ⟨5 - w1.val - 1, by omega⟩
  let z2a : Fin 4 := if w2.val ≤ 2 then z2 else ⟨3 - z2.val, by omega⟩
  let k2a : Fin 5 := if w2.val ≤ 2 then k2 else ⟨(7 - k2.val) % 5, by omega⟩
  let v2a : Fin 2 := if hw22 : w2.val ≤ 2 then ⟨w2.val - 1, by omega⟩ else ⟨5 - w2.val - 1, by omega⟩
  let z0b : Fin 2 := if hz02 : z0.val < 2 then ⟨z0.val, hz02⟩ else ⟨3 - z0.val, by omega⟩
  let k0b : Fin 5 := if z0.val < 2 then k0 else ⟨(7 - k0.val) % 5, by omega⟩
  let z1b : Fin 4 := if z0.val < 2 then z1a else ⟨3 - z1a.val, by omega⟩
  let k1b : Fin 5 := if z0.val < 2 then k1a else ⟨(7 - k1a.val) % 5, by omega⟩
  let z2b : Fin 4 := if z0.val < 2 then z2a else ⟨3 - z2a.val, by omega⟩
  let k2b : Fin 5 := if z0.val < 2 then k2a else ⟨(7 - k2a.val) % 5, by omega⟩
  obtain ⟨h, hh_mem, hh_01⟩ := h_step1 z0b k0b z1b k1b v1a
  obtain ⟨cs, hbit, hc2⟩ := h_step2 h hh_mem z2b k2b v2a
  obtain ⟨hc0, hc1⟩ := hh_01 cs hbit
  let c : Fin 3 := ⟨cs.val / 5, by omega⟩
  let s_core : Fin 5 := ⟨cs.val % 5, by omega⟩
  let s_pre : Fin 5 := if z0.val < 2 then s_core else ⟨(5 - s_core.val) % 5, by omega⟩
  let s_out : Fin 5 := ⟨(s_pre.val * inv0.val) % 5, by omega⟩
  have hs_mul_u0 : (s_out.val * u0v) % 5 = s_pre.val := by
    have h := mul_pow3_cancel_mod5 s_pre.val u0v hu0_nz
    dsimp [s_out, inv0]
    rw [mul_mod_eq_mul_mod s_pre.val (u0v * u0v * u0v) 5, h, Nat.mod_eq_of_lt s_pre.isLt]
  have h0_ok : ok c.val z0.val k0.val u0v s_out.val = true := by
    have hsc := h_scale c z0 k0 ⟨1, by omega⟩ ⟨u0v, by omega⟩ s_out
    simp only [one_mul, Nat.mod_eq_of_lt (show u0v < 5 by omega), hs_mul_u0] at hsc
    rw [hsc]
    by_cases hz02 : z0.val < 2
    · simp only [s_pre, z0b, k0b, hz02, ↓reduceDIte, ↓reduceIte] at hc0 ⊢
      exact hc0
    · simp only [s_pre, z0b, k0b, hz02, ↓reduceDIte, ↓reduceIte] at hc0 ⊢
      rw [h_sym_s c z0 k0 ⟨1, by omega⟩ s_core]
      exact hc0
  have h1_ok : ok c.val z1.val k1.val (u1.val + 1) s_out.val = true := by
    have hsc := h_scale c z1 k1 w1 ⟨u0v, by omega⟩ s_out
    rw [hw1_recover, hs_mul_u0] at hsc
    rw [hsc]
    have h1a : ok c.val z1a.val k1a.val (v1a.val + 1) s_pre.val = true := by
      by_cases hz02 : z0.val < 2
      · simp only [s_pre, z1b, k1b, hz02, ↓reduceIte] at hc1 ⊢; exact hc1
      · simp only [s_pre, z1b, k1b, hz02, ↓reduceIte] at hc1 ⊢
        rw [h_sym_s c z1a k1a ⟨v1a.val + 1, by omega⟩ s_core]
        exact hc1
    by_cases hw12 : w1.val ≤ 2
    · simp only [z1a, k1a, v1a, hw12, ↓reduceDIte, ↓reduceIte] at h1a
      have hv_eq : w1.val - 1 + 1 = w1.val := by omega
      rwa [hv_eq] at h1a
    · simp only [z1a, k1a, v1a, hw12, ↓reduceDIte, ↓reduceIte] at h1a
      have hv_eq : 5 - w1.val - 1 + 1 = 5 - w1.val := by omega
      rw [hv_eq] at h1a
      have hw1_eq : w1.val = (5 - (5 - w1.val)) % 5 := by omega
      conv_lhs => rw [hw1_eq]
      exact (h_sym_u c z1 k1 ⟨5 - w1.val, by omega⟩ s_pre).trans h1a
  have h2_ok : ok c.val z2.val k2.val (u2.val + 1) s_out.val = true := by
    have hsc := h_scale c z2 k2 w2 ⟨u0v, by omega⟩ s_out
    rw [hw2_recover, hs_mul_u0] at hsc
    rw [hsc]
    have h2a : ok c.val z2a.val k2a.val (v2a.val + 1) s_pre.val = true := by
      by_cases hz02 : z0.val < 2
      · simp only [s_pre, z2b, k2b, hz02, ↓reduceIte] at hc2 ⊢; exact hc2
      · simp only [s_pre, z2b, k2b, hz02, ↓reduceIte] at hc2 ⊢
        rw [h_sym_s c z2a k2a ⟨v2a.val + 1, by omega⟩ s_core]
        exact hc2
    by_cases hw22 : w2.val ≤ 2
    · simp only [z2a, k2a, v2a, hw22, ↓reduceDIte, ↓reduceIte] at h2a
      have hv_eq : w2.val - 1 + 1 = w2.val := by omega
      rwa [hv_eq] at h2a
    · simp only [z2a, k2a, v2a, hw22, ↓reduceDIte, ↓reduceIte] at h2a
      have hv_eq : 5 - w2.val - 1 + 1 = 5 - w2.val := by omega
      rw [hv_eq] at h2a
      have hw2_eq : w2.val = (5 - (5 - w2.val)) % 5 := by omega
      conv_lhs => rw [hw2_eq]
      exact (h_sym_u c z2 k2 ⟨5 - w2.val, by omega⟩ s_pre).trans h2a
  have ok_iff : ∀ cv z k u sv, ok cv z k u sv = true →
      (let su := (sv * u) % 5
       if cv = 0 then
         let b := if z < 2 then k else k + 4
         su ≠ b % 5 ∧ su ≠ (b + 4) % 5
       else if cv = 1 then
         su ≠ k % 5 ∧ su ≠ (k + 3) % 5
       else
         let b := if z = 0 then 3 * k else if z < 3 then 3 * k + 3 else 3 * k + 1
         su ≠ b % 5 ∧ su ≠ (b + 3) % 5) := by
    intro cv z k u sv h
    dsimp [ok] at h ⊢
    split_ifs at h ⊢ <;> simp only [Bool.and_eq_true, bne_iff_ne] at h <;> exact h
  exact ⟨c, s_out, ok_iff _ _ _ _ _ h0_ok, ok_iff _ _ _ _ _ h1_ok, ok_iff _ _ _ _ _ h2_ok⟩

private lemma zone_coset_bridge (Q u : ℕ) (hQ : 0 < Q) (hQ5 : Q % 5 ≠ 0)
    (c : Fin 3) (s' : Fin 5) (r : ℕ)
    (z : Fin 4) (k : Fin 5) (u5 : Fin 4)
    (hz_def : z.val = if 3 * (u % (2 * Q)) < 2 * Q then 0
                      else if u % (2 * Q) < Q then 1
                      else if 3 * (u % (2 * Q)) < 4 * Q then 2
                      else 3)
    (hk_mod : (k.val * Q) % 5 = (u % (2 * Q)) % 5)
    (hu5_mod : u5.val + 1 = u % 5)
    (hc_ok :
      let su := (s'.val * (u5.val + 1)) % 5
      if c.val = 0 then
        let b := if z.val < 2 then k.val else k.val + 4
        su ≠ b % 5 ∧ su ≠ (b + 4) % 5
      else if c.val = 1 then
        su ≠ k.val % 5 ∧ su ≠ (k.val + 3) % 5
      else
        let b := if z.val = 0 then 3 * k.val else if z.val < 3 then 3 * k.val + 3 else 3 * k.val + 1
        su ≠ b % 5 ∧ su ≠ (b + 3) % 5) :
    let c_num : ℕ := if c.val = 2 then 3 else 1
    let M : ℕ := if c.val = 0 then Q else 2 * Q
    (c_num + r * M) % 5 = (s'.val * Q) % 5 →
    dist ((((c_num + r * M : ℝ) / (5 * M : ℝ)) * (u : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / 5 := by
  intro c_num M hr_mod
  let rem : ℕ := u % (2 * Q)
  have hrem_lt : rem < 2 * Q := Nat.mod_lt u (by omega)
  have h_mul_Q_inj : ∀ A B : ℕ, A % 5 ≠ B % 5 → (A * Q) % 5 ≠ (B * Q) % 5 := by
    intro A B hne heq
    apply hne
    have hAQ : ((A * Q) * (Q * Q * Q)) % 5 = (((A * Q) % 5) * (Q * Q * Q)) % 5 :=
      (mod_mul_eq_mul_mod (A * Q) (Q * Q * Q) 5).symm
    have hBQ : ((B * Q) * (Q * Q * Q)) % 5 = (((B * Q) % 5) * (Q * Q * Q)) % 5 :=
      (mod_mul_eq_mul_mod (B * Q) (Q * Q * Q) 5).symm
    calc A % 5 = (((A * (Q * Q * Q)) % 5) * Q) % 5 := (mul_pow3_cancel_mod5 A Q hQ5).symm
      _ = (A * Q * (Q * Q * Q)) % 5 := by
          rw [mod_mul_eq_mul_mod]
          congr 1; ring
      _ = (((A * Q) % 5) * (Q * Q * Q)) % 5 := hAQ
      _ = (((B * Q) % 5) * (Q * Q * Q)) % 5 := by rw [heq]
      _ = (B * Q * (Q * Q * Q)) % 5 := hBQ.symm
      _ = (((B * (Q * Q * Q)) % 5) * Q) % 5 := by
          rw [mod_mul_eq_mul_mod]
          congr 1; ring
      _ = B % 5 := mul_pow3_cancel_mod5 B Q hQ5
  have hsu_mul : (((c_num + r * M) % 5) * u) % 5 = ((s'.val * (u5.val + 1)) * Q) % 5 := by
    rw [hr_mod, mod_mul_eq_mul_mod (s'.val * Q) u 5, ← mul_mod_eq_mul_mod (s'.val * Q) u 5, ← hu5_mod]
    congr 1; ring
  have h_u_mod_Q : u % Q = rem % Q := (Nat.mod_mod_of_dvd u (dvd_mul_left Q 2)).symm
  have h_3u_mod_2Q : (3 * u) % (2 * Q) = (3 * rem) % (2 * Q) := by
    dsimp [rem]; rw [mul_mod_eq_mul_mod 3 u (2 * Q)]
  fin_cases c
  · -- c = 0: c_num = 1, M = Q
    have hc_num1 : c_num = 1 := rfl
    have hM_Q : M = Q := rfl
    rw [hc_num1, hM_Q] at hr_mod hsu_mul ⊢
    refine coset_mod5_lonely 1 Q r u hQ ?_ ?_
    · rw [hsu_mul, one_mul, h_u_mod_Q]
      simp only [↓reduceIte] at hc_ok
      by_cases hltQ : rem < Q
      · have hz_lt2 : z.val < 2 := by rw [hz_def]; split_ifs <;> omega
        simp only [hz_lt2, ↓reduceIte] at hc_ok
        have hremQ : rem % Q = rem := Nat.mod_eq_of_lt hltQ
        rw [hremQ, ← hk_mod]
        exact h_mul_Q_inj _ _ hc_ok.1
      · have hz_ge2 : ¬ z.val < 2 := by rw [hz_def]; split_ifs <;> omega
        simp only [hz_ge2, ↓reduceIte] at hc_ok
        have hremQ : rem % Q = rem - Q := by
          have hsub : rem - Q < Q := by omega
          have heq : rem = Q * 1 + (rem - Q) := by omega
          conv_lhs => rw [heq, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hsub]
        have hmod_eq : ((k.val + 4) * Q) % 5 = (rem % Q) % 5 := by
          rw [hremQ, add_mul, Nat.add_mod, hk_mod, ← Nat.add_mod]
          omega
        rw [← hmod_eq]
        exact h_mul_Q_inj _ _ hc_ok.1
    · rw [hsu_mul, one_mul, h_u_mod_Q]
      simp only [↓reduceIte] at hc_ok
      by_cases hltQ : rem < Q
      · have hz_lt2 : z.val < 2 := by rw [hz_def]; split_ifs <;> omega
        simp only [hz_lt2, ↓reduceIte] at hc_ok
        have hremQ : rem % Q = rem := Nat.mod_eq_of_lt hltQ
        have hmod_eq : ((k.val + 4) * Q) % 5 = (rem % Q + 4 * Q) % 5 := by
          rw [hremQ, add_mul, Nat.add_mod, hk_mod, ← Nat.add_mod]
        rw [← hmod_eq]
        exact h_mul_Q_inj _ _ hc_ok.2
      · have hz_ge2 : ¬ z.val < 2 := by rw [hz_def]; split_ifs <;> omega
        simp only [hz_ge2, ↓reduceIte] at hc_ok
        have hremQ : rem % Q = rem - Q := by
          have hsub : rem - Q < Q := by omega
          have heq : rem = Q * 1 + (rem - Q) := by omega
          conv_lhs => rw [heq, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hsub]
        have hmod_eq : ((k.val + 4 + 4) * Q) % 5 = (rem % Q + 4 * Q) % 5 := by
          rw [hremQ, add_assoc, add_mul, Nat.add_mod, hk_mod, ← Nat.add_mod]
          omega
        rw [← hmod_eq]
        exact h_mul_Q_inj _ _ hc_ok.2
  · -- c = 1: c_num = 1, M = 2 * Q
    have hc_num1 : c_num = 1 := rfl
    have hM_2Q : M = 2 * Q := rfl
    rw [hc_num1, hM_2Q] at hr_mod hsu_mul ⊢
    refine coset_mod5_lonely 1 (2 * Q) r u (by omega) ?_ ?_
    · rw [hsu_mul, one_mul]
      change ((s'.val * (u5.val + 1)) * Q) % 5 ≠ rem % 5
      rw [← hk_mod]
      simp only [one_ne_zero, ↓reduceIte] at hc_ok
      exact h_mul_Q_inj _ _ hc_ok.1
    · rw [hsu_mul, one_mul]
      change ((s'.val * (u5.val + 1)) * Q) % 5 ≠ (rem + 4 * (2 * Q)) % 5
      have hmod_eq : ((k.val + 3) * Q) % 5 = (rem + 4 * (2 * Q)) % 5 := by
        rw [add_mul, Nat.add_mod, hk_mod, ← Nat.add_mod]
        omega
      rw [← hmod_eq]
      simp only [one_ne_zero, ↓reduceIte] at hc_ok
      exact h_mul_Q_inj _ _ hc_ok.2
  · -- c = 2: c_num = 3, M = 2 * Q
    have hc_num3 : c_num = 3 := rfl
    have hM_2Q : M = 2 * Q := rfl
    rw [hc_num3, hM_2Q] at hr_mod hsu_mul ⊢
    refine coset_mod5_lonely 3 (2 * Q) r u (by omega) ?_ ?_
    · rw [hsu_mul, h_3u_mod_2Q]
      simp only [show (2 : ℕ) = 0 ↔ False by decide, show (2 : ℕ) = 1 ↔ False by decide, ↓reduceIte] at hc_ok
      have h3k_mod : (3 * k.val * Q) % 5 = (3 * rem) % 5 := by
        rw [mul_assoc, Nat.mul_mod, hk_mod, ← Nat.mul_mod]
      by_cases hz0 : 3 * rem < 2 * Q
      · have hzv : z.val = 0 := by rw [hz_def]; split_ifs <;> omega
        simp only [hzv, ↓reduceIte] at hc_ok
        rw [Nat.mod_eq_of_lt hz0, ← h3k_mod]
        exact h_mul_Q_inj _ _ hc_ok.1
      · by_cases hz2 : 3 * rem < 4 * Q
        · have hzv_ne0 : z.val ≠ 0 := by rw [hz_def]; split_ifs <;> omega
          have hzv_lt3 : z.val < 3 := by rw [hz_def]; split_ifs <;> omega
          simp only [hzv_ne0, hzv_lt3, ↓reduceIte] at hc_ok
          have h3rem : (3 * rem) % (2 * Q) = 3 * rem - 2 * Q := by
            have hsub : 3 * rem - 2 * Q < 2 * Q := by omega
            have heq : 3 * rem = (2 * Q) * 1 + (3 * rem - 2 * Q) := by omega
            conv_lhs => rw [heq, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hsub]
          have hmod_eq : ((3 * k.val + 3) * Q) % 5 = ((3 * rem) % (2 * Q)) % 5 := by
            rw [h3rem, add_mul, Nat.add_mod, h3k_mod, ← Nat.add_mod]
            omega
          rw [← hmod_eq]
          exact h_mul_Q_inj _ _ hc_ok.1
        · have hzv_3 : z.val = 3 := by rw [hz_def]; split_ifs <;> omega
          simp only [hzv_3, show (3 : ℕ) = 0 ↔ False by decide, show (3 : ℕ) < 3 ↔ False by decide, ↓reduceIte] at hc_ok
          have h3rem : (3 * rem) % (2 * Q) = 3 * rem - 4 * Q := by
            have hsub : 3 * rem - 4 * Q < 2 * Q := by omega
            have heq : 3 * rem = (2 * Q) * 2 + (3 * rem - 4 * Q) := by omega
            conv_lhs => rw [heq, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hsub]
          have hmod_eq : ((3 * k.val + 1) * Q) % 5 = ((3 * rem) % (2 * Q)) % 5 := by
            rw [h3rem, add_mul, one_mul, Nat.add_mod, h3k_mod, ← Nat.add_mod]
            omega
          rw [← hmod_eq]
          exact h_mul_Q_inj _ _ hc_ok.1
    · rw [hsu_mul, h_3u_mod_2Q]
      simp only [show (2 : ℕ) = 0 ↔ False by decide, show (2 : ℕ) = 1 ↔ False by decide, ↓reduceIte] at hc_ok
      have h3k_mod : (3 * k.val * Q) % 5 = (3 * rem) % 5 := by
        rw [mul_assoc, Nat.mul_mod, hk_mod, ← Nat.mul_mod]
      by_cases hz0 : 3 * rem < 2 * Q
      · have hzv : z.val = 0 := by rw [hz_def]; split_ifs <;> omega
        simp only [hzv, ↓reduceIte] at hc_ok
        have hmod_eq : ((3 * k.val + 3) * Q) % 5 = ((3 * rem) % (2 * Q) + 4 * (2 * Q)) % 5 := by
          rw [Nat.mod_eq_of_lt hz0, add_mul, Nat.add_mod, h3k_mod, ← Nat.add_mod]
          omega
        rw [← hmod_eq]
        exact h_mul_Q_inj _ _ hc_ok.2
      · by_cases hz2 : 3 * rem < 4 * Q
        · have hzv_ne0 : z.val ≠ 0 := by rw [hz_def]; split_ifs <;> omega
          have hzv_lt3 : z.val < 3 := by rw [hz_def]; split_ifs <;> omega
          simp only [hzv_ne0, hzv_lt3, ↓reduceIte] at hc_ok
          have h3rem : (3 * rem) % (2 * Q) = 3 * rem - 2 * Q := by
            have hsub : 3 * rem - 2 * Q < 2 * Q := by omega
            have heq : 3 * rem = (2 * Q) * 1 + (3 * rem - 2 * Q) := by omega
            conv_lhs => rw [heq, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hsub]
          have hmod_eq : ((3 * k.val + 3 + 3) * Q) % 5 = ((3 * rem) % (2 * Q) + 4 * (2 * Q)) % 5 := by
            rw [h3rem, add_assoc, add_mul, Nat.add_mod, h3k_mod, ← Nat.add_mod]
            omega
          rw [← hmod_eq]
          exact h_mul_Q_inj _ _ hc_ok.2
        · have hzv_3 : z.val = 3 := by rw [hz_def]; split_ifs <;> omega
          simp only [hzv_3, show (3 : ℕ) = 0 ↔ False by decide, show (3 : ℕ) < 3 ↔ False by decide, ↓reduceIte] at hc_ok
          have h3rem : (3 * rem) % (2 * Q) = 3 * rem - 4 * Q := by
            have hsub : 3 * rem - 4 * Q < 2 * Q := by omega
            have heq : 3 * rem = (2 * Q) * 2 + (3 * rem - 4 * Q) := by omega
            conv_lhs => rw [heq, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hsub]
          have hmod_eq : ((3 * k.val + 1 + 3) * Q) % 5 = ((3 * rem) % (2 * Q) + 4 * (2 * Q)) % 5 := by
            rw [h3rem, add_assoc, add_mul, Nat.add_mod, h3k_mod, ← Nat.add_mod]
            omega
          rw [← hmod_eq]
          exact h_mul_Q_inj _ _ hc_ok.2

private lemma lrc_four_one_div5 (a x y z : ℕ)
    (ha_pos : 0 < a) (ha5 : 5 ∣ a)
    (hx5 : ¬ 5 ∣ x) (hy5 : ¬ 5 ∣ y) (hz5 : ¬ 5 ∣ z) :
    ∃ t : ℝ, t ≥ 0 ∧
      dist ((t * (a : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / 5 ∧
      dist ((t * (x : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / 5 ∧
      dist ((t * (y : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / 5 ∧
      dist ((t * (z : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / 5 := by
  obtain ⟨e, m, ha_eq, hm_odd⟩ := nat_extract_two_pow a ha_pos
  have hcop5 : Nat.Coprime 5 (2 ^ e) := by
    exact (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 5)).mpr
      (fun hdvd => absurd (Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 5) hdvd) (by decide))
  have hm5 : 5 ∣ m := hcop5.dvd_of_dvd_mul_left (ha_eq ▸ ha5)
  obtain ⟨ka, hka_eq⟩ := hm5
  have hka_odd : ka % 2 = 1 := by omega
  let Q : ℕ := 2 ^ (e + 1)
  have hQ_pos : 0 < Q := by positivity
  have hQ_eq : Q = 2 * 2 ^ e := by dsimp [Q]; rw [pow_succ, mul_comm]
  have hQ5 : Q % 5 ≠ 0 := by
    intro h0
    have hdvd : 5 ∣ 2 ^ (e + 1) := Nat.dvd_of_mod_eq_zero h0
    exact absurd (Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 5) hdvd) (by decide)
  let mk_z (u : ℕ) : Fin 4 :=
    if 3 * (u % (2 * Q)) < 2 * Q then ⟨0, by omega⟩
    else if u % (2 * Q) < Q then ⟨1, by omega⟩
    else if 3 * (u % (2 * Q)) < 4 * Q then ⟨2, by omega⟩
    else ⟨3, by omega⟩
  let mk_k (u : ℕ) : Fin 5 := ⟨((u % (2 * Q)) * (Q * Q * Q)) % 5, by omega⟩
  have hmk_k (u : ℕ) : ((mk_k u).val * Q) % 5 = (u % (2 * Q)) % 5 :=
    mul_pow3_cancel_mod5 (u % (2 * Q)) Q hQ5
  have hx_mod5 : x % 5 ≠ 0 := fun h => hx5 (Nat.dvd_of_mod_eq_zero h)
  have hy_mod5 : y % 5 ≠ 0 := fun h => hy5 (Nat.dvd_of_mod_eq_zero h)
  have hz_mod5 : z % 5 ≠ 0 := fun h => hz5 (Nat.dvd_of_mod_eq_zero h)
  let ux : Fin 4 := ⟨x % 5 - 1, by omega⟩
  let uy : Fin 4 := ⟨y % 5 - 1, by omega⟩
  let uz : Fin 4 := ⟨z % 5 - 1, by omega⟩
  obtain ⟨c, s', hcx, hcy, hcz⟩ :=
    fin5_four_zone_all (mk_z x) (mk_z y) (mk_z z) (mk_k x) (mk_k y) (mk_k z) ux uy uz
  let c_num : ℕ := if c.val = 2 then 3 else 1
  let M : ℕ := if c.val = 0 then Q else 2 * Q
  have hM_pos : 0 < M := by dsimp [M]; split_ifs <;> omega
  have hM5 : M % 5 ≠ 0 := by
    dsimp [M]; split_ifs
    · exact hQ5
    · intro h0
      have hdvd : 5 ∣ 2 * Q := Nat.dvd_of_mod_eq_zero h0
      have hcop52 : Nat.Coprime 5 2 := by decide
      exact hQ5 (Nat.mod_eq_zero_of_dvd (hcop52.dvd_of_dvd_mul_left hdvd))
  let diff5 : ℕ := (5 - c_num % 5 + (s'.val * Q) % 5) % 5
  let r : ℕ := (diff5 * (M * M * M)) % 5
  have hr_mod : (c_num + r * M) % 5 = (s'.val * Q) % 5 := by
    have hrM : (r * M) % 5 = diff5 := by
      dsimp [r]
      rw [mul_pow3_cancel_mod5 diff5 M hM5, Nat.mod_eq_of_lt (by dsimp [diff5]; omega)]
    rw [Nat.add_mod, hrM]
    dsimp [diff5]
    omega
  let t : ℝ := (c_num + r * M : ℝ) / (5 * M : ℝ)
  refine ⟨t, by positivity, ?_, ?_, ?_, ?_⟩
  · -- Check distance for `a = 2^e * 5 * ka`:
    have ha_val : a = 2 ^ e * (5 * ka) := by rw [ha_eq, hka_eq]
    have h2e_ne : ((2 ^ e : ℕ) : ℝ) ≠ 0 := by positivity
    by_cases hc0 : c.val = 0
    · have hc_num1 : c_num = 1 := by dsimp [c_num]; split_ifs <;> omega
      have hM_Q : M = Q := by dsimp [M]; simp [hc0]
      have ht_mul_a : t * (a : ℝ) = (((1 + r * Q) * ka : ℕ) : ℝ) / (2 : ℝ) := by
        dsimp [t]; rw [hc_num1, hM_Q, ha_val, hQ_eq]
        push_cast; field_simp [h2e_ne]
      rw [ht_mul_a]
      have hodd_num : ((1 + r * Q) * ka) % 2 = 1 := by
        have hQ_even : Q % 2 = 0 := by rw [hQ_eq]; omega
        rw [Nat.mul_mod, Nat.add_mod, Nat.mul_mod r Q, hQ_even, hka_odd]; norm_num
      refine dist_rat_ge_one_fifth ((1 + r * Q) * ka) 2 (by omega) ?_ ?_
      · omega
      · omega
    · have hM_2Q : M = 2 * Q := by dsimp [M]; simp [hc0]
      have hc_odd : c_num % 2 = 1 := by dsimp [c_num]; split_ifs <;> omega
      have ht_mul_a : t * (a : ℝ) = (((c_num + r * (2 * Q)) * ka : ℕ) : ℝ) / (4 : ℝ) := by
        dsimp [t]; rw [hM_2Q, ha_val, hQ_eq]
        push_cast; field_simp [h2e_ne]; ring
      rw [ht_mul_a]
      have hodd_num : ((c_num + r * (2 * Q)) * ka) % 2 = 1 := by
        have h2Q_even : (2 * Q) % 2 = 0 := by omega
        rw [Nat.mul_mod, Nat.add_mod, hc_odd, Nat.mul_mod r (2 * Q), h2Q_even, hka_odd]; norm_num
      have hmod4_ne0 : ((c_num + r * (2 * Q)) * ka) % 4 ≠ 0 := by omega
      have hmod4_lt : ((c_num + r * (2 * Q)) * ka) % 4 < 4 := Nat.mod_lt _ (by omega)
      refine dist_rat_ge_one_fifth ((c_num + r * (2 * Q)) * ka) 4 (by omega) ?_ ?_
      · omega
      · omega
  · -- Check distance for `x`:
    have hzx : (mk_z x).val = if 3 * (x % (2 * Q)) < 2 * Q then 0
        else if x % (2 * Q) < Q then 1
        else if 3 * (x % (2 * Q)) < 4 * Q then 2 else 3 := by
      dsimp [mk_z]; split_ifs <;> rfl
    exact zone_coset_bridge Q x hQ_pos hQ5 c s' r (mk_z x) (mk_k x) ux hzx (hmk_k x)
      (by dsimp [ux]; omega) hcx hr_mod
  · -- Check distance for `y`:
    have hzy : (mk_z y).val = if 3 * (y % (2 * Q)) < 2 * Q then 0
        else if y % (2 * Q) < Q then 1
        else if 3 * (y % (2 * Q)) < 4 * Q then 2 else 3 := by
      dsimp [mk_z]; split_ifs <;> rfl
    exact zone_coset_bridge Q y hQ_pos hQ5 c s' r (mk_z y) (mk_k y) uy hzy (hmk_k y)
      (by dsimp [uy]; omega) hcy hr_mod
  · -- Check distance for `z`:
    have hzz : (mk_z z).val = if 3 * (z % (2 * Q)) < 2 * Q then 0
        else if z % (2 * Q) < Q then 1
        else if 3 * (z % (2 * Q)) < 4 * Q then 2 else 3 := by
      dsimp [mk_z]; split_ifs <;> rfl
    exact zone_coset_bridge Q z hQ_pos hQ5 c s' r (mk_z z) (mk_k z) uz hzz (hmk_k z)
      (by dsimp [uz]; omega) hcz hr_mod

private lemma coset5_bad_at_most_two (t' : ℝ) (u : ℕ) (hu5 : ¬ 5 ∣ u) :
    ∃ s₁ s₂ : Fin 5, ∀ r : Fin 5, r ≠ s₁ → r ≠ s₂ →
      dist (((t' + (r.val : ℝ)) / 5 * (u : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / 5 := by
  have hu_mod : u % 5 ≠ 0 := fun h => hu5 (Nat.dvd_of_mod_eq_zero h)
  let α : ℝ := t' * (u : ℝ) / 5
  let fr : ℝ := Int.fract α
  have hfr0 : 0 ≤ fr := Int.fract_nonneg α
  have hfr1 : fr < 1 := Int.fract_lt_one α
  let pick (k : ℕ) : Fin 5 := ⟨(k * (u * u * u)) % 5, by omega⟩
  have hpick_ne : ∀ (r : Fin 5) (k : ℕ), k < 5 → r ≠ pick k → (r.val * u) % 5 ≠ k := by
    intro r k hk hr heq
    apply hr
    ext
    dsimp [pick]
    rw [← heq, mod_mul_eq_mul_mod (r.val * u) (u * u * u) 5]
    have hassoc : r.val * u * (u * u * u) = (r.val * (u * u * u)) * u := by ring
    rw [hassoc, ← mod_mul_eq_mul_mod (r.val * (u * u * u)) u 5,
      mul_pow3_cancel_mod5 r.val u hu_mod, Nat.mod_eq_of_lt r.isLt]
  have h_eval : ∀ (r : Fin 5) (z : ℤ),
      (z : ℝ) + 1 / 5 ≤ fr + (((r.val * u) % 5 : ℕ) : ℝ) / 5 →
      fr + (((r.val * u) % 5 : ℕ) : ℝ) / 5 ≤ (z : ℝ) + 1 - 1 / 5 →
      dist (((t' + (r.val : ℝ)) / 5 * (u : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / 5 := by
    intro r z hlo hhi
    let q_r : ℕ := (r.val * u) / 5
    let m_r : ℕ := (r.val * u) % 5
    have hdiv : 5 * q_r + m_r = r.val * u := Nat.div_add_mod (r.val * u) 5
    have h_expand : (t' + (r.val : ℝ)) / 5 * (u : ℝ) =
        ((⌊α⌋ + (q_r : ℤ) + z : ℤ) : ℝ) - (z : ℝ) + (fr + (m_r : ℝ) / 5) := by
      have hru_cast : (r.val : ℝ) * (u : ℝ) = 5 * (q_r : ℝ) + (m_r : ℝ) := by exact_mod_cast hdiv.symm
      have hα_split : (⌊α⌋ : ℝ) + fr = α := Int.floor_add_fract α
      calc (t' + (r.val : ℝ)) / 5 * (u : ℝ)
          = α + ((r.val : ℝ) * (u : ℝ)) / 5 := by dsimp [α]; ring
        _ = ((⌊α⌋ : ℝ) + fr) + (5 * (q_r : ℝ) + (m_r : ℝ)) / 5 := by rw [hα_split, hru_cast]
        _ = ((⌊α⌋ + (q_r : ℤ) + z : ℤ) : ℝ) - (z : ℝ) + (fr + (m_r : ℝ) / 5) := by push_cast; ring
    refine unitAddCircle_dist_ge_of_Icc _ (1 / 5) (⌊α⌋ + (q_r : ℤ) + z) ?_ ?_
    · rw [h_expand]; linarith
    · rw [h_expand]; linarith
  rcases lt_or_ge fr (1 / 5) with h1 | h1
  · refine ⟨pick 0, pick 4, fun r hr1 hr2 => ?_⟩
    have hm0 := hpick_ne r 0 (by omega) hr1
    have hm4 := hpick_ne r 4 (by omega) hr2
    have hmlt : (r.val * u) % 5 < 5 := Nat.mod_lt _ (by omega)
    have hm_ge1 : (1 : ℝ) ≤ (((r.val * u) % 5 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ (r.val * u) % 5)
    have hm_le3 : (((r.val * u) % 5 : ℕ) : ℝ) ≤ 3 := by exact_mod_cast (by omega : (r.val * u) % 5 ≤ 3)
    exact h_eval r 0 (by push_cast; linarith) (by push_cast; linarith)
  · rcases lt_or_ge fr (2 / 5) with h2 | h2
    · refine ⟨pick 3, pick 4, fun r hr1 hr2 => ?_⟩
      have hm3 := hpick_ne r 3 (by omega) hr1
      have hm4 := hpick_ne r 4 (by omega) hr2
      have hmlt : (r.val * u) % 5 < 5 := Nat.mod_lt _ (by omega)
      have hm_le2 : (((r.val * u) % 5 : ℕ) : ℝ) ≤ 2 := by exact_mod_cast (by omega : (r.val * u) % 5 ≤ 2)
      have hm_ge0 : (0 : ℝ) ≤ (((r.val * u) % 5 : ℕ) : ℝ) := by positivity
      exact h_eval r 0 (by push_cast; linarith) (by push_cast; linarith)
    · rcases lt_or_ge fr (3 / 5) with h3 | h3
      · refine ⟨pick 2, pick 3, fun r hr1 hr2 => ?_⟩
        have hm2 := hpick_ne r 2 (by omega) hr1
        have hm3 := hpick_ne r 3 (by omega) hr2
        have hmlt : (r.val * u) % 5 < 5 := Nat.mod_lt _ (by omega)
        rcases eq_or_ne ((r.val * u) % 5) 4 with hm4 | hm_le1
        · exact h_eval r 1 (by rw [hm4]; push_cast; linarith) (by rw [hm4]; push_cast; linarith)
        · have hm_le1' : (((r.val * u) % 5 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast (by omega : (r.val * u) % 5 ≤ 1)
          have hm_ge0 : (0 : ℝ) ≤ (((r.val * u) % 5 : ℕ) : ℝ) := by positivity
          exact h_eval r 0 (by push_cast; linarith) (by push_cast; linarith)
      · rcases lt_or_ge fr (4 / 5) with h4 | h4
        · refine ⟨pick 1, pick 2, fun r hr1 hr2 => ?_⟩
          have hm1 := hpick_ne r 1 (by omega) hr1
          have hm2 := hpick_ne r 2 (by omega) hr2
          have hmlt : (r.val * u) % 5 < 5 := Nat.mod_lt _ (by omega)
          rcases eq_or_ne ((r.val * u) % 5) 0 with hm0 | hm_ge3
          · exact h_eval r 0 (by rw [hm0]; push_cast; linarith) (by rw [hm0]; push_cast; linarith)
          · have hm_ge3' : (3 : ℝ) ≤ (((r.val * u) % 5 : ℕ) : ℝ) := by exact_mod_cast (by omega : 3 ≤ (r.val * u) % 5)
            have hm_le4 : (((r.val * u) % 5 : ℕ) : ℝ) ≤ 4 := by exact_mod_cast (by omega : (r.val * u) % 5 ≤ 4)
            exact h_eval r 1 (by push_cast; linarith) (by push_cast; linarith)
        · refine ⟨pick 0, pick 1, fun r hr1 hr2 => ?_⟩
          have hm0 := hpick_ne r 0 (by omega) hr1
          have hm1 := hpick_ne r 1 (by omega) hr2
          have hmlt : (r.val * u) % 5 < 5 := Nat.mod_lt _ (by omega)
          have hm_ge2 : (2 : ℝ) ≤ (((r.val * u) % 5 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ (r.val * u) % 5)
          have hm_le4 : (((r.val * u) % 5 : ℕ) : ℝ) ≤ 4 := by exact_mod_cast (by omega : (r.val * u) % 5 ≤ 4)
          exact h_eval r 1 (by push_cast; linarith) (by push_cast; linarith)

private lemma exists_fin5_ne4 (a b c d : Fin 5) :
    ∃ r : Fin 5, r ≠ a ∧ r ≠ b ∧ r ≠ c ∧ r ≠ d := by
  revert a b c d; decide

private lemma coset5_div5_preserve (t' : ℝ) (r w : ℕ) (hw5 : 5 ∣ w) :
    (((t' + (r : ℝ)) / 5 * (w : ℝ) : ℝ) : UnitAddCircle) =
      ((t' * ((w / 5 : ℕ) : ℝ) : ℝ) : UnitAddCircle) := by
  have hw_eq : 5 * (w / 5) = w := Nat.mul_div_cancel' hw5
  have hw_cast : (w : ℝ) = 5 * ((w / 5 : ℕ) : ℝ) := by exact_mod_cast hw_eq.symm
  have h_mul : (t' + (r : ℝ)) / 5 * (w : ℝ) =
      t' * ((w / 5 : ℕ) : ℝ) + ((r * (w / 5) : ℕ) : ℝ) := by
    rw [hw_cast]; push_cast; ring
  rw [h_mul, QuotientAddGroup.mk_add]
  have h1_zero : ((1 : ℝ) : UnitAddCircle) = 0 :=
    (QuotientAddGroup.eq_zero_iff (1 : ℝ)).mpr (AddSubgroup.mem_zmultiples (1 : ℝ))
  have h_int_zero : ((((r * (w / 5) : ℕ) : ℝ)) : UnitAddCircle) = 0 := by
    rw [← nsmul_one (r * (w / 5)), QuotientAddGroup.mk_nsmul, h1_zero, smul_zero]
  rw [h_int_zero, add_zero]

private lemma lrc_four_two_div5 (a b c d : ℕ)
    (ha_pos : 0 < a) (hab : a < b)
    (ha5 : 5 ∣ a) (hb5 : 5 ∣ b) (hc5 : ¬ 5 ∣ c) (hd5 : ¬ 5 ∣ d) :
    ∃ t : ℝ, t ≥ 0 ∧
      dist ((t * (a : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / 5 ∧
      dist ((t * (b : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / 5 ∧
      dist ((t * (c : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / 5 ∧
      dist ((t * (d : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / 5 := by
  have ha_eq : 5 * (a / 5) = a := Nat.mul_div_cancel' ha5
  have hb_eq : 5 * (b / 5) = b := Nat.mul_div_cancel' hb5
  have hua_pos : 0 < a / 5 := by omega
  have hub_lt : a / 5 < b / 5 := by omega
  let v : Fin 2 → ℝ := fun i => if i.val = 0 then ((a / 5 : ℕ) : ℝ) else ((b / 5 : ℕ) : ℝ)
  have hv_pos : ∀ i : Fin 2, 0 < v i := by
    intro i; fin_cases i <;> dsimp [v] <;> exact_mod_cast (by omega)
  have hv_mono : StrictMono v := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [v] at hij ⊢
    exact_mod_cast hub_lt
  obtain ⟨t', ht'0, ht'_lonely⟩ := lrc_pos_two v hv_pos hv_mono
  obtain ⟨c1, c2, hc_ok⟩ := coset5_bad_at_most_two t' c hc5
  obtain ⟨d1, d2, hd_ok⟩ := coset5_bad_at_most_two t' d hd5
  obtain ⟨r, hrc1, hrc2, hrd1, hrd2⟩ := exists_fin5_ne4 c1 c2 d1 d2
  refine ⟨(t' + (r.val : ℝ)) / 5, by positivity, ?_, ?_, hc_ok r hrc1 hrc2, hd_ok r hrd1 hrd2⟩
  · rw [coset5_div5_preserve t' r.val a ha5]
    have h0 := ht'_lonely 0
    dsimp [v] at h0
    linarith [show (1 : ℝ) / 5 ≤ 1 / ((2 + 1 : ℕ) : ℝ) by norm_num]
  · rw [coset5_div5_preserve t' r.val b hb5]
    have h1 := ht'_lonely 1
    dsimp [v] at h1
    linarith [show (1 : ℝ) / 5 ≤ 1 / ((2 + 1 : ℕ) : ℝ) by norm_num]

private lemma lrc_four_three_div5 (a b c d : ℕ)
    (ha_pos : 0 < a) (hab : a < b) (hbc : b < c)
    (ha5 : 5 ∣ a) (hb5 : 5 ∣ b) (hc5 : 5 ∣ c) (hd5 : ¬ 5 ∣ d) :
    ∃ t : ℝ, t ≥ 0 ∧
      dist ((t * (a : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / 5 ∧
      dist ((t * (b : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / 5 ∧
      dist ((t * (c : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / 5 ∧
      dist ((t * (d : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / 5 := by
  have ha_eq : 5 * (a / 5) = a := Nat.mul_div_cancel' ha5
  have hb_eq : 5 * (b / 5) = b := Nat.mul_div_cancel' hb5
  have hc_eq : 5 * (c / 5) = c := Nat.mul_div_cancel' hc5
  have hua_pos : 0 < a / 5 := by omega
  have hub_lt : a / 5 < b / 5 := by omega
  have huc_lt : b / 5 < c / 5 := by omega
  let v : Fin 3 → ℝ := fun i =>
    if i.val = 0 then ((a / 5 : ℕ) : ℝ)
    else if i.val = 1 then ((b / 5 : ℕ) : ℝ)
    else ((c / 5 : ℕ) : ℝ)
  have hv_pos : ∀ i : Fin 3, 0 < v i := by
    intro i; fin_cases i <;> dsimp [v] <;> exact_mod_cast (by omega)
  have hv_mono : StrictMono v := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [v] at hij ⊢ <;> exact_mod_cast (by omega)
  obtain ⟨t', ht'0, ht'_lonely⟩ := lrc_pos_three v hv_pos hv_mono
  obtain ⟨d1, d2, hd_ok⟩ := coset5_bad_at_most_two t' d hd5
  obtain ⟨r, hrd1, hrd2, _, _⟩ := exists_fin5_ne4 d1 d2 d2 d2
  refine ⟨(t' + (r.val : ℝ)) / 5, by positivity, ?_, ?_, ?_, hd_ok r hrd1 hrd2⟩
  · rw [coset5_div5_preserve t' r.val a ha5]
    have h0 := ht'_lonely 0
    dsimp [v] at h0
    linarith [show (1 : ℝ) / 5 ≤ 1 / ((3 + 1 : ℕ) : ℝ) by norm_num]
  · rw [coset5_div5_preserve t' r.val b hb5]
    have h1 := ht'_lonely 1
    dsimp [v] at h1
    linarith [show (1 : ℝ) / 5 ≤ 1 / ((3 + 1 : ℕ) : ℝ) by norm_num]
  · rw [coset5_div5_preserve t' r.val c hc5]
    have h2 := ht'_lonely 2
    dsimp [v] at h2
    linarith [show (1 : ℝ) / 5 ≤ 1 / ((3 + 1 : ℕ) : ℝ) by norm_num]

private lemma lrc_nat_four (w : Fin 4 → ℕ)
    (hw_pos : ∀ i : Fin 4, 0 < w i) (hw_mono : StrictMono w) :
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin 4, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((4 + 1 : ℕ) : ℝ) := by
  refine lrc_nat_gcd_reduction 4 (by omega) w hw_pos hw_mono ?_
  intro u hu_pos hu_mono hu_gcd
  have h01 : u 0 < u 1 := hu_mono (by decide)
  have h12 : u 1 < u 2 := hu_mono (by decide)
  have h23 : u 2 < u 3 := hu_mono (by decide)
  have h02 : u 0 < u 2 := lt_trans h01 h12
  have h03 : u 0 < u 3 := lt_trans h02 h23
  have h13 : u 1 < u 3 := lt_trans h12 h23
  have hcast5 : (1 : ℝ) / ((4 + 1 : ℕ) : ℝ) = 1 / 5 := by norm_num
  have wrap : ∀ {t : ℝ}, t ≥ 0 →
      dist ((t * (u 0 : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / 5 →
      dist ((t * (u 1 : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / 5 →
      dist ((t * (u 2 : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / 5 →
      dist ((t * (u 3 : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / 5 →
      ∃ t' : ℝ, t' ≥ 0 ∧
        ∀ i : Fin 4, dist ((t' * (u i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((4 + 1 : ℕ) : ℝ) := by
    intro t ht d0 d1 d2 d3
    refine ⟨t, ht, fun i => ?_⟩
    rw [hcast5]
    fin_cases i <;> assumption
  by_cases d0 : 5 ∣ u 0 <;> by_cases d1 : 5 ∣ u 1 <;> by_cases d2 : 5 ∣ u 2 <;> by_cases d3 : 5 ∣ u 3
  · -- 1111: impossible since gcd = 1
    exfalso
    have hdvd : 5 ∣ Finset.univ.gcd u := by
      refine Finset.dvd_gcd fun i _ => ?_
      fin_cases i <;> assumption
    rw [hu_gcd] at hdvd
    omega
  · -- 1110
    obtain ⟨t, ht, h0, h1, h2, h3⟩ := lrc_four_three_div5 (u 0) (u 1) (u 2) (u 3) (hu_pos 0) h01 h12 d0 d1 d2 d3
    exact wrap ht h0 h1 h2 h3
  · -- 1101
    obtain ⟨t, ht, h0, h1, h3, h2⟩ := lrc_four_three_div5 (u 0) (u 1) (u 3) (u 2) (hu_pos 0) h01 h13 d0 d1 d3 d2
    exact wrap ht h0 h1 h2 h3
  · -- 1100
    obtain ⟨t, ht, h0, h1, h2, h3⟩ := lrc_four_two_div5 (u 0) (u 1) (u 2) (u 3) (hu_pos 0) h01 d0 d1 d2 d3
    exact wrap ht h0 h1 h2 h3
  · -- 1011
    obtain ⟨t, ht, h0, h2, h3, h1⟩ := lrc_four_three_div5 (u 0) (u 2) (u 3) (u 1) (hu_pos 0) h02 h23 d0 d2 d3 d1
    exact wrap ht h0 h1 h2 h3
  · -- 1010
    obtain ⟨t, ht, h0, h2, h1, h3⟩ := lrc_four_two_div5 (u 0) (u 2) (u 1) (u 3) (hu_pos 0) h02 d0 d2 d1 d3
    exact wrap ht h0 h1 h2 h3
  · -- 1001
    obtain ⟨t, ht, h0, h3, h1, h2⟩ := lrc_four_two_div5 (u 0) (u 3) (u 1) (u 2) (hu_pos 0) h03 d0 d3 d1 d2
    exact wrap ht h0 h1 h2 h3
  · -- 1000
    obtain ⟨t, ht, h0, h1, h2, h3⟩ := lrc_four_one_div5 (u 0) (u 1) (u 2) (u 3) (hu_pos 0) d0 d1 d2 d3
    exact wrap ht h0 h1 h2 h3
  · -- 0111
    obtain ⟨t, ht, h1, h2, h3, h0⟩ := lrc_four_three_div5 (u 1) (u 2) (u 3) (u 0) (hu_pos 1) h12 h23 d1 d2 d3 d0
    exact wrap ht h0 h1 h2 h3
  · -- 0110
    obtain ⟨t, ht, h1, h2, h0, h3⟩ := lrc_four_two_div5 (u 1) (u 2) (u 0) (u 3) (hu_pos 1) h12 d1 d2 d0 d3
    exact wrap ht h0 h1 h2 h3
  · -- 0101
    obtain ⟨t, ht, h1, h3, h0, h2⟩ := lrc_four_two_div5 (u 1) (u 3) (u 0) (u 2) (hu_pos 1) h13 d1 d3 d0 d2
    exact wrap ht h0 h1 h2 h3
  · -- 0100
    obtain ⟨t, ht, h1, h0, h2, h3⟩ := lrc_four_one_div5 (u 1) (u 0) (u 2) (u 3) (hu_pos 1) d1 d0 d2 d3
    exact wrap ht h0 h1 h2 h3
  · -- 0011
    obtain ⟨t, ht, h2, h3, h0, h1⟩ := lrc_four_two_div5 (u 2) (u 3) (u 0) (u 1) (hu_pos 2) h23 d2 d3 d0 d1
    exact wrap ht h0 h1 h2 h3
  · -- 0010
    obtain ⟨t, ht, h2, h0, h1, h3⟩ := lrc_four_one_div5 (u 2) (u 0) (u 1) (u 3) (hu_pos 2) d2 d0 d1 d3
    exact wrap ht h0 h1 h2 h3
  · -- 0001
    obtain ⟨t, ht, h3, h0, h1, h2⟩ := lrc_four_one_div5 (u 3) (u 0) (u 1) (u 2) (hu_pos 3) d3 d0 d1 d2
    exact wrap ht h0 h1 h2 h3
  · -- 0000
    refine lrc_nat_not_dvd 4 u (fun i => ?_)
    fin_cases i <;> assumption

-- General small-modulus sieve: for ANY 1 ≤ d ≤ m + 1, if no speed is divisible by d,
-- t = 1 / d achieves loneliness ≥ 1 / d ≥ 1 / (m + 1).
private lemma lrc_nat_not_dvd_le (m d : ℕ) (hm1 : 1 ≤ m) (hd1 : 1 ≤ d) (hdm : d ≤ m + 1)
    (w : Fin m → ℕ) (h_ndvd : ∀ i : Fin m, ¬ d ∣ w i) :
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin m, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((m + 1 : ℕ) : ℝ) := by
  rcases eq_or_ne d 1 with rfl | hd_ne1
  · exfalso; exact h_ndvd ⟨0, by omega⟩ (one_dvd _)
  · have hd2 : 2 ≤ d := by omega
    have hd_pos : (0 : ℝ) < (d : ℝ) := by positivity
    refine ⟨1 / (d : ℝ), by positivity, fun i => ?_⟩
    let q : ℕ := w i / d
    let r : ℕ := w i % d
    have hdiv : d * q + r = w i := Nat.div_add_mod (w i) d
    have hr_ge : 1 ≤ r :=
      Nat.one_le_iff_ne_zero.mpr (fun hr0 => h_ndvd i (Nat.dvd_of_mod_eq_zero hr0))
    have hr_le : r ≤ d - 1 := by
      have hlt : r < d := Nat.mod_lt (w i) (by omega)
      omega
    have h_eq : 1 / (d : ℝ) * (w i : ℝ) = ((q : ℤ) : ℝ) + (r : ℝ) / (d : ℝ) := by
      have hwi_cast : (w i : ℝ) = (d : ℝ) * (q : ℝ) + (r : ℝ) := by exact_mod_cast hdiv.symm
      rw [hwi_cast, Int.cast_natCast]; field_simp [ne_of_gt hd_pos]
    rw [h_eq]
    have hlo : ((q : ℤ) : ℝ) + 1 / (d : ℝ) ≤ ((q : ℤ) : ℝ) + (r : ℝ) / (d : ℝ) := by
      have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr_ge
      linarith [div_le_div_of_nonneg_right hr1 hd_pos.le]
    have hhi : ((q : ℤ) : ℝ) + (r : ℝ) / (d : ℝ) ≤ ((q : ℤ) : ℝ) + 1 - 1 / (d : ℝ) := by
      have hrd : (r : ℝ) ≤ ((d - 1 : ℕ) : ℝ) := by exact_mod_cast hr_le
      have hd_sub : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
      have hdiv_le : (r : ℝ) / (d : ℝ) ≤ 1 - 1 / (d : ℝ) := by
        rw [div_le_iff₀ hd_pos]
        have h_rhs : (1 - 1 / (d : ℝ)) * (d : ℝ) = (d : ℝ) - 1 := by
          field_simp [ne_of_gt hd_pos]
        linarith
      linarith
    have hdist_d := unitAddCircle_dist_ge_of_Icc _ (1 / (d : ℝ)) (q : ℤ) hlo hhi
    have hle : 1 / ((m + 1 : ℕ) : ℝ) ≤ 1 / (d : ℝ) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hdm)
    exact le_trans hle hdist_d

-- Parity sieve 1: if all speeds are odd (m ≥ 1), t = 1 / 2 works.
private lemma lrc_nat_all_odd (m : ℕ) (hm1 : 1 ≤ m) (w : Fin m → ℕ)
    (h_odd : ∀ i : Fin m, ¬ 2 ∣ w i) :
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin m, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((m + 1 : ℕ) : ℝ) :=
  lrc_nat_not_dvd_le m 2 hm1 (by omega) (by omega) w h_odd

-- Parity sieve 2: for m ≥ 3, if at most one speed is even and that even speed is not divisible by 4
-- (more generally, if no speed is divisible by 4), t = 1 / 4 works.
private lemma lrc_nat_unique_even_not_dvd_four (m : ℕ) (hm3 : 3 ≤ m) (w : Fin m → ℕ)
    (i₀ : Fin m) (h_other_odd : ∀ i : Fin m, i ≠ i₀ → ¬ 2 ∣ w i) (h_not_4 : ¬ 4 ∣ w i₀) :
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin m, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((m + 1 : ℕ) : ℝ) := by
  refine lrc_nat_not_dvd_le m 4 (by omega) (by omega) (by omega) w fun i h4 => ?_
  rcases eq_or_ne i i₀ with rfl | hne
  · exact h_not_4 h4
  · exact h_other_odd i hne (dvd_trans (by decide : 2 ∣ 4) h4)

-- Top-speed inductive ratio bound: if LRC holds for m - 1 runners and m * w (m - 2) ≤ w (m - 1),
-- then LRC holds for w on [t₀ + 1 - Δ, t₀ + 1 + Δ] with Δ = 1 / (m * (m + 1) * w (m - 2)).
private lemma lrc_nat_last_speed_bound (m : ℕ) (hm3 : 3 ≤ m) (w : Fin m → ℕ)
    (hw_pos : ∀ i : Fin m, 0 < w i) (hw_mono : StrictMono w)
    (h_top_lac : m * w ⟨m - 2, by omega⟩ ≤ w ⟨m - 1, by omega⟩)
    (h_prev : ∀ (u : Fin (m - 1) → ℕ), (∀ l : Fin (m - 1), 0 < u l) → StrictMono u →
      ∃ t : ℝ, t ≥ 0 ∧
        ∀ l : Fin (m - 1), dist ((t * (u l : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((m - 1 + 1 : ℕ) : ℝ)) :
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin m, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((m + 1 : ℕ) : ℝ) := by
  let u : Fin (m - 1) → ℕ := fun l => w ⟨l.val, by omega⟩
  have hu_pos : ∀ l : Fin (m - 1), 0 < u l := fun l => hw_pos ⟨l.val, by omega⟩
  have hu_mono : StrictMono u := fun l₁ l₂ hlt => hw_mono (by rw [Fin.lt_def]; exact hlt)
  obtain ⟨t₀, ht₀, ht₀_lonely⟩ := h_prev u hu_pos hu_mono
  let iprev : Fin m := ⟨m - 2, by omega⟩
  let ilast : Fin m := ⟨m - 1, by omega⟩
  have hw_prev_pos : (0 : ℝ) < (w iprev : ℝ) := Nat.cast_pos.mpr (hw_pos iprev)
  have hw_last_pos : (0 : ℝ) < (w ilast : ℝ) := Nat.cast_pos.mpr (hw_pos ilast)
  have hm_pos : (0 : ℝ) < (m : ℝ) := by positivity
  have hm1_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  let δ : ℝ := 1 / ((m + 1 : ℕ) : ℝ)
  let Δ : ℝ := 1 / ((m : ℝ) * ((m + 1 : ℕ) : ℝ) * (w iprev : ℝ))
  have hΔ_pos : 0 < Δ := by positivity
  have hΔ_le_one : Δ ≤ 1 := by
    dsimp [Δ]
    rw [div_le_iff₀ (by positivity)]
    have hm_ge : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
    have hm1_ge : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ m + 1)
    have hw_ge : (1 : ℝ) ≤ (w iprev : ℝ) := by exact_mod_cast (hw_pos iprev)
    have h12 : (1 : ℝ) ≤ (m : ℝ) * ((m + 1 : ℕ) : ℝ) := by nlinarith
    nlinarith
  let t₁ : ℝ := t₀ + 1
  have ht₁_sub_nonneg : 0 ≤ t₁ - Δ := by dsimp [t₁]; linarith
  have hBA : 2 * (0 : ℝ) + 2 * δ ≤ (w ilast : ℝ) * (t₁ + Δ) - (w ilast : ℝ) * (t₁ - Δ) := by
    have hdiff : (w ilast : ℝ) * (t₁ + Δ) - (w ilast : ℝ) * (t₁ - Δ) =
        (2 * (w ilast : ℝ)) / ((m : ℝ) * ((m + 1 : ℕ) : ℝ) * (w iprev : ℝ)) := by
      dsimp [Δ]; ring
    rw [hdiff]
    dsimp [δ]
    have h2δ : 2 * (0 : ℝ) + 2 * (1 / ((m + 1 : ℕ) : ℝ)) = 2 / ((m + 1 : ℕ) : ℝ) := by ring
    rw [h2δ, div_le_div_iff₀ hm1_pos (by positivity)]
    have htop_cast : (m : ℝ) * (w iprev : ℝ) ≤ (w ilast : ℝ) := by exact_mod_cast h_top_lac
    nlinarith
  have h2δ_le_1 : (0 : ℝ) + 2 * δ ≤ 1 := by
    dsimp [δ]
    have hm4 : (4 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 4 ≤ m + 1)
    rw [ zero_add, mul_one_div, div_le_iff₀ hm1_pos ]
    linarith
  obtain ⟨C, D, z, hAC, hDB, hDC, hz1, hz2⟩ :=
    exists_subinterval_dist_ge ((w ilast : ℝ) * (t₁ - Δ)) ((w ilast : ℝ) * (t₁ + Δ)) δ 0
      (by positivity) le_rfl h2δ_le_1 hBA
  have hCD : C = D := by linarith
  let t : ℝ := C / (w ilast : ℝ)
  have ht_lo : t₁ - Δ ≤ t := (le_div_iff₀ hw_last_pos).mpr (by linarith)
  have ht_hi : t ≤ t₁ + Δ := (div_le_iff₀ hw_last_pos).mpr (by linarith)
  refine ⟨t, le_trans ht₁_sub_nonneg ht_lo, fun i => ?_⟩
  rcases le_or_gt i.val (m - 2) with hi_le | hi_gt
  · let l : Fin (m - 1) := ⟨i.val, by omega⟩
    have hul : u l = w i := by dsimp [u, l]
    have ht₀_i : dist ((t₀ * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / (m : ℝ) := by
      have hstep := ht₀_lonely l
      have hmsub : m - 1 + 1 = m := by omega
      rw [hul, hmsub] at hstep
      exact hstep
    have ht₁_eq : ((t₁ * (w i : ℝ) : ℝ) : UnitAddCircle) = ((t₀ * (w i : ℝ) : ℝ) : UnitAddCircle) := by
      have hexp : t₁ * (w i : ℝ) = t₀ * (w i : ℝ) + (w i : ℝ) := by dsimp [t₁]; ring
      rw [hexp]
      exact unitAddCircle_add_nat (t₀ * (w i : ℝ)) (w i)
    have hwi_le : (w i : ℝ) ≤ (w iprev : ℝ) := by
      rcases lt_or_eq_of_le hi_le with hlt | heq
      · exact (Nat.cast_lt.mpr (hw_mono (by rw [Fin.lt_def]; dsimp [iprev]; exact hlt))).le
      · have hfin : i = iprev := Fin.ext heq
        rw [hfin]
    have habs_diff : |t * (w i : ℝ) - t₁ * (w i : ℝ)| ≤ 1 / ((m : ℝ) * ((m + 1 : ℕ) : ℝ)) := by
      rw [← sub_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (w i : ℝ))]
      have habs_t : |t - t₁| ≤ Δ := abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
      have hmul_le : |t - t₁| * (w i : ℝ) ≤ Δ * (w iprev : ℝ) :=
        mul_le_mul habs_t hwi_le (by positivity) hΔ_pos.le
      have hΔ_simp : Δ * (w iprev : ℝ) = 1 / ((m : ℝ) * ((m + 1 : ℕ) : ℝ)) := by
        dsimp [Δ]
        field_simp [ne_of_gt hm_pos, ne_of_gt hm1_pos, ne_of_gt hw_prev_pos]
      linarith
    have hdist_step : dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) ((t₁ * (w i : ℝ) : ℝ) : UnitAddCircle) ≤
        1 / ((m : ℝ) * ((m + 1 : ℕ) : ℝ)) :=
      le_trans (unitAddCircle_dist_le_abs_sub _ _) habs_diff
    have htri := dist_triangle ((t₀ * (w i : ℝ) : ℝ) : UnitAddCircle)
      ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0
    have hdist_eq : dist ((t₀ * (w i : ℝ) : ℝ) : UnitAddCircle) ((t * (w i : ℝ) : ℝ) : UnitAddCircle) =
        dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) ((t₁ * (w i : ℝ) : ℝ) : UnitAddCircle) := by
      rw [← ht₁_eq, dist_comm]
    rw [hdist_eq] at htri
    have hfrac_sub : 1 / (m : ℝ) - 1 / ((m : ℝ) * ((m + 1 : ℕ) : ℝ)) = 1 / ((m + 1 : ℕ) : ℝ) := by
      field_simp [ne_of_gt hm_pos, ne_of_gt hm1_pos]
      push_cast; ring
    change 1 / ((m + 1 : ℕ) : ℝ) ≤ dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0
    have ht₀_i' : 1 / (m : ℝ) ≤ dist ((t₀ * (w i : ℝ) : ℝ) : UnitAddCircle) 0 := ht₀_i
    linarith
  · have hi_eq : i = ilast := Fin.ext (by dsimp [ilast]; omega)
    rw [hi_eq]
    have hmul : t * (w ilast : ℝ) = C := div_mul_cancel₀ C (ne_of_gt hw_last_pos)
    rw [hmul]
    exact unitAddCircle_dist_ge_of_Icc C δ z hz1 (hCD ▸ hz2)

-- Integer count bound in an open real interval of width 2 * p / (m + 1).
private lemma finset_int_card_open_interval (A : ℝ) (p m : ℕ)
    (X : Finset ℤ)
    (hX : ∀ x ∈ X, A < (x : ℝ) ∧ (x : ℝ) < A + (2 * (p : ℝ)) / ((m + 1 : ℕ) : ℝ)) :
    X.card ≤ (2 * p - 1) / (m + 1) + 1 := by
  rcases X.eq_empty_or_nonempty with rfl | hne
  · simp
  · let x₀ : ℤ := X.min' hne
    let x₁ : ℤ := X.max' hne
    have hx₀_mem : x₀ ∈ X := Finset.min'_mem X hne
    have hx₁_mem : x₁ ∈ X := Finset.max'_mem X hne
    have hx₀_le_x₁ : x₀ ≤ x₁ := Finset.min'_le X x₁ hx₁_mem
    have hlo := (hX x₀ hx₀_mem).1
    have hhi := (hX x₁ hx₁_mem).2
    let d : ℕ := (x₁ - x₀).toNat
    have hd_eq : (d : ℤ) = x₁ - x₀ := Int.toNat_of_nonneg (by omega)
    have hd_eq_r : (d : ℝ) = (x₁ : ℝ) - (x₀ : ℝ) := by exact_mod_cast hd_eq
    have hdiff_r : (d : ℝ) < (2 * (p : ℝ)) / ((m + 1 : ℕ) : ℝ) := by linarith
    have hm1_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
    have hmul_r : (((m + 1) * d : ℕ) : ℝ) < ((2 * p : ℕ) : ℝ) := by
      have h1 := (lt_div_iff₀ hm1_pos).mp hdiff_r
      push_cast at h1 ⊢
      linarith
    have hmul_lt : (m + 1) * d < 2 * p := Nat.cast_lt.mp hmul_r
    have hmul_n : d * (m + 1) ≤ 2 * p - 1 := by
      have hcomm : d * (m + 1) = (m + 1) * d := Nat.mul_comm d (m + 1)
      omega
    have hd_le : d ≤ (2 * p - 1) / (m + 1) :=
      (Nat.le_div_iff_mul_le (Nat.succ_pos m)).mpr hmul_n
    have hsub_Icc : X ⊆ Finset.Icc x₀ x₁ := fun x hx =>
      Finset.mem_Icc.mpr ⟨Finset.min'_le X x hx, Finset.le_max' X x hx⟩
    have hcard_le : X.card ≤ (Finset.Icc x₀ x₁).card := Finset.card_le_card hsub_Icc
    rw [Int.card_Icc] at hcard_le
    have h_icccard : (x₁ + 1 - x₀).toNat = d + 1 := by omega
    omega

-- General s-subset prime-coset shifting sieve (Rosenfeld / Barajas-Serra / BHK).
private lemma lrc_nat_prime_coset_sieve (m : ℕ) (hm3 : 3 ≤ m) (w : Fin m → ℕ)
    (hw_pos : ∀ i : Fin m, 0 < w i) (hw_mono : StrictMono w)
    (hw_gcd : Finset.univ.gcd w = 1)
    (S : Finset (Fin m)) (hS_ne : S.Nonempty) (p : ℕ) (hp_prime : Nat.Prime p)
    (hp_dvd_S : ∀ i ∈ S, p ∣ w i)
    (h_sieve : (m - S.card) * ((2 * p - 1) / (m + 1) + 1) < p)
    (h_prev : ∀ (s : ℕ), 1 ≤ s → s < m → ∀ (u : Fin s → ℕ),
      (∀ l : Fin s, 0 < u l) → StrictMono u →
      ∃ t : ℝ, t ≥ 0 ∧
        ∀ l : Fin s, dist ((t * (u l : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((s + 1 : ℕ) : ℝ)) :
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin m, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((m + 1 : ℕ) : ℝ) := by
  open Classical in
  have hp2 : 2 ≤ p := hp_prime.two_le
  have hp_pos_r : (0 : ℝ) < (p : ℝ) := by positivity
  have hm1_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  let U : Finset (Fin m) := Finset.univ.filter (fun i => p ∣ w i)
  let V : Finset (Fin m) := Finset.univ.filter (fun i => ¬ p ∣ w i)
  have hS_sub_U : S ⊆ U := fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ i, hp_dvd_S i hi⟩
  have hS_le_U : S.card ≤ U.card := Finset.card_le_card hS_sub_U
  have hS_pos : 1 ≤ S.card := Finset.Nonempty.card_pos hS_ne
  have hUV_sum : U.card + V.card = m := by
    have hdisj : Disjoint U V := Finset.disjoint_left.mpr fun i hiU hiV =>
      (Finset.mem_filter.mp hiV).2 (Finset.mem_filter.mp hiU).2
    have hunion : U ∪ V = Finset.univ := by
      ext i
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, U, V]
      exact iff_of_true (Classical.em (p ∣ w i)) trivial
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_fin]
  have hV_pos : 1 ≤ V.card := by
    rcases Nat.eq_zero_or_pos V.card with hV0 | hpos
    · exfalso
      have hV_emp : V = ∅ := Finset.card_eq_zero.mp hV0
      have hdvd_all : p ∣ Finset.univ.gcd w := by
        refine Finset.dvd_gcd fun i _ => ?_
        by_contra hnd
        have hiV : i ∈ V := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hnd⟩
        rw [hV_emp] at hiV
        exact Finset.notMem_empty i hiV
      rw [hw_gcd] at hdvd_all
      have hp1 : p ≤ 1 := Nat.le_of_dvd zero_lt_one hdvd_all
      omega
    · exact hpos
  let s : ℕ := U.card
  have hs1 : 1 ≤ s := le_trans hS_pos hS_le_U
  have hslt : s < m := by omega
  let emb := U.orderEmbOfFin rfl
  let u : Fin s → ℕ := fun l => w (emb l) / p
  have hu_mul : ∀ l : Fin s, p * u l = w (emb l) := fun l =>
    Nat.mul_div_cancel' (Finset.mem_filter.mp (Finset.orderEmbOfFin_mem U rfl l)).2
  have hu_pos : ∀ l : Fin s, 0 < u l := by
    intro l
    rcases Nat.eq_zero_or_pos (u l) with hu0 | hpos
    · exfalso; exact Nat.ne_of_gt (hw_pos (emb l)) (by rw [← hu_mul l, hu0, mul_zero])
    · exact hpos
  have hu_mono : StrictMono u := fun l₁ l₂ hlt =>
    lt_of_mul_lt_mul_left' (by rw [hu_mul l₁, hu_mul l₂]; exact hw_mono (emb.strictMono hlt))
  obtain ⟨t', ht'0, ht'_lonely⟩ := h_prev s hs1 hslt u hu_pos hu_mono
  let δ : ℝ := 1 / ((m + 1 : ℕ) : ℝ)
  let B : Fin m → Finset (Fin p) := fun j =>
    Finset.univ.filter (fun r : Fin p =>
      dist (((t' + (r.val : ℝ)) / (p : ℝ) * (w j : ℝ) : ℝ) : UnitAddCircle) 0 < δ)
  have hB_card : ∀ j ∈ V, (B j).card ≤ (2 * p - 1) / (m + 1) + 1 := by
    intro j hjV
    have hp_ndvd_j : ¬ p ∣ w j := (Finset.mem_filter.mp hjV).2
    have hcop : Nat.Coprime (w j) p := (hp_prime.coprime_iff_not_dvd.mpr hp_ndvd_j).symm
    let f : Fin p → ℤ := fun r =>
      (r.val : ℤ) * (w j : ℤ) - (p : ℤ) * round ((t' + (r.val : ℝ)) / (p : ℝ) * (w j : ℝ))
    have hf_inj : Function.Injective f := by
      intro r₁ r₂ heq
      by_contra hne
      have hval_ne : r₁.val ≠ r₂.val := fun hv => hne (Fin.ext hv)
      let z₁ := round ((t' + (r₁.val : ℝ)) / (p : ℝ) * (w j : ℝ))
      let z₂ := round ((t' + (r₂.val : ℝ)) / (p : ℝ) * (w j : ℝ))
      have hsub_z : ((r₁.val : ℤ) - (r₂.val : ℤ)) * (w j : ℤ) = (p : ℤ) * (z₁ - z₂) := by
        dsimp [f, z₁, z₂] at heq ⊢
        linarith
      rcases lt_or_gt_of_ne hval_ne with hlt | hgt
      · have hdvd_z : (p : ℤ) ∣ ((r₂.val - r₁.val : ℕ) : ℤ) * (w j : ℤ) := by
          refine ⟨z₂ - z₁, ?_⟩
          have hcast : ((r₂.val - r₁.val : ℕ) : ℤ) = (r₂.val : ℤ) - (r₁.val : ℤ) := by omega
          rw [hcast]; linarith
        have hdvd_n : p ∣ (r₂.val - r₁.val) * w j := by exact_mod_cast hdvd_z
        have hdvd_diff : p ∣ r₂.val - r₁.val := hcop.symm.dvd_of_dvd_mul_right hdvd_n
        have hle_p : p ≤ r₂.val - r₁.val := Nat.le_of_dvd (by omega) hdvd_diff
        omega
      · have hdvd_z : (p : ℤ) ∣ ((r₁.val - r₂.val : ℕ) : ℤ) * (w j : ℤ) := by
          refine ⟨z₁ - z₂, ?_⟩
          have hcast : ((r₁.val - r₂.val : ℕ) : ℤ) = (r₁.val : ℤ) - (r₂.val : ℤ) := by omega
          rw [hcast]; linarith
        have hdvd_n : p ∣ (r₁.val - r₂.val) * w j := by exact_mod_cast hdvd_z
        have hdvd_diff : p ∣ r₁.val - r₂.val := hcop.symm.dvd_of_dvd_mul_right hdvd_n
        have hle_p : p ≤ r₁.val - r₂.val := Nat.le_of_dvd (by omega) hdvd_diff
        omega
    let A : ℝ := -t' * (w j : ℝ) - (p : ℝ) / ((m + 1 : ℕ) : ℝ)
    have h_img_open : ∀ x ∈ (B j).image f,
        A < (x : ℝ) ∧ (x : ℝ) < A + (2 * (p : ℝ)) / ((m + 1 : ℕ) : ℝ) := by
      intro x hx
      obtain ⟨r, hrB, rfl⟩ := Finset.mem_image.mp hx
      have hdist_lt : dist (((t' + (r.val : ℝ)) / (p : ℝ) * (w j : ℝ) : ℝ) : UnitAddCircle) 0 < δ :=
        (Finset.mem_filter.mp hrB).2
      rw [dist_zero_right, UnitAddCircle.norm_eq] at hdist_lt
      let xr : ℝ := (t' + (r.val : ℝ)) / (p : ℝ) * (w j : ℝ)
      have habs_lt : |xr - (round xr : ℝ)| < 1 / ((m + 1 : ℕ) : ℝ) := hdist_lt
      have h_id : t' * (w j : ℝ) + (f r : ℝ) = (p : ℝ) * (xr - (round xr : ℝ)) := by
        dsimp [f, xr]
        push_cast
        field_simp [ne_of_gt hp_pos_r]
        ring
      have habs_p := mul_lt_mul_of_pos_left habs_lt hp_pos_r
      rw [← abs_of_pos hp_pos_r, ← abs_mul, ← h_id, abs_of_pos hp_pos_r, mul_one_div] at habs_p
      have hbounds := abs_lt.mp habs_p
      have hA_hi : A + (2 * (p : ℝ)) / ((m + 1 : ℕ) : ℝ) =
          -t' * (w j : ℝ) + (p : ℝ) / ((m + 1 : ℕ) : ℝ) := by dsimp [A]; ring
      refine ⟨by dsimp [A]; linarith, by rw [hA_hi]; linarith⟩
    rw [← Finset.card_image_of_injective (B j) hf_inj]
    exact finset_int_card_open_interval A p m ((B j).image f) h_img_open
  have h_union_lt : (V.biUnion B).card < p := by
    have h1 : (V.biUnion B).card ≤ ∑ j ∈ V, (B j).card := Finset.card_biUnion_le
    have h2 : ∑ j ∈ V, (B j).card ≤ ∑ _j ∈ V, ((2 * p - 1) / (m + 1) + 1) :=
      Finset.sum_le_sum hB_card
    rw [Finset.sum_const, smul_eq_mul] at h2
    have hV_le : V.card ≤ m - S.card := by omega
    have h3 : V.card * ((2 * p - 1) / (m + 1) + 1) ≤ (m - S.card) * ((2 * p - 1) / (m + 1) + 1) :=
      Nat.mul_le_mul_right _ hV_le
    omega
  have h_ex_good : ∃ r : Fin p, r ∉ V.biUnion B := by
    by_contra h_all
    have h_univ_sub : (Finset.univ : Finset (Fin p)) ⊆ V.biUnion B := fun r _ =>
      Decidable.byContradiction fun hnr => h_all ⟨r, hnr⟩
    have hp_le := Finset.card_le_card h_univ_sub
    rw [Finset.card_fin] at hp_le
    omega
  obtain ⟨r, hr_good⟩ := h_ex_good
  refine ⟨(t' + (r.val : ℝ)) / (p : ℝ), by positivity, fun i => ?_⟩
  by_cases hp_i : p ∣ w i
  · have hi_U : i ∈ (U : Set (Fin m)) :=
      Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hp_i⟩)
    have hrange : Set.range emb = (U : Set (Fin m)) := Finset.range_orderEmbOfFin U rfl
    obtain ⟨l, hl⟩ : ∃ l : Fin s, emb l = i := by rwa [← hrange] at hi_U
    have hw_eq : (w i : ℝ) = (p : ℝ) * (u l : ℝ) := by rw [← hl]; exact_mod_cast (hu_mul l).symm
    have h_mul : (t' + (r.val : ℝ)) / (p : ℝ) * (w i : ℝ) =
        t' * (u l : ℝ) + ((r.val * u l : ℕ) : ℝ) := by
      rw [hw_eq]; push_cast; field_simp [ne_of_gt hp_pos_r]
    rw [h_mul, unitAddCircle_add_nat]
    have hstep := ht'_lonely l
    have hfrac : 1 / ((m + 1 : ℕ) : ℝ) ≤ 1 / ((s + 1 : ℕ) : ℝ) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast (by omega : s + 1 ≤ m + 1))
    exact le_trans hfrac hstep
  · have hi_V : i ∈ V := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hp_i⟩
    have hr_not_Bi : r ∉ B i := fun hrB => hr_good (Finset.mem_biUnion.mpr ⟨i, hi_V, hrB⟩)
    have h_not_lt : ¬ dist (((t' + (r.val : ℝ)) / (p : ℝ) * (w i : ℝ) : ℝ) : UnitAddCircle) 0 < δ :=
      fun hlt => hr_not_Bi (Finset.mem_filter.mpr ⟨Finset.mem_univ r, hlt⟩)
    exact le_of_not_gt h_not_lt

-- Special case 1: (m - 1)-subset coprimality sieve (m - S.card = 1 works for ALL primes p ≥ 2, m ≥ 3).
private lemma lrc_nat_one_exception_sieve (m : ℕ) (hm3 : 3 ≤ m) (w : Fin m → ℕ)
    (hw_pos : ∀ i : Fin m, 0 < w i) (hw_mono : StrictMono w)
    (hw_gcd : Finset.univ.gcd w = 1)
    (i₀ : Fin m) (h_sub_gcd : (Finset.univ.erase i₀).gcd w ≠ 1)
    (h_prev : ∀ (s : ℕ), 1 ≤ s → s < m → ∀ (u : Fin s → ℕ),
      (∀ l : Fin s, 0 < u l) → StrictMono u →
      ∃ t : ℝ, t ≥ 0 ∧
        ∀ l : Fin s, dist ((t * (u l : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((s + 1 : ℕ) : ℝ)) :
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin m, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((m + 1 : ℕ) : ℝ) := by
  let S : Finset (Fin m) := Finset.univ.erase i₀
  have hS_card : S.card = m - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_fin]
  have hS_ne : S.Nonempty := Finset.card_pos.mp (by omega)
  let p : ℕ := (S.gcd w).minFac
  have hp_prime : Nat.Prime p := Nat.minFac_prime h_sub_gcd
  have hp2 : 2 ≤ p := hp_prime.two_le
  have hp_dvd_S : ∀ i ∈ S, p ∣ w i := fun i hi =>
    dvd_trans (Nat.minFac_dvd _) (Finset.gcd_dvd hi)
  have hdiv_lt : (2 * p - 1) / (m + 1) + 1 < p := by
    have hdiv_le : (2 * p - 1) / (m + 1) ≤ (2 * p - 1) / 4 :=
      Nat.div_le_div_left (by omega) (by omega)
    omega
  refine lrc_nat_prime_coset_sieve m hm3 w hw_pos hw_mono hw_gcd S hS_ne p hp_prime hp_dvd_S ?_ h_prev
  rw [hS_card]
  have hm_sub : m - (m - 1) = 1 := by omega
  rw [hm_sub, one_mul]
  exact hdiv_lt

-- Special case 2: (m - 2)-subset prime sieve (works for p ≥ 5 when m ≥ 4, and p ≥ 3 when m ≥ 5).
private lemma lrc_nat_two_exception_sieve (m : ℕ) (hm4 : 4 ≤ m) (w : Fin m → ℕ)
    (hw_pos : ∀ i : Fin m, 0 < w i) (hw_mono : StrictMono w)
    (hw_gcd : Finset.univ.gcd w = 1)
    (S : Finset (Fin m)) (hS_card : S.card = m - 2)
    (p : ℕ) (hp_prime : Nat.Prime p) (hp_cond : 5 ≤ p ∨ (5 ≤ m ∧ 3 ≤ p))
    (hp_dvd_S : ∀ i ∈ S, p ∣ w i)
    (h_prev : ∀ (s : ℕ), 1 ≤ s → s < m → ∀ (u : Fin s → ℕ),
      (∀ l : Fin s, 0 < u l) → StrictMono u →
      ∃ t : ℝ, t ≥ 0 ∧
        ∀ l : Fin s, dist ((t * (u l : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((s + 1 : ℕ) : ℝ)) :
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin m, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((m + 1 : ℕ) : ℝ) := by
  have hS_ne : S.Nonempty := Finset.card_pos.mp (by omega)
  refine lrc_nat_prime_coset_sieve m (by omega) w hw_pos hw_mono hw_gcd S hS_ne p hp_prime hp_dvd_S ?_ h_prev
  rw [hS_card]
  have hm_sub : m - (m - 2) = 2 := by omega
  rw [hm_sub]
  rcases hp_cond with hp5 | ⟨hm5, hp3⟩
  · rcases eq_or_ne p 6 with rfl | hp_ne6
    · exfalso; exact absurd hp_prime (by decide)
    rcases eq_or_ne p 8 with rfl | hp_ne8
    · exfalso; exact absurd hp_prime (by decide)
    have hdiv_le : (2 * p - 1) / (m + 1) ≤ (2 * p - 1) / 5 :=
      Nat.div_le_div_left (by omega) (by omega)
    omega
  · rcases eq_or_ne p 4 with rfl | hp_ne4
    · exfalso; exact absurd hp_prime (by decide)
    rcases eq_or_ne p 6 with rfl | hp_ne6
    · exfalso; exact absurd hp_prime (by decide)
    have hdiv_le : (2 * p - 1) / (m + 1) ≤ (2 * p - 1) / 6 :=
      Nat.div_le_div_left (by omega) (by omega)
    omega

-- Special case 3: 4-subset prime sieve for m = 7 (works for ALL primes p ≥ 7).
private lemma lrc_nat_seven_four_subset_sieve (w : Fin 7 → ℕ)
    (hw_pos : ∀ i : Fin 7, 0 < w i) (hw_mono : StrictMono w)
    (hw_gcd : Finset.univ.gcd w = 1)
    (S : Finset (Fin 7)) (hS_card : S.card = 4)
    (p : ℕ) (hp_prime : Nat.Prime p) (hp7 : 7 ≤ p)
    (hp_dvd_S : ∀ i ∈ S, p ∣ w i)
    (h_prev : ∀ (s : ℕ), 1 ≤ s → s < 7 → ∀ (u : Fin s → ℕ),
      (∀ l : Fin s, 0 < u l) → StrictMono u →
      ∃ t : ℝ, t ≥ 0 ∧
        ∀ l : Fin s, dist ((t * (u l : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((s + 1 : ℕ) : ℝ)) :
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin 7, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((7 + 1 : ℕ) : ℝ) := by
  have hS_ne : S.Nonempty := Finset.card_pos.mp (by omega)
  refine lrc_nat_prime_coset_sieve 7 (by omega) w hw_pos hw_mono hw_gcd S hS_ne p hp_prime hp_dvd_S ?_ h_prev
  rw [hS_card]
  rcases eq_or_ne p 8 with rfl | hp8
  · exfalso; exact absurd hp_prime (by decide)
  rcases eq_or_ne p 9 with rfl | hp9
  · exfalso; exact absurd hp_prime (by decide)
  rcases eq_or_ne p 10 with rfl | hp10
  · exfalso; exact absurd hp_prime (by decide)
  omega


private lemma lrc_nat_six_three_subset_sieve (w : Fin 6 → ℕ)
    (hw_pos : ∀ i : Fin 6, 0 < w i) (hw_mono : StrictMono w)
    (hw_gcd : Finset.univ.gcd w = 1)
    (S : Finset (Fin 6)) (hS_card : S.card = 3)
    (p : ℕ) (hp_prime : Nat.Prime p) (hp_cond : p = 7 ∨ 13 ≤ p)
    (hp_dvd_S : ∀ i ∈ S, p ∣ w i)
    (h_prev : ∀ (s : ℕ), 1 ≤ s → s < 6 → ∀ (u : Fin s → ℕ),
      (∀ l : Fin s, 0 < u l) → StrictMono u →
      ∃ t : ℝ, t ≥ 0 ∧
        ∀ l : Fin s, dist ((t * (u l : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((s + 1 : ℕ) : ℝ)) :
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin 6, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((6 + 1 : ℕ) : ℝ) := by
  have hS_ne : S.Nonempty := Finset.card_pos.mp (by omega)
  refine lrc_nat_prime_coset_sieve 6 (by omega) w hw_pos hw_mono hw_gcd S hS_ne p hp_prime hp_dvd_S ?_ h_prev
  rw [hS_card]
  rcases hp_cond with rfl | hp13
  · omega
  · have hp_odd : p % 2 = 1 := by
      rcases hp_prime.eq_two_or_odd with rfl | hodd <;> omega
    have hp_ne15 : p ≠ 15 := fun h => by subst h; exact absurd hp_prime (by decide)
    have hp7 : 3 * ((2 * p - 1) / 7 + 1) < p := by
      rcases lt_or_ge p 18 with hlt18 | hge18 <;> omega
    omega

private lemma lrc_nat_upto_seven (h1 : H1) (h2 : H2) (h3 : H3) :
    ∀ (m : ℕ), 1 ≤ m → m ≤ 7 → ∀ (w : Fin m → ℕ),
      (∀ i : Fin m, 0 < w i) → StrictMono w →
      ∃ t : ℝ, t ≥ 0 ∧
        ∀ i : Fin m, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((m + 1 : ℕ) : ℝ) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm1 hm7 w hw_pos hw_mono
    rcases eq_or_ne m 1 with rfl | hm_ne1
    · exact lrc_pos_one (fun i => (w i : ℝ)) (fun i => Nat.cast_pos.mpr (hw_pos i))
    rcases eq_or_ne m 2 with rfl | hm_ne2
    · exact lrc_pos_two (fun i => (w i : ℝ))
        (fun i => Nat.cast_pos.mpr (hw_pos i)) (fun i j hij => Nat.cast_lt.mpr (hw_mono hij))
    rcases eq_or_ne m 3 with rfl | hm_ne3
    · exact lrc_pos_three (fun i => (w i : ℝ))
        (fun i => Nat.cast_pos.mpr (hw_pos i)) (fun i j hij => Nat.cast_lt.mpr (hw_mono hij))
    rcases eq_or_ne m 4 with rfl | hm_ne4
    · exact lrc_nat_four w hw_pos hw_mono
    have hm5 : 5 ≤ m := by omega
    have h_prev_all : ∀ (s : ℕ), 1 ≤ s → s < m → ∀ (u : Fin s → ℕ),
        (∀ l : Fin s, 0 < u l) → StrictMono u →
        ∃ t : ℝ, t ≥ 0 ∧
          ∀ l : Fin s, dist ((t * (u l : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((s + 1 : ℕ) : ℝ) :=
      fun s hs1 hslt u hu_pos hu_mono => ih s hslt hs1 (by omega) u hu_pos hu_mono
    have h_prev_one : ∀ (u : Fin (m - 1) → ℕ), (∀ l : Fin (m - 1), 0 < u l) → StrictMono u →
        ∃ t : ℝ, t ≥ 0 ∧
          ∀ l : Fin (m - 1), dist ((t * (u l : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((m - 1 + 1 : ℕ) : ℝ) :=
      fun u hu_pos hu_mono => h_prev_all (m - 1) (by omega) (by omega) u hu_pos hu_mono
    refine lrc_nat_gcd_reduction m hm1 w hw_pos hw_mono ?_
    intro u hu_pos hu_mono hu_gcd
    by_cases h_sub1 : ∀ i₀ : Fin m, (Finset.univ.erase i₀).gcd u = 1
    · by_cases h_all_dvd : ∀ d : ℕ, 1 ≤ d → d ≤ m + 1 → ∃ i : Fin m, d ∣ u i
      · by_cases h_top : u ⟨m - 1, by omega⟩ < m * u ⟨m - 2, by omega⟩
        · by_cases hlac : ∃ i j : Fin m, i.val + 1 = j.val ∧ j.val + 1 < m ∧
              (m - 1) * u j < 2 * m * u i
          · rcases eq_or_ne m 5 with rfl | hm_ne5
            · by_cases h_sub2 : ∀ S : Finset (Fin 5), S.card = 3 →
                  ∀ p : ℕ, Nat.Prime p → 3 ≤ p → ¬ p ∣ S.gcd u
              · exact h1 u hu_pos hu_mono hu_gcd h_sub1 h_sub2 h_all_dvd h_top hlac
              · push Not at h_sub2
                obtain ⟨S, hScard, p, hp, hp3, hdvd⟩ := h_sub2
                exact lrc_nat_two_exception_sieve 5 (by omega) u hu_pos hu_mono hu_gcd S hScard p hp
                  (Or.inr ⟨le_rfl, hp3⟩) (fun i hi => dvd_trans hdvd (Finset.gcd_dvd hi)) h_prev_all
            · rcases eq_or_ne m 6 with rfl | hm_ne6
              · by_cases h_sub2 : ∀ S : Finset (Fin 6), S.card = 4 →
                    ∀ p : ℕ, Nat.Prime p → 3 ≤ p → ¬ p ∣ S.gcd u
                · by_cases h_sub3 : ∀ S : Finset (Fin 6), S.card = 3 →
                      ∀ p : ℕ, Nat.Prime p → (p = 7 ∨ 13 ≤ p) → ¬ p ∣ S.gcd u
                  · exact h2 u hu_pos hu_mono hu_gcd h_sub1 h_sub2 h_sub3 h_all_dvd h_top hlac
                  · push Not at h_sub3
                    obtain ⟨S, hScard, p, hp, hp_cond, hdvd⟩ := h_sub3
                    exact lrc_nat_six_three_subset_sieve u hu_pos hu_mono hu_gcd S hScard p hp hp_cond
                      (fun i hi => dvd_trans hdvd (Finset.gcd_dvd hi)) h_prev_all
                · push Not at h_sub2
                  obtain ⟨S, hScard, p, hp, hp3, hdvd⟩ := h_sub2
                  exact lrc_nat_two_exception_sieve 6 (by omega) u hu_pos hu_mono hu_gcd S hScard p hp
                    (Or.inr ⟨by omega, hp3⟩) (fun i hi => dvd_trans hdvd (Finset.gcd_dvd hi)) h_prev_all
              · have hm_eq7 : m = 7 := by omega
                subst hm_eq7
                by_cases h_sub2 : ∀ S : Finset (Fin 7), S.card = 5 →
                      ∀ p : ℕ, Nat.Prime p → 3 ≤ p → ¬ p ∣ S.gcd u
                · by_cases h_sub3 : ∀ S : Finset (Fin 7), S.card = 4 →
                        ∀ p : ℕ, Nat.Prime p → 7 ≤ p → ¬ p ∣ S.gcd u
                  · exact h3 u hu_pos hu_mono hu_gcd h_sub1 h_sub2 h_sub3 h_all_dvd h_top hlac
                  · push Not at h_sub3
                    obtain ⟨S, hScard, p, hp, hp7, hdvd⟩ := h_sub3
                    exact lrc_nat_seven_four_subset_sieve u hu_pos hu_mono hu_gcd S hScard p hp hp7
                      (fun i hi => dvd_trans hdvd (Finset.gcd_dvd hi)) h_prev_all
                · push Not at h_sub2
                  obtain ⟨S, hScard, p, hp, hp3, hdvd⟩ := h_sub2
                  exact lrc_nat_two_exception_sieve 7 (by omega) u hu_pos hu_mono hu_gcd S hScard p hp
                    (Or.inr ⟨by omega, hp3⟩) (fun i hi => dvd_trans hdvd (Finset.gcd_dvd hi)) h_prev_all
          · exact lrc_lacunary_nat m (by omega) u hu_pos hu_mono hlac
        · exact lrc_nat_last_speed_bound m (by omega) u hu_pos hu_mono (Nat.le_of_not_lt h_top) h_prev_one
      · push Not at h_all_dvd
        obtain ⟨d, hd1, hdm, hndvd⟩ := h_all_dvd
        exact lrc_nat_not_dvd_le m d hm1 hd1 hdm u hndvd
    · push Not at h_sub1
      obtain ⟨i₀, hi₀⟩ := h_sub1
      exact lrc_nat_one_exception_sieve m (by omega) u hu_pos hu_mono hu_gcd i₀ hi₀ h_prev_all

end

end ReductionProofs

theorem main : H1 → H2 → H3 → OMA.R_LonelyRunnerConjecture_lonely_runner_conjecture_R1.H2 := by
  intro h1 h2 h3 k hk3 hk7 w hw_pos hw_mono _ _ _
  exact lrc_nat_upto_seven h1 h2 h3 k (by omega) hk7 w hw_pos hw_mono

end OMA.R_LonelyRunnerConjecture_lonely_runner_conjecture_R1_H2_R2
