import FormalConjectures.ErdosProblems.«270»

/-! The factorial ratios form a Cantor series. Multiplying by a suitable
denominator leaves a positive tail strictly smaller than one. -/

open Finset

def OMA.linearDen (n : ℕ) : ℕ := ∏ i ∈ Finset.Icc (n + 1) (n + n), i

lemma OMA.linearDen_pos (n : ℕ) : 0 < OMA.linearDen n := by
  apply Finset.prod_pos
  intro i hi
  have h := (Finset.mem_Icc.mp hi).1
  omega

lemma OMA.linearDen_factorial (n : ℕ) :
    n.factorial * OMA.linearDen n = (n + n).factorial := by
  rw [← Finset.prod_Ico_id_eq_factorial n, ← Finset.prod_Ico_id_eq_factorial (n + n)]
  unfold OMA.linearDen
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_consecutive _ (by omega) (by omega)]

lemma OMA.linearDen_succ (n : ℕ) :
    OMA.linearDen (n + 1) = OMA.linearDen n * (4 * n + 2) := by
  apply Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos (n + 1))
  calc
    (n + 1).factorial * OMA.linearDen (n + 1) = ((n + 1) + (n + 1)).factorial :=
      OMA.linearDen_factorial (n + 1)
    _ = (n + n + 1 + 1).factorial := by
      congr 1
      omega
    _ = (n + 1).factorial * (OMA.linearDen n * (4 * n + 2)) := by
      rw [Nat.factorial_succ (n + n + 1), Nat.factorial_succ (n + n),
        Nat.factorial_succ n, ← OMA.linearDen_factorial n]
      ring

lemma OMA.linearDen_dvd {m n : ℕ} (hmn : m ≤ n) : OMA.linearDen m ∣ OMA.linearDen n := by
  induction n, hmn using Nat.le_induction with
  | base => exact dvd_rfl
  | succ n _ ih =>
    rw [OMA.linearDen_succ]
    exact ih.trans (dvd_mul_right _ _)

lemma OMA.linearDen_geometric (n j r : ℕ) (hr : r ≤ 4 * n + 2) :
    OMA.linearDen n * r ^ j ≤ OMA.linearDen (n + j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, ← mul_assoc, ← Nat.add_assoc, OMA.linearDen_succ]
    exact Nat.mul_le_mul ih (by omega)

lemma OMA.linearDen_self_dvd (n : ℕ) (hn : 0 < n) : n ∣ OMA.linearDen n := by
  have hm : n + n ∈ Finset.Icc (n + 1) (n + n) :=
    Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩
  have hd := Finset.dvd_prod_of_mem (fun i : ℕ => i) hm
  exact (show n ∣ n + n from ⟨2, by omega⟩).trans hd

noncomputable def OMA.linearTerm (i : ℕ) : ℝ := (OMA.linearDen (i + 1) : ℝ)⁻¹

lemma OMA.linearTerm_bound (n j r : ℕ) (hr0 : 0 < r) (hr : r ≤ 4 * n + 2) :
    (OMA.linearDen n : ℝ) * OMA.linearTerm (n + j) ≤ (1 / (r : ℝ)) ^ (j + 1) := by
  have hcast : (OMA.linearDen n : ℝ) * (r : ℝ) ^ (j + 1) ≤
      (OMA.linearDen (n + j + 1) : ℝ) := by
    exact_mod_cast OMA.linearDen_geometric n (j + 1) r hr
  have hden : (0 : ℝ) < (OMA.linearDen (n + j + 1) : ℝ) := by
    exact_mod_cast OMA.linearDen_pos (n + j + 1)
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr0
  unfold OMA.linearTerm
  rw [one_div, inv_pow, ← div_eq_mul_inv, ← one_div]
  exact (div_le_div_iff₀ hden (by positivity)).mpr (by simpa using hcast)

lemma OMA.linearTerm_summable : Summable OMA.linearTerm := by
  have hgeo := summable_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have hgeo' : Summable (fun j : ℕ => (1 / 2 : ℝ) ^ (j + 1)) :=
    (summable_nat_add_iff 1).mpr hgeo
  refine hgeo'.of_nonneg_of_le (fun j => by unfold OMA.linearTerm; positivity) fun j => ?_
  have hzero : OMA.linearDen 0 = 1 := by simp [OMA.linearDen]
  simpa [hzero] using OMA.linearTerm_bound 0 j 2 (by decide) (by decide)

lemma OMA.linearSeries : Erdos270.series id = ∑' i : ℕ, OMA.linearTerm i := by
  unfold Erdos270.series
  congr 1
  funext i
  simp [OMA.linearTerm, OMA.linearDen, Nat.cast_prod, Nat.add_assoc]

theorem OMA.solution : type_of% @Erdos270.erdos_270.variants.linear := by
  rintro ⟨a, ha⟩
  let n := a.den
  have hn : 0 < n := a.den_pos
  let D := OMA.linearDen n
  have hD : (0 : ℝ) < (D : ℝ) := by exact_mod_cast OMA.linearDen_pos n
  let tail (j : ℕ) := (D : ℝ) * OMA.linearTerm (n + j)
  have hnonneg (j : ℕ) : 0 ≤ tail j := by
    unfold tail OMA.linearTerm
    positivity
  have hgeom := summable_geometric_of_lt_one (r := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
  have hgeom' : Summable (fun j : ℕ => (1 / 4 : ℝ) ^ (j + 1)) :=
    (summable_nat_add_iff 1).mpr hgeom
  have htail_le (j : ℕ) : tail j ≤ (1 / 4 : ℝ) ^ (j + 1) :=
    OMA.linearTerm_bound n j 4 (by decide) (by omega)
  have htail := hgeom'.of_nonneg_of_le hnonneg htail_le
  have htailpos : 0 < ∑' j, tail j := by
    apply htail.tsum_pos hnonneg 0
    have hterm : 0 < OMA.linearTerm (n + 0) := by
      unfold OMA.linearTerm
      exact inv_pos.mpr (by exact_mod_cast OMA.linearDen_pos (n + 0 + 1))
    exact mul_pos hD hterm
  have htaillt : (∑' j, tail j) < 1 := by
    calc
      _ ≤ ∑' j : ℕ, (1 / 4 : ℝ) ^ (j + 1) := htail.tsum_le_tsum htail_le hgeom'
      _ = (1 / 4 : ℝ) * (1 - 1 / 4)⁻¹ := by
        simp_rw [pow_succ, mul_comm ((1 / 4 : ℝ) ^ _), tsum_mul_left]
        rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      _ < 1 := by norm_num
  have hq : ∃ u : ℕ, D = n * u := OMA.linearDen_self_dvd n hn
  obtain ⟨u, hu⟩ := hq
  have hNat : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hscaled : (D : ℝ) * Erdos270.series id = (((u : ℤ) * a.num : ℤ) : ℝ) := by
    rw [← ha, hu, Rat.cast_def]
    change ((n * u : ℕ) : ℝ) * ((a.num : ℝ) / (n : ℝ)) = _
    push_cast
    field_simp [hNat.ne']
  let p (i : ℕ) := D / OMA.linearDen (i + 1)
  have hp (i : ℕ) (hi : i ∈ Finset.range n) :
      (D : ℝ) * OMA.linearTerm i = (p i : ℝ) := by
    have hdiv : OMA.linearDen (i + 1) ∣ D :=
      OMA.linearDen_dvd (Nat.succ_le_of_lt (Finset.mem_range.mp hi))
    have he : p i * OMA.linearDen (i + 1) = D := Nat.div_mul_cancel hdiv
    have he' : (p i : ℝ) * (OMA.linearDen (i + 1) : ℝ) = (D : ℝ) := by exact_mod_cast he
    have hdi : (OMA.linearDen (i + 1) : ℝ) ≠ 0 := by
      exact_mod_cast (OMA.linearDen_pos (i + 1)).ne'
    rw [OMA.linearTerm, ← he', mul_assoc, mul_inv_cancel₀ hdi, mul_one]
  have hsum : (∑ i ∈ Finset.range n, (D : ℝ) * OMA.linearTerm i) =
      ((∑ i ∈ Finset.range n, p i : ℕ) : ℝ) := by
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl hp
  have hsplit : (∑ i ∈ Finset.range n, (D : ℝ) * OMA.linearTerm i) + (∑' j, tail j) =
      (D : ℝ) * Erdos270.series id := by
    rw [OMA.linearSeries, ← tsum_mul_left]
    simpa [tail, Nat.add_comm] using (OMA.linearTerm_summable.mul_left (D : ℝ)).sum_add_tsum_nat_add n
  have hint : (∑' j, tail j) =
      (((u : ℤ) * a.num - ((∑ i ∈ Finset.range n, p i : ℕ) : ℤ) : ℤ) : ℝ) := by
    rw [hsum, hscaled, Int.cast_mul, Int.cast_natCast] at hsplit
    calc
      _ = (u : ℝ) * (a.num : ℝ) - ((∑ i ∈ Finset.range n, p i : ℕ) : ℝ) := by
        linarith only [hsplit]
      _ = _ := by rw [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_natCast]
  rw [hint] at htailpos htaillt
  have hlo : 0 < (u : ℤ) * a.num - ((∑ i ∈ Finset.range n, p i : ℕ) : ℤ) := by
    exact_mod_cast htailpos
  have hhi : (u : ℤ) * a.num - ((∑ i ∈ Finset.range n, p i : ℕ) : ℤ) < 1 := by
    exact_mod_cast htaillt
  omega