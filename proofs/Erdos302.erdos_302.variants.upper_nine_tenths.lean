import FormalConjectures.ErdosProblems.«302»

/-! A disjoint family of scaled unit-fraction triples gives an upper density bound. -/

open Filter Finset
open scoped BigOperators

namespace ReciprocalTriplePacking

/-- A finite packing on 2, 3, 5-smooth multipliers, in rows of three. -/
private def multipliers : List ℕ :=
  [2, 3, 6, 4, 5, 20, 8, 12, 24, 10, 15, 30, 18, 27, 54, 36, 60, 90,
   32, 48, 96, 45, 72, 120, 50, 75, 150, 80, 144, 180, 81, 108, 324,
   135, 216, 360, 128, 192, 384, 162, 270, 405, 160, 240, 480, 100, 125, 500,
   200, 300, 600, 320, 576, 720, 250, 375, 750, 288, 450, 800, 432, 675, 1200,
   486, 810, 1215, 540, 900, 1350]

private def coeffIndex (i : Fin 23) (j : Fin 3) : Fin multipliers.length :=
  ⟨3 * i.val + j.val, by
    change 3 * i.val + j.val < 69
    have := i.isLt
    have := j.isLt
    omega⟩

private def coeff (i : Fin 23) (j : Fin 3) : ℕ :=
  multipliers.get (coeffIndex i j)

private lemma coeff_injective : Function.Injective (fun p : Fin 23 × Fin 3 => coeff p.1 p.2) := by
  have h : multipliers.Nodup := by decide
  intro i j hij
  have hindex := List.nodup_iff_injective_get.mp h hij
  have hval := congrArg Fin.val hindex
  change 3 * i.1.val + i.2.val = 3 * j.1.val + j.2.val at hval
  have := i.2.isLt
  have := j.2.isLt
  exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

private lemma coeff_pos : ∀ (i : Fin 23) (j : Fin 3), 0 < coeff i j := by decide

private lemma coeff_le_last : ∀ (i : Fin 23) (j : Fin 3), coeff i j ≤ coeff i 2 := by decide

private lemma coeff_dvd : ∀ (i : Fin 23) (j : Fin 3), coeff i j ∣ 3888000 := by decide

private lemma coeff_cross :
    ∀ i : Fin 23, coeff i 1 * coeff i 2 = coeff i 0 * (coeff i 1 + coeff i 2) := by decide

private lemma coeff_unit_fraction (i : Fin 23) :
    (1 : ℚ) / coeff i 0 = 1 / coeff i 1 + 1 / coeff i 2 := by
  have h : (coeff i 1 : ℚ) * coeff i 2 = coeff i 0 * ((coeff i 1 : ℚ) + coeff i 2) := by
    exact_mod_cast coeff_cross i
  have hne (j : Fin 3) : (coeff i j : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (coeff_pos i j))
  field_simp [hne]
  nlinarith only [h]

/-- The eight positive residues coprime to 30. -/
private def residue : Fin 8 → ℕ := ![1, 7, 11, 13, 17, 19, 23, 29]

private lemma residue_pos : ∀ r, 0 < residue r := by decide

private lemma residue_lt : ∀ r, residue r < 30 := by decide

private lemma residue_coprime : ∀ r, (residue r).Coprime 30 := by decide

private lemma residue_injective : Function.Injective residue := by decide

private def scale (r : Fin 8) (k : ℕ) : ℕ := 30 * k + residue r

private lemma scale_pos (r : Fin 8) (k : ℕ) : 0 < scale r k := by
  have := residue_pos r
  unfold scale
  omega

private lemma scale_coprime (r : Fin 8) (k : ℕ) : (scale r k).Coprime 3888000 := by
  have hc : (scale r k).Coprime 30 := by
    simpa [scale, Nat.Coprime] using residue_coprime r
  have h2 : (scale r k).Coprime 2 := hc.coprime_dvd_right (by decide)
  have h3 : (scale r k).Coprime 3 := hc.coprime_dvd_right (by decide)
  have h5 : (scale r k).Coprime 5 := hc.coprime_dvd_right (by decide)
  change (scale r k).Coprime (2 ^ 7 * 3 ^ 5 * 5 ^ 3)
  exact ((h2.pow_right 7).mul_right (h3.pow_right 5)).mul_right (h5.pow_right 3)

private def block : ℕ := 116640000

private def quota (i : Fin 23) : ℕ := block / (30 * coeff i 2)

private lemma quota_mul : ∀ i, quota i * (30 * coeff i 2) = block := by decide

private lemma quota_sum : (∑ i : Fin 23, 8 * quota i) = 11674120 := by decide

/-- We count the triples using only full blocks of length 116640000 below the cutoff. -/
private abbrev Packing (N : ℕ) :=
  Σ i : Fin 23, Fin 8 × Fin ((N / block) * quota i)

private def point {N : ℕ} (p : Packing N) (j : Fin 3) : ℕ :=
  coeff p.1 j * scale p.2.1 p.2.2.val

private lemma point_pos {N : ℕ} (p : Packing N) (j : Fin 3) : 0 < point p j :=
  Nat.mul_pos (coeff_pos p.1 j) (scale_pos p.2.1 p.2.2.val)

private lemma point_le {N : ℕ} (p : Packing N) (j : Fin 3) : point p j ≤ N := by
  have hscale : scale p.2.1 p.2.2.val ≤ 30 * ((N / block) * quota p.1) := by
    have := residue_lt p.2.1
    have := p.2.2.isLt
    unfold scale
    omega
  calc
    point p j ≤ coeff p.1 2 * (30 * ((N / block) * quota p.1)) :=
      Nat.mul_le_mul (coeff_le_last p.1 j) hscale
    _ = (N / block) * (quota p.1 * (30 * coeff p.1 2)) := by ring
    _ = (N / block) * block := by rw [quota_mul]
    _ ≤ N := Nat.div_mul_le_self _ _

private lemma point_gcd {N : ℕ} (p : Packing N) (j : Fin 3) :
    (point p j).gcd 3888000 = coeff p.1 j := by
  unfold point
  rw [Nat.mul_comm]
  exact Nat.gcd_mul_of_coprime_of_dvd (scale_coprime p.2.1 p.2.2.val) (coeff_dvd p.1 j)

private lemma point_injective (N : ℕ) :
    Function.Injective (fun p : Packing N × Fin 3 => point p.1 p.2) := by
  rintro ⟨⟨i, r, k⟩, j⟩ ⟨⟨i', r', k'⟩, j'⟩ h
  have hg := congrArg (fun n : ℕ => n.gcd 3888000) h
  simp only [point_gcd] at hg
  have hij : (i, j) = (i', j') := coeff_injective hg
  have hi : i = i' := congrArg Prod.fst hij
  have hj : j = j' := congrArg Prod.snd hij
  subst i' j'
  have hs : scale r k.val = scale r' k'.val := Nat.eq_of_mul_eq_mul_left (coeff_pos i j) h
  have hkr : k.val = k'.val ∧ residue r = residue r' := by
    have := residue_lt r
    have := residue_lt r'
    unfold scale at hs
    omega
  have hk : k = k' := Fin.ext hkr.1
  have hr : r = r' := residue_injective hkr.2
  subst k' r'
  rfl

private lemma point_unit_fraction {N : ℕ} (p : Packing N) :
    (1 : ℚ) / point p 0 = 1 / point p 1 + 1 / point p 2 := by
  simp only [point, Nat.cast_mul, div_mul_eq_div_div]
  rw [← add_div, coeff_unit_fraction]

private lemma packing_card (N : ℕ) :
    Fintype.card (Packing N) = 11674120 * (N / block) := by
  simp only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
  rw [← quota_sum, Finset.sum_mul]
  congr 1
  ext i
  ring

private lemma omissions (N : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 N)
    (hfree : Erdos302.NoUnitFractionTriple A) :
    A.card + 11674120 * (N / block) ≤ N := by
  classical
  have hneq (p : Packing N) {j k : Fin 3} (hjk : j ≠ k) : point p j ≠ point p k := by
    intro heq
    have hp : (p, j) = (p, k) := point_injective N heq
    exact hjk (congrArg Prod.snd hp)
  have hm (p : Packing N) : ∃ j, point p j ∉ A := by
    by_contra! h
    exact hfree (point p 0) (h 0) (point p 1) (h 1) (point p 2) (h 2)
      (hneq p (by decide)) (hneq p (by decide)) (hneq p (by decide)) (point_unit_fraction p)
  choose missing hmissing using hm
  let drop : Packing N → ↥(Finset.Icc 1 N \ A) := fun p =>
    ⟨point p (missing p), Finset.mem_sdiff.mpr
      ⟨Finset.mem_Icc.mpr ⟨point_pos p _, point_le p _⟩, hmissing p⟩⟩
  have hdrop : Function.Injective drop := by
    intro p q h
    have heq : point p (missing p) = point q (missing q) := congrArg Subtype.val h
    have hp : (p, missing p) = (q, missing q) := point_injective N heq
    exact congrArg Prod.fst hp
  have hle := Fintype.card_le_of_injective drop hdrop
  rw [packing_card, Fintype.card_coe] at hle
  have htotal := Finset.card_sdiff_add_card_eq_card hA
  rw [Nat.card_Icc] at htotal
  omega

end ReciprocalTriplePacking

open ReciprocalTriplePacking in
theorem OMA.solution : type_of% @Erdos302.erdos_302.variants.upper_nine_tenths := by
  intro f hf ε hε
  obtain ⟨K, hK⟩ := exists_nat_ge ((11674120 : ℝ) / ε)
  filter_upwards [Filter.eventually_ge_atTop K] with N hKN
  obtain ⟨A, hA, hfree, hcard⟩ := (hf N).1
  have hpack := omissions N A hA hfree
  rw [hcard] at hpack
  have hpackR : (f N : ℝ) + 11674120 * ((N / block : ℕ) : ℝ) ≤ N := by
    exact_mod_cast hpack
  have hdiv : N < 116640000 * (N / block + 1) := by
    change N < block * (N / block + 1)
    exact Nat.lt_mul_div_succ _ (by decide)
  have hdivR : (N : ℝ) < 116640000 * (((N / block : ℕ) : ℝ) + 1) := by
    exact_mod_cast hdiv
  have hq : (N : ℝ) / 10 ≤ 11674120 * (((N / block : ℕ) : ℝ) + 1) := calc
    (N : ℝ) / 10 ≤ 11664000 * (((N / block : ℕ) : ℝ) + 1) := by linarith
    _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  have herr0 : (11674120 : ℝ) / ε ≤ N :=
    hK.trans (by exact_mod_cast hKN)
  have herr : (11674120 : ℝ) ≤ ε * N := by
    simpa [mul_comm] using (div_le_iff₀ hε).mp herr0
  rw [add_mul]
  linarith