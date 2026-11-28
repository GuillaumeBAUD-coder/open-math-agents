import OMAStatements.S_mo_495907
import Mathlib

namespace RadicalSpectrum

open OMA.S_mo_495907
open Finset Polynomial Matrix ArithmeticFunction UniqueFactorizationMonoid
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

private theorem rad_eq (i : ℕ) : rad i = radical i :=
  (Nat.radical_eq_prod_primeFactors (n := i)).symm

private theorem rad_pos (i : ℕ) : 0 < rad i := by
  rw [rad_eq]
  exact Nat.radical_pos i

private theorem rad_le (i : ℕ) (hi : i ≠ 0) : rad i ≤ i := by
  rw [rad_eq]
  exact Nat.radical_le_self_iff.mpr hi

private theorem rad_dvd_rad (i j : ℕ) (hj : j ≠ 0) : rad i ∣ rad j ↔ rad i ∣ j := by
  rw [rad_eq i, rad_eq j]
  exact dvd_radical_iff isRadical_radical hj

private def firstAF : ArithmeticFunction ℤ := ζ * ((μ).pmul (ArithmeticFunction.id : ArithmeticFunction ℤ))

private theorem first_eq (n : ℕ) : first n = firstAF n := by
  rw [firstAF, coe_zeta_mul_apply]
  simp only [first, pmul_apply, natCoe_apply, ArithmeticFunction.id_apply]

private theorem first_mult : firstAF.IsMultiplicative :=
  isMultiplicative_zeta.natCast.mul (isMultiplicative_moebius.pmul isMultiplicative_id.natCast)

private theorem first_one : first 1 = 1 := by
  rw [first_eq]
  exact first_mult.map_one

private theorem first_prime {p : ℕ} (hp : p.Prime) : first p = 1 - (p : ℤ) := by
  unfold first
  rw [← pow_one p, Nat.sum_divisors_prime_pow hp]
  norm_num [Finset.sum_range_succ, moebius_apply_prime hp, sub_eq_add_neg]

private def summand (j : ℕ) : ArithmeticFunction ℤ :=
  ⟨fun d => μ d * first (d.gcd j), by simp⟩

private theorem summand_mult (j : ℕ) : (summand j).IsMultiplicative := by
  refine ⟨by simp [summand, first_one], ?_⟩
  intro a b hab
  change μ (a * b) * first ((a * b).gcd j) =
    (μ a * first (a.gcd j)) * (μ b * first (b.gcd j))
  rw [isMultiplicative_moebius.map_mul_of_coprime hab,
    Nat.gcd_comm (a * b) j, hab.gcd_mul, Nat.gcd_comm j a, Nat.gcd_comm j b]
  simp only [first_eq]
  rw [first_mult.map_mul_of_coprime
    (hab.of_dvd_left (Nat.gcd_dvd_left _ _) |>.of_dvd_right (Nat.gcd_dvd_left _ _))]
  ring

private theorem entry_mult (j a b : ℕ) (h : a.Coprime b) :
    entry (a * b) j = entry a j * entry b j := by
  have eq (n : ℕ) : entry n j = ((summand j) * (ζ : ArithmeticFunction ℤ)) n :=
    (coe_mul_zeta_apply (f := summand j)).symm
  simp only [eq]
  exact ((summand_mult j).mul isMultiplicative_zeta.natCast).map_mul_of_coprime h

private theorem entry_prime_power {p k j : ℕ} (hp : p.Prime) (hk : 0 < k) :
    entry (p ^ k) j = if p ∣ j then (p : ℤ) else 0 := by
  unfold entry
  rw [Nat.sum_divisors_prime_pow hp, Finset.sum_range_succ']
  simp only [pow_zero, moebius_apply_one, one_mul, Nat.gcd_one_left, first_one]
  rw [add_comm]
  have ht : (∑ i ∈ range k, μ (p ^ (i + 1)) * first ((p ^ (i + 1)).gcd j)) =
      μ p * first (p.gcd j) := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro i _ hi
      simp [moebius_apply_prime_pow hp (by omega : i + 1 ≠ 0), hi]
    · intro h
      exact (h (Finset.mem_range.mpr hk)).elim
  rw [ht, moebius_apply_prime hp]
  by_cases hd : p ∣ j
  · rw [if_pos hd, Nat.gcd_eq_left hd, first_prime hp]
    ring
  · rw [if_neg hd, (hp.coprime_iff_not_dvd.mpr hd).gcd_eq_one, first_one]
    ring

private theorem entry_formula (i j : ℕ) (hi : i ≠ 0) :
    entry i j = if rad i ∣ j then (rad i : ℤ) else 0 := by
  induction i using Nat.recOnPosPrimePosCoprime with
  | zero => contradiction
  | one => simp [entry, first_one, rad_eq]
  | prime_pow p k hp hk =>
    have he : rad (p ^ k) = p := by
      rw [rad_eq, radical_pow_of_prime hp.prime (ne_of_gt hk)]
      exact normalize_eq _
    rw [he, entry_prime_power hp hk]
  | coprime a b ha hb hab ia ib =>
    have hrad : rad (a * b) = rad a * rad b := by
      simp only [rad_eq]
      exact radical_mul (Nat.coprime_iff_isRelPrime.mp hab)
    have hc : (rad a).Coprime (rad b) :=
      hab.of_dvd (Nat.prod_primeFactors_dvd _) (Nat.prod_primeFactors_dvd _)
    rw [entry_mult j a b hab, ia (by omega), ib (by omega), hrad]
    by_cases h₁ : rad a ∣ j <;> by_cases h₂ : rad b ∣ j
    · simp [h₁, h₂, hc.mul_dvd_of_dvd_of_dvd h₁ h₂]
    · have h' : ¬ rad a * rad b ∣ j := fun h => h₂ ((dvd_mul_left _ _).trans h)
      simp [h₁, h₂, h']
    · have h' : ¬ rad a * rad b ∣ j := fun h => h₁ ((dvd_mul_right _ _).trans h)
      simp [h₁, h₂, h']
    · have h' : ¬ rad a * rad b ∣ j := fun h => h₂ ((dvd_mul_left _ _).trans h)
      simp [h₁, h₂, h']

private def representative {n : ℕ} (i : Fin n) : Fin n :=
  ⟨rad (i.val + 1) - 1, by
    have h := rad_le (i.val + 1) (by omega)
    omega⟩

private theorem representative_val {n : ℕ} (i : Fin n) :
    (representative i).val + 1 = rad (i.val + 1) := by
  change rad (i.val + 1) - 1 + 1 = _
  exact Nat.sub_add_cancel (rad_pos _)

private noncomputable def mark (n : ℕ) : Mat n :=
  fun i j => if representative i = j then 1 else 0

private noncomputable def divMat (n : ℕ) : Mat n :=
  fun i j => if i.val + 1 ∣ rad (j.val + 1) then 1 else 0

private theorem count_eq {n : ℕ} (i : Fin n) :
    count n (i.val + 1) = ((univ : Finset (Fin n)).filter (fun j => representative j = i)).card := by
  unfold count
  congr 1
  ext v
  simp only [mem_filter, mem_univ, true_and]
  rw [← representative_val v]
  exact ⟨fun h => Fin.ext (by omega), fun h => by rw [h]⟩

private theorem sign_eq (i j : ℕ) (hi : i ≠ 0) :
    (entry i j).sign = if rad i ∣ j then 1 else 0 := by
  rw [entry_formula i j hi]
  split
  · exact Int.sign_eq_one_of_pos (by exact_mod_cast rad_pos i)
  · decide

private theorem mark_mul_apply {n : ℕ} (M : Mat n) (i j : Fin n) :
    (mark n * M) i j = M (representative i) j := by
  classical
  rw [Matrix.mul_apply, Finset.sum_eq_single (representative i)]
  · simp [mark]
  · intro b _ hb
    simp [mark, Ne.symm hb]
  · simp

private theorem signs_eq (n : ℕ) : signs n = mark n * divMat n := by
  classical
  ext i j
  change ((entry (i.val + 1) (j.val + 1)).sign : ℝ) = _
  simp only [sign_eq (i.val + 1) (j.val + 1) (by omega),
    ← rad_dvd_rad (i.val + 1) (j.val + 1) (by omega), mark_mul_apply]
  simp [divMat, representative_val]

private theorem raw_eq (n : ℕ) :
    raw n = mark n * (diagonal (fun i : Fin n => ((i.val + 1 : ℕ) : ℝ)) * divMat n) := by
  classical
  ext i j
  change ((entry (i.val + 1) (j.val + 1)) : ℝ) = _
  simp only [entry_formula (i.val + 1) (j.val + 1) (by omega),
    ← rad_dvd_rad (i.val + 1) (j.val + 1) (by omega), mark_mul_apply]
  have h : ((representative i).val : ℝ) + 1 = (rad (i.val + 1) : ℝ) := by
    exact_mod_cast representative_val i
  simp [divMat, Matrix.diagonal_mul, mul_ite, representative_val, h]

private theorem div_mark_apply {n : ℕ} (i j : Fin n) :
    (divMat n * mark n) i j =
      if i.val + 1 ∣ j.val + 1 then (count n (j.val + 1) : ℝ) else 0 := by
  classical
  rw [Matrix.mul_apply]
  simp only [mark, divMat, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter, count_eq]
  have h : ∀ k ∈ (univ : Finset (Fin n)).filter (fun k => representative k = j),
      (if i.val + 1 ∣ rad (k.val + 1) then (1 : ℝ) else 0) =
      (if i.val + 1 ∣ j.val + 1 then (1 : ℝ) else 0) := by
    intro k hk
    rw [← representative_val k, (Finset.mem_filter.mp hk).2]
  rw [Finset.sum_congr rfl h]
  by_cases hd : i.val + 1 ∣ j.val + 1 <;> simp [hd]

private theorem div_mark_upper (n : ℕ) : (divMat n * mark n).IsUpperTriangular := by
  intro i j h
  rw [div_mark_apply, if_neg]
  intro hd
  have hf := Nat.le_of_dvd (show 0 < j.val + 1 by omega) hd
  exact (not_le_of_gt h) (Fin.mk_le_mk.mpr (by omega))

private theorem signs_charpoly (n : ℕ) :
    (signs n).charpoly = ∏ i : Fin n, (X - C (count n (i.val + 1) : ℝ)) := by
  rw [signs_eq, Matrix.charpoly_mul_comm, Matrix.charpoly_of_isUpperTriangular _ (div_mark_upper n)]
  simp [div_mark_apply]

private theorem raw_charpoly (n : ℕ) :
    (raw n).charpoly = ∏ i : Fin n, (X - C ((i.val + 1 : ℕ) * count n (i.val + 1) : ℝ)) := by
  let D : Mat n := diagonal (fun i : Fin n => ((i.val + 1 : ℕ) : ℝ))
  have hd : (D * (divMat n * mark n)).IsUpperTriangular := by
    intro i j hij
    simp [D, Matrix.diagonal_mul, div_mark_upper n hij]
  rw [raw_eq, Matrix.charpoly_mul_comm, mul_assoc, Matrix.charpoly_of_isUpperTriangular _ hd]
  simp [D, Matrix.diagonal_mul, div_mark_apply]

private theorem symm_eq (n : ℕ) : symmSigns n = mark n * (mark n)ᵀ := by
  classical
  ext i j
  change ((entry (i.val + 1) (j.val + 1) * entry (j.val + 1) (i.val + 1)).sign : ℝ) = _
  simp only [Int.sign_mul, sign_eq (i.val + 1) (j.val + 1) (by omega),
    sign_eq (j.val + 1) (i.val + 1) (by omega),
    ← rad_dvd_rad (i.val + 1) (j.val + 1) (by omega),
    ← rad_dvd_rad (j.val + 1) (i.val + 1) (by omega), mark_mul_apply, transpose_apply, mark]
  have hf : rad (i.val + 1) = rad (j.val + 1) ↔ representative j = representative i := by
    rw [← representative_val i, ← representative_val j]
    exact ⟨fun h => Fin.ext (by omega), fun h => by rw [h]⟩
  by_cases ha : rad (i.val + 1) ∣ rad (j.val + 1) <;>
    by_cases hb : rad (j.val + 1) ∣ rad (i.val + 1)
  · simp [ha, hb, hf.mp (Nat.dvd_antisymm ha hb)]
  · have h : representative j ≠ representative i := fun e => hb (by simp [hf.mpr e])
    simp [ha, hb, h]
  · have h : representative j ≠ representative i := fun e => ha (by simp [hf.mpr e])
    simp [ha, hb, h]
  · have h : representative j ≠ representative i := fun e => ha (by simp [hf.mpr e])
    simp [ha, hb, h]

private theorem mark_gram (n : ℕ) :
    (mark n)ᵀ * mark n = diagonal (fun i : Fin n => (count n (i.val + 1) : ℝ)) := by
  classical
  ext i j
  rw [Matrix.mul_apply]
  simp only [mark, transpose_apply, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  by_cases hij : i = j
  · subst j
    rw [Matrix.diagonal_apply_eq, count_eq]
    rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ)) (by intro k hk; simp [(Finset.mem_filter.mp hk).2])]
    simp
  · rw [Matrix.diagonal_apply_ne _ hij]
    apply Finset.sum_eq_zero
    intro k hk
    have hi := (Finset.mem_filter.mp hk).2
    simp [hi, hij]

private theorem symm_charpoly (n : ℕ) : (symmSigns n).charpoly = (signs n).charpoly := by
  rw [symm_eq, Matrix.charpoly_mul_comm, mark_gram, Matrix.charpoly_diagonal, signs_charpoly]

private theorem root_iff {n : ℕ} (y : ℝ) :
    y ∈ eigs (signs n) ↔ ∃ i : Fin n, (count n (i.val + 1) : ℝ) = y := by
  change (signs n).charpoly.IsRoot y ↔ _
  rw [signs_charpoly]
  simp only [Polynomial.IsRoot, eval_prod, eval_sub, eval_X, eval_C, Finset.prod_eq_zero_iff,
    mem_univ, true_and, sub_eq_zero]
  exact exists_congr (fun _ => eq_comm)

private theorem greatest_48 : IsGreatest (eigs (signs 48)) 6 := by
  have h6 : count 48 6 = 6 := by decide +kernel
  have hbound : ∀ i : Fin 48, count 48 (i.val + 1) ≤ 6 := by decide +kernel
  refine ⟨(root_iff 6).mpr ⟨⟨5, by decide⟩, by exact_mod_cast h6⟩, ?_⟩
  intro y hy
  obtain ⟨i, rfl⟩ := (root_iff y).mp hy
  exact_mod_cast hbound i

theorem result : type_of% @main := by
  refine ⟨fun i j hi _ => entry_formula i j hi, signs_charpoly, symm_charpoly, raw_charpoly,
    greatest_48, ?_⟩
  intro h
  have h₄₈ := h 48 (by decide)
  have hl : Nat.log 2 48 = 5 := by decide
  have hle := h₄₈.2 greatest_48.1
  norm_num [hl] at hle

end RadicalSpectrum

theorem OMA.solution : type_of% @OMA.S_mo_495907.main :=
  RadicalSpectrum.result