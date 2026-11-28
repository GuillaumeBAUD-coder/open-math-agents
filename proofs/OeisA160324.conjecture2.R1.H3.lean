import OMAReductions.R_OeisA160324_conjecture2_R1

/-!
# Proof of `OeisA160324.conjecture2.R1.H3`

Proves that for every `m ≥ 66` and every `n : ℕ`, there exists `x : Fin m → ℕ` such that
`n = ∑ i : Fin m, OeisA160324.polygonalNumber (m + i + 1) (x i)`.

Key identity: for every `k ≥ 2` and `u : ℕ`,
`polygonalNumber k (u + 1) + polygonalNumber (k + 4) u = k * u ^ 2 + 1`.
Grouping the first 16 indices `0..15` into four quads `(j, j + 4, 11 - j, 15 - j)` (`j = 0, 1, 2, 3`)
produces `(2 * m + 13) * (u₀ ^ 2 + u₁ ^ 2 + u₂ ^ 2 + u₃ ^ 2) + 8`.

Using the remaining `m - 16 ≥ 50` indices (`16..m - 1`, where `x ∈ {0, 1, 2}` yields `0`, `1`,
and `m + i + 1`), every residue modulo `L = 2 * m + 13` is represented by a sum `R ≤ 4 * m + 25`.
Thus every `n ≥ 4 * m + 33` reduces via Lagrange's four-square theorem (`Nat.sum_four_squares`),
while every `n < 4 * m + 33` is represented directly using at most two `2`s and some `1`s across
all `m` indices.
-/

namespace OeisA160324R1H3Proof

open OeisA160324 Finset

private lemma poly_zero (k : ℕ) : polygonalNumber k 0 = 0 := by
  simp [polygonalNumber]

private lemma poly_one (k : ℕ) : polygonalNumber k 1 = 1 := by
  simp [polygonalNumber]

private lemma poly_two {k : ℕ} (hk : 2 ≤ k) : polygonalNumber k 2 = k := by
  unfold polygonalNumber
  omega

private lemma poly_pair_sq {k : ℕ} (hk : 2 ≤ k) (u : ℕ) :
    polygonalNumber k (u + 1) + polygonalNumber (k + 4) u = k * u ^ 2 + 1 := by
  cases u with
  | zero =>
    simp [polygonalNumber]
  | succ v =>
    unfold polygonalNumber
    have h1 : 2 ∣ (v + 2) * (v + 1) := by
      rcases Nat.even_or_odd v with ⟨t, rfl⟩ | ⟨t, rfl⟩
      · exact ⟨(t + 1) * (t + t + 1), by ring⟩
      · exact ⟨(t + t + 3) * (t + 1), by ring⟩
    have h2 : 2 ∣ (v + 1) * v := by
      rcases Nat.even_or_odd v with ⟨t, rfl⟩ | ⟨t, rfl⟩
      · exact ⟨(t + t + 1) * t, by ring⟩
      · exact ⟨(t + 1) * (t + t + 1), by ring⟩
    obtain ⟨a, ha⟩ := h1
    obtain ⟨b, hb⟩ := h2
    have hdiv1 : (v + 1 + 1) * (v + 1 + 1 - 1) / 2 = a := by
      have : (v + 1 + 1) * (v + 1 + 1 - 1) = 2 * a := by
        simpa [Nat.add_assoc] using ha
      rw [this, Nat.mul_div_cancel_left _ (by decide)]
    have hdiv2 : (v + 1) * (v + 1 - 1) / 2 = b := by
      have : (v + 1) * (v + 1 - 1) = 2 * b := by
        simpa using hb
      rw [this, Nat.mul_div_cancel_left _ (by decide)]
    rw [hdiv1, hdiv2]
    have hsum : a + b = (v + 1) ^ 2 := by nlinarith
    have hdiff : a = b + (v + 1) := by nlinarith
    have hk2 : k - 2 + 2 = k := by omega
    have hk4 : k + 4 - 2 = k + 2 := by omega
    rw [hk4]
    zify [hk]
    nlinarith

-- Helper: sum of `1`s on a range `[lo, lo + t)` inside `Fin m`, `0` elsewhere
private lemma sum_ones_on {m lo t : ℕ} (hbound : lo + t ≤ m) :
    ∑ i : Fin m, polygonalNumber (m + i.val + 1) (if lo ≤ i.val ∧ i.val < lo + t then 1 else 0) = t := by
  have hterm : ∀ i : Fin m,
      polygonalNumber (m + i.val + 1) (if lo ≤ i.val ∧ i.val < lo + t then 1 else 0) =
        if lo ≤ i.val ∧ i.val < lo + t then 1 else 0 := fun i => by
    split_ifs <;> simp [polygonalNumber]
  simp_rw [hterm, Finset.sum_boole, Nat.cast_id]
  have hbij : (Finset.univ.filter fun i : Fin m => lo ≤ i.val ∧ i.val < lo + t).card =
      (Finset.Ico lo (lo + t)).card := by
    refine Finset.card_nbij (fun i : Fin m => i.val) ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact Finset.mem_coe.mpr (Finset.mem_Ico.mpr hi)
    · intro i _ j _ h
      exact Fin.ext h
    · intro k hk
      rw [Finset.mem_coe, Finset.mem_Ico] at hk
      refine ⟨⟨k, by omega⟩, ?_, rfl⟩
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hk
  rw [hbij, Nat.card_Ico]
  omega

-- Helper: sum on `[lo, m)` using zero, one, or two fixed indices set to `2`, and `t` other indices set to `1`.
private lemma repr_ones_in_tail {m lo t : ℕ} (hbound : lo + t ≤ m) :
    ∃ x : Fin m → ℕ, (∀ i : Fin m, i.val < lo → x i = 0) ∧
      ∑ i : Fin m, polygonalNumber (m + i.val + 1) (x i) = t := by
  refine ⟨fun i => if lo ≤ i.val ∧ i.val < lo + t then 1 else 0, ?_, sum_ones_on hbound⟩
  intro i hi
  dsimp only
  rw [if_neg (by omega)]

private lemma repr_one_two_and_ones {m lo idx t : ℕ} (hlo : lo ≤ idx) (hidx : idx < m)
    (ht : t ≤ m - lo - 1) :
    ∃ x : Fin m → ℕ, (∀ i : Fin m, i.val < lo → x i = 0) ∧
      ∑ i : Fin m, polygonalNumber (m + i.val + 1) (x i) = (m + idx + 1) + t := by
  let S : Finset (Fin m) := (Finset.univ.filter fun i : Fin m => lo ≤ i.val).erase ⟨idx, hidx⟩
  have hScard : S.card = m - lo - 1 := by
    have hmem : (⟨idx, hidx⟩ : Fin m) ∈ Finset.univ.filter (fun i : Fin m => lo ≤ i.val) := by
      simp [hlo]
    rw [Finset.card_erase_of_mem hmem]
    have hfilt : (Finset.univ.filter fun i : Fin m => lo ≤ i.val).card = m - lo := by
      have hbij : (Finset.univ.filter fun i : Fin m => lo ≤ i.val).card = (Finset.Ico lo m).card := by
        refine Finset.card_nbij (fun i : Fin m => i.val) ?_ ?_ ?_
        · intro i hi
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi
          exact Finset.mem_coe.mpr (Finset.mem_Ico.mpr ⟨hi, i.isLt⟩)
        · intro i _ j _ h; exact Fin.ext h
        · intro k hk
          rw [Finset.mem_coe, Finset.mem_Ico] at hk
          exact ⟨⟨k, hk.2⟩, by simp [hk.1], rfl⟩
      rw [hbij, Nat.card_Ico]
    omega
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq (show t ≤ S.card by omega)
  let x : Fin m → ℕ := fun i => if i = ⟨idx, hidx⟩ then 2 else if i ∈ T then 1 else 0
  have hzero : ∀ i : Fin m, i.val < lo → x i = 0 := by
    intro i hi
    have hne : i ≠ ⟨idx, hidx⟩ := fun h => by have := congrArg Fin.val h; dsimp at this; omega
    have hnotT : i ∉ T := fun hT => by
      have hS := Finset.mem_erase.mp (hTS hT)
      have := (Finset.mem_filter.mp hS.2).2
      omega
    simp [x, hne, hnotT]
  refine ⟨x, hzero, ?_⟩
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨idx, hidx⟩ : Fin m))]
  have hhead : polygonalNumber (m + idx + 1) (x ⟨idx, hidx⟩) = m + idx + 1 := by
    simp only [x, ↓reduceIte]
    exact poly_two (by omega)
  have htail : ∑ i ∈ Finset.univ.erase (⟨idx, hidx⟩ : Fin m),
      polygonalNumber (m + i.val + 1) (x i) = t := by
    have hterm : ∀ i ∈ Finset.univ.erase (⟨idx, hidx⟩ : Fin m),
        polygonalNumber (m + i.val + 1) (x i) = if i ∈ T then 1 else 0 := by
      intro i hi
      have hne : i ≠ ⟨idx, hidx⟩ := (Finset.mem_erase.mp hi).1
      simp only [x, hne, ↓reduceIte]
      split_ifs <;> simp [polygonalNumber]
    rw [Finset.sum_congr rfl hterm, Finset.sum_boole, Nat.cast_id]
    have hfilt : (Finset.univ.erase (⟨idx, hidx⟩ : Fin m)).filter (· ∈ T) = T := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
      constructor
      · exact fun h => h.2
      · intro hi
        exact ⟨(Finset.mem_erase.mp (hTS hi)).1, hi⟩
    rw [hfilt, hTcard]
  rw [hhead, htail]

private lemma repr_two_twos_and_ones {m lo i1 i2 t : ℕ} (hlo1 : lo ≤ i1) (hlo2 : lo ≤ i2)
    (hi1 : i1 < m) (hi2 : i2 < m) (hne : i1 ≠ i2) (ht : t ≤ m - lo - 2) :
    ∃ x : Fin m → ℕ, (∀ i : Fin m, i.val < lo → x i = 0) ∧
      ∑ i : Fin m, polygonalNumber (m + i.val + 1) (x i) = (m + i1 + 1) + (m + i2 + 1) + t := by
  let u1 : Fin m := ⟨i1, hi1⟩
  let u2 : Fin m := ⟨i2, hi2⟩
  have hu : u1 ≠ u2 := fun h => hne (congrArg Fin.val h)
  let S : Finset (Fin m) := ((Finset.univ.filter fun i : Fin m => lo ≤ i.val).erase u1).erase u2
  have hScard : S.card = m - lo - 2 := by
    have hmem1 : u1 ∈ Finset.univ.filter (fun i : Fin m => lo ≤ i.val) := by simp [u1, hlo1]
    have hmem2 : u2 ∈ (Finset.univ.filter (fun i : Fin m => lo ≤ i.val)).erase u1 :=
      Finset.mem_erase.mpr ⟨hu.symm, by simp [u2, hlo2]⟩
    rw [Finset.card_erase_of_mem hmem2, Finset.card_erase_of_mem hmem1]
    have hfilt : (Finset.univ.filter fun i : Fin m => lo ≤ i.val).card = m - lo := by
      have hbij : (Finset.univ.filter fun i : Fin m => lo ≤ i.val).card = (Finset.Ico lo m).card := by
        refine Finset.card_nbij (fun i : Fin m => i.val) ?_ ?_ ?_
        · intro i hi
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi
          exact Finset.mem_coe.mpr (Finset.mem_Ico.mpr ⟨hi, i.isLt⟩)
        · intro i _ j _ h; exact Fin.ext h
        · intro k hk
          rw [Finset.mem_coe, Finset.mem_Ico] at hk
          exact ⟨⟨k, hk.2⟩, by simp [hk.1], rfl⟩
      rw [hbij, Nat.card_Ico]
    omega
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq (show t ≤ S.card by omega)
  let x : Fin m → ℕ := fun i => if i = u1 ∨ i = u2 then 2 else if i ∈ T then 1 else 0
  have hzero : ∀ i : Fin m, i.val < lo → x i = 0 := by
    intro i hi
    have h1 : i ≠ u1 := fun h => by have := congrArg Fin.val h; dsimp [u1] at this; omega
    have h2 : i ≠ u2 := fun h => by have := congrArg Fin.val h; dsimp [u2] at this; omega
    have hnotT : i ∉ T := fun hT => by
      have hS := Finset.mem_erase.mp (Finset.mem_erase.mp (hTS hT)).2
      have := (Finset.mem_filter.mp hS.2).2
      omega
    simp [x, h1, h2, hnotT]
  refine ⟨x, hzero, ?_⟩
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ u1)]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hu.symm, Finset.mem_univ u2⟩)]
  have h1 : polygonalNumber (m + u1.val + 1) (x u1) = m + i1 + 1 := by
    simp only [x, true_or, ↓reduceIte, u1]
    exact poly_two (by omega)
  have h2 : polygonalNumber (m + u2.val + 1) (x u2) = m + i2 + 1 := by
    simp only [x, or_true, ↓reduceIte, u2]
    exact poly_two (by omega)
  have htail : ∑ i ∈ (Finset.univ.erase u1).erase u2,
      polygonalNumber (m + i.val + 1) (x i) = t := by
    have hterm : ∀ i ∈ (Finset.univ.erase u1).erase u2,
        polygonalNumber (m + i.val + 1) (x i) = if i ∈ T then 1 else 0 := by
      intro i hi
      have hne2 : i ≠ u2 := (Finset.mem_erase.mp hi).1
      have hne1 : i ≠ u1 := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
      simp only [x, hne1, hne2, or_self, ↓reduceIte]
      split_ifs <;> simp [polygonalNumber]
    rw [Finset.sum_congr rfl hterm, Finset.sum_boole, Nat.cast_id]
    have hfilt : ((Finset.univ.erase u1).erase u2).filter (· ∈ T) = T := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
      constructor
      · exact fun h => h.2
      · intro hi
        have hS1 := Finset.mem_erase.mp (hTS hi)
        have hS2 := Finset.mem_erase.mp hS1.2
        exact ⟨⟨hS1.1, hS2.1⟩, hi⟩
    rw [hfilt, hTcard]
  rw [h1, h2, htail]
  omega

-- Every residue class modulo L = 2 * m + 13 has a representative R ≤ 4 * m + 25 using only indices ≥ 16.
private lemma repr_residue_tail {m : ℕ} (hm : 66 ≤ m) (rem : ℕ) (hrem : rem < 2 * m + 13) :
    ∃ R : ℕ, R ≤ 4 * m + 25 ∧ R % (2 * m + 13) = rem ∧
      ∃ x : Fin m → ℕ, (∀ i : Fin m, i.val < 16 → x i = 0) ∧
        ∑ i : Fin m, polygonalNumber (m + i.val + 1) (x i) = R := by
  by_cases h1 : rem ≤ m - 16
  · obtain ⟨x, hx0, hxsum⟩ := repr_ones_in_tail (m := m) (lo := 16) (t := rem) (by omega)
    exact ⟨rem, by omega, Nat.mod_eq_of_lt hrem, x, hx0, hxsum⟩
  by_cases h2 : rem ≤ m + 4
  · -- Use R = (2 * m + 13) + rem ∈ [2*m + 35, 3*m + 17] via i1 = 16, i2 = 17
    set t := (2 * m + 13) + rem - (2 * m + 35)
    obtain ⟨x, hx0, hxsum⟩ :=
      repr_two_twos_and_ones (m := m) (lo := 16) (i1 := 16) (i2 := 17) (t := t)
        (by omega) (by omega) (by omega) (by omega) (by decide) (by omega)
    refine ⟨(2 * m + 13) + rem, by omega, ?_, x, hx0, by omega⟩
    rw [Nat.add_mod_left, Nat.mod_eq_of_lt hrem]
  by_cases h3 : rem ≤ 2 * m - 14
  · -- Use R = (2 * m + 13) + rem ∈ [3*m + 17, 4*m - 1] via i1 = 16, i2 = m - 1
    set t := (2 * m + 13) + rem - (3 * m + 17)
    obtain ⟨x, hx0, hxsum⟩ :=
      repr_two_twos_and_ones (m := m) (lo := 16) (i1 := 16) (i2 := m - 1) (t := t)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    refine ⟨(2 * m + 13) + rem, by omega, ?_, x, hx0, by omega⟩
    rw [Nat.add_mod_left, Nat.mod_eq_of_lt hrem]
  · -- Remaining: 2 * m - 13 ≤ rem < 2 * m + 13; use R = (2 * m + 13) + rem ∈ [4*m, 4*m + 25]
    -- via i1 = m - 2, i2 = m - 1 (sum 4*m - 1) + t ones
    set t := (2 * m + 13) + rem - (4 * m - 1)
    obtain ⟨x, hx0, hxsum⟩ :=
      repr_two_twos_and_ones (m := m) (lo := 16) (i1 := m - 2) (i2 := m - 1) (t := t)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    refine ⟨(2 * m + 13) + rem, by omega, ?_, x, hx0, by omega⟩
    rw [Nat.add_mod_left, Nat.mod_eq_of_lt hrem]

-- Head quad function on indices 0..15 yielding (2 * m + 13) * (u0^2 + u1^2 + u2^2 + u3^2) + 8
private def headVal (u0 u1 u2 u3 : ℕ) (j : ℕ) : ℕ :=
  match j with
  | 0 => u0 + 1
  | 1 => u1 + 1
  | 2 => u2 + 1
  | 3 => u3 + 1
  | 4 => u0
  | 5 => u1
  | 6 => u2
  | 7 => u3
  | 8 => u3 + 1
  | 9 => u2 + 1
  | 10 => u1 + 1
  | 11 => u0 + 1
  | 12 => u3
  | 13 => u2
  | 14 => u1
  | 15 => u0
  | _ => 0

private lemma sum_headVal {m : ℕ} (hm : 66 ≤ m) (u0 u1 u2 u3 : ℕ) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin m => i.val < 16),
      polygonalNumber (m + i.val + 1) (headVal u0 u1 u2 u3 i.val) =
      (2 * m + 13) * (u0 ^ 2 + u1 ^ 2 + u2 ^ 2 + u3 ^ 2) + 8 := by
  have hbij :
      ∑ i ∈ Finset.univ.filter (fun i : Fin m => i.val < 16),
        polygonalNumber (m + i.val + 1) (headVal u0 u1 u2 u3 i.val) =
      ∑ j ∈ Finset.range 16, polygonalNumber (m + j + 1) (headVal u0 u1 u2 u3 j) := by
    refine Finset.sum_nbij (fun i : Fin m => i.val) ?_ ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact Finset.mem_coe.mpr (Finset.mem_range.mpr hi)
    · intro i _ j _ h; exact Fin.ext h
    · intro k hk
      rw [Finset.mem_coe, Finset.mem_range] at hk
      exact ⟨⟨k, by omega⟩, by simp [hk], rfl⟩
    · intro _ _; rfl
  rw [hbij]
  have h16 : ∑ j ∈ Finset.range 16, polygonalNumber (m + j + 1) (headVal u0 u1 u2 u3 j) =
      (polygonalNumber (m + 1) (u0 + 1) + polygonalNumber (m + 5) u0) +
      (polygonalNumber (m + 12) (u0 + 1) + polygonalNumber (m + 16) u0) +
      (polygonalNumber (m + 2) (u1 + 1) + polygonalNumber (m + 6) u1) +
      (polygonalNumber (m + 11) (u1 + 1) + polygonalNumber (m + 15) u1) +
      (polygonalNumber (m + 3) (u2 + 1) + polygonalNumber (m + 7) u2) +
      (polygonalNumber (m + 10) (u2 + 1) + polygonalNumber (m + 14) u2) +
      (polygonalNumber (m + 4) (u3 + 1) + polygonalNumber (m + 8) u3) +
      (polygonalNumber (m + 9) (u3 + 1) + polygonalNumber (m + 13) u3) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, headVal]
    ring
  rw [h16]
  have p0 := poly_pair_sq (k := m + 1) (by omega) u0
  have p0' := poly_pair_sq (k := m + 12) (by omega) u0
  have p1 := poly_pair_sq (k := m + 2) (by omega) u1
  have p1' := poly_pair_sq (k := m + 11) (by omega) u1
  have p2 := poly_pair_sq (k := m + 3) (by omega) u2
  have p2' := poly_pair_sq (k := m + 10) (by omega) u2
  have p3 := poly_pair_sq (k := m + 4) (by omega) u3
  have p3' := poly_pair_sq (k := m + 9) (by omega) u3
  linarith

end OeisA160324R1H3Proof

theorem OMA.solution : OMA.R_OeisA160324_conjecture2_R1.H3 := by
  intro m hm n
  by_cases hsmall : n < 4 * m + 33
  · -- Direct small cases using all m indices
    by_cases h1 : n ≤ m
    · obtain ⟨x, _, hxsum⟩ := OeisA160324R1H3Proof.repr_ones_in_tail (m := m) (lo := 0) (t := n) (by omega)
      exact ⟨x, hxsum.symm⟩
    by_cases h2 : n ≤ 2 * m
    · obtain ⟨x, _, hxsum⟩ :=
        OeisA160324R1H3Proof.repr_one_two_and_ones (m := m) (lo := 0) (idx := n - (m + 1)) (t := 0)
          (by omega) (by omega) (by omega)
      exact ⟨x, by omega⟩
    by_cases h3 : n ≤ 3 * m - 1
    · obtain ⟨x, _, hxsum⟩ :=
        OeisA160324R1H3Proof.repr_one_two_and_ones (m := m) (lo := 0) (idx := m - 1) (t := n - 2 * m)
          (by omega) (by omega) (by omega)
      exact ⟨x, by omega⟩
    by_cases h4 : n ≤ 4 * m - 2
    · obtain ⟨x, _, hxsum⟩ :=
        OeisA160324R1H3Proof.repr_two_twos_and_ones (m := m) (lo := 0) (i1 := 0) (i2 := m - 2)
          (t := n - 3 * m) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      exact ⟨x, by omega⟩
    · obtain ⟨x, _, hxsum⟩ :=
        OeisA160324R1H3Proof.repr_two_twos_and_ones (m := m) (lo := 0) (i1 := m - 2) (i2 := m - 1)
          (t := n - (4 * m - 1)) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      exact ⟨x, by omega⟩
  · -- Large case n ≥ 4 * m + 33: split off residue mod (2 * m + 13) on tail, four squares on head
    set L := 2 * m + 13
    have hLpos : 0 < L := by omega
    set rem := (n - 8) % L
    have hrem : rem < L := Nat.mod_lt _ hLpos
    obtain ⟨R, hRle, hRmod, xTail, hxTail0, hxTailSum⟩ :=
      OeisA160324R1H3Proof.repr_residue_tail hm rem hrem
    have hsub : L ∣ (n - 8 - R) := by
      have h1 : n - 8 = L * ((n - 8) / L) + rem := (Nat.div_add_mod (n - 8) L).symm
      have h2 : R = L * (R / L) + rem := by rw [← hRmod]; exact (Nat.div_add_mod R L).symm
      have hge_div : R / L ≤ (n - 8) / L := Nat.div_le_div_right (by omega)
      refine ⟨(n - 8) / L - R / L, ?_⟩
      rw [Nat.mul_sub]
      omega
    obtain ⟨q, hq⟩ := hsub
    obtain ⟨u0, u1, u2, u3, hu⟩ := Nat.sum_four_squares q
    let x : Fin m → ℕ := fun i =>
      if i.val < 16 then OeisA160324R1H3Proof.headVal u0 u1 u2 u3 i.val else xTail i
    refine ⟨x, ?_⟩
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin m => i.val < 16)]
    have hhead : ∑ i ∈ Finset.univ.filter (fun i : Fin m => i.val < 16),
        OeisA160324.polygonalNumber (m + i.val + 1) (x i) = L * q + 8 := by
      have hcongr : ∑ i ∈ Finset.univ.filter (fun i : Fin m => i.val < 16),
          OeisA160324.polygonalNumber (m + i.val + 1) (x i) =
          ∑ i ∈ Finset.univ.filter (fun i : Fin m => i.val < 16),
            OeisA160324.polygonalNumber (m + i.val + 1) (OeisA160324R1H3Proof.headVal u0 u1 u2 u3 i.val) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have hlt : i.val < 16 := (Finset.mem_filter.mp hi).2
        simp [x, hlt]
      rw [hcongr, OeisA160324R1H3Proof.sum_headVal hm u0 u1 u2 u3, hu]
    have htail : ∑ i ∈ Finset.univ.filter (fun i : Fin m => ¬ i.val < 16),
        OeisA160324.polygonalNumber (m + i.val + 1) (x i) = R := by
      rw [← hxTailSum]
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin m => i.val < 16)]
      have hz : ∑ i ∈ Finset.univ.filter (fun i : Fin m => i.val < 16),
          OeisA160324.polygonalNumber (m + i.val + 1) (xTail i) = 0 := by
        refine Finset.sum_eq_zero fun i hi => ?_
        rw [hxTail0 i (Finset.mem_filter.mp hi).2, OeisA160324R1H3Proof.poly_zero]
      rw [hz, zero_add]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hge : ¬ i.val < 16 := (Finset.mem_filter.mp hi).2
      simp [x, hge]
    rw [hhead, htail]
    omega
