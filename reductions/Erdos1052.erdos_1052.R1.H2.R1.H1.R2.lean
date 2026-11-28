import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R2


lemma complement_product (s : Finset ℕ) (f : ℕ → ℚ)
    (hf : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ 1) :
    1 - ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 - f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hs : ∀ j ∈ s, 0 ≤ f j ∧ f j ≤ 1 := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    obtain ⟨hi0, hi1⟩ := hf i (Finset.mem_insert_self i s)
    have hsum : 0 ≤ ∑ j ∈ s, f j := Finset.sum_nonneg (fun j hj => (hs j hj).1)
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    have hm := mul_le_mul_of_nonneg_left (ih hs) (sub_nonneg.mpr hi1)
    nlinarith [mul_nonneg hi0 hsum]

lemma admissible_of_small_sum (s : Finset ℕ)
    (h : (∑ p ∈ s, ((s.card : ℚ) + 3) / ((p : ℚ) + 1)) ≤ 4 / 2101) :
    (∀ p ∈ s, 128 ≤ p ∧ s.card + 3 ≤ p) ∧
    ∏ p ∈ s, (((p : ℚ) + 1) / ((p : ℚ) - 2 - (s.card : ℚ))) ≤ 2101 / 2097 := by
  let f (p : ℕ) : ℚ := ((s.card : ℚ) + 3) / ((p : ℚ) + 1)
  have hf (p : ℕ) : 0 ≤ f p := by dsimp [f]; positivity
  have hsmall (p : ℕ) (hp : p ∈ s) : f p ≤ 4 / 2101 :=
    (Finset.single_le_sum (fun j _ => hf j) hp).trans h
  have hrange (p : ℕ) (hp : p ∈ s) : 128 ≤ p ∧ s.card + 3 ≤ p := by
    have hp0 : 0 < (p : ℚ) + 1 := by positivity
    have hx := (div_le_iff₀ hp0).mp (hsmall p hp)
    have hk : 0 ≤ (s.card : ℚ) := by positivity
    constructor
    · exact_mod_cast (show (128 : ℚ) ≤ p by linarith)
    · exact_mod_cast (show (s.card : ℚ) + 3 ≤ p by linarith)
  refine ⟨hrange, ?_⟩
  let D := ∏ p ∈ s, (1 - f p)
  have hD : 2097 / 2101 ≤ D := by
    have hprod := complement_product s f (fun p hp => ⟨hf p, le_trans (hsmall p hp) (by norm_num)⟩)
    change (∑ p ∈ s, f p) ≤ 4 / 2101 at h
    dsimp only [D]
    linarith
  have hDpos : 0 < D := by linarith
  have hid : (∏ p ∈ s, (((p : ℚ) + 1) / ((p : ℚ) - 2 - (s.card : ℚ)))) * D = 1 := by
    dsimp only [D]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro p hp
    have h1 : (p : ℚ) - 2 - (s.card : ℚ) ≠ 0 := by
      have hh : (s.card : ℚ) + 3 ≤ p := by exact_mod_cast (hrange p hp).2
      linarith
    have h2 : (p : ℚ) + 1 ≠ 0 := by positivity
    dsimp only [f]
    field_simp
    ring
  rw [(eq_div_iff hDpos.ne').mpr hid]
  apply (div_le_iff₀ hDpos).2
  linarith


lemma small_member_of_not_admissible (s : Finset ℕ)
    (hbad : ¬ ((∀ p ∈ s, 128 ≤ p ∧ s.card + 3 ≤ p) ∧
      ∏ p ∈ s, (((p : ℚ) + 1) / ((p : ℚ) - 2 - (s.card : ℚ))) ≤ 2101 / 2097)) :
    ∃ p ∈ s, 4 * (p + 1) < 2101 * s.card * (s.card + 3) := by
  by_contra! hall
  apply hbad
  apply admissible_of_small_sum
  by_cases hz : s.card = 0
  · simp [Finset.card_eq_zero.mp hz]
    norm_num
  have hpos : (0 : ℚ) < s.card := by exact_mod_cast Nat.pos_of_ne_zero hz
  calc
    _ ≤ ∑ _p ∈ s, ((4 / 2101 : ℚ) / s.card) := by
      apply Finset.sum_le_sum
      intro p hp
      have ha : (2101 : ℚ) * s.card * (s.card + 3) ≤ 4 * ((p : ℚ) + 1) := by exact_mod_cast hall p hp
      have hp' : (0 : ℚ) < (p : ℚ) + 1 := by positivity
      apply (div_le_div_iff₀ hp' hpos).2
      linarith
    _ = 4 / 2101 := by simp [nsmul_eq_mul, ne_of_gt hpos, mul_div_cancel₀]

lemma pair_admissible_iff (p q : ℕ) (hpq : p < q) :
    ((∀ z ∈ ({p, q} : Finset ℕ), 128 ≤ z ∧ ({p, q} : Finset ℕ).card + 3 ≤ z) ∧
    ∏ z ∈ ({p, q} : Finset ℕ), (((z : ℚ) + 1) / ((z : ℚ) - 2 - (({p, q} : Finset ℕ).card : ℚ))) ≤ 2101 / 2097) ↔
    2626 ≤ p ∧ 10501 * (p + q) ≤ 4 * p * q + 31519 := by
  have hc : ({p, q} : Finset ℕ).card = 2 := by simp [hpq.ne]
  rw [hc]
  have hpr (hp : 128 ≤ p) :
      ((∏ z ∈ ({p, q} : Finset ℕ), (((z : ℚ) + 1) / ((z : ℚ) - 2 - (2 : ℕ)))) ≤ 2101 / 2097) ↔
      10501 * (p + q) ≤ 4 * p * q + 31519 := by
    have hp0 : (0 : ℚ) < (p : ℚ) - 2 - 2 := by
      have hh : (128 : ℚ) ≤ p := by exact_mod_cast hp
      linarith
    have hq0 : (0 : ℚ) < (q : ℚ) - 2 - 2 := by
      have hh : (p : ℚ) < q := by exact_mod_cast hpq
      linarith
    simp only [Finset.prod_insert (show p ∉ ({q} : Finset ℕ) by simpa using hpq.ne), Finset.prod_singleton, Nat.cast_ofNat, div_mul_div_comm]
    rw [div_le_div_iff₀ (mul_pos hp0 hq0) (by norm_num)]
    constructor
    · intro h
      exact_mod_cast (show (10501 : ℚ) * ((p : ℚ) + q) ≤ 4 * p * q + 31519 by nlinarith only [h])
    · intro h
      have hr : (10501 : ℚ) * ((p : ℚ) + q) ≤ 4 * p * q + 31519 := by exact_mod_cast h
      nlinarith only [hr]
  constructor
  · rintro ⟨hlow, hprod⟩
    have h128 := (hlow p (by simp)).1
    have hh := (hpr h128).mp hprod
    refine ⟨?_, hh⟩
    by_contra! hn
    have hb : p ≤ 2625 := by omega
    have hbound := Nat.mul_le_mul_right q hb
    nlinarith only [hh, hbound, h128]
  · rintro ⟨hp, hpoly⟩
    have h128 : 128 ≤ p := by omega
    refine ⟨?_, (hpr h128).mpr hpoly⟩
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> omega

lemma two_member_obstruction (s : Finset ℕ)
    (hbad : ¬ ((∀ p ∈ s, 128 ≤ p ∧ s.card + 3 ≤ p) ∧
      ∏ p ∈ s, (((p : ℚ) + 1) / ((p : ℚ) - 2 - (s.card : ℚ))) ≤ 2101 / 2097))
    (hlarge : ∀ p ∈ s, 2101 * (s.card + 3) < 4 * (p + 1)) :
    ∃ p ∈ s, ∃ q ∈ s, p < q ∧
      4 * (p + 1) < 2101 * s.card * (s.card + 3) ∧
      4 * (p + 1) * (q + 1) <
        2101 * (s.card + 3) * ((q + 1) + (s.card - 1) * (p + 1)) := by
  classical
  obtain ⟨t, ht, htbound⟩ := small_member_of_not_admissible s hbad
  let p := s.min' ⟨t, ht⟩
  have hp : p ∈ s := s.min'_mem _
  have hmin (i) (hi : i ∈ s) : p ≤ i := s.min'_le i hi
  have hpbound : 4 * (p + 1) < 2101 * s.card * (s.card + 3) := by
    have := hmin t ht
    omega
  let f (i : ℕ) : ℚ := ((s.card : ℚ) + 3) / ((i : ℚ) + 1)
  have hsum : 4 / 2101 < ∑ i ∈ s, f i := lt_of_not_ge (fun h => hbad (admissible_of_small_sum s h))
  have hp0 : (0 : ℚ) < (p : ℚ) + 1 := by positivity
  have hfp : f p < 4 / 2101 := by
    have hh : (2101 : ℚ) * (s.card + 3) < 4 * ((p : ℚ) + 1) := by exact_mod_cast hlarge p hp
    exact (div_lt_iff₀ hp0).2 (by linarith)
  have hadd := Finset.sum_erase_add (s := s) f hp
  have hne : (s.erase p).Nonempty := by
    by_contra! h
    rw [h] at hadd
    simp only [Finset.sum_empty, zero_add] at hadd
    linarith
  obtain ⟨q, hq, hmax⟩ := (s.erase p).exists_max_image f hne
  obtain ⟨hne', hqs⟩ := Finset.mem_erase.mp hq
  have hrest : (∑ i ∈ s.erase p, f i) ≤ ((s.erase p).card : ℚ) * f q := by
    simpa [nsmul_eq_mul] using (Finset.sum_le_sum (s := s.erase p) (g := fun _ => f q) hmax)
  have htotal : 4 / 2101 < f p + ((s.erase p).card : ℚ) * f q := by linarith
  refine ⟨p, hp, q, hqs, lt_of_le_of_ne (hmin q hqs) hne'.symm, hpbound, ?_⟩
  rw [Finset.card_erase_of_mem hp] at htotal
  dsimp only [f] at htotal
  have hq0 : (0 : ℚ) < (q : ℚ) + 1 := by positivity
  field_simp at htotal
  exact_mod_cast (show (4 : ℚ) * (p + 1) * (q + 1) <
    2101 * ((s.card : ℚ) + 3) * (((q : ℚ) + 1) + ((s.card - 1 : ℕ) : ℚ) * ((p : ℚ) + 1)) by nlinarith only [htotal])

lemma pair_cutoff (p q : ℕ) (hpq : p < q)
    (h : 4 * p * q + 31519 < 10501 * (p + q)) : p < 5249 := by
  by_contra! hp
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hp
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hpq.le
  nlinarith

-- One repeated prime already reaches the individual threshold.
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) →
    (∃ p ∈ S, 4 * (p + 1) ≤ 2101 * (S.card + 3)) → padicValNat 2 n ≤ A

-- Exactly two repeated primes. Both range over an explicit finite set of pairs.
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    ∀ p q : ℕ, (∀ z, z ∈ ({p, q} : Finset ℕ) ↔ z.Prime ∧ z ≠ 2 ∧ z ^ 2 ∣ n) →
    2626 ≤ p → p < 5249 → p < q → 4 * p * q + 31519 < 10501 * (p + q) → padicValNat 2 n ≤ A

-- At least three repeated primes. Two are confined to explicit finite ranges for each cardinality.
def H3 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    ∀ S : Finset ℕ, (∀ z, z ∈ S ↔ z.Prime ∧ z ≠ 2 ∧ z ^ 2 ∣ n) → (3 ≤ S.card) →
    (∀ z ∈ S, 2101 * (S.card + 3) < 4 * (z + 1)) →
    (∃ p ∈ S, ∃ q ∈ S, p < q ∧
      4 * (p + 1) < 2101 * S.card * (S.card + 3) ∧
      4 * (p + 1) * (q + 1) < 2101 * (S.card + 3) * ((q + 1) + (S.card - 1) * (p + 1))) →
    padicValNat 2 n ≤ A

theorem main : H1 → H2 → H3 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1.H1 := by
  classical
  rintro ⟨A, ha⟩ ⟨B, hb⟩ ⟨C, hc⟩
  refine ⟨max A (max B C), ?_⟩
  intro n hn _ S hS hbad
  by_cases hs : ∃ p ∈ S, 4 * (p + 1) ≤ 2101 * (S.card + 3)
  · exact (ha n hn S hS hs).trans (le_max_left _ _)
  have hlarge : ∀ p ∈ S, 2101 * (S.card + 3) < 4 * (p + 1) := by
    intro p hp
    exact lt_of_not_ge (fun h => hs ⟨p, hp, h⟩)
  obtain hw := two_member_obstruction S hbad hlarge
  obtain ⟨p, hp, q, hq, hpq, hw1, hw2⟩ := hw
  have hsub : ({p, q} : Finset ℕ) ⊆ S := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    exact hz.elim (fun e => e ▸ hp) (fun e => e ▸ hq)
  have hcard : ({p, q} : Finset ℕ).card = 2 := by simp [hpq.ne]
  by_cases hsmall : S.card ≤ 2
  · have heq : ({p, q} : Finset ℕ) = S := Finset.eq_of_subset_of_card_le hsub (by omega)
    subst S
    have h2626 : 2626 ≤ p := by have hh := hlarge p (by simp); rw [hcard] at hh; omega
    have hpoly : 4 * p * q + 31519 < 10501 * (p + q) := by
      by_contra! hh
      exact hbad ((pair_admissible_iff p q hpq).mpr ⟨h2626, hh⟩)
    exact (hb n hn p q hS h2626 (pair_cutoff p q hpq hpoly) hpq hpoly).trans ((le_max_left B C).trans (le_max_right A _))
  · exact (hc n hn S hS (by omega) hlarge ⟨p, hp, q, hq, hpq, hw1, hw2⟩).trans ((le_max_right B C).trans (le_max_right A _))

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R2
