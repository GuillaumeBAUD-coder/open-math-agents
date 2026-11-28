import OMAStatements.S_oeis_a032312

/-!
Peter Bala's Gauss congruence conjecture (September 5, 2022), OEIS A032312.
Source: https://oeis.org/A032312/internal
Proof credited to @grp06.
-/

namespace A032312Proof

open Finset Polynomial
open scoped BigOperators

private def size (i : ℕ) : ℕ := i + 1

private def subsets (m : ℕ) : Finset (Finset ℕ) :=
  (range m).powerset.filter fun D => D.sum size = m

private def weight (D : Finset ℕ) : ℕ := 2 ^ D.card * Nat.multinomial D size

private def count (m : ℕ) : ℕ := (subsets m).sum weight

private theorem mem_subsets {D : Finset ℕ} {m : ℕ} :
    D ∈ subsets m ↔ D.sum size = m := by
  simp only [subsets, mem_filter, mem_powerset]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  intro i hi
  have hle : size i ≤ D.sum size := single_le_sum (f := size) (fun _ _ => Nat.zero_le _) hi
  simp only [size, h] at hle
  exact mem_range.mpr (by omega)

private theorem prod_monomials (D : Finset ℕ) (c : ℕ → ℚ) :
    (∏ i ∈ D, monomial (size i) (c i)) =
      monomial (D.sum size) (D.prod c) := by
  classical
  induction D using Finset.induction_on with
  | empty => simp
  | insert i D hi ih =>
    rw [prod_insert hi, ih, sum_insert hi, prod_insert hi, monomial_mul_monomial]

private theorem a_eq_count (m : ℕ) :
    OMA.S_oeis_a032312.a m = (count m : ℚ) := by
  classical
  unfold OMA.S_oeis_a032312.a count
  change (m.factorial : ℚ) *
    (∏ i ∈ range m, (1 + C (2 / ((size i).factorial : ℚ)) * X ^ size i : ℚ[X])).coeff m =
    ((∑ D ∈ subsets m, weight D : ℕ) : ℚ)
  simp_rw [C_mul_X_pow_eq_monomial]
  rw [Finset.prod_one_add, Polynomial.finsetSum_coeff, Finset.mul_sum, Nat.cast_sum]
  unfold subsets
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro D hD
  rw [prod_monomials, coeff_monomial]
  by_cases h : D.sum size = m
  · simp only [if_pos h]
    have hs := Nat.multinomial_spec D size
    rw [h] at hs
    have hsQ : (∏ i ∈ D, ((size i).factorial : ℚ)) *
        (Nat.multinomial D size : ℚ) = (m.factorial : ℚ) := by
      simpa only [Nat.cast_mul, Nat.cast_prod] using congrArg (fun x : ℕ => (x : ℚ)) hs
    have hne : (∏ i ∈ D, ((size i).factorial : ℚ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => by exact_mod_cast Nat.factorial_ne_zero (size i)
    rw [Finset.prod_div_distrib, Finset.prod_const]
    simp only [weight, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [hsQ.symm, mul_comm (∏ i ∈ D, ((size i).factorial : ℚ)),
      mul_assoc, mul_div_cancel₀ _ hne, mul_comm]
  · simp only [if_neg h, mul_zero]

/-- Keep only the factors in a factorial that are coprime to the prime. -/
private def unitFactor (p i : ℕ) : ℕ := if p ∣ i + 1 then 1 else i + 1

private def unitProd (p t : ℕ) : ℕ := (range t).prod (unitFactor p)

private theorem factorial_units (p t : ℕ) :
    t.factorial = p ^ (t / p) * (t / p).factorial * unitProd p t := by
  induction t with
  | zero => simp [unitProd]
  | succ t ih =>
    rw [Nat.factorial_succ, ih]
    have hu : unitProd p (t + 1) = unitProd p t * unitFactor p t :=
      Finset.prod_range_succ (unitFactor p) t
    rw [hu]
    by_cases h : p ∣ t + 1
    · have hd : (t + 1) / p = t / p + 1 := Nat.succ_div_of_dvd h
      have ht : t + 1 = p * (t / p + 1) := by
        rw [← hd, Nat.mul_div_cancel' h]
      rw [hd, unitFactor, if_pos h, mul_one, pow_succ, Nat.factorial_succ]
      calc
        (t + 1) * (p ^ (t / p) * (t / p).factorial * unitProd p t) =
            (p * (t / p + 1)) * (p ^ (t / p) * (t / p).factorial * unitProd p t) :=
          congrArg (fun x => x * (p ^ (t / p) * (t / p).factorial * unitProd p t)) ht
        _ = _ := by ring
    · rw [Nat.succ_div_of_not_dvd h, unitFactor, if_neg h]
      ring

private theorem factorial_units_mul {p : ℕ} (hp : p.Prime) (t : ℕ) :
    (p * t).factorial = p ^ t * t.factorial * unitProd p (p * t) := by
  calc
    (p * t).factorial = p ^ ((p * t) / p) * ((p * t) / p).factorial * unitProd p (p * t) :=
      factorial_units p (p * t)
    _ = _ := by rw [Nat.mul_div_cancel_left t hp.pos]

private theorem unitProd_isUnit {p k : ℕ} (hp : p.Prime) (hk : 0 < k) (t : ℕ) :
    IsUnit (unitProd p t : ZMod (p ^ k)) := by
  rw [unitProd, Nat.cast_prod, IsUnit.prod_iff]
  intro i hi
  by_cases h : p ∣ i + 1
  · simp [unitFactor, h]
  · simpa only [unitFactor, if_neg h] using
      (ZMod.isUnit_natCast_iff_not_dvd_pow hp hk).2 h

private theorem unitFactor_shift {p q a : ℕ} (hpq : p ∣ q) (ha : q ∣ a) (i : ℕ) :
    (unitFactor p (a + i) : ZMod q) = (unitFactor p i : ZMod q) := by
  have hpa : p ∣ a := hpq.trans ha
  have he : p ∣ a + i + 1 ↔ p ∣ i + 1 := by
    rw [add_assoc]
    exact (Nat.dvd_add_iff_right hpa).symm
  by_cases h : p ∣ i + 1
  · simp [unitFactor, h, he.mpr h]
  · have hz : (a : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff a q).2 ha
    simp [unitFactor, h, mt he.mp h, hz]

/-- A complete block of length q has the same product of unit factors
as the initial block, modulo q, when p divides q. -/
private theorem unitProd_blocks {p q : ℕ} (hpq : p ∣ q) (b : ℕ) :
    (unitProd p (q * b) : ZMod q) = (unitProd p q : ZMod q) ^ b := by
  induction b with
  | zero => simp [unitProd]
  | succ b ih =>
    have hb : q ∣ q * b := dvd_mul_right q b
    have hprod : (∏ i ∈ range q, (unitFactor p (q * b + i) : ZMod q)) =
        (unitProd p q : ZMod q) := by
      rw [unitProd, Nat.cast_prod]
      exact Finset.prod_congr rfl fun i _ => unitFactor_shift hpq hb i
    have hstep : (unitProd p (q * (b + 1)) : ZMod q) =
        (unitProd p (q * b) : ZMod q) *
          ∏ i ∈ range q, (unitFactor p (q * b + i) : ZMod q) := by
      simp only [Nat.mul_succ, unitProd, Finset.prod_range_add, Nat.cast_mul, Nat.cast_prod]
    rw [hstep, hprod, ih, pow_succ]

private theorem sum_scale (D : Finset ℕ) (p : ℕ) (f : ℕ → ℕ) :
    (∑ i ∈ D, p * f i) = p * D.sum f :=
  (Finset.mul_sum D f p).symm

private theorem unitProd_congr {p q : ℕ} (hpq : p ∣ q) (D : Finset ℕ) (f : ℕ → ℕ)
    (hf : ∀ i ∈ D, q ∣ f i) :
    unitProd p (D.sum f) ≡ (∏ i ∈ D, unitProd p (f i)) [MOD q] := by
  let g := fun i => f i / q
  have hi : ∀ i ∈ D, f i = q * g i :=
    fun i h => (Nat.mul_div_cancel' (hf i h)).symm
  have hs : D.sum f = q * D.sum g :=
    (Finset.sum_congr rfl hi).trans (sum_scale D q g)
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  rw [hs, unitProd_blocks hpq, Nat.cast_prod, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro i h
  calc
    (unitProd p q : ZMod q) ^ g i = (unitProd p (q * g i) : ZMod q) :=
      (unitProd_blocks hpq (g i)).symm
    _ = (unitProd p (f i) : ZMod q) :=
      congrArg (fun t : ℕ => (unitProd p t : ZMod q)) (hi i h).symm

/-- Cancel the identical product of factorials and the common power of p. -/
private theorem multinomial_units {p : ℕ} (hp : p.Prime) (D : Finset ℕ) (f : ℕ → ℕ) :
    (∏ i ∈ D, unitProd p (p * f i)) * Nat.multinomial D (fun i => p * f i) =
      unitProd p (p * D.sum f) * Nat.multinomial D f := by
  have h := Nat.multinomial_spec D (fun i => p * f i)
  have h' := Nat.multinomial_spec D f
  simp_rw [sum_scale, factorial_units_mul hp] at h
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← h'] at h
  have hc : p ^ D.sum f * (∏ i ∈ D, (f i).factorial) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hp.ne_zero)
      (Finset.prod_ne_zero_iff.mpr fun i _ => Nat.factorial_ne_zero (f i))
  apply (mul_right_inj' hc).mp
  calc
    (p ^ D.sum f * ∏ i ∈ D, (f i).factorial) *
        ((∏ i ∈ D, unitProd p (p * f i)) * Nat.multinomial D (fun i => p * f i)) =
      ((p ^ D.sum f * ∏ i ∈ D, (f i).factorial) * ∏ i ∈ D, unitProd p (p * f i)) *
        Nat.multinomial D (fun i => p * f i) := by ring
    _ = p ^ D.sum f * ((∏ i ∈ D, (f i).factorial) * Nat.multinomial D f) *
        unitProd p (p * D.sum f) := h
    _ = _ := by ring

/-- A size with precisely r factors of p forces the missing p-powers
in the multinomial through the binomial coefficient selecting that size. -/
private theorem multinomial_dvd {p : ℕ} (hp : p.Prime) (D : Finset ℕ) (f : ℕ → ℕ)
    {i r l b : ℕ} (hi : i ∈ D) (hfi : f i = p ^ r * b) (hb : ¬ p ∣ b)
    (hs : p ^ (r + l) ∣ D.sum f) :
    p ^ l ∣ Nat.multinomial D f := by
  have hfi0 : 0 < f i := by
    have hb0 : b ≠ 0 := by
      intro h
      apply hb
      rw [h]
      exact dvd_zero p
    rw [hfi]
    exact Nat.mul_pos (pow_pos hp.pos _) (Nat.pos_of_ne_zero hb0)
  have hsi : 0 < D.sum f :=
    hfi0.trans_le (Finset.single_le_sum (f := f) (fun _ _ => Nat.zero_le _) hi)
  let c := (D.sum f).choose (f i)
  have hchoose : f i * c = D.sum f * ((D.sum f - 1).choose (f i - 1)) := by
    obtain ⟨u, hu⟩ : ∃ u, D.sum f = u + 1 := ⟨D.sum f - 1, by omega⟩
    obtain ⟨v, hv⟩ : ∃ v, f i = v + 1 := ⟨f i - 1, by omega⟩
    unfold c
    rw [hu, hv]
    simpa [mul_comm] using (Nat.add_one_mul_choose_eq u v).symm
  have hmul : p ^ (r + l) ∣ f i * c := by
    rw [hchoose]
    exact dvd_mul_of_dvd_left hs _
  have hbc : p ^ l ∣ b * c := by
    rw [pow_add, hfi, mul_assoc] at hmul
    exact (mul_dvd_mul_iff_left (pow_ne_zero _ hp.ne_zero)).mp hmul
  have hc : p ^ l ∣ c :=
    ((hp.coprime_iff_not_dvd.mpr hb).pow_left l).dvd_of_dvd_mul_left hbc
  have hfactor : c ∣ Nat.multinomial D f := by
    have he : insert i (D.erase i) = D := Finset.insert_erase hi
    have ha : i ∉ D.erase i := Finset.notMem_erase _ _
    have hsum : D.sum f = f i + (D.erase i).sum f :=
      (congrArg (fun A : Finset ℕ => A.sum f) he.symm).trans (Finset.sum_insert ha)
    refine ⟨Nat.multinomial (D.erase i) f, ?_⟩
    calc
      Nat.multinomial D f = Nat.multinomial (insert i (D.erase i)) f :=
        congrArg (fun A => Nat.multinomial A f) he.symm
      _ = c * Nat.multinomial (D.erase i) f := by
        rw [Nat.multinomial_insert ha, ← hsum]
  exact hc.trans hfactor

private theorem common_power (p k : ℕ) (D : Finset ℕ) (f : ℕ → ℕ) :
    ∃ r ≤ k, (∀ i ∈ D, p ^ r ∣ f i) ∧
      (r = k ∨ ∃ i ∈ D, ¬ p ^ (r + 1) ∣ f i) := by
  classical
  induction k with
  | zero => exact ⟨0, le_rfl, by simp, Or.inl rfl⟩
  | succ k ih =>
    by_cases h : ∀ i ∈ D, p ^ (k + 1) ∣ f i
    · exact ⟨k + 1, le_rfl, h, Or.inl rfl⟩
    · obtain ⟨r, hr, hall, he⟩ := ih
      refine ⟨r, by omega, hall, Or.inr ?_⟩
      rcases he with e | e
      · subst r
        push Not at h
        exact h
      · exact e

private theorem multinomial_scale {p : ℕ} (hp : p.Prime) (k : ℕ)
    (D : Finset ℕ) (f : ℕ → ℕ) (hs : p ^ k ∣ D.sum f) :
    Nat.multinomial D (fun i => p * f i) ≡ Nat.multinomial D f [MOD p ^ (k + 1)] := by
  obtain ⟨r, hr, hall, hex⟩ := common_power p k D f
  have hd : p ^ (k - r) ∣ Nat.multinomial D f := by
    rcases hex with he | ⟨i, hi, hnot⟩
    · simp [he]
    · obtain ⟨b, hb⟩ := hall i hi
      have hcop : ¬ p ∣ b := by
        rintro ⟨v, hv⟩
        apply hnot
        exact ⟨v, by rw [hb, hv, pow_succ, mul_assoc]⟩
      have he : r + (k - r) = k := by omega
      exact multinomial_dvd hp D f hi hb hcop (by simpa only [he] using hs)
  have hq : p ∣ p ^ (r + 1) := by
    rw [pow_succ]
    exact dvd_mul_left p (p ^ r)
  have hblock := unitProd_congr hq D (fun i => p * f i) (by
    intro i hi
    obtain ⟨b, hb⟩ := hall i hi
    exact ⟨b, by rw [hb, pow_succ, ← mul_assoc, mul_comm p (p ^ r)]⟩)
  rw [sum_scale] at hblock
  obtain ⟨c, hc⟩ := hd
  have he : k - r + (r + 1) = k + 1 := by omega
  have hscaled := (hblock.mul_left c).mul_left' (p ^ (k - r))
  have hscaled' :
      Nat.multinomial D f * unitProd p (p * D.sum f) ≡
        Nat.multinomial D f * (∏ i ∈ D, unitProd p (p * f i)) [MOD p ^ (k + 1)] := by
    simpa only [← mul_assoc, ← hc, ← pow_add, he] using hscaled
  have hmul :
      (∏ i ∈ D, unitProd p (p * f i)) * Nat.multinomial D (fun i => p * f i) ≡
        (∏ i ∈ D, unitProd p (p * f i)) * Nat.multinomial D f [MOD p ^ (k + 1)] := by
    rw [multinomial_units hp]
    simpa only [mul_comm (Nat.multinomial D f)] using hscaled'
  have hu : IsUnit ((∏ i ∈ D, unitProd p (p * f i) : ℕ) : ZMod (p ^ (k + 1))) := by
    rw [Nat.cast_prod, IsUnit.prod_iff]
    exact fun i _ => unitProd_isUnit hp (Nat.succ_pos k) (p * f i)
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  apply hu.mul_left_cancel
  simpa only [Nat.cast_mul] using (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmul

private def scaleIndex {p : ℕ} (hp : p.Prime) : ℕ ↪ ℕ where
  toFun i := p * size i - 1
  inj' := by
    intro i j h
    change p * size i - 1 = p * size j - 1 at h
    have hi : 0 < p * size i := Nat.mul_pos hp.pos (Nat.succ_pos i)
    have hj : 0 < p * size j := Nat.mul_pos hp.pos (Nat.succ_pos j)
    have he : size i = size j := (mul_right_inj' hp.ne_zero).mp (by omega)
    unfold size at he
    omega

private theorem size_scale {p : ℕ} (hp : p.Prime) (i : ℕ) :
    size (scaleIndex hp i) = p * size i := by
  change p * size i - 1 + 1 = p * size i
  have hi : 0 < p * size i := Nat.mul_pos hp.pos (Nat.succ_pos i)
  omega

private theorem scaleIndex_surj {p : ℕ} (hp : p.Prime) {i : ℕ} (hi : p ∣ size i) :
    ∃ j, scaleIndex hp j = i := by
  obtain ⟨b, hb⟩ := hi
  have hpos : 0 < b := by
    by_contra! h
    have hz : b = 0 := by omega
    simp [hz, size] at hb
  refine ⟨b - 1, ?_⟩
  have he : size (b - 1) = b := by unfold size; omega
  have hs : size (scaleIndex hp (b - 1)) = size i := by
    rw [size_scale, he, hb]
  simpa [size] using hs

private theorem sum_map_scale {p : ℕ} (hp : p.Prime) (D : Finset ℕ) :
    (D.map (scaleIndex hp)).sum size = p * D.sum size := by
  rw [Finset.sum_map]
  simp only [size_scale, sum_scale]

private theorem multinomial_map (D : Finset ℕ) (e : ℕ ↪ ℕ) (f : ℕ → ℕ) :
    Nat.multinomial (D.map e) f = Nat.multinomial D (fun i => f (e i)) := by
  simp only [Nat.multinomial, Finset.sum_map, Finset.prod_map]

private theorem weight_map {p k m : ℕ} (hp : p.Prime) (hm : p ^ k ∣ m)
    (D : Finset ℕ) (hD : D ∈ subsets m) :
    (weight (D.map (scaleIndex hp)) : ZMod (p ^ (k + 1))) =
      (weight D : ZMod (p ^ (k + 1))) := by
  have hc := multinomial_scale hp k D size (by rwa [mem_subsets.mp hD])
  have hcz := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hc
  simp only [weight, Finset.card_map, multinomial_map, size_scale, Nat.cast_mul, hcz]

private theorem weight_zero {p k m : ℕ} (hp : p.Prime) (hm : p ^ k ∣ m)
    (D : Finset ℕ) (hD : D ∈ subsets m) (i : ℕ) (hi : i ∈ D) (hc : ¬ p ∣ size i) :
    (weight D : ZMod (p ^ k)) = 0 := by
  have hd : p ^ k ∣ Nat.multinomial D size :=
    multinomial_dvd hp D size (r := 0) (l := k) hi (by simp) hc
      (by simpa [mem_subsets.mp hD] using hm)
  rw [weight, Nat.cast_mul, (ZMod.natCast_eq_zero_iff _ _).mpr hd, mul_zero]

private theorem count_scale {p : ℕ} (hp : p.Prime) (k n : ℕ) :
    (count (n * p ^ (k + 1)) : ZMod (p ^ (k + 1))) =
      (count (n * p ^ k) : ZMod (p ^ (k + 1))) := by
  classical
  let m := n * p ^ k
  have hM : n * p ^ (k + 1) = p * m := by
    dsimp [m]
    rw [pow_succ]
    ac_rfl
  have hm : p ^ k ∣ m := dvd_mul_left _ _
  have hpM : p ^ (k + 1) ∣ p * m := by
    rw [pow_succ, mul_comm (p ^ k) p]
    exact mul_dvd_mul_left p hm
  let good : Finset ℕ → Prop := fun D => ∀ i ∈ D, p ∣ size i
  let S := (subsets (p * m)).filter good
  have hS : (∑ D ∈ S, (weight D : ZMod (p ^ (k + 1)))) =
      ∑ D ∈ subsets (p * m), (weight D : ZMod (p ^ (k + 1))) := by
    dsimp only [S]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro D hD
    by_cases hg : good D
    · rw [if_pos hg]
    · rw [if_neg hg]
      change ¬ (∀ i ∈ D, p ∣ size i) at hg
      push Not at hg
      obtain ⟨i, hi, hcop⟩ := hg
      exact (weight_zero hp hpM D hD i hi hcop).symm
  rw [hM]
  change (count (p * m) : ZMod (p ^ (k + 1))) = (count m : ZMod (p ^ (k + 1)))
  unfold count
  simp only [Nat.cast_sum]
  rw [← hS]
  symm
  refine Finset.sum_bij (fun D _ => D.map (scaleIndex hp)) ?_ ?_ ?_ ?_
  · intro D hD
    apply Finset.mem_filter.mpr
    refine ⟨mem_subsets.mpr ?_, ?_⟩
    · rw [sum_map_scale hp, mem_subsets.mp hD]
    · intro i hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
      rw [size_scale hp]
      exact dvd_mul_right _ _
  · intro D _ E _ h
    exact Finset.map_injective (scaleIndex hp) h
  · intro E hE
    obtain ⟨hE, hgood⟩ := Finset.mem_filter.mp hE
    let e := scaleIndex hp
    let D := E.preimage e e.injective.injOn
    have hmap : D.map e = E := by
      ext i
      constructor
      · intro hi
        obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
        exact Finset.mem_preimage.mp hj
      · intro hi
        obtain ⟨j, rfl⟩ := scaleIndex_surj hp (hgood i hi)
        exact Finset.mem_map_of_mem e (Finset.mem_preimage.mpr hi)
    refine ⟨D, mem_subsets.mpr ?_, hmap⟩
    apply (mul_right_inj' hp.ne_zero).mp
    rw [← sum_map_scale hp D, hmap]
    exact mem_subsets.mp hE
  · intro D hD
    exact (weight_map hp hm D hD).symm

end A032312Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a032312.main := by
  intro p n k hp _ hk
  cases k with
  | zero => omega
  | succ k =>
    have hZ := A032312Proof.count_scale hp k n
    have hD := (ZMod.natCast_eq_natCast_iff _ _ _).mp hZ.symm
    obtain ⟨z, hz⟩ := Nat.modEq_iff_dvd.mp hD
    refine ⟨z, ?_⟩
    change OMA.S_oeis_a032312.a (n * p ^ (k + 1)) -
      OMA.S_oeis_a032312.a (n * p ^ k) = (p : ℚ) ^ (k + 1) * z
    simp only [A032312Proof.a_eq_count]
    simpa only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Nat.cast_pow, Int.cast_pow] using
      congrArg (fun x : ℤ => (x : ℚ)) hz
