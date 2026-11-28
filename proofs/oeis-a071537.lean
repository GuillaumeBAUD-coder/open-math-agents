import OMAStatements.S_oeis_a071537

open Finset OMA.S_oeis_a071537

namespace OMA.A071537

/- Max Alekseyev's proof on the OEIS entry A071537 uses cancellation of endpoint
exponents and a relation formed from the prime factorization of each composite. -/

private def value (m : ℕ) (k : ℕ → ℤ) : ℚ := ∏ i ∈ Icc 1 m, (i : ℚ) ^ k i

private structure Rel (n m : ℕ) (k : ℕ → ℤ) : Prop where
  first : k n ≠ 0
  below : ∀ i < n, k i = 0
  above : ∀ i > m, k i = 0
  equation : value m k = 1

private theorem Rel.le {n m : ℕ} {k : ℕ → ℤ} (h : Rel n m k) : n ≤ m :=
  le_of_not_gt fun hn => h.first (h.above n hn)

private theorem valueLow {n m : ℕ} {k : ℕ → ℤ} (hn : 0 < n)
    (h : ∀ i < n, k i = 0) :
    value m k = ∏ i ∈ Icc n m, (i : ℚ) ^ k i := by
  symm
  apply prod_subset (Icc_subset_Icc hn le_rfl)
  intro i hi hin
  have hlt : i < n := by
    simp only [mem_Icc, not_and_or, not_le] at hi hin
    omega
  simp [h i hlt]

private theorem valueHigh {m M : ℕ} {k : ℕ → ℤ} (hm : m ≤ M)
    (h : ∀ i > m, k i = 0) : value M k = value m k := by
  symm
  apply prod_subset (Icc_subset_Icc le_rfl hm)
  intro i hi hin
  have hlt : m < i := by
    simp only [mem_Icc, not_and_or, not_le] at hi hin
    omega
  simp [h i hlt]

private theorem Rel.original {n m : ℕ} {k : ℕ → ℤ} (hn : 0 < n) (h : Rel n m k) :
    ProductRelation n m := ⟨h.le, k, h.first, (valueLow hn h.below).symm.trans h.equation⟩

private theorem rel_of_original {n m : ℕ} (hn : 0 < n) (h : ProductRelation n m) :
    ∃ k, Rel n m k := by
  obtain ⟨hnm, k, hk, hp⟩ := h
  let v (i : ℕ) := if n ≤ i ∧ i ≤ m then k i else 0
  have hlo (i : ℕ) (hi : i < n) : v i = 0 := by simp [v, not_le_of_gt hi]
  have hhi (i : ℕ) (hi : m < i) : v i = 0 := by simp [v, not_le_of_gt hi]
  refine ⟨v, by simpa [v, hnm] using hk, hlo, hhi, ?_⟩
  rw [valueLow hn hlo, ← hp]
  apply prod_congr rfl
  intro i hi
  simp [v, mem_Icc.mp hi]

private def single (i : ℕ) (t : ℤ) (j : ℕ) : ℤ := if j = i then t else 0

private theorem valueSingle {i m : ℕ} (hi : i ∈ Icc 1 m) (t : ℤ) :
    value m (single i t) = (i : ℚ) ^ t := by
  unfold value
  rw [prod_eq_single_of_mem i hi]
  · simp [single]
  · intro j _ hj
    simp [single, hj]

private theorem castNeZero {m i : ℕ} (hi : i ∈ Icc 1 m) : (i : ℚ) ≠ 0 := by
  exact_mod_cast (Nat.ne_of_gt (mem_Icc.mp hi).1)

private theorem valueAdd (m : ℕ) (k l : ℕ → ℤ) :
    value m (fun i => k i + l i) = value m k * value m l := by
  unfold value
  rw [← prod_mul_distrib]
  exact prod_congr rfl fun _ hi => zpow_add₀ (castNeZero hi) _ _

private theorem productPow {α : Type} (s : Finset α) (f : α → ℚ) (b : ℤ) :
    (∏ i ∈ s, f i ^ b) = (∏ i ∈ s, f i) ^ b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [prod_insert hi, ih, mul_zpow]

private theorem valueScale (m : ℕ) (k : ℕ → ℤ) (b : ℤ) :
    value m (fun i => b * k i) = (value m k) ^ b := by
  unfold value
  simp_rw [mul_comm b, zpow_mul]
  exact productPow _ _ _

private theorem combination {m : ℕ} {f g : ℕ → ℤ} (hf : value m f = 1)
    (hg : value m g = 1) (c d : ℤ) : value m (fun i => c * f i + d * g i) = 1 := by
  rw [valueAdd, valueScale, valueScale, hf, hg]
  simp

private theorem hasRel (n : ℕ) (hn : 0 < n) : ∃ m, ProductRelation n m := by
  by_cases h : n = 1
  · subst n
    exact ⟨1, le_rfl, fun _ => 1, by simp, by simp⟩
  let m := n * n
  have hnm : n < m := by
    calc
      n = n * 1 := by simp
      _ < n * n := Nat.mul_lt_mul_of_pos_left (by omega) hn
  let k (i : ℕ) := single n 2 i + single m (-1) i
  have hk : Rel n m k := by
    refine ⟨by simp [k, single, hnm.ne], ?_, ?_, ?_⟩
    · intro i hi
      simp [k, single, (hi.trans hnm).ne, hi.ne]
    · intro i hi
      simp [k, single, (hnm.trans hi).ne', hi.ne']
    · rw [valueAdd, valueSingle (mem_Icc.mpr ⟨hn, hnm.le⟩),
        valueSingle (mem_Icc.mpr ⟨hn.trans hnm, le_rfl⟩)]
      norm_num [m, pow_two]
      field_simp
  exact ⟨m, hk.original hn⟩

private theorem minRel (n : ℕ) (hn : 0 < n) : ∃ k, Rel n (a n) k := by
  have hs : ({m | ProductRelation n m} : Set ℕ).Nonempty := hasRel n hn
  exact rel_of_original hn (Nat.sInf_mem hs)

private theorem minLe {n m : ℕ} {k : ℕ → ℤ} (hn : 0 < n) (h : Rel n m k) : a n ≤ m :=
  Nat.sInf_le (h.original hn)

private theorem lastNonzero {n : ℕ} {k : ℕ → ℤ} (hn : 0 < n) (h : Rel n (a n) k) :
    k (a n) ≠ 0 := by
  intro hz
  have hlt : n < a n := lt_of_le_of_ne h.le (fun he => h.first (he ▸ hz))
  have hcut (i : ℕ) (hi : a n - 1 < i) : k i = 0 := by
    by_cases e : i = a n
    · rwa [e]
    · exact h.above i (by omega)
  have hrel : Rel n (a n - 1) k :=
    ⟨h.first, h.below, hcut,
      (valueHigh (Nat.sub_le _ _) hcut).symm.trans h.equation⟩
  have hmin := minLe hn hrel
  omega

private theorem vpProd {p : ℕ} [Fact p.Prime] {α : Type} (s : Finset α) (f : α → ℚ)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValRat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValRat p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have hn : ∀ j ∈ s, f j ≠ 0 := fun j hj => hf j (mem_insert_of_mem hj)
    rw [prod_insert hi, sum_insert hi,
      padicValRat.mul (hf i (mem_insert_self _ _)) (prod_ne_zero_iff.mpr hn), ih hn]

private theorem target (n : ℕ) (hn : 0 < n) : 0 < a n ∧ ¬ (a n).Prime := by
  obtain ⟨k, hk⟩ := minRel n hn
  refine ⟨hn.trans_le hk.le, ?_⟩
  intro hp
  let m := a n
  let : Fact m.Prime := ⟨hp⟩
  have hsum : (∑ i ∈ Icc 1 m, padicValRat m ((i : ℚ) ^ k i)) = 0 := by
    rw [← vpProd _ _ (fun i hi => zpow_ne_zero _ (castNeZero hi))]
    change padicValRat m (value m k) = 0
    rw [hk.equation, padicValRat.one]
  rw [sum_eq_single_of_mem m (mem_Icc.mpr ⟨hp.pos, le_rfl⟩)] at hsum
  · simp at hsum
    exact lastNonzero hn hk hsum
  · intro i hi hne
    obtain ⟨hi₁, hi₂⟩ := mem_Icc.mp hi
    have hlt : i < m := lt_of_le_of_ne hi₂ hne
    have hnd : ¬ m ∣ i := fun hd => (not_le_of_gt hlt) (Nat.le_of_dvd hi₁ hd)
    simp [padicValNat.eq_zero_of_not_dvd hnd]

private theorem injectiveOn : Set.InjOn a {n : ℕ | 0 < n} := by
  intro n hn j hj hij
  suffices lower : ∀ {n j : ℕ}, 0 < n → 0 < j → n < j → a n ≠ a j by
    rcases lt_trichotomy n j with h | h | h
    · exact False.elim ((lower hn hj h) hij)
    · exact h
    · exact False.elim ((lower hj hn h) hij.symm)
  intro r s hr hs hrs eq
  obtain ⟨f, hf⟩ := minRel r hr
  obtain ⟨g, hg⟩ := minRel s hs
  have hlast := lastNonzero hs hg
  rw [← eq] at hg hlast
  let m := a r
  change g m ≠ 0 at hlast
  have hrm : r < m := hrs.trans_le hg.le
  let k (i : ℕ) := g m * f i + (-f m) * g i
  have hkm : k m = 0 := by dsimp [k]; ring
  have hka : ∀ i > m - 1, k i = 0 := by
    intro i hi
    by_cases e : i = m
    · simpa [e] using hkm
    · have hmi : m < i := by omega
      simp [k, hf.above i hmi, hg.above i hmi]
  have hk : Rel r (m - 1) k := by
    refine ⟨?_, ?_, hka, ?_⟩
    · simp [k, hg.below r hrs, hlast, hf.first]
    · intro i hi
      simp [k, hf.below i hi, hg.below i (hi.trans hrs)]
    · rw [← valueHigh (Nat.sub_le m 1) hka]
      exact combination hf.equation hg.equation _ _
  have h := minLe hr hk
  change m ≤ m - 1 at h
  omega

private theorem factorValue (m : ℕ) (hm : 0 < m) :
    value m (fun i => (m.factorization i : ℤ)) = (m : ℚ) := by
  have hsub : m.factorization.support ⊆ Icc 1 m := by
    intro i hi
    have hip : i ∈ m.primeFactors := by simpa using hi
    exact mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactors hip).pos,
      Nat.le_of_dvd hm (Nat.dvd_of_mem_primeFactors hip)⟩
  have h : (∏ i ∈ Icc 1 m, i ^ m.factorization i) = m := by
    calc
      _ = m.factorization.prod (· ^ ·) := by
        symm
        apply prod_subset hsub
        intro i _ hi
        simp [Finsupp.notMem_support_iff.mp hi]
      _ = m := Nat.prod_factorization_pow_eq_self hm.ne'
  simpa only [value, zpow_natCast, Nat.cast_prod, Nat.cast_pow] using
    congrArg (fun j : ℕ => (j : ℚ)) h

private theorem compositeRel (m : ℕ) (hm : 0 < m) (hnp : ¬ m.Prime) :
    ∃ n k, 0 < n ∧ Rel n m k ∧ k m ≠ 0 := by
  by_cases e : m = 1
  · subst m
    refine ⟨1, single 1 1, by decide, ⟨by simp [single], ?_, ?_, ?_⟩, by simp [single]⟩
    · intro i hi
      simp [single, hi.ne]
    · intro i hi
      simp [single, hi.ne']
    · rw [valueSingle (by simp)]
      norm_num
  let n := m.minFac
  have hnp' : n.Prime := Nat.minFac_prime e
  have hd : n ∣ m := Nat.minFac_dvd m
  have hnm : n < m := lt_of_le_of_ne (Nat.le_of_dvd hm hd) (fun h => hnp (h ▸ hnp'))
  let k (i : ℕ) := (m.factorization i : ℤ) + single m (-1) i
  refine ⟨n, k, hnp'.pos, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simp [k, single, hnm.ne, (hnp'.factorization_pos_of_dvd hm.ne' hd).ne']
  · intro i hi
    have hz : m.factorization i = 0 := by
      by_contra h
      have hmem : i ∈ m.factorization.support := Finsupp.mem_support_iff.mpr h
      have hp : i ∈ m.primeFactors := by simpa using hmem
      exact (not_le_of_gt hi) (Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactors hp).two_le
        (Nat.dvd_of_mem_primeFactors hp))
    simp [k, single, hz, (hi.trans hnm).ne]
  · intro i hi
    have hnd : ¬ i ∣ m := fun hd => (not_le_of_gt hi) (Nat.le_of_dvd hm hd)
    simp [k, single, hi.ne', Nat.factorization_eq_zero_of_not_dvd hnd]
  · rw [valueAdd, factorValue m hm, valueSingle (mem_Icc.mpr ⟨hm, le_rfl⟩)]
    simp [(show (m : ℚ) ≠ 0 by exact_mod_cast hm.ne')]
  · simp [k, single, Nat.factorization_eq_zero_of_not_prime m hnp]

private theorem surjectiveOn : Set.SurjOn a {n : ℕ | 0 < n} {m : ℕ | 0 < m ∧ ¬ m.Prime} := by
  classical
  intro m hm
  obtain ⟨hp, hnp⟩ := hm
  let S := (Icc 1 m).filter fun n => ∃ k, Rel n m k ∧ k m ≠ 0
  obtain ⟨j, k, hj, hk, hlast⟩ := compositeRel m hp hnp
  have hS : S.Nonempty := ⟨j, mem_filter.mpr ⟨mem_Icc.mpr ⟨hj, hk.le⟩, k, hk, hlast⟩⟩
  let n := S.max' hS
  obtain ⟨hnI, f, hf, hfm⟩ := mem_filter.mp (max'_mem S hS)
  change Rel n m f at hf
  have hn : 0 < n := (mem_Icc.mp hnI).1
  refine ⟨n, hn, le_antisymm (minLe hn hf) (le_of_not_gt ?_)⟩
  intro hlt
  obtain ⟨g, hg⟩ := minRel n hn
  let k (i : ℕ) := g n * f i + (-f n) * g i
  have hkn : k n = 0 := by dsimp [k]; ring
  have hka (i : ℕ) (hi : m < i) : k i = 0 := by
    simp [k, hf.above i hi, hg.above i (hlt.trans hi)]
  have hkm : k m ≠ 0 := by
    simp [k, hg.above m hlt, hg.first, hfm]
  have he : value m k = 1 := combination hf.equation
    ((valueHigh hlt.le hg.above).trans hg.equation) _ _
  let T := (Icc 1 m).filter fun i => k i ≠ 0
  have hT : T.Nonempty := ⟨m, mem_filter.mpr ⟨mem_Icc.mpr ⟨hp, le_rfl⟩, hkm⟩⟩
  let t := T.min' hT
  obtain ⟨htI, htk⟩ := mem_filter.mp (min'_mem T hT)
  change t ∈ Icc 1 m at htI
  change k t ≠ 0 at htk
  have hnt : n < t := by
    by_contra! h
    rcases lt_or_eq_of_le h with h | h
    · exact htk (by simp [k, hf.below t h, hg.below t h])
    · exact htk (by simpa [h] using hkn)
  have hkb (i : ℕ) (hi : i < t) : k i = 0 := by
    by_cases hi0 : i = 0
    · subst i
      simp [k, hf.below 0 hn, hg.below 0 hn]
    · by_contra hkne
      have hit : i ∈ T := mem_filter.mpr
        ⟨mem_Icc.mpr ⟨Nat.pos_of_ne_zero hi0, hi.le.trans (mem_Icc.mp htI).2⟩, hkne⟩
      exact (not_le_of_gt hi) (min'_le T i hit)
  have htS : t ∈ S := mem_filter.mpr ⟨htI, k, ⟨htk, hkb, hka, he⟩, hkm⟩
  exact (not_le_of_gt hnt) (le_max' S t htS)

end OMA.A071537

theorem OMA.solution : type_of% @OMA.S_oeis_a071537.main :=
  ⟨fun n hn => OMA.A071537.target n hn, OMA.A071537.injectiveOn, OMA.A071537.surjectiveOn⟩
