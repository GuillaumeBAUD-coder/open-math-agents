import FormalConjectures.ErdosProblems.«1026»

/-!
# Proof of Erdős Problem 1026 (Lower Bound)

We prove `1 / Real.sqrt 2 ∈ admissibleConstants` by establishing the stronger weighted
Erdős–Szekeres bound: for any injective positive `x : Fin n → ℝ`, letting `A i` and `B i` be the
maximum sums of monotone and antitone subsequences ending at `i` and `M = max (max A, max B)`, the
rectangles `(A i - x i, A i] × (B i - x i, B i] ⊆ (0, M]²` are pairwise disjoint, giving
`∑ i, x i ^ 2 ≤ M ^ 2` and hence `(1 / √n) * ∑ i, x i ≤ M` by Cauchy–Schwarz. Since
`1 / √2 ≤ 1`, `1 / √2 ∈ admissibleConstants` follows immediately.
-/

-- Problem: Erdős Problem 1026 — lower bound
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1026.lean:109 (declaration Erdos1026.erdos_1026.variants.lower_bound)
-- Credit: @TheWaler (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace Erdos1026LowerBoundProof

open Erdos1026 Filter MeasureTheory

private lemma weighted_erdos_szekeres_exact {n : ℕ} (x : Fin n → ℝ)
    (hx : Function.Injective x) (hx_pos : ∀ i, 0 < x i) :
    ∃ S ∈ monotonicSubsequenceSums x, (1 / Real.sqrt (n : ℝ)) * (∑ i, x i) ≤ S := by
  classical
  by_cases hn : n = 0
  · subst hn
    refine ⟨0, ⟨∅, Or.inl (fun a => a.elim0), by simp⟩, by simp⟩
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
  have : Nonempty (Fin n) := ⟨⟨0, hn_pos⟩⟩
  let incSets : Fin n → Finset (Finset (Fin n)) := fun i =>
    Finset.univ.filter (fun I => i ∈ I ∧ (∀ k ∈ I, k ≤ i) ∧ MonotoneOn x ↑I)
  let decSets : Fin n → Finset (Finset (Fin n)) := fun i =>
    Finset.univ.filter (fun I => i ∈ I ∧ (∀ k ∈ I, k ≤ i) ∧ AntitoneOn x ↑I)
  have hinc_mem_sing : ∀ i : Fin n, ({i} : Finset (Fin n)) ∈ incSets i := by
    intro i
    simp only [incSets, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      forall_eq, le_refl, Finset.coe_singleton]
    exact fun a ha b hb _ => by simp_all
  have hdec_mem_sing : ∀ i : Fin n, ({i} : Finset (Fin n)) ∈ decSets i := by
    intro i
    simp only [decSets, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      forall_eq, le_refl, Finset.coe_singleton]
    exact fun a ha b hb _ => by simp_all
  have hinc_ne : ∀ i : Fin n, ((incSets i).image (fun I => ∑ k ∈ I, x k)).Nonempty :=
    fun i => ⟨x i, Finset.mem_image.mpr ⟨{i}, hinc_mem_sing i, by simp⟩⟩
  have hdec_ne : ∀ i : Fin n, ((decSets i).image (fun I => ∑ k ∈ I, x k)).Nonempty :=
    fun i => ⟨x i, Finset.mem_image.mpr ⟨{i}, hdec_mem_sing i, by simp⟩⟩
  let A : Fin n → ℝ := fun i => ((incSets i).image (fun I => ∑ k ∈ I, x k)).max' (hinc_ne i)
  let B : Fin n → ℝ := fun i => ((decSets i).image (fun I => ∑ k ∈ I, x k)).max' (hdec_ne i)
  have hA_mem : ∀ i : Fin n, A i ∈ monotonicSubsequenceSums x := by
    intro i
    rcases Finset.mem_image.mp (Finset.max'_mem _ (hinc_ne i)) with ⟨I, hI, hsum⟩
    have hI' := (Finset.mem_filter.mp hI).2
    exact ⟨I, Or.inl hI'.2.2, hsum⟩
  have hB_mem : ∀ i : Fin n, B i ∈ monotonicSubsequenceSums x := by
    intro i
    rcases Finset.mem_image.mp (Finset.max'_mem _ (hdec_ne i)) with ⟨I, hI, hsum⟩
    have hI' := (Finset.mem_filter.mp hI).2
    exact ⟨I, Or.inr hI'.2.2, hsum⟩
  have hx_le_A : ∀ i : Fin n, x i ≤ A i := fun i =>
    Finset.le_max' _ _ (Finset.mem_image.mpr ⟨{i}, hinc_mem_sing i, by simp⟩)
  have hx_le_B : ∀ i : Fin n, x i ≤ B i := fun i =>
    Finset.le_max' _ _ (Finset.mem_image.mpr ⟨{i}, hdec_mem_sing i, by simp⟩)
  have hA_step : ∀ {i j : Fin n}, i < j → x i < x j → A i ≤ A j - x j := by
    intro i j hij hxij
    rcases Finset.mem_image.mp (Finset.max'_mem _ (hinc_ne i)) with ⟨I, hI, hsum⟩
    rcases (Finset.mem_filter.mp hI).2 with ⟨hiI, hIle, hImono⟩
    have hj_not : j ∉ I := fun hjI => not_lt_of_ge (hIle j hjI) hij
    have hI'_mem : insert j I ∈ incSets j := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_insert_self j I, ?_, ?_⟩
      · intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hkI
        · exact le_rfl
        · exact le_trans (hIle k hkI) hij.le
      · intro a ha b hb hab
        simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at ha hb
        rcases ha with rfl | haI <;> rcases hb with rfl | hbI
        · exact le_rfl
        · exact absurd (lt_of_le_of_lt (hIle b hbI) hij) (not_lt_of_ge hab)
        · exact le_trans (hImono haI hiI (hIle a haI)) hxij.le
        · exact hImono haI hbI hab
    have hsum' : ∑ k ∈ insert j I, x k = A i + x j := by
      rw [Finset.sum_insert hj_not, hsum, add_comm]
    have hle : A i + x j ≤ A j := by
      rw [← hsum']
      exact Finset.le_max' ((incSets j).image (fun J => ∑ k ∈ J, x k)) _
        (Finset.mem_image.mpr ⟨insert j I, hI'_mem, rfl⟩)
    linarith
  have hB_step : ∀ {i j : Fin n}, i < j → x j < x i → B i ≤ B j - x j := by
    intro i j hij hxji
    rcases Finset.mem_image.mp (Finset.max'_mem _ (hdec_ne i)) with ⟨I, hI, hsum⟩
    rcases (Finset.mem_filter.mp hI).2 with ⟨hiI, hIle, hIanti⟩
    have hj_not : j ∉ I := fun hjI => not_lt_of_ge (hIle j hjI) hij
    have hI'_mem : insert j I ∈ decSets j := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_insert_self j I, ?_, ?_⟩
      · intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hkI
        · exact le_rfl
        · exact le_trans (hIle k hkI) hij.le
      · intro a ha b hb hab
        simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at ha hb
        rcases ha with rfl | haI <;> rcases hb with rfl | hbI
        · exact le_rfl
        · exact absurd (lt_of_le_of_lt (hIle b hbI) hij) (not_lt_of_ge hab)
        · exact le_trans hxji.le (hIanti haI hiI (hIle a haI))
        · exact hIanti haI hbI hab
    have hsum' : ∑ k ∈ insert j I, x k = B i + x j := by
      rw [Finset.sum_insert hj_not, hsum, add_comm]
    have hle : B i + x j ≤ B j := by
      rw [← hsum']
      exact Finset.le_max' ((decSets j).image (fun J => ∑ k ∈ J, x k)) _
        (Finset.mem_image.mpr ⟨insert j I, hI'_mem, rfl⟩)
    linarith
  have huniv_ne : (Finset.univ : Finset (Fin n)).Nonempty := Finset.univ_nonempty
  let M_A : ℝ := (Finset.univ.image A).max' (huniv_ne.image A)
  let M_B : ℝ := (Finset.univ.image B).max' (huniv_ne.image B)
  let M : ℝ := max M_A M_B
  have hA_le_M : ∀ i : Fin n, A i ≤ M := fun i =>
    le_trans (Finset.le_max' _ _ (Finset.mem_image_of_mem A (Finset.mem_univ i))) (le_max_left _ _)
  have hB_le_M : ∀ i : Fin n, B i ≤ M := fun i =>
    le_trans (Finset.le_max' _ _ (Finset.mem_image_of_mem B (Finset.mem_univ i))) (le_max_right _ _)
  have hM_nonneg : 0 ≤ M := by
    let i0 : Fin n := ⟨0, hn_pos⟩
    linarith [hx_pos i0, hx_le_A i0, hA_le_M i0]
  have hM_mem : M ∈ monotonicSubsequenceSums x := by
    rcases max_choice M_A M_B with h | h
    · rw [show M = M_A from h]
      rcases Finset.mem_image.mp (Finset.max'_mem _ (huniv_ne.image A)) with ⟨i, _, hi⟩
      have hMA : M_A = A i := hi.symm
      rw [hMA]
      exact hA_mem i
    · rw [show M = M_B from h]
      rcases Finset.mem_image.mp (Finset.max'_mem _ (huniv_ne.image B)) with ⟨i, _, hi⟩
      have hMB : M_B = B i := hi.symm
      rw [hMB]
      exact hB_mem i
  let R : Fin n → Set (ℝ × ℝ) := fun i =>
    Set.Ioc (A i - x i) (A i) ×ˢ Set.Ioc (B i - x i) (B i)
  have hR_meas : ∀ i ∈ (Finset.univ : Finset (Fin n)), MeasurableSet (R i) :=
    fun _ _ => measurableSet_Ioc.prod measurableSet_Ioc
  have hR_sub : (⋃ i ∈ (Finset.univ : Finset (Fin n)), R i) ⊆ Set.Ioc 0 M ×ˢ Set.Ioc 0 M := by
    intro p hp
    simp only [Set.mem_iUnion, Finset.mem_univ, exists_prop, true_and] at hp
    rcases hp with ⟨i, ⟨hu1, hu2⟩, ⟨hv1, hv2⟩⟩
    exact ⟨⟨by linarith [hx_le_A i], le_trans hu2 (hA_le_M i)⟩,
      ⟨by linarith [hx_le_B i], le_trans hv2 (hB_le_M i)⟩⟩
  have hR_disj : ((Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint R := by
    intro i _ j _ hij
    have haux : ∀ {a b : Fin n}, a < b → Disjoint (R a) (R b) := by
      intro a b hab
      refine Set.disjoint_left.mpr ?_
      intro p hpa hpb
      rcases lt_or_gt_of_ne (fun h => hab.ne (hx h)) with hxlt | hxgt
      · have hstep := hA_step hab hxlt
        linarith [hpa.1.2, hpb.1.1]
      · have hstep := hB_step hab hxgt
        linarith [hpa.2.2, hpb.2.1]
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact haux hlt
    · exact (haux hgt).symm
  have hR_vol : ∀ i : Fin n, volume (R i) = ENNReal.ofReal (x i ^ 2) := by
    intro i
    change volume (Set.Ioc (A i - x i) (A i) ×ˢ Set.Ioc (B i - x i) (B i)) = ENNReal.ofReal (x i ^ 2)
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioc, Real.volume_Ioc,
      sub_sub_cancel, sub_sub_cancel, ← ENNReal.ofReal_mul (hx_pos i).le, sq]
  have hbox_vol : volume (Set.Ioc 0 M ×ˢ Set.Ioc 0 M) = ENNReal.ofReal (M ^ 2) := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioc,
      sub_zero, ← ENNReal.ofReal_mul hM_nonneg, sq]
  have hvol_le : ∑ i : Fin n, ENNReal.ofReal (x i ^ 2) ≤ ENNReal.ofReal (M ^ 2) := by
    calc
      ∑ i : Fin n, ENNReal.ofReal (x i ^ 2) = ∑ i ∈ Finset.univ, volume (R i) := by
        simp [hR_vol]
      _ = volume (⋃ i ∈ (Finset.univ : Finset (Fin n)), R i) :=
        (measure_biUnion_finset hR_disj hR_meas).symm
      _ ≤ volume (Set.Ioc 0 M ×ˢ Set.Ioc 0 M) := measure_mono hR_sub
      _ = ENNReal.ofReal (M ^ 2) := hbox_vol
  have hsum_sq_le : ∑ i : Fin n, x i ^ 2 ≤ M ^ 2 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg (x i))] at hvol_le
    exact (ENNReal.ofReal_le_ofReal_iff (sq_nonneg M)).mp hvol_le
  have hcs : (∑ i : Fin n, x i) ^ 2 ≤ (n : ℝ) * ∑ i : Fin n, x i ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n))) (f := x)
  have hsq_bound : (∑ i : Fin n, x i) ^ 2 ≤ (Real.sqrt (n : ℝ) * M) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    exact le_trans hcs (mul_le_mul_of_nonneg_left hsum_sq_le (Nat.cast_nonneg n))
  have hsum_nonneg : 0 ≤ ∑ i : Fin n, x i := Finset.sum_nonneg fun i _ => (hx_pos i).le
  have hrhs_nonneg : 0 ≤ Real.sqrt (n : ℝ) * M := mul_nonneg (Real.sqrt_nonneg _) hM_nonneg
  have hlin : ∑ i : Fin n, x i ≤ Real.sqrt (n : ℝ) * M := by
    nlinarith
  have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn_pos)
  refine ⟨M, hM_mem, ?_⟩
  rw [one_div, inv_mul_eq_div, div_le_iff₀ hsqrt_pos]
  linarith

private lemma inv_sqrt_two_mem_admissibleConstants :
    1 / Real.sqrt 2 ∈ admissibleConstants := by
  intro ε hε
  refine Filter.Eventually.of_forall ?_
  intro n x hx hx_pos
  rcases weighted_erdos_szekeres_exact x hx hx_pos with ⟨S, hS, hle⟩
  refine ⟨S, hS, le_trans ?_ hle⟩
  have hsum_nonneg : 0 ≤ ∑ i, x i := Finset.sum_nonneg fun i _ => (hx_pos i).le
  have hsqrt2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hinv_le : 1 / Real.sqrt 2 ≤ 1 := by
    rw [div_le_one (by linarith)]
    exact hsqrt2
  have hdiv_le : (1 / Real.sqrt 2 - ε) / Real.sqrt (n : ℝ) ≤ 1 / Real.sqrt (n : ℝ) :=
    div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
  exact mul_le_mul_of_nonneg_right hdiv_le hsum_nonneg

end Erdos1026LowerBoundProof

theorem OMA.solution : type_of% @Erdos1026.erdos_1026.variants.lower_bound :=
  Erdos1026LowerBoundProof.inv_sqrt_two_mem_admissibleConstants
