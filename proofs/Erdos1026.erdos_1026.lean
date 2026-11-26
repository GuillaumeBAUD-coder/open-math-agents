import FormalConjectures.ErdosProblems.«1026»

/-!
# Proof of Erdős Problem 1026

We prove `IsGreatest admissibleConstants 1`:
1. (`1 ∈ admissibleConstants`): For any injective positive `x : Fin n → ℝ`, let `A i` and `B i` be
   the maximum sums of monotone and antitone subsequences ending at `i`, and `M = max (max A, max B)`.
   The rectangles `(A i - x i, A i] × (B i - x i, B i] ⊆ (0, M]²` are pairwise disjoint, so
   `∑ i, x i ^ 2 ≤ M ^ 2`. By Cauchy–Schwarz, `(1 / √n) * ∑ i, x i ≤ M`.
2. (`1 ∈ upperBounds admissibleConstants`): For any `c > 1`, taking `n = k ^ 2` with `k` decreasing
   blocks of size `k` and values `1 + η * key i ∈ [1, 1 + δ / 2]` forces every monotonic
   subsequence to have at most `k` terms and sum at most `k * (1 + δ / 2) < (1 + δ) * k`.
-/

-- Problem: Erdős Problem 1026
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1026.lean:94 (declaration Erdos1026.erdos_1026)
-- Credit: @TheWaler (the owner of the agent is credited as the solver)

namespace Erdos1026Proof

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

private lemma one_mem_admissibleConstants : (1 : ℝ) ∈ admissibleConstants := by
  intro ε hε
  refine Filter.Eventually.of_forall ?_
  intro n x hx hx_pos
  rcases weighted_erdos_szekeres_exact x hx hx_pos with ⟨S, hS, hle⟩
  refine ⟨S, hS, le_trans ?_ hle⟩
  have hsum_nonneg : 0 ≤ ∑ i, x i := Finset.sum_nonneg fun i _ => (hx_pos i).le
  have hdiv_le : (1 - ε) / Real.sqrt (n : ℝ) ≤ 1 / Real.sqrt (n : ℝ) :=
    div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
  exact mul_le_mul_of_nonneg_right hdiv_le hsum_nonneg

private lemma one_mem_upperBounds_admissibleConstants :
    (1 : ℝ) ∈ upperBounds admissibleConstants := by
  intro c hc
  by_contra hlt
  have hlt' : 1 < c := lt_of_not_ge hlt
  set δ : ℝ := (c - 1) / 2
  have hδ : 0 < δ := by
    dsimp only [δ]
    linarith
  have hev := hc δ hδ
  rw [Filter.eventually_atTop] at hev
  rcases hev with ⟨N0, hN0⟩
  set k : ℕ := N0 + 1
  have hk_pos : 0 < k := Nat.succ_pos N0
  have hk2_ge : N0 ≤ k ^ 2 := by
    dsimp only [k]
    nlinarith
  have hk_real_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk_pos
  have hk2_real_pos : (0 : ℝ) < (k ^ 2 : ℝ) := by positivity
  let key : Fin (k ^ 2) → ℕ := fun i => k * (i.val / k) + (k - 1 - i.val % k)
  have hkey_lt : ∀ i : Fin (k ^ 2), key i < k ^ 2 := by
    intro i
    have hq : i.val / k < k := Nat.div_lt_of_lt_mul (by simpa [sq] using i.isLt)
    have hr : k - 1 - i.val % k < k := by omega
    have hmul : k * (i.val / k + 1) ≤ k * k := Nat.mul_le_mul_left k hq
    dsimp only [key]
    nlinarith
  have hkey_inj : Function.Injective key := by
    intro i j hij
    dsimp only [key] at hij
    have hri : i.val % k < k := Nat.mod_lt _ hk_pos
    have hrj : j.val % k < k := Nat.mod_lt _ hk_pos
    have hri' : k - 1 - i.val % k < k := by omega
    have hrj' : k - 1 - j.val % k < k := by omega
    have h1 : (k * (i.val / k) + (k - 1 - i.val % k)) / k = i.val / k := by
      rw [Nat.mul_add_div hk_pos, Nat.div_eq_of_lt hri', add_zero]
    have h2 : (k * (j.val / k) + (k - 1 - j.val % k)) / k = j.val / k := by
      rw [Nat.mul_add_div hk_pos, Nat.div_eq_of_lt hrj', add_zero]
    have hq : i.val / k = j.val / k := by rw [← h1, hij, h2]
    rw [hq] at hij
    have hr : i.val % k = j.val % k := by omega
    apply Fin.ext
    rw [← Nat.div_add_mod i.val k, ← Nat.div_add_mod j.val k, hq, hr]
  have hkey_same_block : ∀ {i j : Fin (k ^ 2)}, i < j → i.val / k = j.val / k → key j < key i := by
    intro i j hij hq
    have hri : i.val % k < k := Nat.mod_lt _ hk_pos
    have hrj : j.val % k < k := Nat.mod_lt _ hk_pos
    have hi_eq : k * (i.val / k) + i.val % k = i.val := Nat.div_add_mod i.val k
    have hj_eq : k * (j.val / k) + j.val % k = j.val := Nat.div_add_mod j.val k
    have hij_val : i.val < j.val := hij
    rw [hq] at hi_eq
    have hrm : i.val % k < j.val % k := by omega
    dsimp only [key]
    rw [hq]
    omega
  have hkey_diff_block : ∀ {i j : Fin (k ^ 2)}, i.val / k < j.val / k → key i < key j := by
    intro i j hq
    have hri' : k - 1 - i.val % k < k := by omega
    have hmul : k * (i.val / k + 1) ≤ k * (j.val / k) := Nat.mul_le_mul_left k hq
    dsimp only [key]
    nlinarith
  set η : ℝ := δ / (2 * (k ^ 2 : ℝ))
  have hη : 0 < η := by positivity
  let x : Fin (k ^ 2) → ℝ := fun i => 1 + η * (key i : ℝ)
  have hx_inj : Function.Injective x := by
    intro i j hij
    dsimp only [x] at hij
    have hcast : (key i : ℝ) = (key j : ℝ) := by
      have : η * (key i : ℝ) = η * (key j : ℝ) := by linarith
      exact mul_left_cancel₀ hη.ne' this
    exact hkey_inj (Nat.cast_injective hcast)
  have hx_ge_one : ∀ i : Fin (k ^ 2), 1 ≤ x i := by
    intro i
    dsimp only [x]
    have : 0 ≤ η * (key i : ℝ) := mul_nonneg hη.le (Nat.cast_nonneg _)
    linarith
  have hx_pos : ∀ i : Fin (k ^ 2), 0 < x i := fun i => by linarith [hx_ge_one i]
  have hx_le : ∀ i : Fin (k ^ 2), x i ≤ 1 + δ / 2 := by
    intro i
    dsimp only [x]
    have hki : (key i : ℝ) ≤ (k ^ 2 : ℝ) := by
      exact_mod_cast (hkey_lt i).le
    have hprod : η * (key i : ℝ) ≤ η * (k ^ 2 : ℝ) := mul_le_mul_of_nonneg_left hki hη.le
    have hηk : η * (k ^ 2 : ℝ) = δ / 2 := by
      dsimp only [η]
      field_simp
    linarith
  rcases hN0 (k ^ 2) hk2_ge x hx_inj hx_pos with ⟨S, ⟨I, hmono, hS_eq⟩, hS_ge⟩
  have hI_card : I.card ≤ k := by
    rcases hmono with hinc | hdec
    · have hinj : Set.InjOn (fun i : Fin (k ^ 2) => i.val / k) ↑I := by
        intro i hi j hj hq
        dsimp only at hq
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt_ij | hgt_ij
        · have hkey_gt : key j < key i := hkey_same_block hlt_ij hq
          have hx_le_ij : x i ≤ x j := hinc hi hj hlt_ij.le
          have hkey_le : (key i : ℝ) ≤ (key j : ℝ) := by
            dsimp only [x] at hx_le_ij
            nlinarith
          have : key i ≤ key j := Nat.cast_le.mp hkey_le
          omega
        · have hkey_gt : key i < key j := hkey_same_block hgt_ij hq.symm
          have hx_le_ji : x j ≤ x i := hinc hj hi hgt_ij.le
          have hkey_le : (key j : ℝ) ≤ (key i : ℝ) := by
            dsimp only [x] at hx_le_ji
            nlinarith
          have : key j ≤ key i := Nat.cast_le.mp hkey_le
          omega
      have hsub : I.image (fun i : Fin (k ^ 2) => i.val / k) ⊆ Finset.range k := by
        intro q hq
        rcases Finset.mem_image.mp hq with ⟨i, _, rfl⟩
        exact Finset.mem_range.mpr (Nat.div_lt_of_lt_mul (by simpa [sq] using i.isLt))
      calc
        I.card = (I.image (fun i : Fin (k ^ 2) => i.val / k)).card :=
          (Finset.card_image_of_injOn hinj).symm
        _ ≤ (Finset.range k).card := Finset.card_le_card hsub
        _ = k := Finset.card_range k
    · have hinj : Set.InjOn (fun i : Fin (k ^ 2) => i.val % k) ↑I := by
        intro i hi j hj hrm
        dsimp only at hrm
        by_contra hne
        have hq_eq : i.val / k = j.val / k := by
          rcases lt_or_gt_of_ne hne with hlt_ij | hgt_ij
          · have hq_le : i.val / k ≤ j.val / k := Nat.div_le_div_right hlt_ij.le
            by_contra hq_ne
            have hq_lt : i.val / k < j.val / k := lt_of_le_of_ne hq_le hq_ne
            have hkey_lt' : key i < key j := hkey_diff_block hq_lt
            have hx_ge_ij : x j ≤ x i := hdec hi hj hlt_ij.le
            have hkey_ge : (key j : ℝ) ≤ (key i : ℝ) := by
              dsimp only [x] at hx_ge_ij
              nlinarith
            have : key j ≤ key i := Nat.cast_le.mp hkey_ge
            omega
          · have hq_le : j.val / k ≤ i.val / k := Nat.div_le_div_right hgt_ij.le
            by_contra hq_ne
            have hq_lt : j.val / k < i.val / k := lt_of_le_of_ne hq_le (Ne.symm hq_ne)
            have hkey_lt' : key j < key i := hkey_diff_block hq_lt
            have hx_ge_ji : x i ≤ x j := hdec hj hi hgt_ij.le
            have hkey_ge : (key i : ℝ) ≤ (key j : ℝ) := by
              dsimp only [x] at hx_ge_ji
              nlinarith
            have : key i ≤ key j := Nat.cast_le.mp hkey_ge
            omega
        apply hne
        apply Fin.ext
        rw [← Nat.div_add_mod i.val k, ← Nat.div_add_mod j.val k, hq_eq, hrm]
      have hsub : I.image (fun i : Fin (k ^ 2) => i.val % k) ⊆ Finset.range k := by
        intro r hr
        rcases Finset.mem_image.mp hr with ⟨i, _, rfl⟩
        exact Finset.mem_range.mpr (Nat.mod_lt _ hk_pos)
      calc
        I.card = (I.image (fun i : Fin (k ^ 2) => i.val % k)).card :=
          (Finset.card_image_of_injOn hinj).symm
        _ ≤ (Finset.range k).card := Finset.card_le_card hsub
        _ = k := Finset.card_range k
  have hS_le : S ≤ (k : ℝ) * (1 + δ / 2) := by
    calc
      S = ∑ i ∈ I, x i := hS_eq.symm
      _ ≤ ∑ _i ∈ I, (1 + δ / 2) := Finset.sum_le_sum fun i _ => hx_le i
      _ = (I.card : ℝ) * (1 + δ / 2) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (k : ℝ) * (1 + δ / 2) :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hI_card) (by linarith)
  have hsum_ge : (k ^ 2 : ℝ) ≤ ∑ i : Fin (k ^ 2), x i := by
    calc
      (k ^ 2 : ℝ) = ∑ _i : Fin (k ^ 2), (1 : ℝ) := by simp
      _ ≤ ∑ i : Fin (k ^ 2), x i := Finset.sum_le_sum fun i _ => hx_ge_one i
  have hsqrt_eq : Real.sqrt ((k ^ 2 : ℕ) : ℝ) = (k : ℝ) := by
    rw [Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg k)]
  have hc_sub : c - δ = 1 + δ := by
    dsimp only [δ]
    ring
  have hS_lower : (k : ℝ) * (1 + δ) ≤ S := by
    rw [hsqrt_eq, hc_sub] at hS_ge
    have hmul : (1 + δ) / (k : ℝ) * (k ^ 2 : ℝ) ≤ (1 + δ) / (k : ℝ) * ∑ i : Fin (k ^ 2), x i :=
      mul_le_mul_of_nonneg_left hsum_ge (div_nonneg (by linarith) hk_real_pos.le)
    have hsimp : (1 + δ) / (k : ℝ) * (k ^ 2 : ℝ) = (k : ℝ) * (1 + δ) := by
      field_simp
    linarith
  nlinarith

end Erdos1026Proof

theorem OMA.solution : type_of% @Erdos1026.erdos_1026 :=
  ⟨Erdos1026Proof.one_mem_admissibleConstants,
    Erdos1026Proof.one_mem_upperBounds_admissibleConstants⟩
