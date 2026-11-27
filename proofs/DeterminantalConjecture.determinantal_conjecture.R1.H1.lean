import OMAReductions.R_DeterminantalConjecture_determinantal_conjecture_R1
import Mathlib

/-!
# Finite Two-Row Marginal Coupling for the Determinantal Conjecture

Given normalized signed permutation weights with nonnegative subset-incidence sums,
the unordered image marginals on any subset of size at most two match those of an
honest probability distribution on permutations.
-/

namespace DeterminantalH1Aux

lemma ind_cut_eq_sum {n : Type*} [Fintype n] [DecidableEq n]
    {a b : n} (hab : a ≠ b) {U : Finset n} (hU : U.Nonempty) (σ : Equiv.Perm n) :
    (if σ a ∈ U ∧ σ b ∉ U then (1 : ℝ) else 0) =
      ∑ K ∈ (Finset.univ \ ({a, b} : Finset n)).powersetCard (U.card - 1),
        if ∀ i ∈ insert a K, σ i ∈ U then (1 : ℝ) else 0 := by
  set rest : Finset n := Finset.univ \ ({a, b} : Finset n)
  by_cases hσa : σ a ∈ U
  · by_cases hσb : σ b ∈ U
    · simp only [hσa, hσb, not_true_eq_false, and_false, ↓reduceIte]
      symm
      apply Finset.sum_eq_zero
      intro K hK
      rw [if_neg]
      intro hall
      obtain ⟨hK_sub, hK_card⟩ := Finset.mem_powersetCard.mp hK
      have haK : a ∉ K := fun ha => (Finset.mem_sdiff.mp (hK_sub ha)).2 (by simp)
      have hb_ins : b ∉ insert a K := by
        intro hb
        rcases Finset.mem_insert.mp hb with hba | hbK
        · exact hab hba.symm
        · exact (Finset.mem_sdiff.mp (hK_sub hbK)).2 (by simp)
      let M : Finset n := insert b (insert a K)
      have hU_pos : 0 < U.card := hU.card_pos
      have hM_card : M.card = U.card + 1 := by
        rw [Finset.card_insert_of_notMem hb_ins, Finset.card_insert_of_notMem haK, hK_card]
        omega
      have hM_sub : M.image σ ⊆ U := by
        intro y hy
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
        rcases Finset.mem_insert.mp hi with rfl | hi'
        · exact hσb
        · exact hall i hi'
      have hle : M.card ≤ U.card := by
        rw [← Finset.card_image_of_injective M σ.injective]
        exact Finset.card_le_card hM_sub
      omega
    · simp only [hσa, hσb, not_false_eq_true, and_self, ↓reduceIte]
      let K₀ : Finset n := (U.image σ.symm).erase a
      have ha_pre : a ∈ U.image σ.symm :=
        Finset.mem_image.mpr ⟨σ a, hσa, σ.symm_apply_apply a⟩
      have hb_not_pre : b ∉ U.image σ.symm := by
        intro hb_pre
        obtain ⟨u, hu, hbu⟩ := Finset.mem_image.mp hb_pre
        apply hσb
        have hσbu : σ b = u := by rw [← hbu, σ.apply_symm_apply]
        exact hσbu ▸ hu
      have hK₀_card : K₀.card = U.card - 1 := by
        rw [Finset.card_erase_of_mem ha_pre, Finset.card_image_of_injective U σ.symm.injective]
      have hK₀_sub : K₀ ⊆ rest := by
        intro x hx
        obtain ⟨hxa, hx_pre⟩ := Finset.mem_erase.mp hx
        have hxb : x ≠ b := fun h => hb_not_pre (h ▸ hx_pre)
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, by simp [hxa, hxb]⟩
      have hK₀_mem : K₀ ∈ rest.powersetCard (U.card - 1) :=
        Finset.mem_powersetCard.mpr ⟨hK₀_sub, hK₀_card⟩
      have hiff : ∀ K ∈ rest.powersetCard (U.card - 1),
          (∀ i ∈ insert a K, σ i ∈ U) ↔ K = K₀ := by
        intro K hK
        obtain ⟨hK_sub, hK_card⟩ := Finset.mem_powersetCard.mp hK
        constructor
        · intro hall
          have hKK₀ : K ⊆ K₀ := by
            intro x hx
            have hxa : x ≠ a :=
              fun h => (Finset.mem_sdiff.mp (hK_sub (h ▸ hx))).2 (by simp)
            have hx_pre : x ∈ U.image σ.symm :=
              Finset.mem_image.mpr ⟨σ x, hall x (Finset.mem_insert_of_mem hx), σ.symm_apply_apply x⟩
            exact Finset.mem_erase.mpr ⟨hxa, hx_pre⟩
          exact Finset.eq_of_subset_of_card_le hKK₀ (by omega)
        · rintro rfl i hi
          rw [Finset.insert_erase ha_pre] at hi
          obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hi
          simpa using hu
      have hsum_eq :
          (∑ K ∈ rest.powersetCard (U.card - 1),
            if ∀ i ∈ insert a K, σ i ∈ U then (1 : ℝ) else 0) =
          ∑ K ∈ rest.powersetCard (U.card - 1),
            if K = K₀ then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro K hK
        simp only [hiff K hK]
      rw [hsum_eq]
      simp [hK₀_mem]
  · simp only [hσa, false_and, ↓reduceIte]
    symm
    apply Finset.sum_eq_zero
    intro K _
    rw [if_neg]
    intro hall
    exact hσa (hall a (Finset.mem_insert_self a K))

lemma cut_nonneg {n : Type*} [Fintype n] [DecidableEq n] (w : Equiv.Perm n → ℝ)
    (hblock : ∀ I J : Finset n, 0 ≤ ∑ σ : Equiv.Perm n,
      w σ * (if ∀ i ∈ I, σ i ∈ J then (1 : ℝ) else 0))
    {a b : n} (hab : a ≠ b) (U : Finset n) :
    0 ≤ ∑ σ : Equiv.Perm n, w σ * (if σ a ∈ U ∧ σ b ∉ U then (1 : ℝ) else 0) := by
  by_cases hU : U.Nonempty
  · simp_rw [ind_cut_eq_sum hab hU, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_nonneg fun K _ => hblock (insert a K) U
  · rw [Finset.not_nonempty_iff_eq_empty] at hU
    subst hU
    simp

lemma sum_range_ite_sub (G : ℕ → ℝ) :
    ∀ i j : ℕ, j ≤ i →
      (∑ r ∈ Finset.range i, if j ≤ r then G (r + 1) - G r else 0) = G i - G j
  | 0, j, hj => by
    have hj0 : j = 0 := by omega
    subst hj0
    simp
  | i + 1, j, hj => by
    by_cases hji : j = i + 1
    · subst hji
      rw [Finset.sum_eq_zero]
      · ring
      · intro r hr
        rw [Finset.mem_range] at hr
        rw [if_neg (by omega)]
    · have hj_le : j ≤ i := by omega
      rw [Finset.sum_range_succ, sum_range_ite_sub G i j hj_le, if_pos hj_le]
      ring

lemma max_diff_nonneg {n : Type*} [Fintype n] [DecidableEq n] (w : Equiv.Perm n → ℝ)
    (hblock : ∀ I J : Finset n, 0 ≤ ∑ σ : Equiv.Perm n,
      w σ * (if ∀ i ∈ I, σ i ∈ J then (1 : ℝ) else 0))
    {a b : n} (hab : a ≠ b) (h : n → ℝ) :
    0 ≤ ∑ σ : Equiv.Perm n, w σ * max (h (σ a) - h (σ b)) 0 := by
  let m := Fintype.card n
  let e : n ≃ Fin m := Fintype.equivFin n
  let f : Fin m → ℝ := fun i => h (e.symm i)
  let equiv : Fin m ≃ n := (Tuple.sort f).trans e.symm
  let g : Fin m → ℝ := f ∘ Tuple.sort f
  have hg_eq : ∀ i : Fin m, h (equiv i) = g i := fun _ => rfl
  have hg_mono : Monotone g := Tuple.monotone_sort f
  let G : ℕ → ℝ := fun r => if hr : r < m then g ⟨r, hr⟩ else 0
  let U : ℕ → Finset n := fun r =>
    (Finset.univ.filter fun idx : Fin m => r < idx.val).map equiv.toEmbedding
  have hmem_U : ∀ (r : ℕ) (x : n), x ∈ U r ↔ r < (equiv.symm x).val := by
    intro r x
    simp only [U, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Equiv.toEmbedding_apply]
    constructor
    · rintro ⟨idx, hlt, rfl⟩
      simpa using hlt
    · intro hlt
      exact ⟨equiv.symm x, hlt, equiv.apply_symm_apply x⟩
  have hdecomp : ∀ x y : n,
      max (h x - h y) 0 =
        ∑ r ∈ Finset.range (m - 1),
          (G (r + 1) - G r) * (if x ∈ U r ∧ y ∉ U r then (1 : ℝ) else 0) := by
    intro x y
    let i : Fin m := equiv.symm x
    let j : Fin m := equiv.symm y
    have hx : h x = g i := by simpa [i] using hg_eq i
    have hy : h y = g j := by simpa [j] using hg_eq j
    have hi_G : G i.val = g i := dif_pos i.isLt
    have hj_G : G j.val = g j := dif_pos j.isLt
    have hcond : ∀ r : ℕ, (x ∈ U r ∧ y ∉ U r) ↔ (j.val ≤ r ∧ r < i.val) := by
      intro r
      rw [hmem_U r x, hmem_U r y]
      change (r < i.val ∧ ¬ r < j.val) ↔ (j.val ≤ r ∧ r < i.val)
      omega
    rw [hx, hy]
    have hrhs :
        (∑ r ∈ Finset.range (m - 1),
          (G (r + 1) - G r) * (if x ∈ U r ∧ y ∉ U r then (1 : ℝ) else 0)) =
        ∑ r ∈ Finset.range (m - 1),
          if j.val ≤ r ∧ r < i.val then G (r + 1) - G r else 0 := by
      apply Finset.sum_congr rfl
      intro r _
      by_cases hc : x ∈ U r ∧ y ∉ U r
      · have hc' : j.val ≤ r ∧ r < i.val := (hcond r).mp hc
        simp [hc, hc']
      · have hc' : ¬ (j.val ≤ r ∧ r < i.val) := fun h' => hc ((hcond r).mpr h')
        simp [hc, hc']
    rw [hrhs]
    by_cases hij : j ≤ i
    · have hij_val : j.val ≤ i.val := hij
      have hmax : max (g i - g j) 0 = G i.val - G j.val := by
        rw [hi_G, hj_G, max_eq_left (sub_nonneg.mpr (hg_mono hij))]
      rw [hmax]
      have hsub_range : Finset.range i.val ⊆ Finset.range (m - 1) := by
        apply Finset.range_mono
        have hi_lt : i.val < m := i.isLt
        omega
      rw [← Finset.sum_subset hsub_range]
      · have htrim :
            (∑ r ∈ Finset.range i.val,
              if j.val ≤ r ∧ r < i.val then G (r + 1) - G r else 0) =
            ∑ r ∈ Finset.range i.val,
              if j.val ≤ r then G (r + 1) - G r else 0 := by
          apply Finset.sum_congr rfl
          intro r hr
          have hr_lt : r < i.val := Finset.mem_range.mp hr
          simp [hr_lt]
        rw [htrim, sum_range_ite_sub G i.val j.val hij_val]
      · intro r _ hr_not
        have hr_ge : ¬ r < i.val := by simpa [Finset.mem_range] using hr_not
        simp [hr_ge]
    · have hji : i ≤ j := le_of_not_ge hij
      rw [max_eq_right (sub_nonpos.mpr (hg_mono hji))]
      symm
      apply Finset.sum_eq_zero
      intro r _
      have hij_lt : i.val < j.val := Nat.lt_of_not_ge hij
      rw [if_neg (by omega)]
  have hc_nonneg : ∀ r ∈ Finset.range (m - 1), 0 ≤ G (r + 1) - G r := by
    intro r hr
    rw [Finset.mem_range] at hr
    have hr1 : r + 1 < m := by omega
    have hr0 : r < m := by omega
    simp only [G, dif_pos hr1, dif_pos hr0]
    exact sub_nonneg.mpr (hg_mono (Fin.mk_le_mk.mpr (by omega)))
  simp_rw [hdecomp, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_nonneg
  intro r hr
  have hmul : ∀ σ : Equiv.Perm n,
      w σ * ((G (r + 1) - G r) * if σ a ∈ U r ∧ σ b ∉ U r then (1 : ℝ) else 0) =
        (G (r + 1) - G r) * (w σ * if σ a ∈ U r ∧ σ b ∉ U r then (1 : ℝ) else 0) :=
    fun _ => by ring
  simp_rw [hmul, ← Finset.mul_sum]
  exact mul_nonneg (hc_nonneg r hr) (cut_nonneg w hblock hab (U r))

lemma pair_image_eq_iff_forall_mem {n : Type*} [DecidableEq n]
    {a b : n} (hab : a ≠ b) {J : Finset n} (hJ : J.card = 2) (σ : Equiv.Perm n) :
    (({a, b} : Finset n).image σ = J) ↔ (∀ i ∈ ({a, b} : Finset n), σ i ∈ J) := by
  constructor
  · rintro rfl i hi
    exact Finset.mem_image_of_mem σ hi
  · intro hall
    have hsub : ({a, b} : Finset n).image σ ⊆ J := by
      intro y hy
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
      exact hall i hi
    have hcard : (({a, b} : Finset n).image σ).card = 2 := by
      rw [Finset.card_image_of_injective _ σ.injective, Finset.card_pair hab]
    exact Finset.eq_of_subset_of_card_le hsub (by omega)

lemma pair_eq_nonneg {n : Type*} [Fintype n] [DecidableEq n] (w : Equiv.Perm n → ℝ)
    (hblock : ∀ I J : Finset n, 0 ≤ ∑ σ : Equiv.Perm n,
      w σ * (if ∀ i ∈ I, σ i ∈ J then (1 : ℝ) else 0))
    {a b : n} (hab : a ≠ b) {J : Finset n} (hJ : J.card = 2) :
    0 ≤ ∑ σ : Equiv.Perm n,
      w σ * (if ({a, b} : Finset n).image σ = J then (1 : ℝ) else 0) := by
  simp_rw [pair_image_eq_iff_forall_mem hab hJ]
  exact hblock {a, b} J

lemma potential_nonneg {n : Type*} [Fintype n] [DecidableEq n] (w : Equiv.Perm n → ℝ)
    (hblock : ∀ I J : Finset n, 0 ≤ ∑ σ : Equiv.Perm n,
      w σ * (if ∀ i ∈ I, σ i ∈ J then (1 : ℝ) else 0))
    {a b : n} (hab : a ≠ b) (u z : n → ℝ) (s : Finset n → ℝ)
    (hg : ∀ σ : Equiv.Perm n, 0 ≤ u (σ a) + z (σ b) + s (({a, b} : Finset n).image σ)) :
    0 ≤ ∑ σ : Equiv.Perm n,
      w σ * (u (σ a) + z (σ b) + s (({a, b} : Finset n).image σ)) := by
  let g : Equiv.Perm n → ℝ := fun σ => u (σ a) + z (σ b) + s (({a, b} : Finset n).image σ)
  let h : n → ℝ := fun x => u x - z x
  let rem : Equiv.Perm n → ℝ := fun σ => g σ - max (h (σ a) - h (σ b)) 0
  have hrem_eq_min : ∀ σ : Equiv.Perm n,
      rem σ = min (u (σ a) + z (σ b)) (u (σ b) + z (σ a)) + s (({a, b} : Finset n).image σ) := by
    intro σ
    simp only [rem, g, h]
    rcases le_total (u (σ a) + z (σ b)) (u (σ b) + z (σ a)) with hle | hle
    · rw [max_eq_right (by linarith), min_eq_left hle]
      ring
    · rw [max_eq_left (by linarith), min_eq_right hle]
      ring
  have hrem_nonneg : ∀ σ : Equiv.Perm n, 0 ≤ rem σ := by
    intro σ
    let τ : Equiv.Perm n := (Equiv.swap a b).trans σ
    have hτa : τ a = σ b := by simp [τ]
    have hτb : τ b = σ a := by simp [τ]
    have hτim : ({a, b} : Finset n).image τ = ({a, b} : Finset n).image σ := by
      simp [Finset.image_insert, hτa, hτb, Finset.pair_comm]
    have hgσ : 0 ≤ g σ := hg σ
    have hgτ : 0 ≤ u (σ b) + z (σ a) + s (({a, b} : Finset n).image σ) := by
      simpa [g, hτa, hτb, hτim] using hg τ
    rw [hrem_eq_min σ]
    rcases le_total (u (σ a) + z (σ b)) (u (σ b) + z (σ a)) with hle | hle
    · rw [min_eq_left hle]
      exact hgσ
    · rw [min_eq_right hle]
      exact hgτ
  have hrem_fiber : ∀ σ₁ σ₂ : Equiv.Perm n,
      ({a, b} : Finset n).image σ₁ = ({a, b} : Finset n).image σ₂ → rem σ₁ = rem σ₂ := by
    intro σ₁ σ₂ him
    have hpair : ({σ₁ a, σ₁ b} : Finset n) = {σ₂ a, σ₂ b} := by
      simpa [Finset.image_insert] using him
    have hne₁ : σ₁ a ≠ σ₁ b := σ₁.injective.ne hab
    have ha_mem : σ₁ a ∈ ({σ₂ a, σ₂ b} : Finset n) := by
      rw [← hpair]
      simp
    have hb_mem : σ₁ b ∈ ({σ₂ a, σ₂ b} : Finset n) := by
      rw [← hpair]
      simp
    rw [hrem_eq_min σ₁, hrem_eq_min σ₂, him]
    rcases Finset.mem_insert.mp ha_mem with ha1 | ha2
    · have hb2 : σ₁ b = σ₂ b := by
        rcases Finset.mem_insert.mp hb_mem with hb1 | hb2
        · exact absurd (ha1.trans hb1.symm) hne₁
        · exact Finset.mem_singleton.mp hb2
      rw [ha1, hb2]
    · have ha2' : σ₁ a = σ₂ b := Finset.mem_singleton.mp ha2
      have hb1 : σ₁ b = σ₂ a := by
        rcases Finset.mem_insert.mp hb_mem with hb1 | hb2
        · exact hb1
        · exact absurd (ha2'.trans (Finset.mem_singleton.mp hb2).symm) hne₁
      rw [ha2', hb1, min_comm]
  have hrem_sum_nonneg : 0 ≤ ∑ σ : Equiv.Perm n, w σ * rem σ := by
    have hpart : ∀ σ : Equiv.Perm n,
        w σ * rem σ =
          ∑ J : Finset n, if ({a, b} : Finset n).image σ = J then w σ * rem σ else 0 :=
      fun _ => by simp
    rw [Finset.sum_congr rfl fun σ _ => hpart σ, Finset.sum_comm]
    apply Finset.sum_nonneg
    intro J _
    by_cases hex : ∃ σ₀ : Equiv.Perm n, ({a, b} : Finset n).image σ₀ = J
    · obtain ⟨σ₀, hσ₀⟩ := hex
      have hJ_card : J.card = 2 := by
        rw [← hσ₀, Finset.card_image_of_injective _ σ₀.injective, Finset.card_pair hab]
      have hcongr : ∀ σ : Equiv.Perm n,
          (if ({a, b} : Finset n).image σ = J then w σ * rem σ else 0) =
            rem σ₀ * (w σ * if ({a, b} : Finset n).image σ = J then 1 else 0) := by
        intro σ
        split_ifs with hσ
        · rw [hrem_fiber σ σ₀ (hσ.trans hσ₀.symm)]
          ring
        · ring
      simp_rw [hcongr, ← Finset.mul_sum]
      exact mul_nonneg (hrem_nonneg σ₀) (pair_eq_nonneg w hblock hab hJ_card)
    · rw [Finset.sum_eq_zero fun σ _ => if_neg fun h => hex ⟨σ, h⟩]
  have hsplit :
      (∑ σ : Equiv.Perm n, w σ * g σ) =
        (∑ σ : Equiv.Perm n, w σ * rem σ) +
          ∑ σ : Equiv.Perm n, w σ * max (h (σ a) - h (σ b)) 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro σ _
    simp only [rem]
    ring
  change 0 ≤ ∑ σ : Equiv.Perm n, w σ * g σ
  rw [hsplit]
  exact add_nonneg hrem_sum_nonneg (max_diff_nonneg w hblock hab h)

abbrev MarginalSpace (n : Type*) := (n → ℝ) × (n → ℝ) × (Finset n → ℝ)

def pairVec {n : Type*} [DecidableEq n] (a b : n) (σ : Equiv.Perm n) : MarginalSpace n :=
  (Pi.single (σ a) 1, Pi.single (σ b) 1, Pi.single (({a, b} : Finset n).image σ) 1)

lemma exists_pair_coupling {n : Type*} [Fintype n] [DecidableEq n]
    (w : Equiv.Perm n → ℝ) (hw_sum : (∑ σ, w σ) = 1)
    (hblock : ∀ I J : Finset n, 0 ≤ ∑ σ : Equiv.Perm n,
      w σ * (if ∀ i ∈ I, σ i ∈ J then (1 : ℝ) else 0))
    {a b : n} (hab : a ≠ b) :
    ∃ t : Equiv.Perm n → ℝ, (∀ σ, 0 ≤ t σ) ∧ (∑ σ, t σ) = 1 ∧
      ∀ S ⊆ ({a, b} : Finset n), ∀ J : Finset n,
        (∑ σ : Equiv.Perm n, if S.image σ = J then w σ else 0) =
          ∑ σ : Equiv.Perm n, if S.image σ = J then t σ else 0 := by
  let v : Equiv.Perm n → MarginalSpace n := pairVec a b
  let x : MarginalSpace n := ∑ σ : Equiv.Perm n, w σ • v σ
  have hx_mem : x ∈ convexHull ℝ (Set.range v) := by
    by_contra hx_not
    obtain ⟨f₀, c, hc_lt, hx_gt⟩ := geometric_hahn_banach_closed_point
      (convex_convexHull ℝ (Set.range v))
      ((Set.finite_range v).isCompact_convexHull ℝ).isClosed
      hx_not
    let F : MarginalSpace n →ₗ[ℝ] ℝ := f₀.toLinearMap
    let u : n → ℝ := fun x₀ => c - F (Pi.single x₀ 1, 0, 0)
    let z : n → ℝ := fun y₀ => - F (0, Pi.single y₀ 1, 0)
    let s : Finset n → ℝ := fun J => - F (0, 0, Pi.single J 1)
    have hv_decomp : ∀ σ : Equiv.Perm n,
        u (σ a) + z (σ b) + s (({a, b} : Finset n).image σ) = c - F (v σ) := by
      intro σ
      have hv_add : v σ =
          (Pi.single (σ a) 1, (0 : n → ℝ), (0 : Finset n → ℝ)) +
            ((0 : n → ℝ), Pi.single (σ b) 1, (0 : Finset n → ℝ)) +
            ((0 : n → ℝ), (0 : n → ℝ), Pi.single (({a, b} : Finset n).image σ) 1) := by
        ext <;> simp [v, pairVec]
      simp only [u, z, s, hv_add, map_add]
      ring
    have hg_nonneg : ∀ σ : Equiv.Perm n,
        0 ≤ u (σ a) + z (σ b) + s (({a, b} : Finset n).image σ) := by
      intro σ
      rw [hv_decomp σ]
      have hlt : F (v σ) < c := hc_lt (v σ) (subset_convexHull ℝ _ ⟨σ, rfl⟩)
      linarith
    have hsum_nonneg : 0 ≤ ∑ σ : Equiv.Perm n,
        w σ * (u (σ a) + z (σ b) + s (({a, b} : Finset n).image σ)) :=
      potential_nonneg w hblock hab u z s hg_nonneg
    have hsum_eval :
        (∑ σ : Equiv.Perm n, w σ * (c - F (v σ))) = c - F x := by
      have hterm : ∀ σ : Equiv.Perm n,
          w σ * (c - F (v σ)) = w σ * c - F (w σ • v σ) := by
        intro σ
        rw [map_smul, smul_eq_mul]
        ring
      simp_rw [hterm]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hw_sum, one_mul, ← map_sum]
    simp_rw [hv_decomp] at hsum_nonneg
    rw [hsum_eval] at hsum_nonneg
    have hx_gt' : c < F x := hx_gt
    linarith
  obtain ⟨ι, _hι, w', z', hw'0, hw'1, hz', hsum_z'⟩ :=
    mem_convexHull_iff_exists_fintype.mp hx_mem
  have hex_pick : ∀ i : ι, ∃ σ : Equiv.Perm n, v σ = z' i := hz'
  choose pick hpick using hex_pick
  let t : Equiv.Perm n → ℝ := fun σ => ∑ i : ι, if pick i = σ then w' i else 0
  have ht_nonneg : ∀ σ : Equiv.Perm n, 0 ≤ t σ := by
    intro σ
    apply Finset.sum_nonneg
    intro i _
    split_ifs
    · exact hw'0 i
    · exact le_rfl
  have ht_sum : (∑ σ : Equiv.Perm n, t σ) = 1 := by
    dsimp only [t]
    rw [Finset.sum_comm]
    simp [hw'1]
  have ht_vec : (∑ σ : Equiv.Perm n, t σ • v σ) = x := by
    dsimp only [t]
    simp_rw [Finset.sum_smul]
    rw [Finset.sum_comm]
    have hinner : ∀ i : ι,
        (∑ σ : Equiv.Perm n, (if pick i = σ then w' i else 0) • v σ) = w' i • z' i := by
      intro i
      simp_rw [ite_smul, zero_smul]
      simp [hpick i]
    simp_rw [hinner]
    exact hsum_z'
  have hm1 : ∀ x₀ : n,
      (∑ σ : Equiv.Perm n, if σ a = x₀ then w σ else 0) =
        ∑ σ : Equiv.Perm n, if σ a = x₀ then t σ else 0 := by
    intro x₀
    have heval := congrFun (congrArg Prod.fst ht_vec.symm) x₀
    simp only [x, v, pairVec, Prod.smul_mk, Prod.fst_sum, Finset.sum_apply,
      Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero] at heval
    simpa only [eq_comm] using heval
  have hm2 : ∀ y₀ : n,
      (∑ σ : Equiv.Perm n, if σ b = y₀ then w σ else 0) =
        ∑ σ : Equiv.Perm n, if σ b = y₀ then t σ else 0 := by
    intro y₀
    have heval := congrFun (congrArg (fun p : MarginalSpace n => p.2.1) ht_vec.symm) y₀
    simp only [x, v, pairVec, Prod.smul_mk, Prod.snd_sum, Prod.fst_sum, Finset.sum_apply,
      Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero] at heval
    simpa only [eq_comm] using heval
  have hm3 : ∀ J : Finset n,
      (∑ σ : Equiv.Perm n, if ({a, b} : Finset n).image σ = J then w σ else 0) =
        ∑ σ : Equiv.Perm n, if ({a, b} : Finset n).image σ = J then t σ else 0 := by
    intro J
    have heval := congrFun (congrArg (fun p : MarginalSpace n => p.2.2) ht_vec.symm) J
    simp only [x, v, pairVec, Prod.smul_mk, Prod.snd_sum, Finset.sum_apply,
      Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero] at heval
    simpa only [eq_comm] using heval
  refine ⟨t, ht_nonneg, ht_sum, ?_⟩
  intro S hS J
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S
  · have hSab : S = {a, b} := by
      ext y
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hy
        exact Finset.mem_insert.mp (hS hy) |>.imp id Finset.mem_singleton.mp
      · rintro (rfl | rfl) <;> assumption
    rw [hSab]
    exact hm3 J
  · have hSa : S = {a} := by
      ext y
      simp only [Finset.mem_singleton]
      constructor
      · intro hy
        rcases Finset.mem_insert.mp (hS hy) with rfl | hyb
        · rfl
        · exact absurd (Finset.mem_singleton.mp hyb ▸ hy) hb
      · rintro rfl
        exact ha
    rw [hSa]
    simp only [Finset.image_singleton]
    by_cases hJ : ∃ x₀ : n, J = {x₀}
    · obtain ⟨x₀, rfl⟩ := hJ
      simp only [Finset.singleton_inj]
      exact hm1 x₀
    · have hne : ∀ σ : Equiv.Perm n, ({σ a} : Finset n) ≠ J :=
        fun σ h => hJ ⟨σ a, h.symm⟩
      simp [hne]
  · have hSb : S = {b} := by
      ext y
      simp only [Finset.mem_singleton]
      constructor
      · intro hy
        rcases Finset.mem_insert.mp (hS hy) with rfl | hyb
        · exact absurd hy ha
        · exact Finset.mem_singleton.mp hyb
      · rintro rfl
        exact hb
    rw [hSb]
    simp only [Finset.image_singleton]
    by_cases hJ : ∃ y₀ : n, J = {y₀}
    · obtain ⟨y₀, rfl⟩ := hJ
      simp only [Finset.singleton_inj]
      exact hm2 y₀
    · have hne : ∀ σ : Equiv.Perm n, ({σ b} : Finset n) ≠ J :=
        fun σ h => hJ ⟨σ b, h.symm⟩
      simp [hne]
  · have hS0 : S = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro y hy
      rcases Finset.mem_insert.mp (hS hy) with rfl | hyb
      · exact ha hy
      · exact hb (Finset.mem_singleton.mp hyb ▸ hy)
    rw [hS0]
    simp only [Finset.image_empty]
    by_cases hJ : (∅ : Finset n) = J
    · simp [hJ, hw_sum, ht_sum]
    · simp [hJ]

end DeterminantalH1Aux

theorem prove_Determinantal_H1 :
    ∀ (n : Type) [Fintype n] [DecidableEq n] (w : Equiv.Perm n → ℝ),
      (∑ σ, w σ) = 1 →
      (∀ I J : Finset n, 0 ≤ ∑ σ : Equiv.Perm n,
        w σ * (if ∀ i ∈ I, σ i ∈ J then (1 : ℝ) else 0)) →
      ∀ T : Finset n, T.card ≤ 2 →
      ∃ t : Equiv.Perm n → ℝ, (∀ σ, 0 ≤ t σ) ∧ (∑ σ, t σ) = 1 ∧
        ∀ S ⊆ T, ∀ J : Finset n,
          (∑ σ : Equiv.Perm n, if S.image σ = J then w σ else 0) =
            ∑ σ : Equiv.Perm n, if S.image σ = J then t σ else 0 := by
  intro n _ _ w hw_sum hblock T hT
  by_cases hcard : Fintype.card n ≤ 1
  · have : Subsingleton n := Fintype.card_le_one_iff_subsingleton.mp hcard
    have hperm_eq : ∀ σ : Equiv.Perm n, σ = 1 :=
      fun σ => Equiv.ext fun x => Subsingleton.elim _ _
    have huniv : (Finset.univ : Finset (Equiv.Perm n)) = {1} := by
      ext σ
      simp [hperm_eq σ]
    have hw1 : w 1 = 1 := by
      simpa [huniv] using hw_sum
    refine ⟨w, ?_, hw_sum, fun _ _ _ => rfl⟩
    intro σ
    rw [hperm_eq σ, hw1]
    exact zero_le_one
  · have : Nontrivial n := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    have hex_pair : ∃ a b : n, a ≠ b ∧ T ⊆ ({a, b} : Finset n) := by
      have hcases : T.card = 0 ∨ T.card = 1 ∨ T.card = 2 := by omega
      rcases hcases with h0 | h1 | h2
      · obtain ⟨a, b, hab⟩ := exists_pair_ne n
        rw [Finset.card_eq_zero.mp h0]
        exact ⟨a, b, hab, Finset.empty_subset _⟩
      · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h1
        obtain ⟨b, hba⟩ := exists_ne a
        refine ⟨a, b, hba.symm, ?_⟩
        intro x hx
        simp [Finset.mem_singleton.mp hx]
      · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h2
        exact ⟨a, b, hab, fun _ hx => hx⟩
    obtain ⟨a, b, hab, hT_sub⟩ := hex_pair
    obtain ⟨t, ht0, ht1, hmarg⟩ :=
      DeterminantalH1Aux.exists_pair_coupling w hw_sum hblock hab
    exact ⟨t, ht0, ht1, fun S hST J => hmarg S (hST.trans hT_sub) J⟩

theorem OMA.solution : OMA.R_DeterminantalConjecture_determinantal_conjecture_R1.H1 :=
  prove_Determinantal_H1
