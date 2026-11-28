import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R2
import Mathlib

-- Scratch proof for Erdos142.erdos_142.variants.lower.R2.H1.R2.H1

namespace Scratch36944H1

open Finset Filter

lemma count_bound (N q s : ℕ) (hN : 0 < N) (hsN : s ≤ N)
    (h : 2 * (N : ℝ) * Real.log (N : ℝ) < (q : ℝ) * (s : ℝ)) :
    N * (2 * N - s) ^ q < (2 * N) ^ q := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsr : (s : ℝ) ≤ N := by exact_mod_cast hsN
  have hMpos : (0 : ℝ) < 2 * N := by positivity
  set a : ℝ := (s : ℝ) / (2 * N) with ha
  have ha1 : a ≤ 1 := by
    rw [ha, div_le_one hMpos]
    linarith
  have hcast : (((2 * N - s : ℕ)) : ℝ) = (2 * N) * (1 - a) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    rw [ha]
    field_simp
  have hexp : (1 - a) ^ q ≤ Real.exp (-(q * a)) := by
    calc (1 - a) ^ q ≤ Real.exp (-a) ^ q := by
          apply pow_le_pow_left₀ (by linarith)
          linarith [Real.add_one_le_exp (-a)]
      _ = Real.exp (-(q * a)) := by
          rw [← Real.exp_nat_mul]
          ring_nf
  have hlog : Real.log N < q * a := by
    rw [ha, mul_div_assoc', lt_div_iff₀ hMpos]
    linarith
  have hlt : Real.exp (-(q * a)) < 1 / N := by
    rw [one_div, ← Real.exp_log hNr, ← Real.exp_neg, Real.exp_lt_exp]
    linarith
  have hkey : (N : ℝ) * (1 - a) ^ q < 1 := by
    calc (N : ℝ) * (1 - a) ^ q ≤ N * Real.exp (-(q * a)) :=
          mul_le_mul_of_nonneg_left hexp hNr.le
      _ < N * (1 / N) := mul_lt_mul_of_pos_left hlt hNr
      _ = 1 := by field_simp
  have hreal : ((N * (2 * N - s) ^ q : ℕ) : ℝ) < (((2 * N) ^ q : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_pow, hcast, mul_pow, Nat.cast_pow]
    have hpow : (0 : ℝ) < (2 * N) ^ q := by positivity
    have e2 : (((2 * N : ℕ)) : ℝ) = 2 * (N : ℝ) := by push_cast; ring
    rw [e2]
    calc (N : ℝ) * ((2 * N) ^ q * (1 - a) ^ q) = (2 * N) ^ q * ((N : ℝ) * (1 - a) ^ q) := by ring
      _ < (2 * N) ^ q * 1 := mul_lt_mul_of_pos_left hkey hpow
      _ = (2 * N) ^ q := mul_one _
  exact_mod_cast hreal

lemma exists_shift_cover (N q : ℕ) (S : Finset ℕ) (hN : 0 < N) (hS : S ⊆ Icc 1 N)
    (h : 2 * (N : ℝ) * Real.log (N : ℝ) < (q : ℝ) * (S.card : ℝ)) :
    ∃ shifts : Fin q → ℕ, ∀ x ∈ Icc 1 N, ∃ t : Fin q, ∃ b ∈ S, x + N = shifts t + b := by
  have hsN : S.card ≤ N := by simpa using card_le_card hS
  let A : ℕ → Finset (Fin (2 * N)) := fun x =>
    univ.filter (fun r : Fin (2 * N) => ∀ b ∈ S, r.val + b ≠ x + N)
  have hA : ∀ x ∈ Icc 1 N, (A x).card ≤ 2 * N - S.card := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := mem_Icc.mp hx
    let C := univ.filter (fun r : Fin (2 * N) => ¬ ∀ b ∈ S, r.val + b ≠ x + N)
    have hC : S.card ≤ C.card := by
      apply card_le_card_of_injOn
        (fun b => (⟨(x + N - b) % (2 * N), Nat.mod_lt _ (by omega)⟩ : Fin (2 * N)))
      · intro b hb
        rw [mem_coe] at hb
        have hb' := mem_Icc.mp (hS hb)
        rw [mem_coe, mem_filter]
        refine ⟨mem_univ _, ?_⟩
        intro hall
        apply hall b hb
        simp only
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
      · intro b hb b' hb' heq
        rw [mem_coe] at hb hb'
        have h1 := mem_Icc.mp (hS hb)
        have h2 := mem_Icc.mp (hS hb')
        have hv := congrArg Fin.val heq
        simp only at hv
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hv
        omega
    have hsum := card_filter_add_card_filter_not (s := (univ : Finset (Fin (2 * N))))
      (fun r : Fin (2 * N) => ∀ b ∈ S, r.val + b ≠ x + N)
    rw [card_univ, Fintype.card_fin] at hsum
    change (A x).card + C.card = 2 * N at hsum
    omega
  let Bad : ℕ → Finset (Fin q → Fin (2 * N)) := fun x => Fintype.piFinset (fun _ => A x)
  let U := (Icc 1 N).biUnion Bad
  have hU : U.card < (univ : Finset (Fin q → Fin (2 * N))).card := by
    calc U.card ≤ ∑ x ∈ Icc 1 N, (Bad x).card := card_biUnion_le
      _ ≤ ∑ x ∈ Icc 1 N, (2 * N - S.card) ^ q := by
          apply sum_le_sum
          intro x hx
          change (Fintype.piFinset fun _ : Fin q => A x).card ≤ _
          rw [Fintype.card_piFinset_const]
          exact Nat.pow_le_pow_left (hA x hx) q
      _ = N * (2 * N - S.card) ^ q := by
          rw [sum_const, Nat.card_Icc, smul_eq_mul]; simp
      _ < (2 * N) ^ q := count_bound N q S.card hN hsN h
      _ = (univ : Finset (Fin q → Fin (2 * N))).card := by rw [card_univ]; simp
  obtain ⟨f, -, hf⟩ := exists_mem_notMem_of_card_lt_card hU
  refine ⟨fun t => (f t).val, ?_⟩
  intro x hx
  have hnot : f ∉ Bad x := fun hmem => hf (mem_biUnion.mpr ⟨x, hx, hmem⟩)
  rw [Fintype.mem_piFinset] at hnot
  push Not at hnot
  obtain ⟨t, ht⟩ := hnot
  simp only [A, mem_filter, mem_univ, true_and, not_forall, not_not] at ht
  obtain ⟨b, hb, hbeq⟩ := ht
  exact ⟨t, b, hb, hbeq.symm⟩

theorem test_36944_H1 :
    ∀ A : Set ℕ, (∀ x ∈ A, ∃ j : ℕ, 4 * 4 ^ j < x ∧ x ≤ 5 * 4 ^ j) →
      ¬ Summable (A.indicator (fun n : ℕ ↦ (n : ℝ)⁻¹)) →
      ∀ J : ℕ, ∃ j : ℕ, J ≤ j ∧
        ∃ shifts : Fin ((⌈Real.log ((4 ^ j : ℕ) : ℝ)⌉₊ + 1) ^ 4) → ℕ,
          ∀ x ∈ Finset.Icc 1 (4 ^ j),
            ∃ t : Fin ((⌈Real.log ((4 ^ j : ℕ) : ℝ)⌉₊ + 1) ^ 4),
              ∃ b ∈ Finset.Icc 1 (4 ^ j), 4 * 4 ^ j + b ∈ A ∧ x + 4 ^ j = shifts t + b := by
  classical
  intro A hA hns J
  by_contra hno
  push Not at hno
  let S : ℕ → Finset ℕ := fun j => (Finset.Icc 1 (4 ^ j)).filter (fun b => 4 * 4 ^ j + b ∈ A)
  let g : ℕ → ℝ := fun j => ∑ b ∈ S j, ((4 * 4 ^ j + b : ℕ) : ℝ)⁻¹
  have hg_nonneg : ∀ j, 0 ≤ g j := fun j => Finset.sum_nonneg (fun _ _ => by positivity)
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hg_bound : ∀ j : ℕ, max J 1 ≤ j →
      g j ≤ (2 * (Real.log 4) ^ 3)⁻¹ * ((j : ℝ) ^ (3 : ℝ))⁻¹ := by
    intro j hj
    have hjJ : J ≤ j := (le_max_left _ _).trans hj
    have hj1 : 1 ≤ j := (le_max_right _ _).trans hj
    have hNpos : 0 < 4 ^ j := by positivity
    let q := (⌈Real.log ((4 ^ j : ℕ) : ℝ)⌉₊ + 1) ^ 4
    have hnot_gt : ¬ (2 * ((4 ^ j : ℕ) : ℝ) * Real.log ((4 ^ j : ℕ) : ℝ) <
        (q : ℝ) * ((S j).card : ℝ)) := by
      intro hlt
      obtain ⟨shifts, hshifts⟩ := exists_shift_cover (4 ^ j) q (S j) hNpos (Finset.filter_subset _ _) hlt
      obtain ⟨x, hx, hbad⟩ := hno j hjJ shifts
      obtain ⟨t, b, hbS, hbeq⟩ := hshifts x hx
      obtain ⟨hbIcc, hbA⟩ := Finset.mem_filter.mp hbS
      exact hbad t b hbIcc hbA hbeq
    have hcard_le : (q : ℝ) * ((S j).card : ℝ) ≤
        2 * ((4 ^ j : ℕ) : ℝ) * Real.log ((4 ^ j : ℕ) : ℝ) := le_of_not_gt hnot_gt
    have hcast4 : ((4 ^ j : ℕ) : ℝ) = (4 : ℝ) ^ j := by norm_num
    have hL : Real.log ((4 ^ j : ℕ) : ℝ) = (j : ℝ) * Real.log 4 := by
      rw [hcast4, Real.log_pow]
    have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
    have hLpos : 0 < (j : ℝ) * Real.log 4 := mul_pos hjpos hlog4
    have hLq : ((j : ℝ) * Real.log 4) ^ 4 ≤ (q : ℝ) := by
      have h1 : (j : ℝ) * Real.log 4 ≤ ((⌈Real.log ((4 ^ j : ℕ) : ℝ)⌉₊ + 1 : ℕ) : ℝ) := by
        rw [← hL, Nat.cast_add, Nat.cast_one]
        linarith [Nat.le_ceil (Real.log ((4 ^ j : ℕ) : ℝ))]
      have h2 := pow_le_pow_left₀ hLpos.le h1 4
      exact_mod_cast h2
    have hS_le : ((S j).card : ℝ) ≤ 2 * (4 : ℝ) ^ j / ((j : ℝ) * Real.log 4) ^ 3 := by
      rw [le_div_iff₀ (pow_pos hLpos 3)]
      have hstep : ((j : ℝ) * Real.log 4) ^ 4 * ((S j).card : ℝ) ≤
          2 * (4 : ℝ) ^ j * ((j : ℝ) * Real.log 4) := by
        calc ((j : ℝ) * Real.log 4) ^ 4 * ((S j).card : ℝ)
            ≤ (q : ℝ) * ((S j).card : ℝ) := mul_le_mul_of_nonneg_right hLq (Nat.cast_nonneg _)
          _ ≤ 2 * ((4 ^ j : ℕ) : ℝ) * Real.log ((4 ^ j : ℕ) : ℝ) := hcard_le
          _ = 2 * (4 : ℝ) ^ j * ((j : ℝ) * Real.log 4) := by rw [hL, hcast4]
      nlinarith
    have hg_le_card : g j ≤ ((S j).card : ℝ) / (4 * (4 : ℝ) ^ j) := by
      calc g j
          ≤ ∑ _b ∈ S j, (4 * (4 : ℝ) ^ j)⁻¹ := by
            apply Finset.sum_le_sum
            intro b hb
            have hb1 : 1 ≤ b := (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1
            apply inv_anti₀ (by positivity)
            have : 4 * 4 ^ j ≤ 4 * 4 ^ j + b := by omega
            exact_mod_cast this
        _ = ((S j).card : ℝ) / (4 * (4 : ℝ) ^ j) := by simp [div_eq_mul_inv]
    calc g j ≤ ((S j).card : ℝ) / (4 * (4 : ℝ) ^ j) := hg_le_card
      _ ≤ (2 * (4 : ℝ) ^ j / ((j : ℝ) * Real.log 4) ^ 3) / (4 * (4 : ℝ) ^ j) :=
          div_le_div_of_nonneg_right hS_le (by positivity)
      _ = (2 * (Real.log 4) ^ 3)⁻¹ * ((j : ℝ) ^ (3 : ℝ))⁻¹ := by
          have hj3 : ((j : ℝ) ^ (3 : ℝ)) = (j : ℝ) ^ 3 := by norm_cast
          rw [hj3, mul_pow]
          have h4pos : (4 : ℝ) ^ j ≠ 0 := by positivity
          field_simp
          ring
  have hg_summable : Summable g := by
    have hp : Summable (fun j : ℕ => (2 * (Real.log 4) ^ 3)⁻¹ * ((j : ℝ) ^ (3 : ℝ))⁻¹) :=
      (Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 3)).mul_left _
    refine Summable.of_norm_bounded_eventually_nat hp ?_
    filter_upwards [eventually_ge_atTop (max J 1)] with j hj
    rw [Real.norm_of_nonneg (hg_nonneg j)]
    exact hg_bound j hj
  apply hns
  refine summable_of_sum_le (c := ∑' j, g j)
    (fun n => Set.indicator_nonneg (fun _ _ => by positivity) n) ?_
  intro s
  let M : ℕ := s.sup id + 1
  have hblock_mem : ∀ x ∈ s, x ∈ A →
      x ∈ (Finset.range M).biUnion (fun j => (S j).map (addLeftEmbedding (4 * 4 ^ j))) := by
    intro x hx hxA
    obtain ⟨j, hj1, hj2⟩ := hA x hxA
    have hjM : j < M := by
      have hxle : x ≤ s.sup id := Finset.le_sup (f := id) hx
      have h4j : j < 4 ^ j := Nat.lt_pow_self (by decide : 1 < 4)
      omega
    refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hjM, ?_⟩
    refine Finset.mem_map.mpr ⟨x - 4 * 4 ^ j, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
      rwa [show 4 * 4 ^ j + (x - 4 * 4 ^ j) = x by omega]
    · change 4 * 4 ^ j + (x - 4 * 4 ^ j) = x
      omega
  have hdisj : Set.PairwiseDisjoint ((Finset.range M : Finset ℕ) : Set ℕ)
      (fun j => (S j).map (addLeftEmbedding (4 * 4 ^ j))) := by
    intro i _ j _ hne
    apply Finset.disjoint_left.mpr
    intro x hxi hxj
    obtain ⟨bi, hbi, rfl⟩ := Finset.mem_map.mp hxi
    obtain ⟨bj, hbj, heq⟩ := Finset.mem_map.mp hxj
    have hi := Finset.mem_Icc.mp (Finset.mem_filter.mp hbi).1
    have hj := Finset.mem_Icc.mp (Finset.mem_filter.mp hbj).1
    change 4 * 4 ^ j + bj = 4 * 4 ^ i + bi at heq
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : 4 * 4 ^ i ≤ 4 ^ j := by
        rw [mul_comm, ← pow_succ]
        exact Nat.pow_le_pow_right (by decide) hlt
      omega
    · have : 4 * 4 ^ j ≤ 4 ^ i := by
        rw [mul_comm, ← pow_succ]
        exact Nat.pow_le_pow_right (by decide) hgt
      omega
  calc ∑ n ∈ s, A.indicator (fun n : ℕ => (n : ℝ)⁻¹) n
      = ∑ n ∈ s.filter (· ∈ A), (n : ℝ)⁻¹ := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro n _
        by_cases hn : n ∈ A <;> simp [Set.indicator, hn]
    _ ≤ ∑ n ∈ (Finset.range M).biUnion (fun j => (S j).map (addLeftEmbedding (4 * 4 ^ j))),
          (n : ℝ)⁻¹ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro x hx
          obtain ⟨hxs, hxA⟩ := Finset.mem_filter.mp hx
          exact hblock_mem x hxs hxA
        · intro _ _ _; positivity
    _ = ∑ j ∈ Finset.range M, g j := by
        rw [Finset.sum_biUnion hdisj]
        apply Finset.sum_congr rfl
        intro j _
        simp [g, Finset.sum_map]
    _ ≤ ∑' j, g j := hg_summable.sum_le_tsum (Finset.range M) (fun j _ => hg_nonneg j)

end Scratch36944H1

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R2.H1 := Scratch36944H1.test_36944_H1
