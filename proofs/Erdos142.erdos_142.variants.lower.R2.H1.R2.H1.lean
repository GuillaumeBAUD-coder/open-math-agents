import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R2
import Mathlib

namespace E142W

open Finset

lemma cover_step (N : ℕ) (S U : Finset ℕ) (hS : S ⊆ Icc 1 N) (hU : U ⊆ Icc (N + 1) (2 * N))
    (hN : 1 ≤ N) :
    ∃ s : ℕ, ((U.filter (fun y => ∀ b ∈ S, y ≠ s + b)).card : ℝ) ≤
      U.card * (1 - S.card / (2 * N)) := by
  classical
  have hN' : (0 : ℝ) < 2 * N := by positivity
  have hmap : ∀ p ∈ U ×ˢ S, (fun p : ℕ × ℕ => p.1 - p.2) p ∈ range (2 * N) := by
    intro p hp
    simp only [mem_product] at hp
    have a1 := mem_Icc.1 (hU hp.1)
    have a2 := mem_Icc.1 (hS hp.2)
    simp only [mem_range]
    omega
  have hne : (range (2 * N)).Nonempty := ⟨0, by simp; omega⟩
  have hb : (range (2 * N)).card • (((U.card : ℝ) * S.card) / (2 * N)) ≤ ((U ×ˢ S).card : ℝ) := by
    rw [card_range, card_product, nsmul_eq_mul]
    push_cast
    field_simp
    exact le_refl _
  obtain ⟨s, -, hs⟩ := exists_le_card_fiber_of_nsmul_le_card_of_maps_to hmap hne hb
  · refine ⟨s, ?_⟩
    have h1 : ((U ×ˢ S).filter (fun p : ℕ × ℕ => p.1 - p.2 = s)).card ≤
        (U.filter (fun y => ¬ ∀ b ∈ S, y ≠ s + b)).card := by
      apply card_le_card_of_injOn Prod.fst
      · intro p hp
        simp only [coe_filter, mem_product, Set.mem_ofPred_eq] at hp
        simp only [coe_filter, Set.mem_ofPred_eq, not_forall, not_not]
        obtain ⟨⟨hp1, hp2⟩, hp3⟩ := hp
        have a1 := mem_Icc.1 (hU hp1)
        have a2 := mem_Icc.1 (hS hp2)
        exact ⟨hp1, p.2, hp2, by omega⟩
      · intro p hp r hr h
        simp only [coe_filter, mem_product, Set.mem_ofPred_eq] at hp hr
        have a1 := mem_Icc.1 (hU hp.1.1)
        have a2 := mem_Icc.1 (hS hp.1.2)
        have a3 := mem_Icc.1 (hS hr.1.2)
        have h' : p.1 = r.1 := h
        exact Prod.ext h' (by omega)
    have h2 := card_filter_add_card_filter_not (s := U)
      (p := fun y => ∀ b ∈ S, y ≠ s + b)
    have h1' : (((U ×ˢ S).filter (fun p : ℕ × ℕ => p.1 - p.2 = s)).card : ℝ) ≤
        ((U.filter (fun y => ¬ ∀ b ∈ S, y ≠ s + b)).card : ℝ) := by exact_mod_cast h1
    have h2' : ((U.filter (fun y => ∀ b ∈ S, y ≠ s + b)).card : ℝ) +
        ((U.filter (fun y => ¬ ∀ b ∈ S, y ≠ s + b)).card : ℝ) = U.card := by exact_mod_cast h2
    have h3 : (U.card : ℝ) * (1 - S.card / (2 * N)) = U.card - (U.card * S.card) / (2 * N) := by
      ring
    rw [h3]
    linarith

lemma cover_iter (N : ℕ) (S : Finset ℕ) (hS : S ⊆ Icc 1 N) (hN : 1 ≤ N) :
    ∀ m : ℕ, ∃ sh : Fin m → ℕ,
      (((Icc (N + 1) (2 * N)).filter (fun y => ∀ t, ∀ b ∈ S, y ≠ sh t + b)).card : ℝ) ≤
        N * (1 - S.card / (2 * N)) ^ m
  | 0 => by
    refine ⟨Fin.elim0, ?_⟩
    have : (Icc (N + 1) (2 * N)).card = N := by rw [Nat.card_Icc]; omega
    simp [this]
  | m + 1 => by
    classical
    obtain ⟨sh, hsh⟩ := cover_iter N S hS hN m
    obtain ⟨s, hs⟩ := cover_step N S
      ((Icc (N + 1) (2 * N)).filter (fun y => ∀ t, ∀ b ∈ S, y ≠ sh t + b)) hS
      (filter_subset _ _) hN
    refine ⟨Fin.cons s sh, ?_⟩
    have heq : (Icc (N + 1) (2 * N)).filter
        (fun y => ∀ t, ∀ b ∈ S, y ≠ (Fin.cons s sh : Fin (m + 1) → ℕ) t + b) =
        ((Icc (N + 1) (2 * N)).filter (fun y => ∀ t, ∀ b ∈ S, y ≠ sh t + b)).filter
          (fun y => ∀ b ∈ S, y ≠ s + b) := by
      ext y
      simp only [mem_filter, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ]
      tauto
    have hc : (S.card : ℝ) ≤ N := by
      have := card_le_card hS
      rw [Nat.card_Icc] at this
      exact_mod_cast (by omega : S.card ≤ N)
    have hNpos : (0 : ℝ) < 2 * N := by positivity
    have h1c : 0 ≤ 1 - (S.card : ℝ) / (2 * N) := by
      rw [sub_nonneg, div_le_one hNpos]
      linarith
    rw [heq, pow_succ, ← mul_assoc]
    exact hs.trans (mul_le_mul_of_nonneg_right hsh h1c)

lemma cover (N q : ℕ) (S : Finset ℕ) (hS : S ⊆ Icc 1 N)
    (h : 2 * (N : ℝ) * Real.log N < q * S.card) :
    ∃ shifts : Fin q → ℕ, ∀ x ∈ Icc 1 N, ∃ t, ∃ b ∈ S, x + N = shifts t + b := by
  classical
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have : S = ∅ := by
      apply subset_empty.1
      simpa using hS
    subst this
    simp at h
  obtain ⟨sh, hsh⟩ := cover_iter N S hS hN q
  refine ⟨sh, ?_⟩
  set c : ℝ := S.card / (2 * N) with hc_def
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : (S.card : ℝ) ≤ N := by
    have := card_le_card hS
    rw [Nat.card_Icc] at this
    exact_mod_cast (by omega : S.card ≤ N)
  have h1c : 0 ≤ 1 - c := by
    rw [hc_def, sub_nonneg, div_le_one (by positivity)]
    linarith
  have hlt : (N : ℝ) * (1 - c) ^ q < 1 := by
    have e1 : (1 - c) ^ q ≤ Real.exp (-c) ^ q := by
      apply pow_le_pow_left₀ h1c
      have := Real.add_one_le_exp (-c)
      linarith
    have e2 : Real.exp (-c) ^ q = Real.exp (-(c * q)) := by
      rw [← Real.exp_nat_mul]
      ring_nf
    have e3 : Real.log N < c * q := by
      rw [hc_def, div_mul_eq_mul_div, lt_div_iff₀ (by positivity)]
      linarith
    calc (N : ℝ) * (1 - c) ^ q ≤ N * Real.exp (-(c * q)) := by
          rw [← e2]; exact mul_le_mul_of_nonneg_left e1 hNpos.le
      _ = Real.exp (Real.log N - c * q) := by
          rw [Real.exp_sub, Real.exp_log hNpos, Real.exp_neg, div_eq_mul_inv]
      _ < Real.exp 0 := Real.exp_lt_exp.2 (by linarith)
      _ = 1 := Real.exp_zero
  have hempty : (Icc (N + 1) (2 * N)).filter (fun y => ∀ t, ∀ b ∈ S, y ≠ sh t + b) = ∅ := by
    apply card_eq_zero.1
    have := hsh.trans_lt hlt
    exact_mod_cast (show ((Icc (N + 1) (2 * N)).filter
      (fun y => ∀ t, ∀ b ∈ S, y ≠ sh t + b)).card < 1 by exact_mod_cast this) |> Nat.lt_one_iff.1
  intro x hx
  by_contra hcon
  push Not at hcon
  have hmem : x + N ∈ (Icc (N + 1) (2 * N)).filter (fun y => ∀ t, ∀ b ∈ S, y ≠ sh t + b) := by
    have := mem_Icc.1 hx
    rw [mem_filter, mem_Icc]
    exact ⟨⟨by omega, by omega⟩, hcon⟩
  rw [hempty] at hmem
  simp at hmem

noncomputable def slice (A : Set ℕ) (j : ℕ) : Finset ℕ := by
  classical
  exact (Icc 1 (4 ^ j)).filter (fun b => 4 * 4 ^ j + b ∈ A)

lemma mem_slice (A : Set ℕ) (j b : ℕ) :
    b ∈ slice A j ↔ b ∈ Icc 1 (4 ^ j) ∧ 4 * 4 ^ j + b ∈ A := by
  unfold slice
  simp only [mem_filter]

lemma slice_subset (A : Set ℕ) (j : ℕ) : slice A j ⊆ Icc 1 (4 ^ j) := by
  intro b hb
  exact ((mem_slice A j b).1 hb).1

lemma sum_biUnion_le' {ι : Type*} [DecidableEq ι] (s : Finset ι) (t : ι → Finset ℕ)
    (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) :
    ∑ x ∈ s.biUnion t, f x ≤ ∑ i ∈ s, ∑ x ∈ t i, f x := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [biUnion_insert, sum_insert ha]
    have h := sum_union_inter (s₁ := t a) (s₂ := s.biUnion t) (f := f)
    have h0 : 0 ≤ ∑ x ∈ t a ∩ s.biUnion t, f x := sum_nonneg (fun n _ => hf n)
    linarith

lemma slice_sum (A : Set ℕ) (j : ℕ) :
    ∑ n ∈ (slice A j).image (fun b : ℕ => (4 * 4 ^ j + b : ℕ)), ((n : ℕ) : ℝ)⁻¹ ≤
      ((slice A j).card : ℝ) / 4 ^ j := by
  have hinj : ∀ a ∈ slice A j, ∀ b ∈ slice A j, 4 * 4 ^ j + a = 4 * 4 ^ j + b → a = b :=
    fun a _ b _ h => Nat.add_left_cancel h
  rw [sum_image hinj]
  have hle : ∀ b ∈ slice A j, ((4 * 4 ^ j + b : ℕ) : ℝ)⁻¹ ≤ ((4 : ℝ) ^ j)⁻¹ := by
    intro b _
    apply inv_anti₀ (by positivity)
    have h1 : (4 ^ j : ℕ) ≤ 4 * 4 ^ j + b := by omega
    exact_mod_cast h1
  calc ∑ b ∈ slice A j, ((4 * 4 ^ j + b : ℕ) : ℝ)⁻¹
      ≤ ∑ b ∈ slice A j, ((4 : ℝ) ^ j)⁻¹ := sum_le_sum hle
    _ = ((slice A j).card : ℝ) / 4 ^ j := by
        rw [sum_const, nsmul_eq_mul, div_eq_mul_inv]

lemma block_mass (A : Set ℕ) (hA : ∀ x ∈ A, ∃ j : ℕ, 4 * 4 ^ j < x ∧ x ≤ 5 * 4 ^ j)
    (u : Finset ℕ) :
    ∑ n ∈ u, A.indicator (fun n : ℕ ↦ (n : ℝ)⁻¹) n ≤
      ∑ j ∈ range (u.sup id + 1), ((slice A j).card : ℝ) / 4 ^ j := by
  classical
  have e1 : ∑ n ∈ u, A.indicator (fun n : ℕ ↦ (n : ℝ)⁻¹) n =
      ∑ n ∈ u.filter (· ∈ A), ((n : ℕ) : ℝ)⁻¹ := by
    rw [sum_filter]
    apply sum_congr rfl
    intro n _
    simp only [Set.indicator_apply]
  rw [e1]
  have hsub : u.filter (· ∈ A) ⊆ (range (u.sup id + 1)).biUnion
      (fun j => (slice A j).image (fun b : ℕ => (4 * 4 ^ j + b : ℕ))) := by
    intro x hx
    rw [mem_filter] at hx
    obtain ⟨j, hj1, hj2⟩ := hA x hx.2
    have hxle : x ≤ u.sup id := le_sup (f := id) hx.1
    have hj : j < 4 ^ j := Nat.lt_pow_self (by norm_num)
    rw [mem_biUnion]
    refine ⟨j, by rw [mem_range]; omega, ?_⟩
    rw [mem_image]
    refine ⟨x - 4 * 4 ^ j, ?_, by omega⟩
    rw [mem_slice, mem_Icc]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    have : 4 * 4 ^ j + (x - 4 * 4 ^ j) = x := by omega
    rw [this]
    exact hx.2
  calc ∑ n ∈ u.filter (· ∈ A), ((n : ℕ) : ℝ)⁻¹
      ≤ ∑ n ∈ (range (u.sup id + 1)).biUnion
          (fun j => (slice A j).image (fun b : ℕ => (4 * 4 ^ j + b : ℕ))), ((n : ℕ) : ℝ)⁻¹ :=
        sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => inv_nonneg.2 (Nat.cast_nonneg n))
    _ ≤ ∑ j ∈ range (u.sup id + 1),
          ∑ n ∈ (slice A j).image (fun b : ℕ => (4 * 4 ^ j + b : ℕ)), ((n : ℕ) : ℝ)⁻¹ :=
        sum_biUnion_le' _ _ _ (fun n => inv_nonneg.2 (Nat.cast_nonneg n))
    _ ≤ ∑ j ∈ range (u.sup id + 1), ((slice A j).card : ℝ) / 4 ^ j :=
        sum_le_sum (fun j _ => slice_sum A j)

lemma log_four_gt_one : 1 < Real.log 4 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

lemma main_aux (A : Set ℕ) (hA : ∀ x ∈ A, ∃ j : ℕ, 4 * 4 ^ j < x ∧ x ≤ 5 * 4 ^ j)
    (hdiv : ¬ Summable (A.indicator (fun n : ℕ ↦ (n : ℝ)⁻¹))) (J : ℕ) :
    ∃ j : ℕ, J ≤ j ∧
      ∃ shifts : Fin ((⌈Real.log ((4 ^ j : ℕ) : ℝ)⌉₊ + 1) ^ 4) → ℕ,
        ∀ x ∈ Finset.Icc 1 (4 ^ j),
          ∃ t : Fin ((⌈Real.log ((4 ^ j : ℕ) : ℝ)⌉₊ + 1) ^ 4),
            ∃ b ∈ Finset.Icc 1 (4 ^ j), 4 * 4 ^ j + b ∈ A ∧ x + 4 ^ j = shifts t + b := by
  by_contra hcon
  have hbound : ∀ j, J ≤ j →
      (((⌈Real.log ((4 ^ j : ℕ) : ℝ)⌉₊ + 1) ^ 4 : ℕ) : ℝ) * ((slice A j).card : ℝ) ≤
        2 * ((4 ^ j : ℕ) : ℝ) * Real.log ((4 ^ j : ℕ) : ℝ) := by
    intro j hj
    by_contra hlt
    push Not at hlt
    apply hcon
    obtain ⟨sh, hsh⟩ := cover (4 ^ j) ((⌈Real.log ((4 ^ j : ℕ) : ℝ)⌉₊ + 1) ^ 4) (slice A j)
      (slice_subset A j) hlt
    refine ⟨j, hj, sh, fun x hx => ?_⟩
    obtain ⟨t, b, hb, he⟩ := hsh x hx
    exact ⟨t, b, ((mem_slice A j b).1 hb).1, ((mem_slice A j b).1 hb).2, he⟩
  have ha_nonneg : ∀ j, 0 ≤ ((slice A j).card : ℝ) / 4 ^ j := fun j => by positivity
  have hev : ∀ j, max J 1 ≤ j → ((slice A j).card : ℝ) / 4 ^ j ≤ 2 * (1 / (j : ℝ) ^ 3) := by
    intro j hj
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (le_of_max_le_right hj)
    have hL : Real.log ((4 ^ j : ℕ) : ℝ) = j * Real.log 4 := by
      push_cast
      rw [Real.log_pow]
    have hl4 := log_four_gt_one
    have hb := hbound j (le_of_max_le_left hj)
    set L := Real.log ((4 ^ j : ℕ) : ℝ) with hL_def
    have hLj : (j : ℝ) ≤ L := by rw [hL]; nlinarith
    have hLpos : 0 < L := by linarith
    have hq : L ^ 4 ≤ (((⌈L⌉₊ + 1) ^ 4 : ℕ) : ℝ) := by
      push_cast
      apply pow_le_pow_left₀ hLpos.le
      have := Nat.le_ceil L
      linarith
    have hS0 : (0 : ℝ) ≤ (slice A j).card := by positivity
    have key : ((slice A j).card : ℝ) * L ^ 3 ≤ 2 * ((4 ^ j : ℕ) : ℝ) := by
      have h1 : L * (((slice A j).card : ℝ) * L ^ 3) ≤ L * (2 * ((4 ^ j : ℕ) : ℝ)) := by
        have := mul_le_mul_of_nonneg_right hq hS0
        nlinarith
      exact le_of_mul_le_mul_left h1 hLpos
    have key2 : ((slice A j).card : ℝ) * (j : ℝ) ^ 3 ≤ 2 * (4 : ℝ) ^ j := by
      have := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hLj 3) hS0
      push_cast at key
      linarith
    rw [show 2 * (1 / (j : ℝ) ^ 3) = 2 / (j : ℝ) ^ 3 by ring,
      div_le_div_iff₀ (by positivity) (by positivity)]
    exact key2
  have hsum : Summable (fun j => ((slice A j).card : ℝ) / 4 ^ j) := by
    apply Summable.of_norm_bounded_eventually_nat
      ((Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 3)).mul_left 2)
    rw [Filter.eventually_atTop]
    exact ⟨max J 1, fun j hj => by rw [Real.norm_of_nonneg (ha_nonneg j)]; exact hev j hj⟩
  apply hdiv
  apply summable_of_sum_le (c := ∑' j, ((slice A j).card : ℝ) / 4 ^ j)
  · intro n
    apply Set.indicator_nonneg
    intro n _
    positivity
  · intro u
    exact (block_mass A hA u).trans (hsum.sum_le_tsum _ (fun j _ => ha_nonneg j))

end E142W

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R2.H1 :=
  fun A hA hdiv J => E142W.main_aux A hA hdiv J
