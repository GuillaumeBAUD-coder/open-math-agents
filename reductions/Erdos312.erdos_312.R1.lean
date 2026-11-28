import FormalConjectures.ErdosProblems.«312»
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Multiset.Replicate
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Multiset.Filter
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace OMA.R_Erdos312_erdos_312_R1

/-- Stable multisets of primes. -/
def H1 : Prop := ∃ c : ℝ, 0 < c ∧ ∀ (K : ℝ), 1 < K → ∀ A : Multiset ℕ,
      (∀ n ∈ A, Nat.Prime n) →
      (∀ n ∈ A, ∀ p : ℕ, Nat.Prime p → p ∣ n → A.count n < p) →
      K < (A.map (fun n : ℕ => (n : ℝ)⁻¹)).sum →
      ∃ S ≤ A, 1 - Real.exp (-(c*K)) < (S.map (fun n : ℕ => (n : ℝ)⁻¹)).sum ∧
        (S.map (fun n : ℕ => (n : ℝ)⁻¹)).sum ≤ 1

/-- Stable multisets of composite positive integers. -/
def H2 : Prop := ∃ c : ℝ, 0 < c ∧ ∀ (K : ℝ), 1 < K → ∀ A : Multiset ℕ,
      (∀ n ∈ A, 2 ≤ n ∧ ¬ Nat.Prime n) →
      (∀ n ∈ A, ∀ p : ℕ, Nat.Prime p → p ∣ n → A.count n < p) →
      K < (A.map (fun n : ℕ => (n : ℝ)⁻¹)).sum →
      ∃ S ≤ A, 1 - Real.exp (-(c*K)) < (S.map (fun n : ℕ => (n : ℝ)⁻¹)).sum ∧
        (S.map (fun n : ℕ => (n : ℝ)⁻¹)).sum ≤ 1




open Multiset


@[simp] theorem mass_cons (n : ℕ) (A : Multiset ℕ) :
    ((n ::ₘ A).map (fun n : ℕ => (n : ℝ)⁻¹)).sum = (n : ℝ)⁻¹ + ((A).map (fun n : ℕ => (n : ℝ)⁻¹)).sum := by
  simp

@[simp] theorem mass_add (A B : Multiset ℕ) :
    ((A+B).map (fun n : ℕ => (n : ℝ)⁻¹)).sum = ((A).map (fun n : ℕ => (n : ℝ)⁻¹)).sum + ((B).map (fun n : ℕ => (n : ℝ)⁻¹)).sum := by
  simp

@[simp] theorem mass_replicate (k n : ℕ) :
    ((replicate k n).map (fun n : ℕ => (n : ℝ)⁻¹)).sum = (k : ℝ) * (n : ℝ)⁻¹ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [replicate_succ, mass_cons, ih, Nat.cast_succ, add_mul, one_mul, add_comm]

/-- Replacing `p` copies of `n` by one copy of `n / p` preserves reciprocal mass. -/
theorem factor_mass_eq (p n : ℕ) (hp : 2 ≤ p) (hn : 0 < n)
    (hd : p ∣ n) :
    (↑(n / p) : ℝ)⁻¹ = ((replicate p n).map (fun n : ℕ => (n : ℝ)⁻¹)).sum := by
  rw [mass_replicate]
  obtain ⟨q, hq⟩ := hd
  have hp0 : p ≠ 0 := by omega
  have hq0 : q ≠ 0 := by
    intro h
    simp [h] at hq
    omega
  rw [hq, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hp0)]
  rw [Nat.cast_mul]
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp0
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq0
  rw [mul_comm (p : ℝ) (q : ℝ), mul_inv_rev, mul_inv_cancel_left₀ hpR]

/-- Every subsum of the compressed multiset lifts to an actual subsum of the original. -/
theorem merge_lift (B : Multiset ℕ) (p n : ℕ) (hp : 2 ≤ p)
    (hn : 0 < n) (hd : p ∣ n) {U : Multiset ℕ}
    (hU : U ≤ (n/p) ::ₘ B) :
    ∃ V : Multiset ℕ, V ≤ replicate p n + B ∧ ((V).map (fun n : ℕ => (n : ℝ)⁻¹)).sum = ((U).map (fun n : ℕ => (n : ℝ)⁻¹)).sum := by
  by_cases hmem : n/p ∈ U
  · have hErase : U.erase (n/p) ≤ B := erase_le_iff_le_cons.mpr hU
    refine ⟨replicate p n + U.erase (n/p), Multiset.add_le_add_left hErase, ?_⟩
    rw [mass_add, ← factor_mass_eq p n hp hn hd, ← mass_cons, cons_erase hmem]
  · have hSub : U ≤ B := (le_cons_of_notMem hmem).mp hU
    exact ⟨U, le_trans hSub (Multiset.le_add_left B (replicate p n)), rfl⟩

/-- Prime-factor compression. Each denominator can be replaced by a divisor when
enough copies occur. The resulting multiset has the same mass, stays in the
original positive denominator range, and all of its subsums lift. -/
theorem compression_exists (A : Multiset ℕ) (N : ℝ)
    (hA : ∀ n ∈ A, 0 < n ∧ (n : ℝ) < N) :
    ∃ C : Multiset ℕ,
      (∀ n ∈ C, 0 < n ∧ (n : ℝ) < N) ∧
      ((C).map (fun n : ℕ => (n : ℝ)⁻¹)).sum = ((A).map (fun n : ℕ => (n : ℝ)⁻¹)).sum ∧
      (∀ n p : ℕ, 2 ≤ p → p ∣ n → C.count n < p) ∧
      (∀ U : Multiset ℕ, U ≤ C → ∃ V : Multiset ℕ, V ≤ A ∧ ((V).map (fun n : ℕ => (n : ℝ)⁻¹)).sum = ((U).map (fun n : ℕ => (n : ℝ)⁻¹)).sum) := by
  classical
  revert hA
  apply (measure (fun A : Multiset ℕ => A.card)).wf.induction (C := fun A =>
    (∀ n ∈ A, 0 < n ∧ (n : ℝ) < N) →
    ∃ C : Multiset ℕ,
      (∀ n ∈ C, 0 < n ∧ (n : ℝ) < N) ∧
      ((C).map (fun n : ℕ => (n : ℝ)⁻¹)).sum = ((A).map (fun n : ℕ => (n : ℝ)⁻¹)).sum ∧
      (∀ n p : ℕ, 2 ≤ p → p ∣ n → C.count n < p) ∧
      (∀ U : Multiset ℕ, U ≤ C → ∃ V : Multiset ℕ, V ≤ A ∧ ((V).map (fun n : ℕ => (n : ℝ)⁻¹)).sum = ((U).map (fun n : ℕ => (n : ℝ)⁻¹)).sum)) A
  intro A ih hA
  by_cases hs : ∀ n p : ℕ, 2 ≤ p → p ∣ n → A.count n < p
  · exact ⟨A, hA, rfl, hs, fun U hU => ⟨U, hU, rfl⟩⟩
  obtain ⟨n, hn⟩ := not_forall.mp hs
  obtain ⟨p, hp⟩ := not_forall.mp hn
  have hp' : 2 ≤ p := by
    by_contra h
    exact hp (fun h' => (h h').elim)
  have hd : p ∣ n := by
    by_contra h
    exact hp (fun _ h' => (h h').elim)
  have hc : p ≤ count n A := le_of_not_gt (fun h => hp (fun _ _ => h))
  clear hp
  have hn : n ∈ A := count_pos.mp (lt_of_lt_of_le (by omega : 0 < p) hc)
  have hn0 : 0 < n := (hA n hn).1
  have hrep : replicate p n ≤ A := le_count_iff_replicate_le.mp hc
  obtain ⟨B, hB⟩ := Multiset.le_iff_exists_add.mp hrep
  let C' : Multiset ℕ := (n / p) ::ₘ B
  have hp0 : 0 < p := by omega
  have hC' : ∀ m ∈ C', 0 < m ∧ (m : ℝ) < N := by
    intro m hm
    rcases mem_cons.mp hm with h | h
    · subst m
      exact ⟨Nat.div_pos (Nat.le_of_dvd hn0 hd) hp0,
        lt_of_le_of_lt (by exact_mod_cast Nat.div_le_self n p) (hA n hn).2⟩
    · exact hA m (by rw [hB]; exact mem_add.mpr (Or.inr h))
  have hmass : ((C').map (fun n : ℕ => (n : ℝ)⁻¹)).sum = ((A).map (fun n : ℕ => (n : ℝ)⁻¹)).sum := by
    rw [hB]
    simp only [C', mass_cons, mass_add, factor_mass_eq p n hp' hn0 hd]
  have hsmall : C'.card < A.card := by
    rw [hB]
    simp only [C', card_cons, card_add, card_replicate]
    omega
  obtain ⟨C, hC, hmassC, hstable, hLift⟩ := ih C' hsmall hC'
  refine ⟨C, hC, hmassC.trans hmass, hstable, ?_⟩
  intro U hU
  obtain ⟨V, hV, hmassV⟩ := hLift U hU
  obtain ⟨W, hW, hmassW⟩ := merge_lift B p n hp' hn0 hd hV
  exact ⟨W, by simpa only [hB] using hW, hmassW.trans hmassV⟩

/-- An original multiset without exact unit subsums cannot compress to denominator one. -/
theorem one_not_mem_of_lift {A C : Multiset ℕ}
    (hNoOne : ∀ U : Multiset ℕ, U ≤ A → ((U).map (fun n : ℕ => (n : ℝ)⁻¹)).sum ≠ 1)
    (hLift : ∀ U : Multiset ℕ, U ≤ C → ∃ V : Multiset ℕ, V ≤ A ∧ ((V).map (fun n : ℕ => (n : ℝ)⁻¹)).sum = ((U).map (fun n : ℕ => (n : ℝ)⁻¹)).sum) :
    1 ∉ C := by
  intro h
  obtain ⟨V, hV, hmass⟩ := hLift {1} (by simpa using h)
  exact hNoOne V hV (by simpa using hmass)




-- For any tolerance and real budget L, it suffices to handle stable prime-only
-- and stable composite-only multisets of mass > L, as long as the whole multiset
-- has mass > L + L.
theorem stable_partition (A : Multiset ℕ) (L δ : ℝ)
    (hden : ∀ n ∈ A, 2 ≤ n)
    (hstable : ∀ n ∈ A, ∀ p : ℕ, Nat.Prime p → p ∣ n → A.count n < p)
    (hmass : L + L < (A.map (fun n : ℕ => (n : ℝ)⁻¹)).sum)
    (HP : ∀ P : Multiset ℕ, (∀ n ∈ P, Nat.Prime n) →
      (∀ n ∈ P, ∀ p : ℕ, Nat.Prime p → p ∣ n → P.count n < p) →
      L < (P.map (fun n : ℕ => (n : ℝ)⁻¹)).sum →
      ∃ S ≤ P, 1 - δ < (S.map (fun n : ℕ => (n : ℝ)⁻¹)).sum ∧
        (S.map (fun n : ℕ => (n : ℝ)⁻¹)).sum ≤ 1)
    (HC : ∀ C : Multiset ℕ, (∀ n ∈ C, 2 ≤ n ∧ ¬ Nat.Prime n) →
      (∀ n ∈ C, ∀ p : ℕ, Nat.Prime p → p ∣ n → C.count n < p) →
      L < (C.map (fun n : ℕ => (n : ℝ)⁻¹)).sum →
      ∃ S ≤ C, 1 - δ < (S.map (fun n : ℕ => (n : ℝ)⁻¹)).sum ∧
        (S.map (fun n : ℕ => (n : ℝ)⁻¹)).sum ≤ 1) :
      ∃ S ≤ A, 1 - δ < (S.map (fun n : ℕ => (n : ℝ)⁻¹)).sum ∧
        (S.map (fun n : ℕ => (n : ℝ)⁻¹)).sum ≤ 1 := by
  classical
  let P := A.filter Nat.Prime
  let C := A.filter (fun n => ¬Nat.Prime n)
  have hPsub : P ≤ A := Multiset.filter_le _ _
  have hCsub : C ≤ A := Multiset.filter_le _ _
  have hsplit : P + C = A := Multiset.filter_add_not _ _
  have hsplitMass :
      (P.map (fun n : ℕ => (n : ℝ)⁻¹)).sum + (C.map (fun n : ℕ => (n : ℝ)⁻¹)).sum =
      (A.map (fun n : ℕ => (n : ℝ)⁻¹)).sum := by
    rw [← Multiset.sum_add, ← Multiset.map_add, hsplit]
  by_cases hpM : L < (P.map (fun n : ℕ => (n : ℝ)⁻¹)).sum
  · have hPden : ∀ n ∈ P, Nat.Prime n := fun n hn => (Multiset.mem_filter.mp hn).2
    have hPstable : ∀ n ∈ P, ∀ p : ℕ, Nat.Prime p → p ∣ n → P.count n < p := by
      intro n hn p hp hd
      exact lt_of_le_of_lt (Multiset.count_le_of_le n hPsub)
        (hstable n (Multiset.mem_of_le hPsub hn) p hp hd)
    obtain ⟨S,hS,hlo,hup⟩ := HP P hPden hPstable hpM
    exact ⟨S,hS.trans hPsub,hlo,hup⟩
  · have hcM : L < (C.map (fun n : ℕ => (n : ℝ)⁻¹)).sum := by
      by_contra hn
      have hh := add_le_add (le_of_not_gt hpM) (le_of_not_gt hn)
      rw [hsplitMass] at hh
      exact (not_le_of_gt hmass) hh
    have hCden : ∀ n ∈ C, 2 ≤ n ∧ ¬ Nat.Prime n := fun n hn =>
      ⟨hden n (Multiset.mem_of_le hCsub hn), (Multiset.mem_filter.mp hn).2⟩
    have hCstable : ∀ n ∈ C, ∀ p : ℕ, Nat.Prime p → p ∣ n → C.count n < p := by
      intro n hn p hp hd
      exact lt_of_le_of_lt (Multiset.count_le_of_le n hCsub)
        (hstable n (Multiset.mem_of_le hCsub hn) p hp hd)
    obtain ⟨S,hS,hlo,hup⟩ := HC C hCden hCstable hcM
    exact ⟨S,hS.trans hCsub,hlo,hup⟩


open BigOperators

theorem lift_submultiset {ι : Type*} [DecidableEq ι] (a : ι → ℕ) (T : Finset ι)
    (B : Multiset ℕ) (hB : B ≤ T.val.map a) :
    ∃ S : Finset ι, S ⊆ T ∧ S.val.map a = B := by
  induction T using Finset.induction_on generalizing B with
  | empty =>
    simp at hB
    exact ⟨∅, by simp, by simp [hB]⟩
  | @insert i T hi ih =>
    rw [Finset.insert_val_of_notMem hi, Multiset.map_cons] at hB
    by_cases hb : a i ∈ B
    · have hh : B.erase (a i) ≤ T.val.map a := Multiset.erase_le_iff_le_cons.mpr hB
      obtain ⟨S, hs, heq⟩ := ih (B.erase (a i)) hh
      have hiS : i ∉ S := fun h => hi (hs h)
      refine ⟨insert i S, ?_, ?_⟩
      · exact Finset.insert_subset_insert i hs
      · rw [Finset.insert_val_of_notMem hiS, Multiset.map_cons, heq,
          Multiset.cons_erase hb]
    · have hh : B ≤ T.val.map a := (Multiset.le_cons_of_notMem hb).mp hB
      obtain ⟨S, hs, heq⟩ := ih B hh
      exact ⟨S, hs.trans (Finset.subset_insert i T), heq⟩

theorem mass_map_eq_sum {ι : Type*} (a : ι → ℕ) (S : Finset ι) :
    ((S.val.map a).map (fun n : ℕ => (n : ℝ)⁻¹)).sum = ∑ i ∈ S, (a i : ℝ)⁻¹ := by
  simp only [Multiset.map_map]
  rfl

theorem filter_positive_mass (A : Multiset ℕ) :
    ((A.filter (fun n => 0 < n)).map (fun n : ℕ => (n : ℝ)⁻¹)).sum = ((A).map (fun n : ℕ => (n : ℝ)⁻¹)).sum := by
  induction A using Multiset.induction_on with
  | empty => simp
  | cons n A ih =>
    by_cases h : 0 < n
    · rw [Multiset.filter_cons_of_pos _ h]
      simp [ih]
    · have hz : n = 0 := by omega
      subst n
      simp [ih]

/-- For each choice of tolerance and budget, the prime-only and composite-only
    stable cases together suffice for all multisets of twice the mass budget. -/
theorem packing_reduction (L δ : ℝ) (hδ : 0 < δ)
    (HP : ∀ P : Multiset ℕ, (∀ n ∈ P, Nat.Prime n) →
      (∀ n ∈ P, ∀ p : ℕ, Nat.Prime p → p ∣ n → P.count n < p) →
      L < (P.map (fun n : ℕ => (n : ℝ)⁻¹)).sum →
      ∃ S ≤ P, 1 - δ < (S.map (fun n : ℕ => (n : ℝ)⁻¹)).sum ∧
        (S.map (fun n : ℕ => (n : ℝ)⁻¹)).sum ≤ 1)
    (HC : ∀ C : Multiset ℕ, (∀ n ∈ C, 2 ≤ n ∧ ¬ Nat.Prime n) →
      (∀ n ∈ C, ∀ p : ℕ, Nat.Prime p → p ∣ n → C.count n < p) →
      L < (C.map (fun n : ℕ => (n : ℝ)⁻¹)).sum →
      ∃ S ≤ C, 1 - δ < (S.map (fun n : ℕ => (n : ℝ)⁻¹)).sum ∧
        (S.map (fun n : ℕ => (n : ℝ)⁻¹)).sum ≤ 1)
    (A : Multiset ℕ) (hA : L + L < ((A).map (fun n : ℕ => (n : ℝ)⁻¹)).sum) :
    ∃ S ≤ A, 1 - δ < ((S).map (fun n : ℕ => (n : ℝ)⁻¹)).sum ∧ ((S).map (fun n : ℕ => (n : ℝ)⁻¹)).sum ≤ 1 := by
  classical
  let B := A.filter (fun n => 0 < n)
  let N : ℝ := (B.sum : ℝ) + 1
  have hB : ∀ n ∈ B, 0 < n ∧ (n : ℝ) < N := by
    intro n hn
    refine ⟨(Multiset.mem_filter.mp hn).2, ?_⟩
    have hsum : n ≤ B.sum := by
      obtain ⟨C, hC⟩ := Multiset.le_iff_exists_add.mp (Multiset.singleton_le.mpr hn)
      rw [hC, Multiset.sum_add, Multiset.sum_singleton]
      exact Nat.le_add_right n _
    exact (Nat.cast_le.mpr hsum).trans_lt (lt_add_of_pos_right _ zero_lt_one)
  obtain ⟨C,hC,hmass,hStable,hLift⟩ := compression_exists B N hB
  have hm : L + L < (C.map (fun n : ℕ => (n : ℝ)⁻¹)).sum := by
    rw [hmass]
    simpa [B, filter_positive_mass] using hA
  have hBsub : B ≤ A := Multiset.filter_le _ _
  by_cases hOne : 1 ∈ C
  · have hU : ({1} : Multiset ℕ) ≤ C := Multiset.singleton_le.mpr hOne
    obtain ⟨S,hS,hEq⟩ := hLift {1} hU
    have hs1 : ((S).map (fun n : ℕ => (n : ℝ)⁻¹)).sum = 1 := by
      rw [hEq]
      simp
    exact ⟨S,hS.trans hBsub,by rw [hs1]; exact sub_lt_self _ hδ,by rw [hs1]⟩
  · have hden : ∀ n ∈ C, 2 ≤ n := by
      intro n hn
      have hp := (hC n hn).1
      have hne : n ≠ 1 := fun h => hOne (h ▸ hn)
      omega
    have hStable' : ∀ n ∈ C, ∀ p : ℕ, Nat.Prime p → p ∣ n → C.count n < p := by
      intro n hn p hp hd
      exact hStable n p hp.two_le hd
    obtain ⟨U,hU,hlo,hup⟩ := stable_partition C L δ hden hStable' hm HP HC
    obtain ⟨S,hS,hEq⟩ := hLift U hU
    exact ⟨S,hS.trans hBsub,by rw [hEq]; exact hlo,by rw [hEq]; exact hup⟩

/-- Indexed version of the reduction, matching the finite family in the problem. -/
theorem indexed_packing_reduction (L δ : ℝ) (hδ : 0 < δ)
    (HP : ∀ P : Multiset ℕ, (∀ n ∈ P, Nat.Prime n) →
      (∀ n ∈ P, ∀ p : ℕ, Nat.Prime p → p ∣ n → P.count n < p) →
      L < (P.map (fun n : ℕ => (n : ℝ)⁻¹)).sum →
      ∃ S ≤ P, 1 - δ < (S.map (fun n : ℕ => (n : ℝ)⁻¹)).sum ∧
        (S.map (fun n : ℕ => (n : ℝ)⁻¹)).sum ≤ 1)
    (HC : ∀ C : Multiset ℕ, (∀ n ∈ C, 2 ≤ n ∧ ¬ Nat.Prime n) →
      (∀ n ∈ C, ∀ p : ℕ, Nat.Prime p → p ∣ n → C.count n < p) →
      L < (C.map (fun n : ℕ => (n : ℝ)⁻¹)).sum →
      ∃ S ≤ C, 1 - δ < (S.map (fun n : ℕ => (n : ℝ)⁻¹)).sum ∧
        (S.map (fun n : ℕ => (n : ℝ)⁻¹)).sum ≤ 1)
    (n : ℕ) (a : Fin n → ℕ) (htotal : L + L < ∑ i, (a i : ℝ)⁻¹) :
    ∃ S : Finset (Fin n), 1 - δ < ∑ i ∈ S, (a i : ℝ)⁻¹ ∧
      ∑ i ∈ S, (a i : ℝ)⁻¹ ≤ 1 := by
  classical
  have hm : L + L < (((Finset.univ : Finset (Fin n)).val.map a).map (fun n : ℕ => (n : ℝ)⁻¹)).sum := by
    rw [mass_map_eq_sum]
    exact htotal
  obtain ⟨B,hB,hlo,hup⟩ := packing_reduction L δ hδ HP HC (Finset.univ.val.map a) hm
  obtain ⟨S,hS,hEq⟩ := lift_submultiset a Finset.univ B hB
  refine ⟨S,?_,?_⟩
  · rw [← mass_map_eq_sum,hEq]; exact hlo
  · rw [← mass_map_eq_sum,hEq]; exact hup




private lemma greedy {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℝ)
    (δ : ℝ) (hδ : 0 < δ) (hf : ∀ i ∈ s, f i ≤ δ) (z : ℝ)
    (hz : 0 ≤ z) (hs : z ≤ ∑ i ∈ s, f i) :
    ∃ t ⊆ s, z - δ < ∑ i ∈ t, f i ∧ ∑ i ∈ t, f i ≤ z := by
  induction s using Finset.induction_on generalizing z with
  | empty =>
    simp only [Finset.sum_empty] at hs
    exact ⟨∅, (by simp), by simpa using sub_neg.mpr (hs.trans_lt hδ), by simpa using hz⟩
  | @insert a s ha ih =>
    by_cases h : z < f a
    · exact ⟨∅, Finset.empty_subset _, by simpa using sub_neg.mpr (h.trans_le (hf a (Finset.mem_insert_self _ _))), by simpa using hz⟩
    · have ht : ∀ i ∈ s, f i ≤ δ := fun i hi => hf i (Finset.mem_insert_of_mem hi)
      have hs' : z - f a ≤ ∑ i ∈ s, f i := by
        rw [Finset.sum_insert ha] at hs
        exact sub_le_iff_le_add.mpr (by simpa only [add_comm] using hs)
      obtain ⟨t, ht', htl, htu⟩ := ih ht (z - f a) (sub_nonneg.mpr (le_of_not_gt h)) hs'
      have hna : a ∉ t := fun hmem => ha (ht' hmem)
      refine ⟨insert a t, Finset.insert_subset_insert _ ht', ?_, ?_⟩
      · rw [Finset.sum_insert hna]
        have hp := add_lt_add_right htl (f a)
        have heq : f a + (z - f a - δ) = z - δ := by
          rw [← add_sub_assoc, ← add_sub_assoc, add_sub_cancel_left]
        rwa [heq] at hp
      · rw [Finset.sum_insert hna]
        simpa only [add_comm] using (le_sub_iff_add_le.mp htu)

/-- Uniformly for all finite indexed families of total mass >1, find a
    reciprocal subsum in (1/2,1]. -/
theorem near_half (n : ℕ) (a : Fin n → ℕ) (ht : 1 < ∑ i, (a i : ℝ)⁻¹) :
    ∃ S : Finset (Fin n), (1/2 : ℝ) < ∑ i ∈ S, (a i : ℝ)⁻¹ ∧
      ∑ i ∈ S, (a i : ℝ)⁻¹ ≤ 1 := by
  classical
  by_cases hone : ∃ i : Fin n, a i = 1
  · obtain ⟨i, hi⟩ := hone
    refine ⟨{i}, ?_, ?_⟩ <;> norm_num [hi]
  have hf : ∀ i ∈ (Finset.univ : Finset (Fin n)), (a i : ℝ)⁻¹ ≤ 1/2 := by
    intro i hi
    by_cases hz : a i = 0
    · norm_num [hz]
    have hn : 2 ≤ a i := by
      have hne : a i ≠ 1 := fun h => hone ⟨i,h⟩
      omega
    simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 2) (Nat.cast_le.mpr hn)
  obtain ⟨S, _, hS, hS'⟩ := greedy Finset.univ (fun i => (a i : ℝ)⁻¹)
    (1/2) (by norm_num) hf 1 zero_le_one (le_of_lt ht)
  norm_num at hS
  exact ⟨S, hS, hS'⟩

theorem main : H1 → H2 → type_of% @Erdos312.erdos_312 := by
  intro h1 h2
  obtain ⟨cP,hcP,HP⟩ := h1
  obtain ⟨cC,hcC,HC⟩ := h2
  let c := min (min cP cC / 2) (1/8)
  have hc : 0 < c := lt_min (half_pos (lt_min hcP hcC)) (by norm_num)
  have hcP' : c ≤ cP / 2 := (min_le_left _ _).trans
    (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
  have hcC' : c ≤ cC / 2 := (min_le_left _ _).trans
    (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))
  have hc8 : c ≤ 1/8 := min_le_right _ _
  refine ⟨c,hc,fun K hK => ⟨0,?_⟩⟩
  intro n a ha
  have hKpos : 0 < K := zero_lt_one.trans hK
  by_cases hsmall : K ≤ 2
  · obtain ⟨S,hS,hS'⟩ := near_half n a (hK.trans ha.2)
    have hprod : c * K ≤ 1/2 := by
      calc
        _ ≤ (1/8)*K := mul_le_mul_of_nonneg_right hc8 hKpos.le
        _ ≤ (1/8)*2 := mul_le_mul_of_nonneg_left hsmall (by norm_num)
        _ ≤ _ := by norm_num
    have hexp : (1/2 : ℝ) ≤ Real.exp (-(c*K)) := by
      have hp := neg_le_neg hprod
      calc
        _ = -(1/2 : ℝ) + 1 := by norm_num
        _ ≤ -(c*K) + 1 := add_le_add_left hp _
        _ ≤ _ := Real.add_one_le_exp _
    have hsub : 1 - Real.exp (-(c*K)) ≤ (1/2 : ℝ) := by
      calc
        _ ≤ 1 - (1/2 : ℝ) := sub_le_sub_left hexp _
        _ = _ := by norm_num
    exact ⟨S,hsub.trans_lt hS,hS'⟩
  have hK2 : 1 < K / 2 := (lt_div_iff₀ (by norm_num)).mpr
    (by simpa using lt_of_not_ge hsmall)
  have hPprod : c * K ≤ cP * (K/2) := by
    rw [← mul_div_assoc, ← div_mul_eq_mul_div₀]
    exact mul_le_mul_of_nonneg_right hcP' hKpos.le
  have hCprod : c * K ≤ cC * (K/2) := by
    rw [← mul_div_assoc, ← div_mul_eq_mul_div₀]
    exact mul_le_mul_of_nonneg_right hcC' hKpos.le
  have hPerr : Real.exp (-(cP*(K/2))) ≤ Real.exp (-(c*K)) :=
    Real.exp_le_exp.mpr (neg_le_neg hPprod)
  have hCerr : Real.exp (-(cC*(K/2))) ≤ Real.exp (-(c*K)) :=
    Real.exp_le_exp.mpr (neg_le_neg hCprod)
  apply indexed_packing_reduction (K/2) _ (Real.exp_pos _)
  · intro P hPden hPstable hPm
    obtain ⟨S,hS,hlo,hup⟩ := HP (K/2) hK2 P hPden hPstable hPm
    exact ⟨S,hS,(sub_le_sub_left hPerr 1).trans_lt hlo,hup⟩
  · intro C hCden hCstable hCm
    obtain ⟨S,hS,hlo,hup⟩ := HC (K/2) hK2 C hCden hCstable hCm
    exact ⟨S,hS,(sub_le_sub_left hCerr 1).trans_lt hlo,hup⟩
  · rw [add_halves]; exact ha.2


end OMA.R_Erdos312_erdos_312_R1
