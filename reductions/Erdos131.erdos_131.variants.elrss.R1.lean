import FormalConjectures.ErdosProblems.«131»
import Mathlib.Algebra.Order.Chebyshev

/-!
The least element of a non-dividing set is the modulus. Partition the
other elements by their integer quotient, so each class has distinct
residues. Apply Olson to each class and apply Scherk–Kemperman to their
sets of subset sums. See Erdős, Lev, Rauzy, Sándor and Sárközy, 1999,
Theorem 3 and Corollary 1.
-/

-- Credit: @dk8827

open Finset
open scoped BigOperators Classical

namespace OMA.R_Erdos131_erdos_131_variants_elrss_R1

/-- Olson's quadratic bound for a zero-sum-free set. -/
def H1 : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ R : Finset (ZMod n),
    (∀ T ⊆ R, T.Nonempty → ∑ x ∈ T, x ≠ 0) →
    R.card ^ 2 ≤ 9 * ((R.powerset.image fun T => ∑ x ∈ T, x).card - 1)

/-- The iterated Scherk–Kemperman bound applied to the cyclic group's capacity. -/
def H2 : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (J : Finset ℕ) (S : ℕ → Finset (ZMod n)),
    (∀ j ∈ J, (0 : ZMod n) ∈ S j) →
    (∀ f : ℕ → ZMod n, (∀ j ∈ J, f j ∈ S j) →
      (∑ j ∈ J, f j) = 0 → ∀ j ∈ J, f j = 0) →
    (∑ j ∈ J, ((S j).card - 1)) + 1 ≤ n

set_option maxHeartbeats 2000000 in
theorem main : H1 → H2 → type_of% @Erdos131.erdos_131.variants.elrss := by
  classical
  intro olson capacity N
  obtain ⟨A, hA, hnd, hmax⟩ := Erdos131.exists_card_eq_F N
  by_cases hAn : A.Nonempty
  swap
  · rw [← hmax, not_nonempty_iff_eq_empty.1 hAn]
    simp only [card_empty, Nat.cast_zero]
    positivity
  let a := A.min' hAn
  have haA : a ∈ A := A.min'_mem hAn
  have haN := mem_Icc.1 (hA haA)
  have ha : 0 < a := by omega
  have hN : 0 < N := ha.trans_le haN.2
  let B := A.erase a
  let J := Icc 1 (N / a)
  let P (j : ℕ) := B.filter fun x => x / a = j
  let R (j : ℕ) := (P j).image (fun x : ℕ => (x : ZMod a))
  let S (j : ℕ) := ((P j).powerset).image fun (U : Finset ℕ) => ∑ x ∈ U, (x : ZMod a)
  have hBa (x : ℕ) (hx : x ∈ B) : a ≤ x := A.min'_le _ (mem_of_mem_erase hx)
  have cast_inj (j : ℕ) : Set.InjOn (fun x : ℕ => (x : ZMod a)) (P j : Set ℕ) := by
    intro x hx y hy he
    have hm := congrArg ZMod.val he
    simp only [ZMod.val_natCast] at hm
    have hx' := (mem_filter.1 hx).2
    have hy' := (mem_filter.1 hy).2
    have hxd := Nat.mod_add_div x a
    have hyd := Nat.mod_add_div y a
    rw [hx'] at hxd
    rw [hy'] at hyd
    omega
  have hull (U : Finset ℕ) (hU : U ⊆ B) (hz : (∑ x ∈ U, (x : ZMod a)) = 0) :
      U = ∅ := by
    by_contra hne
    apply hnd a haA U hU (nonempty_iff_ne_empty.mpr hne)
    apply (ZMod.natCast_eq_zero_iff _ _).1
    simpa only [Nat.cast_sum] using hz
  have hOl (j : ℕ) : (P j).card ^ 2 ≤ 9 * ((S j).card - 1) := by
    let G := fun U : Finset (ZMod a) => ∑ x ∈ U, x
    have hL (T : Finset (ZMod a)) (hT : T ⊆ R j) :
        ∃ U ⊆ P j, U.image (fun x : ℕ => (x : ZMod a)) = T := by
      refine ⟨(P j).filter (fun x : ℕ => (x : ZMod a) ∈ T), filter_subset _ _, ?_⟩
      ext t
      constructor
      · intro hh
        obtain ⟨x, hx, rfl⟩ := mem_image.1 hh
        exact (mem_filter.1 hx).2
      · intro ht
        obtain ⟨x, hx, rfl⟩ := mem_image.1 (hT ht)
        exact mem_image.2 ⟨x, mem_filter.2 ⟨hx, ht⟩, rfl⟩
    have hsum (U : Finset ℕ) (hU : U ⊆ P j) :
        G (U.image (fun x : ℕ => (x : ZMod a))) = ∑ x ∈ U, (x : ZMod a) := by
      exact sum_image (fun x hx y hy h => cast_inj j (hU hx) (hU hy) h)
    have hR : (R j).card = (P j).card := card_image_of_injOn (cast_inj j)
    have hzero (T : Finset (ZMod a)) (hT : T ⊆ R j) (hTne : T.Nonempty) :
        G T ≠ 0 := by
      obtain ⟨U, hU, hUT⟩ := hL T hT
      intro h
      have h' := hsum U hU
      rw [hUT, h] at h'
      have he := hull U (hU.trans (filter_subset _ _)) h'.symm
      simp [he] at hUT
      exact hTne.ne_empty hUT.symm
    have hSet : (R j).powerset.image G = S j := by
      ext t
      constructor
      · intro ht
        obtain ⟨T, hT, rfl⟩ := mem_image.1 ht
        obtain ⟨U, hU, hUT⟩ := hL T (mem_powerset.1 hT)
        refine mem_image.2 ⟨U, mem_powerset.2 hU, ?_⟩
        rw [← hsum U hU, hUT]
      · intro ht
        obtain ⟨U, hU, rfl⟩ := mem_image.1 ht
        have hU' := mem_powerset.1 hU
        refine mem_image.2 ⟨U.image (fun x : ℕ => (x : ZMod a)), mem_powerset.2 ?_, hsum U hU'⟩
        exact image_subset_image hU'
    have h := olson a ha (R j) hzero
    change (R j).card ^ 2 ≤ 9 * (((R j).powerset.image G).card - 1) at h
    simpa only [hR, hSet] using h
  have hS0 (j : ℕ) (_ : j ∈ J) : (0 : ZMod a) ∈ S j :=
    mem_image.2 ⟨∅, empty_mem_powerset _, by simp⟩
  have hUnique (f : ℕ → ZMod a) (hf : ∀ j ∈ J, f j ∈ S j)
      (hf0 : (∑ j ∈ J, f j) = 0) : ∀ j ∈ J, f j = 0 := by
    have hSub (j : ℕ) : j ∈ J → ∃ T ⊆ P j, (∑ x ∈ T, (x : ZMod a)) = f j := by
      intro hj
      obtain ⟨T, hT, hEq⟩ := mem_image.1 (hf j hj)
      exact ⟨T, mem_powerset.1 hT, hEq⟩
    have hChoose (j : ℕ) : ∃ T : Finset ℕ, T ⊆ P j ∧
        (j ∈ J → (∑ x ∈ T, (x : ZMod a)) = f j) := by
      by_cases hj : j ∈ J
      · obtain ⟨T, hT, hEq⟩ := hSub j hj
        exact ⟨T, hT, fun _ => hEq⟩
      · exact ⟨∅, empty_subset _, fun hh => (hj hh).elim⟩
    choose T hT hsum using hChoose
    let U := J.biUnion T
    have hdis : (J : Set ℕ).PairwiseDisjoint T := by
      intro i hi j hj hij
      apply disjoint_left.2
      intro x hxi hxj
      exact hij ((mem_filter.1 (hT i hxi)).2.symm.trans (mem_filter.1 (hT j hxj)).2)
    have hUB : U ⊆ B := by
      intro x hx
      obtain ⟨j, _, hxT⟩ := mem_biUnion.1 hx
      exact (mem_filter.1 (hT j hxT)).1
    have hU0 : (∑ x ∈ U, (x : ZMod a)) = 0 := by
      rw [show U = J.biUnion T from rfl, sum_biUnion hdis]
      exact (sum_congr rfl hsum).trans hf0
    have hUempty := hull U hUB hU0
    intro j hj
    have hTempty : T j = ∅ := by
      apply eq_empty_iff_forall_notMem.2
      intro x hx
      have hxU : x ∈ U := mem_biUnion.2 ⟨j, hj, hx⟩
      simp [hUempty] at hxU
    simpa [hTempty] using (hsum j hj).symm
  have hcap := capacity a ha J S hS0 hUnique
  have hJ : J.card = N / a := by simp [J, Nat.card_Icc]
  have hBcard : B.card = ∑ j ∈ J, (P j).card := by
    apply card_eq_sum_card_fiberwise (f := fun x => x / a)
    intro x hx
    exact mem_Icc.2 ⟨(Nat.le_div_iff_mul_le ha).2 (by simpa only [one_mul] using hBa x hx),
      Nat.div_le_div_right (mem_Icc.1 (hA (mem_of_mem_erase hx))).2⟩
  have hsum : (∑ j ∈ J, (P j).card ^ 2) ≤ 9 * (a - 1) := by
    calc
      _ ≤ ∑ j ∈ J, 9 * ((S j).card - 1) := sum_le_sum fun j _ => hOl j
      _ = 9 * (∑ j ∈ J, ((S j).card - 1)) := (mul_sum ..).symm
      _ ≤ _ := Nat.mul_le_mul_left 9 (by omega)
  have hsq : B.card ^ 2 < 9 * N := by
    have hq : 0 < N / a := Nat.div_pos haN.2 ha
    have hlt : (N / a) * (a - 1) < N := by
      exact (Nat.mul_lt_mul_of_pos_left (by omega : a - 1 < a) hq).trans_le
        (Nat.div_mul_le_self N a)
    calc
      _ ≤ J.card * (∑ j ∈ J, (P j).card ^ 2) := by
        rw [hBcard]
        exact sq_sum_le_card_mul_sum_sq (s := J) (f := fun j => (P j).card)
      _ ≤ (N / a) * (9 * (a - 1)) := by rw [hJ]; exact Nat.mul_le_mul_left _ hsum
      _ = 9 * ((N / a) * (a - 1)) := by ring
      _ < _ := Nat.mul_lt_mul_of_pos_left hlt (by decide)
  have hsq' : (B.card : ℝ) ^ 2 < 9 * (N : ℝ) := by exact_mod_cast hsq
  have hBlt : (B.card : ℝ) < 3 * Real.sqrt N := by
    have hm : (3 * Real.sqrt (N : ℝ)) ^ 2 = 9 * (N : ℝ) := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]; norm_num
    apply lt_of_pow_lt_pow_left₀ 2 (by positivity)
    rwa [hm]
  have haSize : B.card + 1 = Erdos131.F N := (card_erase_add_one haA).trans hmax
  rw [← haSize, Nat.cast_add, Nat.cast_one]
  linarith only [hBlt]

end OMA.R_Erdos131_erdos_131_variants_elrss_R1
