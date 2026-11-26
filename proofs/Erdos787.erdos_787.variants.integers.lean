import FormalConjectures.ErdosProblems.«787»
import Mathlib.Algebra.Module.Submodule.Union

/-! Finite real sets admit integer models for their two-term additive relations. -/

open Erdos787

lemma OMA.klarner_integer_model (A : Finset ℝ) :
    ∃ F : ℝ → ℤ, Set.InjOn F (A : Set ℝ) ∧
      ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, F a + F b = F c ↔ a + b = c := by
  classical
  let P : Finset ℝ := (A.product A).image fun ab => ab.1 - ab.2
  let Q : Finset ℝ := (A.product (A.product A)).image fun abc => abc.1 + abc.2.1 - abc.2.2
  let D := (P ∪ Q).erase 0
  have hD (v : D) : (v : ℝ) ≠ 0 := (Finset.mem_erase.mp v.property).1
  obtain ⟨f, hf⟩ := Module.exists_dual_forall_apply_ne_zero (K := ℚ)
    (fun v : D => (v : ℝ)) hD
  let d : ℕ := ∏ a ∈ A, (f a).den
  have hdn : 0 < d := Finset.prod_pos fun a _ => Rat.pos (f a)
  have hd : (d : ℚ) ≠ 0 := by exact_mod_cast hdn.ne'
  let F (a : ℝ) : ℤ := ((d / (f a).den : ℕ) : ℤ) * (f a).num
  have hF (a : ℝ) (ha : a ∈ A) : (F a : ℚ) = (d : ℚ) * f a := by
    have hdvd : (f a).den ∣ d := Finset.dvd_prod_of_mem (fun x => (f x).den) ha
    have hmul : ((d / (f a).den : ℕ) : ℚ) * ((f a).den : ℚ) = (d : ℚ) := by
      exact_mod_cast Nat.div_mul_cancel hdvd
    have ha₀ : ((f a).den : ℚ) ≠ 0 := by exact_mod_cast Rat.den_nz (f a)
    have hnum : ((f a).den : ℚ) * f a = ((f a).num : ℚ) := by
      calc
        ((f a).den : ℚ) * f a = (((f a).num : ℚ) / ((f a).den : ℚ)) * ((f a).den : ℚ) := by
          rw [Rat.num_div_den, mul_comm]
        _ = _ := div_mul_cancel₀ _ ha₀
    calc
      (F a : ℚ) = ((d / (f a).den : ℕ) : ℚ) * ((f a).num : ℚ) := by
        simp only [F, Int.cast_mul, Int.cast_natCast]
      _ = ((d / (f a).den : ℕ) : ℚ) * (((f a).den : ℚ) * f a) := by rw [hnum]
      _ = (d : ℚ) * f a := by rw [← mul_assoc, hmul]
  refine ⟨F, ?_, ?_⟩
  · intro a ha b hb heq
    by_contra hab
    have hmemP : a - b ∈ P := Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩
    have hmem : a - b ∈ D := Finset.mem_erase.mpr ⟨sub_ne_zero.mpr hab, Finset.mem_union_left _ hmemP⟩
    have hq := congrArg (fun z : ℤ => (z : ℚ)) heq
    rw [hF a ha, hF b hb] at hq
    have hfab : f a = f b := mul_left_cancel₀ hd hq
    have hnot : f (a - b) ≠ 0 := hf ⟨a - b, hmem⟩
    exact hnot (by rw [map_sub, hfab, sub_self])
  · intro a ha b hb c hc
    have he : ((F a + F b : ℤ) : ℚ) = (d : ℚ) * f (a + b) := by
      rw [Int.cast_add, hF a ha, hF b hb, map_add, mul_add]
    constructor
    · intro h
      by_contra hABC
      have hmemQ : a + b - c ∈ Q := Finset.mem_image.mpr
        ⟨(a, b, c), Finset.mem_product.mpr ⟨ha, Finset.mem_product.mpr ⟨hb, hc⟩⟩, rfl⟩
      have hmem : a + b - c ∈ D :=
        Finset.mem_erase.mpr ⟨sub_ne_zero.mpr hABC, Finset.mem_union_right _ hmemQ⟩
      have hq := congrArg (fun z : ℤ => (z : ℚ)) h
      rw [he, hF c hc] at hq
      have hfc : f (a + b) = f c := mul_left_cancel₀ hd hq
      have hnot : f (a + b - c) ≠ 0 := hf ⟨_, hmem⟩
      exact hnot (by rw [map_sub, hfc, sub_self])
    · intro h
      apply Rat.intCast_injective
      rw [he, hF c hc, h]

lemma OMA.klarner_problem_bounded (G : Type*) [Add G] [DecidableEq G] [Infinite G] (n : ℕ) :
    BddAbove {m : ℕ | ∀ A : Finset G, A.card = n →
      ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A} := by
  refine ⟨n, ?_⟩
  intro m hm
  obtain ⟨A, hA⟩ := Infinite.exists_subset_card_eq G n
  obtain ⟨B, hB, hcard, _⟩ := hm A hA
  exact hcard.trans ((Finset.card_le_card hB).trans_eq hA)

lemma OMA.klarner_attained (G : Type*) [Add G] [DecidableEq G] [Infinite G] (n : ℕ) :
    ∀ A : Finset G, A.card = n →
      ∃ B ⊆ A, g G n ≤ B.card ∧ Disjoint B.restrictedSumset A := by
  have hne : ({m : ℕ | ∀ A : Finset G, A.card = n →
      ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A}).Nonempty := by
    refine ⟨0, ?_⟩
    intro A _
    exact ⟨∅, Finset.empty_subset _, Nat.zero_le _, by simp [Finset.restrictedSumset]⟩
  exact Nat.sSup_mem hne (OMA.klarner_problem_bounded G n)

lemma OMA.klarner_pullback {G H : Type*} [Add G] [Add H] [DecidableEq G] [DecidableEq H]
    (A : Finset G) (f : G → H) (hf : Set.InjOn f (A : Set G))
    (hadd : ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, f a + f b = f c ↔ a + b = c)
    (C : Finset H) (hC : C ⊆ A.image f) (hfree : Disjoint C.restrictedSumset (A.image f)) :
    ∃ B ⊆ A, C.card = B.card ∧ Disjoint B.restrictedSumset A := by
  let B := A.filter (fun a => f a ∈ C)
  have hBA : B ⊆ A := Finset.filter_subset _ _
  have hBC : B.image f = C := by
    ext c
    constructor
    · intro hc
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hc
      exact (Finset.mem_filter.mp hb).2
    · intro hc
      obtain ⟨a, ha, he⟩ := Finset.mem_image.mp (hC hc)
      exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, he.symm ▸ hc⟩, he⟩
  refine ⟨B, hBA, ?_, ?_⟩
  · rw [← hBC]
    exact Finset.card_image_of_injOn (hf.mono (Finset.coe_subset.mpr hBA))
  · apply (disjoint_restrictedSumset_iff A B).mpr
    intro a ha b hb hne hsum
    obtain ⟨haA, haC⟩ := Finset.mem_filter.mp ha
    obtain ⟨hbA, hbC⟩ := Finset.mem_filter.mp hb
    have hne' : f a ≠ f b := fun h => hne (hf haA hbA h)
    have hsum' : f a + f b ∈ A.image f := Finset.mem_image.mpr
      ⟨a + b, hsum, ((hadd a haA b hbA (a + b) hsum).mpr rfl).symm⟩
    exact (disjoint_restrictedSumset_iff (A.image f) C).mp hfree (f a) haC (f b) hbC hne' hsum'

theorem OMA.solution : type_of% @Erdos787.erdos_787.variants.integers := by
  intro n
  apply le_antisymm
  · apply le_g
    intro A hA
    obtain ⟨f, hfinj, hfadd⟩ := OMA.klarner_integer_model A
    have hsize : (A.image f).card = n := (Finset.card_image_of_injOn hfinj).trans hA
    obtain ⟨C, hC, hcard, hfree⟩ := OMA.klarner_attained ℤ n (A.image f) hsize
    obtain ⟨B, hB, hBC, hBfree⟩ := OMA.klarner_pullback A f hfinj hfadd C hC hfree
    exact ⟨B, hB, hcard.trans_eq hBC, hBfree⟩
  · apply le_csSup (OMA.klarner_problem_bounded ℤ n)
    intro A hA
    let f (a : ℤ) : ℝ := (a : ℝ)
    have hfinj : Set.InjOn f (A : Set ℤ) := Int.cast_injective.injOn
    have hfadd (a : ℤ) (_ : a ∈ A) (b : ℤ) (_ : b ∈ A) (c : ℤ) (_ : c ∈ A) :
        f a + f b = f c ↔ a + b = c := by
      change (a : ℝ) + (b : ℝ) = (c : ℝ) ↔ a + b = c
      rw [← Int.cast_add, Int.cast_inj]
    have hsize : (A.image f).card = n := (Finset.card_image_of_injOn hfinj).trans hA
    obtain ⟨C, hC, hcard, hfree⟩ := OMA.klarner_attained ℝ n (A.image f) hsize
    obtain ⟨B, hB, hBC, hBfree⟩ := OMA.klarner_pullback A f hfinj hfadd C hC hfree
    exact ⟨B, hB, hcard.trans_eq hBC, hBfree⟩