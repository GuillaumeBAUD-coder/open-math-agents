import FormalConjectures.ErdosProblems.«757»

-- Reduction Erdos757.erdos_757.variants.lowerBound.R1 of Erdős Problem 757 — lowerBound
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/757.lean (declaration Erdos757.erdos_757.variants.lowerBound)
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
-- Source: Gyárfás and Lehel, Linear sets with five distinct differences among any four elements,
-- J. Combin. Theory Ser. B (1995). No new result is claimed.
--
-- Split.
--   H1 (the combinatorial heart, Gyárfás–Lehel, for finite sets of integers, in 3-AP-free form):
--      there is c > 1/2 such that every finite set of integers in which every 4-subset determines
--      at least five distinct positive differences contains a 3-AP-free subset of size at least c|A|.
--   H2 (Freiman-type transfer to the integers): for every finite A ⊆ ℝ there is an additive map
--      f : ℝ →+ ℝ, injective on A - A, sending A into ℤ.
-- Proved here (main):
--   * the difference condition forbids a + b = c + d with a, b, c, d distinct (B - B would have
--     at most 9 elements), so inside such a set a 3-AP-free subset is automatically Sidon;
--   * the difference condition, Sidon sets and cardinalities transfer along f;
--   * the admissible constants are bounded above by 1 (take A a singleton), so sSup > 1/2.

namespace OMA.R_Erdos757_erdos_757_variants_lowerBound_R1

open scoped Pointwise

/-- Gyárfás–Lehel, integer sets, 3-AP-free form. -/
def H1 : Prop := ∃ c : ℝ, 1 / 2 < c ∧ ∀ A : Set ℝ, A.Finite → A ⊆ Set.range ((↑) : ℤ → ℝ) →
  (∀ B ⊆ A, B.ncard = 4 → 11 ≤ (B - B).ncard) →
  ∃ S ⊆ A, (∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x + z = 2 * y → x = z) ∧ c * A.ncard ≤ (S.ncard : ℝ)

/-- Transfer of a finite set of reals to the integers by an additive map injective on A - A. -/
def H2 : Prop := ∀ A : Set ℝ, A.Finite →
  ∃ f : ℝ →+ ℝ, Set.InjOn f (A - A) ∧ f '' A ⊆ Set.range ((↑) : ℤ → ℝ)

/-- A finite list of reals has at most its length many distinct entries. -/
theorem ncard_list_le (l : List ℝ) : ({x | x ∈ l} : Set ℝ).ncard ≤ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have e : {x | x ∈ a :: l} = insert a {x | x ∈ l} := by
      ext x; simp
    rw [e]
    exact (Set.ncard_insert_le _ _).trans (by simp; omega)

/-- Inside a set where every 4-subset has at least five distinct positive differences,
a 3-AP-free subset is a Sidon set. -/
theorem sidon_of_apfree {A S : Set ℝ} (hSA : S ⊆ A)
    (hcond : ∀ B ⊆ A, B.ncard = 4 → 11 ≤ (B - B).ncard)
    (hap : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x + z = 2 * y → x = z) :
    IsSidon S := by
  intro a ha c hc b hb d hd h
  by_cases hac : a = c
  · left
    exact ⟨hac, by subst hac; linarith⟩
  by_cases had : a = d
  · right
    exact ⟨had, by subst had; linarith⟩
  exfalso
  by_cases hab : a = b
  · subst hab
    have e := hap c hc a ha d hd (by linarith)
    subst e
    exact hac (by linarith)
  by_cases hcd : c = d
  · subst hcd
    exact hab (hap a ha c hc b hb (by linarith))
  have hbc : b ≠ c := fun e => had (by linarith)
  have hbd : b ≠ d := fun e => hac (by linarith)
  have hBA : ({a, b, c, d} : Set ℝ) ⊆ A := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with e | e | e | e <;> rw [e]
    exacts [hSA ha, hSA hb, hSA hc, hSA hd]
  have hB4 : ({a, b, c, d} : Set ℝ).ncard = 4 := by
    have hl : ({a, b, c, d} : Set ℝ) = ↑([a, b, c, d].toFinset) := by
      ext x; simp
    rw [hl, Set.ncard_coe_finset, List.toFinset_card_of_nodup]
    · rfl
    · simp [hab, hac, had, hbc, hbd, hcd]
  have hsub : ({a, b, c, d} : Set ℝ) - {a, b, c, d} ⊆
      {x | x ∈ [0, a - c, c - a, a - d, d - a, a - b, b - a, c - d, d - c]} := by
    rintro x ⟨u, hu, v, hv, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    simp only [Set.mem_setOf_eq, List.mem_cons, List.mem_singleton]
    rcases hu with e1 | e1 | e1 | e1 <;> rcases hv with e2 | e2 | e2 | e2 <;> rw [e1, e2] <;>
      repeat (first | (left; linarith) | right)
    all_goals linarith
  have h9 : (({a, b, c, d} : Set ℝ) - {a, b, c, d}).ncard ≤ 9 :=
    (Set.ncard_le_ncard hsub (List.finite_toSet _)).trans (ncard_list_le _)
  have h11 := hcond _ hBA hB4
  omega

/-- Admissible constants are at most 1. -/
theorem bdd : BddAbove {c : ℝ | Erdos757.IsAdmissible c} := by
  refine ⟨1, fun c hc => ?_⟩
  have hc' : Erdos757.IsAdmissible c := hc
  obtain ⟨S, hS, -, hcS⟩ := hc' (A := ({0} : Set ℝ)) (Set.finite_singleton 0) (by
    intro B hB hB4
    exfalso
    have h := Set.ncard_le_ncard hB (Set.finite_singleton 0)
    rw [Set.ncard_singleton] at h
    omega)
  have h1 : S.ncard ≤ 1 := by
    have h := Set.ncard_le_ncard hS (Set.finite_singleton 0)
    rwa [Set.ncard_singleton] at h
  rw [Set.ncard_singleton] at hcS
  have h' : (S.ncard : ℝ) ≤ 1 := by exact_mod_cast h1
  push_cast at hcS
  linarith

/-- The image of A ∩ f⁻¹ T under f, when T ⊆ f '' A. -/
theorem image_inter_preimage_eq {f : ℝ → ℝ} {A T : Set ℝ} (hT : T ⊆ f '' A) :
    f '' (A ∩ f ⁻¹' T) = T := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact hx.2
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := hT hy
    exact ⟨x, ⟨hx, hy⟩, rfl⟩

theorem image_sub_eq (f : ℝ →+ ℝ) (B : Set ℝ) : f '' (B - B) = f '' B - f '' B := by
  ext y
  constructor
  · rintro ⟨_, ⟨u, hu, v, hv, rfl⟩, rfl⟩
    exact ⟨f u, ⟨u, hu, rfl⟩, f v, ⟨v, hv, rfl⟩, (map_sub f u v).symm⟩
  · rintro ⟨_, ⟨u, hu, rfl⟩, _, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨u - v, ⟨u, hu, v, hv, rfl⟩, map_sub f u v⟩

theorem admissible (h1 : H1) (h2 : H2) : ∃ c : ℝ, 1 / 2 < c ∧ Erdos757.IsAdmissible c := by
  obtain ⟨c, hc, hH⟩ := h1
  refine ⟨c, hc, ?_⟩
  intro A hA hcond
  obtain ⟨f, hinj, hint⟩ := h2 A hA
  have hinjA : Set.InjOn f A := by
    intro x hx y hy hxy
    have h0 : f (x - y) = f (x - x) := by
      rw [map_sub, map_sub, hxy]
    have e := hinj (Set.sub_mem_sub hx hy) (Set.sub_mem_sub hx hx) h0
    linarith
  have hcond' : ∀ B' ⊆ f '' A, B'.ncard = 4 → 11 ≤ (B' - B').ncard := by
    intro B' hB' hB'4
    have hBA : A ∩ f ⁻¹' B' ⊆ A := Set.inter_subset_left
    have hfB : f '' (A ∩ f ⁻¹' B') = B' := image_inter_preimage_eq hB'
    have hB4 : (A ∩ f ⁻¹' B').ncard = 4 := by
      rw [← Set.ncard_image_of_injOn (hinjA.mono hBA), hfB, hB'4]
    have h11 := hcond _ hBA hB4
    rw [← hfB, ← image_sub_eq,
      Set.ncard_image_of_injOn (hinj.mono (Set.sub_subset_sub hBA hBA))]
    exact h11
  obtain ⟨S', hS'A, hap, hcard⟩ := hH (f '' A) (hA.image f) hint hcond'
  have hSA : A ∩ f ⁻¹' S' ⊆ A := Set.inter_subset_left
  have hfS : f '' (A ∩ f ⁻¹' S') = S' := image_inter_preimage_eq hS'A
  have hsid : IsSidon S' := sidon_of_apfree hS'A hcond' hap
  refine ⟨A ∩ f ⁻¹' S', hSA, ?_, ?_⟩
  · intro a ha b hb c hc d hd h
    rcases hsid (f a) ha.2 (f b) hb.2 (f c) hc.2 (f d) hd.2
        (by rw [← map_add, ← map_add, h]) with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · left
      exact ⟨hinjA ha.1 hb.1 e1, hinjA hc.1 hd.1 e2⟩
    · right
      exact ⟨hinjA ha.1 hd.1 e1, hinjA hc.1 hb.1 e2⟩
  · have e1 : (f '' A).ncard = A.ncard := Set.ncard_image_of_injOn hinjA
    have e2 : S'.ncard = (A ∩ f ⁻¹' S').ncard := by
      rw [← Set.ncard_image_of_injOn (hinjA.mono hSA), hfS]
    rw [e1, e2] at hcard
    exact hcard

theorem main : H1 → H2 → type_of% @Erdos757.erdos_757.variants.lowerBound := by
  intro h1 h2 A
  obtain ⟨c, hc, hadm⟩ := admissible h1 h2
  exact lt_csSup_of_lt bdd hadm hc

end OMA.R_Erdos757_erdos_757_variants_lowerBound_R1
