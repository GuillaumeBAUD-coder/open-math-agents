import FormalConjectures.Paper.WeaklyFirstCountable

-- Problem: Conjectures about Weakly First Countable spaces — exists weakly first countable not first countable
-- Upstream: formal-conjectures FormalConjectures/Paper/WeaklyFirstCountable.lean:73 (declaration WeaklyFirstCountable.exists_weakly_first_countable_not_first_countable)
-- Credit: @Genbox (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMAArensAux

open Topology Filter

abbrev X := Option (ℕ × Option ℕ)

def V : X → ℕ → Set X
  | none, n => {x | x = none ∨ ∃ i, n ≤ i ∧ x = some (i, none)}
  | some (i, none), n => {x | x = some (i, none) ∨ ∃ j, n ≤ j ∧ x = some (i, some j)}
  | some (i, some j), _ => {some (i, some j)}

lemma V_anti (x : X) : Antitone (V x) := by
  intro a b hab
  rcases x with _ | ⟨i, _ | j⟩
  · rintro y (h | ⟨i, hi, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨i, le_trans hab hi, rfl⟩
  · rintro y (h | ⟨j, hj, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨j, le_trans hab hj, rfl⟩
  · exact le_rfl

lemma V_mem (x : X) (n : ℕ) : x ∈ V x n := by
  rcases x with _ | ⟨i, _ | j⟩
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact rfl

def T : TopologicalSpace X where
  IsOpen O := ∀ x ∈ O, ∃ k, V x k ⊆ O
  isOpen_univ := fun _ _ => ⟨0, Set.subset_univ _⟩
  isOpen_inter s t hs ht x hx := by
    obtain ⟨a, ha⟩ := hs x hx.1
    obtain ⟨b, hb⟩ := ht x hx.2
    exact ⟨max a b, Set.subset_inter ((V_anti x (le_max_left a b)).trans ha)
      ((V_anti x (le_max_right a b)).trans hb)⟩
  isOpen_sUnion S h x hx := by
    obtain ⟨t, ht, hxt⟩ := hx
    obtain ⟨k, hk⟩ := h t ht x hxt
    exact ⟨k, hk.trans (Set.subset_sUnion_of_mem ht)⟩

def U (f : ℕ → ℕ) : Set X :=
  {x | x = none ∨ (∃ i, x = some (i, none)) ∨ ∃ i j, f i ≤ j ∧ x = some (i, some j)}

lemma U_open (f : ℕ → ℕ) : @IsOpen X T (U f) := by
  intro x hx
  rcases x with _ | ⟨i, _ | j⟩
  · refine ⟨0, ?_⟩
    rintro y (rfl | ⟨i, -, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨i, rfl⟩)
  · refine ⟨f i, ?_⟩
    rintro y (rfl | ⟨j, hj, rfl⟩)
    · exact Or.inr (Or.inl ⟨i, rfl⟩)
    · exact Or.inr (Or.inr ⟨i, j, hj, rfl⟩)
  · refine ⟨0, ?_⟩
    rintro y rfl
    exact hx

lemma main : ∃ (Y : Type) (_ : TopologicalSpace Y),
    WeaklyFirstCountable.WeaklyFirstCountableTopology Y ∧ ¬ FirstCountableTopology Y := by
  letI : TopologicalSpace X := T
  refine ⟨X, T, ⟨⟨V, fun x => ⟨V_anti x, V_mem x⟩, fun O => Iff.rfl⟩⟩, ?_⟩
  intro hfc
  have : (𝓝 (none : X)).IsCountablyGenerated := hfc.nhds_generated_countable none
  obtain ⟨s, hs⟩ := (𝓝 (none : X)).exists_antitone_basis
  have key : ∀ m, ∃ k : ℕ, ∃ g : ℕ → ℕ, ∀ i j, k ≤ i → g i ≤ j → (some (i, some j) : X) ∈ s m := by
    intro m
    obtain ⟨O, hOs, hO, hnO⟩ := mem_nhds_iff.mp (hs.mem m)
    obtain ⟨k, hk⟩ := hO none hnO
    have hl : ∀ i, k ≤ i → ∃ l : ℕ, ∀ j, l ≤ j → (some (i, some j) : X) ∈ s m := by
      intro i hi
      have hai : (some (i, none) : X) ∈ O := hk (Or.inr ⟨i, hi, rfl⟩)
      obtain ⟨l, hl⟩ := hO _ hai
      exact ⟨l, fun j hj => hOs (hl (Or.inr ⟨j, hj, rfl⟩))⟩
    refine ⟨k, fun i => if hi : k ≤ i then (hl i hi).choose else 0, fun i j hi hj => ?_⟩
    have hj2 : (hl i hi).choose ≤ j := by simpa only [dif_pos hi] using hj
    exact (hl i hi).choose_spec j hj2
  choose k h hh using key
  let f : ℕ → ℕ := fun i => (Finset.range (i + 1)).sup (fun m => h m i) + 1
  have hU : U f ∈ 𝓝 (none : X) := (U_open f).mem_nhds (Or.inl rfl)
  obtain ⟨m, -, hm⟩ := hs.toHasBasis.mem_iff.mp hU
  let i := max m (k m)
  have h1 := hm (hh m i (h m i) (le_max_right _ _) le_rfl)
  rcases h1 with h1 | ⟨i', h1⟩ | ⟨i', j', hle, h1⟩
  · exact absurd h1 (by simp)
  · exact absurd h1 (by simp)
  · simp only [Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    have hmi : h m i ≤ (Finset.range (i + 1)).sup (fun m => h m i) :=
      Finset.le_sup (f := fun m => h m i) (Finset.mem_range.mpr (by omega))
    simp only [f] at hle
    omega

end OMAArensAux

theorem OMA.solution : type_of% @WeaklyFirstCountable.exists_weakly_first_countable_not_first_countable :=
  OMAArensAux.main
