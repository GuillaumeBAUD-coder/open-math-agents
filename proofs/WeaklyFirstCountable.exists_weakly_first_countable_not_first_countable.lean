import FormalConjectures.Paper.WeaklyFirstCountable

namespace A

open Topology Filter

abbrev X := Option (ℕ × Option ℕ)

def P : X → X × ℕ
  | none => (none, 0)
  | some (i, none) => (none, i)
  | some (i, some j) => (some (i, none), j)

def V (x : X) (n : ℕ) : Set X := {y | y = x ∨ (P y).1 = x ∧ n ≤ (P y).2}

lemma V_anti (x : X) : Antitone (V x) := fun a b h y => Or.imp_right (.imp_right h.trans)

def T : TopologicalSpace X where
  IsOpen O := ∀ x ∈ O, ∃ k, V x k ⊆ O
  isOpen_univ := fun _ _ => ⟨0, Set.subset_univ _⟩
  isOpen_inter s t hs ht x hx :=
    let ⟨a, ha⟩ := hs x hx.1
    let ⟨b, hb⟩ := ht x hx.2
    ⟨max a b, fun y hy => ⟨ha (V_anti x (le_max_left a b) hy), hb (V_anti x (le_max_right a b) hy)⟩⟩
  isOpen_sUnion S h x := fun ⟨t, ht, hxt⟩ =>
    let ⟨k, hk⟩ := h t ht x hxt
    ⟨k, hk.trans (Set.subset_sUnion_of_mem ht)⟩

def U (f : ℕ → ℕ) : Set X := {x | match x with | some (i, some j) => f i ≤ j | _ => True}

lemma U_open (f : ℕ → ℕ) : @IsOpen X T (U f) := fun x hx => ⟨f (P x).2, fun y hy => by
  rcases x with _ | ⟨i, _ | j⟩ <;> rcases y with _ | ⟨i', _ | j'⟩ <;> simp_all [V, P, U]⟩

lemma main : ∃ (Y : Type) (_ : TopologicalSpace Y),
    WeaklyFirstCountable.WeaklyFirstCountableTopology Y ∧ ¬ FirstCountableTopology Y := by
  letI : TopologicalSpace X := T
  refine ⟨X, T, ⟨⟨V, fun x => ⟨V_anti x, fun _ => Or.inl rfl⟩, fun O => Iff.rfl⟩⟩, fun hfc => ?_⟩
  have := hfc.nhds_generated_countable (none : X)
  obtain ⟨s, hs⟩ := (𝓝 (none : X)).exists_antitone_basis
  have key : ∀ m, ∃ k, ∃ g : ℕ → ℕ, ∀ i, k ≤ i → ∀ j, g i ≤ j → (some (i, some j) : X) ∈ s m := fun m => by
    obtain ⟨O, hOs, hO, hnO⟩ := mem_nhds_iff.mp (hs.mem m)
    obtain ⟨k, hk⟩ := hO none hnO
    have hl : ∀ i, k ≤ i → ∃ l : ℕ, ∀ j, l ≤ j → (some (i, some j) : X) ∈ s m := fun i hi => by
      obtain ⟨l, hl⟩ := hO _ (hk (Or.inr ⟨rfl, hi⟩ : (some (i, none) : X) ∈ V none k))
      exact ⟨l, fun j hj => hOs (hl (Or.inr ⟨rfl, hj⟩))⟩
    choose! g hg using hl
    exact ⟨k, g, hg⟩
  choose k h hh using key
  obtain ⟨m, -, hm⟩ := hs.toHasBasis.mem_iff.mp
    ((U_open fun i => (Finset.range (i + 1)).sup (h · i) + 1).mem_nhds trivial)
  have h1 : _ + 1 ≤ h m (max m (k m)) := hm (hh m _ (le_max_right _ _) _ le_rfl)
  have := Finset.le_sup (f := (h · (max m (k m)))) (b := m) (Finset.mem_range.mpr (Nat.lt_add_one_of_le (le_max_left m (k m))))
  omega

end A

theorem OMA.solution : type_of% @WeaklyFirstCountable.exists_weakly_first_countable_not_first_countable := A.main
