import FormalConjectures.Arxiv.«1609.08688».sIncreasingrTuples

-- Problem: The length of an $s$-increasing sequence of $r$-tuples — maximalLength four
-- Upstream: formal-conjectures FormalConjectures/Arxiv/1609.08688/sIncreasingrTuples.lean:155 (declaration Arxiv.«1609.08688».maximalLength_four)
-- Credit: @Genbox (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMAMaxLen4Aux

open Arxiv.«1609.08688»

def lt2b (a b : ℕ × ℕ × ℕ) : Bool :=
  (decide (a.1 < b.1) && decide (a.2.1 < b.2.1)) || (decide (a.1 < b.1) && decide (a.2.2 < b.2.2)) ||
    (decide (a.2.1 < b.2.1) && decide (a.2.2 < b.2.2))

def noSeq : ℕ → List (ℕ × ℕ × ℕ) → Bool
  | 0, _ => false
  | k + 1, c => c.all (fun b => noSeq k (c.filter (fun x => lt2b b x)))

def L4 : List ℕ := [1, 2, 3, 4]

def allT : List (ℕ × ℕ × ℕ) :=
  L4.flatMap (fun x => L4.flatMap (fun y => L4.map (fun z => (x, y, z))))

lemma noSeq_spec : ∀ (s : List (ℕ × ℕ × ℕ)) (k : ℕ) (c : List (ℕ × ℕ × ℕ)),
    noSeq k c = true → s.Pairwise (fun a b => lt2b a b = true) → (∀ a ∈ s, a ∈ c) →
    s.length < k := by
  intro s
  induction s with
  | nil =>
    intro k c h _ _
    cases k with
    | zero => simp [noSeq] at h
    | succ k => simp
  | cons a t ih =>
    intro k c h hp hs
    cases k with
    | zero => simp [noSeq] at h
    | succ k =>
      simp only [noSeq, List.all_eq_true] at h
      have ha : a ∈ c := hs a (by simp)
      have h1 := h a ha
      rw [List.pairwise_cons] at hp
      have := ih k _ h1 hp.2 (fun x hx => by
        rw [List.mem_filter]
        exact ⟨hs x (by simp [hx]), hp.1 x hx⟩)
      simp
      omega

lemma noSeq_nine : noSeq 9 allT = true := by decide +kernel

def f (a : Fin 3 → ℕ) : ℕ × ℕ × ℕ := (a 0, a 1, a 2)

lemma lt2b_of (a b : Fin 3 → ℕ) (h : lt₂ a b) : lt2b (f a) (f b) = true := by
  obtain ⟨i, j, hij, hi, hj⟩ := h
  simp only [lt2b, f, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  fin_cases i <;> fin_cases j <;> simp_all

lemma mem_allT (a : Fin 3 → ℕ) (h : Set.range a ⊆ Set.Icc 1 4) : f a ∈ allT := by
  have h0 := h ⟨0, rfl⟩
  have h1 := h ⟨1, rfl⟩
  have h2 := h ⟨2, rfl⟩
  simp only [Set.mem_Icc] at h0 h1 h2
  have m : ∀ x : ℕ, 1 ≤ x → x ≤ 4 → x ∈ L4 := by
    intro x hx1 hx2
    simp only [L4, List.mem_cons, List.not_mem_nil, or_false]
    omega
  simp only [allT, f, List.mem_flatMap, List.mem_map]
  exact ⟨a 0, m _ h0.1 h0.2, a 1, m _ h1.1 h1.2, a 2, m _ h2.1 h2.2, rfl⟩

lemma len_le (s : List (Fin 3 → ℕ)) (hr : ∀ a ∈ s, Set.range a ⊆ Set.Icc 1 4)
    (hs : IsIncreasing₂ s) : s.length ≤ 8 := by
  have := noSeq_spec (s.map f) 9 allT noSeq_nine
    (by
      rw [List.pairwise_map]
      exact hs.imp (fun {a b} h => lt2b_of a b h))
    (by
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      exact mem_allT a (hr a ha))
  simp at this
  omega

def ex : List (Fin 3 → ℕ) :=
  [![1, 1, 1], ![1, 2, 2], ![2, 1, 3], ![2, 2, 4], ![3, 3, 1], ![3, 4, 2], ![4, 3, 3], ![4, 4, 4]]

lemma ex_inc : IsIncreasing₂ ex := by
  unfold IsIncreasing₂ ex lt₂
  decide

lemma ex_range : ∀ a ∈ ex, Set.range a ⊆ Set.Icc 1 4 := by
  intro a ha
  simp only [ex, List.mem_cons, List.not_mem_nil, or_false] at ha
  rintro _ ⟨i, rfl⟩
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    fin_cases i <;> simp

lemma main : maximalLength 4 = 8 := by
  have hub : ∀ m ∈ { List.length s | (s) (_ : ∀ a ∈ s, Set.range a ⊆ Set.Icc 1 4)
      (_ : IsIncreasing₂ s) }, m ≤ 8 := by
    rintro _ ⟨s, hr, hs, rfl⟩
    exact len_le s hr hs
  have hmem : 8 ∈ { List.length s | (s) (_ : ∀ a ∈ s, Set.range a ⊆ Set.Icc 1 4)
      (_ : IsIncreasing₂ s) } := ⟨ex, ex_range, ex_inc, rfl⟩
  unfold maximalLength
  exact le_antisymm (csSup_le ⟨8, hmem⟩ hub) (le_csSup ⟨8, hub⟩ hmem)

end OMAMaxLen4Aux

theorem OMA.solution : type_of% @Arxiv.«1609.08688».maximalLength_four :=
  OMAMaxLen4Aux.main
