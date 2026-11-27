import OMAReductions.R_Arxiv_1609_08688_maximalLength_le_isBigO_R1
import Mathlib

/-! Step Arxiv.1609.08688.maximalLength_le_isBigO.R1.H2: hypothesis H2 of reduction Arxiv.1609.08688.maximalLength_le_isBigO.R1.
Credit: @ivillar (original proof). A longest 2-increasing sequence of triples in [1, n]^3 (it exists
since lengths are bounded by n^3) is encoded as the triangles (a0 - 1, a1 - 1, a2 - 1). Two distinct
triples of the sequence are 2-comparable, so they cannot share two coordinates (edge-disjointness),
and three triples pairwise sharing one coordinate would give contradictory orders (no accidental
triangles). -/

open Arxiv.«1609.08688» SimpleGraph.TripartiteFromTriangles

namespace OMA1609H2

lemma lt2_cases {a b : Fin 3 → ℕ} (h : lt₂ a b) :
    (a 0 < b 0 ∧ a 1 < b 1) ∨ (a 0 < b 0 ∧ a 2 < b 2) ∨ (a 1 < b 1 ∧ a 2 < b 2) := by
  obtain ⟨i, j, hij, hi, hj⟩ := h
  fin_cases i <;> fin_cases j <;> simp_all

lemma comparable : ∀ {s : List (Fin 3 → ℕ)}, s.Pairwise lt₂ →
    ∀ {a b : Fin 3 → ℕ}, a ∈ s → b ∈ s → a ≠ b → lt₂ a b ∨ lt₂ b a
  | [], _, _, _, ha, _, _ => absurd ha List.not_mem_nil
  | x :: s, h, a, b, ha, hb, hne => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.mp ha with h1 | h1 <;> rcases List.mem_cons.mp hb with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · subst h1; exact Or.inl (h.1 _ h2)
    · subst h2; exact Or.inr (h.1 _ h1)
    · exact comparable h.2 h1 h2 hne

lemma length_le {n : ℕ} {s : List (Fin 3 → ℕ)} (hs : ∀ a ∈ s, Set.range a ⊆ Set.Icc 1 n)
    (hinc : IsIncreasing₂ s) : s.length ≤ n ^ 3 := by
  classical
  have hnd : s.Nodup := List.Pairwise.imp (fun {a b} (h : lt₂ a b) => by
    rintro rfl; exact not_lt₂_self _ h) hinc
  rw [← List.toFinset_card_of_nodup hnd]
  have hsub : s.toFinset ⊆ Fintype.piFinset (fun _ : Fin 3 => Finset.Icc 1 n) := by
    intro a ha
    rw [Fintype.mem_piFinset]
    intro i
    have := hs a (List.mem_toFinset.mp ha) (Set.mem_range_self i)
    simpa using this
  calc s.toFinset.card ≤ (Fintype.piFinset (fun _ : Fin 3 => Finset.Icc 1 n)).card :=
        Finset.card_le_card hsub
    _ = n ^ 3 := by simp

lemma exists_optimal (n : ℕ) : ∃ s : List (Fin 3 → ℕ), (∀ a ∈ s, Set.range a ⊆ Set.Icc 1 n) ∧
    IsIncreasing₂ s ∧ s.length = maximalLength n := by
  unfold maximalLength
  obtain ⟨s, hs, hinc, hlen⟩ := Nat.sSup_mem
    (s := { List.length s | (s : List (Fin 3 → ℕ)) (_ : ∀ a ∈ s, Set.range a ⊆ Set.Icc 1 n)
      (_ : IsIncreasing₂ s) })
    ⟨0, [], by simp, by simp, rfl⟩
    ⟨n ^ 3, by rintro x ⟨s, hs, hinc, rfl⟩; exact length_le hs hinc⟩
  exact ⟨s, hs, hinc, hlen⟩

theorem main_H2 : OMA.R_Arxiv_1609_08688_maximalLength_le_isBigO_R1.H2 := by
  intro n
  classical
  obtain ⟨s, hs, hinc, hlen⟩ := exists_optimal n
  have hb : ∀ a ∈ s, ∀ i, 1 ≤ a i ∧ a i ≤ n := fun a ha i => by
    have := hs a ha (Set.mem_range_self i)
    simpa using this
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨∅, ?_, ⟨by simp, by simp, by simp⟩, ⟨by simp⟩⟩
    rw [← hlen]
    cases s with
    | nil => rfl
    | cons a s =>
      have := hb a List.mem_cons_self 0
      omega
  let f : (Fin 3 → ℕ) → Fin n × Fin n × Fin n := fun a =>
    (⟨min (a 0 - 1) (n - 1), by omega⟩, ⟨min (a 1 - 1) (n - 1), by omega⟩,
      ⟨min (a 2 - 1) (n - 1), by omega⟩)
  have hf : ∀ a ∈ s, (f a).1.val + 1 = a 0 ∧ (f a).2.1.val + 1 = a 1 ∧ (f a).2.2.val + 1 = a 2 := by
    intro a ha
    have h0 := hb a ha 0
    have h1 := hb a ha 1
    have h2 := hb a ha 2
    simp only [f]
    omega
  have hmem : ∀ x y z, (x, y, z) ∈ s.toFinset.image f →
      ∃ a ∈ s, x.val + 1 = a 0 ∧ y.val + 1 = a 1 ∧ z.val + 1 = a 2 := by
    intro x y z h
    obtain ⟨a, ha, hfa⟩ := Finset.mem_image.mp h
    have ha' := List.mem_toFinset.mp ha
    obtain ⟨e0, e1, e2⟩ := hf a ha'
    rw [hfa] at e0 e1 e2
    exact ⟨a, ha', e0, e1, e2⟩
  have hnd : s.Nodup := List.Pairwise.imp (fun {a b} (h : lt₂ a b) => by
    rintro rfl; exact not_lt₂_self _ h) hinc
  refine ⟨s.toFinset.image f, ?_, ⟨?_, ?_, ?_⟩, ⟨?_⟩⟩
  · rw [Finset.card_image_of_injOn, List.toFinset_card_of_nodup hnd, hlen]
    intro a ha b hb' hab
    have ha' := List.mem_toFinset.mp ha
    have hb'' := List.mem_toFinset.mp hb'
    obtain ⟨a0, a1, a2⟩ := hf a ha'
    obtain ⟨b0, b1, b2⟩ := hf b hb''
    have hab' : f a = f b := hab
    rw [hab'] at a0 a1 a2
    funext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue]; omega
    · simp only [Fin.mk_one, Fin.isValue]; omega
    · simp only [Fin.reduceFinMk, Fin.isValue]; omega
  · intro x y z x' h1 h2
    obtain ⟨a, ha, a0, a1, a2⟩ := hmem _ _ _ h1
    obtain ⟨b, hb', b0, b1, b2⟩ := hmem _ _ _ h2
    apply Fin.ext
    by_contra hne
    have hab : a ≠ b := fun h => hne (by have := congrFun h 0; omega)
    rcases comparable hinc ha hb' hab with h | h <;> rcases lt2_cases h with h | h | h <;> omega
  · intro x y z y' h1 h2
    obtain ⟨a, ha, a0, a1, a2⟩ := hmem _ _ _ h1
    obtain ⟨b, hb', b0, b1, b2⟩ := hmem _ _ _ h2
    apply Fin.ext
    by_contra hne
    have hab : a ≠ b := fun h => hne (by have := congrFun h 1; omega)
    rcases comparable hinc ha hb' hab with h | h <;> rcases lt2_cases h with h | h | h <;> omega
  · intro x y z z' h1 h2
    obtain ⟨a, ha, a0, a1, a2⟩ := hmem _ _ _ h1
    obtain ⟨b, hb', b0, b1, b2⟩ := hmem _ _ _ h2
    apply Fin.ext
    by_contra hne
    have hab : a ≠ b := fun h => hne (by have := congrFun h 2; omega)
    rcases comparable hinc ha hb' hab with h | h <;> rcases lt2_cases h with h | h | h <;> omega
  · intro x x' y y' z z' h1 h2 h3
    obtain ⟨u, hu, u0, u1, u2⟩ := hmem _ _ _ h1
    obtain ⟨v, hv, v0, v1, v2⟩ := hmem _ _ _ h2
    obtain ⟨w, hw, w0, w1, w2⟩ := hmem _ _ _ h3
    by_contra hne
    simp only [not_or] at hne
    obtain ⟨hx, hy, hz⟩ := hne
    have hx' : x.val ≠ x'.val := fun h => hx (Fin.ext h)
    have hy' : y.val ≠ y'.val := fun h => hy (Fin.ext h)
    have hz' : z.val ≠ z'.val := fun h => hz (Fin.ext h)
    have huv : u ≠ v := fun h => hx' (by have := congrFun h 0; omega)
    have hvw : v ≠ w := fun h => hy' (by have := congrFun h 1; omega)
    have huw : u ≠ w := fun h => hz' (by have := congrFun h 2; omega)
    rcases comparable hinc hu hv huv with h | h <;> rcases lt2_cases h with h | h | h <;>
    rcases comparable hinc hv hw hvw with h' | h' <;> rcases lt2_cases h' with h' | h' | h' <;>
    rcases comparable hinc hu hw huw with h'' | h'' <;> rcases lt2_cases h'' with h'' | h'' | h'' <;>
    omega

end OMA1609H2

theorem OMA.solution : OMA.R_Arxiv_1609_08688_maximalLength_le_isBigO_R1.H2 := OMA1609H2.main_H2
