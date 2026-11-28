import OMAReductions.R_Erdos627_erdos_627_variants_afm_upper_R1_H1_R1
import Mathlib.Combinatorics.SimpleGraph.Clique
-- Credit: @LordMike

open SimpleGraph

namespace OMA.QS

theorem pascal {V : Type*} [DecidableEq V] (C : SimpleGraph V) [DecidableRel C.Adj] :
    ∀ (m : ℕ) (a b : ℕ), a + b = m → ∀ S : Finset V, (a+b).choose a ≤ S.card →
      (∃ T ⊆ S, C.IsNClique (a+1) T) ∨ (∃ T ⊆ S, Cᶜ.IsNClique (b+1) T) := by
  intro m
  induction m with
  | zero =>
    intro a b hab S hS
    obtain rfl : a = 0 := by omega
    obtain rfl : b = 0 := by omega
    obtain ⟨v, hv⟩ := Finset.card_pos.mp (lt_of_lt_of_le (Nat.choose_pos (by omega)) hS)
    exact Or.inl ⟨{v}, by simpa using hv, by simp⟩
  | succ m ih =>
    intro a b hab S hS
    rcases a with _ | a
    · obtain ⟨v, hv⟩ := Finset.card_pos.mp (lt_of_lt_of_le (Nat.choose_pos (by omega)) hS)
      exact Or.inl ⟨{v}, by simpa using hv, by simp⟩
    rcases b with _ | b
    · obtain ⟨v, hv⟩ := Finset.card_pos.mp (lt_of_lt_of_le (Nat.choose_pos (by omega)) hS)
      exact Or.inr ⟨{v}, by simpa using hv, by simp⟩
    have hpos : 0 < (a+1+(b+1)).choose (a+1) := Nat.choose_pos (by omega)
    obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
    let A := S.filter (fun w => C.Adj v w)
    let B := S.filter (fun w => w ≠ v ∧ ¬ C.Adj v w)
    have hcard : A.card + B.card + 1 = S.card := by
      have h1 : (S.erase v).card + 1 = S.card := Finset.card_erase_add_one hv
      have h2 : (S.erase v).filter (fun w => C.Adj v w) = A := by
        ext w
        simp only [A, Finset.mem_filter, Finset.mem_erase]
        constructor
        · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h2, h3⟩
        · rintro ⟨h2, h3⟩
          exact ⟨⟨fun e => by subst e; exact C.loopless.irrefl _ h3, h2⟩, h3⟩
      have h3 : (S.erase v).filter (fun w => ¬ C.Adj v w) = B := by
        ext w
        simp only [B, Finset.mem_filter, Finset.mem_erase]
        tauto
      have := Finset.card_filter_add_card_filter_not (s := S.erase v) (fun w => C.Adj v w)
      rw [h2, h3] at this
      omega
    have hsplit : (a+1+(b+1)).choose (a+1) =
        (a+(b+1)).choose a + (a+1+b).choose (a+1) := by
      rw [show a+1+(b+1) = (a+b+1)+1 by ring, Nat.choose_succ_succ,
        show a+(b+1) = a+b+1 by ring, show a+1+b = a+b+1 by ring]
    by_cases hA : (a+(b+1)).choose a ≤ A.card
    · rcases ih a (b+1) (by omega) A hA with ⟨T, hT, hc⟩ | ⟨T, hT, hc⟩
      · refine Or.inl ⟨insert v T, ?_, hc.insert ?_⟩
        · intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · exact hv
          · exact (Finset.mem_filter.mp (hT hw)).1
        · intro w hw; exact (Finset.mem_filter.mp (hT hw)).2
      · exact Or.inr ⟨T, fun w hw => (Finset.mem_filter.mp (hT hw)).1, hc⟩
    · have hB : (a+1+b).choose (a+1) ≤ B.card := by omega
      rcases ih (a+1) b (by omega) B hB with ⟨T, hT, hc⟩ | ⟨T, hT, hc⟩
      · exact Or.inl ⟨T, fun w hw => (Finset.mem_filter.mp (hT hw)).1, hc⟩
      · refine Or.inr ⟨insert v T, ?_, hc.insert ?_⟩
        · intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · exact hv
          · exact (Finset.mem_filter.mp (hT hw)).1
        · intro w hw
          have := (Finset.mem_filter.mp (hT hw)).2
          simp only [compl_adj]
          exact ⟨fun e => this.1 e.symm, this.2⟩

end OMA.QS

theorem OMA.solution : OMA.R_Erdos627_erdos_627_variants_afm_upper_R1_H1_R1.H2 := by
  classical
  intro n G
  set a := G.cliqueNum with ha
  set b := G.indepNum with hb
  let P : ℕ → Prop := fun N => ∀ (C : SimpleGraph (Fin N)),
    (completeGraph (Fin (a+1))).IsContained C ∨ (completeGraph (Fin (b+1))).IsContained Cᶜ
  have hR : classicalRamsey (a+1) (b+1) = sInf {N | P N} := rfl
  have hup : P ((a+b).choose a) := by
    intro C
    rw [← not_cliqueFree_iff_top_isContained, ← not_cliqueFree_iff_top_isContained]
    have := OMA.QS.pascal C (a+b) a b rfl Finset.univ (by simp)
    rcases this with ⟨T, -, hT⟩ | ⟨T, -, hT⟩
    · left; intro h; exact h T hT
    · right; intro h; exact h T hT
  refine ⟨?_, by rw [hR]; exact Nat.sInf_le hup⟩
  rw [hR]
  have hne : ({N | P N} : Set ℕ).Nonempty := ⟨_, hup⟩
  by_contra hlt
  rw [not_lt] at hlt
  have hm := Nat.sInf_mem hne
  set m := sInf {N | P N}
  have hmn : m ≤ n := hlt
  let f : Fin m ↪ Fin n := Fin.castLEEmb hmn
  let C : SimpleGraph (Fin m) := G.comap f
  have h1 : G.CliqueFree (a+1) := by
    intro t ht
    have := ht.isClique.card_le_cliqueNum
    rw [ht.card_eq] at this; omega
  have h2 : Gᶜ.CliqueFree (b+1) := by
    intro t ht
    have := ht.isClique.card_le_cliqueNum
    rw [ht.card_eq] at this; simp at this; omega
  have hCG : C ⊑ G := ⟨(Embedding.comap f G).toCopy⟩
  have hCG' : Cᶜ ⊑ Gᶜ := by
    have : Cᶜ = Gᶜ.comap f := by ext x y; simp [C]
    rw [this]; exact ⟨(Embedding.comap f Gᶜ).toCopy⟩
  rcases hm C with h | h
  · exact ((not_cliqueFree_iff_top_isContained _).mpr h) (h1.comap hCG)
  · exact ((not_cliqueFree_iff_top_isContained _).mpr h) (h2.comap hCG')
