import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1_H1_R2
import Mathlib


/-!
# Step H1 of Erdos142.erdos_142.variants.lower.R1.H2.R3.H1.R1.H1.R2

Greedy minimum-degree argument (Turan bound in Caro-Wei form). Let `S` be the sum over
`v` in `A` of the number of neighbours of `v` inside `A`. Removing a vertex of minimum
degree `d` together with its `d` neighbours drops at least `(d + 1) * d` from `S`, and
induction gives `|A| ^ 2 ≤ (|A| + S) * |B|` for an independent set `B`. Finally `S`
is at most twice the number of oriented edges.
-/

namespace OMA.Helpers

open Finset

/-- Neighbours of `v` inside `A` for the oriented edge set `E`. -/
def e142ind_nbr {V : Type} [DecidableEq V] (E : Finset (V × V)) (A : Finset V) (v : V) :
    Finset V :=
  A.filter (fun u => (v, u) ∈ E ∨ (u, v) ∈ E)

theorem e142ind_nbr_sub {V : Type} [DecidableEq V] (E : Finset (V × V)) {A A' : Finset V}
    (h : A' ⊆ A) (v : V) : e142ind_nbr E A' v ⊆ e142ind_nbr E A v :=
  filter_subset_filter _ h

theorem e142ind_degsum_le {V : Type} [DecidableEq V] (E : Finset (V × V)) (A : Finset V) :
    ∑ v ∈ A, (e142ind_nbr E A v).card ≤ 2 * E.card := by
  have hout : ∑ v ∈ A, (A.filter (fun u => (v, u) ∈ E)).card ≤ E.card := by
    have h1 : ∑ v ∈ A, (A.filter (fun u => (v, u) ∈ E)).card
        = ((A ×ˢ A).filter (fun x => x ∈ E)).card := by
      simp only [card_filter, sum_product]
    rw [h1]
    exact card_le_card (fun x hx => (mem_filter.mp hx).2)
  have hin : ∑ v ∈ A, (A.filter (fun u => (u, v) ∈ E)).card ≤ E.card := by
    have h1 : ∑ v ∈ A, (A.filter (fun u => (u, v) ∈ E)).card
        = ((A ×ˢ A).filter (fun x => x.swap ∈ E)).card := by
      simp only [card_filter, sum_product, Prod.swap_prod_mk]
    rw [h1]
    apply card_le_card_of_injOn Prod.swap
    · intro x hx
      exact (mem_filter.mp hx).2
    · intro x _ y _ hxy
      exact Prod.swap_injective hxy
  calc ∑ v ∈ A, (e142ind_nbr E A v).card
      ≤ ∑ v ∈ A, ((A.filter (fun u => (v, u) ∈ E)).card
          + (A.filter (fun u => (u, v) ∈ E)).card) := by
        apply sum_le_sum
        intro v _
        unfold e142ind_nbr
        rw [filter_or]
        exact card_union_le _ _
    _ = ∑ v ∈ A, (A.filter (fun u => (v, u) ∈ E)).card
          + ∑ v ∈ A, (A.filter (fun u => (u, v) ∈ E)).card := sum_add_distrib
    _ ≤ E.card + E.card := add_le_add hout hin
    _ = 2 * E.card := by ring

theorem e142ind_arith (x d S S' b : ℕ) (hx : x ^ 2 ≤ (x + S') * b)
    (hS : S' + (d + 1) * d ≤ S) :
    (x + (d + 1)) ^ 2 ≤ (x + (d + 1) + S) * (b + 1) := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · have hx0 : x = 0 := by nlinarith
    subst hx0
    nlinarith
  · have h2 : b * (2 * x * (d + 1)) ≤ b * (x + S' + (d + 1) ^ 2 * b) := by
      have hxz : ((x : ℤ)) ^ 2 ≤ (x + S') * b := by exact_mod_cast hx
      have : (b : ℤ) * (2 * x * (d + 1)) ≤ b * (x + S' + (d + 1) ^ 2 * b) := by
        nlinarith [sq_nonneg ((x : ℤ) - (d + 1) * b)]
      exact_mod_cast this
    have key : 2 * x * (d + 1) ≤ x + S' + (d + 1) ^ 2 * b := Nat.le_of_mul_le_mul_left h2 hb
    have hSb : (S' + (d + 1) * d) * b ≤ S * b := Nat.mul_le_mul_right b hS
    nlinarith

theorem e142ind_main {V : Type} [DecidableEq V] (E : Finset (V × V))
    (hE : ∀ e ∈ E, e.1 ≠ e.2) :
    ∀ n : ℕ, ∀ A : Finset V, A.card = n → ∃ B ⊆ A,
      A.card ^ 2 ≤ (A.card + ∑ v ∈ A, (e142ind_nbr E A v).card) * B.card ∧
      ∀ e ∈ E, e.1 ∈ B → e.2 ∉ B := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A hAn
  rcases A.eq_empty_or_nonempty with hA | hA
  · subst hA
    exact ⟨∅, empty_subset _, by simp, fun e _ h => absurd h (notMem_empty _)⟩
  obtain ⟨v, hvA, hmin⟩ := exists_min_image A (fun u => (e142ind_nbr E A u).card) hA
  have hvnb : v ∉ e142ind_nbr E A v := by
    intro h
    rcases (mem_filter.mp h).2 with h1 | h1 <;> exact hE _ h1 rfl
  have hNA : insert v (e142ind_nbr E A v) ⊆ A := insert_subset hvA (filter_subset _ _)
  have hNcard : (insert v (e142ind_nbr E A v)).card = (e142ind_nbr E A v).card + 1 :=
    card_insert_of_notMem hvnb
  have hA'A : A \ insert v (e142ind_nbr E A v) ⊆ A := sdiff_subset
  have hA'card : (A \ insert v (e142ind_nbr E A v)).card
      + (insert v (e142ind_nbr E A v)).card = A.card := card_sdiff_add_card_eq_card hNA
  have hlt : (A \ insert v (e142ind_nbr E A v)).card < n := by omega
  obtain ⟨B', hB'A', hB'size, hB'ind⟩ := ih _ hlt _ rfl
  have hvB' : v ∉ B' := fun h => (mem_sdiff.mp (hB'A' h)).2 (mem_insert_self _ _)
  refine ⟨insert v B', insert_subset hvA (hB'A'.trans hA'A), ?_, ?_⟩
  · rw [card_insert_of_notMem hvB']
    have hsplit : ∑ u ∈ A \ insert v (e142ind_nbr E A v), (e142ind_nbr E A u).card
        + ∑ u ∈ insert v (e142ind_nbr E A v), (e142ind_nbr E A u).card
        = ∑ u ∈ A, (e142ind_nbr E A u).card := sum_sdiff hNA
    have hA'sum : ∑ u ∈ A \ insert v (e142ind_nbr E A v),
          (e142ind_nbr E (A \ insert v (e142ind_nbr E A v)) u).card
        ≤ ∑ u ∈ A \ insert v (e142ind_nbr E A v), (e142ind_nbr E A u).card :=
      sum_le_sum (fun u _ => card_le_card (e142ind_nbr_sub E hA'A u))
    have hNsum : (insert v (e142ind_nbr E A v)).card • (e142ind_nbr E A v).card
        ≤ ∑ u ∈ insert v (e142ind_nbr E A v), (e142ind_nbr E A u).card :=
      card_nsmul_le_sum _ _ _ (fun u hu => hmin u (hNA hu))
    rw [smul_eq_mul, hNcard] at hNsum
    rw [← hA'card, hNcard]
    exact e142ind_arith _ _ _ _ _ hB'size (by linarith)
  · intro e he h1 h2
    rcases mem_insert.mp h1 with h1 | h1 <;> rcases mem_insert.mp h2 with h2 | h2
    · exact hE e he (h1.trans h2.symm)
    · have h2A' := hB'A' h2
      apply (mem_sdiff.mp h2A').2
      apply mem_insert_of_mem
      refine mem_filter.mpr ⟨(mem_sdiff.mp h2A').1, Or.inl ?_⟩
      rw [← h1]
      exact he
    · have h1A' := hB'A' h1
      apply (mem_sdiff.mp h1A').2
      apply mem_insert_of_mem
      refine mem_filter.mpr ⟨(mem_sdiff.mp h1A').1, Or.inr ?_⟩
      rw [← h2]
      exact he
    · exact hB'ind e he h1 h2

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1_H1_R2.H1 := by
  classical
  intro V A E hE
  obtain ⟨B, hBA, hsize, hind⟩ := e142ind_main E hE A.card A rfl
  refine ⟨B, hBA, hsize.trans ?_, hind⟩
  exact Nat.mul_le_mul_right _ (Nat.add_le_add_left (e142ind_degsum_le E A) _)
