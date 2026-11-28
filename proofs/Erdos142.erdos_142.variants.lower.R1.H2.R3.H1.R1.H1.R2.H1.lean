import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1_H1_R2
import Mathlib

open Finset

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Caro-Wei by greedy induction: removing a minimum-degree vertex with its neighbourhood shows
-- that some independent B has |B| at least the sum of 1/(deg v + 1) over A; Cauchy-Schwarz
-- (a positivity argument) gives |A|^2 <= |B| (|A| + sum deg) <= |B| (|A| + 2|E|).

namespace OMA.SolCW

open Finset

def cwDeg {V : Type} [DecidableEq V] (E : Finset (V × V)) (S : Finset V) (v : V) : ℕ :=
  (E.filter (fun e => (e.1 = v ∧ e.2 ∈ S) ∨ (e.2 = v ∧ e.1 ∈ S))).card

lemma cw_deg_mono {V : Type} [DecidableEq V] (E : Finset (V × V)) {S T : Finset V}
    (h : S ⊆ T) (v : V) : cwDeg E S v ≤ cwDeg E T v := by
  unfold cwDeg
  apply card_le_card
  intro e he
  simp only [mem_filter] at he ⊢
  rcases he with ⟨he, h1 | h2⟩
  · exact ⟨he, Or.inl ⟨h1.1, h h1.2⟩⟩
  · exact ⟨he, Or.inr ⟨h2.1, h h2.2⟩⟩

lemma cw_nbhd_card {V : Type} [DecidableEq V] (E : Finset (V × V)) (S : Finset V) (v : V) :
    (S.filter (fun u => u = v ∨ (v,u) ∈ E ∨ (u,v) ∈ E)).card ≤ cwDeg E S v + 1 := by
  unfold cwDeg
  set D := E.filter (fun e => (e.1 = v ∧ e.2 ∈ S) ∨ (e.2 = v ∧ e.1 ∈ S)) with hD
  have hsub : S.filter (fun u => u = v ∨ (v,u) ∈ E ∨ (u,v) ∈ E) ⊆
      insert v (D.image (fun e => if e.1 = v then e.2 else e.1)) := by
    intro u hu
    simp only [mem_filter] at hu
    rw [mem_insert, mem_image]
    rcases hu with ⟨huS, h | h | h⟩
    · exact Or.inl h
    · right
      refine ⟨(v,u), ?_, ?_⟩
      · rw [hD, mem_filter]; exact ⟨h, Or.inl ⟨rfl, huS⟩⟩
      · simp
    · by_cases huv : u = v
      · exact Or.inl huv
      right
      refine ⟨(u,v), ?_, ?_⟩
      · rw [hD, mem_filter]; exact ⟨h, Or.inr ⟨rfl, huS⟩⟩
      · simp [huv]
  calc _ ≤ (insert v (D.image (fun e => if e.1 = v then e.2 else e.1))).card := card_le_card hsub
    _ ≤ (D.image (fun e => if e.1 = v then e.2 else e.1)).card + 1 := card_insert_le _ _
    _ ≤ D.card + 1 := Nat.add_le_add_right card_image_le 1

lemma cw_key {V : Type} [DecidableEq V] (E : Finset (V × V)) (hE : ∀ e ∈ E, e.1 ≠ e.2) :
    ∀ n, ∀ S : Finset V, S.card = n → ∃ B ⊆ S, (∀ e ∈ E, e.1 ∈ B → e.2 ∉ B) ∧
      ∑ v ∈ S, (1:ℝ) / ((cwDeg E S v : ℝ) + 1) ≤ B.card := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S hS
  rcases S.eq_empty_or_nonempty with h | hne
  · subst h; exact ⟨∅, subset_refl _, by simp, by simp⟩
  obtain ⟨v, hvS, hvmin⟩ := exists_min_image S (cwDeg E S) hne
  have hNc := cw_nbhd_card E S v
  set Nv := S.filter (fun u => u = v ∨ (v,u) ∈ E ∨ (u,v) ∈ E) with hNv
  have hNvS : Nv ⊆ S := filter_subset _ _
  have hvN : v ∈ Nv := by rw [hNv, mem_filter]; exact ⟨hvS, Or.inl rfl⟩
  have hcard : (S \ Nv).card < n := by
    rw [← hS]
    apply card_lt_card
    rw [Finset.ssubset_iff_of_subset sdiff_subset]
    exact ⟨v, hvS, fun h => (mem_sdiff.mp h).2 hvN⟩
  obtain ⟨B', hB'S, hB'ind, hB'sum⟩ := ih _ hcard (S \ Nv) rfl
  have hvB' : v ∉ B' := fun h => (mem_sdiff.mp (hB'S h)).2 hvN
  refine ⟨insert v B', ?_, ?_, ?_⟩
  · exact insert_subset hvS (hB'S.trans sdiff_subset)
  · intro e he h1 h2
    rw [mem_insert] at h1 h2
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact hE e he (h1.trans h2.symm)
    · have := mem_sdiff.mp (hB'S h2)
      apply this.2
      rw [hNv, mem_filter]
      refine ⟨this.1, Or.inr (Or.inl ?_)⟩
      rw [← h1]; exact he
    · have := mem_sdiff.mp (hB'S h1)
      apply this.2
      rw [hNv, mem_filter]
      refine ⟨this.1, Or.inr (Or.inr ?_)⟩
      rw [← h2]; exact he
    · exact hB'ind e he h1 h2
  · rw [card_insert_of_notMem hvB']
    push_cast
    rw [← sum_sdiff hNvS]
    have h1 : ∑ u ∈ S \ Nv, (1:ℝ) / ((cwDeg E S u : ℝ) + 1) ≤
        ∑ u ∈ S \ Nv, (1:ℝ) / ((cwDeg E (S \ Nv) u : ℝ) + 1) := by
      apply sum_le_sum
      intro u _
      apply one_div_le_one_div_of_le
      · positivity
      · have := cw_deg_mono E (sdiff_subset : S \ Nv ⊆ S) u
        have : (cwDeg E (S \ Nv) u : ℝ) ≤ cwDeg E S u := by exact_mod_cast this
        linarith
    have h2 : ∑ u ∈ Nv, (1:ℝ) / ((cwDeg E S u : ℝ) + 1) ≤ 1 := by
      calc ∑ u ∈ Nv, (1:ℝ) / ((cwDeg E S u : ℝ) + 1)
          ≤ ∑ u ∈ Nv, (1:ℝ) / ((cwDeg E S v : ℝ) + 1) := by
            apply sum_le_sum
            intro u hu
            apply one_div_le_one_div_of_le
            · positivity
            · have := hvmin u (hNvS hu)
              have : (cwDeg E S v : ℝ) ≤ cwDeg E S u := by exact_mod_cast this
              linarith
        _ = Nv.card / ((cwDeg E S v : ℝ) + 1) := by rw [sum_const, nsmul_eq_mul]; ring
        _ ≤ 1 := by
            rw [div_le_one (by positivity)]
            exact_mod_cast hNc
    linarith

lemma cw_fiber_sum {V : Type} [DecidableEq V] (E : Finset (V × V)) (A : Finset V)
    (g : V × V → V) : ∑ v ∈ A, (E.filter (fun e => g e = v)).card ≤ E.card := by
  simp only [card_filter]
  rw [sum_comm, card_eq_sum_ones]
  apply sum_le_sum
  intro e _
  rw [sum_ite_eq]
  split_ifs <;> simp

lemma cw_deg_sum {V : Type} [DecidableEq V] (E : Finset (V × V)) (A : Finset V) :
    ∑ v ∈ A, cwDeg E A v ≤ 2 * E.card := by
  have h : ∀ v, cwDeg E A v ≤
      (E.filter (fun e => e.1 = v)).card + (E.filter (fun e => e.2 = v)).card := by
    intro v
    unfold cwDeg
    calc _ ≤ (E.filter (fun e => e.1 = v) ∪ E.filter (fun e => e.2 = v)).card := by
          apply card_le_card
          intro e he
          simp only [mem_filter, mem_union] at he ⊢
          tauto
      _ ≤ _ := card_union_le _ _
  calc ∑ v ∈ A, cwDeg E A v ≤ ∑ v ∈ A, ((E.filter (fun e => e.1 = v)).card
        + (E.filter (fun e => e.2 = v)).card) := sum_le_sum (fun v _ => h v)
    _ = ∑ v ∈ A, (E.filter (fun e => e.1 = v)).card
        + ∑ v ∈ A, (E.filter (fun e => e.2 = v)).card := sum_add_distrib
    _ ≤ E.card + E.card := add_le_add (cw_fiber_sum E A Prod.fst) (cw_fiber_sum E A Prod.snd)
    _ = 2 * E.card := by ring

end OMA.SolCW

open OMA.SolCW in
theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1_H1_R2.H1 := by
  unfold OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1_H1_R2.H1
  intro V A E hE
  classical
  obtain ⟨B, hBA, hind, hsum⟩ := cw_key E hE A.card A rfl
  refine ⟨B, hBA, ?_, hind⟩
  rcases A.eq_empty_or_nonempty with h | hne
  · subst h; simp
  have hCS := Finset.sq_sum_div_le_sum_sq_div A (fun _ => (1:ℝ))
    (g := fun v => (cwDeg E A v : ℝ) + 1) (fun i _ => by positivity)
  simp only [sum_const, nsmul_eq_mul, mul_one, one_pow] at hCS
  have hG : ∑ v ∈ A, ((cwDeg E A v : ℝ) + 1) ≤ (A.card : ℝ) + 2 * E.card := by
    rw [sum_add_distrib, sum_const, nsmul_eq_mul, mul_one]
    have := cw_deg_sum E A
    have : (∑ v ∈ A, (cwDeg E A v : ℝ)) ≤ 2 * (E.card : ℝ) := by exact_mod_cast this
    linarith
  have hGpos : 0 < ∑ v ∈ A, ((cwDeg E A v : ℝ) + 1) := by
    apply sum_pos (fun i _ => by positivity) hne
  have h3 : (A.card : ℝ) ^ 2 / ∑ v ∈ A, ((cwDeg E A v : ℝ) + 1) ≤ B.card := hCS.trans hsum
  rw [div_le_iff₀ hGpos] at h3
  have h4 : (A.card : ℝ) ^ 2 ≤ ((A.card : ℝ) + 2 * E.card) * B.card := by
    have : (B.card : ℝ) * ∑ v ∈ A, ((cwDeg E A v : ℝ) + 1) ≤
        (B.card : ℝ) * ((A.card : ℝ) + 2 * E.card) :=
      mul_le_mul_of_nonneg_left hG (by positivity)
    linarith
  exact_mod_cast h4
