import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1_H1_R2
import Mathlib

/-!
# Step H1 of the reduction Erdos142.erdos_142.variants.lower.R1.H2.R3.H1.R1.H1.R2

Turan's independent set bound for a finite graph given by oriented edges without loops:
a vertex set A with edge list E contains an independent set B with |A|^2 <= (|A| + 2|E|) |B|.

Greedy proof by strong induction on |A|. Take a vertex v of A of minimum degree, delete v and
its neighbours inside A (a set S of size s) and every edge not inside the remaining set A'.
Every vertex of S has degree at least deg v >= s - 1, and each deleted edge is incident to at
most two vertices of S, so at least s (s - 1) / 2 edges are deleted. With P = |A'| + 2|E'| and
D = |A| + 2|E| this gives P + s^2 <= D, and the induction hypothesis |A'|^2 <= P x yields
  P (D (x + 1) - |A|^2) >= (P - |A'| s)^2 >= 0,
which is the claim for B = B' with v added.
-/

namespace TuranIS

open Finset

lemma arith (a s m m' x : ℤ) (ha : 0 ≤ a) (hs : 0 ≤ s) (hm' : 0 ≤ m') (hx : 0 ≤ x)
    (h1 : a ^ 2 ≤ (a + 2 * m') * x) (h2 : 2 * m' + s * s ≤ 2 * m + s) :
    (s + a) ^ 2 ≤ (s + a + 2 * m) * (x + 1) := by
  have hP0 : 0 ≤ a + 2 * m' := by linarith
  have hD : a + 2 * m' + s ^ 2 ≤ s + a + 2 * m := by nlinarith
  have hD0 : 0 ≤ s + a + 2 * m := by nlinarith [sq_nonneg s]
  rcases hP0.eq_or_lt with hP | hP
  · have ha0 : a = 0 := by linarith
    subst ha0
    nlinarith [mul_nonneg hD0 hx]
  · have key : (a + 2 * m') * (s + a) ^ 2 ≤ (a + 2 * m') * ((s + a + 2 * m) * (x + 1)) := by
      nlinarith [sq_nonneg (a + 2 * m' - a * s),
        mul_nonneg (sub_nonneg.mpr hD) (add_nonneg (sq_nonneg a) hP.le),
        mul_le_mul_of_nonneg_left h1 hD0]
    exact le_of_mul_le_mul_left key hP

theorem indep (n : ℕ) : ∀ (V : Type) (A : Finset V) (E : Finset (V × V)), A.card = n →
    (∀ e ∈ E, e.1 ≠ e.2) →
    ∃ B ⊆ A, A.card ^ 2 ≤ (A.card + 2 * E.card) * B.card ∧ ∀ e ∈ E, e.1 ∈ B → e.2 ∉ B := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V A E hn hE
    classical
    rcases A.eq_empty_or_nonempty with rfl | hne
    · exact ⟨∅, Subset.rfl, by simp, by simp⟩
    obtain ⟨v, hvA, hmin⟩ := A.exists_min_image
      (fun u => (E.filter fun e => e.1 = u ∨ e.2 = u).card) hne
    let nb : V → Prop := fun u => u = v ∨ (v, u) ∈ E ∨ (u, v) ∈ E
    let inA' : V × V → Prop := fun e =>
      e.1 ∈ A.filter (fun u => ¬ nb u) ∧ e.2 ∈ A.filter (fun u => ¬ nb u)
    have hvS : v ∈ A.filter nb := mem_filter.mpr ⟨hvA, Or.inl rfl⟩
    have hcard : (A.filter nb).card + (A.filter fun u => ¬ nb u).card = A.card :=
      card_filter_add_card_filter_not nb
    have hEcard : (E.filter inA').card + (E.filter fun e => ¬ inA' e).card = E.card :=
      card_filter_add_card_filter_not inA'
    have hSpos : 0 < (A.filter nb).card := card_pos.mpr ⟨v, hvS⟩
    obtain ⟨B', hB'A, hB'card, hB'ind⟩ := ih (A.filter fun u => ¬ nb u).card (by omega) V
      (A.filter fun u => ¬ nb u) (E.filter inA') rfl (fun e he => hE e (mem_filter.mp he).1)
    have hvB' : v ∉ B' := fun h => (mem_filter.mp (hB'A h)).2 (Or.inl rfl)
    -- the closed neighbourhood of `v` has at most `deg v + 1` elements
    have hdegv : (A.filter nb).card ≤ (E.filter fun e => e.1 = v ∨ e.2 = v).card + 1 := by
      have hsub : A.filter nb ⊆ insert v ((E.filter fun e => e.1 = v ∨ e.2 = v).image
          fun e => if e.1 = v then e.2 else e.1) := by
        intro u hu
        rcases (mem_filter.mp hu).2 with rfl | h | h
        · exact mem_insert_self _ _
        · refine mem_insert_of_mem (mem_image.mpr ⟨(v, u), mem_filter.mpr ⟨h, Or.inl rfl⟩, ?_⟩)
          simp
        · refine mem_insert_of_mem (mem_image.mpr ⟨(u, v), mem_filter.mpr ⟨h, Or.inr rfl⟩, ?_⟩)
          by_cases huv : u = v <;> simp [huv]
      calc (A.filter nb).card ≤ _ := card_le_card hsub
        _ ≤ ((E.filter fun e => e.1 = v ∨ e.2 = v).image
              fun e => if e.1 = v then e.2 else e.1).card + 1 := card_insert_le _ _
        _ ≤ _ := Nat.add_le_add_right card_image_le 1
    -- double counting of incidences between the neighbourhood and the deleted edges
    have hsum : (A.filter nb).card * (E.filter fun e => e.1 = v ∨ e.2 = v).card ≤
        2 * (E.filter fun e => ¬ inA' e).card := by
      calc (A.filter nb).card * (E.filter fun e => e.1 = v ∨ e.2 = v).card
          = (A.filter nb).card • (E.filter fun e => e.1 = v ∨ e.2 = v).card := by
            rw [smul_eq_mul]
        _ ≤ ∑ u ∈ A.filter nb, (E.filter fun e => e.1 = u ∨ e.2 = u).card :=
            card_nsmul_le_sum _ _ _ fun u hu => hmin u (mem_filter.mp hu).1
        _ = ∑ e ∈ E, ((A.filter nb).filter fun u => e.1 = u ∨ e.2 = u).card := by
            simp only [card_filter]
            exact sum_comm
        _ = ∑ e ∈ E.filter inA', ((A.filter nb).filter fun u => e.1 = u ∨ e.2 = u).card +
              ∑ e ∈ E.filter (fun e => ¬ inA' e),
                ((A.filter nb).filter fun u => e.1 = u ∨ e.2 = u).card :=
            (sum_filter_add_sum_filter_not E inA' _).symm
        _ ≤ 0 + ∑ _e ∈ E.filter (fun e => ¬ inA' e), 2 := by
            refine Nat.add_le_add (le_of_eq (sum_eq_zero fun e he => ?_))
              (sum_le_sum fun e _ => ?_)
            · rw [card_eq_zero, filter_eq_empty_iff]
              intro u hu h
              have hin : inA' e := (mem_filter.mp he).2
              rcases h with h | h
              · exact (mem_filter.mp hin.1).2 (h ▸ (mem_filter.mp hu).2)
              · exact (mem_filter.mp hin.2).2 (h ▸ (mem_filter.mp hu).2)
            · calc ((A.filter nb).filter fun u => e.1 = u ∨ e.2 = u).card
                  ≤ ({e.1, e.2} : Finset V).card := card_le_card fun u hu => by
                    rcases (mem_filter.mp hu).2 with h | h <;> simp [h.symm]
                _ ≤ 2 := card_le_two
        _ = 2 * (E.filter fun e => ¬ inA' e).card := by simp [mul_comm]
    refine ⟨insert v B', ?_, ?_, ?_⟩
    · intro u hu
      rcases mem_insert.mp hu with rfl | h
      · exact hvA
      · exact (mem_filter.mp (hB'A h)).1
    · rw [card_insert_of_notMem hvB', ← hcard]
      have h2 : 2 * (E.filter inA').card + (A.filter nb).card * (A.filter nb).card ≤
          2 * E.card + (A.filter nb).card := by
        have := Nat.mul_le_mul_left (A.filter nb).card hdegv
        nlinarith
      have := arith ((A.filter fun u => ¬ nb u).card) ((A.filter nb).card) (E.card)
        ((E.filter inA').card) (B'.card) (by positivity) (by positivity) (by positivity)
        (by positivity) (by exact_mod_cast hB'card) (by exact_mod_cast h2)
      exact_mod_cast this
    · intro e he h1 h2
      rcases mem_insert.mp h1 with h1v | h1B
      · rcases mem_insert.mp h2 with h2v | h2B
        · exact hE e he (h1v.trans h2v.symm)
        · have hmem : (v, e.2) ∈ E := by rw [← h1v]; exact he
          exact (mem_filter.mp (hB'A h2B)).2 (Or.inr (Or.inl hmem))
      · rcases mem_insert.mp h2 with h2v | h2B
        · have hmem : (e.1, v) ∈ E := by rw [← h2v]; exact he
          exact (mem_filter.mp (hB'A h1B)).2 (Or.inr (Or.inr hmem))
        · exact hB'ind e (mem_filter.mpr ⟨he, hB'A h1B, hB'A h2B⟩) h1B h2B

end TuranIS

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1_H1_R2.H1 :=
  fun V A E hE => TuranIS.indep A.card V A E rfl hE
