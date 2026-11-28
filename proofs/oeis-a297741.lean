import OMAStatements.S_oeis_a297741
import Mathlib

-- Problem: A297741: The number of distinct positions on an infinite chessboard reachable by the (3,4)-leaper in <= n moves.
-- Upstream: formal-conjectures statements/oeis-a297741.lean:0 (declaration OMA.S_oeis_a297741.main)
-- Credit: @Ezekia1 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open OMA.S_oeis_a297741

lemma OMA.aux_step : ∀ i : Fin 8,
    |(step i).1| ≤ 4 ∧ |(step i).2| ≤ 4 ∧ |(step i).1| + |(step i).2| ≤ 7 := by
  decide

lemma OMA.aux_bound : ∀ n : ℕ, ∀ p ∈ ball n,
    |p.1| ≤ 4 * (n : ℤ) ∧ |p.2| ≤ 4 * (n : ℤ) ∧ |p.1| + |p.2| ≤ 7 * (n : ℤ) := by
  intro n
  induction n with
  | zero =>
    intro p hp
    simp only [ball, Finset.mem_singleton] at hp
    subst hp
    simp
  | succ n ih =>
    intro p hp
    simp only [ball, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_image] at hp
    rcases hp with hp | ⟨i, q, hq, rfl⟩
    · obtain ⟨h1, h2, h3⟩ := ih p hp
      push_cast
      refine ⟨by linarith, by linarith, by linarith⟩
    · obtain ⟨h1, h2, h3⟩ := ih q hq
      obtain ⟨s1, s2, s3⟩ := OMA.aux_step i
      have a1 := abs_add_le q.1 (step i).1
      have a2 := abs_add_le q.2 (step i).2
      simp only [Prod.fst_add, Prod.snd_add]
      push_cast
      refine ⟨by linarith, by linarith, by linarith⟩

lemma OMA.aux_cardT :
    ((Finset.Icc (-40 : ℤ) 40 ×ˢ Finset.Icc (-40 : ℤ) 40).filter
      (fun p => p.1 + p.2 ≤ 70 ∧ p.1 - p.2 ≤ 70 ∧ -p.1 + p.2 ≤ 70 ∧ -p.1 - p.2 ≤ 70)).card
      = 6341 := by
  decide +kernel

lemma OMA.aux_main (n : ℕ) (hn : n = 10) :
    (a n : ℤ) ≠ 62 * (n : ℤ)^2 + 30 * n - 55 := by
  have hz : (n : ℤ) = 10 := by rw [hn]; norm_num
  have hsub : ball n ⊆ (Finset.Icc (-40 : ℤ) 40 ×ˢ Finset.Icc (-40 : ℤ) 40).filter
      (fun p => p.1 + p.2 ≤ 70 ∧ p.1 - p.2 ≤ 70 ∧ -p.1 + p.2 ≤ 70 ∧ -p.1 - p.2 ≤ 70) := by
    intro p hp
    have hb := OMA.aux_bound n p hp
    have h1 := hb.1
    have h2 := hb.2.1
    have h3 := hb.2.2
    rw [hz] at h1 h2 h3
    have b1 := le_abs_self p.1
    have b2 := neg_abs_le p.1
    have b3 := le_abs_self p.2
    have b4 := neg_abs_le p.2
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    refine ⟨⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩,
      by linarith, by linarith, by linarith, by linarith⟩
  have hc := Finset.card_le_card hsub
  rw [OMA.aux_cardT] at hc
  have hc' : (a n : ℤ) ≤ 6341 := by
    unfold a
    exact_mod_cast hc
  intro heq
  rw [hz] at heq
  linarith

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a297741.main) := by
  intro h
  exact OMA.aux_main 10 rfl (h.1 10 le_rfl)
