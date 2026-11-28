import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1_H1_R3
import Mathlib

open Finset

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Join the first two terms of each nontrivial progression of A with canonical difference
-- (d.val < (-d).val; reversal pairs each progression with its canonical copy, p odd) by an
-- edge, so |E| <= |P'|/2. A Caro-Wei independent set B (greedy minimum-degree induction plus
-- Cauchy-Schwarz) has |A|^2 <= (|A| + 2|E|)|B| <= |P||B| and contains no nontrivial progression.
-- p = 2 is checked by hand.

namespace OMA.SolAP

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

theorem cw_turan : ∀ (V : Type) (A : Finset V) (E : Finset (V × V)),
    (∀ e ∈ E, e.1 ≠ e.2) →
    ∃ B ⊆ A, A.card ^ 2 ≤ (A.card + 2 * E.card) * B.card ∧
      ∀ e ∈ E, e.1 ∈ B → e.2 ∉ B := by
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

lemma ap_rev {p : ℕ} (k : ℕ) (S : Finset (ZMod p)) (a d : ZMod p)
    (h : ∀ i : Fin k, a + (i.val : ZMod p) * d ∈ S) :
    ∀ i : Fin k, (a + ((k-1 : ℕ) : ZMod p) * d) + (i.val : ZMod p) * (-d) ∈ S := by
  intro i
  have hi := i.isLt
  have := h ⟨k - 1 - i.val, by omega⟩
  convert this using 1
  simp only
  rw [Nat.cast_sub (show i.val ≤ k - 1 by omega)]
  ring

lemma ap_card_le {p : ℕ} [NeZero p] (k : ℕ) (A : Finset (ZMod p)) :
    A.card ≤ ((univ.filter fun u : ZMod p × ZMod p =>
      ∀ i : Fin k, u.1 + (i.val : ZMod p) * u.2 ∈ A).filter (fun u => u.2 = 0)).card := by
  rw [← card_image_of_injective A (f := fun a => (a, (0 : ZMod p)))
    (fun x y h => by simpa using h)]
  apply card_le_card
  intro u hu
  simp only [mem_image] at hu
  obtain ⟨a, ha, rfl⟩ := hu
  simp [ha]

lemma ap_main (p : ℕ) [NeZero p] (hodd : p % 2 = 1) (k : ℕ) (hk : 2 ≤ k)
    (A : Finset (ZMod p)) : ∃ B ⊆ A,
    (∀ a d : ZMod p, (∀ i : Fin k, a + (i.val : ZMod p) * d ∈ B) → d = 0) ∧
    A.card ^ 2 ≤ B.card * (univ.filter fun u : ZMod p × ZMod p =>
      ∀ i : Fin k, u.1 + (i.val : ZMod p) * u.2 ∈ A).card := by
  set P := (univ.filter fun u : ZMod p × ZMod p =>
      ∀ i : Fin k, u.1 + (i.val : ZMod p) * u.2 ∈ A) with hP
  have hA0 := ap_card_le k A
  rw [← hP] at hA0
  set P' := P.filter (fun u => ¬ u.2 = 0) with hP'
  have hsplit := card_le_card (show P.filter (fun u => u.2 = 0) ∪ P' ⊆ P from
    union_subset (filter_subset _ _) (filter_subset _ _))
  rw [card_union_of_disjoint (by
    rw [disjoint_left]
    intro u hu hu2
    exact (mem_filter.mp hu2).2 (mem_filter.mp hu).2)] at hsplit
  set Pc := P'.filter (fun u => u.2.val < (-u.2).val) with hPc
  let rev : ZMod p × ZMod p → ZMod p × ZMod p :=
    fun u => (u.1 + ((k-1 : ℕ) : ZMod p) * u.2, -u.2)
  have hrevinj : Function.Injective rev := by
    intro x y hxy
    simp only [rev, Prod.mk.injEq, neg_inj] at hxy
    obtain ⟨h1, h2⟩ := hxy
    rw [h2] at h1
    exact Prod.ext (add_right_cancel h1) h2
  have hvalne : ∀ d : ZMod p, d ≠ 0 → d.val ≠ (-d).val := by
    intro d hd
    rw [ZMod.neg_val, if_neg hd]
    have := ZMod.val_lt d
    omega
  have hPc2 : 2 * Pc.card ≤ P'.card := by
    have hdisj : Disjoint Pc (Pc.image rev) := by
      rw [disjoint_left]
      intro u hu hu2
      obtain ⟨v, hv, rfl⟩ := mem_image.mp hu2
      simp only [hPc, mem_filter, rev, neg_neg] at hu hv
      omega
    have hsub : Pc ∪ Pc.image rev ⊆ P' := by
      intro u hu
      rcases mem_union.mp hu with hu | hu
      · exact (mem_filter.mp hu).1
      · obtain ⟨v, hv, rfl⟩ := mem_image.mp hu
        have hv' := (mem_filter.mp hv).1
        simp only [hP', hP, mem_filter, mem_univ, true_and] at hv' ⊢
        exact ⟨ap_rev k A v.1 v.2 hv'.1, by simpa [rev] using hv'.2⟩
    have := card_le_card hsub
    rw [card_union_of_disjoint hdisj, card_image_of_injective _ hrevinj] at this
    omega
  set E := Pc.image (fun u => (u.1, u.1 + u.2)) with hE
  have hEc : E.card ≤ Pc.card := card_image_le
  have hloop : ∀ e ∈ E, e.1 ≠ e.2 := by
    intro e he
    obtain ⟨u, hu, rfl⟩ := mem_image.mp he
    have := (mem_filter.mp (mem_filter.mp hu).1).2
    intro h
    apply this
    simpa using h
  obtain ⟨B, hBA, hcw, hind⟩ := cw_turan (ZMod p) A E hloop
  refine ⟨B, hBA, ?_, ?_⟩
  · intro a d h
    by_contra hd
    have hAm : ∀ i : Fin k, a + (i.val : ZMod p) * d ∈ A := fun i => hBA (h i)
    rcases lt_or_gt_of_ne (hvalne d hd) with hlt | hgt
    · have hu : (a, d) ∈ Pc := by
        simp only [hPc, hP', hP, mem_filter, mem_univ, true_and]
        exact ⟨⟨hAm, hd⟩, hlt⟩
      have he : (a, a + d) ∈ E := mem_image.mpr ⟨(a, d), hu, rfl⟩
      exact hind _ he (by simpa using h ⟨0, by omega⟩) (by simpa using h ⟨1, by omega⟩)
    · have hu : rev (a, d) ∈ Pc := by
        simp only [hPc, hP', hP, mem_filter, mem_univ, true_and, rev, neg_neg]
        exact ⟨⟨ap_rev k A a d hAm, neg_ne_zero.mpr hd⟩, hgt⟩
      have he : ((rev (a, d)).1, (rev (a, d)).1 + (rev (a, d)).2) ∈ E :=
        mem_image.mpr ⟨rev (a, d), hu, rfl⟩
      have hB := ap_rev k B a d h
      exact hind _ he (by simpa [rev] using hB ⟨0, by omega⟩)
        (by simpa [rev] using hB ⟨1, by omega⟩)
  · calc A.card ^ 2 ≤ (A.card + 2 * E.card) * B.card := hcw
      _ ≤ P.card * B.card := Nat.mul_le_mul_right _ (by omega)
      _ = B.card * P.card := Nat.mul_comm _ _

lemma ap_two_free : ∀ A : Finset (ZMod 2), A ≠ univ → ∀ a d : ZMod 2,
    a ∈ A → a + d ∈ A → d = 0 := by decide

end OMA.SolAP

open OMA.SolAP in
theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1_H1_R3.H2 := by
  unfold OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1_H1_R3.H2
  intro p hp
  letI : NeZero p := ⟨hp.ne_zero⟩
  intro k hk A
  rcases hp.eq_two_or_odd with h2 | hodd
  · subst h2
    by_cases hA : A = univ
    · subst hA
      refine ⟨{0}, subset_univ _, ?_, ?_⟩
      · intro a d h
        have h0 := h ⟨0, by omega⟩
        have h1 := h ⟨1, by omega⟩
        simp at h0 h1
        rw [h0] at h1
        simpa using h1
      · have : (univ.filter fun u : ZMod 2 × ZMod 2 =>
            ∀ i : Fin k, u.1 + (i.val : ZMod 2) * u.2 ∈ (univ : Finset (ZMod 2))) = univ := by
          ext u; simp
        rw [this]
        simp [Finset.card_univ, ZMod.card]
    · refine ⟨A, subset_refl _, ?_, ?_⟩
      · intro a d h
        exact ap_two_free A hA a d (by simpa using h ⟨0, by omega⟩)
          (by simpa using h ⟨1, by omega⟩)
      · have := ap_card_le k A
        have h3 := card_filter_le (univ.filter fun u : ZMod 2 × ZMod 2 =>
            ∀ i : Fin k, u.1 + (i.val : ZMod 2) * u.2 ∈ A) (fun u => u.2 = 0)
        rw [sq]
        exact Nat.mul_le_mul_left _ (this.trans h3)
  · exact ap_main p hodd k hk A
