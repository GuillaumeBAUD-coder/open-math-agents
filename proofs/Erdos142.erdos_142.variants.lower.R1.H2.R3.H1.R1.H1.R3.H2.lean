import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1_H1_R3
import Mathlib

/-!
# Step H2 of Erdos142.erdos_142.variants.lower.R1.H2.R3.H1.R1.H1.R3

Case `k < p`: the number `k - 1` is a unit mod `p`. Join the two endpoints `a` and
`a + (k - 1) d` of every nonconstant progression inside `A`. Reversing a progression
shows that this oriented edge set is symmetric, so the degree sum is at most the number
of edges, which is at most the number of nonconstant progressions. The progressions with
`d = 0` contribute at least `|A|` more. The greedy minimum-degree bound (Turan in
Caro-Wei form) gives an independent set `B` with `|A| ^ 2 ≤ (|A| + degree sum) |B|`,
and `B` has no nonconstant progression since its endpoints would be joined.

Case `p ≤ k`: a nonconstant progression of length `k` covers all of `ZMod p`. If `A` is
everything take `B = {0}`, otherwise take `B = A`.
-/

namespace OMA.Helpers

open Finset

/-- Neighbours of `v` inside `A` for the oriented edge set `E`. -/
def e142xs_nbr {V : Type} [DecidableEq V] (E : Finset (V × V)) (A : Finset V) (v : V) :
    Finset V :=
  A.filter (fun u => (v, u) ∈ E ∨ (u, v) ∈ E)

theorem e142xs_nbr_sub {V : Type} [DecidableEq V] (E : Finset (V × V)) {A A' : Finset V}
    (h : A' ⊆ A) (v : V) : e142xs_nbr E A' v ⊆ e142xs_nbr E A v :=
  filter_subset_filter _ h

/-- For a symmetric edge set the degree sum is at most the number of edges. -/
theorem e142xs_degsum_symm {V : Type} [DecidableEq V] (E : Finset (V × V)) (A : Finset V)
    (hsym : ∀ x y, (x, y) ∈ E → (y, x) ∈ E) :
    ∑ v ∈ A, (e142xs_nbr E A v).card ≤ E.card := by
  have h0 : ∀ v ∈ A, (e142xs_nbr E A v).card = (A.filter (fun u => (v, u) ∈ E)).card := by
    intro v _
    unfold e142xs_nbr
    congr 1
    apply filter_congr
    intro u _
    constructor
    · rintro (h | h)
      · exact h
      · exact hsym _ _ h
    · intro h
      exact Or.inl h
  rw [sum_congr rfl h0]
  have h1 : ∑ v ∈ A, (A.filter (fun u => (v, u) ∈ E)).card
      = ((A ×ˢ A).filter (fun x => x ∈ E)).card := by
    simp only [card_filter, sum_product]
  rw [h1]
  exact card_le_card (fun x hx => (mem_filter.mp hx).2)

theorem e142xs_arith (x d S S' b : ℕ) (hx : x ^ 2 ≤ (x + S') * b)
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

/-- Greedy independent set: remove a vertex of minimum degree with its neighbours. -/
theorem e142xs_turan {V : Type} [DecidableEq V] (E : Finset (V × V))
    (hE : ∀ e ∈ E, e.1 ≠ e.2) :
    ∀ n : ℕ, ∀ A : Finset V, A.card = n → ∃ B ⊆ A,
      A.card ^ 2 ≤ (A.card + ∑ v ∈ A, (e142xs_nbr E A v).card) * B.card ∧
      ∀ e ∈ E, e.1 ∈ B → e.2 ∉ B := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A hAn
  rcases A.eq_empty_or_nonempty with hA | hA
  · subst hA
    exact ⟨∅, empty_subset _, by simp, fun e _ h => absurd h (notMem_empty _)⟩
  obtain ⟨v, hvA, hmin⟩ := exists_min_image A (fun u => (e142xs_nbr E A u).card) hA
  have hvnb : v ∉ e142xs_nbr E A v := by
    intro h
    rcases (mem_filter.mp h).2 with h1 | h1 <;> exact hE _ h1 rfl
  have hNA : insert v (e142xs_nbr E A v) ⊆ A := insert_subset hvA (filter_subset _ _)
  have hNcard : (insert v (e142xs_nbr E A v)).card = (e142xs_nbr E A v).card + 1 :=
    card_insert_of_notMem hvnb
  have hA'A : A \ insert v (e142xs_nbr E A v) ⊆ A := sdiff_subset
  have hA'card : (A \ insert v (e142xs_nbr E A v)).card
      + (insert v (e142xs_nbr E A v)).card = A.card := card_sdiff_add_card_eq_card hNA
  have hlt : (A \ insert v (e142xs_nbr E A v)).card < n := by omega
  obtain ⟨B', hB'A', hB'size, hB'ind⟩ := ih _ hlt _ rfl
  have hvB' : v ∉ B' := fun h => (mem_sdiff.mp (hB'A' h)).2 (mem_insert_self _ _)
  refine ⟨insert v B', insert_subset hvA (hB'A'.trans hA'A), ?_, ?_⟩
  · rw [card_insert_of_notMem hvB']
    have hsplit : ∑ u ∈ A \ insert v (e142xs_nbr E A v), (e142xs_nbr E A u).card
        + ∑ u ∈ insert v (e142xs_nbr E A v), (e142xs_nbr E A u).card
        = ∑ u ∈ A, (e142xs_nbr E A u).card := sum_sdiff hNA
    have hA'sum : ∑ u ∈ A \ insert v (e142xs_nbr E A v),
          (e142xs_nbr E (A \ insert v (e142xs_nbr E A v)) u).card
        ≤ ∑ u ∈ A \ insert v (e142xs_nbr E A v), (e142xs_nbr E A u).card :=
      sum_le_sum (fun u _ => card_le_card (e142xs_nbr_sub E hA'A u))
    have hNsum : (insert v (e142xs_nbr E A v)).card • (e142xs_nbr E A v).card
        ≤ ∑ u ∈ insert v (e142xs_nbr E A v), (e142xs_nbr E A u).card :=
      card_nsmul_le_sum _ _ _ (fun u hu => hmin u (hNA hu))
    rw [smul_eq_mul, hNcard] at hNsum
    rw [← hA'card, hNcard]
    exact e142xs_arith _ _ _ _ _ hB'size (by linarith)
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

/-- A nonconstant progression of length at least `p` covers `ZMod p`. -/
theorem e142xs_cover {p : ℕ} [NeZero p] [Fact p.Prime] {k : ℕ} (hpk : p ≤ k)
    (S : Finset (ZMod p)) (a d : ZMod p) (hd : d ≠ 0)
    (h : ∀ i : Fin k, a + (i.val : ZMod p) * d ∈ S) (x : ZMod p) : x ∈ S := by
  have hj : ((x - a) * d⁻¹).val < k := lt_of_lt_of_le (ZMod.val_lt _) hpk
  have hx := h ⟨_, hj⟩
  have e : a + ((((x - a) * d⁻¹).val : ℕ) : ZMod p) * d = x := by
    rw [ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ hd, mul_one]
    ring
  rw [← e]
  exact hx

end OMA.Helpers

open OMA.Helpers Finset in
theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1_H1_R3.H2 := by
  intro p hp k hk A
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Fact p.Prime := ⟨hp⟩
  set P := (univ.filter fun u : ZMod p × ZMod p =>
    ∀ i : Fin k, u.1 + (i.val : ZMod p) * u.2 ∈ A) with hP
  have hA0 : A.card ≤ (P.filter (fun u => u.2 = 0)).card := by
    apply card_le_card_of_injOn (fun a => (a, (0 : ZMod p)))
    · intro a ha
      simp only [coe_filter, P, mem_filter, mem_univ, true_and, mul_zero, add_zero,
        Set.mem_setOf_eq]
      exact ⟨fun _ => ha, trivial⟩
    · intro x _ y _ hxy
      simpa using hxy
  have hAP : A.card ≤ P.card := hA0.trans (card_le_card (filter_subset _ _))
  by_cases hkp : k < p
  · set c : ZMod p := ((k - 1 : ℕ) : ZMod p) with hc
    have hc0 : c ≠ 0 := by
      intro h
      rw [hc, ZMod.natCast_eq_zero_iff] at h
      have := Nat.le_of_dvd (by omega) h
      omega
    set P0 := P.filter (fun u => ¬ u.2 = 0) with hP0
    set E := P0.image (fun u : ZMod p × ZMod p => (u.1, u.1 + c * u.2)) with hEdef
    have hE : ∀ e ∈ E, e.1 ≠ e.2 := by
      intro e he
      obtain ⟨⟨a, d⟩, hu, rfl⟩ := mem_image.mp he
      have hd : d ≠ 0 := (mem_filter.mp hu).2
      intro h
      have h' : c * d = 0 := by
        have := congrArg (fun z => z - a) h
        simpa using this.symm
      exact (mul_ne_zero hc0 hd) h'
    have hsym : ∀ x y, (x, y) ∈ E → (y, x) ∈ E := by
      intro x y hxy
      obtain ⟨⟨a, d⟩, hu, he⟩ := mem_image.mp hxy
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      simp only [P0, P, mem_filter, mem_univ, true_and] at hu
      obtain ⟨hprog, hd⟩ := hu
      apply mem_image.mpr
      refine ⟨(a + c * d, -d), ?_, ?_⟩
      · simp only [P0, P, mem_filter, mem_univ, true_and]
        refine ⟨fun i => ?_, neg_ne_zero.mpr hd⟩
        have hik := i.isLt
        have hi := hprog ⟨k - 1 - i.val, by omega⟩
        have hcast : ((k - 1 - i.val : ℕ) : ZMod p) = c - (i.val : ZMod p) := by
          rw [hc, Nat.cast_sub (by omega)]
        simp only [hcast] at hi
        have e : a + c * d + (i.val : ZMod p) * -d = a + (c - (i.val : ZMod p)) * d := by ring
        rw [e]
        exact hi
      · refine Prod.ext rfl ?_
        show a + c * d + c * -d = a
        ring
    obtain ⟨B, hBA, hsize, hind⟩ := e142xs_turan E hE A.card A rfl
    refine ⟨B, hBA, ?_, ?_⟩
    · intro a d hB
      by_contra hd
      have hmem : (a, a + c * d) ∈ E := by
        apply mem_image.mpr
        refine ⟨(a, d), ?_, rfl⟩
        simp only [P0, P, mem_filter, mem_univ, true_and]
        exact ⟨fun i => hBA (hB i), hd⟩
      have h0 := hB ⟨0, by omega⟩
      have h1 := hB ⟨k - 1, by omega⟩
      simp only [Nat.cast_zero, zero_mul, add_zero] at h0
      exact hind _ hmem h0 h1
    · have hdeg := e142xs_degsum_symm E A hsym
      have hEc : E.card ≤ P0.card := card_image_le
      have hsplit : (P.filter (fun u => u.2 = 0)).card + P0.card = P.card :=
        card_filter_add_card_filter_not _
      calc A.card ^ 2 ≤ (A.card + ∑ v ∈ A, (e142xs_nbr E A v).card) * B.card := hsize
        _ ≤ P.card * B.card := Nat.mul_le_mul_right _ (by omega)
        _ = B.card * P.card := mul_comm _ _
  · have hpk : p ≤ k := by omega
    by_cases hall : ∀ x : ZMod p, x ∈ A
    · refine ⟨{0}, fun x _ => hall x, ?_, ?_⟩
      · intro a d hB
        have h0 := hB ⟨0, by omega⟩
        have h1 := hB ⟨1, by omega⟩
        simp only [Nat.cast_zero, zero_mul, add_zero, mem_singleton] at h0
        simp only [Nat.cast_one, one_mul, mem_singleton, h0, zero_add] at h1
        exact h1
      · rw [card_singleton, one_mul, sq, ← card_product]
        apply card_le_card
        intro u _
        simp only [P, mem_filter, mem_univ, true_and]
        exact fun i => hall _
    · push_neg at hall
      obtain ⟨x, hx⟩ := hall
      refine ⟨A, subset_refl _, ?_, ?_⟩
      · intro a d hB
        by_contra hd
        exact hx (e142xs_cover hpk A a d hd hB x)
      · rw [sq]
        exact Nat.mul_le_mul_left _ hAP
