import FormalConjectures.ErdosProblems.«124»

-- Problem: Erdős Problem 124 — zero
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/124.lean:48 (declaration Erdos124.erdos124.zero)
-- Credit: @LordMike (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA

open Finset

theorem brown {α : Type*} [DecidableEq α] (w : α → ℕ) (s : Finset α) :
    (∀ a ∈ s, w a ≤ 1 + ∑ b ∈ s.filter (fun b => w b < w a), w b) →
      ∀ n ≤ ∑ b ∈ s, w b, ∃ t ⊆ s, ∑ b ∈ t, w b = n := by
  induction s using Finset.induction_on_max_value w with
  | empty =>
    intro _ n hn
    exact ⟨∅, by simp, by simp at hn; simp [hn]⟩
  | insert a s ha hmax ih =>
    intro h n hn
    have h' : ∀ x ∈ s, w x ≤ 1 + ∑ b ∈ s.filter (fun b => w b < w x), w b := by
      intro x hx
      have := h x (Finset.mem_insert_of_mem hx)
      rwa [Finset.filter_insert, if_neg (not_lt.2 (hmax x hx))] at this
    have ha' := h a (Finset.mem_insert_self a s)
    rw [Finset.filter_insert, if_neg (lt_irrefl _)] at ha'
    have hle : ∑ b ∈ s.filter (fun b => w b < w a), w b ≤ ∑ b ∈ s, w b :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    rw [Finset.sum_insert ha] at hn
    by_cases hns : n ≤ ∑ b ∈ s, w b
    · obtain ⟨t, hts, rfl⟩ := ih h' n hns
      exact ⟨t, hts.trans (Finset.subset_insert _ _), rfl⟩
    · obtain ⟨t, hts, ht⟩ := ih h' (n - w a) (by omega)
      refine ⟨insert a t, Finset.insert_subset_insert _ hts, ?_⟩
      rw [Finset.sum_insert (fun hat => ha (hts hat)), ht]
      omega

theorem geo (e x X : ℕ) (he : 2 ≤ e) (hx : x < X) :
    ((x : ℚ) - 1) ≤ ((e : ℚ) - 1) * ∑ j ∈ (range X).filter (fun j => e ^ j < x), ((e : ℚ) ^ j) := by
  have hex : ∃ t, x ≤ e ^ t := ⟨x, (Nat.lt_pow_self (by omega)).le⟩
  classical
  set t := Nat.find hex with ht
  have hfil : (range X).filter (fun j => e ^ j < x) = range t := by
    ext j
    simp only [mem_filter, mem_range]
    constructor
    · rintro ⟨_, hj⟩
      by_contra hc
      have h1 : x ≤ e ^ t := Nat.find_spec hex
      have h2 : e ^ t ≤ e ^ j := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    · intro hj
      have h1 : ¬ x ≤ e ^ j := Nat.find_min hex hj
      have h2 : j < e ^ j := Nat.lt_pow_self (by omega)
      omega
  rw [hfil]
  have hg := geom_sum_mul (e : ℚ) t
  have h1 : x ≤ e ^ t := Nat.find_spec hex
  have h1' : (x : ℚ) ≤ (e : ℚ) ^ t := by exact_mod_cast h1
  rw [mul_comm]
  linarith

theorem key (D : Finset ℕ) (hD : ∀ d ∈ D, 3 ≤ d) (hsum : 1 ≤ ∑ d ∈ D, (d - 1 : ℚ)⁻¹)
    (x X : ℕ) (hx1 : 1 ≤ x) (hx : x < X) :
    x ≤ 1 + ∑ b ∈ ((D ×ˢ range X).filter (fun p : ℕ × ℕ => p.1 ^ p.2 < X)).filter
      (fun b : ℕ × ℕ => b.1 ^ b.2 < x), b.1 ^ b.2 := by
  rw [Finset.filter_filter]
  have hcongr : ((D ×ˢ range X).filter (fun p : ℕ × ℕ => p.1 ^ p.2 < X ∧ p.1 ^ p.2 < x)) =
      ((D ×ˢ range X).filter (fun p : ℕ × ℕ => p.1 ^ p.2 < x)) := by
    apply Finset.filter_congr
    intro p _
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨by omega, h⟩
  rw [hcongr, Finset.sum_filter, Finset.sum_product]
  simp_rw [← Finset.sum_filter]
  have hQ : ((x : ℚ) - 1) ≤ ∑ e ∈ D, ∑ j ∈ (range X).filter (fun j => e ^ j < x), ((e : ℚ) ^ j) := by
    calc ((x : ℚ) - 1) ≤ ((x : ℚ) - 1) * ∑ d ∈ D, (d - 1 : ℚ)⁻¹ := by
          have : (0 : ℚ) ≤ (x : ℚ) - 1 := by
            have : (1 : ℚ) ≤ x := by exact_mod_cast hx1
            linarith
          nlinarith
      _ = ∑ e ∈ D, ((x : ℚ) - 1) * (e - 1 : ℚ)⁻¹ := by rw [Finset.mul_sum]
      _ ≤ _ := by
          apply Finset.sum_le_sum
          intro e he
          have he3 := hD e he
          have hpos : (0 : ℚ) < (e : ℚ) - 1 := by
            have : (3 : ℚ) ≤ e := by exact_mod_cast he3
            linarith
          have hg := geo e x X (by omega) hx
          rw [← div_eq_mul_inv, div_le_iff₀ hpos]
          linarith
  have hcast : ((∑ e ∈ D, ∑ j ∈ (range X).filter (fun j => e ^ j < x), e ^ j : ℕ) : ℚ) =
      ∑ e ∈ D, ∑ j ∈ (range X).filter (fun j => e ^ j < x), ((e : ℚ) ^ j) := by
    push_cast; rfl
  have : (x : ℚ) ≤ 1 + ((∑ e ∈ D, ∑ j ∈ (range X).filter (fun j => e ^ j < x), e ^ j : ℕ) : ℚ) := by
    rw [hcast]; linarith
  exact_mod_cast this

end OMA

theorem OMA.solution : type_of% @Erdos124.erdos124.zero := by
  intro D hD hsum
  refine Filter.Eventually.of_forall (fun n => ?_)
  classical
  set X := n + 2 with hX
  set s := (D ×ˢ Finset.range X).filter (fun p : ℕ × ℕ => p.1 ^ p.2 < X) with hs
  have hcond : ∀ a ∈ s, (fun p : ℕ × ℕ => p.1 ^ p.2) a ≤
      1 + ∑ b ∈ s.filter (fun b => (fun p : ℕ × ℕ => p.1 ^ p.2) b <
        (fun p : ℕ × ℕ => p.1 ^ p.2) a), (fun p : ℕ × ℕ => p.1 ^ p.2) b := by
    intro a ha
    have ha' := (Finset.mem_filter.1 ha)
    have hd := hD a.1 (Finset.mem_product.1 ha'.1).1
    have h1 : 1 ≤ a.1 ^ a.2 := Nat.one_le_pow _ _ (by omega)
    exact OMA.key D hD hsum (a.1 ^ a.2) X h1 ha'.2
  have htot : n ≤ ∑ b ∈ s, (fun p : ℕ × ℕ => p.1 ^ p.2) b := by
    have := OMA.key D hD hsum (n + 1) X (by omega) (by omega)
    rw [← hs] at this
    have hle : ∑ b ∈ s.filter (fun b : ℕ × ℕ => b.1 ^ b.2 < n + 1), b.1 ^ b.2 ≤
        ∑ b ∈ s, b.1 ^ b.2 := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    simp only
    omega
  obtain ⟨t, hts, htn⟩ := OMA.brown (fun p : ℕ × ℕ => p.1 ^ p.2) s hcond n htot
  rw [Set.mem_finsetSum]
  have hmaps : ∀ p ∈ t, p.1 ∈ D := fun p hp =>
    (Finset.mem_product.1 (Finset.mem_filter.1 (hts hp)).1).1
  refine ⟨fun d => ∑ p ∈ t.filter (fun p => p.1 = d), p.1 ^ p.2, ?_, ?_⟩
  · intro d _
    refine ⟨(t.filter (fun p => p.1 = d)).image Prod.snd, fun _ _ => Nat.zero_le _, ?_⟩
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro p hp
      rw [(Finset.mem_filter.1 hp).2]
    · intro p hp q hq hpq
      have h1 := (Finset.mem_filter.1 hp).2
      have h2 := (Finset.mem_filter.1 hq).2
      exact Prod.ext (h1.trans h2.symm) hpq
  · rw [Finset.sum_fiberwise_of_maps_to hmaps]
    exact htn
