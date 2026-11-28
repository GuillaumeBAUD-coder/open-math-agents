import OMAStatements.S_oeis_a092905
import Mathlib

open OMA.S_oeis_a092905

namespace A092905Proof

/-- Multisets of positive integers with `k` elements and sum at most `N`. -/
def B (N k : ℕ) : Finset (Multiset ℕ) :=
  (((Finset.Icc 1 N).sym k).filter (fun s : Sym ℕ k => (s : Multiset ℕ).sum ≤ N)).image
    (fun s : Sym ℕ k => s.1)

lemma mem_B {N k : ℕ} {μ : Multiset ℕ} :
    μ ∈ B N k ↔ Multiset.card μ = k ∧ (∀ x ∈ μ, 1 ≤ x) ∧ μ.sum ≤ N := by
  constructor
  · intro hμ
    simp only [B, Finset.mem_image, Finset.mem_filter, Finset.mem_sym_iff] at hμ
    obtain ⟨s, ⟨hs, hsum⟩, rfl⟩ := hμ
    refine ⟨s.2, fun x hx => ?_, hsum⟩
    have := hs x hx
    simp only [Finset.mem_Icc] at this
    exact this.1
  · rintro ⟨hc, hp, hs⟩
    simp only [B, Finset.mem_image, Finset.mem_filter, Finset.mem_sym_iff]
    refine ⟨⟨μ, hc⟩, ⟨fun x hx => ?_, hs⟩, rfl⟩
    have hx' : x ∈ μ := hx
    simp only [Finset.mem_Icc]
    exact ⟨hp x hx', le_trans (Multiset.le_sum_of_mem hx') hs⟩

/-- Subtract one from every element and drop the zeros. -/
def g (μ : Multiset ℕ) : Multiset ℕ := (μ.map (fun x => x - 1)).filter (fun x => 0 < x)

lemma g_cons_pos (a : ℕ) (s : Multiset ℕ) (h : 1 < a) : g (a ::ₘ s) = (a - 1) ::ₘ g s := by
  unfold g
  rw [Multiset.map_cons, Multiset.filter_cons_of_pos _ (by omega)]

lemma g_cons_one (s : Multiset ℕ) : g (1 ::ₘ s) = g s := by
  unfold g
  rw [Multiset.map_cons, Multiset.filter_cons_of_neg _ (by omega)]

lemma card_g_le (μ : Multiset ℕ) : Multiset.card (g μ) ≤ Multiset.card μ := by
  unfold g
  exact (Multiset.card_le_card (Multiset.filter_le _ _)).trans (by rw [Multiset.card_map])

lemma g_spec (μ : Multiset ℕ) (hμ : ∀ x ∈ μ, 1 ≤ x) :
    (g μ).map (· + 1) + Multiset.replicate (Multiset.card μ - Multiset.card (g μ)) 1 = μ ∧
    μ.sum = (g μ).sum + Multiset.card μ ∧ (∀ x ∈ g μ, 1 ≤ x) := by
  induction μ using Multiset.induction_on with
  | empty => simp [g]
  | cons a s ih =>
    have ha : 1 ≤ a := hμ a (Multiset.mem_cons_self a s)
    have hs : ∀ x ∈ s, 1 ≤ x := fun x hx => hμ x (Multiset.mem_cons_of_mem hx)
    obtain ⟨ih1, ih2, ih3⟩ := ih hs
    have hle := card_g_le s
    rcases Nat.lt_or_ge 1 a with h | h
    · rw [g_cons_pos a s h]
      refine ⟨?_, ?_, ?_⟩
      · rw [Multiset.map_cons, Multiset.card_cons, Multiset.card_cons,
          show Multiset.card s + 1 - (Multiset.card (g s) + 1) =
            Multiset.card s - Multiset.card (g s) by omega, Multiset.cons_add, ih1]
        congr 1
        omega
      · rw [Multiset.sum_cons, Multiset.sum_cons, Multiset.card_cons, ih2]
        omega
      · intro x hx
        rw [Multiset.mem_cons] at hx
        rcases hx with rfl | hx
        · omega
        · exact ih3 x hx
    · have ha1 : a = 1 := by omega
      subst ha1
      rw [g_cons_one]
      refine ⟨?_, ?_, ih3⟩
      · rw [Multiset.card_cons, show Multiset.card s + 1 - Multiset.card (g s) =
            (Multiset.card s - Multiset.card (g s)) + 1 by omega, Multiset.replicate_succ,
          Multiset.add_cons, ih1]
      · rw [Multiset.sum_cons, Multiset.card_cons, ih2]
        omega

lemma g_inv (ν : Multiset ℕ) (hν : ∀ x ∈ ν, 1 ≤ x) (r : ℕ) :
    g (ν.map (· + 1) + Multiset.replicate r 1) = ν := by
  unfold g
  rw [Multiset.map_add, Multiset.filter_add, Multiset.map_map, Multiset.map_replicate]
  have h1 : Multiset.map ((fun x => x - 1) ∘ (· + 1)) ν = ν := by
    conv_rhs => rw [← Multiset.map_id ν]
    apply Multiset.map_congr rfl
    intro x _
    simp
  rw [h1, Multiset.filter_eq_self.mpr (fun x hx => by have := hν x hx; omega)]
  rw [Multiset.filter_eq_nil.mpr (fun x hx => by
    rw [Multiset.eq_of_mem_replicate hx]; omega)]
  simp

lemma card_B_succ (N k : ℕ) (hN : k + 1 ≤ N) :
    (B N (k + 1)).card = ∑ j ∈ Finset.range (k + 2), (B (N - (k + 1)) j).card := by
  rw [← Finset.card_sigma]
  symm
  apply Finset.card_nbij'
    (fun x => x.2.map (· + 1) + Multiset.replicate (k + 1 - x.1) 1)
    (fun μ => ⟨Multiset.card (g μ), g μ⟩)
  · rintro ⟨j, ν⟩ hx
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.coe_range, Set.mem_Iio,
      Finset.mem_coe, mem_B] at hx
    obtain ⟨hj, hc, hp, hs⟩ := hx
    simp only [Finset.mem_coe, mem_B]
    refine ⟨?_, ?_, ?_⟩
    · rw [Multiset.card_add, Multiset.card_map, Multiset.card_replicate]
      omega
    · intro x hx
      rw [Multiset.mem_add] at hx
      rcases hx with hx | hx
      · obtain ⟨y, _, rfl⟩ := Multiset.mem_map.mp hx
        omega
      · rw [Multiset.eq_of_mem_replicate hx]
    · rw [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul, mul_one]
      have : (ν.map (· + 1)).sum = ν.sum + Multiset.card ν := by
        rw [Multiset.sum_map_add, Multiset.map_const', Multiset.sum_replicate, smul_eq_mul,
          mul_one, Multiset.map_id']
      rw [this]
      omega
  · intro μ hμ
    simp only [Finset.mem_coe, mem_B] at hμ
    obtain ⟨hc, hp, hs⟩ := hμ
    obtain ⟨_, h2, h3⟩ := g_spec μ hp
    have hle := card_g_le μ
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.coe_range, Set.mem_Iio,
      Finset.mem_coe, mem_B]
    refine ⟨by omega, by simp, h3, by omega⟩
  · rintro ⟨j, ν⟩ hx
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.coe_range, Set.mem_Iio,
      Finset.mem_coe, mem_B] at hx
    obtain ⟨hj, hc, hp, hs⟩ := hx
    simp only
    rw [g_inv ν hp, hc]
  · intro μ hμ
    simp only [Finset.mem_coe, mem_B] at hμ
    obtain ⟨hc, hp, hs⟩ := hμ
    obtain ⟨h1, _, _⟩ := g_spec μ hp
    simp only
    rw [← hc]
    exact h1

lemma card_B_zero (N : ℕ) : (B N 0).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨0, ?_⟩
  ext μ
  rw [mem_B, Finset.mem_singleton]
  constructor
  · rintro ⟨hc, _, _⟩
    exact Multiset.card_eq_zero.mp hc
  · rintro rfl
    simp

lemma card_B_eq_T : ∀ N k : ℕ, (B N k).card = T N k := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro k
    cases k with
    | zero => rw [card_B_zero, T]
    | succ k =>
      rw [T]
      by_cases h : k + 1 ≤ N
      · rw [dif_pos h, card_B_succ N k h]
        apply Finset.sum_congr rfl
        intro j _
        exact ih (N - (k + 1)) (by omega) j
      · rw [dif_neg h, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro μ hμ
        rw [mem_B] at hμ
        obtain ⟨hc, hp, hs⟩ := hμ
        obtain ⟨_, h2, _⟩ := g_spec μ hp
        omega

lemma a_eq_card (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) : a n m = (B (n - 1) (m - 1)).card := by
  unfold a
  rw [← Finset.card_sigma]
  refine Finset.card_bij'
    (fun x _ => x.1.parts.erase x.2)
    (fun μ hμ => ⟨⟨(n - μ.sum) ::ₘ μ, ?_, ?_⟩, n - μ.sum⟩) ?_ ?_ ?_ ?_
  · intro i hi
    rw [mem_B] at hμ
    rw [Multiset.mem_cons] at hi
    rcases hi with rfl | hi
    · omega
    · exact hμ.2.1 i hi
  · rw [mem_B] at hμ
    rw [Multiset.sum_cons]
    omega
  · rintro ⟨p, v⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and,
      Multiset.mem_toFinset] at hx
    obtain ⟨hc, hv⟩ := hx
    rw [mem_B]
    dsimp only
    refine ⟨?_, ?_, ?_⟩
    · rw [Multiset.card_erase_of_mem hv, hc]
      rfl
    · intro x hx
      exact p.parts_pos (Multiset.mem_of_mem_erase hx)
    · have h1 := Multiset.sum_erase hv
      have h2 := p.parts_sum
      have h3 := p.parts_pos hv
      omega
  · intro μ hμ
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and,
      Multiset.mem_toFinset, Multiset.card_cons, Multiset.mem_cons_self, and_true]
    rw [mem_B] at hμ
    omega
  · rintro ⟨p, v⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and,
      Multiset.mem_toFinset] at hx
    obtain ⟨hc, hv⟩ := hx
    have h1 := Multiset.sum_erase hv
    have h2 := p.parts_sum
    have hval : n - (p.parts.erase v).sum = v := by omega
    simp only [hval]
    congr 1
    · ext1
      exact Multiset.cons_erase hv
  · intro μ hμ
    simp

end A092905Proof

open A092905Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a092905.main := by
  intro n m hn hm _
  rw [a_eq_card n m hn hm, card_B_eq_T]
