import FormalConjectures.ErdosProblems.«441»

-- Problem: Erdős Problem 441 — lower bound
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/441.lean:108 (declaration Erdos441.erdos_441.variants.lower_bound)
-- Credit: @philipsaint (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA441

open Finset

/-- The construction: all of `[1, u]` together with the even numbers `2j` for `u/2 < j ≤ u`,
where `u = ⌊√(N/2)⌋`. -/
def constr (u : ℕ) : Finset ℕ := Icc 1 u ∪ (Ioc (u / 2) u).image (fun j => 2 * j)

lemma constr_card (u : ℕ) : 2 * (constr u).card ≥ 3 * u := by
  unfold constr
  rw [card_union_of_disjoint]
  · rw [card_image_of_injective _ (fun a b h => by simpa using h)]
    simp only [Nat.card_Icc, Nat.card_Ioc]
    omega
  · rw [disjoint_left]
    intro a ha hb
    simp only [mem_Icc] at ha
    simp only [mem_image, mem_Ioc] at hb
    obtain ⟨j, ⟨hj1, _⟩, rfl⟩ := hb
    omega

lemma mem_constr {u a : ℕ} (h : a ∈ constr u) :
    (1 ≤ a ∧ a ≤ u) ∨ ∃ j, 1 ≤ j ∧ j ≤ u ∧ a = 2 * j := by
  unfold constr at h
  simp only [mem_union, mem_Icc, mem_image, mem_Ioc] at h
  rcases h with h | ⟨j, ⟨h1, h2⟩, rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨j, by omega, h2, rfl⟩

lemma constr_lcm {N u : ℕ} (hu : 2 * (u * u) ≤ N) :
    ∀ a ∈ constr u, ∀ b ∈ constr u, Nat.lcm a b ≤ N := by
  intro a ha b hb
  rcases mem_constr ha with ⟨_, ha2⟩ | ⟨i, _, hi2, rfl⟩ <;>
    rcases mem_constr hb with ⟨_, hb2⟩ | ⟨j, _, hj2, rfl⟩ <;>
    first
    | exact (Nat.div_le_self _ _).trans (by nlinarith)
    | rw [Nat.lcm_mul_left]; exact (Nat.mul_le_mul_left 2 (Nat.div_le_self _ _)).trans (by nlinarith)

lemma constr_sub {N u : ℕ} (hu : 2 * (u * u) ≤ N) : constr u ⊆ Icc 1 N := by
  intro a ha
  rw [mem_Icc]
  have : u ≤ u * u := Nat.le_mul_self u
  rcases mem_constr ha with ⟨h1, h2⟩ | ⟨j, h1, h2, rfl⟩
  · omega
  · omega

lemma g_ge (N : ℕ) : (constr (Nat.sqrt (N / 2))).card ≤ Erdos441.g N := by
  set u := Nat.sqrt (N / 2)
  have hu : 2 * (u * u) ≤ N := by
    have : u * u ≤ N / 2 := Nat.sqrt_le (N / 2)
    omega
  apply le_csSup
  · refine ⟨N, ?_⟩
    rintro k ⟨A, hA, -, rfl⟩
    simpa using Finset.card_le_card hA
  · exact ⟨constr u, constr_sub hu, constr_lcm hu, rfl⟩

end OMA441

theorem OMA.solution : type_of% @Erdos441.erdos_441.variants.lower_bound := by
  refine ⟨2, fun N => ?_⟩
  set u := Nat.sqrt (N / 2) with hu_def
  have hcard := OMA441.constr_card u
  have hg := OMA441.g_ge N
  have hlt : N / 2 < (u + 1) * (u + 1) := Nat.lt_succ_sqrt (N / 2)
  have hN : (N : ℝ) < 2 * ((u : ℝ) + 1) ^ 2 := by
    have : N < 2 * ((u + 1) * (u + 1)) := by omega
    have : (N : ℝ) < ((2 * ((u + 1) * (u + 1)) : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this
    nlinarith
  have hsq : √(9 / 8 * (N : ℝ)) ≤ 3 / 2 * ((u : ℝ) + 1) := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  have h1 : (3 : ℝ) * u ≤ 2 * ((OMA441.constr u).card : ℝ) := by exact_mod_cast hcard
  have h2 : ((OMA441.constr u).card : ℝ) ≤ (Erdos441.g N : ℝ) := by exact_mod_cast hg
  linarith
