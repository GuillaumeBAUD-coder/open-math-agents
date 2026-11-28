import FormalConjectures.ErdosProblems.«302»

/-! Cambie's construction for Erdős Problem 302. -/

open Filter Finset

theorem OMA.solution : type_of% @Erdos302.erdos_302.variants.lower_five_eighths := by
  intro f hf ε hε
  obtain ⟨M, hM⟩ := exists_nat_ge (1 / ε)
  refine eventually_atTop.2 ⟨M, fun N hMN => ?_⟩
  let S := (range ((N / 4 + 1) / 2)).image (2 * · + 1)
  let B := Ioc (N / 2) N
  let A := S ∪ B
  have hS {a} (ha : a ∈ S) : 0 < a ∧ 4 * a ≤ N ∧ a % 2 = 1 := by
    obtain ⟨i, hi, rfl⟩ := mem_image.mp ha; rw [mem_range] at hi; omega
  have hB {a} (ha : a ∈ B) : N < 2 * a ∧ a ≤ N := by
    have := mem_Ioc.mp ha; omega
  have hA {a} (ha : a ∈ A) := (mem_union.mp ha).imp hS hB
  have hsub : A ⊆ Icc 1 N := fun a ha => mem_Icc.2 (by rcases hA ha with ⟨_, _, _⟩ | ⟨_, _⟩ <;> omega)
  have hno : Erdos302.NoUnitFractionTriple A := by
    intro a ha b hb c hc _ _ _ h
    have ⟨ha₁, _⟩ := mem_Icc.mp (hsub ha)
    have ⟨hb₁, hb₂⟩ := mem_Icc.mp (hsub hb)
    have ⟨hc₁, hc₂⟩ := mem_Icc.mp (hsub hc)
    have hq : (b : ℚ) * c = a * (c + b) := by
      have ha' : (a : ℚ) ≠ 0 := by positivity
      have hb' : (b : ℚ) ≠ 0 := by positivity
      have hc' : (c : ℚ) ≠ 0 := by positivity
      field_simp at h; linarith
    have hn : b * c = a * (c + b) := by exact_mod_cast hq
    rcases hA ha with ⟨_, haN, haO⟩ | ⟨haN, _⟩
    · have hm : b % 2 = 0 ∧ c % 2 = 0 := by
        have hm' : (b * c) % 2 = (a * (c + b)) % 2 := congrArg (· % 2) hn
        rcases Nat.mod_two_eq_zero_or_one b with h1 | h1 <;>
          rcases Nat.mod_two_eq_zero_or_one c with h2 | h2
        · exact ⟨h1, h2⟩
        all_goals simp [Nat.mul_mod, Nat.add_mod, haO, h1, h2] at hm'
      have hbN : N < 2 * b := by rcases hA hb with ⟨_, _, _⟩ | ⟨h1, _⟩ <;> omega
      have hcN : N < 2 * c := by rcases hA hc with ⟨_, _, _⟩ | ⟨h1, _⟩ <;> omega
      nlinarith
    · nlinarith
  have hcard : 5 * N ≤ 8 * A.card + 8 := by
    rw [card_union_of_disjoint (disjoint_left.2 fun a ha hb => by have := hS ha; have := hB hb; omega),
      card_image_of_injective _ (fun _ _ h => by omega), card_range, Nat.card_Ioc]
    omega
  have : (A.card : ℝ) ≤ f N := by exact_mod_cast (hf N).2 ⟨A, hsub, hno, rfl⟩
  have : (5 : ℝ) * N ≤ 8 * A.card + 8 := by exact_mod_cast hcard
  have : 1 ≤ ε * N := by rw [← div_le_iff₀' hε]; exact hM.trans (by exact_mod_cast hMN)
  linarith
