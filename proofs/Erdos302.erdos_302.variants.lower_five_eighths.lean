import FormalConjectures.ErdosProblems.«302»

/-! Cambie's construction for Erdős Problem 302 uses the small odd integers
together with the interval strictly above the midpoint. -/

open Filter Finset

namespace OMA

private lemma reciprocal_upper {N a : ℕ} (hN : 0 < N) (ha : N / 2 < a) :
    (1 : ℚ) / a < 2 * (1 / (N : ℚ)) := by
  have hn : (0 : ℚ) < N := by exact_mod_cast hN
  have hab : (N : ℚ) < 2 * (a : ℚ) := by exact_mod_cast (show N < 2 * a by omega)
  have h := one_div_lt_one_div_of_lt
    (show (0 : ℚ) < (N : ℚ) / 2 by positivity)
    (show (N : ℚ) / 2 < a by linarith)
  rw [one_div_div] at h
  simpa [div_eq_mul_inv] using h

private lemma reciprocal_lower {N a : ℕ} (ha₀ : 0 < a) (ha : a ≤ N / 4) :
    4 * (1 / (N : ℚ)) ≤ (1 : ℚ) / a := by
  have hap : (0 : ℚ) < a := by exact_mod_cast ha₀
  have hab : 4 * (a : ℚ) ≤ N := by exact_mod_cast (show 4 * a ≤ N by omega)
  have h := one_div_le_one_div_of_le hap (show (a : ℚ) ≤ (N : ℚ) / 4 by linarith)
  rw [one_div_div] at h
  simpa [div_eq_mul_inv] using h

private lemma even_of_odd_left {a b c : ℕ} (ha : a % 2 = 1)
    (h : b * c = a * (c + b)) : b % 2 = 0 ∧ c % 2 = 0 := by
  have hm := congrArg (fun n : ℕ => n % 2) h
  change (b * c) % 2 = (a * (c + b)) % 2 at hm
  have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
  have hc : c % 2 = 0 ∨ c % 2 = 1 := by omega
  rcases hb with hb | hb <;> rcases hc with hc | hc
  · exact ⟨hb, hc⟩
  all_goals simp [Nat.mul_mod, Nat.add_mod, ha, hb, hc] at hm

end OMA

theorem OMA.solution : type_of% @Erdos302.erdos_302.variants.lower_five_eighths := by
  intro f hf ε hε
  obtain ⟨M, hM⟩ := exists_nat_ge (1 / ε)
  refine eventually_atTop.2 ⟨M, fun N hMN => ?_⟩
  let S := (range ((N / 4 + 1) / 2)).image (fun i : ℕ => 2 * i + 1)
  let B := Ioc (N / 2) N
  let A := S ∪ B
  have hS {a : ℕ} (ha : a ∈ S) : 0 < a ∧ a ≤ N / 4 ∧ a % 2 = 1 := by
    obtain ⟨i, hi, rfl⟩ := mem_image.mp ha
    rw [mem_range] at hi
    omega
  have hB {a : ℕ} (ha : a ∈ B) : N / 2 < a ∧ a ≤ N := mem_Ioc.mp ha
  have hA {a : ℕ} (ha : a ∈ A) : (0 < a ∧ a ≤ N / 4 ∧ a % 2 = 1) ∨
      (N / 2 < a ∧ a ≤ N) := (mem_union.mp ha).imp hS hB
  have hsub : A ⊆ Icc 1 N := by
    intro a ha
    rw [mem_Icc]
    rcases hA ha with ⟨ha₀, haN, _⟩ | ⟨ha₀, haN⟩ <;> omega
  have hno : Erdos302.NoUnitFractionTriple A := by
    intro a ha b hb c hc _ _ _ h
    have haI := mem_Icc.mp (hsub ha)
    have hbI := mem_Icc.mp (hsub hb)
    have hcI := mem_Icc.mp (hsub hc)
    have hN : 0 < N := by omega
    have hab : (0 : ℚ) < b := by exact_mod_cast (show 0 < b by omega)
    have hac : (0 : ℚ) < c := by exact_mod_cast (show 0 < c by omega)
    rcases hA ha with ⟨ha₀, haN, haOdd⟩ | ⟨haN, _⟩
    · have haa : (0 : ℚ) < a := by exact_mod_cast ha₀
      have hcross : b * c = a * (c + b) := by
        have ha' := ne_of_gt haa
        have hb' := ne_of_gt hab
        have hc' := ne_of_gt hac
        have he := h
        field_simp at he
        exact_mod_cast he
      obtain ⟨hbEven, hcEven⟩ := OMA.even_of_odd_left haOdd hcross
      have hbN : N / 2 < b := by
        rcases hA hb with ⟨_, _, hbOdd⟩ | ⟨hbN, _⟩
        · omega
        · exact hbN
      have hcN : N / 2 < c := by
        rcases hA hc with ⟨_, _, hcOdd⟩ | ⟨hcN, _⟩
        · omega
        · exact hcN
      have hsmall := OMA.reciprocal_lower ha₀ haN
      have hlargeB := OMA.reciprocal_upper hN hbN
      have hlargeC := OMA.reciprocal_upper hN hcN
      linarith
    · have hlarge := OMA.reciprocal_upper hN haN
      have hboundB : (1 : ℚ) / N ≤ 1 / b :=
        one_div_le_one_div_of_le hab (by exact_mod_cast hbI.2)
      have hboundC : (1 : ℚ) / N ≤ 1 / c :=
        one_div_le_one_div_of_le hac (by exact_mod_cast hcI.2)
      linarith
  have hdisj : Disjoint S B := by
    rw [Finset.disjoint_left]
    intro a ha hb
    have haN := (hS ha).2.1
    have hbN := (hB hb).1
    omega
  have hscard : S.card = (N / 4 + 1) / 2 := by
    change ((range ((N / 4 + 1) / 2)).image (fun i : ℕ => 2 * i + 1)).card = _
    have hinj : Function.Injective (fun i : ℕ => 2 * i + 1) := by
      intro a b hab
      change 2 * a + 1 = 2 * b + 1 at hab
      omega
    rw [card_image_of_injective _ hinj, card_range]
  have hbcard : B.card = N - N / 2 := Nat.card_Ioc _ _
  have hcard : 5 * N ≤ 8 * A.card + 8 := by
    change 5 * N ≤ 8 * (S ∪ B).card + 8
    rw [card_union_of_disjoint hdisj, hscard, hbcard]
    omega
  have hmax : A.card ≤ f N := (hf N).2 ⟨A, hsub, hno, rfl⟩
  have hcount : (5 : ℝ) * N ≤ 8 * (A.card : ℝ) + 8 := by exact_mod_cast hcard
  have hfN : (A.card : ℝ) ≤ f N := by exact_mod_cast hmax
  have hNε : 1 ≤ ε * (N : ℝ) := by
    have hcast : (M : ℝ) ≤ N := by exact_mod_cast hMN
    have hquot : 1 / ε ≤ (N : ℝ) := hM.trans hcast
    simpa only [mul_comm] using (div_le_iff₀ hε).mp hquot
  linarith