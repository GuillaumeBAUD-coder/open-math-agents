import OMAReductions.R_Erdos933_erdos_933_variants_mahler_R1

-- Step Erdos933.erdos_933.variants.mahler.R1.H2
-- Credit: @caa1982

open Filter Asymptotics

private def buildM (N₀ : ℕ → ℕ) : ℕ → ℕ
  | 0 => N₀ 0
  | k + 1 => max (buildM N₀ k + 1) (N₀ (k + 1))

private lemma buildM_ge (N₀ : ℕ → ℕ) (k : ℕ) : N₀ k ≤ buildM N₀ k := by
  cases k with
  | zero => exact le_rfl
  | succ k => exact le_max_right _ _

private lemma buildM_strictMono (N₀ : ℕ → ℕ) : StrictMono (buildM N₀) :=
  strictMono_nat_of_lt_succ fun k =>
    Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)

private def idxOf (M : ℕ → ℕ) (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sup (fun k => if M k ≤ n then k else 0)

private lemma buildM_idxOf_le (N₀ : ℕ → ℕ) (n : ℕ) (hn0 : buildM N₀ 0 ≤ n) :
    buildM N₀ (idxOf (buildM N₀) n) ≤ n := by
  unfold idxOf
  have hmem : ∀ s : Finset ℕ,
      (∀ k ∈ s, buildM N₀ (if buildM N₀ k ≤ n then k else 0) ≤ n) →
      buildM N₀ (s.sup (fun k => if buildM N₀ k ≤ n then k else 0)) ≤ n := by
    intro s hs
    induction s using Finset.induction_on with
    | empty => simpa using hn0
    | insert a s ha ih =>
      rw [Finset.sup_insert]
      have ha' := hs a (Finset.mem_insert_self a s)
      have hs' := ih (fun k hk => hs k (Finset.mem_insert_of_mem hk))
      rcases le_total (if buildM N₀ a ≤ n then a else 0)
          (s.sup (fun k => if buildM N₀ k ≤ n then k else 0)) with hle | hle
      · rwa [sup_eq_right.mpr hle]
      · rwa [sup_eq_left.mpr hle]
  refine hmem (Finset.range (n + 1)) (fun k _ => ?_)
  split_ifs with h
  · exact h
  · exact hn0

private lemma le_idxOf (N₀ : ℕ → ℕ) (K n : ℕ) (hKn : buildM N₀ K ≤ n) :
    K ≤ idxOf (buildM N₀) n := by
  have hKid : K ≤ buildM N₀ K := (buildM_strictMono N₀).id_le K
  have hK_mem : K ∈ Finset.range (n + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (hKid.trans hKn))
  have hle := Finset.le_sup (f := fun k => if buildM N₀ k ≤ n then k else 0) hK_mem
  simpa [idxOf, hKn] using hle

theorem OMA.solution : OMA.R_Erdos933_erdos_933_variants_mahler_R1.H2 := by
  intro F hF
  have hN : ∀ k : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → F n < (n : ℝ) ^ (1 + 1 / ((k : ℝ) + 1)) := by
    intro k
    have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    simpa [Filter.eventually_atTop] using hF (1 / ((k : ℝ) + 1)) hpos
  choose N₀ hN₀ using hN
  let c (n : ℕ) : ℝ := 1 / ((idxOf (buildM N₀) n : ℝ) + 1)
  refine ⟨c, ?_, ?_⟩
  · change c =o[atTop] (fun _ : ℕ => (1 : ℝ))
    rw [Asymptotics.isLittleO_one_iff, Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨K, hK⟩ := exists_nat_one_div_lt hε
    refine ⟨buildM N₀ K, fun n hn => ?_⟩
    have hKi : K ≤ idxOf (buildM N₀) n := le_idxOf N₀ K n hn
    have hpos : (0 : ℝ) ≤ c n := by positivity
    have hle : c n ≤ 1 / ((K : ℝ) + 1) := by
      dsimp only [c]
      gcongr
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hpos]
    exact lt_of_le_of_lt hle hK
  · rw [Filter.eventually_atTop]
    refine ⟨buildM N₀ 0, fun n hn => ?_⟩
    have hMn : buildM N₀ (idxOf (buildM N₀) n) ≤ n := buildM_idxOf_le N₀ n hn
    exact hN₀ (idxOf (buildM N₀) n) n ((buildM_ge N₀ _).trans hMn)
