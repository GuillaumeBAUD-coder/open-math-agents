import OMAReductions.R_Erdos261_erdos_261_parts_iii_R1

/-!
Enumerating an infinite set in increasing order preserves its weighted sum.
The range of the enumeration recovers the set, so distinct sets give distinct representations.
-/

open scoped Cardinal

theorem OMA.solution : OMA.R_Erdos261_erdos_261_parts_iii_R1.H3 := by
  classical
  rintro ⟨A, hA, hsets⟩
  let seq (b : ℕ → Bool) := Nat.nth (fun n => n ∈ A b)
  have hrange (b : ℕ → Bool) : Set.range (seq b) = A b :=
    Nat.range_nth_of_infinite (hsets b).1
  have hrep (b : ℕ → Bool) : Erdos261.Erdos261InfiniteRepresentation 1 (seq b) := by
    have hmono : StrictMono (seq b) := Nat.nth_strictMono (hsets b).1
    let weight (n : ℕ) : ℝ := (n : ℝ) / 2 ^ n
    have hreal : HasSum (weight ∘ seq b) 1 := by
      apply (hmono.injective.hasSum_range_iff (f := weight)).mp
      apply (hasSum_subtype_iff_indicator (f := weight)).mpr
      rw [hrange b]
      exact (hsets b).2.2
    -- The real sum is rational, so the same partial sums converge to it in ℚ.
    have hrat : HasSum (fun k => (seq b k : ℚ) / 2 ^ seq b k) 1 := by
      have he : Topology.IsInducing (Rat.castHom ℝ) := Rat.isEmbedding_coe_real.isInducing
      apply (he.hasSum_iff _ _).mp
      simpa [Function.comp_def, weight] using hreal
    exact ⟨hmono, fun k => (hsets b).2.1 _ (Nat.nth_mem_of_infinite (hsets b).1 k),
      hrat.summable, hrat.tsum_eq.symm⟩
  let toRep (b : ℕ → Bool) : {a : ℕ → ℕ | Erdos261.Erdos261InfiniteRepresentation 1 a} :=
    ⟨seq b, hrep b⟩
  have hinj : Function.Injective toRep := by
    intro b c h
    apply hA
    rw [← hrange b, ← hrange c]
    exact congrArg Set.range (congrArg Subtype.val h)
  calc
    𝔠 = #(ℕ → Bool) := by simp [Cardinal.two_power_aleph0]
    _ ≤ _ := Cardinal.mk_le_of_injective hinj
