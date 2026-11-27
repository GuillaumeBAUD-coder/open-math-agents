import OMAReductions.R_Erdos261_erdos_261_parts_iii_R1

/-! Each set of the family is enumerated increasingly by `Nat.nth`. The enumeration determines the
set, so the map is injective; the real series `∑ a / 2^a` over the set is the series along the
enumeration, and since its terms and its sum `1` are rational it also converges in `ℚ`. -/

open scoped Cardinal

namespace OMA.E261iii

theorem rep_of_set (A : Set ℕ) (hinf : A.Infinite) (hpos : ∀ a ∈ A, 1 ≤ a)
    (hsum : HasSum (A.indicator (fun a : ℕ => (a : ℝ) / 2 ^ a)) 1) :
    Erdos261.Erdos261InfiniteRepresentation 1 (Nat.nth (· ∈ A)) := by
  have hinf' : (Set.ofPred (· ∈ A)).Infinite := hinf
  have hrange : Set.range (Nat.nth (· ∈ A)) = A := Nat.range_nth_of_infinite hinf'
  have hR : HasSum ((fun a : ℕ => (a : ℝ) / 2 ^ a) ∘ Nat.nth (· ∈ A)) 1 := by
    have h1 : HasSum ((fun a : ℕ => (a : ℝ) / 2 ^ a) ∘ ((↑) : A → ℕ)) 1 :=
      hasSum_subtype_iff_indicator.mpr hsum
    have h2 : HasSum ((fun a : ℕ => (a : ℝ) / 2 ^ a) ∘
        ((↑) : Set.range (Nat.nth (· ∈ A)) → ℕ)) 1 := by
      rw [hrange]
      exact h1
    exact (Function.Injective.hasSum_range_iff (f := fun a : ℕ => (a : ℝ) / 2 ^ a)
      (Nat.nth_injective hinf')).mp h2
  have hQ : HasSum ((fun a : ℕ => (a : ℚ) / 2 ^ a) ∘ Nat.nth (· ∈ A)) 1 := by
    have hcomp : (⇑(Rat.castHom ℝ)) ∘ ((fun a : ℕ => (a : ℚ) / 2 ^ a) ∘ Nat.nth (· ∈ A)) =
        (fun a : ℕ => (a : ℝ) / 2 ^ a) ∘ Nat.nth (· ∈ A) := by
      funext k
      simp
    have hone : (Rat.castHom ℝ) 1 = (1 : ℝ) := by simp
    have h3 : HasSum ((⇑(Rat.castHom ℝ)) ∘
        ((fun a : ℕ => (a : ℚ) / 2 ^ a) ∘ Nat.nth (· ∈ A))) ((Rat.castHom ℝ) 1) := by
      rw [hcomp, hone]
      exact hR
    exact (Topology.IsInducing.hasSum_iff (g := Rat.castHom ℝ)
      (show Topology.IsInducing ⇑(Rat.castHom ℝ) from Rat.isEmbedding_coe_real.isInducing)
      _ _).mp h3
  refine ⟨Nat.nth_strictMono hinf', fun k => hpos _ (Nat.nth_mem_of_infinite hinf' k),
    hQ.summable, hQ.tsum_eq.symm⟩

end OMA.E261iii

theorem OMA.solution : OMA.R_Erdos261_erdos_261_parts_iii_R1.H3 := by
  rintro ⟨A, hinj, hA⟩
  have key : Function.Injective
      (fun b : ℕ → Bool => (⟨Nat.nth (· ∈ A b),
        OMA.E261iii.rep_of_set (A b) (hA b).1 (hA b).2.1 (hA b).2.2⟩ :
        {a : ℕ → ℕ | Erdos261.Erdos261InfiniteRepresentation 1 a})) := by
    intro b b' h
    apply hinj
    have h' : Nat.nth (· ∈ A b) = Nat.nth (· ∈ A b') := congrArg Subtype.val h
    have h1 : Set.range (Nat.nth (· ∈ A b)) = A b := Nat.range_nth_of_infinite (hA b).1
    have h2 : Set.range (Nat.nth (· ∈ A b')) = A b' := Nat.range_nth_of_infinite (hA b').1
    rw [← h1, ← h2, h']
  have := Cardinal.mk_le_of_injective key
  rwa [← Cardinal.power_def, Cardinal.mk_bool, Cardinal.mk_nat, Cardinal.two_power_aleph0] at this
