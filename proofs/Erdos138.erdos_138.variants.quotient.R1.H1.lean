import OMAReductions.R_Erdos138_erdos_138_variants_quotient_R1

-- Step Erdos138.erdos_138.variants.quotient.R1.H1: hypothesis H1 of reduction Erdos138.erdos_138.variants.quotient.R1
-- Credit: @Williamnowak
-- H1 := ∀ k : ℕ, 1 ≤ k → (Erdos138.monoAP_guarantee_set 2 k).Nonempty ∧ 1 ≤ Erdos138.W k

/-!
Van der Waerden's theorem from the Hales–Jewett theorem in Mathlib
(`Combinatorics.Line.exists_mono_in_high_dimension`), the same route as the merged proof
`proofs/Erdos138.monoAP_guarantee_set_nonempty.lean`.

A point `w : ι → Fin k` is sent to `1 + ∑ i, w i`. Along a combinatorial line the coordinate sum
is `a + j * d`, where `d ≥ 1` is the number of moving coordinates, so a monochromatic line gives a
monochromatic arithmetic progression of length `k` inside `[1, 1 + |ι| * k]`.

Positivity of `W k`: for `k ≥ 1` the number `0` does not guarantee a progression, since the
interval `[1, 0]` is empty; the infimum of a nonempty set of naturals is attained.
-/

namespace OMA

/-- Along a combinatorial line the coordinate sum is an arithmetic progression in the
parameter, whose difference is the number of moving coordinates. -/
lemma line_sum {k : ℕ} {ι : Type} [Fintype ι]
    (l : Combinatorics.Line (Fin k) ι) (j : Fin k) :
    ∑ i, ((l j i : Fin k) : ℕ) =
      (∑ i, (l.idxFun i).elim 0 (fun x => (x : ℕ))) +
        (j : ℕ) * (Finset.univ.filter fun i => l.idxFun i = none).card := by
  rw [Finset.card_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  cases h : l.idxFun i <;> simp [Combinatorics.Line.coe_apply, h]

/-- Van der Waerden's theorem, in the form used by Erdős Problem 138. -/
theorem vdw (r k : ℕ) : (Erdos138.monoAP_guarantee_set r k).Nonempty := by
  classical
  obtain ⟨ι, _, hj⟩ := Combinatorics.Line.exists_mono_in_high_dimension (Fin k) (Fin r)
  refine ⟨1 + Fintype.card ι * k, fun coloring => ?_⟩
  have hbd : ∀ w : ι → Fin k,
      1 + ∑ i, ((w i : Fin k) : ℕ) ∈ Finset.Icc 1 (1 + Fintype.card ι * k) := by
    intro w
    have h : ∑ i, ((w i : Fin k) : ℕ) ≤ ∑ _i : ι, k :=
      Finset.sum_le_sum fun i _ => (w i).isLt.le
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at h
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  obtain ⟨l, c, hc⟩ := hj fun w => coloring ⟨_, hbd w⟩
  obtain ⟨i₀, hi₀⟩ := l.proper
  have hd : 0 < (Finset.univ.filter fun i => l.idxFun i = none).card :=
    Finset.card_pos.mpr ⟨i₀, by simp [hi₀]⟩
  generalize hdd : (Finset.univ.filter fun i => l.idxFun i = none).card = d at hd
  have hval : ∀ j : Fin k, 1 + ∑ i, ((l j i : Fin k) : ℕ) =
      (1 + ∑ i, (l.idxFun i).elim 0 (fun x => (x : ℕ))) + (j : ℕ) * d := by
    intro j
    rw [line_sum, hdd, Nat.add_assoc]
  generalize (1 + ∑ i, (l.idxFun i).elim 0 (fun x => (x : ℕ))) = a at hval
  have himg : (fun x : Finset.Icc 1 (1 + Fintype.card ι * k) => x.1) ''
      (Set.range fun j : Fin k =>
        (⟨_, hbd (l j)⟩ : Finset.Icc 1 (1 + Fintype.card ι * k))) =
      Set.range fun j : Fin k => a + (j : ℕ) * d := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext hval)
  have hinj : Function.Injective fun j : Fin k => a + (j : ℕ) * d := by
    intro x y hxy
    have h1 : (x : ℕ) * d = (y : ℕ) * d := Nat.add_left_cancel hxy
    exact Fin.ext (Nat.eq_of_mul_eq_mul_right hd h1)
  refine ⟨c, Set.range fun j : Fin k =>
    (⟨_, hbd (l j)⟩ : Finset.Icc 1 (1 + Fintype.card ι * k)), ⟨a, d, ?_, ?_⟩, ?_⟩
  · have hcard : ENat.card (Set.range fun j : Fin k => a + (j : ℕ) * d) = (k : ℕ∞) := by
      rw [← ENat.card_congr (Equiv.ofInjective _ hinj), ENat.card_eq_coe_fintype_card,
        Fintype.card_fin]
    exact (congrArg (fun s : Set ℕ => ENat.card s) himg).trans hcard
  · refine himg.trans ?_
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨j, by exact_mod_cast j.isLt, by simp⟩
    · rintro ⟨n, hn, rfl⟩
      exact ⟨⟨n, by exact_mod_cast hn⟩, by simp⟩
  · rintro _ ⟨j, rfl⟩
    exact hc j

/-- The empty interval `[1, 0]` contains no progression of positive length. -/
theorem zero_not_mem (r k : ℕ) (hk : 1 ≤ k) : 0 ∉ Erdos138.monoAP_guarantee_set r k := by
  intro h
  have hemp : IsEmpty (Finset.Icc 1 0 : Finset ℕ) := ⟨fun x => by
    have hx := Finset.mem_Icc.mp x.2
    omega⟩
  obtain ⟨c, ap, ⟨a, d, hcard, -⟩, -⟩ := h fun x => (hemp.false x).elim
  have h0 : (fun x : (Finset.Icc 1 0 : Finset ℕ) => x.1) '' ap = (∅ : Set ℕ) := by
    ext y
    simp only [Set.mem_image, Set.mem_empty_iff_false, iff_false]
    rintro ⟨x, -, -⟩
    exact hemp.false x
  have hcard' : ENat.card (∅ : Set ℕ) = (k : ℕ∞) :=
    (congrArg (fun s : Set ℕ => ENat.card s) h0).symm.trans hcard
  have hk0 : ((k : ℕ) : ℕ∞) = 0 := by
    rw [← hcard']
    simp
  have hk' : k = 0 := by exact_mod_cast hk0
  omega

end OMA

theorem OMA.solution : OMA.R_Erdos138_erdos_138_variants_quotient_R1.H1 := by
  intro k hk
  have hne := OMA.vdw 2 k
  refine ⟨hne, ?_⟩
  have hmem : Erdos138.W k ∈ Erdos138.monoAP_guarantee_set 2 k := Nat.sInf_mem hne
  by_contra hlt
  have h0 : Erdos138.W k = 0 := by omega
  rw [h0] at hmem
  exact OMA.zero_not_mem 2 k hk hmem
