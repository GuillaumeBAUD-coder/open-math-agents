import FormalConjectures.ErdosProblems.«5»
import Mathlib

-- Credit: @marcusbuffett
namespace OMA.R_Erdos5_erdos_5_variants_merikoski_measure_R1

open Filter MeasureTheory Real Set Erdos5
open scoped Topology

-- Merikoski's four-shift sieve theorem, in its original prime normalization.
def H1 : Prop := ∀ β : Fin 4 → ℝ, Monotone β →
    ∃ i j, i < j ∧ ∃ n : ℕ → ℕ, StrictMono n ∧
      Tendsto (fun k => (primeGap (n k) : ℝ) / log (Nat.nth Nat.Prime (n k)))
        atTop (𝓝 (β j - β i))

-- Passing from prime normalization to index normalization.
def H2 : Prop := Tendsto (fun n : ℕ => log (Nat.nth Nat.Prime n) / log n) atTop (𝓝 1)

-- Choose a point near the left end of the remaining set. Its forbidden
-- successors cost at most one translated copy of the difference set and ε.
private lemma selectPoint {T ε : ℝ} {S A : Set ℝ} (he : 0 < ε)
    (ha : A ⊆ Icc 0 T) (hp : 0 < volume.real A) :
    ∃ x ∈ A, ∃ B ⊆ A, (∀ y ∈ B, x < y ∧ y-x ∉ S) ∧
      volume.real A - ε - volume.real (S ∩ Icc 0 T) ≤ volume.real B := by
  have hn : A.Nonempty := by
    by_contra! h
    simp [h] at hp
  have hb : BddBelow A := ⟨0, fun y hy => (ha hy).1⟩
  obtain ⟨x,hx,hsmall⟩ := exists_lt_of_csInf_lt hn (show sInf A < sInf A + ε by linarith)
  let I := Icc (sInf A) x
  let D := (fun y : ℝ => y + -x) ⁻¹' (S ∩ Icc 0 T)
  let B := (A \ I) \ D
  have hμ : volume D = volume (S ∩ Icc 0 T) := measure_preimage_add_right _ _ _
  have hD : volume D ≠ ⊤ := hμ ▸ measure_ne_top_of_subset inter_subset_right (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hI : volume I ≠ ⊤ := by dsimp [I]; rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hi : volume.real I ≤ ε := by
    rw [Real.volume_real_Icc_of_le (csInf_le hb hx)]
    linarith
  refine ⟨x,hx,B,fun _ hy => hy.1.1,?_,?_⟩
  · intro y hy
    obtain ⟨⟨hya,hyi⟩,hyd⟩ := hy
    have hxy : x < y := lt_of_not_ge fun h => hyi ⟨csInf_le hb hya,h⟩
    refine ⟨hxy,fun hs => hyd ?_⟩
    change y + -x ∈ S ∩ Icc 0 T
    rw [← sub_eq_add_neg]
    exact ⟨hs,sub_nonneg.mpr hxy.le,by linarith [(ha hx).1,(ha hya).2]⟩
  · have h₁ := le_measureReal_sdiff (s₁ := A) hI
    have h₂ := le_measureReal_sdiff (s₁ := A \ I) hD
    have hr : volume.real D = volume.real (S ∩ Icc 0 T) := congrArg ENNReal.toReal hμ
    dsimp [B]
    linarith

theorem main : H1 → H2 → type_of% @Erdos5.erdos_5.variants.merikoski_measure := by
  intro sieve scale T hT
  let S := limitPointSet ∩ Icc 0 T
  have hS : volume S ≠ ⊤ := measure_ne_top_of_subset inter_subset_right (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  apply (ENNReal.ofReal_le_iff_le_toReal hS).2
  change T / 3 ≤ volume.real S
  by_contra! short
  let ε := (T - 3 * volume.real S) / 6
  have he : 0 < ε := by dsimp [ε]; linarith
  have hvol : volume.real (Icc 0 T) = T := by rw [Real.volume_real_Icc_of_le hT.le, sub_zero]
  obtain ⟨a,ha,A,haA,hax,hA⟩ := selectPoint (S := limitPointSet) he (Set.Subset.rfl : Icc 0 T ⊆ Icc 0 T)
    (hvol.symm ▸ hT)
  change volume.real (Icc 0 T) - ε - volume.real S ≤ volume.real A at hA
  obtain ⟨b,hb,B,hAB,hbx,hB⟩ := selectPoint (S := limitPointSet) he haA
    (by dsimp [ε] at hA; linarith [measureReal_nonneg (μ := volume) (s := S)])
  change volume.real A - ε - volume.real S ≤ volume.real B at hB
  obtain ⟨c,hc,C,hBC,hcx,hC⟩ := selectPoint (S := limitPointSet) he (hAB.trans haA)
    (by dsimp [ε] at hA hB; linarith [measureReal_nonneg (μ := volume) (s := S)])
  change volume.real B - ε - volume.real S ≤ volume.real C at hC
  have hpos : 0 < volume.real C := by dsimp [ε] at hA hB hC; linarith
  obtain ⟨d,hd⟩ : C.Nonempty := by
    by_contra! h
    simp [h] at hpos
  obtain ⟨hab, nab⟩ := hax b hb
  obtain ⟨hac, nac⟩ := hax c (hAB hc)
  obtain ⟨had, nad⟩ := hax d (hAB (hBC hd))
  obtain ⟨hbc, nbc⟩ := hbx c hc
  obtain ⟨hbd, nbd⟩ := hbx d (hBC hd)
  obtain ⟨hcd, ncd⟩ := hcx d hd
  let β : Fin 4 → ℝ := ![a,b,c,d]
  have hm : Monotone β := by
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    fin_cases i <;> first | exact hab.le | exact hbc.le | exact hcd.le
  obtain ⟨i,j,hij,n,hn,hlim⟩ := sieve β hm
  have hit : β j - β i ∈ limitPointSet := by
    apply (mem_limitPointSet_iff _).2
    refine ⟨n,hn,?_⟩
    have h := hlim.mul (scale.comp hn.tendsto_atTop)
    rw [mul_one] at h
    apply h.congr
    intro k
    have hp : 0 < log (Nat.nth Nat.Prime (n k)) :=
      Real.log_pos (by exact_mod_cast (Nat.prime_nth_prime (n k)).one_lt)
    simp [normalizedGap, div_mul_div_cancel₀, hp.ne']
  fin_cases i <;> fin_cases j <;> first
    | exact (by decide : ¬ _ < _) hij
    | exact nab hit
    | exact nac hit
    | exact nad hit
    | exact nbc hit
    | exact nbd hit
    | exact ncd hit

end OMA.R_Erdos5_erdos_5_variants_merikoski_measure_R1
