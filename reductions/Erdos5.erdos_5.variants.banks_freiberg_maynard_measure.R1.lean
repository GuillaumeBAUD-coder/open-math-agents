import FormalConjectures.ErdosProblems.«5»
import Mathlib

-- Credit: @marcusbuffett
namespace OMA.R_Erdos5_erdos_5_variants_banks_freiberg_maynard_measure_R1

open Filter MeasureTheory Real Set Erdos5
open scoped Topology

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

private lemma pack {S : Set ℝ} {T ε : ℝ} (he : 0 < ε) (n : ℕ) {A : Set ℝ}
    (ha : A ⊆ Icc 0 T)
    (hp : n * (ε + volume.real (S ∩ Icc 0 T)) < volume.real A) :
    ∃ β : Fin (n+1) → ℝ, (∀ i, β i ∈ A) ∧
      ∀ i j, i < j → β i < β j ∧ β j - β i ∉ S := by
  induction n generalizing A with
  | zero =>
    obtain ⟨x,hx⟩ : A.Nonempty := by
      by_contra! h
      simp [h] at hp
    exact ⟨fun _ => x,fun _ => hx,fun i j hij => by omega⟩
  | succ n ih =>
    have hμ := measureReal_nonneg (μ := volume) (s := S ∩ Icc 0 T)
    have hpos : 0 < volume.real A := (mul_nonneg (Nat.cast_nonneg _) (by linarith)).trans_lt hp
    obtain ⟨x,hx,B,hBA,avoid,hB⟩ := selectPoint (S := S) he ha hpos
    obtain ⟨β,hβ,havoid⟩ := ih (hBA.trans ha) (by push_cast at hp; nlinarith)
    refine ⟨Fin.cons x β,?_,?_⟩
    · intro i
      refine Fin.cases ?_ (fun t => ?_) i
      · exact hx
      · exact hBA (hβ t)
    · intro i j
      refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) j
      · intro h; exact (lt_irrefl _ h).elim
      · intro _; exact avoid _ (hβ b)
      · intro h; exact (Fin.not_lt_zero _ h).elim
      · intro h; exact havoid a b (Fin.succ_lt_succ_iff.mp h)

-- The nine-shift difference theorem of Banks, Freiberg and Maynard, in its original prime normalization.
def H1 : Prop := ∀ β : Fin 9 → ℝ, (∀ i, 0 ≤ β i) → StrictMono β →
    ∃ i j, i < j ∧ ∃ n : ℕ → ℕ, StrictMono n ∧
      Tendsto (fun k => (primeGap (n k) : ℝ) / log (Nat.nth Nat.Prime (n k)))
        atTop (𝓝 (β j - β i))

-- Passing from prime normalization to index normalization.
def H2 : Prop := Tendsto (fun n : ℕ => log (Nat.nth Nat.Prime n) / log n) atTop (𝓝 1)

theorem main : H1 → H2 → type_of% @Erdos5.erdos_5.variants.banks_freiberg_maynard_measure := by
  intro sieve scale δ hδ
  filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
  let S := limitPointSet ∩ Icc 0 T
  have hS : volume S ≠ ⊤ := measure_ne_top_of_subset inter_subset_right (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  apply (ENNReal.ofReal_le_iff_le_toReal hS).2
  change (1-δ)*T/8 ≤ volume.real S
  suffices T/8 ≤ volume.real S by nlinarith [mul_pos hδ hT]
  by_contra! short
  let ε := (T-8*volume.real S)/16
  have he : 0 < ε := by dsimp [ε]; linarith
  have hvol : volume.real (Icc 0 T) = T := by rw [Real.volume_real_Icc_of_le hT.le,sub_zero]
  obtain ⟨β,hβ,avoid⟩ := pack (S := limitPointSet) he 8
    (Set.Subset.rfl : Icc 0 T ⊆ Icc 0 T) (by
      rw [hvol]; change (8:ℝ)*(ε+volume.real S)<T; dsimp [ε]; linarith)
  obtain ⟨i,j,hij,n,hn,hlim⟩ := sieve β (fun i => (hβ i).1) (fun i j h => (avoid i j h).1)
  apply (avoid i j hij).2
  apply (mem_limitPointSet_iff _).2
  refine ⟨n,hn,?_⟩
  have h := hlim.mul (scale.comp hn.tendsto_atTop)
  rw [mul_one] at h
  apply h.congr
  intro k
  have hp : 0 < log (Nat.nth Nat.Prime (n k)) :=
    Real.log_pos (by exact_mod_cast (Nat.prime_nth_prime (n k)).one_lt)
  simp [normalizedGap,div_mul_div_cancel₀,hp.ne']

end OMA.R_Erdos5_erdos_5_variants_banks_freiberg_maynard_measure_R1
