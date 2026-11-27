import OMAStatements.S_mse_5127397
import Mathlib.Analysis.Normed.Field.WithAbs
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum

/-! Over the trivially normed field with two elements, the sum norm on the
product of two copies gives a discrete normed vector space. A series converges
exactly when its terms are eventually zero, but the two coordinate vectors
violate the strong triangle inequality. -/

open Filter
open OMA.S_mse_5127397

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private def trivialAbs : AbsoluteValue (ZMod 2) ℝ := AbsoluteValue.trivial

private abbrev K := WithAbs trivialAbs
private abbrev E := WithLp 1 (K × K)

private theorem series_disc {V : Type} [NormedAddCommGroup V] [DiscreteTopology V]
    (u : ℕ → V) : SeriesConverges u ↔ Tendsto u atTop (nhds 0) := by
  simp only [SeriesConverges, nhds_discrete, tendsto_pure, eventually_atTop]
  constructor
  · rintro ⟨s, N, hN⟩
    refine ⟨N, fun n hn => ?_⟩
    have hsucc := hN (n + 1) (by omega)
    rw [Finset.sum_range_succ, hN n hn] at hsucc
    exact add_left_cancel (hsucc.trans (add_zero s).symm)
  · rintro ⟨N, hN⟩
    refine ⟨∑ i ∈ Finset.range N, u i, N, fun n hn => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    clear hn
    induction k with
    | zero => simp
    | succ k ih =>
      rw [← Nat.add_assoc, Finset.sum_range_succ, ih, hN _ (by omega), add_zero]

theorem OMA.disproof : ¬ (type_of% @OMA.S_mse_5127397.main) := by
  intro h
  let : Finite K := Finite.of_equiv (ZMod 2) (WithAbs.equiv trivialAbs).symm.toEquiv
  let : Finite E := Finite.of_equiv (K × K) (WithLp.equiv 1 (K × K)).symm
  have htriangle := (h K E series_disc).2 (WithLp.toLp 1 ((1 : K), 0))
    (WithLp.toLp 1 ((0 : K), 1))
  rw [WithLp.prod_norm_eq_of_L1, WithLp.norm_toLp_fst, WithLp.norm_toLp_snd] at htriangle
  norm_num [WithLp.add_fst, WithLp.add_snd] at htriangle
