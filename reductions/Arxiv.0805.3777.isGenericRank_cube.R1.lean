import FormalConjectures.Arxiv.«0805.3777».TensorRank

/-! The dimension bound excludes smaller ranks. A spanning family of tangent spaces
to the cone of simple tensors gives the generic upper bound by dominance of the
sum map. The three steps separate the dimension estimate, the dominance criterion
and Lickteig's existence result for cubes. -/

namespace OMA.R_Arxiv_0805_3777_isGenericRank_cube_R1

open Arxiv.«0805.3777» Set

/-- A family with too few rank-one summands has nowhere dense closure. -/
def H1 : Prop :=
  ∀ (n r : ℕ), 1 ≤ n → (3 * n - 2) * r < n ^ 3 →
    interior (closure {T : Holor ℂ [n, n, n] | T.cprank ≤ r}) = ∅

/-- A surjective differential of the sum map yields a dense open set of
tensors admitting a decomposition into at most the given number of summands. -/
def H2 : Prop :=
  ∀ (n r : ℕ) (a b c : Fin r → Holor ℂ [n]),
    (∀ T : Holor ℂ [n, n, n], ∃ u v w : Fin r → Holor ℂ [n],
      T = ∑ i, (Holor.mul (u i) (Holor.mul (b i) (c i)) +
        Holor.mul (a i) (Holor.mul (v i) (c i)) +
        Holor.mul (a i) (Holor.mul (b i) (w i)))) →
    Dense (interior {T : Holor ℂ [n, n, n] | Holor.CPRankMax r T})

/-- At the predicted rank, some configuration of simple tensors has tangent
spaces spanning the entire cube. -/
def H3 : Prop :=
  ∀ (n : ℕ), 1 ≤ n → n ≠ 3 →
    let r := n ^ 3 ⌈/⌉ (3 * n - 2)
    ∃ a b c : Fin r → Holor ℂ [n], ∀ T : Holor ℂ [n, n, n],
      ∃ u v w : Fin r → Holor ℂ [n],
        T = ∑ i, (Holor.mul (u i) (Holor.mul (b i) (c i)) +
          Holor.mul (a i) (Holor.mul (v i) (c i)) +
          Holor.mul (a i) (Holor.mul (b i) (w i)))

theorem main : H1 → H2 → H3 → type_of% @Arxiv.«0805.3777».isGenericRank_cube := by
  classical
  intro hdim hdom hspan n hn hn3
  let r := n ^ 3 ⌈/⌉ (3 * n - 2)
  have hden : 0 < 3 * n - 2 := by omega
  have hpos : 0 < n ^ 3 := pow_pos (by omega) _
  have hr : 0 < r := by
    by_contra! hz
    have : n ^ 3 ≤ (3 * n - 2) * 0 := (ceilDiv_le_iff_le_mul hden).mp hz
    rw [Nat.mul_zero] at this
    omega
  have hcost : (3 * n - 2) * (r - 1) < n ^ 3 := by
    by_contra! h
    have : r ≤ r - 1 := (ceilDiv_le_iff_le_mul hden).mpr h
    omega
  let K := closure {T : Holor ℂ [n, n, n] | T.cprank ≤ r - 1}
  have hd : Dense Kᶜ := interior_eq_empty_iff_dense_compl.mp (hdim n (r - 1) hn hcost)
  obtain ⟨a, b, c, ht⟩ := hspan n hn hn3
  let U := interior {T : Holor ℂ [n, n, n] | Holor.CPRankMax r T}
  have hu : Dense U := hdom n r a b c ht
  refine ⟨U ∩ Kᶜ, isOpen_interior.inter isClosed_closure.isOpen_compl,
    hu.inter_of_isOpen_left hd isOpen_interior, ?_⟩
  intro T hT
  have hdecomp : Holor.CPRankMax r T := interior_subset hT.1
  have hupper : T.cprank ≤ r := Nat.find_min' _ hdecomp
  have hlower : ¬ T.cprank ≤ r - 1 := fun h => hT.2 (subset_closure h)
  change T.cprank = r
  omega

end OMA.R_Arxiv_0805_3777_isGenericRank_cube_R1
