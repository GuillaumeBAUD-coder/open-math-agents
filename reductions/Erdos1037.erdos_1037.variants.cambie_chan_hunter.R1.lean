import FormalConjectures.ErdosProblems.«1037»

/-! # Ramsey graphs, a degree construction on eight copies, and padding -/
-- Credit: @steveDOTdigital
namespace OMA.R_Erdos1037_erdos_1037_variants_cambie_chan_hunter_R1
open Filter

-- A random graph has only logarithmically large homogeneous sets.
def H1 : Prop := ∃ K : ℝ, 0 < K ∧ ∀ᶠ m : ℕ in atTop, ∃ G : SimpleGraph (Fin m),
    ∀ s : Set (Fin m), G.IsHomogeneous s → (s.ncard : ℝ) ≤ K * Real.log m

-- Double the input graph to regularize it, then join four copies by a staircase.
def H2 : Prop := ∀ (m : ℕ), 2 ≤ m → ∀ (G : SimpleGraph (Fin m)) (t : ℝ),
    (∀ s : Set (Fin m), G.IsHomogeneous s → (s.ncard : ℝ) ≤ t) →
    ∃ F : SimpleGraph (Fin (8*m)),
      (∀ d : ℕ, {v : Fin (8*m) | (F.neighborSet v).ncard = d}.ncard ≤ 2) ∧
      (3/4 * ((8*m : ℕ) : ℝ) ≤ ((Set.range fun v => (F.neighborSet v).ncard).ncard : ℝ)) ∧
      (∀ s : Set (Fin (8*m)), F.IsHomogeneous s → (s.ncard : ℝ) ≤ 8*t) ∧
      ∀ v, 0 < (F.neighborSet v).ncard

-- Add at most seven vertices while preserving the degree conditions.
def H3 : Prop := ∀ (N r : ℕ), 0 < N → r < 8 → ∀ (F : SimpleGraph (Fin N)) (t : ℝ),
    (∀ d : ℕ, {v : Fin N | (F.neighborSet v).ncard = d}.ncard ≤ 2) →
    (3/4 * (N : ℝ) ≤ ((Set.range fun v => (F.neighborSet v).ncard).ncard : ℝ)) →
    (∀ s : Set (Fin N), F.IsHomogeneous s → (s.ncard : ℝ) ≤ t) →
    (∀ v, 0 < (F.neighborSet v).ncard) →
    ∃ G : SimpleGraph (Fin (N+r)),
      (∀ d : ℕ, {v : Fin (N+r) | (G.neighborSet v).ncard = d}.ncard ≤ 2) ∧
      (3/4 * ((N+r : ℕ) : ℝ) ≤ ((Set.range fun v => (G.neighborSet v).ncard).ncard : ℝ)) ∧
      ∀ s : Set (Fin (N+r)), G.IsHomogeneous s → (s.ncard : ℝ) ≤ t+r

theorem main : H1 → H2 → H3 → type_of% @Erdos1037.erdos_1037.variants.cambie_chan_hunter := by
  rintro ⟨K,hK,ramsey⟩ construct pad
  obtain ⟨M,hM⟩ := eventually_atTop.mp ramsey
  refine ⟨8*K+7,?_⟩
  have logs : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (8*(M+2)), logs.eventually (eventually_ge_atTop 1)] with n hn logn
  have m2 : 2 ≤ n/8 := by omega
  obtain ⟨G,hG⟩ := hM (n/8) (by omega)
  obtain ⟨F,hm,hd,hh,hp⟩ := construct (n/8) m2 G _ hG
  have res := pad (8*(n/8)) (n%8) (by omega) (by omega) F _ hm hd hh hp
  have en : 8*(n/8)+n%8 = n := by omega
  rw [en] at res
  obtain ⟨J,hj,dj,sj⟩ := res
  refine ⟨J,hj,dj,?_⟩
  intro s hs
  have gm : 0 < (↑(n/8) : ℝ) := by exact_mod_cast (by omega : 0 < n/8)
  have cmp := Real.log_le_log gm (by exact_mod_cast Nat.div_le_self n 8 : (↑(n/8) : ℝ) ≤ n)
  have tail : ((n%8 : ℕ) : ℝ) ≤ 7 := by exact_mod_cast (by omega : n%8 ≤ 7)
  change 1 ≤ Real.log n at logn
  nlinarith [sj s hs, mul_le_mul_of_nonneg_left cmp hK.le]

end OMA.R_Erdos1037_erdos_1037_variants_cambie_chan_hunter_R1
