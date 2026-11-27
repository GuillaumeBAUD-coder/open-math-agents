import OMAReductions.R_Erdos969_erdos_969_variants_evelyn_linfoot_R1

/-!
Discrete partial summation expresses the series for the first differences of
a counting function in terms of the differences of two neighboring powers.
The interior identity requires a big-O error bound. At the boundary the
little-o bound makes the transform vanish after multiplication by the real
increment. Differentiability of zeta cancels that increment at a zero.
-/

namespace OMA.R_Erdos969_erdos_969_variants_evelyn_linfoot_R1_H3_R1

open Filter Topology Asymptotics

/-- Continue the partial-summation identity inside the half-plane. The term
involving the count at zero comes from the lower limit of partial summation. -/
def H1 : Prop :=
  ∀ (A : ℕ → ℕ) (c : ℝ),
    ((fun n : ℕ => |(A n : ℝ) - c * n|) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (1 / 4 : ℝ))) →
    (∀ s : ℂ, 1 < s.re →
      LSeries (fun n : ℕ => (A n : ℂ) - (A (n - 1) : ℂ)) s *
        riemannZeta (2 * s) = riemannZeta s) →
    ∀ s : ℂ, (1 / 4 : ℝ) < s.re → s.im ≠ 0 →
      ((c : ℂ) * riemannZeta s - (A 0 : ℂ) +
        ∑' n : ℕ, (((A (n + 1) : ℝ) - c * (n + 1 : ℕ) : ℝ) : ℂ) *
          (((n + 1 : ℕ) : ℂ) ^ (-s) - ((n + 2 : ℕ) : ℂ) ^ (-s))) *
        riemannZeta (2 * s) = riemannZeta s

/-- An Abelian estimate for an arbitrary real error sequence. It does not
require a zeta identity or any hypothesis about zeros. -/
def H2 : Prop :=
  ∀ (u : ℕ → ℝ) (z : ℂ), (1 / 4 : ℝ) ≤ z.re →
    ((fun n : ℕ => |u n|) =o[atTop] (fun n : ℕ => (n : ℝ) ^ (1 / 4 : ℝ))) →
    Tendsto (fun t : ℝ => (t : ℂ) *
      ∑' n : ℕ, (u (n + 1) : ℂ) *
        (((n + 1 : ℕ) : ℂ) ^ (-(z + t)) - ((n + 2 : ℕ) : ℂ) ^ (-(z + t))))
      (𝓝[>] 0) (𝓝 0)

lemma boundary_zero {D F G : ℝ → ℂ} (hF : DifferentiableAt ℝ F 0)
    (hF0 : F 0 = 0) (hG : ContinuousAt G 0)
    (hid : ∀ᶠ t : ℝ in 𝓝[>] 0, G t = D t * F t)
    (hD : Tendsto (fun t : ℝ => (t : ℂ) * D t) (𝓝[>] 0) (𝓝 0)) :
    G 0 = 0 := by
  have hs : Tendsto (fun t : ℝ => (t : ℂ)⁻¹ * F t) (𝓝[>] 0) (𝓝 (deriv F 0)) := by
    simpa [hF0, Complex.real_smul] using hF.hasDerivAt.tendsto_slope_zero_right
  have hp : Tendsto (fun t : ℝ => ((t : ℂ) * D t) * ((t : ℂ)⁻¹ * F t))
      (𝓝[>] 0) (𝓝 0) := by simpa using hD.mul hs
  have hG0 : Tendsto G (𝓝[>] 0) (𝓝 0) := by
    apply hp.congr'
    filter_upwards [self_mem_nhdsWithin, hid] with t ht heq
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (show 0 < t from ht))
    rw [heq]
    field_simp
  exact tendsto_nhds_unique (hG.tendsto.mono_left nhdsWithin_le_nhds) hG0

theorem main : H1 → H2 → OMA.R_Erdos969_erdos_969_variants_evelyn_linfoot_R1.H3 := by
  intro hcont hab A c z hre him hzero hseries hsmall
  let u (n : ℕ) : ℝ := (A n : ℝ) - c * n
  let T (s : ℂ) := ∑' n : ℕ, (u (n + 1) : ℂ) *
    (((n + 1 : ℕ) : ℂ) ^ (-s) - ((n + 2 : ℕ) : ℂ) ^ (-s))
  let G (t : ℝ) := riemannZeta (z + t)
  let F (t : ℝ) := riemannZeta (2 * (z + t))
  let B (t : ℝ) := (c : ℂ) * G t - (A 0 : ℂ)
  let D (t : ℝ) := B t + T (z + t)
  have hz : z ≠ 1 := by rintro rfl; simp at him
  have h2z : 2 * z ≠ 1 := by
    intro h
    have h' := congrArg Complex.im h
    simp at h'
    exact him (by linarith)
  have harg : DifferentiableAt ℝ (fun t : ℝ => z + (t : ℂ)) 0 := by fun_prop
  have h2arg : DifferentiableAt ℝ (fun t : ℝ => 2 * (z + (t : ℂ))) 0 := by fun_prop
  have hG : ContinuousAt G 0 := by
    apply ContinuousAt.comp (g := riemannZeta) (f := fun t : ℝ => z + (t : ℂ))
    · simpa using (differentiableAt_riemannZeta hz).continuousAt
    · exact harg.continuousAt
  have hF : DifferentiableAt ℝ F 0 := by
    apply DifferentiableAt.comp (g := riemannZeta) (f := fun t : ℝ => 2 * (z + (t : ℂ)))
    · simpa using (differentiableAt_riemannZeta h2z).restrictScalars ℝ
    · exact h2arg
  have hid : ∀ᶠ t : ℝ in 𝓝[>] 0, G t = D t * F t := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hrt : (1 / 4 : ℝ) < (z + (t : ℂ)).re := by
      simp only [Complex.add_re, Complex.ofReal_re]
      linarith [show 0 < t from ht]
    exact (hcont A c hsmall.isBigO hseries (z + t) hrt (by simpa using him)).symm
  have hT : Tendsto (fun t : ℝ => (t : ℂ) * T (z + t)) (𝓝[>] 0) (𝓝 0) :=
    hab u z hre hsmall
  have hB : ContinuousAt B 0 := (continuousAt_const.mul hG).sub continuousAt_const
  have ht : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (Complex.continuous_ofReal.continuousAt (x := (0 : ℝ))).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi 0))
  have hD : Tendsto (fun t : ℝ => (t : ℂ) * D t) (𝓝[>] 0) (𝓝 0) := by
    simpa [D, mul_add] using ((ht.mul (hB.tendsto.mono_left nhdsWithin_le_nhds)).add hT)
  have := boundary_zero hF (by simpa [F] using hzero) hG hid hD
  simpa [G] using this

end OMA.R_Erdos969_erdos_969_variants_evelyn_linfoot_R1_H3_R1
