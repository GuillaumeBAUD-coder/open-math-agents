import OMAReductions.R_Erdos707_erdos_707_variants_small_sidon_sets_R2_H2_R1

-- Step Erdos707.erdos_707.variants.small_sidon_sets.R2.H2.R1.H2: hypothesis H2 of reduction Erdos707.erdos_707.variants.small_sidon_sets.R2.H2.R1
-- Credit: @<your GitHub handle>

theorem OMA.solution : OMA.R_Erdos707_erdos_707_variants_small_sidon_sets_R2_H2_R1.H2 := by
  intro F K _ _ _ u v x c hc
  dsimp only
  have hdir : ∀ (y : K) (d : F), d ≠ 0 →
      ((¬ ∃ a : F, y ^ (u.gcd v) = algebraMap F K a) ∧
        ∃ s t : F, y ^ v = algebraMap F K s + algebraMap F K t * y ^ u) →
      ((¬ ∃ a : F, (y * algebraMap F K d) ^ (u.gcd v) = algebraMap F K a) ∧
        ∃ s t : F, (y * algebraMap F K d) ^ v =
          algebraMap F K s + algebraMap F K t * (y * algebraMap F K d) ^ u) := by
    intro y d hd ⟨h1, s, t, h2⟩
    have hdK : algebraMap F K d ≠ 0 :=
      (map_ne_zero_iff (algebraMap F K) (RingHom.injective _)).mpr hd
    constructor
    · rintro ⟨a, ha⟩
      apply h1
      refine ⟨a * (d ^ (u.gcd v))⁻¹, ?_⟩
      have hdg : algebraMap F K d ^ (u.gcd v) ≠ 0 := pow_ne_zero _ hdK
      rw [mul_pow] at ha
      rw [map_mul, map_inv₀, map_pow, ← ha, mul_assoc, mul_inv_cancel₀ hdg, mul_one]
    · refine ⟨s * d ^ v, t * d ^ v * (d ^ u)⁻¹, ?_⟩
      have hdu : algebraMap F K d ^ u ≠ 0 := pow_ne_zero _ hdK
      rw [mul_pow, mul_pow, h2, add_mul]
      simp only [map_mul, map_inv₀, map_pow]
      have hterm : algebraMap F K t * algebraMap F K d ^ v * (algebraMap F K d ^ u)⁻¹ *
          (y ^ u * algebraMap F K d ^ u) = algebraMap F K t * y ^ u * algebraMap F K d ^ v := by
        calc
          algebraMap F K t * algebraMap F K d ^ v * (algebraMap F K d ^ u)⁻¹ *
              (y ^ u * algebraMap F K d ^ u)
              = algebraMap F K t * y ^ u * algebraMap F K d ^ v *
                  ((algebraMap F K d ^ u)⁻¹ * algebraMap F K d ^ u) := by ring
          _ = algebraMap F K t * y ^ u * algebraMap F K d ^ v * 1 := by
                rw [inv_mul_cancel₀ hdu]
          _ = algebraMap F K t * y ^ u * algebraMap F K d ^ v := mul_one _
      rw [hterm]
  constructor
  · intro h
    have hinv := hdir (x * algebraMap F K c) c⁻¹ (inv_ne_zero hc) h
    have hx : x * algebraMap F K c * algebraMap F K c⁻¹ = x := by
      rw [mul_assoc, ← map_mul, mul_inv_cancel₀ hc, map_one, mul_one]
    rwa [hx] at hinv
  · exact hdir x c hc
