import OMAReductions.R_Green17_green_17_variants_exponential_R1

namespace OMA.Green17ExpH1

/-- A point of the product set projects into `A` and into `B`. -/
lemma proj_mem {m n : ℕ} {A : Finset (𝔽₃ m)} {B : Finset (𝔽₃ n)} {y : 𝔽₃ (m + n)}
    (hy : y ∈ (A ×ˢ B).image (fun p => Fin.append p.1 p.2)) :
    (fun i => y (Fin.castAdd n i)) ∈ A ∧ (fun j => y (Fin.natAdd m j)) ∈ B := by
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hy
  rw [Finset.mem_product] at hab
  simpa only [Fin.append_left, Fin.append_right] using hab

end OMA.Green17ExpH1

open OMA.Green17ExpH1 in
theorem OMA.solution : OMA.R_Green17_green_17_variants_exponential_R1.H1 := by
  intro m n A B hA hB
  refine ⟨(A ×ˢ B).image (fun p => Fin.append p.1 p.2), ?_, ?_⟩
  · rw [Finset.card_image_of_injective, Finset.card_product]
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h' : Fin.append a b = Fin.append a' b' := h
    have ha : a = a' := funext fun i => by
      simpa only [Fin.append_left] using congrFun h' (Fin.castAdd n i)
    have hb : b = b' := funext fun j => by
      simpa only [Fin.append_right] using congrFun h' (Fin.natAdd m j)
    rw [ha, hb]
  · rintro ⟨x, d, hd, h01, hx, hxd, hx2d⟩
    obtain ⟨hxA, hxB⟩ := proj_mem hx
    obtain ⟨hxdA, hxdB⟩ := proj_mem hxd
    obtain ⟨hx2dA, hx2dB⟩ := proj_mem hx2d
    by_cases hL : (fun i => d (Fin.castAdd n i)) = 0
    · apply hB
      refine ⟨fun j => x (Fin.natAdd m j), fun j => d (Fin.natAdd m j), ?_,
        fun j => h01 _, hxB, hxdB, hx2dB⟩
      intro hR
      apply hd
      rw [← Fin.append_castAdd_natAdd (f := d), hL, hR]
      funext i
      refine Fin.addCases (fun i => ?_) (fun j => ?_) i
      · simp
      · simp
    · exact hA ⟨fun i => x (Fin.castAdd n i), fun i => d (Fin.castAdd n i), hL,
        fun i => h01 _, hxA, hxdA, hx2dA⟩
