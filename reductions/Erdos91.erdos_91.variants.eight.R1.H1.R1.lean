import OMAReductions.R_Erdos91_erdos_91_variants_eight_R1

/-!
# The seven-point configurations cannot be extended

Use the seven-point classification of Erdős and Fishburn, Maximum planar sets
that determine k distances (1996), Section 2. An external point different from
the circle centre sees at most two vertices at each distance. Thus seven
cocircular vertices already force a fourth distance. For the hexagon with its
centre, all three distance fibres must have size two, and the sum of squared
distances to the six vertices excludes the three possible centre distances.
-/

namespace OMA.R_Erdos91_erdos_91_variants_eight_R1_H1_R1

open Finset EuclideanGeometry InnerProductSpace
open scoped Classical

private theorem pair_distance {A : Finset ℝ²} {p q : ℝ²} (hp : p ∈ A)
    (hq : q ∈ A) (h : p ≠ q) : dist p q ∈ distanceSet A := by
  exact mem_image.mpr ⟨(p,q), mem_offDiag.mpr ⟨hp,hq,h⟩, rfl⟩

private theorem distances_mono {A B : Finset ℝ²} (h : B ⊆ A) :
    distanceSet B ⊆ distanceSet A := by
  intro d hd
  obtain ⟨⟨p,q⟩, hpq, rfl⟩ := mem_image.mp hd
  obtain ⟨hp,hq,hne⟩ := mem_offDiag.mp hpq
  exact pair_distance (h hp) (h hq) hne

private theorem fibre_count {P : Type*} {W : Finset P} {T : Finset ℝ} {f : P → ℝ}
    (hMaps : ∀ w ∈ W, f w ∈ T)
    (hFibres : ∀ d ∈ T, (W.filter fun w => f w = d).card ≤ 2) :
    W.card ≤ 2*T.card := by
  rw [card_eq_sum_card_fiberwise (fun w hw => hMaps w hw)]
  exact (sum_le_sum hFibres).trans_eq (by simp [mul_comm])

private theorem fibre_saturation {P : Type*} {W : Finset P} {T : Finset ℝ} {f : P → ℝ}
    (hMaps : ∀ w ∈ W, f w ∈ T) (hW : W.card = 6) (hT : T.card = 3)
    (hFibres : ∀ d ∈ T, (W.filter fun w => f w = d).card ≤ 2) :
    ∀ d ∈ T, (W.filter fun w => f w = d).card = 2 := by
  intro d hd
  by_contra! h
  have hstrict := sum_lt_sum hFibres ⟨d, hd, lt_of_le_of_ne (hFibres d hd) h⟩
  rw [← card_eq_sum_card_fiberwise (fun w hw => hMaps w hw)] at hstrict
  simp [hW, hT] at hstrict

private theorem distance_square_sum (W : Finset ℝ²) (c p : ℝ²) (r : ℝ)
    (hRad : ∀ w ∈ W, dist c w = r) (hBal : ∑ w ∈ W, (w-c) = 0) :
    (∑ w ∈ W, (dist p w)^2) = (W.card:ℝ)*((dist p c)^2+r^2) := by
  have hterm (w : ℝ²) (hw : w ∈ W) :
      (dist p w)^2 = (dist p c)^2+r^2-2*inner ℝ (p-c) (w-c) := by
    have hwr : ‖w-c‖ = r := by
      rw [← dist_eq_norm, dist_comm]
      exact hRad w hw
    rw [dist_eq_norm, show (p-w) = (p-c)-(w-c) by abel, norm_sub_sq_real,
      ← dist_eq_norm, hwr]
    ring
  rw [sum_congr rfl hterm, sum_sub_distrib, ← mul_sum, ← inner_sum, hBal]
  simp [nsmul_eq_mul]
  ring

private theorem square_codes (T : Finset ℝ) (r : ℝ) (hr : 0 < r)
    (hT : T.card = 3) (hpos : ∀ d ∈ T, 0 ≤ d)
    (hValues : ∀ d ∈ T, d^2 = r^2 ∨ d^2 = 3*r^2 ∨ d^2 = 4*r^2) :
    (∑ d ∈ T, d^2) = 8*r^2 := by
  let U : Finset ℝ := {r^2,3*r^2,4*r^2}
  have hsub : T.image (fun d => d^2) ⊆ U := by
    intro d hd
    obtain ⟨e,he,rfl⟩ := mem_image.mp hd
    simpa [U] using hValues e he
  have hinj : Set.InjOn (fun d : ℝ => d^2) (T : Set ℝ) := by
    intro x hx y hy h
    exact le_antisymm ((sq_le_sq₀ (hpos x hx) (hpos y hy)).mp h.le)
      ((sq_le_sq₀ (hpos y hy) (hpos x hx)).mp h.ge)
  have h01 : r^2 ≠ 3*r^2 := by nlinarith
  have h02 : r^2 ≠ 4*r^2 := by nlinarith
  have h12 : 3*r^2 ≠ 4*r^2 := by nlinarith
  have hU : U.card = 3 := by simp [U, h01, h02, h12]
  have he : T.image (fun d => d^2) = U := by
    apply eq_of_subset_of_card_le hsub
    rw [hU, card_image_of_injOn hinj, hT]
  calc
    _ = ∑ x ∈ T.image (fun d => d^2), x := (sum_image hinj).symm
    _ = _ := by
      rw [he]
      simp [U, h01, h02, h12]
      ring

/-- The seven-point classification, recording only the circle and distance data used below. -/
def H1 : Prop :=
  ∀ B : Finset ℝ², B.card = 7 → distinctDistances B ≤ 3 →
    distinctDistances B = 3 ∧
    ((∃ (c : ℝ²) (r : ℝ), 0 < r ∧ (∀ x ∈ B, dist c x = r) ∧ r ∉ distanceSet B) ∨
     (∃ (c : ℝ²) (r : ℝ), c ∈ B ∧ 0 < r ∧ (∀ x ∈ B.erase c, dist c x = r) ∧
       (∑ x ∈ B.erase c, (x-c)) = 0 ∧
       ∀ d ∈ distanceSet B, d^2 = r^2 ∨ d^2 = 3*r^2 ∨ d^2 = 4*r^2))

/-- Two circles with distinct centres have at most two common points. -/
def H2 : Prop :=
  ∀ (p q : ℝ²) (r d : ℝ), p ≠ q → ∀ W : Finset ℝ²,
    (∀ w ∈ W, dist p w = r ∧ dist q w = d) → W.card ≤ 2

theorem main : H1 → H2 → OMA.R_Erdos91_erdos_91_variants_eight_R1.H1 := by
  intro hClass hCircle A hA
  by_contra! hFew
  have hA3 : (distanceSet A).card ≤ 3 := by
    change distinctDistances A ≤ 3
    omega
  obtain ⟨p,hp⟩ : A.Nonempty := card_pos.mp (by omega)
  let B := A.erase p
  let T := distanceSet A
  have hB : B.card = 7 := by
    rw [show B.card = A.card-1 from card_erase_of_mem hp, hA]
  have hBB : B ⊆ A := erase_subset _ _
  have hSub := distances_mono hBB
  have hBd : distinctDistances B ≤ 3 := (card_le_card hSub).trans hA3
  obtain ⟨hThree,hCases⟩ := hClass B hB hBd
  change (distanceSet B).card = 3 at hThree
  have hT : T.card = 3 := le_antisymm hA3 (hThree ▸ card_le_card hSub)
  have hEq : distanceSet B = T := by
    apply eq_of_subset_of_card_le hSub
    exact hT.le.trans hThree.ge
  have hCode (x : ℝ²) (hx : x ∈ B) : dist p x ∈ T :=
    pair_distance hp (hBB hx) (fun he => (mem_erase.mp hx).1 he.symm)
  rcases hCases with ⟨c,r,hr,hRad,hNew⟩ | ⟨c,r,hc,hr,hRad,hBal,hOld⟩
  · by_cases he : p = c
    · obtain ⟨x,hx⟩ : B.Nonempty := card_pos.mp (by omega)
      have hd := hCode x hx
      rw [he, hRad x hx, ← hEq] at hd
      exact hNew hd
    · have hb (d : ℝ) (_ : d ∈ T) : (B.filter fun x => dist p x = d).card ≤ 2 :=
        hCircle c p r d (Ne.symm he) _ fun x hx =>
          ⟨hRad x (mem_filter.mp hx).1, (mem_filter.mp hx).2⟩
      have hn := fibre_count hCode hb
      omega
  · let W := B.erase c
    have hW : W.card = 6 := by rw [show W.card = B.card-1 from card_erase_of_mem hc, hB]
    have hpc : p ≠ c := (mem_erase.mp hc).1.symm
    have hMaps (x : ℝ²) (hx : x ∈ W) : dist p x ∈ T := hCode x (erase_subset _ _ hx)
    have hFibres (d : ℝ) (_ : d ∈ T) : (W.filter fun x => dist p x = d).card ≤ 2 :=
      hCircle c p r d hpc.symm _ fun x hx =>
        ⟨hRad x (mem_filter.mp hx).1, (mem_filter.mp hx).2⟩
    have hSaturated := fibre_saturation hMaps hW hT hFibres
    have hTpos (d : ℝ) (hd : d ∈ T) : 0 ≤ d := by
      obtain ⟨⟨u,v⟩,_,rfl⟩ := mem_image.mp hd
      exact dist_nonneg
    have hValues (d : ℝ) (hd : d ∈ T) : d^2 = r^2 ∨ d^2 = 3*r^2 ∨ d^2 = 4*r^2 :=
      hOld d (hEq ▸ hd)
    have hsum : (∑ x ∈ W, (dist p x)^2) = 16*r^2 := by
      calc
        _ = ∑ d ∈ T, ∑ x ∈ W.filter (fun x => dist p x = d), (dist p x)^2 :=
          (sum_fiberwise_of_maps_to hMaps (fun x => (dist p x)^2)).symm
        _ = ∑ d ∈ T, 2*d^2 := by
          refine sum_congr rfl fun d hd => ?_
          calc
            _ = ∑ _x ∈ W.filter (fun x => dist p x = d), d^2 :=
              sum_congr rfl (fun x hx => by rw [(mem_filter.mp hx).2])
            _ = _ := by simp [nsmul_eq_mul, hSaturated d hd]
        _ = _ := by rw [← mul_sum, square_codes T r hr hT hTpos hValues]; ring
    have hs := distance_square_sum W c p r hRad hBal
    rw [hW, hsum] at hs
    norm_num at hs
    have hd := hValues (dist p c) (hCode c hc)
    rcases hd with hd | hd | hd <;> nlinarith

end OMA.R_Erdos91_erdos_91_variants_eight_R1_H1_R1
