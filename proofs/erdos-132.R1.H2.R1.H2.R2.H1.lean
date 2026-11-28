import OMAReductions.R_erdos_132_R1_H2_R1_H2_R2

/-!
# Rare distances for points on a circle with optional center (`erdos-132.R1.H2.R1.H2.R2.H1`)

Two distinct circles in `ℝ²` intersect in at most two points. Removing the optional center `o`
leaves `B = A.erase o` on the circle of radius `r` around `o` with `|B| ≥ 2k + 2`:
- Every distance `d ≠ r` occurs at most twice from any `x ∈ B` and never from `o`, giving
  `pairMultiplicity A d ≤ |B| ≤ |A|`.
- Fixing any `p ∈ B`, the `|B| - 1 ≥ 2k + 1` points of `B.erase p` realize at least `k + 1`
  distinct distances from `p`; dropping at most the radius `r` leaves at least `k` rare distances.

Credit: @DPS0340
-/

open Finset OMA.S_erdos_132

namespace Erdos132Circle

lemma circle_inter_le_two (o p : EuclideanSpace ℝ (Fin 2)) (hpo : p ≠ o) (r d : ℝ)
    (S : Finset (EuclideanSpace ℝ (Fin 2)))
    (hS : ∀ x ∈ S, dist x o = r ∧ dist x p = d) : S.card ≤ 2 := by
  by_contra hgt
  push Not at hgt
  obtain ⟨x₁, hx₁, x₂, hx₂, x₃, hx₃, h12, h13, h23⟩ := two_lt_card.mp hgt
  have hdist_sq : ∀ x y : EuclideanSpace ℝ (Fin 2),
      dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
    intro x y
    rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]
    simp [Real.dist_eq]
  let v0 : ℝ := p 0 - o 0
  let v1 : ℝ := p 1 - o 1
  have hv_ne : v0 ≠ 0 ∨ v1 ≠ 0 := by
    by_contra h
    push Not at h
    apply hpo
    ext i
    fin_cases i
    · change p 0 = o 0; linarith [h.1]
    · change p 1 = o 1; linarith [h.2]
  have heq_pt : ∀ x ∈ S,
      (x 0 - o 0) ^ 2 + (x 1 - o 1) ^ 2 = r ^ 2 ∧
      2 * v0 * (x 0 - o 0) + 2 * v1 * (x 1 - o 1) = r ^ 2 + v0 ^ 2 + v1 ^ 2 - d ^ 2 := by
    intro x hx
    obtain ⟨hxo, hxp⟩ := hS x hx
    have h1 : (x 0 - o 0) ^ 2 + (x 1 - o 1) ^ 2 = r ^ 2 := by
      have := hdist_sq x o; rw [hxo] at this; linarith
    have h2 : (x 0 - p 0) ^ 2 + (x 1 - p 1) ^ 2 = d ^ 2 := by
      have := hdist_sq x p; rw [hxp] at this; linarith
    have hxp0 : x 0 - p 0 = (x 0 - o 0) - v0 := by dsimp [v0]; ring
    have hxp1 : x 1 - p 1 = (x 1 - o 1) - v1 := by dsimp [v1]; ring
    rw [hxp0, hxp1] at h2
    exact ⟨h1, by nlinarith⟩
  have ⟨hq1, hl1⟩ := heq_pt x₁ hx₁
  have ⟨hq2, hl2⟩ := heq_pt x₂ hx₂
  have ⟨hq3, hl3⟩ := heq_pt x₃ hx₃
  let C : ℝ := r ^ 2 + v0 ^ 2 + v1 ^ 2 - d ^ 2
  have quad_three : ∀ (A B D t₁ t₂ t₃ : ℝ), 0 < A →
      A * t₁ ^ 2 + B * t₁ + D = 0 →
      A * t₂ ^ 2 + B * t₂ + D = 0 →
      A * t₃ ^ 2 + B * t₃ + D = 0 →
      t₁ = t₂ ∨ t₁ = t₃ ∨ t₂ = t₃ := by
    intro A B D t₁ t₂ t₃ hA e1 e2 e3
    by_contra h
    push Not at h
    obtain ⟨hne12, hne13, hne23⟩ := h
    have f12 : (t₁ - t₂) * (A * (t₁ + t₂) + B) = 0 := by nlinarith
    have f13 : (t₁ - t₃) * (A * (t₁ + t₃) + B) = 0 := by nlinarith
    have s12 : A * (t₁ + t₂) + B = 0 := (mul_eq_zero.mp f12).resolve_left (sub_ne_zero.mpr hne12)
    have s13 : A * (t₁ + t₃) + B = 0 := (mul_eq_zero.mp f13).resolve_left (sub_ne_zero.mpr hne13)
    have hA23 : A * (t₂ - t₃) = 0 := by linarith
    exact hne23 (sub_eq_zero.mp ((mul_eq_zero.mp hA23).resolve_left hA.ne'))
  have ext2 : ∀ x y : EuclideanSpace ℝ (Fin 2), x 0 = y 0 → x 1 = y 1 → x = y := by
    intro x y h0 h1; ext i; fin_cases i <;> assumption
  rcases hv_ne with hv0 | hv1
  · have hApos : 0 < 4 * (v0 ^ 2 + v1 ^ 2) := by positivity
    have hpoly : ∀ x : EuclideanSpace ℝ (Fin 2),
        (x 0 - o 0) ^ 2 + (x 1 - o 1) ^ 2 = r ^ 2 →
        2 * v0 * (x 0 - o 0) + 2 * v1 * (x 1 - o 1) = C →
        4 * (v0 ^ 2 + v1 ^ 2) * (x 1 - o 1) ^ 2 + (-4 * C * v1) * (x 1 - o 1) +
          (C ^ 2 - 4 * v0 ^ 2 * r ^ 2) = 0 := by
      intro x hq hl
      have h2v : 2 * v0 * (x 0 - o 0) = C - 2 * v1 * (x 1 - o 1) := by linarith
      have hsq : (2 * v0 * (x 0 - o 0)) ^ 2 = (C - 2 * v1 * (x 1 - o 1)) ^ 2 := by rw [h2v]
      linear_combination 4 * v0 ^ 2 * hq - hsq
    have hroots := quad_three (4 * (v0 ^ 2 + v1 ^ 2)) (-4 * C * v1) (C ^ 2 - 4 * v0 ^ 2 * r ^ 2)
      (x₁ 1 - o 1) (x₂ 1 - o 1) (x₃ 1 - o 1) hApos
      (hpoly x₁ hq1 hl1) (hpoly x₂ hq2 hl2) (hpoly x₃ hq3 hl3)
    rcases hroots with e | e | e
    · have hy : x₁ 1 = x₂ 1 := by linarith
      have hx : x₁ 0 = x₂ 0 := by
        have : 2 * v0 * (x₁ 0 - x₂ 0) = 0 := by linear_combination hl1 - hl2 - 2 * v1 * hy
        have := (mul_eq_zero.mp this).resolve_left (mul_ne_zero (by norm_num) hv0)
        linarith
      exact h12 (ext2 x₁ x₂ hx hy)
    · have hy : x₁ 1 = x₃ 1 := by linarith
      have hx : x₁ 0 = x₃ 0 := by
        have : 2 * v0 * (x₁ 0 - x₃ 0) = 0 := by linear_combination hl1 - hl3 - 2 * v1 * hy
        have := (mul_eq_zero.mp this).resolve_left (mul_ne_zero (by norm_num) hv0)
        linarith
      exact h13 (ext2 x₁ x₃ hx hy)
    · have hy : x₂ 1 = x₃ 1 := by linarith
      have hx : x₂ 0 = x₃ 0 := by
        have : 2 * v0 * (x₂ 0 - x₃ 0) = 0 := by linear_combination hl2 - hl3 - 2 * v1 * hy
        have := (mul_eq_zero.mp this).resolve_left (mul_ne_zero (by norm_num) hv0)
        linarith
      exact h23 (ext2 x₂ x₃ hx hy)
  · have hApos : 0 < 4 * (v0 ^ 2 + v1 ^ 2) := by positivity
    have hpoly : ∀ x : EuclideanSpace ℝ (Fin 2),
        (x 0 - o 0) ^ 2 + (x 1 - o 1) ^ 2 = r ^ 2 →
        2 * v0 * (x 0 - o 0) + 2 * v1 * (x 1 - o 1) = C →
        4 * (v0 ^ 2 + v1 ^ 2) * (x 0 - o 0) ^ 2 + (-4 * C * v0) * (x 0 - o 0) +
          (C ^ 2 - 4 * v1 ^ 2 * r ^ 2) = 0 := by
      intro x hq hl
      have h2v : 2 * v1 * (x 1 - o 1) = C - 2 * v0 * (x 0 - o 0) := by linarith
      have hsq : (2 * v1 * (x 1 - o 1)) ^ 2 = (C - 2 * v0 * (x 0 - o 0)) ^ 2 := by rw [h2v]
      linear_combination 4 * v1 ^ 2 * hq - hsq
    have hroots := quad_three (4 * (v0 ^ 2 + v1 ^ 2)) (-4 * C * v0) (C ^ 2 - 4 * v1 ^ 2 * r ^ 2)
      (x₁ 0 - o 0) (x₂ 0 - o 0) (x₃ 0 - o 0) hApos
      (hpoly x₁ hq1 hl1) (hpoly x₂ hq2 hl2) (hpoly x₃ hq3 hl3)
    rcases hroots with e | e | e
    · have hx : x₁ 0 = x₂ 0 := by linarith
      have hy : x₁ 1 = x₂ 1 := by
        have : 2 * v1 * (x₁ 1 - x₂ 1) = 0 := by linear_combination hl1 - hl2 - 2 * v0 * hx
        have := (mul_eq_zero.mp this).resolve_left (mul_ne_zero (by norm_num) hv1)
        linarith
      exact h12 (ext2 x₁ x₂ hx hy)
    · have hx : x₁ 0 = x₃ 0 := by linarith
      have hy : x₁ 1 = x₃ 1 := by
        have : 2 * v1 * (x₁ 1 - x₃ 1) = 0 := by linear_combination hl1 - hl3 - 2 * v0 * hx
        have := (mul_eq_zero.mp this).resolve_left (mul_ne_zero (by norm_num) hv1)
        linarith
      exact h13 (ext2 x₁ x₃ hx hy)
    · have hx : x₂ 0 = x₃ 0 := by linarith
      have hy : x₂ 1 = x₃ 1 := by
        have : 2 * v1 * (x₂ 1 - x₃ 1) = 0 := by linear_combination hl2 - hl3 - 2 * v0 * hx
        have := (mul_eq_zero.mp this).resolve_left (mul_ne_zero (by norm_num) hv1)
        linarith
      exact h23 (ext2 x₂ x₃ hx hy)

end Erdos132Circle

theorem OMA.solution : OMA.R_erdos_132_R1_H2_R1_H2_R2.H1 := by
  classical
  intro A o r hA k hk
  let B := A.erase o
  have hBcard : 2 * k + 2 ≤ B.card := by
    dsimp only [B]
    by_cases ho : o ∈ A
    · have h1 := card_erase_of_mem ho; omega
    · rw [erase_eq_of_notMem ho]; omega
  have hB_dist : ∀ x ∈ B, x ≠ o ∧ dist x o = r := by
    intro x hx
    have hxo : x ≠ o := (mem_erase.mp hx).1
    have hxA : x ∈ A := (mem_erase.mp hx).2
    exact ⟨hxo, (hA x hxA).resolve_left hxo⟩
  have hBne : B.Nonempty := card_pos.mp (by omega)
  obtain ⟨p, hpB⟩ := hBne
  let B' := B.erase p
  have hB'card : 2 * k + 1 ≤ B'.card := by
    dsimp only [B']
    have h1 := card_erase_of_mem hpB; omega
  let D := B'.image (fun y => dist p y)
  have hD_card : k + 1 ≤ D.card := by
    have hsum : B'.card = ∑ d ∈ D, (B'.filter fun y => dist p y = d).card :=
      card_eq_sum_card_image (fun y => dist p y) B'
    have hle : ∑ d ∈ D, (B'.filter fun y => dist p y = d).card ≤ ∑ _d ∈ D, 2 := by
      apply sum_le_sum
      intro d _
      apply Erdos132Circle.circle_inter_le_two o p (hB_dist p hpB).1 r d
      intro y hy
      have hyB' := (mem_filter.mp hy).1
      have hyd := (mem_filter.mp hy).2
      have hyB : y ∈ B := (mem_erase.mp hyB').2
      exact ⟨(hB_dist y hyB).2, by rw [dist_comm]; exact hyd⟩
    simp only [sum_const, smul_eq_mul] at hle
    omega
  have hsub_rare : D.erase r ⊆ rareDistances A := by
    intro d hd
    have hdr : d ≠ r := (mem_erase.mp hd).1
    have hdD : d ∈ D := (mem_erase.mp hd).2
    obtain ⟨q, hqB', hqp_dist⟩ := mem_image.mp hdD
    have hqp : q ≠ p := (mem_erase.mp hqB').1
    have hqB : q ∈ B := (mem_erase.mp hqB').2
    have hpA : p ∈ A := (mem_erase.mp hpB).2
    have hqA : q ∈ A := (mem_erase.mp hqB).2
    have hpq_off : (p, q) ∈ A.offDiag := mem_offDiag.mpr ⟨hpA, hqA, hqp.symm⟩
    have hqp_off : (q, p) ∈ A.offDiag := mem_offDiag.mpr ⟨hqA, hpA, hqp⟩
    refine mem_filter.mpr ⟨mem_image.mpr ⟨(p, q), hpq_off, hqp_dist⟩, ?_, ?_⟩
    · -- pairMultiplicity A d ≥ 1
      unfold pairMultiplicity
      have hpair_sub : ({(p, q), (q, p)} : Finset _) ⊆ A.offDiag.filter (fun u => dist u.1 u.2 = d) := by
        intro u hu
        rcases mem_insert.mp hu with rfl | hu2
        · exact mem_filter.mpr ⟨hpq_off, hqp_dist⟩
        · rw [mem_singleton.mp hu2]
          exact mem_filter.mpr ⟨hqp_off, by rw [dist_comm]; exact hqp_dist⟩
      have hne_pairs : ((p, q) : EuclideanSpace ℝ (Fin 2) × _) ≠ (q, p) :=
        fun h => hqp.symm (congrArg Prod.fst h)
      have hcard2 : 2 ≤ (A.offDiag.filter (fun u => dist u.1 u.2 = d)).card := by
        calc 2 = ({(p, q), (q, p)} : Finset _).card := (card_pair hne_pairs).symm
          _ ≤ _ := card_le_card hpair_sub
      omega
    · -- pairMultiplicity A d ≤ A.card
      unfold pairMultiplicity
      have hord_le : (A.offDiag.filter (fun u => dist u.1 u.2 = d)).card ≤ 2 * B.card := by
        have hsub_prod : A.offDiag.filter (fun u => dist u.1 u.2 = d) ⊆
            B.biUnion fun x => (B.filter fun y => dist x y = d).image (fun y => (x, y)) := by
          rintro ⟨x, y⟩ hxy
          obtain ⟨hoff, hdist⟩ := mem_filter.mp hxy
          obtain ⟨hxA, hyA, _⟩ := mem_offDiag.mp hoff
          have hxo : x ≠ o := by
            intro h
            have hyo : y ≠ o := by rw [← h]; exact (mem_offDiag.mp hoff).2.2.symm
            have : dist x y = r := by rw [h, dist_comm]; exact (hA y hyA).resolve_left hyo
            exact hdr (hdist.symm.trans this)
          have hyo : y ≠ o := by
            intro h
            have : dist x y = r := by rw [h]; exact (hA x hxA).resolve_left hxo
            exact hdr (hdist.symm.trans this)
          have hxB : x ∈ B := mem_erase.mpr ⟨hxo, hxA⟩
          have hyB : y ∈ B := mem_erase.mpr ⟨hyo, hyA⟩
          exact mem_biUnion.mpr ⟨x, hxB, mem_image.mpr ⟨y, mem_filter.mpr ⟨hyB, hdist⟩, rfl⟩⟩
        calc (A.offDiag.filter (fun u => dist u.1 u.2 = d)).card
            ≤ (B.biUnion fun x => (B.filter fun y => dist x y = d).image (fun y => (x, y))).card :=
              card_le_card hsub_prod
          _ ≤ ∑ x ∈ B, ((B.filter fun y => dist x y = d).image (fun y => (x, y))).card :=
              card_biUnion_le
          _ ≤ ∑ x ∈ B, (B.filter fun y => dist x y = d).card :=
              sum_le_sum fun _ _ => card_image_le
          _ ≤ ∑ _x ∈ B, 2 := by
              apply sum_le_sum
              intro x hxB
              apply Erdos132Circle.circle_inter_le_two o x (hB_dist x hxB).1 r d
              intro y hy
              exact ⟨(hB_dist y (mem_filter.mp hy).1).2, by rw [dist_comm]; exact (mem_filter.mp hy).2⟩
          _ = 2 * B.card := by simp [sum_const, smul_eq_mul, mul_comm]
      have hBA : B.card ≤ A.card := card_erase_le
      omega
  have herase : k ≤ (D.erase r).card := by
    by_cases hr : r ∈ D
    · have := card_erase_of_mem hr; omega
    · rw [erase_eq_of_notMem hr]; omega
  exact herase.trans (card_le_card hsub_rare)
