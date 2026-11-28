import OMAStatements.S_mo_198221
import Mathlib

open OMA.S_mo_198221 Finset Set
open scoped RealInnerProductSpace

namespace DirectionOptimization

noncomputable section

private def disk : Set Plane := Metric.closedBall 0 1

private theorem disk_mem (v : Plane) : v ∈ disk ↔ ‖v‖ ≤ 1 := by
  simp [disk, Metric.mem_closedBall, dist_zero_right]

private theorem net_exists (ε : ℝ) (hε : 0 < ε) : ∃ D : Finset Plane, directionNet ε D := by
  classical
  have hc : IsCompact disk := isCompact_closedBall _ _
  obtain ⟨T, hT, hfin, hcov⟩ := hc.finite_cover_balls hε
  refine ⟨hfin.toFinset, ⟨?_, ?_⟩⟩
  · intro d hd
    exact (disk_mem d).mp (hT (hfin.mem_toFinset.mp hd))
  · intro z hz
    have hh := hcov ((disk_mem z).mpr hz)
    simp only [mem_iUnion, Metric.mem_ball] at hh
    obtain ⟨d, hd, hdist⟩ := hh
    exact ⟨d, hfin.mem_toFinset.mpr hd, hdist.le⟩

private def objective {n : ℕ} (u : Directions n) (x : Configuration n) : ℝ :=
  ∑ i, ∑ j, ⟪u i j,x i-x j⟫

private theorem objective_eq {n : ℕ} (u : Directions n) (x : Configuration n) :
    objective u x = ∑ i, ⟪resultant u i,x i⟫ := by
  unfold objective resultant
  simp only [sum_inner, inner_sub_left, inner_sub_right, sum_sub_distrib]
  rw [sum_comm (f := fun i j => ⟪u i j,x j⟫)]

private theorem objective_le_energy {n : ℕ} {u : Directions n} (hu : withinDisk u)
    (x : Configuration n) : objective u x ≤ energy x := by
  unfold objective energy
  apply sum_le_sum
  intro i _
  apply sum_le_sum
  intro j _
  exact (real_inner_le_norm _ _).trans
    (by simpa using mul_le_mul_of_nonneg_right (hu i j) (norm_nonneg (x i-x j)))

private theorem support_optimal {n : ℕ} {C : Set Plane} {p : Plane → Plane}
    (hp : supportChoice C p) (u : Directions n) {x : Configuration n}
    (hx : ∀ i, x i ∈ C) : objective u x ≤ score p u := by
  rw [objective_eq, score]
  exact sum_le_sum fun i _ => (hp _).2 _ (hx i)

private theorem picked_mem {n : ℕ} {C : Set Plane} {p : Plane → Plane}
    (hp : supportChoice C p) (u : Directions n) (i : Fin n) : picked p u i ∈ C :=
  (hp (resultant u i)).1

private theorem score_le_energy {n : ℕ} {p : Plane → Plane} {u : Directions n}
    (hu : withinDisk u) : score p u ≤ energy (picked p u) := by
  simpa only [objective_eq, score] using objective_le_energy hu (picked p u)

private def direction (v : Plane) : Plane := ‖v‖⁻¹ • v

private theorem direction_unit (v : Plane) : ‖direction v‖ ≤ 1 := by
  by_cases hz : v = 0
  · simp [hz, direction]
  · have hn : 0 < ‖v‖ := norm_pos_iff.mpr hz
    simp [direction, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hn.le), hn.ne']

private theorem direction_value (v : Plane) : ⟪direction v,v⟫ = ‖v‖ := by
  by_cases hz : v = 0
  · simp [hz, direction]
  · have hn : 0 < ‖v‖ := norm_pos_iff.mpr hz
    rw [direction, real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp

private def directionsOf {n : ℕ} (x : Configuration n) : Directions n :=
  fun i j => direction (x i-x j)

private theorem directionsOf_disk {n : ℕ} (x : Configuration n) : withinDisk (directionsOf x) :=
  fun i j => direction_unit (x i-x j)

private theorem directionsOf_energy {n : ℕ} (x : Configuration n) :
    objective (directionsOf x) x = energy x := by
  simp [objective, directionsOf, energy, direction_value]

private theorem approximate_direction (v d : Plane) (ε : ℝ)
    (hd : dist (direction v) d ≤ ε) : (1-ε)*‖v‖ ≤ ⟪d,v⟫ := by
  have hnorm : ‖direction v-d‖ ≤ ε := by simpa [dist_eq_norm] using hd
  have hinner := (real_inner_le_norm (direction v-d) v).trans
    (mul_le_mul_of_nonneg_right hnorm (norm_nonneg v))
  rw [inner_sub_left, direction_value] at hinner
  nlinarith

private theorem approximation {n : ℕ} {ε : ℝ} {D : Finset Plane} (hD : directionNet ε D)
    (x : Configuration n) : ∃ u : Directions n, uses D u ∧ (1-ε)*energy x ≤ objective u x := by
  choose u hu hdist using
    fun (i j : Fin n) => hD.2 (direction (x i-x j)) (direction_unit _)
  refine ⟨u, hu, ?_⟩
  unfold objective energy
  simp_rw [mul_sum]
  exact sum_le_sum fun i _ => sum_le_sum fun j _ =>
    approximate_direction _ _ _ (hdist i j)

private theorem finite_max {n : ℕ} {ε : ℝ} {D : Finset Plane} (hD : directionNet ε D)
    (p : Plane → Plane) :
    ∃ u : Directions n, uses D u ∧ ∀ v : Directions n, uses D v → score p v ≤ score p u := by
  classical
  obtain ⟨d, hd, _⟩ := hD.2 0 (by simp)
  letI : Nonempty D := ⟨⟨d, hd⟩⟩
  let lift (v : Fin n → Fin n → D) : Directions n := fun i j => v i j
  obtain ⟨u, _, hu⟩ := (univ : Finset (Fin n → Fin n → D)).exists_max_image
    (fun v => score p (lift v)) univ_nonempty
  refine ⟨lift u, fun i j => (u i j).property, ?_⟩
  intro v hv
  let v' (i j : Fin n) : D := ⟨v i j, hv i j⟩
  exact hu v' (mem_univ _)

private theorem config_max {n : ℕ} {C : Set Plane} (hc : IsCompact C) (hne : C.Nonempty) :
    ∃ x : Configuration n, (∀ i, x i ∈ C) ∧
      ∀ y : Configuration n, (∀ i, y i ∈ C) → energy y ≤ energy x := by
  let S : Set (Configuration n) := {x | ∀ i, x i ∈ C}
  have hS : IsCompact S := isCompact_pi_infinite (fun _ => hc)
  obtain ⟨c, hc'⟩ := hne
  have hneS : S.Nonempty := ⟨fun _ => c, by simpa [S] using fun _ : Fin n => hc'⟩
  have hcont : Continuous (energy (n := n)) := by unfold energy; fun_prop
  obtain ⟨x, hx, hm⟩ := hS.exists_isMaxOn hneS hcont.continuousOn
  refine ⟨x, by simpa [S] using hx, ?_⟩
  intro y hy
  exact hm (by simpa [S] using hy : y ∈ S)

theorem result :
    (∀ (ε : ℝ), 0 < ε → ∃ D : Finset Plane, directionNet ε D) ∧
    ∀ (C : Set Plane), IsCompact C → C.Nonempty → ∃ p : Plane → Plane,
      supportChoice C p ∧ ∀ n : ℕ,
      ((∃ u : Directions n, withinDisk u ∧ ∀ v : Directions n, withinDisk v → score p v ≤ score p u) ∧
       (∀ u : Directions n, withinDisk u → (∀ v : Directions n, withinDisk v → score p v ≤ score p u) →
        energy (picked p u) = score p u ∧ ∀ x : Configuration n,
          (∀ i, x i ∈ C) → energy x ≤ energy (picked p u))) ∧
      ∀ (ε : ℝ) (D : Finset Plane), directionNet ε D →
        (∃ u : Directions n, uses D u ∧ ∀ v : Directions n, uses D v → score p v ≤ score p u) ∧
        ∀ u : Directions n, uses D u → (∀ v : Directions n, uses D v → score p v ≤ score p u) →
          ∀ x : Configuration n, (∀ i, x i ∈ C) → (1-ε)*energy x ≤ energy (picked p u) := by
  classical
  refine ⟨net_exists, ?_⟩
  intro C hC hne
  have hsupport (b : Plane) : ∃ p ∈ C, ∀ y ∈ C, ⟪b,y⟫ ≤ ⟪b,p⟫ := by
    have hc : Continuous fun y : Plane => ⟪b,y⟫ := by fun_prop
    obtain ⟨p, hp, hm⟩ := hC.exists_isMaxOn hne hc.continuousOn
    exact ⟨p, hp, fun _ hy => hm hy⟩
  choose p hp hmax using hsupport
  have hs : supportChoice C p := fun b => ⟨hp b, hmax b⟩
  refine ⟨p, hs, fun n => ⟨?_, ?_⟩⟩
  · obtain ⟨x, hx, hxmax⟩ := config_max (n := n) hC hne
    have hexact : energy x = score p (directionsOf x) := by
      apply le_antisymm
      · rw [← directionsOf_energy x]
        exact support_optimal hs _ hx
      · exact (score_le_energy (directionsOf_disk x)).trans (hxmax _ (picked_mem hs _))
    have hub (u : Directions n) (hu : withinDisk u) : score p u ≤ energy x :=
      (score_le_energy hu).trans (hxmax _ (picked_mem hs _))
    refine ⟨⟨directionsOf x, directionsOf_disk x, fun u hu => (hub u hu).trans hexact.le⟩, ?_⟩
    intro u hu humax
    have hxu : energy x ≤ score p u := hexact.le.trans (humax _ (directionsOf_disk x))
    have hsu := score_le_energy (p := p) hu
    refine ⟨le_antisymm ((hxmax _ (picked_mem hs _)).trans hxu) hsu, ?_⟩
    exact fun _ hy => (hxmax _ hy).trans (hxu.trans hsu)
  · intro ε D hD
    refine ⟨finite_max hD p, ?_⟩
    intro u hu humax x hx
    obtain ⟨v, hv, hval⟩ := approximation hD x
    exact hval.trans ((support_optimal hs v hx).trans ((humax v hv).trans
      (score_le_energy fun i j => hD.1 _ (hu i j))))

end

end DirectionOptimization

namespace OMA

theorem solution :
    (∀ (ε : ℝ), 0 < ε → ∃ D : Finset Plane, directionNet ε D) ∧
    ∀ (C : Set Plane), IsCompact C → C.Nonempty → ∃ p : Plane → Plane,
      supportChoice C p ∧ ∀ n : ℕ,
      ((∃ u : Directions n, withinDisk u ∧ ∀ v : Directions n, withinDisk v → score p v ≤ score p u) ∧
       (∀ u : Directions n, withinDisk u → (∀ v : Directions n, withinDisk v → score p v ≤ score p u) →
        energy (picked p u) = score p u ∧ ∀ x : Configuration n,
          (∀ i, x i ∈ C) → energy x ≤ energy (picked p u))) ∧
      ∀ (ε : ℝ) (D : Finset Plane), directionNet ε D →
        (∃ u : Directions n, uses D u ∧ ∀ v : Directions n, uses D v → score p v ≤ score p u) ∧
        ∀ u : Directions n, uses D u → (∀ v : Directions n, uses D v → score p v ≤ score p u) →
          ∀ x : Configuration n, (∀ i, x i ∈ C) → (1-ε)*energy x ≤ energy (picked p u) :=
  DirectionOptimization.result

end OMA