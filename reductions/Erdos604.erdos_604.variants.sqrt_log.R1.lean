import FormalConjectures.ErdosProblems.«604»

/-! The sharp pinned bound follows from an algebraic integer transfer and an arithmetic
reciprocal-fiber estimate. One pin with more than half of the targets in small fibers
already yields the sharp bound by summing inverse fiber sizes. -/

-- Credit: @NicholasWierenga

/-
For H1 one can record distinctness and all pinned squared-distance equalities as
polynomial conditions over the integers. Transfer to the real algebraic numbers
preserves these conditions. A common positive integer then scales the finitely
many coordinates to algebraic integers. A related formal specialization for
unpinned distances is in open-math-agents pull request 2219.

H2 requires one constant over all degrees and heights. Only configurations in
which the small fibers contain at most n/2 targets at every pin enter that step.
-/

open Filter
open scoped EuclideanGeometry Finset

namespace OMA.R_Erdos604_erdos_604_variants_sqrt_log_R1

/-- Every finite planar configuration admits one of the same size with algebraic integer
coordinates and no increase in its largest pinned distance count. -/
def H1 : Prop :=
  ∀ A : Finset ℝ², ∃ B : Finset ℝ², B.card = A.card ∧
    (∀ b ∈ B, ∀ i : Fin 2, IsIntegral ℤ (b i)) ∧
    B.sup (distinctDistancesFrom B) ≤ A.sup (distinctDistancesFrom A)

open Classical in
/-- The reciprocal distance-fiber sum has the sharp average lower bound for finite planar
configurations with algebraic integer coordinates in which every pin has at most half of the
targets in fibers of size at most the square root of the logarithm of the configuration size. -/
def H2 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ B : Finset ℝ², B.card = n →
    (∀ b ∈ B, ∀ i : Fin 2, IsIntegral ℤ (b i)) →
    (∀ x ∈ B, 2 * ((B.erase x).filter (fun y =>
      (((B.erase x).filter (fun z => dist z x = dist y x)).card : ℝ) ≤
        (n : ℝ).log.sqrt)).card ≤ n) →
    C * (n : ℝ) ^ 2 / (n : ℝ).log.sqrt ≤
      ∑ x ∈ B, ∑ y ∈ B.erase x,
        (((B.erase x).filter (fun z => dist z x = dist y x)).card : ℝ)⁻¹

open Classical in
private theorem sum_inv_fiber_card (B : Finset ℝ²) (x : ℝ²) :
    (∑ y ∈ B.erase x,
      (((B.erase x).filter (fun z => dist z x = dist y x)).card : ℝ)⁻¹) =
        (distinctDistancesFrom B x : ℝ) := by
  classical
  let S := B.erase x
  let f : ℝ² → ℝ := fun z => dist z x
  have hmap : ∀ y ∈ S, f y ∈ S.image f := fun y hy => Finset.mem_image_of_mem f hy
  calc
    _ = ∑ d ∈ S.image f, ∑ _z ∈ S.filter (fun z => f z = d),
          ((S.filter (fun z => f z = d)).card : ℝ)⁻¹ := by
      simpa only [S, f] using
        (Finset.sum_fiberwise_of_maps_to' hmap
          (fun d => ((S.filter (fun z => f z = d)).card : ℝ)⁻¹)).symm
    _ = ∑ _d ∈ S.image f, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro d hd
      obtain ⟨z, hz, heq⟩ := Finset.mem_image.mp hd
      have hpos : 0 < (S.filter (fun z => f z = d)).card :=
        Finset.card_pos.mpr ⟨z, Finset.mem_filter.mpr ⟨hz, heq⟩⟩
      have hne : ((S.filter (fun z => f z = d)).card : ℝ) ≠ 0 := by
        exact_mod_cast hpos.ne'
      rw [Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ hne]
    _ = ((S.image f).card : ℝ) := by simp
    _ = _ := by
      unfold distinctDistancesFrom
      congr 2
      ext d
      simp [S, f]

open Classical in
private theorem light_fibers_bound (B : Finset ℝ²) (x : ℝ²) (L : ℝ) :
    (((B.erase x).filter (fun y =>
      (((B.erase x).filter (fun z => dist z x = dist y x)).card : ℝ) ≤ L)).card : ℝ) / L ≤
        (distinctDistancesFrom B x : ℝ) := by
  classical
  let S := B.erase x
  let F := fun y : ℝ² => S.filter (fun z => dist z x = dist y x)
  let T := S.filter (fun y => ((F y).card : ℝ) ≤ L)
  rw [← sum_inv_fiber_card]
  calc
    (T.card : ℝ) / L = ∑ _y ∈ T, L⁻¹ := by
      simp [div_eq_mul_inv, nsmul_eq_mul]
    _ ≤ ∑ y ∈ T, ((F y).card : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro y hy
      obtain ⟨hyS, hyL⟩ := Finset.mem_filter.mp hy
      have hpos : 0 < (F y).card :=
        Finset.card_pos.mpr ⟨y, Finset.mem_filter.mpr ⟨hyS, rfl⟩⟩
      have hpos_real : (0 : ℝ) < (F y).card := by exact_mod_cast hpos
      simpa only [one_div] using one_div_le_one_div_of_le hpos_real hyL
    _ ≤ ∑ y ∈ S, ((F y).card : ℝ)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by intros; positivity)

theorem main :
    H1 → H2 → type_of% @Erdos604.erdos_604.variants.sqrt_log := by
  classical
  intro htransfer
  rintro ⟨C, hC, harithmetic⟩
  let c : ℝ := min C (1 / 2)
  have hc : 0 < c := lt_min hC (by norm_num)
  refine Asymptotics.isBigO_iff.mpr ⟨c⁻¹, ?_⟩
  filter_upwards [harithmetic, eventually_ge_atTop (1 : ℕ)] with n hn hnpos
  obtain ⟨X, hX⟩ := Infinite.exists_subset_card_eq ℝ² n
  have hnonempty :
      {m : ℕ | ∃ A : Finset ℝ², A.card = n ∧ A.sup (distinctDistancesFrom A) = m}.Nonempty :=
    ⟨_, X, hX, rfl⟩
  have hminimum : ∃ A : Finset ℝ², A.card = n ∧
      A.sup (distinctDistancesFrom A) = Erdos604.pinnedDistinctDistances n :=
    Nat.sInf_mem hnonempty
  obtain ⟨A, hA, hsup⟩ := hminimum
  obtain ⟨B, hB, hcoord, hle⟩ := htransfer A
  have hBn : B.card = n := hB.trans hA
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hbound : c * ((n : ℝ) / (n : ℝ).log.sqrt) ≤
      (Erdos604.pinnedDistinctDistances n : ℝ) := by
    by_cases hheavy : ∀ x ∈ B, 2 * ((B.erase x).filter (fun y =>
        (((B.erase x).filter (fun z => dist z x = dist y x)).card : ℝ) ≤
          (n : ℝ).log.sqrt)).card ≤ n
    · have hlower := hn B hBn hcoord hheavy
      simp only [sum_inv_fiber_card] at hlower
      have hsum : (∑ x ∈ B, distinctDistancesFrom B x) ≤
          n * Erdos604.pinnedDistinctDistances n := by
        calc
          _ ≤ ∑ _x ∈ B, Erdos604.pinnedDistinctDistances n := by
            apply Finset.sum_le_sum
            intro x hx
            rw [← hsup]
            exact (Finset.le_sup hx).trans hle
          _ = _ := by simp [hBn]
      have hsum_real : (∑ x ∈ B, (distinctDistancesFrom B x : ℝ)) ≤
          (n : ℝ) * (Erdos604.pinnedDistinctDistances n : ℝ) := by exact_mod_cast hsum
      apply le_of_mul_le_mul_left _ hnreal
      calc
        (n : ℝ) * (c * ((n : ℝ) / (n : ℝ).log.sqrt)) =
            c * ((n : ℝ) ^ 2 / (n : ℝ).log.sqrt) := by ring
        _ ≤ C * ((n : ℝ) ^ 2 / (n : ℝ).log.sqrt) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
        _ = C * (n : ℝ) ^ 2 / (n : ℝ).log.sqrt := by ring
        _ ≤ ∑ x ∈ B, (distinctDistancesFrom B x : ℝ) := hlower
        _ ≤ _ := hsum_real
    · push Not at hheavy
      obtain ⟨x, hx, hxlight⟩ := hheavy
      let T := (B.erase x).filter (fun y =>
        (((B.erase x).filter (fun z => dist z x = dist y x)).card : ℝ) ≤ (n : ℝ).log.sqrt)
      have hmany : (n : ℝ) < 2 * (T.card : ℝ) := by
        exact_mod_cast (show n < 2 * T.card from hxlight)
      have hd : distinctDistancesFrom B x ≤ Erdos604.pinnedDistinctDistances n := by
        rw [← hsup]
        exact (Finset.le_sup hx).trans hle
      calc
        _ ≤ (1 / 2 : ℝ) * ((n : ℝ) / (n : ℝ).log.sqrt) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
        _ = ((n : ℝ) / 2) / (n : ℝ).log.sqrt := by ring
        _ ≤ (T.card : ℝ) / (n : ℝ).log.sqrt :=
          div_le_div_of_nonneg_right (by linarith) (by positivity)
        _ ≤ (distinctDistancesFrom B x : ℝ) := light_fibers_bound B x _
        _ ≤ _ := by exact_mod_cast hd
  simp only [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ (n : ℝ) / (n : ℝ).log.sqrt by positivity),
    abs_of_nonneg (show 0 ≤ (Erdos604.pinnedDistinctDistances n : ℝ) by positivity)]
  calc
    _ ≤ (Erdos604.pinnedDistinctDistances n : ℝ) / c :=
      (le_div_iff₀ hc).2 (by simpa only [mul_comm c] using hbound)
    _ = _ := by rw [div_eq_mul_inv, mul_comm]

end OMA.R_Erdos604_erdos_604_variants_sqrt_log_R1
