import FormalConjectures.ErdosProblems.«1070»
import Mathlib

/-!
Finite planar unit-distance graphs can have independence ratio below one quarter.
Mathematical proof: Ákos Dúcz and Dániel Varga, arXiv:2606.28157.
Adapted from the published Left to Solve reduction by @ysanatomic (#5286),
the averaging proof by @ysanatomic (#5657), and the G29 certificate by @Genbox (#8732).
These three arguments are included here to check the full catalog target in one file.
-/

/-! A geometric averaging reduction for an independence ratio strictly below one quarter. -/

-- The finite dual certificate and the averaging method are due to Dúcz–Varga and
-- Matolcsi–Ruzsa–Varga–Zsámboki, arXiv:2606.28157 and arXiv:2311.10069.

-- Credit: @ysanatomic

namespace OMA.R_Erdos1070_erdos_1070_parts_ii_R1

open SimpleGraph BigOperators

private theorem complex_independent
    (h : ∀ n : ℕ, (n : ℝ) / 4 ≤ (Erdos1070.f n : ℝ)) :
    ∀ X : Finset ℂ, ∃ B ⊆ X, (X.card : ℝ) / 4 ≤ B.card ∧
      ∀ x ∈ B, ∀ y ∈ B, dist x y ≠ 1 := by
  classical
  intro X
  let e := Complex.orthonormalBasisOneI.repr
  let Y := X.map e.toEquiv.toEmbedding
  let G := UnitDistancePlaneGraph (Y : Set (EuclideanSpace ℝ (Fin 2)))
  obtain ⟨D, hD⟩ := G.exists_isNIndepSet_indepNum
  let r : (Y : Set (EuclideanSpace ℝ (Fin 2))) ↪ ℂ :=
    ⟨fun v ↦ e.symm v.val, fun v w hvw ↦ Subtype.ext (e.symm.injective hvw)⟩
  refine ⟨D.map r, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨z, hz, hzy⟩ := Finset.mem_map.mp (show y.val ∈ Y from y.property)
    convert hz using 1
    change e.symm y.val = z
    exact e.symm_apply_eq.mpr hzy.symm
  · rw [Finset.card_map, hD.card_eq]
    have hc : Y.card = X.card := Finset.card_map _
    rw [← hc]
    exact (h Y.card).trans (by exact_mod_cast Erdos1070.f_le Y)
  · intro x hx y hy hxy
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hy
    have hdist := e.symm.isometry.dist_eq v.val w.val
    change dist (e.symm v.val) (e.symm w.val) = 1 at hxy
    rw [hdist] at hxy
    have hne : v ≠ w := by
      intro eq
      subst w
      simp at hxy
    exact hD.isIndepSet hv hw hne hxy

/-- The G29 integer dual inequalities on independent subsets, with certified congruences. -/
def H1 : Prop := by
  classical
  exact ∃ p : Fin 29 → ℂ, ∃ C : List (ℤ × Finset (Fin 29) × Finset (Fin 29)),
    (∀ r ∈ C, ∃ a b : ℂ, ‖a‖ = 1 ∧
      (r.2.1.image (fun i ↦ a * p i + b) = r.2.2.image p ∨
        r.2.1.image (fun i ↦ a * (star (p i)) + b) = r.2.2.image p)) ∧
    ∃ D N : ℤ, 0 < D ∧ 4 * D < N ∧
    ∀ I : Finset (Fin 29), (∀ i ∈ I, ∀ j ∈ I, dist (p i) (p j) ≠ 1) →
      N * (if 0 ∈ I then 1 else 0) ≤ D +
        (C.map fun r ↦ r.1 * ((if r.2.1 ⊆ I then 1 else 0) -
                                      (if r.2.2 ⊆ I then 1 else 0))).sum

/-- Approximate local moments of independent sets, if every finite complex geometry has
an independent subset of relative size at least one quarter. -/
def H2 : Prop := by
  classical
  exact ∀ (p : Fin 29 → ℂ) (C : List (ℤ × Finset (Fin 29) × Finset (Fin 29))),
    (∀ r ∈ C, ∃ a b : ℂ, ‖a‖ = 1 ∧
      (r.2.1.image (fun i ↦ a * p i + b) = r.2.2.image p ∨
        r.2.1.image (fun i ↦ a * (star (p i)) + b) = r.2.2.image p)) →
    (∀ X : Finset ℂ, ∃ B ⊆ X, (X.card : ℝ) / 4 ≤ B.card ∧
      ∀ x ∈ B, ∀ y ∈ B, dist x y ≠ 1) →
    ∀ ε > (0 : ℝ), ∃ μ : Finset (Fin 29) → ℝ,
      (∀ I, 0 ≤ μ I) ∧ (∑ I, μ I) = 1 ∧
      (∀ I, ¬ (∀ i ∈ I, ∀ j ∈ I, dist (p i) (p j) ≠ 1) → μ I = 0) ∧
      let moment := fun S : Finset (Fin 29) ↦ ∑ I, if S ⊆ I then μ I else 0
      1 / 4 - ε ≤ moment {0} ∧ ∀ r ∈ C, |moment r.2.1 - moment r.2.2| ≤ ε


theorem main : H1 → H2 → type_of% @Erdos1070.erdos_1070.parts.ii := by
  classical
  intro hCert hAveraging h
  obtain ⟨p, C, hCongruent, d, n, hd, hnd, hDual⟩ := hCert
  let N : ℝ := n
  let D : ℝ := d
  have hD : 0 < D := by
    change (0 : ℝ) < (d : ℝ)
    exact_mod_cast hd
  have hND : 4 * D < N := by
    change (4 : ℝ) * (d : ℝ) < (n : ℝ)
    exact_mod_cast hnd
  have hgap : 0 < N / 4 - D := by linarith
  let W : ℝ := (C.map fun r ↦ |(r.1 : ℝ)|).sum
  have hW : 0 ≤ W := by
    change 0 ≤ (C.map fun r ↦ |(r.1 : ℝ)|).sum
    apply List.sum_nonneg
    intro x hx
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hx
    exact abs_nonneg _
  let ε := (N / 4 - D) / (N + W + 1)
  have hN : 0 ≤ N := by linarith
  have hTotal : 0 < N + W + 1 := by linarith
  have hε : 0 < ε := div_pos hgap hTotal
  obtain ⟨μ, hμ, hmass, hzero, hroot, hshape⟩ :=
    hAveraging p C hCongruent (complex_independent h) ε hε
  let moment (S : Finset (Fin 29)) : ℝ := ∑ I, if S ⊆ I then μ I else 0
  let contribution (r : ℤ × Finset (Fin 29) × Finset (Fin 29)) (I : Finset (Fin 29)) :=
    (r.1 : ℝ) * ((if r.2.1 ⊆ I then μ I else 0) - (if r.2.2 ⊆ I then μ I else 0))
  have hPoint (I : Finset (Fin 29)) :
      N * (if ({0} : Finset (Fin 29)) ⊆ I then μ I else 0) ≤
        D * μ I + (C.map fun r ↦ contribution r I).sum := by
    by_cases hI : ∀ i ∈ I, ∀ j ∈ I, dist (p i) (p j) ≠ 1
    · have hr : N * (if 0 ∈ I then (1 : ℝ) else 0) ≤ D +
          (C.map fun r ↦ (r.1 : ℝ) * ((if r.2.1 ⊆ I then 1 else 0) -
                                               (if r.2.2 ⊆ I then 1 else 0))).sum := by
        have hi := (Int.cast_le (R := ℝ)).mpr (hDual I hI)
        simpa only [N, D, Int.cast_mul, Int.cast_add, Int.cast_sub, Int.cast_list_sum,
          List.map_map, Function.comp_def, apply_ite (fun x : ℤ ↦ (x : ℝ)),
          Int.cast_one, Int.cast_zero, Int.cast_ofNat] using hi
      have hmul := mul_le_mul_of_nonneg_right hr (hμ I)
      rw [add_mul, ← List.sum_map_mul_right] at hmul
      simpa only [List.map_map, Function.comp_def, mul_assoc, sub_mul, ite_mul, one_mul,
        zero_mul, contribution, Finset.singleton_subset_iff] using hmul
    · simp [hzero I hI, contribution]
  have hSwap (L : List (ℤ × Finset (Fin 29) × Finset (Fin 29))) :
      ∑ I, (L.map fun r ↦ contribution r I).sum =
        (L.map fun r ↦ (r.1 : ℝ) * (moment r.2.1 - moment r.2.2)).sum := by
    induction L with
    | nil => simp
    | cons r L ih =>
      simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]
      congr 1
      simp [contribution, moment, Finset.mul_sum, ← Finset.sum_sub_distrib, mul_sub]
  have hAvg :
      N * moment {0} ≤ D + (C.map fun r ↦ (r.1 : ℝ) * (moment r.2.1 - moment r.2.2)).sum := by
    have hm := Finset.sum_le_sum (fun I (_ : I ∈ (Finset.univ : Finset (Finset (Fin 29)))) ↦ hPoint I)
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, hmass, mul_one, hSwap] at hm
    exact hm
  have hErr :
      (C.map fun r ↦ (r.1 : ℝ) * (moment r.2.1 - moment r.2.2)).sum ≤ W * ε := by
    unfold W
    rw [← List.sum_map_mul_right]
    refine List.sum_le_sum ?_
    intro r hr
    calc
      (r.1 : ℝ) * (moment r.2.1 - moment r.2.2)
          ≤ |(r.1 : ℝ) * (moment r.2.1 - moment r.2.2)| := le_abs_self _
      _ = |(r.1 : ℝ)| * |moment r.2.1 - moment r.2.2| := abs_mul _ _
      _ ≤ |(r.1 : ℝ)| * ε := mul_le_mul_of_nonneg_left (hshape r hr) (abs_nonneg _)
  have hBound : (N + W) * ε < N / 4 - D := by
    dsimp [ε]
    rw [← mul_div_assoc, div_lt_iff₀ hTotal, mul_comm (N + W)]
    exact mul_lt_mul_of_pos_left (by linarith) hgap
  have hm : N * (1 / 4 - ε) ≤ N * moment {0} := mul_le_mul_of_nonneg_left hroot hN
  linarith

end OMA.R_Erdos1070_erdos_1070_parts_ii_R1

/-! Finite sums with slowly growing support and with room for prescribed shifts. -/

namespace OMA.Erdos1070

open Filter BigOperators Topology

section FiniteSums

variable {ι G : Type*} [Fintype ι] [AddCommGroup G]

private def evalBox (g : ι → G) (n : ℕ) (a : ι → Fin (2 * n + 1)) : G :=
  ∑ i, (((a i : ℕ) : ℤ) - (n : ℤ)) • g i

private noncomputable def sumBox (g : ι → G) (n : ℕ) : Finset G :=
  by
    classical
    exact Finset.univ.image (evalBox g n)

private theorem zero_mem_sumBox (g : ι → G) (n : ℕ) : 0 ∈ sumBox g n := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨fun _ ↦ ⟨n, by omega⟩, Finset.mem_univ _, ?_⟩
  simp [evalBox]

private theorem sumBox_card (g : ι → G) (n : ℕ) :
    (sumBox g n).card ≤ (2 * n + 1) ^ Fintype.card ι := by
  classical
  exact Finset.card_image_le.trans_eq (by simp)

private theorem sumBox_translate (g : ι → G) (n : ℕ) (d : ι → ℤ)
    (hd : ∀ i, -1 ≤ d i ∧ d i ≤ 1) {x : G} (hx : x ∈ sumBox g n) :
    (∑ i, d i • g i) + x ∈ sumBox g (n + 1) := by
  classical
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
  let b (i : ι) : Fin (2 * (n + 1) + 1) :=
    ⟨(((a i : ℕ) : ℤ) + 1 + d i).toNat, by
      have ha := (a i).isLt
      have hdi := hd i
      omega⟩
  apply Finset.mem_image.mpr
  refine ⟨b, Finset.mem_univ _, ?_⟩
  unfold evalBox
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← add_zsmul]
  congr 1
  have hdi := hd i
  change (((((a i : ℕ) : ℤ) + 1 + d i).toNat : ℕ) : ℤ) - ((n + 1 : ℕ) : ℤ)
    = d i + (((a i : ℕ) : ℤ) - (n : ℤ))
  omega

theorem exists_finite_sum_boxes (g : ι → G) (ε : ℝ) (hε : 0 < ε) :
    ∃ A B : Finset G, A.Nonempty ∧ ((B.card : ℝ) < (1 + ε) * (A.card : ℝ)) ∧
      ∀ (d : ι → ℤ), (∀ i, -1 ≤ d i ∧ d i ≤ 1) →
        ∀ x ∈ A, (∑ i, d i • g i) + x ∈ B := by
  classical
  suffices h : ∃ n, ((sumBox g (n + 1)).card : ℝ) < (1 + ε) * (sumBox g n).card by
    obtain ⟨n, hn⟩ := h
    exact ⟨sumBox g n, sumBox g (n + 1), ⟨0, zero_mem_sumBox g n⟩, hn,
      fun d hd _ hx ↦ sumBox_translate g n d hd hx⟩
  by_contra! h
  have hLower (n : ℕ) : (1 + ε) ^ n ≤ ((sumBox g n).card : ℝ) := by
    induction n with
    | zero =>
      simp only [pow_zero]
      exact_mod_cast Finset.card_pos.mpr (show (sumBox g 0).Nonempty from
        ⟨0, zero_mem_sumBox g 0⟩)
    | succ n ih =>
      rw [pow_succ']
      exact (mul_le_mul_of_nonneg_left ih (by positivity)).trans (h n)
  let k := Fintype.card ι
  have hlim := tendsto_pow_const_div_const_pow_of_one_lt k (by linarith : 1 < 1 + ε)
  have hlt : ∀ᶠ n : ℕ in atTop,
      (3 : ℝ)^k * ((n : ℝ)^k / (1 + ε)^n) < 1 := by
    apply (tendsto_const_nhds.mul hlim).eventually_lt tendsto_const_nhds
    simp
  obtain ⟨n, hn, hne⟩ := ((eventually_ge_atTop (1 : ℕ)).and hlt).exists
  have hpoly : ((sumBox g n).card : ℝ) ≤ (3 : ℝ)^k * (n : ℝ)^k := by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    calc
      ((sumBox g n).card : ℝ) ≤ ((2 * (n : ℝ) + 1) ^ k) := by
        exact_mod_cast sumBox_card g n
      _ ≤ (3 * (n : ℝ)) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) _
      _ = _ := mul_pow _ _ _
  rw [← mul_div_assoc, div_lt_iff₀ (pow_pos (by positivity) _), one_mul] at hne
  exact (not_lt_of_ge ((hLower n).trans hpoly)) hne

end FiniteSums

end OMA.Erdos1070

namespace OMA.Erdos1070

open BigOperators ComplexConjugate

private def oriented (r : Additive Circle × Bool) (z : ℂ) : ℂ :=
  (r.1.toMul : ℂ) * (if r.2 then conj z else z)

private noncomputable def composeOrientation (s r : Additive Circle × Bool) : Additive Circle × Bool :=
  (r.1 + (if r.2 then -s.1 else s.1), r.2 ^^ s.2)

private theorem oriented_add (r : Additive Circle × Bool) (b z : ℂ) :
    oriented r (z + b) = oriented r z + oriented r b := by
  cases r with
  | mk r f =>
    cases f <;> simp [oriented, mul_add]

private theorem oriented_dist (r : Additive Circle × Bool) (x y : ℂ) :
    dist (oriented r x) (oriented r y) = dist x y := by
  cases r with
  | mk r f =>
    cases f <;> simp [oriented, dist_eq_norm, ← mul_sub, ← map_sub, Circle.norm_coe]

private theorem oriented_compose (s r : Additive Circle × Bool) (z : ℂ) :
    oriented (composeOrientation s r) z = oriented r (oriented s z) := by
  rcases r with ⟨r, fr⟩
  rcases s with ⟨s, fs⟩
  have hc : ((s.toMul : ℂ)⁻¹) = conj (s.toMul : ℂ) := by
    rw [← Circle.coe_inv]
    exact Circle.coe_inv_eq_conj _
  cases fr <;> cases fs <;>
    simp [oriented, composeOrientation, mul_assoc, hc]

private theorem composeOrientation_inj (s : Additive Circle × Bool) :
    Function.Injective (composeOrientation s) := by
  rintro ⟨a, fa⟩ ⟨b, fb⟩ h
  have h₂ := congrArg Prod.snd h
  have hbool : fa = fb := by
    change (fa ^^ s.2) = (fb ^^ s.2) at h₂
    cases fs : s.2 <;> simpa [fs] using h₂
  subst fb
  have h₁ := congrArg Prod.fst h
  change a + (if fa then -s.1 else s.1) = b + (if fa then -s.1 else s.1) at h₁
  exact congrArg (fun v ↦ (v, fa)) (add_right_cancel h₁)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private noncomputable def shifts (B : Finset ℂ) (v : ι → ℂ) (S : Finset ι) : Finset ℂ := by
  classical
  exact if h : S.Nonempty then
    (B.image fun z ↦ z - v h.choose).filter fun t ↦ ∀ i ∈ S, v i + t ∈ B
    else ∅

private theorem mem_shifts {B : Finset ℂ} {v : ι → ℂ} {S : Finset ι} (hS : S.Nonempty) (t : ℂ) :
    t ∈ shifts B v S ↔ ∀ i ∈ S, v i + t ∈ B := by
  classical
  rw [shifts, dif_pos hS, Finset.mem_filter]
  refine ⟨And.right, fun h ↦ ⟨?_, h⟩⟩
  exact Finset.mem_image.mpr ⟨v hS.choose + t, h _ hS.choose_spec, by abel⟩

private theorem card_shifts_le {B : Finset ℂ} {v : ι → ℂ} {S : Finset ι} :
    (shifts B v S).card ≤ B.card := by
  classical
  by_cases hS : S.Nonempty
  · rw [shifts, dif_pos hS]
    exact (Finset.card_filter_le _ _).trans Finset.card_image_le
  · simp [shifts, hS]

private theorem card_shifts_singleton (B : Finset ℂ) (v : ι → ℂ) (i : ι) :
    (shifts B v {i}).card = B.card := by
  classical
  have h : shifts B v {i} = B.image (fun b ↦ b - v i) := by
    ext t
    rw [mem_shifts (Finset.singleton_nonempty i), Finset.mem_image]
    simp only [Finset.mem_singleton, forall_eq]
    exact ⟨fun h ↦ ⟨v i + t, h, by abel⟩, by
      rintro ⟨b, hb, rfl⟩
      rwa [add_comm, sub_add_cancel]⟩
  rw [h, Finset.card_image_of_injective]
  exact sub_left_injective

private theorem card_shifts_congr {B : Finset ℂ} {u v : ι → ℂ}
    {S R : Finset ι} (hS : S.Nonempty) (hR : R.Nonempty) (c : ℂ)
    (h : S.image (fun i ↦ u i + c) = R.image v) :
    (shifts B u S).card = (shifts B v R).card := by
  classical
  have hs : (shifts B u S).image (fun t ↦ t - c) = shifts B v R := by
    ext t
    rw [mem_shifts hR, Finset.mem_image]
    refine ⟨?_, ?_⟩
    · rintro ⟨x, hx, rfl⟩ j hj
      have hmem : v j ∈ S.image (fun i ↦ u i + c) :=
        h.symm ▸ Finset.mem_image_of_mem v hj
      obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hmem
      rw [← he, show u i + c + (x - c) = u i + x by abel]
      exact (mem_shifts hS x).mp hx i hi
    · intro ht
      refine ⟨t + c, (mem_shifts hS _).mpr ?_, add_sub_cancel_right _ _⟩
      intro i hi
      have hmem : u i + c ∈ R.image v :=
        h ▸ Finset.mem_image_of_mem (fun i ↦ u i + c) hi
      obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hmem
      rw [show u i + (t + c) = u i + c + t by abel, ← he]
      exact ht j hj
  rw [← hs, Finset.card_image_of_injective]
  exact sub_left_injective


private theorem exists_orientation_boxes (o : ι → Additive Circle × Bool) (ε : ℝ) (hε : 0 < ε) :
    ∃ F L : Finset (Additive Circle × Bool), F.Nonempty ∧ F ⊆ L ∧
      (L.card : ℝ) < (1 + ε) * (F.card : ℝ) ∧
      ∀ i r, r ∈ F → composeOrientation (o i) r ∈ L := by
  classical
  obtain ⟨A, B, hA, hcard, hMove⟩ := exists_finite_sum_boxes (fun i ↦ (o i).1) ε hε
  have hSub : A ⊆ B := by
    intro a ha
    simpa using hMove (fun _ ↦ 0) (fun _ ↦ by norm_num) a ha
  let F := A ×ˢ (Finset.univ : Finset Bool)
  let L := B ×ˢ (Finset.univ : Finset Bool)
  refine ⟨F, L, hA.product Finset.univ_nonempty, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨h, hf⟩ := Finset.mem_product.mp hx
    exact Finset.mem_product.mpr ⟨hSub h, hf⟩
  · dsimp [F, L]
    simp only [Finset.card_product, Nat.cast_mul, ← mul_assoc]
    exact mul_lt_mul_of_pos_right hcard (by norm_num)
  · intro i r hr
    let d j : ℤ := if j = i then (if r.2 then -1 else 1) else 0
    have hd : ∀ j, -1 ≤ d j ∧ d j ≤ 1 := by
      intro j
      by_cases hij : j = i <;> cases hbool : r.2 <;> simp [d, hij, hbool]
    have hsum : ∑ j, d j • (o j).1 = if r.2 then -(o i).1 else (o i).1 := by
      cases hbool : r.2 <;> simp [d, hbool, ite_smul]
    have h := hMove d hd r.1 (Finset.mem_product.mp hr).1
    rw [hsum, add_comm] at h
    exact Finset.mem_product.mpr ⟨h, Finset.mem_univ _⟩

private theorem exists_translation_boxes (g : ι → ℂ) (ε : ℝ) (hε : 0 < ε) :
    ∃ X T : Finset ℂ, X.Nonempty ∧ X ⊆ T ∧ (T.card : ℝ) < (1 + ε) * (X.card : ℝ)
      ∧ ∀ i x, x ∈ X → x - g i ∈ T := by
  classical
  obtain ⟨X, T, hX, hcard, hMove⟩ := exists_finite_sum_boxes g ε hε
  have hSub : X ⊆ T := by
    intro x hx
    simpa using hMove (fun _ ↦ 0) (fun _ ↦ by norm_num) x hx
  refine ⟨X, T, hX, hSub, hcard, ?_⟩
  intro i x hx
  let d j : ℤ := if j = i then -1 else 0
  have hd : ∀ j, -1 ≤ d j ∧ d j ≤ 1 := by
    intro j
    by_cases hji : j = i <;> simp [d, hji]
  have hsum : ∑ j, d j • g j = -g i := by simp [d, ite_smul]
  have h := hMove d hd x hx
  rwa [hsum, add_comm, ← sub_eq_add_neg] at h

private theorem sum_shift_error {α : Type*} [DecidableEq α]
    {F L : Finset α} (hF : F ⊆ L) {f : α → ℝ} {M : ℝ}
    (hValues : ∀ x ∈ L, 0 ≤ f x ∧ f x ≤ M) (e : α ↪ α) (he : F.map e ⊆ L) :
    |(∑ x ∈ F, f (e x)) - ∑ x ∈ F, f x| ≤ ((L.card : ℝ) - F.card) * M := by
  have rest (A : Finset α) (hA : A ⊆ L) :
      0 ≤ ∑ x ∈ L \ A, f x ∧
        (∑ x ∈ L \ A, f x) ≤ ((L.card : ℝ) - A.card) * M := by
    have hsubset : L \ A ⊆ L := Finset.sdiff_subset
    have hCount : ((L \ A).card : ℝ) = (L.card : ℝ) - A.card := by
      rw [Finset.card_sdiff_of_subset hA, Nat.cast_sub (Finset.card_le_card hA)]
    refine ⟨Finset.sum_nonneg (fun x hx ↦ (hValues x (hsubset hx)).1), ?_⟩
    calc
      (∑ x ∈ L \ A, f x) ≤ ∑ x ∈ L \ A, M :=
        Finset.sum_le_sum fun x hx ↦ (hValues x (hsubset hx)).2
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hCount]
  have h₁ := Finset.sum_sdiff hF (f := f)
  have h₂ := Finset.sum_sdiff he (f := f)
  have hb₁ := rest F hF
  have hb₂ := rest (F.map e) he
  rw [Finset.sum_map] at h₂
  rw [Finset.card_map] at hb₂
  exact abs_le.mpr ⟨by linarith [hb₁.1, hb₂.2], by linarith [hb₂.1, hb₁.2]⟩


theorem exists_complex_moments (p : ι → ℂ)
    (C : List (ℤ × Finset ι × Finset ι)) (i₀ : ι)
    (hCongruent : ∀ r ∈ C, ∃ a b : ℂ, ‖a‖ = 1 ∧
      (r.2.1.image (fun i ↦ a * p i + b) = r.2.2.image p ∨
        r.2.1.image (fun i ↦ a * conj (p i) + b) = r.2.2.image p))
    (hLarge : ∀ X : Finset ℂ, ∃ B ⊆ X, (X.card : ℝ) / 4 ≤ B.card ∧
      ∀ x ∈ B, ∀ y ∈ B, dist x y ≠ 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ μ : Finset ι → ℝ,
      (∀ I, 0 ≤ μ I) ∧ (∑ I, μ I) = 1 ∧
      (∀ I, ¬ (∀ i ∈ I, ∀ j ∈ I, dist (p i) (p j) ≠ 1) → μ I = 0) ∧
      let moment := fun S : Finset ι ↦ ∑ I, if S ⊆ I then μ I else 0
      1 / 4 - ε ≤ moment {i₀} ∧ ∀ r ∈ C, |moment r.2.1 - moment r.2.2| ≤ ε := by
  classical
  let CSet := C.toFinset
  have hMaps (r : CSet) : ∃ (o : Additive Circle × Bool) (b : ℂ),
      r.val.2.1.image (fun i ↦ oriented o (p i) + b) = r.val.2.2.image p := by
    obtain ⟨a, b, ha, hb⟩ := hCongruent r.val (List.mem_toFinset.mp r.property)
    let v : Circle := ⟨a, mem_sphere_zero_iff_norm.mpr ha⟩
    rcases hb with h | h
    · exact ⟨(Additive.ofMul v, false), b, h⟩
    · exact ⟨(Additive.ofMul v, true), b, h⟩
  choose o b hb using hMaps
  obtain ⟨F, L, hF, hFL, hFLCard, hFMove⟩ := exists_orientation_boxes o ε hε
  let g (i : F × ι) := oriented (i.1 : Additive Circle × Bool) (p i.2)
  obtain ⟨X, T, hX, hXT, hXTCard, hTMove⟩ := exists_translation_boxes g ε hε
  obtain ⟨B, hBX, hBCard, hB⟩ := hLarge X
  let P := F ×ˢ T
  let atom (z : (Additive Circle × Bool) × ℂ) : Finset ι :=
    Finset.univ.filter fun i ↦ oriented z.1 (p i) + z.2 ∈ B
  let μ (I : Finset ι) : ℝ := ((P.filter fun z ↦ atom z = I).card : ℝ) / P.card
  let moment (S : Finset ι) : ℝ := ∑ I, if S ⊆ I then μ I else 0
  have hFPos : 0 < (F.card : ℝ) := by exact_mod_cast hF.card_pos
  have hTPos : 0 < (T.card : ℝ) := by exact_mod_cast (hX.mono hXT).card_pos
  have hPPos : 0 < (P.card : ℝ) := by
    dsimp [P]
    rw [Finset.card_product, Nat.cast_mul]
    exact mul_pos hFPos hTPos
  have hMoment (S : Finset ι) :
      moment S = ((P.filter fun z ↦ S ⊆ atom z).card : ℝ) / P.card := by
    have hc := Finset.sum_card_fiberwise_eq_card_filter P
      (Finset.univ.filter fun I : Finset ι ↦ S ⊆ I) atom
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.sum_filter] at hc
    have hI (I : Finset ι) :
        (if S ⊆ I then ((P.filter fun z ↦ atom z = I).card : ℝ) / P.card else 0) =
          (if S ⊆ I then ((P.filter fun z ↦ atom z = I).card : ℝ) else 0) / P.card := by
      split_ifs <;> simp
    unfold moment μ
    simp_rw [hI]
    rw [← Finset.sum_div]
    congr 1
    exact_mod_cast hc
  have hMomentShifts (S : Finset ι) (hS : S.Nonempty) :
      moment S = (∑ r ∈ F, ((shifts B (fun i ↦ oriented r (p i)) S).card : ℝ)) / P.card := by
    rw [hMoment, Finset.card_filter, Nat.cast_sum]
    dsimp only [P]
    rw [Finset.sum_product]
    congr 1
    apply Finset.sum_congr rfl
    intro r hr
    have hEq : (T.filter fun t ↦ S ⊆ atom (r,t)) =
        shifts B (fun i ↦ oriented r (p i)) S := by
      ext t
      rw [Finset.mem_filter, mem_shifts hS]
      constructor
      · intro ht i hi
        exact (Finset.mem_filter.mp (ht.2 hi)).2
      · intro ht
        have hXt := hBX (ht hS.choose hS.choose_spec)
        have hMove := hTMove (⟨r, hr⟩, hS.choose) (oriented r (p hS.choose) + t) hXt
        have htT : t ∈ T := by
          convert hMove using 1
          dsimp [g]
          abel
        exact ⟨htT, fun i hi ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht i hi⟩⟩
    rw [← hEq, Finset.card_filter, Nat.cast_sum]
  refine ⟨μ, fun I ↦ div_nonneg (Nat.cast_nonneg _) hPPos.le, ?_, ?_, ?_, ?_⟩
  · rw [show (∑ I, μ I) = moment ∅ by simp [moment], hMoment]
    simp [hPPos.ne']
  · intro I hI
    have he : (P.filter fun z ↦ atom z = I) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro z hz
      obtain ⟨_, hEq⟩ := Finset.mem_filter.mp hz
      apply hI
      subst I
      intro i hi j hj hij
      have hi' := (Finset.mem_filter.mp hi).2
      have hj' := (Finset.mem_filter.mp hj).2
      apply hB _ hi' _ hj'
      rwa [dist_add_right, oriented_dist]
    simp [μ, he]
  · change 1 / 4 - ε ≤ moment {i₀}
    rw [hMomentShifts _ (Finset.singleton_nonempty _)]
    simp only [card_shifts_singleton, Finset.sum_const, nsmul_eq_mul]
    dsimp only [P]
    rw [Finset.card_product, Nat.cast_mul, mul_div_mul_left _ _ hFPos.ne']
    have hXLe : (X.card : ℝ) ≤ T.card := by exact_mod_cast Finset.card_le_card hXT
    have hXError : (T.card : ℝ) - X.card ≤ ε * T.card := by
      exact (show (T.card : ℝ) - X.card ≤ ε * X.card by linarith [hXTCard]).trans
        (mul_le_mul_of_nonneg_left hXLe hε.le)
    apply (le_div_iff₀ hTPos).mpr
    linarith [hXError, mul_nonneg hε.le hTPos.le]
  · intro r hr
    change |moment r.2.1 - moment r.2.2| ≤ ε
    let c : CSet := ⟨r, List.mem_toFinset.mpr hr⟩
    have hEq := hb c
    change r.2.1.image (fun i ↦ oriented (o c) (p i) + b c) = r.2.2.image p at hEq
    by_cases hLeft : r.2.1.Nonempty
    · have hRight : r.2.2.Nonempty := Finset.image_nonempty.mp
        (hEq ▸ hLeft.image _)
      let e : (Additive Circle × Bool) ↪ (Additive Circle × Bool) :=
        ⟨composeOrientation (o c), composeOrientation_inj _⟩
      have hMap : F.map e ⊆ L := by
        intro a h
        obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp h
        exact hFMove c z hz
      let f (z : Additive Circle × Bool) :=
        ((shifts B (fun i ↦ oriented z (p i)) r.2.1).card : ℝ)
      have hReindex (z : Additive Circle × Bool) :
          f (e z) = ((shifts B (fun i ↦ oriented z (p i)) r.2.2).card : ℝ) := by
        dsimp [f, e]
        exact_mod_cast card_shifts_congr hLeft hRight (oriented z (b c)) (by
          have he := congrArg (Finset.image (oriented z)) hEq
          simpa only [Finset.image_image, Function.comp_def, oriented_add, oriented_compose] using he)
      have hValues (z) (_ : z ∈ L) : 0 ≤ f z ∧ f z ≤ (B.card : ℝ) := by
        refine ⟨Nat.cast_nonneg _, ?_⟩
        dsimp [f]
        exact_mod_cast card_shifts_le
      have herror := sum_shift_error hFL hValues e hMap
      rw [hMomentShifts _ hLeft, hMomentShifts _ hRight, abs_sub_comm,
        ← sub_div, abs_div, abs_of_pos hPPos]
      simp only [hReindex] at herror
      apply (div_le_iff₀ hPPos).mpr
      refine herror.trans ?_
      have hBT : (B.card : ℝ) ≤ T.card := by exact_mod_cast Finset.card_le_card (hBX.trans hXT)
      calc
        ((L.card : ℝ) - F.card) * (B.card : ℝ) ≤ (ε * F.card) * (B.card : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith [hFLCard]) (Nat.cast_nonneg _)
        _ ≤ (ε * F.card) * (T.card : ℝ) :=
          mul_le_mul_of_nonneg_left hBT (mul_nonneg hε.le hFPos.le)
        _ = ε * (P.card : ℝ) := by
          rw [show P.card = F.card * T.card by exact Finset.card_product _ _, Nat.cast_mul]
          ring
    · have hn : r.2.1 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hLeft
      rw [hn, Finset.image_empty, eq_comm, Finset.image_eq_empty] at hEq
      rw [hn, hEq, sub_self, abs_zero]
      exact hε.le

end OMA.Erdos1070

private theorem averaging : OMA.R_Erdos1070_erdos_1070_parts_ii_R1.H2 := by
  intro p C hCongruent hLarge ε hε
  exact OMA.Erdos1070.exists_complex_moments p C 0 hCongruent hLarge ε hε

/-!
The integer dual certificate and exact 29-vertex construction of Ágoston Dúcz
and Dániel Varga (arXiv:2606.28157). The source and image masks, coefficients,
and chosen motions encode the paper's public supplementary data.

The kernel checks the exact distances and congruences in a nested quadratic
extension, the signed arithmetic on independent masks, and the coverage of
the branches of a vertex split.
-/

/- Arithmetic of radix-encoded nonnegative mask coefficients. -/

namespace UnitDistancePacked

abbrev Weights := List (ℕ × ℕ)

def encode (base : ℕ) (t : Weights) : ℕ :=
  (t.map (fun r => r.2 * base^r.1)).sum

def mass (t : Weights) : ℕ := (t.map Prod.snd).sum

def low (split : ℕ) (t : Weights) : Weights :=
  t.filter (fun r => r.1 < split)

def high (split : ℕ) (t : Weights) : Weights :=
  t.filterMap (fun r => if split ≤ r.1 then some (r.1 - split, r.2) else none)

theorem encode_append (base : ℕ) (t u : Weights) :
    encode base (t ++ u) = encode base t + encode base u := by
  simp [encode]

theorem mass_partition (h : ℕ) (t : Weights) :
    mass (low h t) + mass (high h t) = mass t := by
  induction t with
  | nil => rfl
  | cons r t ih =>
    by_cases hr : r.1 < h
    · have hneg : ¬h ≤ r.1 := by omega
      simp [low, high, hr, hneg, mass] at ih ⊢
      omega
    · have hpos : h ≤ r.1 := by omega
      simp [low, high, hr, hpos, mass] at ih ⊢
      omega

theorem encode_partition (base h : ℕ) (t : Weights) :
    encode base t = encode base (low h t) + base^h * encode base (high h t) := by
  induction t with
  | nil => simp [encode, low, high]
  | cons r t ih =>
    by_cases hr : r.1 < h
    · have hneg : ¬h ≤ r.1 := by omega
      simp [low, high, hr, hneg, encode] at ih ⊢
      omega
    · have hpos : h ≤ r.1 := by omega
      have hf : base^r.1 = base^h * base^(r.1 - h) := by
        rw [← pow_add, Nat.add_sub_of_le hpos]
      simp [low, high, hr, hpos, encode, hf, Nat.mul_add] at ih ⊢
      rw [ih]
      ring

private theorem encode_le_mul (base k : ℕ) (hb : 0 < base) (t : Weights)
    (ht : ∀ r ∈ t, r.1 ≤ k) : encode base t ≤ mass t * base^k := by
  induction t with
  | nil => simp [encode, mass]
  | cons r t ih =>
    simp only [encode, mass, List.map_cons, List.sum_cons, Nat.add_mul]
    apply Nat.add_le_add
    · exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hb (ht r List.mem_cons_self))
    · exact ih (fun x hx => ht x (List.mem_cons_of_mem _ hx))

private theorem encode_low_lt {base : ℕ} (hb : 0 < base) (h : ℕ) (t : Weights)
    (ht : mass t < base) : encode base (low h t) < base^h := by
  cases h with
  | zero => simp [low, encode]
  | succ k =>
    have hm : mass (low (k+1) t) < base := by
      have hp := mass_partition (k+1) t
      omega
    have hw := encode_le_mul base k hb (low (k+1) t) fun r hr => by
      have hh := (List.mem_filter.1 hr).2
      have hlt : r.1 < k+1 := of_decide_eq_true hh
      omega
    apply hw.trans_lt
    rw [pow_succ, Nat.mul_comm (base^k) base]
    exact Nat.mul_lt_mul_of_pos_right hm (Nat.pow_pos hb)

theorem encode_low_eq_mod {base : ℕ} (hb : 0 < base) (h : ℕ) (t : Weights)
    (ht : mass t < base) : encode base t % base^h = encode base (low h t) := by
  rw [encode_partition base h t, Nat.add_comm, Nat.mul_add_mod_self_left]
  exact Nat.mod_eq_of_lt (encode_low_lt hb h t ht)

theorem encode_high_eq_div {base : ℕ} (hb : 0 < base) (h : ℕ) (t : Weights)
    (ht : mass t < base) : encode base t / base^h = encode base (high h t) := by
  rw [encode_partition base h t, Nat.add_mul_div_left _ _ (Nat.pow_pos hb),
    Nat.div_eq_of_lt (encode_low_lt hb h t ht), Nat.zero_add]

theorem encode_mod_mass {base : ℕ} (hb : 1 < base - 1) (t : Weights)
    (ht : mass t < base - 1) : encode base t % (base-1) = mass t := by
  have hbase : base ≡ 1 [MOD base-1] := by
    change base % (base - 1) = 1 % (base - 1)
    calc
      _ = ((base-1) + 1) % (base-1) := by congr 1; omega
      _ = _ := Nat.add_mod_left _ _
  have hmod (u : Weights) : encode base u ≡ mass u [MOD base-1] := by
    induction u with
    | nil => rfl
    | cons r u ih =>
      simp only [encode, mass, List.map_cons, List.sum_cons]
      simpa only [encode, mass, one_pow, Nat.mul_one] using ((Nat.ModEq.refl r.2).mul (hbase.pow r.1)).add ih
  exact (show encode base t % (base-1) = mass t % (base-1) from hmod t).trans
    (Nat.mod_eq_of_lt ht)

private theorem encode_low_one (base : ℕ) (t : Weights) :
    encode base (low 1 t) = mass (low 1 t) := by
  unfold encode mass
  apply congrArg List.sum
  apply List.map_congr_left
  intro r hr
  have hlt : r.1 < 1 := of_decide_eq_true (List.mem_filter.1 hr).2
  simp [Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hlt)]

theorem encode_mod_zero {base : ℕ} (hb : 0 < base) (t : Weights)
    (ht : mass t < base) : encode base t % base = mass (low 1 t) := by
  have h := encode_low_eq_mod hb 1 t ht
  simpa only [pow_one, encode_low_one] using h

end UnitDistancePacked



namespace UnitDistancePacked

def lane (base word i : ℕ) : ℕ := (word / base^i) % base

def massAt (i : ℕ) (t : Weights) : ℕ := mass (t.filter (fun r => r.1 = i))

private theorem mass_at_eq (t : Weights) (i : ℕ) :
    mass (low 1 (high i t)) = massAt i t := by
  induction t with
  | nil => rfl
  | cons r t ih =>
    by_cases h : i ≤ r.1
    · have he : r.1 - i < 1 ↔ r.1 = i := by omega
      by_cases hr : r.1 = i
      · simpa [high, low, massAt, mass, h, hr] using congrArg (r.2 + ·) ih
      · have hz : r.1 - i ≠ 0 := by omega
        simpa [high, low, massAt, mass, h, he, hr, hz] using ih
    · have hh : r.1 ≠ i := by omega
      simpa [high, low, massAt, mass, h, hh] using ih

theorem lane_encode {base : ℕ} (hb : 0 < base) (t : Weights) (ht : mass t < base) (i : ℕ) :
    lane base (encode base t) i = massAt i t := by
  unfold lane
  rw [encode_high_eq_div hb i t ht, encode_mod_zero hb (high i t), mass_at_eq]
  have hm := mass_partition i t
  omega

theorem testBit_lane {width : ℕ} (hw : 0 < width) (word i : ℕ) :
    word.testBit i = (lane (2^width) word (i/width)).testBit (i%width) := by
  unfold lane
  rw [← pow_mul, ← Nat.shiftRight_eq_div_pow, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftRight]
  have hm : decide (i % width < width) = true := decide_eq_true (Nat.mod_lt i hw)
  rw [hm]
  simp only [Bool.true_and]
  rw [Nat.div_add_mod]

theorem testBit_encode {width : ℕ} (hw : 0 < width) (t : Weights) (ht : mass t < 2^width) (i : ℕ) :
    (encode (2^width) t).testBit i = (massAt (i/width) t).testBit (i%width) := by
  rw [testBit_lane hw, lane_encode (Nat.two_pow_pos _) t ht]

private theorem mass_filter_le (t : Weights) (p : ℕ × ℕ → Bool) :
    mass (t.filter p) ≤ mass t := by
  induction t with
  | nil => rfl
  | cons r t ih =>
    cases e : p r <;>
      simp [mass, e] at ih ⊢ <;> omega

private theorem massAt_filter (t : Weights) (p : ℕ → Bool) (i : ℕ) :
    massAt i (t.filter (fun r => p r.1)) = if p i then massAt i t else 0 := by
  unfold massAt
  rw [List.filter_filter]
  by_cases hi : p i
  · have h : t.filter (fun x => decide (x.1 = i) && p x.1) = t.filter (fun x => decide (x.1 = i)) := by
      apply List.filter_congr
      intro r _
      by_cases hr : r.1 = i <;> simp [hr, hi]
    rw [h, if_pos hi]
  · have h : t.filter (fun x => decide (x.1 = i) && p x.1) = [] := by
      apply List.filter_eq_nil_iff.2
      intro r _
      by_cases hr : r.1 = i <;> simp [hr, hi]
    rw [h, if_neg hi]
    rfl

theorem encode_filter_by_mask {width : ℕ} (hw : 0 < width)
    (t : Weights) (ht : mass t < 2^width) (predicate : ℕ → Bool) (mask : ℕ)
    (hmask : ∀ i, mask.testBit i = predicate (i/width)) :
    encode (2^width) t &&& mask = encode (2^width) (t.filter fun r => predicate r.1) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_land, hmask, testBit_encode hw t ht,
    testBit_encode hw _ ((mass_filter_le _ _).trans_lt ht), massAt_filter]
  by_cases h : predicate (i/width) <;> simp [h]

end UnitDistancePacked


namespace UnitDistancePacked

private def repeatWord (word period : ℕ) : ℕ → ℕ
  | 0 => word
  | h+1 =>
    let a := repeatWord word period h
    a ||| (a <<< (period * 2^h))

private def lowStripes (width n j : ℕ) : ℕ :=
  let block := width * 2^j
  repeatWord (2^block-1) (2*block) (n-(j+1))

private def zetaWord (width n : ℕ) (a : ℕ) : ℕ :=
  (List.range n).foldl (fun w j =>
    w + ((w &&& lowStripes width n j) <<< (width * 2^j))) a

private def auditGuards (width : ℕ) (rows : List ℕ) (allowed : ℕ) : ℕ × ℕ :=
  let n := rows.length
  let guards := repeatWord (2^(width-1)) width n
  let mask := (List.range n).foldl (fun acc i =>
    let stripe := lowStripes width n i
    if allowed.testBit i then
      let row := rows[i]?.getD 0
      (List.range i).foldl (fun curr j =>
        if row.testBit j then curr &&& (stripe ||| lowStripes width n j) else curr) acc
    else acc &&& stripe) guards
  (guards, mask)

end UnitDistancePacked

namespace UnitDistancePacked

private theorem repeatWord_bits {word period : ℕ} (hword : word < 2^period)
    (depth i : ℕ) :
    (repeatWord word period depth).testBit i =
      (decide (i < period * 2^depth) && word.testBit (i % period)) := by
  induction depth generalizing i with
  | zero =>
    simp only [repeatWord, pow_zero, Nat.mul_one]
    by_cases hi : i < period
    · simp [hi, Nat.mod_eq_of_lt hi]
    · have hbound : word < 2^i := hword.trans_le
        (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_not_gt hi))
      simp [hi, Nat.testBit_lt_two_pow hbound]
  | succ depth ih =>
    simp only [repeatWord, Nat.testBit_or, Nat.testBit_shiftLeft, ih]
    let cut := period * 2^depth
    have hsize : period * 2^(depth+1) = 2 * cut := by
      dsimp [cut]
      rw [pow_succ]
      ring
    change (decide (i < cut) && word.testBit (i % period) ||
        (decide (cut ≤ i) &&
          (decide (i-cut < cut) && word.testBit ((i-cut) % period)))) =
      (decide (i < period * 2^(depth+1)) && word.testBit (i % period))
    rw [hsize]
    by_cases hi : i < cut
    · have hlt : i < 2*cut := by omega
      simp [hi, hlt, Nat.not_le_of_lt hi]
    · have hl := Nat.le_of_not_gt hi
      have htail : i - cut < cut ↔ i < 2 * cut := by omega
      have hmod : (i-cut)%period = i%period := by
        conv_rhs => rw [show i = i-cut + period * 2^depth from (Nat.sub_add_cancel hl).symm]
        exact (Nat.add_mul_mod_self_left _ _ _).symm
      simp [hi, hl, htail, hmod]

theorem lowStripes_bits {width n j : ℕ} (hw : 0 < width) (hj : j < n) (i : ℕ) :
    (lowStripes width n j).testBit i = (decide (i/width < 2^n) && !(i/width).testBit j) := by
  let block := width * 2^j
  have hb : 0 < block := Nat.mul_pos hw (Nat.two_pow_pos _)
  have hword : 2^block-1 < 2^(2*block) := by
    have hpow : 2^block ≤ 2^(2*block) := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
    have hlt := Nat.two_pow_pos block
    omega
  change (repeatWord (2^block-1) (2*block) (n-(j+1))).testBit i = _
  rw [repeatWord_bits hword, Nat.testBit_two_pow_sub_one]
  have hlen : (2 * block) * 2^(n - (j+1)) = width * 2^n := by
    calc
      _ = width * (2^(j+1) * 2^(n-(j+1))) := by
        rw [pow_succ]
        dsimp [block]
        ring
      _ = _ := by rw [← pow_add, Nat.add_sub_of_le (Nat.succ_le_of_lt hj)]
  have hsize : i < width * 2^n ↔ i/width < 2^n := by
    rw [Nat.div_lt_iff_lt_mul hw, Nat.mul_comm width (2^n)]
  have hb' : i % (2*block) < block ↔ i / block % 2 = 0 := by
    have he : (i % (2*block)) / block < 1 ↔ i % (2*block) < block := by
      simpa only [Nat.one_mul] using (Nat.div_lt_iff_lt_mul hb (x := i % (2*block)) (y := 1))
    rw [← he, Nat.mod_mul_left_div_self]
    exact Nat.lt_one_iff
  rw [hlen, Nat.testBit_eq_decide_div_mod_eq, Nat.div_div_eq_div_mul]
  change (decide (i < width * 2^n) && decide (i % (2*block) < block)) =
    (decide (i / width < 2^n) && !decide (i / block % 2 = 1))
  rcases Nat.mod_two_eq_zero_or_one (i / block) with h | h <;> simp [hsize, hb', h]

end UnitDistancePacked


namespace UnitDistancePacked

private def zetaTerms (j : ℕ) (t : Weights) : Weights :=
  t ++ (t.filter fun r => !r.1.testBit j).map (fun r => (r.1 + 2^j, r.2))

private theorem encode_shift (width h : ℕ) (t : Weights) :
    encode (2^width) (t.map fun r => (r.1 + h, r.2)) =
      encode (2^width) t <<< (width * h) := by
  rw [Nat.shiftLeft_eq, pow_mul]
  induction t with
  | nil => simp [encode]
  | cons r t ih =>
    simp only [encode, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, pow_add]
    ring

private theorem stripe_filter (width n j : ℕ) (hw : 0 < width) (hj : j < n)
    (t : Weights) (hbound : ∀ r ∈ t, r.1 < 2^n) (ht : mass t < 2^width) :
    encode (2^width) t &&& lowStripes width n j =
      encode (2^width) (t.filter fun r => !r.1.testBit j) := by
  rw [encode_filter_by_mask hw t ht (fun k => decide (k < 2^n) && !k.testBit j)
    (lowStripes width n j) (lowStripes_bits hw hj)]
  congr 1
  apply List.filter_congr
  intro r hr
  simp [hbound r hr]

private theorem encode_zeta_step (width n j : ℕ) (hw : 0 < width) (hj : j < n)
    (t : Weights) (hbound : ∀ r ∈ t, r.1 < 2^n) (ht : mass t < 2^width) :
    encode (2^width) (zetaTerms j t) =
      encode (2^width) t + ((encode (2^width) t &&& lowStripes width n j) <<< (width * 2^j)) := by
  rw [zetaTerms, encode_append, encode_shift, stripe_filter width n j hw hj t hbound ht]

private theorem zetaTerms_mass (j : ℕ) (t : Weights) :
    mass (zetaTerms j t) ≤ 2 * mass t := by
  have h := mass_filter_le t (fun r => !r.1.testBit j)
  simp only [zetaTerms, mass, List.map_append, List.sum_append,
    List.map_map, Function.comp_def] at h ⊢
  change (List.map Prod.snd (List.filter (fun r => !r.1.testBit j) t)).sum ≤ _ at h
  exact (Nat.add_le_add_left h _).trans (by omega)

end UnitDistancePacked


namespace UnitDistancePacked

private theorem setBit_of_clear {x j : ℕ} (hx : x.testBit j = false) :
    x + 2^j = x ||| 2^j := by
  let b := 2^(j+1)
  let r := x % b
  let q := x / b
  have hr : r < 2^j := by
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    change (x % 2^(j+1)).testBit i = false
    rw [Nat.testBit_mod_two_pow]
    rcases Nat.eq_or_lt_of_le hi with h | h
    · subst i
      simp [hx]
    · simp [show ¬ i < j+1 by omega]
  have hrb : r < b := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hr' : r + 2^j < b := by
    dsimp [b]
    rw [pow_succ]
    omega
  have hqr : x = b * q + r := (Nat.div_add_mod _ _).symm
  have hqr' : x + 2^j = b * q + (r + 2^j) := by omega
  apply Nat.eq_of_testBit_eq
  intro i
  rw [hqr', Nat.testBit_or, hqr, Nat.testBit_two_pow_mul_add q hrb,
    Nat.testBit_two_pow_mul_add q hr', Nat.testBit_two_pow]
  by_cases hi : i < j+1
  · simp only [hi, if_true]
    rw [← Nat.or_two_pow_eq_add_of_lt hr, Nat.testBit_or, Nat.testBit_two_pow]
  · have hj : j ≠ i := by omega
    simp [hi, hj]

private theorem zetaTerms_bounded {n j : ℕ} (hj : j < n)
    (t : Weights) (ht : ∀ r ∈ t, r.1 < 2^n) :
    ∀ r ∈ zetaTerms j t, r.1 < 2^n := by
  intro r hr
  rw [zetaTerms, List.mem_append] at hr
  rcases hr with hr | hr
  · exact ht _ hr
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hr
    have hv' := List.mem_filter.1 hv
    have hbit : v.1.testBit j = false := by simpa using hv'.2
    change v.1 + 2^j < 2^n
    rw [setBit_of_clear hbit]
    exact Nat.or_lt_two_pow (ht v hv'.1)
      (Nat.pow_lt_pow_right (by decide : 1 < 2) hj)

end UnitDistancePacked


namespace UnitDistancePacked

private theorem zetaTerms_fold_mass (js : List ℕ) (t : Weights) :
    mass (js.foldl (fun w j => zetaTerms j w) t) ≤ mass t * 2^js.length := by
  induction js generalizing t with
  | nil => simp
  | cons j js ih =>
    simp only [List.foldl_cons, List.length_cons, pow_succ]
    calc
      _ ≤ mass (zetaTerms j t) * 2^js.length := ih _
      _ ≤ (2 * mass t) * 2^js.length := Nat.mul_le_mul_right _ (zetaTerms_mass j t)
      _ = _ := by ring

private theorem zetaTerms_fold_bounded (js : List ℕ) (n : ℕ) (t : Weights)
    (hjs : ∀ j ∈ js, j < n) (ht : ∀ r ∈ t, r.1 < 2^n) :
    ∀ r ∈ js.foldl (fun w j => zetaTerms j w) t, r.1 < 2^n := by
  induction js generalizing t with
  | nil => exact ht
  | cons j js ih =>
    exact ih _ (fun k hk => hjs k (List.mem_cons_of_mem _ hk))
      (zetaTerms_bounded (hjs j List.mem_cons_self) t ht)

private theorem encode_zeta_fold (width n : ℕ) (hw : 0 < width)
    (js : List ℕ) (t : Weights) (hjs : ∀ j ∈ js, j < n)
    (hbound : ∀ r ∈ t, r.1 < 2^n) (hmass : mass t * 2^js.length < 2^width) :
    encode (2^width) (js.foldl (fun w j => zetaTerms j w) t) =
      js.foldl (fun w j =>
        w + ((w &&& lowStripes width n j) <<< (width * 2^j))) (encode (2^width) t) := by
  induction js generalizing t with
  | nil => rfl
  | cons j js ih =>
    have hj := hjs j List.mem_cons_self
    have hinit : mass t < 2^width := by
      refine lt_of_le_of_lt ?_ hmass
      exact Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
    have hnext : mass (zetaTerms j t) * 2^js.length < 2^width := by
      apply lt_of_le_of_lt _ hmass
      simpa only [List.length_cons, pow_succ, Nat.mul_assoc, Nat.mul_left_comm,
        Nat.mul_comm] using (Nat.mul_le_mul_right (2^js.length) (zetaTerms_mass j t))
    simp only [List.foldl_cons]
    rw [← encode_zeta_step width n j hw hj t hbound hinit]
    exact ih _ (fun k hk => hjs k (List.mem_cons_of_mem _ hk))
      (zetaTerms_bounded hj t hbound) hnext

private theorem zetaWord_eq (width n : ℕ) (hw : 0 < width) (t : Weights)
    (hbound : ∀ r ∈ t, r.1 < 2^n) (hmass : mass t * 2^n < 2^width) :
    zetaWord width n (encode (2^width) t) =
      encode (2^width) ((List.range n).foldl (fun w j => zetaTerms j w) t) := by
  apply Eq.symm
  apply encode_zeta_fold width n hw
  · exact fun j hj => List.mem_range.1 hj
  · exact hbound
  · simpa only [List.length_range] using hmass

end UnitDistancePacked


namespace UnitDistancePacked

private theorem bit_at_lane {width j : ℕ} (hw : 0 < width) (hj : j < width)
    (word i : ℕ) :
    (lane (2^width) word i).testBit j = word.testBit (j + width*i) := by
  rw [testBit_lane hw word, Nat.add_mul_div_left _ _ hw, Nat.add_mul_mod_self_left,
    Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hj, Nat.zero_add]

private theorem high_guard_lane {width n : ℕ} (hw : 0 < width) (i : ℕ) :
    lane (2^width) (repeatWord (2^(width-1)) width n) i =
      if i < 2^n then 2^(width-1) else 0 := by
  have hx : 2^(width-1) < 2^width := Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega)
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < width
  · rw [bit_at_lane hw hj, repeatWord_bits hx, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
    have hindex : j + width*i < width * 2^n ↔ i < 2^n := by
      rw [Nat.mul_comm width (2^n), ← Nat.div_lt_iff_lt_mul hw,
        Nat.add_mul_div_left _ _ hw, Nat.div_eq_of_lt hj, Nat.zero_add]
    by_cases hi : i < 2^n <;> simp [hi, hindex]
  · have hl := Nat.mod_lt ((repeatWord (2^(width-1)) width n) / (2^width)^i) (Nat.two_pow_pos width)
    have hp : 2^width ≤ 2^j := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_not_gt hj)
    have hleft : lane (2^width) (repeatWord (2^(width-1)) width n) i < 2^j := hl.trans_le hp
    by_cases hi : i < 2^n <;> simp [hi, Nat.testBit_lt_two_pow hleft,
      Nat.testBit_lt_two_pow (hx.trans_le hp)]

private theorem high_bit_iff {width word : ℕ} (hw : 0 < width) (hword : word < 2^width) :
    word.testBit (width-1) = true ↔ 2^(width-1) ≤ word := by
  refine ⟨Nat.ge_two_pow_of_testBit, fun h => Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt h ?_⟩
  rwa [Nat.sub_add_cancel (by omega : 1 ≤ width)]

end UnitDistancePacked


namespace UnitDistancePacked

private def encodeVector (base : ℕ) : List ℕ → ℕ
  | [] => 0
  | d :: ds => d + base * encodeVector base ds

private theorem lane_vector {base : ℕ} (hb : 0 < base) (ds : List ℕ)
    (hd : ∀ d ∈ ds, d < base) (i : ℕ) :
    lane base (encodeVector base ds) i = ds[i]?.getD 0 := by
  induction ds generalizing i with
  | nil => simp [lane, encodeVector]
  | cons d ds ih =>
    have hlt := hd d List.mem_cons_self
    cases i with
    | zero =>
      simp only [lane, encodeVector, pow_zero, Nat.div_one, List.getElem?_cons_zero, Option.getD_some]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
    | succ i =>
      simp only [lane, encodeVector, pow_succ, List.getElem?_cons_succ]
      rw [Nat.mul_comm (base^i) base, ← Nat.div_div_eq_div_mul,
        Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt hlt, Nat.zero_add]
      exact ih (fun x hx => hd x (List.mem_cons_of_mem _ hx)) i

private theorem word_of_vector {width n word : ℕ} (hw : 0 < width)
    (hword : ∀ i ≥ n, lane (2^width) word i = 0) :
    word = encodeVector (2^width) ((List.range n).map (lane (2^width) word)) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_lane hw word, testBit_lane hw (encodeVector _ _), lane_vector (Nat.two_pow_pos _)]
  · by_cases hj : j/width < n
    · simp [hj]
    · simp [hj, hword _ (Nat.le_of_not_gt hj)]
  · intro d hd
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hd
    exact Nat.mod_lt _ (Nat.two_pow_pos _)

private theorem encodeVector_balance (base : ℕ) (d : ℕ → ℕ)
    (p q r : ℕ → ℕ) (n : ℕ)
    (h : ∀ i < n, r i + q i = d i + p i) :
    encodeVector base ((List.range n).map r) + encodeVector base ((List.range n).map q) =
      encodeVector base ((List.range n).map d) + encodeVector base ((List.range n).map p) := by
  induction n generalizing d p q r with
  | zero => simp [encodeVector]
  | succ n ih =>
    simp only [List.range_succ_eq_map, List.map_cons, List.map_map, Function.comp_def, encodeVector]
    have h₁ := h 0 (Nat.zero_lt_succ n)
    have h₂ := ih (fun i => d (i+1)) (fun i => p (i+1)) (fun i => q (i+1)) (fun i => r (i+1))
      (fun i hi => h (i+1) (by omega))
    rw [Nat.add_add_add_comm, Nat.add_add_add_comm (d 0), ← Nat.mul_add, ← Nat.mul_add, h₁, h₂]

end UnitDistancePacked


namespace UnitDistancePacked

private theorem guarded_sub_lane {width n p q : ℕ} (hw : 0 < width)
    (hp : ∀ i, lane (2^width) p i < 2^(width-1))
    (hq : ∀ i, lane (2^width) q i < 2^(width-1))
    (hp0 : ∀ i ≥ 2^n, lane (2^width) p i = 0)
    (hq0 : ∀ i ≥ 2^n, lane (2^width) q i = 0) (i : ℕ) (hi : i < 2^n) :
    lane (2^width) (repeatWord (2^(width-1)) width n + p - q) i =
      2^(width-1) + lane (2^width) p i - lane (2^width) q i := by
  let base := 2^width
  let guard := 2^(width-1)
  let g := repeatWord guard width n
  let r (i : ℕ) := guard + lane base p i - lane base q i
  have hbase : base = guard * 2 := by
    dsimp [base, guard]
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ width)]
  have hguard (j : ℕ) := high_guard_lane (n := n) hw j
  have hg0 (j : ℕ) (hj : j ≥ 2^n) : lane base g j = 0 := by
    simpa [base, g, guard, Nat.not_lt_of_ge hj] using hguard j
  have he (j : ℕ) (hj : j < 2^n) :
      r j + lane base q j = lane base g j + lane base p j := by
    have hl : lane base g j = guard := by simpa [base, g, guard, hj] using hguard j
    rw [hl]
    have hqj : lane base q j < guard := hq j
    dsimp [r]
    omega
  have hbal := encodeVector_balance base (lane base g) (lane base p) (lane base q) r (2^n) he
  rw [← word_of_vector hw hg0, ← word_of_vector hw hp0, ← word_of_vector hw hq0] at hbal
  have htotal : g + p - q = encodeVector base ((List.range (2^n)).map r) := by omega
  have hr (j : ℕ) : r j < base := by
    have hpj : lane base p j < guard := hp j
    calc
      r j < guard * 2 := by dsimp [r]; omega
      _ = base := hbase.symm
  change lane base (g+p-q) i = r i
  rw [htotal, lane_vector (Nat.two_pow_pos width)]
  · simp [hi]
  · intro d hd
    obtain ⟨j, _, rfl⟩ := List.mem_map.1 hd
    exact hr j

private theorem zeta_lane_zero {width n : ℕ} (t : Weights)
    (ht : ∀ r ∈ t, r.1 < 2^n)
    (hm : mass t * 2^n < 2^width) (hw : 0 < width) (i : ℕ) (hi : i ≥ 2^n) :
    lane (2^width) (zetaWord width n (encode (2^width) t)) i = 0 := by
  let e := (List.range n).foldl (fun w j => zetaTerms j w) t
  have he := zetaTerms_fold_bounded (List.range n) n t (fun _ hj => List.mem_range.1 hj) ht
  have hmass := zetaTerms_fold_mass (List.range n) t
  rw [List.length_range] at hmass
  rw [zetaWord_eq width n hw t ht hm, lane_encode (Nat.two_pow_pos _) e (lt_of_le_of_lt hmass hm)]
  unfold massAt
  have he' : e.filter (fun r => r.1 = i) = [] := by
    apply List.filter_eq_nil_iff.2
    intro r hr
    have hl : r.1 < 2^n := he r hr
    simp [show r.1 ≠ i by omega]
  simp [he', mass]

end UnitDistancePacked


namespace UnitDistancePacked

private theorem setBit_xor_of_clear {x j : ℕ} (hx : x.testBit j = false) :
    x + 2^j = x ^^^ 2^j := by
  rw [setBit_of_clear hx]
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [Nat.testBit_or, Nat.testBit_xor, Nat.testBit_two_pow]
  by_cases h : j = k
  · subst k
    simp [hx]
  · simp [h]

private theorem toggleBit_of {x j : ℕ} :
    (x ^^^ 2^j).testBit j = !x.testBit j := by
  rw [Nat.testBit_xor, Nat.testBit_two_pow_self]
  cases x.testBit j <;> decide

private theorem massAt_cons (i : ℕ) (r : ℕ × ℕ) (t : Weights) :
    massAt i (r :: t) = (if r.1 = i then r.2 else 0) + massAt i t := by
  by_cases h : r.1 = i <;> simp [massAt, mass, h]

private theorem massAt_append (i : ℕ) (t u : Weights) :
    massAt i (t ++ u) = massAt i t + massAt i u := by
  simp [massAt, mass]

private theorem massAt_copy (j i : ℕ) (t : Weights) :
    massAt i ((t.filter fun r => !r.1.testBit j).map (fun r => (r.1 + 2^j, r.2))) =
      if i.testBit j then massAt (i ^^^ 2^j) t else 0 := by
  induction t with
  | nil => simp [massAt, mass]
  | cons r t ih =>
    have hc : (r.1 ^^^ 2^j = i) ↔ r.1 = (i ^^^ 2^j) := by
      constructor <;> intro h
      · rw [← h, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
      · rw [h, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    cases hr : r.1.testBit j
    · have hadd := setBit_xor_of_clear hr
      have hfalse (hi : i.testBit j = false) : r.1 ^^^ 2^j ≠ i := by
        intro h
        have he := congrArg (fun p : ℕ => p.testBit j) h
        simp [hr, hi] at he
      cases hi : i.testBit j
      · simp [hr, hi, ih, massAt_cons, hadd, hfalse hi]
      · simp [hr, hi, ih, massAt_cons, hadd, hc]
    · have hfalse (hi : i.testBit j = true) : r.1 ≠ i ^^^ 2^j := by
        intro h
        have he := congrArg (fun p : ℕ => p.testBit j) h
        simp [hr, hi] at he
      cases hi : i.testBit j
      · simp [hr, hi, ih]
      · simp [hr, hi, ih, massAt_cons, hfalse hi]

private theorem massAt_zetaTerms (j i : ℕ) (t : Weights) :
    massAt i (zetaTerms j t) =
      massAt i t + if i.testBit j then massAt (i ^^^ 2^j) t else 0 := by
  rw [zetaTerms, massAt_append, massAt_copy]

end UnitDistancePacked


namespace UnitDistancePacked

private def Reachable (k source target : ℕ) : Prop :=
  (∀ j < k, source.testBit j = true → target.testBit j = true) ∧
  ∀ j ≥ k, source.testBit j = target.testBit j

private theorem reachable_zero (source target : ℕ) :
    Reachable 0 source target ↔ source = target := by
  constructor
  · intro h
    exact Nat.eq_of_testBit_eq fun j => h.2 j (Nat.zero_le j)
  · rintro rfl
    exact ⟨fun _ _ h => h, fun _ _ => rfl⟩

private theorem testBit_xor_other {i j : ℕ} (h : i ≠ j) (x : ℕ) :
    (x ^^^ 2^i).testBit j = x.testBit j := by
  rw [Nat.testBit_xor, Nat.testBit_two_pow_of_ne h]
  cases x.testBit j <;> decide

private theorem reachable_succ (k a b : ℕ) :
    Reachable (k+1) a b ↔
      Reachable k a b ∨ (b.testBit k = true ∧ Reachable k a (b ^^^ 2^k)) := by
  constructor
  · intro h
    by_cases hab : a.testBit k = b.testBit k
    · exact Or.inl ⟨fun j hj => h.1 j (by omega), fun j hj => by
        rcases Nat.eq_or_lt_of_le hj with h₁ | h₁
        · simpa [← h₁] using hab
        · exact h.2 j (by omega)⟩
    · have ha : a.testBit k = false := by
        cases e : a.testBit k
        · rfl
        · exact False.elim (hab (e.trans (h.1 k (by omega) e).symm))
      have hb : b.testBit k = true := by
        cases e : b.testBit k
        · exact False.elim (hab (ha.trans e.symm))
        · rfl
      refine Or.inr ⟨hb, ⟨?_, ?_⟩⟩
      · intro j hj hja
        rw [testBit_xor_other (by omega : k ≠ j)]
        exact h.1 j (by omega) hja
      · intro j hj
        rcases Nat.eq_or_lt_of_le hj with h₁ | h₁
        · subst j
          simp [ha, hb]
        · rw [testBit_xor_other (by omega : k ≠ j)]
          exact h.2 j (by omega)
  · intro h
    rcases h with h | ⟨hb, h⟩
    · refine ⟨?_, fun j hj => h.2 j (by omega)⟩
      intro j hj hja
      by_cases hlt : j < k
      · exact h.1 j hlt hja
      · rwa [← h.2 j (by omega)]
    · refine ⟨?_, ?_⟩
      · intro j hj hja
        by_cases hlt : j < k
        · have ht := h.1 j hlt hja
          rwa [testBit_xor_other (by omega : k ≠ j)] at ht
        · rwa [show j = k by omega]
      · intro j hj
        have ht := h.2 j (by omega)
        rwa [testBit_xor_other (by omega : k ≠ j)] at ht

private theorem reachable_disjoint (k a b : ℕ)
    (h : Reachable k a b) (h' : Reachable k a (b ^^^ 2^k)) : False := by
  have s := (h.2 k le_rfl).symm.trans (h'.2 k le_rfl)
  rw [toggleBit_of] at s
  cases e : b.testBit k <;> simp [e] at s

end UnitDistancePacked


namespace UnitDistancePacked

private noncomputable def massWhere (p : ℕ → Prop) (t : Weights) : ℕ := by
  classical
  exact (t.map fun r => if p r.1 then r.2 else 0).sum

private theorem massWhere_cons (p : ℕ → Prop) (r : ℕ × ℕ) (t : Weights) :
    letI := Classical.propDecidable
    massWhere p (r :: t) = (if p r.1 then r.2 else 0) + massWhere p t := rfl

private theorem massWhere_eq (I : ℕ) (t : Weights) :
    massWhere (· = I) t = massAt I t := by
  induction t with
  | nil => rfl
  | cons r t ih =>
    rw [massWhere_cons, massAt_cons, ih]
    by_cases h : r.1 = I <;> simp [h]

private theorem massWhere_reach_succ (k I : ℕ) (t : Weights) :
    massWhere (Reachable (k+1) · I) t =
      massWhere (Reachable k · I) t +
        if I.testBit k then massWhere (Reachable k · (I ^^^ 2^k)) t else 0 := by
  classical
  induction t with
  | nil => cases I.testBit k <;> rfl
  | cons r t ih =>
    simp only [massWhere_cons]
    rw [ih, reachable_succ k r.1 I]
    by_cases h₁ : Reachable k r.1 I
    · have h₂ : ¬Reachable k r.1 (I ^^^ 2^k) :=
        fun h => reachable_disjoint k r.1 I h₁ h
      cases hi : I.testBit k <;> simp [h₁, h₂, Nat.add_assoc]
    · cases hi : I.testBit k
      · simp [h₁]
      · simp [h₁, Nat.add_left_comm]

private theorem massAt_zeta_range (k I : ℕ) (t : Weights) :
    massAt I ((List.range k).foldl (fun w j => zetaTerms j w) t) =
      massWhere (Reachable k · I) t := by
  induction k generalizing I with
  | zero =>
    change massAt I t = _
    rw [show (Reachable 0 · I) = (· = I) from funext (fun a => propext (reachable_zero a I)),
      massWhere_eq]
  | succ k ih =>
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [massAt_zetaTerms, ih, ih, massWhere_reach_succ]

private def submask (m I : ℕ) : Prop := m &&& I = m

private theorem submask_iff (m I : ℕ) :
    submask m I ↔ ∀ j, m.testBit j = true → I.testBit j = true := by
  constructor
  · intro h j hj
    have hh := congrArg (fun n => Nat.testBit n j) h
    simpa only [Nat.testBit_land, hj, Bool.true_and] using hh
  · intro h
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_land]
    cases e : m.testBit j
    · simp
    · simp only [Bool.true_and]
      exact h j e

private theorem reachable_full {n a I : ℕ} (ha : a < 2^n) (hI : I < 2^n) :
    Reachable n a I ↔ submask a I := by
  have off {m : ℕ} (hm : m < 2^n) {k : ℕ} (hk : n ≤ k) :
      m.testBit k = false :=
    Nat.testBit_lt_two_pow (hm.trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) hk))
  rw [submask_iff]
  constructor
  · intro h k hs
    by_cases hk : k < n
    · exact h.1 k hk hs
    · simp [off ha (Nat.le_of_not_gt hk)] at hs
  · intro h
    exact ⟨fun k _ => h k, fun k hk => (off ha hk).trans (off hI hk).symm⟩

private theorem massWhere_congr (p q : ℕ → Prop) (t : Weights)
    (h : ∀ r ∈ t, p r.1 ↔ q r.1) : massWhere p t = massWhere q t := by
  classical
  unfold massWhere
  congr 1
  apply List.map_congr_left
  intro r hr
  simp only [h r hr]

private theorem zeta_submask_lane (width n : ℕ) (hw : 0 < width) (t : Weights)
    (hbound : ∀ r ∈ t, r.1 < 2^n) (hmass : mass t * 2^n < 2^width)
    (I : ℕ) (hI : I < 2^n) :
    lane (2^width) (zetaWord width n (encode (2^width) t)) I = massWhere (submask · I) t := by
  have h := zetaTerms_fold_mass (List.range n) t
  rw [List.length_range] at h
  rw [zetaWord_eq width n hw t hbound hmass,
    lane_encode (Nat.two_pow_pos _) _ (h.trans_lt hmass), massAt_zeta_range]
  apply massWhere_congr
  exact fun r hr => reachable_full (hbound r hr) hI

end UnitDistancePacked


namespace UnitDistancePacked

private theorem foldl_preserves {α β : Type} (p : α → Prop) (f : α → β → α)
    (a : α) (xs : List β) (ha : p a)
    (hf : ∀ b ∈ xs, ∀ curr, p curr → p (f curr b)) :
    p (xs.foldl f a) := by
  induction xs generalizing a with
  | nil => exact ha
  | cons b xs ih =>
    exact ih (f a b) (hf b List.mem_cons_self a ha)
      (fun x hx => hf x (List.mem_cons_of_mem _ hx))

private theorem valid_guard_bit {width : ℕ} (hw : 0 < width) (rows : List ℕ)
    (allowed mask : ℕ) (hmask : mask < 2^rows.length)
    (ha : ∀ i < rows.length, mask.testBit i = true → allowed.testBit i = true)
    (he : ∀ i < rows.length, ∀ j < i, (rows[i]?.getD 0).testBit j = true →
      mask.testBit i = false ∨ mask.testBit j = false) :
    (auditGuards width rows allowed).2.testBit (width-1 + width*mask) = true := by
  let n := rows.length
  let index := width-1 + width*mask
  have hwidth : width-1 < width := by omega
  have hindex : index/width = mask := by
    dsimp [index]
    rw [Nat.add_mul_div_left _ _ hw, Nat.div_eq_of_lt hwidth, Nat.zero_add]
  have guard : (repeatWord (2^(width-1)) width n).testBit index = true := by
    rw [← bit_at_lane hw hwidth, high_guard_lane hw, if_pos hmask, Nat.testBit_two_pow_self]
  have stripe (i : ℕ) (hi : i < n) :
      (lowStripes width n i).testBit index = !mask.testBit i := by
    rw [lowStripes_bits hw hi, hindex]
    simp [hmask, n]
  unfold auditGuards
  refine foldl_preserves (fun (a : ℕ) => a.testBit index = true) _ _ _ guard ?_
  intro i hi current hcurrent
  have hin := List.mem_range.1 hi
  dsimp only
  split
  · refine foldl_preserves (fun (a : ℕ) => a.testBit index = true) _ _ _ hcurrent ?_
    intro j hj curr hcurr
    have hji := List.mem_range.1 hj
    split
    · rename_i hv
      rw [Nat.testBit_and, Nat.testBit_or, stripe i hin, stripe j (hji.trans hin)]
      rcases he i hin j hji hv with hx | hx <;> simp [hcurr, hx]
    · exact hcurr
  · rename_i hv
    have hm : mask.testBit i = false := by
      cases hc : mask.testBit i
      · rfl
      · exact False.elim (hv (ha i hin hc))
    have hstripe : (lowStripes width rows.length i).testBit index = !mask.testBit i := stripe i hin
    simp [Nat.testBit_and, hstripe, hcurrent, hm]

end UnitDistancePacked


namespace UnitDistancePacked

private abbrev Terms := List (ℕ × ℤ)

private def positiveTerms (t : Terms) : Weights :=
  t.filterMap fun r => if 0 ≤ r.2 then some (r.1, r.2.toNat) else none

private def negativeTerms (t : Terms) : Weights :=
  t.filterMap fun r => if 0 ≤ r.2 then none else some (r.1, (-r.2).toNat)

private def packAdd (width : ℕ) (a : ℕ × ℕ) (r : ℕ × ℤ) : ℕ × ℕ :=
  if 0 ≤ r.2 then (a.1 + (r.2.toNat <<< (width*r.1)), a.2)
  else (a.1, a.2 + ((-r.2).toNat <<< (width*r.1)))

private def packWords (width : ℕ) (t : Terms) : ℕ × ℕ :=
  t.foldl (packAdd width) (0, 0)

private theorem packFold_eq (width : ℕ) (t : Terms) (a : ℕ × ℕ) :
    t.foldl (packAdd width) a =
      (a.1 + encode (2^width) (positiveTerms t), a.2 + encode (2^width) (negativeTerms t)) := by
  induction t generalizing a with
  | nil => simp [positiveTerms, negativeTerms, encode]
  | cons r t ih =>
    rw [List.foldl_cons, ih]
    by_cases hr : 0 ≤ r.2 <;>
      simp [packAdd, encode, positiveTerms, negativeTerms, hr, Nat.shiftLeft_eq, pow_mul, Nat.add_assoc]

private theorem packWords_eq (width : ℕ) (t : Terms) :
    packWords width t =
      (encode (2^width) (positiveTerms t), encode (2^width) (negativeTerms t)) := by
  simpa only [packWords, Nat.zero_add] using packFold_eq width t (0,0)

private def totalMass (t : Terms) : ℕ := (t.map (fun r => r.2.natAbs)).sum

private theorem absMass_bound (t : Terms) :
    mass (positiveTerms t) + mass (negativeTerms t) = totalMass t := by
  induction t with
  | nil => rfl
  | cons r t ih =>
    by_cases hr : 0 ≤ r.2
    · have hh : r.2.toNat = r.2.natAbs := by omega
      simp [positiveTerms, negativeTerms, mass, totalMass, hr, hh] at ih ⊢
      omega
    · have hh : (-r.2).toNat = r.2.natAbs := by omega
      simp [positiveTerms, negativeTerms, mass, totalMass, hr, hh] at ih ⊢
      omega

private theorem terms_bounded (n : ℕ) (t : Terms)
    (ht : ∀ r ∈ t, r.1 < 2^n) :
    (∀ r ∈ positiveTerms t, r.1 < 2^n) ∧ (∀ r ∈ negativeTerms t, r.1 < 2^n) := by
  constructor <;> intro r hr
  · obtain ⟨x, hx, e⟩ := List.mem_filterMap.1 hr
    by_cases h : 0 ≤ x.2
    · simp [h] at e
      rw [← e]
      exact ht x hx
    · simp [h] at e
  · obtain ⟨x, hx, e⟩ := List.mem_filterMap.1 hr
    by_cases h : 0 ≤ x.2
    · simp [h] at e
    · simp [h] at e
      rw [← e]
      exact ht x hx

private instance (m I : ℕ) : Decidable (submask m I) :=
  inferInstanceAs (Decidable (_ = _))

def score (I : ℕ) (t : Terms) : ℤ :=
  (t.map fun r => if submask r.1 I then r.2 else 0).sum

private theorem score_split (I : ℕ) (t : Terms) :
    score I t = (massWhere (submask · I) (positiveTerms t) : ℤ) -
      (massWhere (submask · I) (negativeTerms t) : ℤ) := by
  induction t with
  | nil => rfl
  | cons r t ih =>
    simp only [score, List.map_cons, List.sum_cons] at ih ⊢
    by_cases hr : 0 ≤ r.2 <;>
      by_cases hm : submask r.1 I <;>
      simp [positiveTerms, negativeTerms, hr, massWhere_cons, hm] at ih ⊢ <;>
      omega

private def auditPacked (width : ℕ) (rows : List ℕ) (allowed : ℕ) (packed : ℕ × ℕ) : Bool :=
  let n := rows.length
  let (p, q) := packed
  let (g, valid) := auditGuards width rows allowed
  let word := g + zetaWord width n p - zetaWord width n q
  word &&& valid == valid

private theorem zeta_lane_lt_guard (width n : ℕ) (hw : 0 < width) (t : Weights)
    (ht : ∀ r ∈ t, r.1 < 2^n)
    (hm : mass t * 2^n < 2^(width-1)) (i : ℕ) :
    lane (2^width) (zetaWord width n (encode (2^width) t)) i < 2^(width-1) := by
  have hg : 2^(width-1) ≤ 2^width := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  have h := zetaTerms_fold_mass (List.range n) t
  rw [List.length_range] at h
  rw [zetaWord_eq width n hw t ht (hm.trans_le hg),
    lane_encode (Nat.two_pow_pos _) _ ((h.trans_lt hm).trans_le hg)]
  exact (mass_filter_le _ _).trans_lt (h.trans_lt hm)

private theorem auditPacked_sound {width : ℕ} (hw : 0 < width) (rows : List ℕ)
    (allowed : ℕ) (t : Terms) (hcheck : auditPacked width rows allowed (packWords width t) = true)
    (hterms : ∀ r ∈ t, r.1 < 2^rows.length)
    (hmass : totalMass t * 2^rows.length < 2^(width-1))
    (I : ℕ) (hI : I < 2^rows.length)
    (ha : ∀ i < rows.length, I.testBit i = true → allowed.testBit i = true)
    (he : ∀ i < rows.length, ∀ j < i, (rows[i]?.getD 0).testBit j = true →
      I.testBit i = false ∨ I.testBit j = false) : 0 ≤ score I t := by
  let n := rows.length

  obtain ⟨hp, hq⟩ := terms_bounded n t hterms
  have hgt : 2^(width-1) ≤ 2^width := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  have hm := absMass_bound t
  have hmp : mass (positiveTerms t) * 2^n < 2^(width-1) :=
    (Nat.mul_le_mul_right _ (show mass (positiveTerms t) ≤ totalMass t by omega)).trans_lt hmass
  have hmq : mass (negativeTerms t) * 2^n < 2^(width-1) :=
    (Nat.mul_le_mul_right _ (show mass (negativeTerms t) ≤ totalMass t by omega)).trans_lt hmass
  let P := zetaWord width n (encode (2^width) (positiveTerms t))
  let Q := zetaWord width n (encode (2^width) (negativeTerms t))
  let G := repeatWord (2^(width-1)) width n
  let V := (auditGuards width rows allowed).2
  simp only [auditPacked, packWords_eq, beq_iff_eq] at hcheck
  change (G + P - Q) &&& V = V at hcheck
  let idx := width-1 + width*I
  have hv : V.testBit idx = true := valid_guard_bit hw rows allowed I hI ha he
  have hb := congrArg (fun w : ℕ => w.testBit idx) hcheck
  simp only [Nat.testBit_and, hv, Bool.and_true] at hb
  have ht : width-1 < width := by omega
  change (G + P - Q).testBit (width-1 + width*I) = true at hb
  rw [← bit_at_lane hw ht] at hb
  have hguard := (high_bit_iff hw (Nat.mod_lt _ (Nat.two_pow_pos width))).1 hb
  change 2^(width-1) ≤ lane (2^width) (G + P - Q) I at hguard
  rw [guarded_sub_lane hw (zeta_lane_lt_guard width n hw _ hp hmp)
    (zeta_lane_lt_guard width n hw _ hq hmq)
    (zeta_lane_zero _ hp (hmp.trans_le hgt) hw)
    (zeta_lane_zero _ hq (hmq.trans_le hgt) hw) I hI] at hguard
  rw [zeta_submask_lane width n hw _ hp (hmp.trans_le hgt) I hI,
      zeta_submask_lane width n hw _ hq (hmq.trans_le hgt) I hI] at hguard
  rw [score_split]
  have hgpos := Nat.two_pow_pos (width-1)
  omega

end UnitDistancePacked


namespace UnitDistancePacked

private def restrictMask (free : List ℕ) (m : ℕ) : ℕ :=
  match free with
  | [] => 0
  | v :: vs => Nat.bit (m.testBit v) (restrictMask vs m)

private theorem restrictMask_lt (free : List ℕ) (m : ℕ) :
    restrictMask free m < 2^free.length := by
  induction free with
  | nil => simp [restrictMask]
  | cons v vs ih => simpa [restrictMask] using ih

private theorem testBit_restrictMask (free : List ℕ) (m i : ℕ) (hi : i < free.length) :
    (restrictMask free m).testBit i = m.testBit (free[i]'hi) := by
  induction free generalizing i with
  | nil => simp at hi
  | cons v vs ih =>
    cases i with
    | zero => simp [restrictMask]
    | succ i =>
      rw [restrictMask, Nat.testBit_bit_succ]
      exact ih i (by simpa using hi)

private def freeMask : List ℕ → ℕ
  | [] => 0
  | v :: vs => 2^v ||| freeMask vs

private theorem testBit_freeMask (free : List ℕ) (j : ℕ) :
    (freeMask free).testBit j = true ↔ j ∈ free := by
  induction free with
  | nil => simp [freeMask]
  | cons v vs ih =>
    simp only [freeMask, Nat.testBit_or, Bool.or_eq_true, Nat.testBit_two_pow,
      decide_eq_true_eq, ih, List.mem_cons]
    exact or_congr eq_comm Iff.rfl

private def AgreesOutside (free : List ℕ) (fixed I : ℕ) : Prop :=
  ∀ j ∉ free, I.testBit j = fixed.testBit j

private theorem submask_restrict (free : List ℕ) (fixed I m : ℕ)
    (hI : AgreesOutside free fixed I) :
    submask m I ↔ submask m (fixed ||| freeMask free) ∧
      submask (restrictMask free m) (restrictMask free I) := by
  simp only [submask_iff]
  constructor
  · intro h
    constructor
    · intro j hj
      rw [Nat.testBit_or, Bool.or_eq_true]
      by_cases hjf : j ∈ free
      · exact Or.inr ((testBit_freeMask free j).2 hjf)
      · exact Or.inl ((hI j hjf).symm.trans (h j hj))
    · intro i hi
      by_cases hib : i < free.length
      · rw [testBit_restrictMask free m i hib] at hi
        rw [testBit_restrictMask free I i hib]
        exact h _ hi
      · have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_not_gt hib)
        simp [Nat.testBit_lt_two_pow ((restrictMask_lt free m).trans_le hpow)] at hi
  · rintro ⟨hallowed, hproj⟩ j hj
    by_cases hm : j ∈ free
    · obtain ⟨i, hi, he⟩ := List.getElem_of_mem hm
      have hb : (restrictMask free m).testBit i = true := by
        rw [testBit_restrictMask free m i hi, he, hj]
      have h := hproj i hb
      rwa [testBit_restrictMask free I i hi, he] at h
    · have hbit : (freeMask free).testBit j = false := by
        cases h : (freeMask free).testBit j
        · rfl
        · exact False.elim (hm ((testBit_freeMask free j).1 h))
      have hf := hallowed j hj
      rw [Nat.testBit_or, hbit, Bool.or_false] at hf
      exact (hI j hm).trans hf

private def projectTerms (free : List ℕ) (fixed : ℕ) (t : Terms) : Terms :=
  let allowed := fixed ||| freeMask free
  t.filterMap fun r =>
    if submask r.1 allowed then some (restrictMask free r.1, r.2) else none

private theorem score_projectTerms (free : List ℕ) (fixed I : ℕ) (t : Terms)
    (hi : AgreesOutside free fixed I) :
    score (restrictMask free I) (projectTerms free fixed t) = score I t := by
  induction t with
  | nil => rfl
  | cons r t ih =>
    have hm := submask_restrict free fixed I r.1 hi
    by_cases h : submask r.1 (fixed ||| freeMask free)
    · have he : submask r.1 I ↔ submask (restrictMask free r.1) (restrictMask free I) := by
        rw [hm, and_iff_right h]
      simp [projectTerms, h, score, he] at ih ⊢
      rw [ih]
    · have hn : ¬submask r.1 I := fun e => h (hm.1 e).1
      simpa [projectTerms, score, h, hn] using ih

private def restrictRows (adj : ℕ → ℕ) (free : List ℕ) : List ℕ :=
  free.map fun i => restrictMask free (adj i)

private def Independent (adj : ℕ → ℕ) (I : ℕ) : Prop :=
  ∀ i j, (adj i).testBit j = true → I.testBit i = true → I.testBit j = false

private theorem restriction_independent (adj : ℕ → ℕ) (free : List ℕ) (I : ℕ)
    (hI : Independent adj I) (i : ℕ) (hi : i < (restrictRows adj free).length)
    (j : ℕ) (hj : j < i)
    (he : ((restrictRows adj free)[i]?.getD 0).testBit j = true) :
    (restrictMask free I).testBit i = false ∨ (restrictMask free I).testBit j = false := by
  have hi' : i < free.length := by simpa [restrictRows] using hi
  have hj' : j < free.length := hj.trans hi'
  rw [restrictRows, List.getElem?_map, List.getElem?_eq_getElem hi',
    Option.map_some, Option.getD_some, testBit_restrictMask free _ j hj'] at he
  rw [testBit_restrictMask free I i hi', testBit_restrictMask free I j hj']
  cases hh : I.testBit (free[i]'hi')
  · exact Or.inl rfl
  · exact Or.inr (hI _ _ he hh)

private def omitVertex (free : List ℕ) (v : ℕ) : List ℕ :=
  free.filter fun w => w ≠ v

private def omitNeighbors (adj : ℕ → ℕ) (free : List ℕ) (v : ℕ) : List ℕ :=
  free.filter fun w => (decide (w ≠ v)) && !(adj v).testBit w

private def exclude (fixed v : ℕ) : ℕ := Nat.ldiff fixed (2^v)

private def includeVertex (adj : ℕ → ℕ) (fixed v : ℕ) : ℕ :=
  Nat.ldiff fixed (adj v) ||| 2^v

private def NonnegativeOn (adj : ℕ → ℕ) (free : List ℕ) (fixed : ℕ) (t : Terms) : Prop :=
  ∀ I, Independent adj I → AgreesOutside free fixed I → 0 ≤ score I t

private theorem nonnegative_branch (adj : ℕ → ℕ) (free : List ℕ) (fixed v : ℕ) (t : Terms)
    (hoff : NonnegativeOn adj (omitVertex free v) (exclude fixed v) t)
    (hon : NonnegativeOn adj (omitNeighbors adj free v) (includeVertex adj fixed v) t) :
    NonnegativeOn adj free fixed t := by
  intro I hi hag
  cases hv : I.testBit v
  · apply hoff I hi
    intro j hj
    by_cases e : j = v
    · subst j
      simp [exclude, hv]
    · have hfree : j ∉ free := fun h => hj (List.mem_filter.2 ⟨h, by simp [e]⟩)
      simpa [exclude, Nat.testBit_two_pow_of_ne (Ne.symm e)] using hag j hfree
  · apply hon I hi
    intro j hj
    by_cases e : j = v
    · subst j
      simp [includeVertex, hv]
    · cases hn : (adj v).testBit j
      · have hfree : j ∉ free := fun h => hj (List.mem_filter.2 ⟨h, by simp [e, hn]⟩)
        simpa [includeVertex, hn, Nat.testBit_two_pow_of_ne (Ne.symm e)] using hag j hfree
      · have hj' := hi v j hn hv
        simp [includeVertex, hn, hj', Nat.testBit_two_pow_of_ne (Ne.symm e)]

private theorem nonnegative_unconstrained (adj : ℕ → ℕ) (n : ℕ) (t : Terms)
    (h : NonnegativeOn adj (List.range n) 0 t) (I : ℕ)
    (hi : Independent adj I) (hb : I < 2^n) :
    0 ≤ score I t := by
  apply h I hi
  intro j hj
  have hle : n ≤ j := Nat.le_of_not_gt (fun h => hj (List.mem_range.2 h))
  rw [Nat.zero_testBit]
  exact Nat.testBit_lt_two_pow
    (hb.trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) hle))

end UnitDistancePacked


namespace UnitDistancePacked

private def addProjection (width : ℕ) (free : List ℕ) (allowed : ℕ)
    (a : ℕ × ℕ) (r : ℕ × ℤ) : ℕ × ℕ :=
  if submask r.1 allowed then packAdd width a (restrictMask free r.1, r.2) else a

private def packProjected (width : ℕ) (free : List ℕ) (fixed : ℕ)
    (blocks : List Terms) : ℕ × ℕ :=
  let add := addProjection width free (fixed ||| freeMask free)
  blocks.foldl (fun a b => b.foldl add a) (0, 0)

private def checkProjected (width : ℕ) (adj : ℕ → ℕ) (free : List ℕ)
    (fixed : ℕ) (blocks : List Terms) : Bool :=
  let n := free.length
  let (p, q) := packProjected width free fixed blocks
  let (g, valid) := auditGuards width (restrictRows adj free) (2^n-1)
  let word := g + zetaWord width n p - zetaWord width n q
  word &&& valid == valid

private theorem packProjected_eq (width : ℕ) (free : List ℕ) (fixed : ℕ)
    (blocks : List Terms) :
    packProjected width free fixed blocks =
      packWords width (projectTerms free fixed blocks.flatten) := by
  let a := addProjection width free (fixed ||| freeMask free)
  have h₁ (t : Terms) (w : ℕ × ℕ) :
      t.foldl a w = (projectTerms free fixed t).foldl (packAdd width) w := by
    induction t generalizing w with
    | nil => rfl
    | cons r t ih =>
      rw [List.foldl_cons, ih]
      by_cases hr : submask r.1 (fixed ||| freeMask free) <;>
        simp [a, addProjection, projectTerms, hr]
  have h₂ (w : ℕ × ℕ) :
      blocks.foldl (fun w b => b.foldl a w) w =
      blocks.flatten.foldl a w := by
    induction blocks generalizing w with
    | nil => rfl
    | cons b bs ih => simp only [List.foldl_cons, ih, List.flatten_cons, List.foldl_append]
  exact (h₂ (0,0)).trans (h₁ blocks.flatten (0,0))

private theorem projectTerms_support (free : List ℕ) (fixed : ℕ) (t : Terms) :
    ∀ r ∈ projectTerms free fixed t, r.1 < 2^free.length := by
  intro r hr
  obtain ⟨s, _, hs⟩ := List.mem_filterMap.1 hr
  by_cases ha : submask s.1 (fixed ||| freeMask free)
  · simp [ha] at hs
    rw [← hs]
    exact restrictMask_lt free s.1
  · simp [ha] at hs

private theorem projectTerms_mass (free : List ℕ) (fixed : ℕ) (t : Terms) :
    totalMass (projectTerms free fixed t) ≤ totalMass t := by
  induction t with
  | nil => simp [projectTerms, totalMass]
  | cons r rs ih =>
    by_cases h : submask r.1 (fixed ||| freeMask free) <;>
      simp [projectTerms, totalMass, h] at ih ⊢ <;> omega

private theorem checkProjected_sound {width : ℕ} (hw : 0 < width)
    (adj : ℕ → ℕ) (free : List ℕ) (fixed : ℕ) (blocks : List Terms)
    (hm : totalMass blocks.flatten * 2^free.length < 2^(width-1))
    (hc : checkProjected width adj free fixed blocks = true) :
    NonnegativeOn adj free fixed blocks.flatten := by
  intro I hI hag
  rw [← score_projectTerms free fixed I _ hag]
  let rows := restrictRows adj free
  have hlen : rows.length = free.length := by simp [rows, restrictRows]
  have hcore : auditPacked width rows (2^free.length-1)
      (packWords width (projectTerms free fixed blocks.flatten)) = true := by
    rw [← packProjected_eq]
    unfold auditPacked checkProjected at *
    rwa [hlen]
  apply auditPacked_sound hw rows _ _ hcore
  · intro r hr
    rw [hlen]
    exact projectTerms_support free fixed _ r hr
  · rw [hlen]
    exact (Nat.mul_le_mul_right _ (projectTerms_mass free fixed _)).trans_lt hm
  · rw [hlen]
    exact restrictMask_lt free I
  · intro i hi _
    rw [Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
    exact hi.trans_eq hlen
  · exact fun i hi j hj => restriction_independent adj free I hI i hi j hj

end UnitDistancePacked

/- Exact integer arithmetic for the four radicals in the 29-vertex construction. -/

namespace SnailCoordinates

private def extendAdd {K : Type} (add : K → K → K) (x y : K × K) : K × K :=
  (add x.1 y.1, add x.2 y.2)

private def extendNeg {K : Type} (neg : K → K) (x : K × K) : K × K :=
  (neg x.1, neg x.2)

private def extendMul {K : Type} (add mul : K → K → K) (D : K)
    (x y : K × K) : K × K :=
  (add (mul x.1 y.1) (mul D (mul x.2 y.2)),
    add (mul x.1 y.2) (mul x.2 y.1))

private def extendEval {K : Type} (e : K → ℝ) (r : ℝ) (x : K × K) : ℝ :=
  e x.1 + r * e x.2

private theorem extendEval_add {K : Type} (e : K → ℝ) (r : ℝ) (add : K → K → K)
    (hadd : ∀ x y, e (add x y) = e x + e y) (x y : K × K) :
    extendEval e r (extendAdd add x y) = extendEval e r x + extendEval e r y := by
  simp only [extendEval, extendAdd, hadd]
  ring

private theorem extendEval_neg {K : Type} (e : K → ℝ) (r : ℝ) (neg : K → K)
    (hneg : ∀ x, e (neg x) = - e x) (x : K × K) :
    extendEval e r (extendNeg neg x) = - extendEval e r x := by
  simp only [extendEval, extendNeg, hneg]
  ring

private theorem extendEval_mul {K : Type} (e : K → ℝ) (r : ℝ) (add mul : K → K → K)
    (D : K) (hr : r^2 = e D)
    (hadd : ∀ x y, e (add x y) = e x + e y)
    (hmul : ∀ x y, e (mul x y) = e x * e y) (x y : K × K) :
    extendEval e r (extendMul add mul D x y) = extendEval e r x * extendEval e r y := by
  simp only [extendEval, extendMul, hadd, hmul]
  linear_combination -(e x.2 * e y.2) * hr

private abbrev K0 := ℤ
private def int0 (q : ℤ) : K0 := q
private def add0 (x y : K0) : K0 := x + y
private def mul0 (x y : K0) : K0 := x * y
private def neg0 (x : K0) : K0 := -x
private def eval0 (q : K0) : ℝ := q

private theorem eval0_add (x y : K0) : eval0 (add0 x y) = eval0 x + eval0 y := by
  simp [eval0, add0]

private theorem eval0_neg (x : K0) : eval0 (neg0 x) = -eval0 x := by simp [eval0, neg0]
private theorem eval0_mul (x y : K0) : eval0 (mul0 x y) = eval0 x * eval0 y := by simp [eval0, mul0]
private theorem eval0_int (q : ℤ) : eval0 (int0 q) = q := rfl

private abbrev K1 := K0 × K0
private def int1 (q : ℤ) : K1 := (int0 q, int0 0)
private def add1 := extendAdd (K := K0) add0
private def neg1 := extendNeg (K := K0) neg0
private def square1 : K0 := int0 3
private def mul1 := extendMul (K := K0) add0 mul0 square1
private noncomputable def radical1 : ℝ := Real.sqrt 3
private noncomputable def eval1 := extendEval (K := K0) eval0 radical1

private theorem eval1_int (q : ℤ) : eval1 (int1 q) = q := by
  simp [eval1, int1, extendEval, eval0_int]

private theorem radical1_sq : radical1^2 = eval0 square1 := by
  unfold radical1
  rw [Real.sq_sqrt (by norm_num)]
  unfold square1
  rw [eval0_int]
  norm_num

private theorem eval1_add (x y : K1) : eval1 (add1 x y) = eval1 x + eval1 y :=
  extendEval_add eval0 radical1 add0 eval0_add x y
private theorem eval1_neg (x : K1) : eval1 (neg1 x) = -eval1 x :=
  extendEval_neg eval0 radical1 neg0 eval0_neg x
private theorem eval1_mul (x y : K1) : eval1 (mul1 x y) = eval1 x * eval1 y :=
  extendEval_mul eval0 radical1 add0 mul0 square1 radical1_sq eval0_add eval0_mul x y

private abbrev K2 := K1 × K1
private def int2 (q : ℤ) : K2 := (int1 q, int1 0)
private def add2 := extendAdd (K := K1) add1
private def neg2 := extendNeg (K := K1) neg1
private def square2 : K1 := int1 11
private def mul2 := extendMul (K := K1) add1 mul1 square2
private noncomputable def radical2 : ℝ := Real.sqrt 11
private noncomputable def eval2 := extendEval (K := K1) eval1 radical2

private theorem eval2_int (q : ℤ) : eval2 (int2 q) = q := by
  simp [eval2, int2, extendEval, eval1_int]

private theorem radical2_sq : radical2^2 = eval1 square2 := by
  unfold radical2
  rw [Real.sq_sqrt (by norm_num)]
  unfold square2
  rw [eval1_int]
  norm_num

private theorem eval2_add (x y : K2) : eval2 (add2 x y) = eval2 x + eval2 y :=
  extendEval_add eval1 radical2 add1 eval1_add x y
private theorem eval2_neg (x : K2) : eval2 (neg2 x) = -eval2 x :=
  extendEval_neg eval1 radical2 neg1 eval1_neg x
private theorem eval2_mul (x y : K2) : eval2 (mul2 x y) = eval2 x * eval2 y :=
  extendEval_mul eval1 radical2 add1 mul1 square2 radical2_sq eval1_add eval1_mul x y

private abbrev K3 := K2 × K2
private def int3 (q : ℤ) : K3 := (int2 q, int2 0)
private def add3 := extendAdd (K := K2) add2
private def neg3 := extendNeg (K := K2) neg2
private def square3 : K2 := int2 5
private def mul3 := extendMul (K := K2) add2 mul2 square3
private noncomputable def radical3 : ℝ := Real.sqrt 5
private noncomputable def eval3 := extendEval (K := K2) eval2 radical3

private theorem eval3_int (q : ℤ) : eval3 (int3 q) = q := by
  simp [eval3, int3, extendEval, eval2_int]

private theorem radical3_sq : radical3^2 = eval2 square3 := by
  unfold radical3
  rw [Real.sq_sqrt (by norm_num)]
  unfold square3
  rw [eval2_int]
  norm_num

private theorem eval3_add (x y : K3) : eval3 (add3 x y) = eval3 x + eval3 y :=
  extendEval_add eval2 radical3 add2 eval2_add x y
private theorem eval3_neg (x : K3) : eval3 (neg3 x) = -eval3 x :=
  extendEval_neg eval2 radical3 neg2 eval2_neg x
private theorem eval3_mul (x y : K3) : eval3 (mul3 x y) = eval3 x * eval3 y :=
  extendEval_mul eval2 radical3 add2 mul2 square3 radical3_sq eval2_add eval2_mul x y

private abbrev K4 := K3 × K3
private def int4 (q : ℤ) : K4 := (int3 q, int3 0)
private def add4 := extendAdd (K := K3) add3
private def neg4 := extendNeg (K := K3) neg3
private def square4 : K3 := (((830, 0), (0, 158)), ((0, 0), (0, 0)))
private def mul4 := extendMul (K := K3) add3 mul3 square4
private noncomputable def radical4 : ℝ := Real.sqrt (830 + 158 * radical1 * radical2)
private noncomputable def eval4 := extendEval (K := K3) eval3 radical4

private theorem eval4_int (q : ℤ) : eval4 (int4 q) = q := by
  simp [eval4, int4, extendEval, eval3_int]

private theorem radical4_sq : radical4^2 = eval3 square4 := by
  unfold radical4 square4
  rw [Real.sq_sqrt (by unfold radical1 radical2; positivity)]
  simp only [eval3, eval2, eval1, eval0, extendEval]
  push_cast
  ring

private theorem eval4_add (x y : K4) : eval4 (add4 x y) = eval4 x + eval4 y :=
  extendEval_add eval3 radical4 add3 eval3_add x y
private theorem eval4_neg (x : K4) : eval4 (neg4 x) = -eval4 x :=
  extendEval_neg eval3 radical4 neg3 eval3_neg x
private theorem eval4_mul (x y : K4) : eval4 (mul4 x y) = eval4 x * eval4 y :=
  extendEval_mul eval3 radical4 add3 mul3 square4 radical4_sq eval3_add eval3_mul x y

abbrev Coordinates := K4 × K4

def add (x y : Coordinates) : Coordinates := (add4 x.1 y.1, add4 x.2 y.2)

def neg (x : Coordinates) : Coordinates := (neg4 x.1, neg4 x.2)

def sub (x y : Coordinates) : Coordinates := add x (neg y)

def conj (x : Coordinates) : Coordinates := (x.1, neg4 x.2)

def mul (x y : Coordinates) : Coordinates :=
  (add4 (mul4 x.1 y.1) (neg4 (mul4 x.2 y.2)),
    add4 (mul4 x.1 y.2) (mul4 x.2 y.1))

def squareNorm (x : Coordinates) : K4 := add4 (mul4 x.1 x.1) (mul4 x.2 x.2)

noncomputable def toComplex (x : Coordinates) : ℂ := ⟨eval4 x.1, eval4 x.2⟩

theorem toComplex_sub (x y : Coordinates) : toComplex (sub x y) = toComplex x - toComplex y := by
  apply Complex.ext <;> simp [toComplex, sub, add, neg, eval4_add, eval4_neg, sub_eq_add_neg]

theorem toComplex_conj (x : Coordinates) : toComplex (conj x) = star (toComplex x) := by
  apply Complex.ext <;> simp [toComplex, conj, eval4_neg]

theorem toComplex_mul (x y : Coordinates) : toComplex (mul x y) = toComplex x * toComplex y := by
  apply Complex.ext <;>
    simp [toComplex, mul, eval4_add, eval4_mul, eval4_neg, sub_eq_add_neg]

theorem eval_squareNorm (x : Coordinates) :
    eval4 (squareNorm x) = Complex.normSq (toComplex x) := by
  simp [Complex.normSq_apply, squareNorm, toComplex, eval4_add, eval4_mul]

end SnailCoordinates


namespace UnitDistanceCertificate

private def oriented (reverse : Bool) (z : ℂ) : ℂ :=
  if reverse then star z else z

theorem normSq_orientation (reverse : Bool) (z : ℂ) :
    Complex.normSq (oriented reverse z) = Complex.normSq z := by
  cases reverse <;> simp [oriented, Complex.normSq_apply]

theorem congruence_of_cross_products {V : Type*} [DecidableEq V] (p : V → ℂ)
    (S : Finset V) (σ : V → V) (i j : V) (reverse : Bool)
    (hne : oriented reverse (p j) - oriented reverse (p i) ≠ 0)
    (hnorm :
      Complex.normSq (p (σ j) - p (σ i)) =
      Complex.normSq (oriented reverse (p j) - oriented reverse (p i)))
    (hcross : ∀ k ∈ S,
      (p (σ j) - p (σ i)) * (oriented reverse (p k) - oriented reverse (p i)) =
      (p (σ k) - p (σ i)) * (oriented reverse (p j) - oriented reverse (p i))) :
    ∃ a b : ℂ, ‖a‖ = 1 ∧
      (S.image (fun k => a * p k + b) = (S.image σ).image p ∨
        S.image (fun k => a * star (p k) + b) = (S.image σ).image p) := by
  classical
  let x := fun k => oriented reverse (p k)
  let y := p ∘ σ
  let u := x j - x i
  let v := y j - y i
  let a := v / u
  let b := y i - a * x i
  have hu : u ≠ 0 := hne
  have hnorm' : ‖v‖ = ‖u‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
    change Complex.normSq v = Complex.normSq u at hnorm
    simpa only [Complex.normSq_eq_norm_sq] using hnorm
  have ha : ‖a‖ = 1 := by
    rw [show a = v / u from rfl, norm_div, hnorm', div_self (norm_ne_zero_iff.2 hu)]
  have hmap (k : V) (hk : k ∈ S) : a * x k + b = y k := by
    have h := hcross k hk
    change v * (x k - x i) = (y k - y i) * u at h
    have hh : a * (x k - x i) = y k - y i := by
      calc
        _ = (v * (x k - x i)) / u := by unfold a; ring
        _ = _ := (div_eq_iff hu).2 h
    unfold b
    linear_combination hh
  have himage : S.image (fun k => a * x k + b) = (S.image σ).image p := by
    rw [Finset.image_image]
    exact Finset.image_congr hmap
  refine ⟨a, b, ha, ?_⟩
  cases reverse
  · exact Or.inl (by simpa [x, oriented] using himage)
  · exact Or.inr (by simpa [x, oriented] using himage)

theorem edge_of_normSq_one {x y : ℂ} (h : Complex.normSq (x - y) = 1) : dist x y = 1 := by
  rw [dist_eq_norm]
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).1
  simpa only [Complex.normSq_eq_norm_sq, one_pow] using h

end UnitDistanceCertificate


namespace SnailCoordinates

private def scaleFactor : ℤ := 384

private def vertices : Fin 29 → Coordinates := ![
  (((((1600, 0), (0, -64)), ((-72, 0), (0, -8))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 728), (8, 0)), ((0, 64), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))),
  (((((1648, 0), (0, -64)), ((0, 0), (0, 0))), (((0, 1), (-3, 0)), ((0, 0), (0, 0)))), ((((0, 632), (56, 0)), ((0, 0), (0, 0))), (((9, 0), (0, -1)), ((0, 0), (0, 0))))),
  (((((1792, 0), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 768), (128, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))),
  (((((1728, 0), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 768), (192, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))),
  (((((1504, 0), (0, -32)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 736), (32, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))),
  (((((1824, 0), (0, -32)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 736), (96, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))),
  (((((1760, 0), (0, -32)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 736), (160, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))),
  (((((2144, 0), (0, -32)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 736), (160, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))),
  (((((1952, 0), (0, -32)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 928), (160, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))),
  (((((1888, 0), (0, -32)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 544), (224, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))),
  (((((2080, 0), (0, -32)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 736), (224, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))),
  (((((1888, 0), (0, -32)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 928), (224, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))),
  (((((2048, 0), (0, -64)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 896), (64, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))),
  (((((2176, 0), (0, -64)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 704), (128, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))),
  (((((1600, 0), (0, -64)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 896), (128, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))),
  (((((1984, 0), (0, -64)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 896), (128, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))),
  (((((2112, 0), (0, -64)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 704), (192, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))),
  (((((1920, 0), (0, -64)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 896), (192, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))),
  (((((1664, 0), (0, -64)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 704), (256, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))),
  (((((1856, 0), (0, -64)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 896), (256, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))),
  (((((1984, 0), (0, -64)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 704), (320, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))),
  (((((1952, 0), (0, -96)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 480), (160, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))),
  (((((1760, 0), (0, -96)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 672), (160, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))),
  (((((2144, 0), (0, -96)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 672), (160, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))),
  (((((1696, 0), (0, -96)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 672), (224, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))),
  (((((2080, 0), (0, -96)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 672), (224, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))),
  (((((1888, 0), (0, -96)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 864), (224, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))),
  (((((2272, 0), (0, -96)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 864), (224, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))),
  (((((1984, 0), (0, -128)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 832), (128, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))))]

private def edges : List (Fin 29 × Fin 29) := [(0, 4), (1, 4), (2, 8), (3, 5), (3, 11), (4, 5), (5, 7), (5, 15), (6, 7), (6, 8), (6, 10), (6, 14), (6, 17), (6, 18), (6, 22), (7, 8), (7, 15), (7, 23), (8, 12), (8, 19), (9, 10), (10, 11), (10, 13), (10, 17), (10, 20), (10, 25), (11, 15), (11, 26), (13, 15), (13, 25), (14, 15), (14, 17), (15, 26), (15, 28), (16, 17), (16, 27), (18, 19), (18, 20), (18, 22), (20, 25), (21, 22), (21, 23), (22, 23), (22, 25), (23, 28), (24, 25), (24, 26), (25, 26), (25, 27), (26, 27), (26, 28)]

end SnailCoordinates


namespace SnailCoordinates

private def Encloses (a : ℚ × ℚ) (x : ℝ) : Prop :=
  (a.1 : ℝ) ≤ x ∧ x ≤ (a.2 : ℝ)

private def extendBounds {K : Type} (bounds : K → ℚ × ℚ) (r : ℚ × ℚ)
    (x : K × K) : ℚ × ℚ :=
  ((bounds x.1).1 + min (r.1 * (bounds x.2).1) (r.2 * (bounds x.2).1),
    (bounds x.1).2 + max (r.1 * (bounds x.2).2) (r.2 * (bounds x.2).2))

private theorem extendBounds_sound {K : Type} (bounds : K → ℚ × ℚ) (e : K → ℝ)
    (H : ∀ a, Encloses (bounds a) (e a)) {r : ℝ} {s : ℚ × ℚ}
    (hr₀ : 0 ≤ r) (hr : Encloses s r) (x : K × K) :
    Encloses (extendBounds bounds s x) (extendEval e r x) := by
  obtain ⟨hl, hu⟩ := hr
  obtain ⟨h₁l, h₁u⟩ := H x.1
  obtain ⟨h₂l, h₂u⟩ := H x.2
  unfold Encloses extendBounds extendEval
  simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_min, Rat.cast_max]
  refine ⟨add_le_add h₁l ?_, add_le_add h₁u ?_⟩
  · refine le_trans ?_ (mul_le_mul_of_nonneg_left h₂l hr₀)
    by_cases ha : 0 ≤ ((bounds x.2).1 : ℝ)
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_right hl ha)
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_right hu (le_of_not_ge ha))
  · refine (mul_le_mul_of_nonneg_left h₂u hr₀).trans ?_
    by_cases ha : 0 ≤ ((bounds x.2).2 : ℝ)
    · exact (mul_le_mul_of_nonneg_right hu ha).trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonpos_right hl (le_of_not_ge ha)).trans (le_max_left _ _)

private theorem sqrt_between {a b v : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h₁ : a^2 ≤ v) (h₂ : v ≤ b^2) : a ≤ Real.sqrt v ∧ Real.sqrt v ≤ b := by
  have hv : 0 ≤ v := (sq_nonneg a).trans h₁
  refine ⟨(sq_le_sq₀ ha (Real.sqrt_nonneg _)).1 ?_,
    (sq_le_sq₀ (Real.sqrt_nonneg _) hb).1 ?_⟩
  · simpa only [Real.sq_sqrt hv] using h₁
  · simpa only [Real.sq_sqrt hv] using h₂

private def root1Box : ℚ × ℚ := (17320/10000, 17321/10000)
private def root2Box : ℚ × ℚ := (33166/10000, 33167/10000)
private def root3Box : ℚ × ℚ := (22360/10000, 22361/10000)
private def root4Box : ℚ × ℚ := (416848/10000, 416852/10000)

private theorem root1Bound : Encloses root1Box radical1 := by
  norm_num [Encloses, root1Box, radical1]
  exact sqrt_between (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem root2Bound : Encloses root2Box radical2 := by
  norm_num [Encloses, root2Box, radical2]
  exact sqrt_between (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem root3Bound : Encloses root3Box radical3 := by
  norm_num [Encloses, root3Box, radical3]
  exact sqrt_between (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem root4Bound : Encloses root4Box radical4 := by
  have hmul : radical1 * radical2 = Real.sqrt 33 := by
    rw [radical1, radical2, ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have hx : (574456/100000 : ℝ) ≤ Real.sqrt 33 ∧ Real.sqrt 33 ≤ (574457/100000 : ℝ) :=
    sqrt_between (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold Encloses root4Box radical4
  push_cast
  rw [mul_assoc, hmul]
  exact sqrt_between (by norm_num) (by norm_num)
    (by linarith only [hx.1]) (by linarith only [hx.2])

private def bounds0 (r : ℤ) : ℚ × ℚ := (r, r)

private theorem bounds0_sound (r : ℤ) : Encloses (bounds0 r) (eval0 r) := by
  simp [bounds0, Encloses, eval0]

private def bounds1 := extendBounds (K := K0) bounds0 root1Box

private theorem bounds1_sound (v : K1) : Encloses (bounds1 v) (eval1 v) :=
  extendBounds_sound _ _ bounds0_sound (by unfold radical1; positivity) root1Bound v

private def bounds2 := extendBounds (K := K1) bounds1 root2Box

private theorem bounds2_sound (v : K2) : Encloses (bounds2 v) (eval2 v) :=
  extendBounds_sound _ _ bounds1_sound (by unfold radical2; positivity) root2Bound v

private def bounds3 := extendBounds (K := K2) bounds2 root3Box

private theorem bounds3_sound (v : K3) : Encloses (bounds3 v) (eval3 v) :=
  extendBounds_sound _ _ bounds2_sound (by unfold radical3; positivity) root3Bound v

private def bounds4 := extendBounds (K := K3) bounds3 root4Box

private theorem bounds4_sound (v : K4) : Encloses (bounds4 v) (eval4 v) :=
  extendBounds_sound _ _ bounds3_sound (by unfold radical4; positivity) root4Bound v

private def edgeCheck (e : Fin 29 × Fin 29) : Bool :=
  decide (squareNorm (sub (vertices e.1) (vertices e.2)) = int4 (scaleFactor^2))

set_option maxHeartbeats 0 in
private theorem edgeAudit : edges.all edgeCheck = true := by
  decide +kernel

theorem edge_dist {i j : Fin 29} (h : (i,j) ∈ edges) :
    dist (toComplex (vertices i) / 384) (toComplex (vertices j) / 384) = 1 := by
  have hcheck := List.all_eq_true.1 edgeAudit _ h
  have hr := congrArg eval4 (of_decide_eq_true hcheck)
  rw [eval_squareNorm, toComplex_sub, eval4_int, Complex.normSq_eq_norm_sq] at hr
  have hs : ‖toComplex (vertices i) - toComplex (vertices j)‖^2 = (384 : ℝ)^2 := by
    norm_num [scaleFactor] at hr ⊢
    exact hr
  have he := (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 384)).1 hs
  rw [dist_eq_norm, ← sub_div, norm_div, he]
  norm_num

private structure Motion where
  reflect : Bool
  source : Fin 29 × Fin 29
  target : Fin 29 × Fin 29
  pairs : List (Fin 29 × Fin 29)

private def transformed (m : Motion) (i : Fin 29) : Coordinates :=
  if m.reflect then conj (vertices i) else vertices i

private def u (m : Motion) : Coordinates :=
  sub (transformed m m.source.2) (transformed m m.source.1)

private def v (m : Motion) : Coordinates :=
  sub (vertices m.target.2) (vertices m.target.1)

private def motionCheck (m : Motion) : Bool :=
  decide (0 < (bounds4 (squareNorm (u m))).1 ∧ squareNorm (u m) = squareNorm (v m)) &&
    m.pairs.all (fun e =>
      let lhs := mul (v m) (sub (transformed m e.1) (transformed m m.source.1))
      let rhs := mul (sub (vertices e.2) (vertices m.target.1)) (u m)
      decide (lhs.1 = rhs.1) && decide (lhs.2 = rhs.2))

end SnailCoordinates


namespace SnailCoordinates

private def ms0 : List Motion := [
  ⟨false, (2, 7), (20, 19), [(2, 20), (7, 19), (8, 18), (9, 27), (10, 26), (11, 24), (13, 11), (14, 9), (16, 17), (18, 23), (19, 22), (20, 28), (22, 7), (23, 8), (24, 13), (25, 15), (27, 14), (28, 2)]⟩,
  ⟨true, (2, 3), (24, 18), [(2, 24), (3, 18), (4, 21), (5, 22), (8, 26), (11, 19), (12, 28), (14, 16), (16, 14), (17, 17), (18, 3), (19, 11), (21, 4), (22, 5), (24, 2), (26, 8), (28, 12)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg0 : PLift (ms0.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms1 : List Motion := [
  ⟨true, (2, 3), (23, 25), [(2, 23), (3, 25), (5, 13), (6, 16), (9, 9), (11, 26), (12, 12), (13, 5), (15, 15), (16, 6), (17, 17), (19, 19), (23, 2), (25, 3), (26, 11)]⟩,
  ⟨true, (2, 6), (12, 15), [(2, 12), (6, 15), (7, 5), (9, 16), (13, 2), (16, 6), (17, 14), (18, 26), (20, 24), (22, 11), (23, 3), (24, 19)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg1 : PLift (ms1.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms2 : List Motion := [
  ⟨true, (3, 5), (12, 8), [(3, 12), (5, 8), (6, 15), (7, 7), (8, 5), (10, 13), (12, 3), (13, 10), (14, 14), (15, 6), (16, 16), (18, 28), (22, 26), (25, 25), (26, 22), (28, 18)]⟩,
  ⟨true, (2, 3), (11, 8), [(2, 11), (3, 8), (5, 19), (6, 17), (8, 10), (11, 7), (12, 20), (16, 27), (17, 16), (19, 13), (24, 28), (26, 23)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg2 : PLift (ms2.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms3 : List Motion := [
  ⟨true, (2, 4), (14, 4), [(2, 14), (4, 4), (9, 28), (10, 26), (11, 11), (13, 24), (14, 2), (20, 27), (24, 13), (25, 25), (26, 10), (27, 20), (28, 9)]⟩,
  ⟨false, (2, 6), (12, 15), [(2, 12), (6, 15), (7, 13), (9, 6), (10, 7), (13, 23), (16, 16), (18, 11), (21, 24), (22, 26), (23, 25), (24, 19)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg3 : PLift (ms3.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms4 : List Motion := [
  ⟨true, (2, 5), (18, 24), [(2, 18), (5, 24), (7, 26), (9, 14), (10, 17), (11, 10), (15, 25), (17, 16), (18, 5), (19, 7), (23, 28), (26, 13)]⟩,
  ⟨true, (2, 5), (2, 6), [(2, 2), (5, 6), (6, 5), (7, 7), (9, 12), (12, 9), (13, 16), (16, 13), (21, 28), (23, 23), (28, 21)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg4 : PLift (ms4.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms5 : List Motion := [
  ⟨true, (2, 3), (8, 15), [(2, 8), (3, 15), (5, 11), (6, 17), (7, 10), (8, 6), (9, 27), (10, 16), (19, 22), (23, 20), (26, 24)]⟩,
  ⟨true, (2, 3), (2, 5), [(2, 2), (3, 5), (5, 3), (6, 6), (9, 16), (16, 9), (18, 22), (20, 21), (21, 20), (22, 18), (24, 24)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg5 : PLift (ms5.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms6 : List Motion := [
  ⟨true, (2, 9), (9, 2), [(2, 9), (9, 2), (11, 24), (13, 13), (14, 20), (15, 25), (20, 14), (24, 11), (25, 15), (26, 26), (27, 28), (28, 27)]⟩,
  ⟨true, (2, 3), (3, 2), [(2, 3), (3, 2), (6, 6), (7, 10), (9, 15), (10, 7), (15, 9), (16, 16), (22, 22), (23, 25), (25, 23)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg6 : PLift (ms6.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms7 : List Motion := [
  ⟨false, (6, 7), (27, 26), [(6, 27), (7, 26), (8, 25), (11, 23), (12, 20), (13, 19), (16, 17), (17, 16), (19, 13), (20, 12), (23, 11), (25, 8), (26, 7), (27, 6)]⟩,
  ⟨false, (2, 3), (2, 6), [(2, 2), (3, 6), (6, 5), (9, 13), (10, 15), (11, 14), (14, 4), (16, 12), (20, 28)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg7 : PLift (ms7.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms8 : List Motion := [
  ⟨false, (2, 5), (3, 2), [(2, 3), (5, 2), (6, 6), (7, 8), (9, 16), (10, 17), (16, 15), (17, 14), (18, 22), (23, 12)]⟩,
  ⟨false, (2, 7), (9, 16), [(2, 9), (7, 16), (10, 25), (11, 24), (12, 5), (13, 13), (16, 23), (17, 22), (27, 28)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg8 : PLift (ms8.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms9 : List Motion := [
  ⟨false, (2, 8), (4, 5), [(2, 4), (8, 5), (11, 2), (14, 14), (17, 6), (19, 3), (27, 9), (28, 24)]⟩,
  ⟨true, (2, 5), (12, 15), [(2, 12), (5, 15), (7, 13), (12, 6), (13, 16), (16, 23), (23, 25), (27, 21), (28, 24)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg9 : PLift (ms9.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms10 : List Motion := [
  ⟨true, (2, 3), (7, 16), [(2, 7), (3, 16), (6, 10), (8, 6), (10, 9), (14, 11), (15, 3), (18, 20), (19, 18)]⟩,
  ⟨false, (2, 3), (24, 22), [(2, 24), (3, 22), (4, 20), (5, 18), (9, 14), (14, 9), (18, 5), (20, 4), (22, 3), (24, 2)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg10 : PLift (ms10.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms11 : List Motion := [
  ⟨true, (2, 3), (7, 13), [(2, 7), (3, 13), (4, 11), (5, 10), (6, 16), (15, 9), (19, 21)]⟩,
  ⟨false, (2, 4), (24, 9), [(2, 24), (4, 9), (6, 22), (9, 28), (13, 14), (21, 12), (28, 4)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg11 : PLift (ms11.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms12 : List Motion := [
  ⟨true, (2, 4), (9, 20), [(2, 9), (4, 20), (13, 2), (14, 24), (27, 4), (28, 14)]⟩,
  ⟨false, (2, 3), (13, 7), [(2, 13), (3, 7), (4, 28), (5, 23), (6, 16), (9, 9), (14, 27), (24, 20)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg12 : PLift (ms12.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms13 : List Motion := [
  ⟨true, (2, 3), (16, 25), [(2, 16), (3, 25), (5, 10), (7, 9), (11, 24), (12, 3), (14, 19), (17, 18)]⟩,
  ⟨true, (2, 5), (23, 16), [(2, 23), (5, 16), (6, 25), (8, 22), (12, 6), (13, 9), (14, 26), (17, 24), (22, 20)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg13 : PLift (ms13.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms14 : List Motion := [
  ⟨true, (2, 5), (8, 17), [(2, 8), (5, 17), (6, 15), (8, 7), (13, 27), (15, 16), (17, 13), (22, 28)]⟩,
  ⟨true, (3, 5), (20, 25), [(3, 20), (5, 25), (7, 26), (10, 19), (15, 27), (16, 17), (21, 5), (22, 7), (23, 15), (25, 8)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg14 : PLift (ms14.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms15 : List Motion := [
  ⟨false, (3, 8), (5, 13), [(3, 5), (8, 13), (11, 7), (13, 21), (15, 23), (17, 16), (19, 10), (22, 24), (24, 18)]⟩,
  ⟨true, (2, 3), (13, 16), [(2, 13), (3, 16), (6, 7), (7, 5), (8, 15), (10, 6), (11, 17), (16, 2), (17, 8), (19, 11)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg15 : PLift (ms15.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms16 : List Motion := [
  ⟨true, (2, 5), (25, 16), [(2, 25), (5, 16), (8, 26), (10, 18), (12, 15), (13, 6), (15, 17), (17, 19), (23, 3)]⟩,
  ⟨true, (2, 6), (24, 22), [(2, 24), (6, 22), (8, 25), (11, 16), (14, 21), (16, 28), (17, 23), (19, 13), (20, 12)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg16 : PLift (ms16.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms17 : List Motion := [
  ⟨true, (2, 7), (9, 6), [(2, 9), (7, 6), (8, 10), (10, 3), (12, 13), (13, 5), (15, 7), (16, 2)]⟩,
  ⟨false, (2, 8), (14, 17), [(2, 14), (8, 17), (11, 11), (13, 24), (15, 26), (16, 18), (17, 19), (27, 20)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg17 : PLift (ms17.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms18 : List Motion := [
  ⟨false, (2, 8), (13, 10), [(2, 13), (8, 10), (12, 9), (16, 2), (19, 11), (21, 4), (24, 14)]⟩,
  ⟨true, (2, 3), (19, 11), [(2, 19), (3, 11), (4, 24), (5, 26), (6, 17), (14, 16), (15, 27), (24, 12)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg18 : PLift (ms18.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms19 : List Motion := [
  ⟨true, (2, 11), (4, 14), [(2, 4), (11, 14), (14, 2), (26, 15), (27, 28), (28, 13)]⟩,
  ⟨false, (2, 5), (12, 15), [(2, 12), (5, 15), (7, 5), (12, 16), (13, 6), (15, 7), (16, 2), (23, 3)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg19 : PLift (ms19.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms20 : List Motion := [
  ⟨false, (5, 13), (20, 19), [(5, 20), (13, 19), (15, 18), (16, 26), (17, 24), (22, 16), (23, 17), (24, 23), (26, 22), (28, 6)]⟩,
  ⟨false, (2, 9), (9, 23), [(2, 9), (9, 23), (10, 7), (13, 5), (15, 3), (24, 26), (25, 15), (26, 11)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg20 : PLift (ms20.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms21 : List Motion := [
  ⟨true, (2, 3), (22, 24), [(2, 22), (3, 24), (4, 13), (14, 17), (15, 14), (22, 3)]⟩,
  ⟨true, (3, 9), (3, 17), [(3, 3), (9, 17), (10, 10), (13, 20), (17, 9), (20, 13), (22, 24), (24, 22), (25, 25)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg21 : PLift (ms21.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms22 : List Motion := [
  ⟨true, (2, 5), (25, 23), [(2, 25), (5, 23), (6, 16), (8, 27), (9, 6), (10, 17), (16, 15), (23, 12)]⟩,
  ⟨true, (2, 5), (5, 6), [(2, 5), (5, 6), (9, 23), (13, 9), (22, 24)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg22 : PLift (ms22.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms23 : List Motion := [
  ⟨true, (2, 5), (11, 17), [(2, 11), (5, 17), (6, 8), (12, 27), (14, 7), (22, 12)]⟩,
  ⟨false, (3, 6), (2, 5), [(3, 2), (6, 5), (10, 7), (11, 8), (15, 12), (16, 13), (17, 15), (19, 17), (24, 22), (25, 23)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg23 : PLift (ms23.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms24 : List Motion := [
  ⟨true, (5, 6), (23, 25), [(5, 23), (6, 25), (7, 22), (10, 24), (14, 27), (17, 26), (18, 20), (22, 10), (23, 6), (26, 19), (28, 8)]⟩,
  ⟨true, (3, 6), (3, 6), [(3, 3), (6, 6), (7, 17), (8, 10), (10, 8), (12, 25), (15, 16), (16, 15), (17, 7), (25, 12)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg24 : PLift (ms24.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms25 : List Motion := [
  ⟨false, (5, 8), (9, 18), [(5, 9), (8, 18), (12, 6), (13, 16), (16, 25), (17, 24), (22, 21), (23, 23)]⟩,
  ⟨false, (2, 7), (9, 6), [(2, 9), (7, 6), (9, 13), (13, 2), (16, 5), (27, 4)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg25 : PLift (ms25.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms26 : List Motion := [
  ⟨false, (3, 5), (6, 22), [(3, 6), (5, 22), (8, 16), (10, 9), (11, 10), (14, 26), (15, 25), (26, 20)]⟩,
  ⟨false, (3, 10), (28, 22), [(3, 28), (10, 22), (11, 23), (16, 24), (17, 25), (18, 17), (19, 16), (20, 6), (24, 19), (25, 18)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg26 : PLift (ms26.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms27 : List Motion := [
  ⟨false, (2, 5), (25, 16), [(2, 25), (5, 16), (6, 23), (8, 22), (10, 28), (12, 6), (13, 15), (23, 12)]⟩,
  ⟨false, (3, 7), (9, 7), [(3, 9), (7, 7), (8, 6), (10, 16), (15, 5), (16, 13), (18, 21), (19, 22)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg27 : PLift (ms27.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms28 : List Motion := [
  ⟨true, (2, 5), (3, 6), [(2, 3), (5, 6), (6, 2), (7, 8), (12, 16), (13, 15), (15, 7), (23, 12)]⟩,
  ⟨true, (2, 7), (9, 16), [(2, 9), (7, 16), (9, 5), (10, 7), (13, 23), (16, 13)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg28 : PLift (ms28.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms29 : List Motion := [
  ⟨false, (2, 3), (15, 8), [(2, 15), (3, 8), (6, 17), (7, 16), (10, 10), (13, 25), (15, 27), (25, 20)]⟩,
  ⟨false, (3, 5), (25, 20), [(3, 25), (5, 20), (7, 18), (9, 17), (17, 9), (18, 7), (20, 5), (25, 3)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg29 : PLift (ms29.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms30 : List Motion := [
  ⟨false, (2, 3), (3, 6), [(2, 3), (3, 6), (6, 2), (19, 4)]⟩,
  ⟨true, (2, 3), (3, 6), [(2, 3), (3, 6), (10, 9), (18, 24)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg30 : PLift (ms30.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms31 : List Motion := [
  ⟨true, (2, 11), (4, 2), [(2, 4), (11, 2), (20, 13), (27, 9)]⟩,
  ⟨true, (2, 12), (5, 9), [(2, 5), (12, 9), (16, 23), (19, 26)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg31 : PLift (ms31.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms32 : List Motion := [
  ⟨false, (2, 5), (6, 5), [(2, 6), (5, 5), (7, 15), (8, 14), (9, 23), (13, 12)]⟩,
  ⟨true, (3, 6), (18, 24), [(3, 18), (6, 24), (10, 26), (17, 25), (19, 16), (20, 15), (25, 28), (26, 23)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg32 : PLift (ms32.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms33 : List Motion := [
  ⟨false, (6, 8), (10, 11), [(6, 10), (8, 11), (11, 19), (14, 6), (15, 8), (17, 17), (18, 25), (19, 26), (22, 13), (24, 23), (28, 12)]⟩,
  ⟨false, (6, 7), (25, 24), [(6, 25), (7, 24), (10, 22), (11, 21), (13, 18), (18, 13), (21, 11), (22, 10), (24, 7), (25, 6)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg33 : PLift (ms33.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms34 : List Motion := [
  ⟨false, (2, 3), (17, 8), [(2, 17), (3, 8), (5, 19), (6, 11), (8, 10), (10, 3), (12, 20)]⟩,
  ⟨false, (2, 8), (11, 26), [(2, 11), (8, 26), (12, 27), (16, 20), (19, 24), (24, 9)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg34 : PLift (ms34.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms35 : List Motion := [
  ⟨true, (2, 4), (13, 17), [(2, 13), (4, 17), (5, 16), (6, 23), (12, 9), (14, 22), (17, 21)]⟩,
  ⟨false, (5, 6), (2, 3), [(5, 2), (6, 3), (13, 7), (15, 8), (16, 10), (17, 11), (23, 16), (24, 18), (26, 19)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg35 : PLift (ms35.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms36 : List Motion := [
  ⟨false, (9, 13), (20, 11), [(9, 20), (13, 11), (16, 19), (21, 16), (23, 17), (24, 24), (25, 26), (28, 14)]⟩,
  ⟨false, (2, 3), (16, 13), [(2, 16), (3, 13), (5, 10), (6, 7), (7, 6), (10, 5), (13, 3), (16, 2)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg36 : PLift (ms36.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms37 : List Motion := [
  ⟨true, (3, 6), (8, 11), [(3, 8), (6, 11), (8, 3), (10, 10), (11, 6), (18, 26), (20, 25), (25, 20), (26, 18)]⟩,
  ⟨false, (3, 7), (27, 19), [(3, 27), (7, 19), (10, 17), (11, 16), (16, 11), (17, 10), (19, 7), (27, 3)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg37 : PLift (ms37.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms38 : List Motion := [
  ⟨true, (5, 6), (11, 8), [(5, 11), (6, 8), (14, 6), (15, 10), (17, 7), (18, 12), (23, 27), (26, 13), (28, 25)]⟩,
  ⟨false, (2, 9), (14, 18), [(2, 14), (9, 18), (10, 22), (24, 10), (25, 25), (26, 13)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg38 : PLift (ms38.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms39 : List Motion := [
  ⟨false, (3, 10), (12, 13), [(3, 12), (10, 13), (16, 23), (18, 17), (20, 10), (24, 26), (25, 25), (26, 27)]⟩,
  ⟨true, (2, 3), (7, 10), [(2, 7), (3, 10), (7, 2), (8, 8), (10, 3), (11, 11)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg39 : PLift (ms39.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms40 : List Motion := [
  ⟨false, (2, 3), (11, 17), [(2, 11), (3, 17), (6, 8), (11, 14), (14, 2), (18, 12)]⟩,
  ⟨false, (2, 3), (18, 24), [(2, 18), (3, 24), (16, 14), (22, 5)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg40 : PLift (ms40.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms41 : List Motion := [
  ⟨true, (2, 8), (18, 19), [(2, 18), (8, 19), (13, 14), (14, 10), (15, 17), (17, 11), (22, 2)]⟩,
  ⟨false, (2, 4), (26, 10), [(2, 26), (4, 10), (5, 17), (15, 14), (22, 12)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg41 : PLift (ms41.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms42 : List Motion := [
  ⟨false, (2, 5), (26, 19), [(2, 26), (5, 19), (6, 17), (10, 14), (14, 10), (17, 6), (19, 5), (26, 2)]⟩,
  ⟨true, (3, 6), (24, 22), [(3, 24), (6, 22), (11, 26), (14, 23), (15, 28), (18, 6), (19, 17), (24, 5), (26, 15)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg42 : PLift (ms42.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms43 : List Motion := [
  ⟨false, (5, 8), (27, 23), [(5, 27), (8, 23), (13, 17), (15, 16), (16, 15), (17, 13), (23, 8), (27, 5)]⟩,
  ⟨false, (9, 13), (28, 24), [(9, 28), (13, 24), (16, 22), (17, 21), (21, 17), (22, 16), (24, 13), (28, 9)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg43 : PLift (ms43.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms44 : List Motion := [
  ⟨true, (12, 13), (12, 13), [(12, 12), (13, 13), (16, 23), (17, 28), (22, 27), (23, 16), (25, 25), (27, 22), (28, 17)]⟩,
  ⟨true, (2, 10), (2, 15), [(2, 2), (10, 15), (11, 11), (13, 13), (15, 10), (27, 27)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg44 : PLift (ms44.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms45 : List Motion := [
  ⟨true, (2, 8), (3, 5), [(2, 3), (8, 5), (12, 15), (19, 4)]⟩,
  ⟨false, (2, 3), (10, 16), [(2, 10), (3, 16), (6, 7), (7, 8), (8, 6), (10, 15), (15, 2), (17, 5)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg45 : PLift (ms45.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms46 : List Motion := [
  ⟨false, (2, 12), (12, 23), [(2, 12), (12, 23), (16, 6), (27, 18)]⟩,
  ⟨false, (2, 3), (19, 26), [(2, 19), (3, 26), (5, 11), (6, 17), (14, 6), (17, 14), (24, 12)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg46 : PLift (ms46.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms47 : List Motion := [
  ⟨true, (3, 5), (28, 15), [(3, 28), (5, 15), (9, 25), (10, 22), (13, 6), (15, 14), (22, 19), (25, 18)]⟩,
  ⟨true, (4, 5), (8, 7), [(4, 8), (5, 7), (6, 13), (22, 25), (26, 21)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg47 : PLift (ms47.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms48 : List Motion := [
  ⟨true, (6, 7), (27, 16), [(6, 27), (7, 16), (10, 25), (12, 8), (13, 10), (15, 17), (17, 26), (25, 20), (27, 18)]⟩,
  ⟨true, (16, 19), (2, 4), [(16, 2), (19, 4), (21, 11), (23, 3), (24, 14), (25, 6)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg48 : PLift (ms48.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms49 : List Motion := [
  ⟨false, (2, 3), (2, 5), [(2, 2), (3, 5), (11, 4)]⟩,
  ⟨false, (2, 24), (2, 26), [(2, 2), (24, 26)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg49 : PLift (ms49.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms50 : List Motion := [
  ⟨false, (7, 9), (23, 15), [(7, 23), (9, 15), (10, 13), (13, 25), (16, 16), (21, 19), (25, 10)]⟩,
  ⟨false, (2, 25), (3, 23), [(2, 3), (25, 23), (27, 28)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg50 : PLift (ms50.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms51 : List Motion := [
  ⟨true, (2, 13), (6, 12), [(2, 6), (13, 12), (14, 19)]⟩,
  ⟨false, (2, 3), (7, 13), [(2, 7), (3, 13), (8, 5), (10, 12)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg51 : PLift (ms51.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms52 : List Motion := [
  ⟨false, (2, 3), (7, 16), [(2, 7), (3, 16), (6, 13), (8, 15), (15, 12), (19, 28)]⟩,
  ⟨true, (5, 9), (12, 23), [(5, 12), (9, 23), (13, 5), (21, 10), (22, 17), (23, 6), (24, 26)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg52 : PLift (ms52.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms53 : List Motion := [
  ⟨true, (2, 10), (10, 2), [(2, 10), (10, 2), (14, 26), (15, 15), (26, 14)]⟩,
  ⟨true, (2, 4), (13, 28), [(2, 13), (4, 28), (9, 9), (13, 2), (28, 4)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg53 : PLift (ms53.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms54 : List Motion := [
  ⟨false, (2, 11), (13, 17), [(2, 13), (11, 17), (14, 22), (15, 6), (26, 14)]⟩,
  ⟨false, (2, 10), (17, 18), [(2, 17), (10, 18), (11, 22), (13, 20), (14, 13), (15, 25)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg54 : PLift (ms54.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms55 : List Motion := [
  ⟨false, (2, 8), (18, 6), [(2, 18), (8, 6), (19, 7), (27, 12)]⟩,
  ⟨true, (2, 8), (28, 15), [(2, 28), (8, 15), (19, 7), (27, 3)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg55 : PLift (ms55.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms56 : List Motion := [
  ⟨true, (3, 6), (11, 19), [(3, 11), (6, 19), (11, 10), (14, 18), (15, 20), (19, 16), (26, 25)]⟩,
  ⟨false, (4, 7), (1, 25), [(4, 1), (7, 25)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg56 : PLift (ms56.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms57 : List Motion := [
  ⟨true, (4, 9), (12, 21), [(4, 12), (9, 21), (12, 4), (21, 9), (24, 24)]⟩,
  ⟨false, (5, 6), (25, 23), [(5, 25), (6, 23), (7, 22), (8, 21), (21, 8), (22, 7), (23, 6), (25, 5)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg57 : PLift (ms57.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms58 : List Motion := [
  ⟨false, (5, 12), (27, 17), [(5, 27), (12, 17), (14, 23), (17, 28), (28, 12)]⟩,
  ⟨false, (6, 7), (23, 21), [(6, 23), (7, 21), (18, 7), (21, 18), (24, 10), (25, 9)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg58 : PLift (ms58.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms59 : List Motion := [
  ⟨false, (7, 14), (0, 12), [(7, 0), (14, 12)]⟩,
  ⟨true, (7, 15), (21, 23), [(7, 21), (15, 23), (17, 25), (25, 9), (28, 7)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg59 : PLift (ms59.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms60 : List Motion := [
  ⟨true, (8, 12), (15, 11), [(8, 15), (12, 11), (15, 17), (16, 27), (19, 28), (27, 25)]⟩,
  ⟨false, (10, 13), (15, 26), [(10, 15), (13, 26), (15, 27), (16, 17), (23, 19), (25, 11), (27, 10)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg60 : PLift (ms60.all motionCheck = true) := ⟨by decide +kernel⟩

private theorem allConsChecked {m : List Motion} {ms : List (List Motion)}
    (hm : m.all motionCheck = true) (hms : ms.all (·.all motionCheck) = true) :
    (m :: ms).all (·.all motionCheck) = true := by
  rw [List.all_cons, hm, hms]
  rfl

private theorem mp0 : ms0.all motionCheck = true :=
  mg0.down

private theorem mp1 : ms1.all motionCheck = true :=
  mg1.down

private theorem mp2 : ms2.all motionCheck = true :=
  mg2.down

private theorem mp3 : ms3.all motionCheck = true :=
  mg3.down

private theorem mp4 : ms4.all motionCheck = true :=
  mg4.down

private theorem mp5 : ms5.all motionCheck = true :=
  mg5.down

private theorem mp6 : ms6.all motionCheck = true :=
  mg6.down

private theorem mp7 : ms7.all motionCheck = true :=
  mg7.down

private theorem mp8 : ms8.all motionCheck = true :=
  mg8.down

private theorem mp9 : ms9.all motionCheck = true :=
  mg9.down

private theorem mp10 : ms10.all motionCheck = true :=
  mg10.down

private theorem mp11 : ms11.all motionCheck = true :=
  mg11.down

private theorem mp12 : ms12.all motionCheck = true :=
  mg12.down

private theorem mp13 : ms13.all motionCheck = true :=
  mg13.down

private theorem mp14 : ms14.all motionCheck = true :=
  mg14.down

private theorem mp15 : ms15.all motionCheck = true :=
  mg15.down

private theorem mp16 : ms16.all motionCheck = true :=
  mg16.down

private theorem mp17 : ms17.all motionCheck = true :=
  mg17.down

private theorem mp18 : ms18.all motionCheck = true :=
  mg18.down

private theorem mp19 : ms19.all motionCheck = true :=
  mg19.down

private theorem mp20 : ms20.all motionCheck = true :=
  mg20.down

private theorem mp21 : ms21.all motionCheck = true :=
  mg21.down

private theorem mp22 : ms22.all motionCheck = true :=
  mg22.down

private theorem mp23 : ms23.all motionCheck = true :=
  mg23.down

private theorem mp24 : ms24.all motionCheck = true :=
  mg24.down

private theorem mp25 : ms25.all motionCheck = true :=
  mg25.down

private theorem mp26 : ms26.all motionCheck = true :=
  mg26.down

private theorem mp27 : ms27.all motionCheck = true :=
  mg27.down

private theorem mp28 : ms28.all motionCheck = true :=
  mg28.down

private theorem mp29 : ms29.all motionCheck = true :=
  mg29.down

private theorem mp30 : ms30.all motionCheck = true :=
  mg30.down

private theorem mp31 : ms31.all motionCheck = true :=
  mg31.down

private theorem mp32 : ms32.all motionCheck = true :=
  mg32.down

private theorem mp33 : ms33.all motionCheck = true :=
  mg33.down

private theorem mp34 : ms34.all motionCheck = true :=
  mg34.down

private theorem mp35 : ms35.all motionCheck = true :=
  mg35.down

private theorem mp36 : ms36.all motionCheck = true :=
  mg36.down

private theorem mp37 : ms37.all motionCheck = true :=
  mg37.down

private theorem mp38 : ms38.all motionCheck = true :=
  mg38.down

private theorem mp39 : ms39.all motionCheck = true :=
  mg39.down

private theorem mp40 : ms40.all motionCheck = true :=
  mg40.down

private theorem mp41 : ms41.all motionCheck = true :=
  mg41.down

private theorem mp42 : ms42.all motionCheck = true :=
  mg42.down

private theorem mp43 : ms43.all motionCheck = true :=
  mg43.down

private theorem mp44 : ms44.all motionCheck = true :=
  mg44.down

private theorem mp45 : ms45.all motionCheck = true :=
  mg45.down

private theorem mp46 : ms46.all motionCheck = true :=
  mg46.down

private theorem mp47 : ms47.all motionCheck = true :=
  mg47.down

private theorem mp48 : ms48.all motionCheck = true :=
  mg48.down

private theorem mp49 : ms49.all motionCheck = true :=
  mg49.down

private theorem mp50 : ms50.all motionCheck = true :=
  mg50.down

private theorem mp51 : ms51.all motionCheck = true :=
  mg51.down

private theorem mp52 : ms52.all motionCheck = true :=
  mg52.down

private theorem mp53 : ms53.all motionCheck = true :=
  mg53.down

private theorem mp54 : ms54.all motionCheck = true :=
  mg54.down

private theorem mp55 : ms55.all motionCheck = true :=
  mg55.down

private theorem mp56 : ms56.all motionCheck = true :=
  mg56.down

private theorem mp57 : ms57.all motionCheck = true :=
  mg57.down

private theorem mp58 : ms58.all motionCheck = true :=
  mg58.down

private theorem mp59 : ms59.all motionCheck = true :=
  mg59.down

private theorem mp60 : ms60.all motionCheck = true :=
  mg60.down

private def mb60 : List (List Motion) := ms60 :: []

private theorem mj60 : mb60.all (·.all motionCheck) = true :=
  allConsChecked mp60 rfl

private def mb59 : List (List Motion) := ms59 :: mb60

private theorem mj59 : mb59.all (·.all motionCheck) = true :=
  allConsChecked mp59 mj60

private def mb58 : List (List Motion) := ms58 :: mb59

private theorem mj58 : mb58.all (·.all motionCheck) = true :=
  allConsChecked mp58 mj59

private def mb57 : List (List Motion) := ms57 :: mb58

private theorem mj57 : mb57.all (·.all motionCheck) = true :=
  allConsChecked mp57 mj58

private def mb56 : List (List Motion) := ms56 :: mb57

private theorem mj56 : mb56.all (·.all motionCheck) = true :=
  allConsChecked mp56 mj57

private def mb55 : List (List Motion) := ms55 :: mb56

private theorem mj55 : mb55.all (·.all motionCheck) = true :=
  allConsChecked mp55 mj56

private def mb54 : List (List Motion) := ms54 :: mb55

private theorem mj54 : mb54.all (·.all motionCheck) = true :=
  allConsChecked mp54 mj55

private def mb53 : List (List Motion) := ms53 :: mb54

private theorem mj53 : mb53.all (·.all motionCheck) = true :=
  allConsChecked mp53 mj54

private def mb52 : List (List Motion) := ms52 :: mb53

private theorem mj52 : mb52.all (·.all motionCheck) = true :=
  allConsChecked mp52 mj53

private def mb51 : List (List Motion) := ms51 :: mb52

private theorem mj51 : mb51.all (·.all motionCheck) = true :=
  allConsChecked mp51 mj52

private def mb50 : List (List Motion) := ms50 :: mb51

private theorem mj50 : mb50.all (·.all motionCheck) = true :=
  allConsChecked mp50 mj51

private def mb49 : List (List Motion) := ms49 :: mb50

private theorem mj49 : mb49.all (·.all motionCheck) = true :=
  allConsChecked mp49 mj50

private def mb48 : List (List Motion) := ms48 :: mb49

private theorem mj48 : mb48.all (·.all motionCheck) = true :=
  allConsChecked mp48 mj49

private def mb47 : List (List Motion) := ms47 :: mb48

private theorem mj47 : mb47.all (·.all motionCheck) = true :=
  allConsChecked mp47 mj48

private def mb46 : List (List Motion) := ms46 :: mb47

private theorem mj46 : mb46.all (·.all motionCheck) = true :=
  allConsChecked mp46 mj47

private def mb45 : List (List Motion) := ms45 :: mb46

private theorem mj45 : mb45.all (·.all motionCheck) = true :=
  allConsChecked mp45 mj46

private def mb44 : List (List Motion) := ms44 :: mb45

private theorem mj44 : mb44.all (·.all motionCheck) = true :=
  allConsChecked mp44 mj45

private def mb43 : List (List Motion) := ms43 :: mb44

private theorem mj43 : mb43.all (·.all motionCheck) = true :=
  allConsChecked mp43 mj44

private def mb42 : List (List Motion) := ms42 :: mb43

private theorem mj42 : mb42.all (·.all motionCheck) = true :=
  allConsChecked mp42 mj43

private def mb41 : List (List Motion) := ms41 :: mb42

private theorem mj41 : mb41.all (·.all motionCheck) = true :=
  allConsChecked mp41 mj42

private def mb40 : List (List Motion) := ms40 :: mb41

private theorem mj40 : mb40.all (·.all motionCheck) = true :=
  allConsChecked mp40 mj41

private def mb39 : List (List Motion) := ms39 :: mb40

private theorem mj39 : mb39.all (·.all motionCheck) = true :=
  allConsChecked mp39 mj40

private def mb38 : List (List Motion) := ms38 :: mb39

private theorem mj38 : mb38.all (·.all motionCheck) = true :=
  allConsChecked mp38 mj39

private def mb37 : List (List Motion) := ms37 :: mb38

private theorem mj37 : mb37.all (·.all motionCheck) = true :=
  allConsChecked mp37 mj38

private def mb36 : List (List Motion) := ms36 :: mb37

private theorem mj36 : mb36.all (·.all motionCheck) = true :=
  allConsChecked mp36 mj37

private def mb35 : List (List Motion) := ms35 :: mb36

private theorem mj35 : mb35.all (·.all motionCheck) = true :=
  allConsChecked mp35 mj36

private def mb34 : List (List Motion) := ms34 :: mb35

private theorem mj34 : mb34.all (·.all motionCheck) = true :=
  allConsChecked mp34 mj35

private def mb33 : List (List Motion) := ms33 :: mb34

private theorem mj33 : mb33.all (·.all motionCheck) = true :=
  allConsChecked mp33 mj34

private def mb32 : List (List Motion) := ms32 :: mb33

private theorem mj32 : mb32.all (·.all motionCheck) = true :=
  allConsChecked mp32 mj33

private def mb31 : List (List Motion) := ms31 :: mb32

private theorem mj31 : mb31.all (·.all motionCheck) = true :=
  allConsChecked mp31 mj32

private def mb30 : List (List Motion) := ms30 :: mb31

private theorem mj30 : mb30.all (·.all motionCheck) = true :=
  allConsChecked mp30 mj31

private def mb29 : List (List Motion) := ms29 :: mb30

private theorem mj29 : mb29.all (·.all motionCheck) = true :=
  allConsChecked mp29 mj30

private def mb28 : List (List Motion) := ms28 :: mb29

private theorem mj28 : mb28.all (·.all motionCheck) = true :=
  allConsChecked mp28 mj29

private def mb27 : List (List Motion) := ms27 :: mb28

private theorem mj27 : mb27.all (·.all motionCheck) = true :=
  allConsChecked mp27 mj28

private def mb26 : List (List Motion) := ms26 :: mb27

private theorem mj26 : mb26.all (·.all motionCheck) = true :=
  allConsChecked mp26 mj27

private def mb25 : List (List Motion) := ms25 :: mb26

private theorem mj25 : mb25.all (·.all motionCheck) = true :=
  allConsChecked mp25 mj26

private def mb24 : List (List Motion) := ms24 :: mb25

private theorem mj24 : mb24.all (·.all motionCheck) = true :=
  allConsChecked mp24 mj25

private def mb23 : List (List Motion) := ms23 :: mb24

private theorem mj23 : mb23.all (·.all motionCheck) = true :=
  allConsChecked mp23 mj24

private def mb22 : List (List Motion) := ms22 :: mb23

private theorem mj22 : mb22.all (·.all motionCheck) = true :=
  allConsChecked mp22 mj23

private def mb21 : List (List Motion) := ms21 :: mb22

private theorem mj21 : mb21.all (·.all motionCheck) = true :=
  allConsChecked mp21 mj22

private def mb20 : List (List Motion) := ms20 :: mb21

private theorem mj20 : mb20.all (·.all motionCheck) = true :=
  allConsChecked mp20 mj21

private def mb19 : List (List Motion) := ms19 :: mb20

private theorem mj19 : mb19.all (·.all motionCheck) = true :=
  allConsChecked mp19 mj20

private def mb18 : List (List Motion) := ms18 :: mb19

private theorem mj18 : mb18.all (·.all motionCheck) = true :=
  allConsChecked mp18 mj19

private def mb17 : List (List Motion) := ms17 :: mb18

private theorem mj17 : mb17.all (·.all motionCheck) = true :=
  allConsChecked mp17 mj18

private def mb16 : List (List Motion) := ms16 :: mb17

private theorem mj16 : mb16.all (·.all motionCheck) = true :=
  allConsChecked mp16 mj17

private def mb15 : List (List Motion) := ms15 :: mb16

private theorem mj15 : mb15.all (·.all motionCheck) = true :=
  allConsChecked mp15 mj16

private def mb14 : List (List Motion) := ms14 :: mb15

private theorem mj14 : mb14.all (·.all motionCheck) = true :=
  allConsChecked mp14 mj15

private def mb13 : List (List Motion) := ms13 :: mb14

private theorem mj13 : mb13.all (·.all motionCheck) = true :=
  allConsChecked mp13 mj14

private def mb12 : List (List Motion) := ms12 :: mb13

private theorem mj12 : mb12.all (·.all motionCheck) = true :=
  allConsChecked mp12 mj13

private def mb11 : List (List Motion) := ms11 :: mb12

private theorem mj11 : mb11.all (·.all motionCheck) = true :=
  allConsChecked mp11 mj12

private def mb10 : List (List Motion) := ms10 :: mb11

private theorem mj10 : mb10.all (·.all motionCheck) = true :=
  allConsChecked mp10 mj11

private def mb9 : List (List Motion) := ms9 :: mb10

private theorem mj9 : mb9.all (·.all motionCheck) = true :=
  allConsChecked mp9 mj10

private def mb8 : List (List Motion) := ms8 :: mb9

private theorem mj8 : mb8.all (·.all motionCheck) = true :=
  allConsChecked mp8 mj9

private def mb7 : List (List Motion) := ms7 :: mb8

private theorem mj7 : mb7.all (·.all motionCheck) = true :=
  allConsChecked mp7 mj8

private def mb6 : List (List Motion) := ms6 :: mb7

private theorem mj6 : mb6.all (·.all motionCheck) = true :=
  allConsChecked mp6 mj7

private def mb5 : List (List Motion) := ms5 :: mb6

private theorem mj5 : mb5.all (·.all motionCheck) = true :=
  allConsChecked mp5 mj6

private def mb4 : List (List Motion) := ms4 :: mb5

private theorem mj4 : mb4.all (·.all motionCheck) = true :=
  allConsChecked mp4 mj5

private def mb3 : List (List Motion) := ms3 :: mb4

private theorem mj3 : mb3.all (·.all motionCheck) = true :=
  allConsChecked mp3 mj4

private def mb2 : List (List Motion) := ms2 :: mb3

private theorem mj2 : mb2.all (·.all motionCheck) = true :=
  allConsChecked mp2 mj3

private def mb1 : List (List Motion) := ms1 :: mb2

private theorem mj1 : mb1.all (·.all motionCheck) = true :=
  allConsChecked mp1 mj2

private def mb0 : List (List Motion) := ms0 :: mb1

private theorem mj0 : mb0.all (·.all motionCheck) = true :=
  allConsChecked mp0 mj1

private def chunkedMotions : List Motion := mb0.flatten

private theorem chunkedAudit : chunkedMotions.all motionCheck = true := by
  rw [chunkedMotions, List.all_flatten]
  exact mj0

end SnailCoordinates

namespace SnailCoordinates

private theorem transformed_eval (m : Motion) (i : Fin 29) :
    toComplex (transformed m i) =
      UnitDistanceCertificate.oriented m.reflect (toComplex (vertices i)) := by
  cases h : m.reflect <;> simp [h, transformed, UnitDistanceCertificate.oriented, toComplex_conj]

private theorem motionCheck_sound (m : Motion) (hm : motionCheck m = true) :
    ∃ a b : ℂ, ‖a‖ = 1 ∧ ∀ e ∈ m.pairs,
      a * UnitDistanceCertificate.oriented m.reflect (toComplex (vertices e.1)) + b =
        toComplex (vertices e.2) := by
  let x (i : Fin 29) := toComplex (transformed m i)
  let y (i : Fin 29) := toComplex (vertices i)
  let c := toComplex (u m)
  let d := toComplex (v m)
  let a := d / c
  let b := y m.target.1 - a * x m.source.1
  simp only [motionCheck, Bool.and_eq_true] at hm
  have han : 0 < (bounds4 (squareNorm (u m))).1 ∧ squareNorm (u m) = squareNorm (v m) :=
    of_decide_eq_true hm.1
  have hcp : 0 < Complex.normSq c := by
    have hlo := (bounds4_sound (squareNorm (u m))).1
    rw [eval_squareNorm] at hlo
    exact (Rat.cast_pos.2 han.1).trans_le hlo
  have hcn : c ≠ 0 := Complex.normSq_pos.1 hcp
  have hnd : ‖d‖ = ‖c‖ := by
    have h := congrArg eval4 han.2.symm
    rw [eval_squareNorm, eval_squareNorm, Complex.normSq_eq_norm_sq,
      Complex.normSq_eq_norm_sq] at h
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h
  have ha : ‖a‖ = 1 := by
    dsimp [a]
    rw [norm_div, hnd, div_self (norm_ne_zero_iff.2 hcn)]
  refine ⟨a,b,ha,?_⟩
  intro e he
  rw [← transformed_eval]
  change a * x e.1 + b = y e.2
  have hraw := List.all_eq_true.1 hm.2 e he
  simp only [Bool.and_eq_true] at hraw
  have heq :
      mul (v m) (sub (transformed m e.1) (transformed m m.source.1)) =
      mul (sub (vertices e.2) (vertices m.target.1)) (u m) :=
    Prod.ext (of_decide_eq_true hraw.1) (of_decide_eq_true hraw.2)
  have heq' := congrArg toComplex heq
  rw [toComplex_mul, toComplex_mul, toComplex_sub, toComplex_sub] at heq'
  change d * (x e.1 - x m.source.1) = (y e.2 - y m.target.1) * c at heq'
  have hs : a * (x e.1 - x m.source.1) = y e.2 - y m.target.1 := by
    calc
      _ = (d * (x e.1 - x m.source.1)) / c := by unfold a; ring
      _ = _ := (div_eq_iff hcn).2 heq'
  unfold b
  linear_combination hs

end SnailCoordinates


namespace SnailCoordinates

private noncomputable def point (i : Fin 29) : ℂ := toComplex (vertices i) / 384

private theorem scaled_orientation (reverse : Bool) (z : ℂ) :
    UnitDistanceCertificate.oriented reverse z / 384 =
      UnitDistanceCertificate.oriented reverse (z / 384) := by
  cases reverse <;> simp [UnitDistanceCertificate.oriented]

private theorem scaledMotion_sound (m : Motion) (hm : motionCheck m = true) :
    ∃ a b : ℂ, ‖a‖ = 1 ∧ ∀ e ∈ m.pairs,
      a * UnitDistanceCertificate.oriented m.reflect (point e.1) + b = point e.2 := by
  obtain ⟨a, b, ha, hab⟩ := motionCheck_sound m hm
  refine ⟨a, b / 384, ha, ?_⟩
  intro e he
  have h := congrArg (fun z : ℂ => z / 384) (hab e he)
  change (_ * _ + _) / (384 : ℂ) = point e.2 at h
  rwa [add_div, mul_div_assoc, scaled_orientation] at h

private def targetSubset (m : Motion) (s : Finset (Fin 29)) : Finset (Fin 29) :=
  (m.pairs.toFinset.filter fun e => e.1 ∈ s).image Prod.snd

private theorem targetSubset_congr (m : Motion) (hm : motionCheck m = true)
    (s : Finset (Fin 29)) (hs : ∀ i ∈ s, ∃ j, (i, j) ∈ m.pairs) :
    ∃ a b : ℂ, ‖a‖ = 1 ∧
      ((s.image fun i => a * point i + b) = (targetSubset m s).image point ∨
       (s.image fun i => a * star (point i) + b) = (targetSubset m s).image point) := by
  obtain ⟨a, b, ha, hab⟩ := scaledMotion_sound m hm
  have ht : (s.image fun i => a * UnitDistanceCertificate.oriented m.reflect (point i) + b)
        = (targetSubset m s).image point := by
    ext z
    constructor
    · intro hz
      obtain ⟨i, hi, hiz⟩ := Finset.mem_image.1 hz
      obtain ⟨j, hj⟩ := hs i hi
      have hab' := hab (i,j) hj
      exact Finset.mem_image.2 ⟨j, Finset.mem_image.2
        ⟨(i,j), Finset.mem_filter.2 ⟨List.mem_toFinset.2 hj, hi⟩, rfl⟩,
        hab'.symm.trans hiz⟩
    · intro hz
      obtain ⟨j, hj, hjz⟩ := Finset.mem_image.1 hz
      obtain ⟨e, he, hej⟩ := Finset.mem_image.1 hj
      obtain ⟨he, hei⟩ := Finset.mem_filter.1 he
      exact Finset.mem_image.2 ⟨e.1, hei, (hab e (List.mem_toFinset.1 he)).trans
        ((congrArg point hej).trans hjz)⟩
  refine ⟨a, b, ha, ?_⟩
  cases hr : m.reflect
  · exact Or.inl (by simpa [hr, UnitDistanceCertificate.oriented] using ht)
  · exact Or.inr (by simpa [hr, UnitDistanceCertificate.oriented] using ht)

end SnailCoordinates


namespace SnailCoordinates

private abbrev CertificateRow := ℤ × ℕ × ℕ
private abbrev ProofRow := ℤ × Finset (Fin 29) × Finset (Fin 29)

private def maskSet (mask : ℕ) : Finset (Fin 29) :=
  Finset.univ.filter fun i => mask.testBit i

private theorem mem_maskSet (mask : ℕ) (i : Fin 29) :
    i ∈ maskSet mask ↔ mask.testBit i = true := by
  simp [maskSet]

private def pairMask {α : Type} (use : α → Bool) (index : α → ℕ) : List α → ℕ
  | [] => 0
  | x :: xs => (if use x then 2^(index x) else 0) ||| pairMask use index xs

private theorem testBit_pairMask {α : Type} (use : α → Bool) (index : α → ℕ)
    (xs : List α) (k : ℕ) :
    (pairMask use index xs).testBit k = true ↔ ∃ x ∈ xs, use x = true ∧ index x = k := by
  induction xs with
  | nil => simp [pairMask]
  | cons x xs ih =>
    simp only [pairMask, Nat.testBit_or, Bool.or_eq_true, ih, List.mem_cons, exists_eq_or_imp]
    cases he : use x <;> simp [Nat.testBit_two_pow]

private def sourceMask (m : Motion) : ℕ :=
  pairMask (fun _ => true) (fun e => e.1.val) m.pairs

private def targetMask (m : Motion) (s : ℕ) : ℕ :=
  pairMask (fun e => s.testBit e.1.val) (fun e => e.2.val) m.pairs

private def motionRow (m : Motion) (src : ℕ × ℤ) : CertificateRow :=
  let s := src.1 &&& sourceMask m
  (src.2, s, targetMask m s)

private def proofRow (r : CertificateRow) : ProofRow :=
  (r.1, maskSet r.2.1, maskSet r.2.2)

private def Congruent (r : ProofRow) : Prop :=
  ∃ a b : ℂ, ‖a‖ = 1 ∧
    ((r.2.1.image fun i => a * point i + b) = r.2.2.image point ∨
      (r.2.1.image fun i => a * star (point i) + b) = r.2.2.image point)

private theorem maskSet_targetMask (m : Motion) (s : ℕ) :
    maskSet (targetMask m s) = targetSubset m (maskSet s) := by
  ext j
  rw [mem_maskSet, targetMask, testBit_pairMask]
  constructor
  · rintro ⟨e, he, hs, hj⟩
    refine Finset.mem_image.2 ⟨e, Finset.mem_filter.2 ⟨List.mem_toFinset.2 he, ?_⟩, Fin.ext hj⟩
    exact (mem_maskSet s e.1).2 hs
  · intro hj
    obtain ⟨e, he, h⟩ := Finset.mem_image.1 hj
    obtain ⟨he, hs⟩ := Finset.mem_filter.1 he
    exact ⟨e, List.mem_toFinset.1 he, (mem_maskSet s e.1).1 hs, congrArg Fin.val h⟩

private theorem motionRow_congr (m : Motion) (hm : motionCheck m = true) (r : ℕ × ℤ) :
    Congruent (proofRow (motionRow m r)) := by
  let s := r.1 &&& sourceMask m
  change Congruent (r.2, maskSet s, maskSet (targetMask m s))
  rw [maskSet_targetMask]
  apply targetSubset_congr m hm
  intro i hi
  have hbit : (sourceMask m).testBit i = true := by
    have hv := (mem_maskSet s i).1 hi
    rw [show s = r.1 &&& sourceMask m from rfl, Nat.testBit_and, Bool.and_eq_true] at hv
    exact hv.2
  rw [sourceMask, testBit_pairMask] at hbit
  obtain ⟨e, he, _, hi⟩ := hbit
  have heq : e.1 = i := Fin.ext hi
  exact ⟨e.2, by simpa only [← heq] using he⟩

private def singletonRow (r : ℤ × Fin 29 × Fin 29) : CertificateRow :=
  (r.1, 2^(r.2.1.val), 2^(r.2.2.val))

private theorem maskSet_singleton (i : Fin 29) : maskSet (2^i.val) = {i} := by
  ext j
  rw [mem_maskSet, Nat.testBit_two_pow, decide_eq_true_eq, Finset.mem_singleton]
  constructor
  · intro h
    exact Fin.ext h.symm
  · rintro rfl
    rfl

private theorem singletonRow_congr (r : ℤ × Fin 29 × Fin 29) :
    Congruent (proofRow (singletonRow r)) := by
  refine ⟨1, point r.2.2 - point r.2.1, norm_one, Or.inl ?_⟩
  change (maskSet (2^r.2.1.val)).image _ = (maskSet (2^r.2.2.val)).image _
  rw [maskSet_singleton, maskSet_singleton]
  simp [sub_eq_add_neg, add_comm]

end SnailCoordinates


namespace SnailCoordinates

private theorem pairMask_lt {α : Type} (use : α → Bool) (idx : α → ℕ)
    (xs : List α) (n : ℕ) (h : ∀ x ∈ xs, idx x < n) :
    pairMask use idx xs < 2^n := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  cases hb : (pairMask use idx xs).testBit j
  · rfl
  · obtain ⟨x, hx, _, he⟩ := (testBit_pairMask use idx xs j).1 hb
    exact False.elim (by have hlt := h x hx; omega)

private def BoundedRow (r : CertificateRow) : Prop :=
  r.2.1 < 2^29 ∧ r.2.2 < 2^29

private theorem motionRow_bounded (m : Motion) (r : ℕ × ℤ) : BoundedRow (motionRow m r) := by
  have h : sourceMask m < 2^29 := pairMask_lt _ _ _ _ (fun e _ => e.1.isLt)
  constructor
  · change r.1 &&& sourceMask m < 2^29
    exact Nat.and_le_right.trans_lt h
  · exact pairMask_lt _ _ _ _ (fun e _ => e.2.isLt)

private theorem singletonRow_bounded (r : ℤ × Fin 29 × Fin 29) :
    BoundedRow (singletonRow r) :=
  ⟨Nat.pow_lt_pow_right (by decide : 1 < 2) r.2.1.isLt,
    Nat.pow_lt_pow_right (by decide : 1 < 2) r.2.2.isLt⟩

private def maskOf (I : Finset (Fin 29)) : ℕ :=
  ∑ j ∈ I.image Fin.val, 2^j

private theorem testBit_maskOf (I : Finset (Fin 29)) (i : ℕ) :
    (maskOf I).testBit i = true ↔ ∃ j ∈ I, (j : ℕ) = i := by
  rw [← Nat.mem_bitIndices, ← List.mem_toFinset, maskOf, Finset.toFinset_bitIndices_sum_two_pow]
  exact Finset.mem_image

private theorem testBit_maskOf_fin (I : Finset (Fin 29)) (i : Fin 29) :
    (maskOf I).testBit i = true ↔ i ∈ I := by
  rw [testBit_maskOf]
  constructor
  · rintro ⟨j, hj, he⟩
    rwa [← Fin.ext he]
  · exact fun h => ⟨i, h, rfl⟩

private theorem maskOf_lt (I : Finset (Fin 29)) : maskOf I < 2^29 := by
  apply Nat.lt_pow_two_of_testBit
  intro k hk
  cases hb : (maskOf I).testBit k
  · rfl
  · obtain ⟨j, _, hj⟩ := (testBit_maskOf I k).1 hb
    exact False.elim (by have hj' := j.isLt; omega)

private theorem submask_iff_subset (I : Finset (Fin 29)) (s : ℕ) (hs : s < 2^29) :
    UnitDistancePacked.submask s (maskOf I) ↔ maskSet s ⊆ I := by
  rw [UnitDistancePacked.submask_iff]
  constructor
  · intro h i hi
    exact (testBit_maskOf_fin I i).1 (h _ ((mem_maskSet s i).1 hi))
  · intro h k hb
    have hk0 := Nat.ge_two_pow_of_testBit hb
    have hk : k < 29 := by
      by_contra hn
      have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_not_gt hn)
      omega
    exact (testBit_maskOf_fin I ⟨k,hk⟩).2 (h ((mem_maskSet s ⟨k,hk⟩).2 hb))

private def rowTerms (r : CertificateRow) : UnitDistancePacked.Terms :=
  [(r.2.1, r.1), (r.2.2, -r.1)]

private theorem score_rowTerms (I : Finset (Fin 29)) (r : CertificateRow) (h : BoundedRow r) :
    UnitDistancePacked.score (maskOf I) (rowTerms r) =
      r.1 * ((if (proofRow r).2.1 ⊆ I then 1 else 0) -
             (if (proofRow r).2.2 ⊆ I then 1 else 0)) := by
  unfold UnitDistancePacked.score rowTerms proofRow
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    submask_iff_subset I _ h.1, submask_iff_subset I _ h.2]
  split_ifs <;> ring

private theorem score_rows (I : Finset (Fin 29)) (rows : List CertificateRow)
    (h : ∀ r ∈ rows, BoundedRow r) :
    UnitDistancePacked.score (maskOf I) (rows.flatMap rowTerms) =
      ((rows.map proofRow).map fun r => r.1 *
        ((if r.2.1 ⊆ I then 1 else 0) - (if r.2.2 ⊆ I then 1 else 0))).sum := by
  induction rows with
  | nil => rfl
  | cons r rs ih =>
    have h₁ := score_rowTerms I r (h r List.mem_cons_self)
    have h₂ := ih (fun r hr => h r (List.mem_cons_of_mem _ hr))
    simp only [List.flatMap_cons, List.map_cons, List.sum_cons]
    rw [show UnitDistancePacked.score (maskOf I) (rowTerms r ++ rs.flatMap rowTerms) =
      UnitDistancePacked.score (maskOf I) (rowTerms r) +
      UnitDistancePacked.score (maskOf I) (rs.flatMap rowTerms) by
        simp [UnitDistancePacked.score], h₁, h₂]
    rfl

private def edgeMask (i : ℕ) : ℕ :=
  pairMask (fun e => decide (e.1.val = i)) (fun e => e.2.val) (edges ++ edges.map Prod.swap)

private theorem edgeMask_dist {i j : ℕ} (he : (edgeMask i).testBit j = true) :
    ∃ a b : Fin 29, a.val = i ∧ b.val = j ∧ dist (point a) (point b) = 1 := by
  rw [edgeMask, testBit_pairMask] at he
  obtain ⟨e, he, hai, hbj⟩ := he
  refine ⟨e.1, e.2, of_decide_eq_true hai, hbj, ?_⟩
  rcases List.mem_append.1 he with h | h
  · exact edge_dist h
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h
    rw [dist_comm]
    exact edge_dist hr

private theorem maskOf_independent (I : Finset (Fin 29))
    (hI : ∀ i ∈ I, ∀ j ∈ I, dist (point i) (point j) ≠ 1) :
    UnitDistancePacked.Independent edgeMask (maskOf I) := by
  intro i j he hi
  obtain ⟨a, b, rfl, rfl, hab⟩ := edgeMask_dist he
  cases hj : (maskOf I).testBit b
  · rfl
  · exact False.elim
      (hI a ((testBit_maskOf_fin I a).1 hi) b ((testBit_maskOf_fin I b).1 hj) hab)

end SnailCoordinates


namespace SnailCoordinates

private def proofRows (rows : List CertificateRow) : List ProofRow :=
  rows.map proofRow

private def completeTerms (d n : ℤ) (rows : List CertificateRow) : UnitDistancePacked.Terms :=
  (0, d) :: (1, -n) :: rows.flatMap rowTerms

private theorem score_completeTerms (I : Finset (Fin 29)) (d n : ℤ)
    (rows : List CertificateRow) (hb : ∀ r ∈ rows, BoundedRow r) :
    UnitDistancePacked.score (maskOf I) (completeTerms d n rows) =
      d - n * (if (0 : Fin 29) ∈ I then 1 else 0) +
        ((proofRows rows).map fun r => r.1 *
          ((if r.2.1 ⊆ I then 1 else 0) - (if r.2.2 ⊆ I then 1 else 0))).sum := by
  have h₀ : UnitDistancePacked.submask 0 (maskOf I) := by
    exact Nat.zero_and _
  have h₁ : UnitDistancePacked.submask 1 (maskOf I) ↔ (0 : Fin 29) ∈ I := by
    have hs := submask_iff_subset I 1 (by decide)
    have ht : maskSet 1 = {(0 : Fin 29)} := by
      simpa using maskSet_singleton (0 : Fin 29)
    rwa [ht, Finset.singleton_subset_iff] at hs
  unfold completeTerms
  change (if UnitDistancePacked.submask 0 (maskOf I) then d else 0) +
      ((if UnitDistancePacked.submask 1 (maskOf I) then -n else 0) +
      UnitDistancePacked.score (maskOf I) (rows.flatMap rowTerms)) = _
  rw [if_pos h₀, score_rows I rows hb]
  by_cases hi : (0 : Fin 29) ∈ I
  · simp [hi, h₁, proofRows]
    ring
  · simp [hi, h₁, proofRows]

private theorem certificate_sound (d n : ℤ) (rows : List CertificateRow)
    (hb : ∀ r ∈ rows, BoundedRow r)
    (hc : ∀ r ∈ rows, Congruent (proofRow r))
    (hscore : ∀ I < 2^29, UnitDistancePacked.Independent edgeMask I →
      0 ≤ UnitDistancePacked.score I (completeTerms d n rows))
    (hd : 0 < d) (hn : 4*d < n) :
    ∃ p : Fin 29 → ℂ, ∃ C : List ProofRow,
      (∀ r ∈ C, ∃ a b : ℂ, ‖a‖ = 1 ∧
        (r.2.1.image (fun i ↦ a * p i + b) = r.2.2.image p ∨
          r.2.1.image (fun i ↦ a * star (p i) + b) = r.2.2.image p)) ∧
      ∃ D N : ℤ, 0 < D ∧ 4 * D < N ∧
        ∀ I : Finset (Fin 29), (∀ i ∈ I, ∀ j ∈ I, dist (p i) (p j) ≠ 1) →
          N * (if 0 ∈ I then 1 else 0) ≤ D +
            (C.map fun r ↦ r.1 * ((if r.2.1 ⊆ I then 1 else 0) -
                                          (if r.2.2 ⊆ I then 1 else 0))).sum := by
  classical
  refine ⟨point, proofRows rows, ?_, d, n, hd, hn, ?_⟩
  · intro r hr
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hr
    exact hc s hs
  · intro I hI
    have h := hscore (maskOf I) (maskOf_lt I) (maskOf_independent I hI)
    rw [score_completeTerms I d n rows hb] at h
    omega

end SnailCoordinates


namespace SnailCoordinates

private def rowFits (m : Motion) (r : CertificateRow) : Bool :=
  (r.2.1 &&& sourceMask m == r.2.1) && (targetMask m r.2.1 == r.2.2)

private theorem rowFits_congr (m : Motion) (hm : motionCheck m = true)
    (r : CertificateRow) (h : rowFits m r = true) : Congruent (proofRow r) := by
  rcases r with ⟨w, s, t⟩
  simp only [rowFits, Bool.and_eq_true, beq_iff_eq] at h
  have hrow : motionRow m (s, w) = (w, s, t) := by
    change (w, s &&& sourceMask m, targetMask m (s &&& sourceMask m)) = (w, s, t)
    rw [h.1, h.2]
  rw [← hrow]
  exact motionRow_congr m hm _

private theorem rowFits_bounded (m : Motion) (r : CertificateRow) (h : rowFits m r = true) :
    BoundedRow r := by
  rcases r with ⟨w, s, t⟩
  simp only [rowFits, Bool.and_eq_true, beq_iff_eq] at h
  have hrow : motionRow m (s, w) = (w, s, t) := by
    change (w, s &&& sourceMask m, targetMask m (s &&& sourceMask m)) = (w, s, t)
    rw [h.1, h.2]
  rw [← hrow]
  exact motionRow_bounded m _

end SnailCoordinates

namespace SnailCoordinates

private abbrev RowBlock := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ

private def decodeCoefficient (u : ℕ) : ℤ :=
  if u % 2 = 0 then Int.ofNat (u / 2) else -Int.ofNat (u / 2 + 1)

private def unpackRows (block : RowBlock) : List CertificateRow :=
  let (count, width, s, sw, t, tw, bits) := block
  (List.range count).map fun i =>
    let cell := (bits >>> (width * i)) % (2^width)
    (decodeCoefficient (cell >>> (sw+tw)), (cell % (2^sw)) <<< s, ((cell >>> sw) % (2^tw)) <<< t)

private def singletonRows : List (ℤ × Fin 29 × Fin 29) := [(-1, 0, 1), (-1242579097, 0, 2), (94697399, 0, 3), (1058199, 0, 4), (-116055208, 0, 5), (729913735, 0, 6), (621115501, 0, 7), (398544897, 0, 8), (-712410074, 0, 9), (998944164, 0, 10), (262434946, 0, 11), (-926345377, 0, 12), (340317927, 0, 13), (845804849, 0, 14), (659917025, 0, 15), (-427797197, 0, 16), (714582776, 0, 17), (365810760, 0, 18), (-685474022, 0, 19), (606649491, 0, 20), (-1026288, 0, 21), (358353054, 0, 22), (179965117, 0, 23), (-530297663, 0, 24), (741211147, 0, 25), (330612660, 0, 26), (97261952, 0, 27), (295505631, 0, 28)]

private def rowBlocks : List (List RowBlock) := [
  [(43, 69, 2, 23, 7, 18, 0x7f6ae8614822492007b850f86a40644a403d69bcdb1020d00201e02f2928c10680110efc2a22148024900075d5587e3451a09443a753fb91021600201cd9340e2d04492410e5642920680a4140871fab358b41524b0438616bf7502ad21a01be1b4618800480100def2d6ac682a416886e171f92b455a4b443691fe965201224001b3d5fb28d11682910d65b206c48a581280646c621ca055a43003134f810502b62180185335212905912c00c147069968ab496085f305c34a40644a002e020944500a9218016c8a7a62914692400b3826e4460a34028858db2366a41524b40296f49c35820d202213f992d1a915b12d009da4b6fd60a3482884df5a58aa446c4a402655448a58089208212f99f2dc910b0a1009554f11e480c854804a4072fa24112094023e2c7f95222d2520113b46faa910b1210088232dfc488d8148043328cc8a046c4200218dcf745828d208210b12a7e2d14692410856806b5482249280424249ff2052c214020ffd5985209224801), (91, 71, 2, 23, 7, 18, 0x1fa9b5dc040ab406007f535faa2810690000fdfea8691028d00a01fb715fee3045a02443ed3c5ecd4022482807d5aae100815b00c00fab4ec1d5029620a01f467d7a8241640b003dcbbe9844804810807b0a24862804490400f481ac151022d01201e8ce834c2045a02003cba16afd60ab4868878d702360915b02c00f19d8f9d5808920a21d81faa40a446c4a003aafa2c15400a4848074f153712814690400e993f42f120a905a01d2ff63fc341520b043a3c0085448ad8168073d6d855c811b08900e46174b1502b621a01c65dbd5b20024204038a4ed3f96002480087109a2412801490800e1ab58eb5a02925221c12c66c0a045a420037dd53e15608b484886ed317812911692800dd2f0f97102ad01a01b87f5f26a046c424036b057dad48a5892806d2490ff8901482900d97d242e9003211001a502162ab0152434434972c12d408348080688833230911b02800ce5dde2112216042019caa5cde241640b403370afe14600a4048866b613b12905492c00cd21a3dc5820d2002198438bc230012004432fd1684648ad856806534317c4811b08800ca34e3d11a20d0422194333b6b241642b40327e4c384402480280639693ef2910b12000c6c9a7eb1228d04a018a6ba8b62005202403102cbb3968834900861db79328804480500c2672612922b6158018385ace0b4012480430581b97548a3492805fa95491a810b10100bd4f2991920121420179cc17e6a40524a402ee6dfc48408d804005daf99308c15680d10baa777bf100a901a0173ff6152a012441402e63501b54004880805c82cda8a905912d00b8dc34d558009202216e9752062002400402d87391254002480805af94383a915692d00b5ae2cea5220d2400166f40e463455a0b442cd8dab74480c81480597e4e562915692c00b273eda25a0292502164343f2ea051a41402c5e2843e402484280587e5877c805908d00b0cf065b90216102015c773986a045a42402b83c6cfe48248528056df49978814b00500abdc1ef15209224a015723bc65240642a002a5c87f38480c8140054b85191ad10692110a8d40b5c5a22d250214eabe046a4024484029b9142b4602a40688534ce73a2804910400a61b68499003211201), (48, 73, 2, 23, 7, 20, 0xed65a4064911b0a880f3e28c1d1688349048739beed58a446c4a20383d745641820d00121b98b52a22800490080da2821652480c854406b25a7558a042c402034951a08c5002921101a49658b22911692880ce505627148024904065cfb2288300520224317e4c8e41223605101889375ea2901492880c1545ad50680a414485f4ebe958240520a202ebbc2284520322510175d6a7820910b02080b736402316002480485b2c5ce88a442c48202d10e5bfc920121410160246c460901902880adf209db0408580040546f94238a041a40202961da16c90236111014a7c14aa0c00480090a369b1a3040834004051b221d582002400202894e2eb412012041014320ddee4910b0a080a0cfbf3104883410404fde5a5682046c02202720ed0b4900121010136fae7c608004800809a3a20c91408b484404ca884288b4012482425c3c09b45822d211212bb8178648019088809369d4cd1408d8844048dc8c6a834012082423b2fbf5c5a029251211b1adabe0801900880864eb54d160834804842f41a1f82401208202169008ec50032211010b0a54a208014808808515997b1600a484484248d1e282045a0220200e2fe4c5220d24101), (96, 73, 2, 21, 7, 22, 0xf7cee04322411a2540fb8713d381202d14207c235e0e8ac016c2443d03ab0944402b41a01e71c9ee70b411b2450f344b2e985a00d9028791a160788804681403bbf901745480b65201dc6194760b005b0810ed18fff085008c8220747d81c6829056cb003a3b190aa16023208a1ce05e0c622401a2100e6819e4b91a00d10a872e6a0cacad046c9543946965860602b418a1c85c8b592b41192550e333959115a0ad96886f2bfeeecad016ca543793988da4482304a81bab7c32623001a0110db30c6c891200c10a06d4572ed828046c10036930b4840400b41001b2ceec462b411b2510d778ad3c91a02c14a86b6315064890560b5035753fc3c5402b61a01aafa9c9a23401a2110d4a0f55f0100ad060069608acd828016c20034ab03d2256803242a19ce0b03f22011a0540cdf5e9b30120ad16006682da894a9046495032da1f27c5482b65a0194c2f30b02015a0c40c9fc497d11802d048864647425c28056c31031f0de53a5602320aa18cbe652623415a2d10c20ca8bf15800d80885fd995d24a900648502f8f91a924682304aa17aacc0660a001b0000bcf29c4501202d14005ce3cfbc8890568b402e5f9dd5c5680b652216e46dc022a001b0100b6fae9d915808d82885a4af742c8c04681542ca59dfac4680b452216492a0722a411b2500b179a4150500ad8600583c1f028890168a402beeb52a416003600215ee18b2623011a0510aeb3779905200d900056d1c9f98a8046c1402b0bddb924400b012815812db7e0a411b2400ab1137d59180ad06a85552c0b2c8d0168a5429f3469be448034428149efd1ba0b015b0c10a480100d91a0ad16a851c905b182d046c9042805623ae4682344aa13ea38e2922011805409bdbe83991000d00a04d77e848488006005026aaec14a5680b252a134462489230118055098b73f4915a00d90884c24532e48c0060054257e0af625400b212812bb8298f03005a085095b2868105a02d940849c60f7e488056035024d6047cc4682344a21259644e10a00190040909b0e3911208d1280483940ab4a90164a5023ebbef4e56803642a11ebe356902005808408e42680d05a0ad9608454ea71d88c0568344229c7152646003402a110721a262a401b210087e7f02d01a0ad160842cb993b4ad0564b542154b6bc416803640210a7bc22203005a081082ba831d91802d04a840ed6d6180c05683042038bb57c0680b45021), (73, 75, 2, 23, 7, 22, 0x7c44e88b05a22d65021f601d55a22441a88403ea74bbd6140ab586207cd2f36742d14692450f3bdb7a19122ad45a81e723914e2a055ac3403cae8e3dc448ab5168078ab1ef9c8d146a2550ed40c61311a20d44221d33d53fa2b451ac9443a3dbeae6140a3582207371604748814680540e52e20b911822d41221ca3abbc323041a805438b7bc494560835808871216f54c8d106a2150e1ded8cb0522ad65801bc8e13c20a055ac30036e39f566168a3592286dac8e0aca9146b2540db40fb971182ad41a21ae1e5f9e0b041ac0043571f23ce048ab516206a9ed3f88a8146b0500d48b859385228d64881a0f579c303045a821433eda839c548a3592806755822ac8c156a0d50cdc2b11495828d20aa1980229b30a455acb1032c3a87dc0488b514006581e49e4ad14692550c73ef0d885028d2088187e0e0e623445a8a442ff99fab40688b514085f4a1c1942c14690450be1aea5791020d402817b748c8122041a00502f138a944168ab596085b85687e48815680d40b684423511022d412016a8f890f2b451ac9542c078ebd20408b40420580ce8254a911692940af4aa01f91220d4428154460e360b441ac8042a4a997f256083480a85474e8f248811680940a240701915a20d642213c84a6d20a451ac90027811e7cc14883590004e93368dc0c156a0c509c29b85315220d6420135554b820a041ac000262fee4c4440a3502804c42314b808156a0c0095f99dbb05028d60801296b43562a045ac24024f26a4dc1408b5840048fbfbca88d146a251091b3ea4895220d2428121e738a52a455a4b5023ef725dc168a35920846bea3e44a9146925408b62750311222d4520115404e0e22055a83402272745fe448a3512a04420e6ac808116a0800882b90ee85020d200810f51f11e2a041ac04021a21997446083500884116adf8889146a250081fbb64591a2ad45aa1), (41, 72, 2, 23, 8, 21, 0xf0c43824c804a10a81cf7d0e7c2911e65081cacf41b48901a05281c1590e742901a25081bfa47914c905a15a81b6d07354c805a11a81b1272fd80915e45801ac2418fc8810e402819ddb21388904a44a0197c78b182911e65001899ca95ca910e6428183f57024a904a24a81806923e82915e658017e97c54c2800a60081709da68c0811e410816a941fe88900a4420169b9b83c2805a61881679d9f880901a4500150694fc4c810e102814f8958cc2900a640814ee15d044815e118814e7dc7d48811e0128146159718a905a65a0142dbdefca810e6028141fa6e448900a0428141e798388905a45a0141c82cdc2811e6108141b095b88910e44201352b43fc8910e442812d4bbd648910e042812bbd9e444915e1588128710e48a800a6020128514f282900a64001274709bc2804a608812153ad0ca815e61a811a7340c4c911e1528118a06c382800a600011151ff748905a05a8102891c28a915e65a0100b775d88901a452010060a818a904a64a01), (46, 73, 2, 22, 8, 21, 0x3e827d8a82801cc2003ef4a5fe24400600281f22c1c0b2241722d40f8221c7881203814207a6027da48804c01503c3e21e244400e41201e0346aaf2240722940eed2e95f010039040074a3f3e0ca800cc05039d9d27265482664a81c96308d9324130a540e41ab9f38520b996207104b0068a901cca4037d8430925480624281bd64f8372200320140de025da191009902a06ecbff1188804c814036b3bdfc25400e21281b489710f0240722840d9cf0db991003904a06becd5f08a804cc140358d879860482e45881aa0365e92200700940d474721e99003844a0687405d748904c0950340c662926480e1528196a4a2d10a41712c40c7b94c618520399420633d0d40c8900c88503177dfb641482e65801860c35372a40332140c2b76ea499001840a06001e94982904cc9002f9d95bfa4402e01a817be58d2e0241722c00bb003f4d11001900805cb18f6f8a900cc8402e23947f65480e6528165c3d8330a41332440b2c3d99791209912a05916e8e7ca801cc2502abed7ba414026608014e31e1870a00730840a236b4ed8100390420503a11344a804c4150280380b7c1480e65001), (51, 74, 2, 23, 8, 21, 0x3f1fd30588811e41201ef0742822a043980807b57e1b280811e41001ed1f77b52a443890a0798949cb48810e00281de200b370a457996207724eb4682814e60801d4821c472a047984a0743da1a744811e11081cab6920d2a047884a06feb74f9c2814e60881be4cd7d532057846a06ebb698e8a811e61201ba545df522057806a06c9d82294c814e10a81acda2e8b2a053982a06adafbbaca911e65281a5dbcc3922457816a065e8e97b42811e21081931886c10244781420642054ec40815e018818e56faae0a45399200638062e8c8911e452818bd1105e0a0439800061ba31e488914e44a01830ad8d6220439008060b9345480911e45001828493190a443890205f95bb40c8915e45a817a1bc4ff0a443990205e57f2bfc8815e41a817401263b02447914205a3f50f78a910e6420166efb5430a043980205959bfbb48914e04a815ff032ab22053902a056ca34a0c2914e64881564850c10204780420558c58044c915e15a81555f5a4e0a04798400545df03a4c914e14a81514717b22205390280537eeec38a911e652014dcf45bf2a453992a052e09a7682910e640014b3728762a0579868052b135f1c8914e44a814a58bf272a457996a05290e23b88911e4520148d69d3722047904a05177656844911e15081), (84, 67, 2, 18, 9, 19, 0xfca07bbc1682cb043f552dd44c80546a07be665c885a0b2c50f5475b26324055201ea82152e6680aa543d10cf670ad0492887a151fd805a032810f02bc0dc320110a01df027ebc148249003b3152534cc0546a87499d65d098028810e8c767aa924055101d070853a5480ca50399df3e7449015420722ef09795a092550e32ff71d1300510a1c3b52a2604808a1037d217124ac0482a86de5b4201180a0d10db8716673300512a1b5e6f80a54824950365a26a204c0546086c9756c6150090500d8b29a408b0061121b0ac0d9e1680ca1434ef4f1244805462069b2fe1649a02a890d1b37f960a01618019d0cbcb41480ca0032a6edc50890516806487169e152032900c8878c5a8b40651218de32ee006828b0431635b8a40d01142862887fb219a08a510c4ecd9b30b41248a1857ee88456024144301d9fc682c0482085e0fec220520b2c00bc1830af2a006128174d17d8e640221502e3c641e84d0154085bf246b30900a8c00b75519581240550016c4669e12600a2242d1d11b04cd0452a858582656918080550af262350330051221515b156d0600822429b17154c4d015428531b154d1900a8d00a5f05c38330151a214aac69a46682ab44292237f88a905968052187f3391a082550a3d5e2c092005110146de15fa6682ab5428a4dbc008d05168850987d7e412022880a1191e461341558214218ea245402c340281aa0d38ad0194884fd13aa141a0228909f6a2305224104a813c6f126a44828b50265a6ee602d0492084cb2697391a0229509733deff3240552812bf66ba26482ab50252d3ce0cc80144a0492f4e8d99808855091c0991522404528117e8ec26648229502287a353c4801442044e0250f91a0a2d5087c8b2782b4165a210c26079d1480ca20213452772280184404234cd3d05009040083fb10e60340450210609a0725680ca542089d87d88d0114884103653d11202290081810546324114a01), (67, 69, 2, 19, 9, 20, 0x7b35bd1d85a0992287c79ac3a82901ca003cff4c5fc5402e1a01d02aa4222b4072910e7829e7d9580b86a8734c8d7dcad04c954398eb99ee1602608a1cb0210ce0a0130400deb15d0715a0b96886ecf2a6e82c01c204375e0e42e5400e1281b77636e60b0170c10dae0f0bd11a0b16886c2d6416c2c05c31435fa9d0d4160260821afaeac5e0a4172c00d50981391520b96806a55781c8ad04c94434fe15c460480c5081a5ce25830b4072850d1e4fc379520b96a06702cb66c0d058b1432ee2a98c4482c5a0194c43956234062910c86f49ab81a031428628af528c89018a503124e7a1e0482c588186f973770b4172c50c345a0fb95a0394a85e79e3448ac04c1442f24db68c468244a2175b6b116024062800b55dda5915003848059c45d0d82801c2002c230ea4e5600e12a15e07975a024162c00ad10b69d91a0912a8547b829382d04c90429eaa10d6548264a814b8645620a4132400a229e3838580384284f7d1997cac04c154278d27aae0602c18a13a02dc2b2b4172d509c90fd0d91a0b16a84da3a0e182d01ca0426a65df160600c10a13339cca203406281099041d6f1180902884b7770d4c8c018254257f075644480c52012b1fac86034162c108f5aa1359120b16a0476536c4c8d018a54236cd98f4540260a0115c73d2e230160d108add659b9500982a044c07fb7ca805c350216c9325e460240aa10b36f52222412250085210637152099280425e8dcbc8904895021271873c4600c12210668316f230160d50821e2ac50180b060840df77c680c01820420484a1141682e5821), (44, 61, 2, 19, 17, 12, 0xfb5189e13308150fd6d5fa819250807a32da8802c40043cb9605a85620221d728a7108b52090ea65143b15b908872d68c58c2cc014395d6c05e54e4281cad6a9222a72100e28ff57099250a06e6123d78a8c04035eb52a8216a40a1a58c53452a52140d20cad3385b902867e14bbb02d4804339ef71524484281998bc4ed2300150c63aa87f053900062b6032122c402430a96d0d656e42a17fc544c20a30000b99b764195180a05bb459880cc20442c30a9f7914201015f091e3a0b72010adc99e6815a9088563b5b214ad48542a956dc3114a41014f3a063d334a150a5f2329d91b10a85153f7b648d08542850341da641028140d75fb622621009cf9f1b911b10884caf60da88c804426312e07124941012d5f52e323201509676a55991310a04a19f6868acc04425033dc1c166002126bf7d8f2b30150912076ee49a50484858049e24c20242312325e12410101), (49, 71, 2, 23, 9, 18, 0x708d8ee6640ac11a01d7c07068291584b003ad1e2af95a2b0968874303e9c8304600890e743e2c26608c11221cbfff78c29148490039354e238982b0460871fbe1fc0b45612c10e16c7e272608c11121c05e47c0091580b00380246e90902b046006e00c55d2245602d00db7461e06488c15201b5cfc48ca8148414035cf880509823044086b3db1343305608d10d40d60222488c15001a15b8d9c0d1580b04340cf77e45a2309448673e92ac334560ad10cd4a8d9d0488c051019a6d41f48c148014431895f76c5023084405fe4139d924460a880bf279a680688c0502177b226c8cc14821442ef1a60015023084805bfdcdbe2345202510a71409904488c052014c7788a02d148490429060ec01582908288518c5c422304600910a2d51e4b1608c211214508482ca91584b4028180584c5223094404fa423a6324520a5009d6d494c2688c1502139c9c0f0c8148214026cf2d4f8502b086004cddbd752305600d10976cf4852408c111012c9d1418a91484940246a165e858290820847c20220934460a8908ef52b0c540ac21a011cda269089148094023831bc191a2b01688446938cb134560ac1087773da04688c05221), (35, 71, 2, 23, 9, 20, 0x1f893b8485829082287b74739e0344622810f3b06f464608c412a1dd444c5c091588b103b77fdae85a290922876b9cb1b0b45632c50ed3f1ada448ac05a81da0305088d1188a4438168e968902b046206f3ccbca0a45632c00d31d5732568a424aa196f5a3b4291584b10328c2d5c89a2305428613d1b572344622950c0f7eb8e568ac65aa181263134891180a502f5e61e499a29052a85c09399b2b05630d50b72bac26460ac41aa16e1196ec0c11882142cde7d4291229012a058f8c9312345202550b084d21c460ac41a215f2367a8a8148c1402ab973579122b116a0505ddcd30b05630c509e644514068ac45821324e0bcca9148c95024c4b40d11a291128845cbc15622452225008b8ec1d6068ac458a10f1a7784c8158235021cd05850182b1060841af91b1320520854081850f06540a460a81), (69, 73, 2, 23, 9, 20, 0x1fcf410f41408c61001f8f60b713304608950f609523f15023184807a5cd86d4a914849503d17aba7e5488c65281e88cda6b2b45232550f3a2df45852291922079951f5ac2c118c2143c88611126688c152a1e0bf69c20a05230400eec77b1d1122b116807731661f82c148c1043b56485e2668ac15aa1d13e60072b04630950e84357d081a2b0162872a853fb44c1182214391791c345488c65201c3e615bf0a05230440e0c6ea7e91823004a8704abf81cac148c15437f94b4c20488c05081bef7b11e2b05630d10defcc66885023084206e528dc5829118ca003606416fa140ac21881afedcc532b44632950d78313a191829102a86bbb26d28ac148c14434abd57ea1488c25081a55e48350344602850d10427d085a23094286806b5394091580b103400029ee148ac658819fc691720b05630c10cdc6d37d1182910288655d43ee4cc148215432840d2cc548ac65a01903f76ca0304620810c034fd359502b186a05fe4a83788c11882442f96a2d7e468ac45aa174cb31ba0244622800b9d5070691a23014a85cc7f6f988d1588b442de68e5ac548a464a016de9e6db2345222550b678c20191223114a05a67de4f4ac14841542cee92e0c048ac4580165017ab11204608840b0bb340899229052a057858ef2829148c9002b9a8098a6408c112815c5a087d0a45212440ae17e14285a2b0962856e9d9e78ad148c9442b6cdb81c5688c6522159392e4d2305200550ac7b7be515a2b19688561cd5cf8891188a402b0e47bb4168ac6582157b0a5d20b44632810aa6932299522b196a053a0e2a948d1580b5429026d17e448a444a8145caf04b2a04630940a170265905a291920850b1929d4281484110282b0a9fa268ac158a1), (56, 69, 2, 23, 13, 16, 0xfbcf0ffd2a0610140fbf6447a4123010407cba8919c2918c8103e08f1316168c640a1ed4320ad33460a150f2bc4aa58503180206f9ed7b324818202037ac0d8a2160c200a1b5aaa3f4320608100cf82cdce9923050a0677940fc0cd1828443338ffa5c560c6022199c7389b2b0630150caaed2e791a3110a865207e524a918485031f2a1afe160c600a18e412b348b0610090c5606c688523090206172adc14281840103055f0791248c14101804ee27f2b4632150bfcb08221983040885e637e1c08c1800442e0929c24568c642216fb11b09234602150b1528a4d9523190a0578682f48891888402b93f7ebe540c602814c080a042b0610110a469fa679183100a85179a8398a918c84028a9b7139168c241214170d4e20a4632000a0465c8685a3090284dfc3d482291848202641265d0168c240213060dee42346021109821d05f9123110a04ac83af188d1888442535d5c28568c2422129a8fb422a0630100947f4085058318008481d60da4c8182050236da539c140c60001193589492246021408c07bee49183000a844fb60e202c1840042237ca50c168c640211048f6952b0610150878e4b3695a3090a843b747ed20c18002421aed26e9140c201010d52fe2493060809085d4237111831008842d5dde54cc182054202a02e80448c04201), (40, 71, 2, 24, 8, 17, 0xefa59e5aa105042403a8e9b2384a0e814007342a169a840d10100e3e829475083a21201c7639969250742a00366712ca442068008066a14537a940d12100c3c43d639a8281522186832074a1050420030286ced14a0e894005f83d39a4c41408810bdb3f07a18828010217a5fef902503408002e92e0b2e4a0e854805ba0f297c841d08900b094ad411281a042015e2bbf8f3105022442b854077e4a06850805513933d0941402800a9cffb1e9281a140014b7dc6f2210740240291e68cd0420e80400523b0f342941412800a32a38f09083a11001423dc3d8a1074420028289ec5d4a0a094804f1fa2bf2940d1200097d4a7a55283a25201253bc422350500a44248e98a6c4a0e8148048f56660894140290090ae5b6390828112011ee62f18350500a04228dd9d524a0a0540044bcc5628c41400910858c74289081a100010a446db3210342040210539e32420a0440040e3e322c94140a900802573a29a82815021), (45, 72, 2, 26, 7, 16, 0xf9865de2c316521021f2d4c01c820a200001ccee932cc212001021cc3a9e82c352421821c97318c6c306520021c7a39e86c312421021c6d98b68c252001821b5a29cbc821a201001aa120808c216101021a9104928c306500021a7e3b10a835a6218019abf8302c2561218219a074f2a820a220001957cd3a68306520001929eb3fec24612082189957d8c835a6018018085de80824a2008017d13675683524218016ab210a6824a220801663a28688246100801602dda3a83465208015fe6791a831a6210015e3958ccc2061000215c9bc02482561018014f0f87f6c35652182149e8275e831652100149e1676283565218013fb4f12883165010013d0a641ac3465208213ca69f84831a6010013a0d03f48206100001387998dc8216101001338698de820612000132f68e308306500001328cd4548356501801282688ecc35240182121fd11f283124210011990cf4cc35650182117deed80c312401021138d6d9682461208010eab4f70c2461008210bd8a35cc25610182105246af68256121801032256a4834650080100cb7a60c346500821), (72, 74, 2, 26, 7, 18, 0xfb3d484e30948006887eb925e1a8216121201f9a024b230c49004887cef008f88346500a01f18ceb2f20828840807bcece59ac206120221eef77c03309480468878d8d5228834a600a01e28c437a20d5940680730e11588821a201201b31c795120868844006b730f65a8356521a01aa348b76b0d49086886a197ebbac256121a21a5524489209288420068ae7edba8246120a01a21a8ae320c490448065a67d80a8352421a0193cddf9220d698068063b6d1f9a820a2202018da7f3cd30948046086322860fa83124212018737e5632092884280612f32c188316501201790bdd7720c69844805d6469f68c212001221715c32ce30d49006885c1c2723c8252011a016f8daab6b0c59484885bbe11668c356501a216ed5113a20818400805baafd88482520118016b4a1e3ab0c194808859e30f9f4c312411021670b46d62092880280593b92ceac356521a215ecd5adb209688468056ddef91cc352411a215b50a54930848044085683a56a8c346500a21574b18752084804400554adaa74834a610801507abac2a095848680509667f4a831a62120141fe2b92a0c594848050228bca8c31650122140268b8d20c29840005005659ea82061202014014d67e30c19400884f9b09a1cc3124112213e5f1e3130d49046084ed19cc18c2061002213b02da4520c49044004e2257628c246100a21386d7a9e30958406884e12d81ec821a2112013806165220c19400804da84fad4820a21000133eb67ca20918402804b40979588256101a012a1ed75520c698440048eafc95c82120112012319fefb30848044884743217b882161012011cfb995b20d4904680462a7750483524118011889b7e2b0c490848843c57fd2a83065202010edbfb0ea092888280428c6a808c21610122105f09eda20c698048040a7f9e2c834a610a01), (36, 76, 2, 26, 7, 20, 0xd57e9c8e0830a600101cb68e5b20820a200101b9439fe22c316521121b287df824821a211101ac1aaed20c316501121aad38d6e0c306500121a7af6012483124111018fc6255a2821202110182efa24e2c3124211217f16f4be2c2161211217d41b41e4821201110179472e36083165011016c28d2ae4831a6111015d25216e0821a201101599842a20c2061001215551dc8e2c21202112152167ace0c312401121502f23a62831a6211013ab7d1b24c21201112134e7acf20830650010133c11d7228306520101327ead72283124211012e77d7222c30652012126ac785e28216121101205af786282061201011fbe833e0c2161011211e3b7a72082161011011e29b40a0831a6011011bf89ffe0c21200112118b9d8e60820610010116d7d1f228316521101104338ae4820a2101010fc3753a4830a6101010c6050864c31241112107f5277e2c206120121074e94fa2821a221101), (85, 78, 2, 26, 7, 22, 0x3f37328540c3065000a1fbcf201b020958506207eec2164428316521081fb9758ca220c19500807e946e9b88c316541221f720ef96020958506007d59c36dc8c2061402a1f3e0d933220858504a07cd6763c888256141a01f238ae992a0c59484a07b0161e742c2061200a1e914d07e0a0c195800079a84670c88246140a81e2edc973220c19500a07888a24d8ac246160a21dd2cd1290b0d59486287728ad2fcac256161aa1d684e75a0b0c195800873ef3a9a40c2561018a1cc9d2a760a09185820072c60c638a8206160201c99cedf7020c19500207154848940c2461008a1c09ff5d10a0c19480206eea6395828216161001bb463ded2b0918482a86e5d8b1c428346520881b8d43c15020c594042069f1a73a40c2061000a1a747c817230958506a868c297cc8082161410019a297585020818400206555d7f888c2161412218fb142170209185022063b68d9148820610028186100a92220c595048060f20388888246140a017b2ed9bd030d59406285defda7fc2c3565618a176452d522a0c19580805ceb419948831650128170f849bd220958406a05bd124c94ac3165212a16d39a805220918402a05a14f38a42c2461208a1677b97b30208185002058bae0fb42c3465208a162c7df2b030c195002858ae815048c2161012a162976b222a08585848057fa5ffc4883065002815bc89431020c19400205698333888821614120157b99596230c195008855175f0f82c20616002153c242710a08184802054bf362dc8c3065402a151e89199230818400a853ecacbfc0c2461408a14d50dba62b0c195808852a221d14a8256121a81487f47cf2b0818580a85094d0844a8246120a814169b8c7030d195022850256c24488356501a813ab0aa0d2a0d59486a04e5ecb52c8c2161412a1374dbb310b0c19480284b1abe9f42c3165210a122bffe7b030818500284691a1d548821610128118818f92020c1950000459dfc38888346540a0115cd962b230918502a8449652c048c3065002a1113d4fc92a0d19482a0442da3f98082061400010fe84ede2b08185808843786b6148c246100aa10d368cc92b0c19480a842e19ff6c88206140281098f28c5230c59404a840e5387448c356501aa100e9c651230958406a840173f5a4a8206120281), (36, 74, 2, 24, 8, 20, 0xfe8ca1021420a0842077fa629481283a05081dac5c7d20420680020723f0abd91081a00281bc116d9e4620a004a86b5c556295281a242818b2b33ce44a06810a06288f485952828252818781db3e64a0e854a0619b5084818828010a1835e23de5420e884a05fe5c8fe998828112a17ce4849a6420e844a05ede90af89083a110814d40d17e24a068502052cb87689928281528142a68d6624a0e8542050a08f5f91283a052814118748206a0a014284e934c1781281a0408132d03a6e2620a044284ca02da7852828250812bf560c644a0a014a049b7ce1289081a1008124432ab25420a084a047fbcf3d890828110811bba4d5666a0a054a846e03857892828150811a6fbfc61420e8842045fb439399081a10281170c069246a0a014a84553f31d81083a0108111d4384e26a0a05428446aec8d990828112810d882c9a4420e804a040e7931f81282805081), (34, 75, 2, 26, 8, 21, 0x3e4321320a083130000f890f9861612a0618a1e396289c0824c481103ba0e5f9118629104887364165e0a093130400e60df09224106210081c0ed30bc2834ccc11037fceb7f9504b8986a06da2fce1220d7300d40da3c7d82041a660088197f32ca4c820c4205030de777781041890020612af0d52b0c5210950be8433ea5412e221a8178af67642820c440102ec91e55858629184285c9fa54b020d7320c40b25d069a6412a011a8159e20344a8354843502b2a51a78506199802054074753030d5220c50a655c1a6041a66408813ab509dc8835cc835026339ec70586a9186084b710766020d3320400950430165410626028128011de4c835cc23502407da12910699802a0471e3f85320c52089408c5f3f26441a6640a81160d24d80824c481002233019a998428044a843cbccfa0a0c73308008443df361610a0610a1), (86, 77, 2, 26, 8, 21, 0x3fdfbcbac2821c4c2103fb70a81a44126200a81f6ee9a5e0b085030810fb46b028890639844207d04b84cc0825c483103e21ec7fa261aa4118a1f10b428e0a0d3330400f67da6530184a8106087a2f00708282140c2003c8c65fbc441a6640a01e3d2f4892a0c7310940f16d2d1b15042818480786024f6c2824c4c1103c2f7d5ec141ae661801e11ddfe202087120800f035aabe8904a8046207774360c448214022103b42975da5410a021281d9f9debe020c7320800ec8237c7158629184887621415188820c480403ab3f784a14126220881d51a84d513085008850e95f290a8186290042873e7763c8ac3548c34439ea5a74c1410e261001cc82c85b03095020c50e54121da8586a9086287295a9ea4cc31482254390eb726e5412a061a81c6a68f7f22093120540e184265f15063998480706df67f44835cc231038194599a64186610281bea150b22a0d3330500de08bd3c950438884a06ec4d804c8820c480503704d728a141a6620881b6147c1d320c7308940da5a3867958629184a86d018f3b80830cc800035e30bb9a54126220a81ad4024d10a0c7310840d4cc9ac2990498842a06a02229542835cc431034f62127c0618a441021a679605e2a093130500cd7d50b49986a9046a865f52e4f8a830ccc04032f36e794541ae661a0197209e990b0c5210850cad6c70c89862904428650e73ccc0c31488214322308e36461aa441aa1867fa2fa0b0c5230810c2ad4573850418980206138453b4a835cc4350305f601b4041062400017f27cbf623085020910bc2cb5949504a8086a05c4da67740830cc00102da11e49c541062602016c34f8af23095020d50b5cfe830890619840205ad7c205c8830cc80502d4920d5a041062000816a296dcb2a093130540b36e0dce950629084a059a764fbc8831cc82502c432c9641418666000161f3ad7d22083100140b03de71e910639804a057558e22c0830cc80102b7a81192641a6610a815b6ef12532097108d40acd54deb8504b898620551129e74c8214022502a7b0a7ea2418a411081507baff112093108440a48ab86f1186a910688521d9212c0831cc8210290d4932e5410e261281478edb39120d5208c40a37607178104389042050b4a3c948c31480254284837044061aa441821), (42, 67, 2, 24, 15, 13, 0x3937d7e985ac12050ee298228231800221d689325e1430401038ea42b2429609020718c5ed989ac0a050e1490a32235804221bf5b76bc0630000432e082b500960100065b870e619ac0a110cabe54f90318000a194d825ae46b0085431603685cc96050a061f0e213158c10110c0baea590358040a17c2d7944663020442e1fba6484d6050085a887eca092c0a000b1dff8472318002a162a6db7a643020502c23e67402c60800855904dd5192c0a100a49f73972a182028148f0e5c826302004284366118ad6090884f0f34e3890c080409c5aac88035804021329f28b6663020542570d30e4496050204903c8ba812c020409204390a0a1820001207bafba5630405423e1610d02d60900847b9ee35898c080508bf8bf712a58242811721cac854b0484022ba94a50486040004534bfea912c0214089179f6c3218102010bae1a74543040402097440088960108040a21cc1858c10050802549040a5824001), (52, 74, 2, 26, 11, 18, 0xfee7f131120d9042207b698bef44c364108a1d323697c030d900208718a40f142836420881c3148c9113098042287070f62a80c26040821bce3bfc32a098182a06eaeffd848c36400aa1ba73994623098102886d8a65b7c0c364408a1b3e3c2ae0b098182086b4b6c290ac26020a21a8d1fbeb230d9102a86943be0604c36410821a2e459680b0d9082086853f2944a826020a8195cd3e9d23098002a863889da202c260208218468f65d0b09808228604a37de8a836460a017503afc823098002885d00fbc588c36440a2168bdbe590309800228595293ab4cc36410aa1641ee1dc0a0d908200584e7a73cac36460aa15ab50fb50b0d908228567ffb01c2c364608a1580fa09c330d904288558cfcbc4cc26010aa1518748042b0d908288534b08a104c260108214019a46a0b0d9182084f17143d048260108013664424833098042884c408fa1048364108012ebfe3e52b0d9082a84b28655b4482601088126e136842a0d90828047d02f4a4c826010a811f0da1182a09808280473e7193c2c260608a11c12c8dd2a0d9082a046a1900b4ac26020aa1178989cc3209804280459202af8a826060a011603182a030d9102084561a53a40c364008a113175c0c0a09808200439984870c836410a0107eb803a2b0d91828840f13ac54c836410a81), (57, 72, 2, 26, 13, 16, 0xff97df2a2a0a060201fb7ca31a2b0a060221f040af888b0e420121ee30f874830a000121ee2d58672a0a060281e95535290b0a0200a1e205ac552a0a020281de2d7b78030e400021dab780260a0a060001d60e733c330a010221cc7323340b0e420021b615c59e2b0e460221ac6e30a80a0e420001a5f04b752b0e4202a1a0596830330e4102219e7535150a0a0200819b68e1a5030a0000a19af6627c0b0a020021828b5e50320a010201808d36cb2b0e4602a17f992859230e4002a17dc53ded120a0100817a2ca8c4830e40012179327ce60b0a06002176afbd5a0a0e46000172f9b3520b0e46002172a8fc262a0e4602016b56aa270b0e4600a16acf3504320e410201641ecbb10b0e4200a1609bcff1230a0002a15cc56438130a0100215794a0d5130e4100a14fefb21c130e4100214f42a096030a0400213e827341130a0100a13dfeff3d030e4000a1312c1a430b0a0600a12fb0094c8a0e4201012e1c98dc2a0e4202012d58b00e030e440021298f9c21320a010281294f65a8120a01000127cd3b0c2b0a02022126e4f854230a00022124de819d330e4102a1234b2840120e4100011f7b3a7c920a010101177a3c488b0a02012116907f79320e4102811580add5330a0102a11433c8c88a0a02010113275108930e4101210ea6573d120e4100810c020c150a0e42008106a94100930a01012105329978920e410101), (71, 74, 2, 21, 7, 22, 0x3fc7c17185600b21221fb8404c38520ad96207d7858fd21400b21081f22e36208100ac06207a93b946a5402b21a81e870d86e85a00c902879da3e30e1602b618a1e41a916681a02c142878af321ce16003600a1dd7ec80b9120ad16a0771d147004480304201dbe418329580ac86a876f2df3ea1682b258a1d7f4ab5095008c82a075b7151165482b65a81d341589085a02c9428745189ff80600b01021d093764c05202c94007327f62ee5402b61a81c86d2cd215200c908070eaaa65e0400b41081c327106e11a00c10887023865021480324081bff0374395808d82a86fbe2e13616023608a1beb1411211808c02886e5332fe61400360081b542d7ad9580ad86a86d3e9c07a4682b05aa1b46aaf920580ac86086d0fff2400602b01821b38e6acf95802d84a86c5315d420600b010a1b06d416585a0ad96286c00d915a4600b012a1aae74f3411a08c12886a25e39464402b41a81a6dcb43581a02d142868b630b761482364881a194597311002d0480681c2b61e1680b650a19fb877b011a02c148867baeb72c1480b650019d8b002395208d92a0675a4ccfe54003602819d4cfb6d11000d008066eaedb560482b458819933de0d91202d14a065d25801a56003202a195b7c2dc85a08c92286549d77b65402360a819389295995800d80a8646f1f14a4480b052818f5f4cae95000c80a0633feaf8e14023608818a71732c9520ac96a0629c39fee5682b65aa18a2e52e09180ac06a8626adc3905402b21a01895f36bc85800c8028623ed8d0056803242218856101f85200d902061c82a15c160236082185313d6b91002d04a060ab9889a46803042a1829c1d0115002d848060a1981f65480364281818a013015a0ac96886058ee8ec5602b61a21806bc54205000c8000600f83cb00482b05801), (83, 75, 2, 23, 7, 21, 0x1fdf7fd96460ab406a87eeeaf0e4a815690d40fc5c6c170522b625801f77f9c512a041a40503e506bbe614824892207c80bac4ca814690540f82bb53e01222d05001ef45246403455a0b043db84471214804890207b00e8e502914b12400f4e0ae201902b611a01e7a0acbf2a40644a503cdc6618a0402c8062078fb3bebca805910d40f1231d370182ad01821e173c6750b441a48143c153f75e040ab4062077baf92b48911682940ee7a52b38500b221881dc7d2f9232446c2a403b68ae57e64804850a076b48a2420d11682890ebdb7ab495021620281d5929ee022455a0b403a5b7d5e04402c806807431751084815b08c00e86166f491228d04a81d04e210f2b441a485439d14de4a6408d844a0738bafe9c4805908c40e70804178120b205881caf15fb40a042c4000391439dd02402c8460071f617c4c8d14682550e20af34691822d012a1c3f527f42a00644240385fa19e21402488220706e5e9f4a911b12940e039881b0122ad05801be076489120064221037bf1486a548a5892a06e3a94a58c914b0a500da1fe79e15a28d24a21b11de14f2b045a425435a8d2dae2480c854206afb94f9a0c11680890d544e6178502b621881a95f51f123441a085434b42d0b44482481280696734b2c2810b10040d26b9c7d85820d200a1a2f0813722446c0a5034168a6444400c8048067a4f3f1c2914b12440cdce1ee68502ad218819a42bab812446c2a003337a971a440a5802a065e25e0242801910840cae969d101a22d05021951599b622441a084032a0986d00400c8040064bdf57242914692440c9006e6385220d2408191e0a2c30a045a421031f72140264885850a063ac6a6bc0801900840c744af3d8122b6058818d7031ed23051a015431a11a13c4488b41480630b60b08ad11692910c5dcd01f45a22d2512189f3165323041a005431365470c440ad806806250547f8490590ac00c4966b5791220d04281887b52480b055a430430c68d1f04408d804806135f16322800910080c23f78e64902161010183dc1bb68a4024482030616cd750488b4144060c0429a82801910800c1616c8985223625081), (52, 76, 2, 23, 7, 22, 0xfa0e2abb8102b641881ec1a856791822d412a1ea42156181a2ad458a1e02630cd15a22d65221deb949f185820d600a1dc7413651522ad65a01d530b86b0582ad61821d4c0ba1905222d65001d37088bf85828d608a1d266dca785a20d640a1cd91019715029660a01cb8491c90100b241801cadfa2858122b645881c9adce9b95028d60a81c1c6e57f15828d60a21c190c85f9522ad65a81c0b626e595020d60281bfa5b69d8582ad618a1bf192cc395009260a81bdd0f09b91222d45281bc47ff1f15222d65201b650290991a22d452a1b611bce59500b261a81ad0cecef0102b641801acf3ee891102b641a01abe35d1991028d40a81abc1d72315003261201a97eec131100b241a01a92600a50182ad41821a67f2c6d11828d40a21a61a8e9185220d64081a39ab5191500b261a01a2e9293391828d40aa1a257bee991022d41281a0c39c7f01a2ad45821a07567e181222d450819f78e06795220d642819eab23179100b241a819c226a159502ad61a819aad938d95a20d642a199b532eb01822d410219719b30b85020d6008192d783590122ad4580191efce1b1122b645a018c1000bb11020d402018a5b32eb8100b2418818a04a72785a2ad658a189444d8115229664a01878e518b9520b265a818774d75911a2ad45a218726babf9102ad41a81850e0c5d0502b661801), (45, 70, 2, 19, 9, 20, 0x3f01585721402a1881fb94acc61580a86887e51c64da148024081f7dbd9ca9520a96a07bae83fda540220a81e46b614a81802042878c437c261482e5881d8c03b3c85208922075883ce4e1480e5081d4f3fa4e8980a46287415201aa1482a5881cef2b2fa85800802871db4d7e0060081021c1cdfcc49180204a87044e2e18060281821ba95fdb089a0a56286e38d9dd8668014221b8b0b58c8120a16206e1bc99825600202a1b765f1071520394806cc61a020668095221ad7c311281a0a16286b0ee54e8660210a21aaac09211580b86886991b2e0a140220881a5c29dfb850018020693959240248295801a2482edc85202942067f1d07265480e52819f0d4f1a9180a06a867bac1a684600812219e7637b2850028420675d3b4f41402e18019cf68e91850038420672ea9da0548224a0193cf55a5850098220641ff78b61480640818feee28f85209922063b4126725602a1aa18bf40d0a0120a160062922380c5600e12218a08db8e1920a568060fbd67621602208a1825591d38500b8620600b25c225682a5aa1), (50, 74, 2, 23, 9, 20, 0xfb0e7afa9982b046a87eb7566d01608c21021f82d42f89522b096a07de7ad152540a420a81f506b02841a21010487d05087b20608c010a1edde4db60582b0860879911369a540ac21a81e4fd40a5852231942079334cedc140ac61801e43266301582b086887623a30205688c25221d78d721419023044807522305fe1688c650a1d2bc17a29922b056a0747cd4cba560ac21aa1cf65caa495023084a07394109d0060ac01821cc53e2fb8182b1062872be6d16e168a4648a1c42c447c95a2b096a86ff7cc2692688414121ba38a7c695a23094a86e3cd6b42248ac15881b8e3790205a23094086ce4641f6160a4608a1b159bb7499223054a06c037a018568a424a21af8c932615823084886b8f703b4540ac61a01aa0c597c9182b006a86a645e6586488414201a74f0e401922b0568068fbf6cbc1608c61021a1842b0d81a23114286860d3fa25608c212a1a0495cf78122311420664929df2260ac118a191af287515823184886466a0a182408c11001918ca86a0182300408645d3e65e1408c610818ffeaec619a230548863ce9d5a8248ac1580187e94c8d8502b1862061ba11c7a5488c25281863f150e41a230144861651c81a2488c15081847ba6580502908200601f85688668a414a21), (88, 78, 2, 23, 7, 22, 0x893e5bcba068ab4162861dc3afb895a22d252a181a6197065608b584a85fa6dfbf295a2ad25aa1777e7b1620688b414285cc300af395a22d652a171c38e072048ab416205bd67a69b9582ad61aa16f10697921602a486285b2e8507985a22d650a16a2fead121608b4842859cd0f7ff85822d610a165b29728a0482a416205929e5fc995222d652816395d2382468ab416a85829f09f28580a0218a1607e42cba1600a4842858139fb208182ad018a15df24726a0488b4142056fe6aa9795022d612815bf66ff8a0608b4042856d2fb11685a22d250a15a886fc220682a4162855d1e2a0e858224210a1563e1f1521488b49420556c4cb408520a925881549c61f7e1488b594205522996349502b621a8153f2b84ca160ab4862854dfc028d1582ad61a2153057860a148ab4962054be6e418858020210a152c7b261a56008084a85489ac4ab15a2ad65a2151e4b9fd2168ab4962854615069195828d60aa1512587b5e0688b5142854065a50c058029210214fd6d4e025482c896a053e7f3d3e95029620a814f1664984160a35820853911b9508180a0018a14e10369fa54004880a05333ad974158020212214cae8b838160080840852e9cc5048522b6258814b5be93085402c8868052ba5688691a22d052a14acdab368140a58820052a941234958029212a14a979eb961408b58420528fb51a68500a92188149c26e9e22482c8562052666a1cd81022d41081493a9b6ee5480a594a05244dbbf59500296128148e746e4a448ab416a05224417829522b625a814873d219e56083580a8520d1c6989500a021a81480090bc0160280860851ee18d7e8182a4018a1479b7898e1400a5842051e352341858029610a1474cdafda1480a4942051b92859e95022d21281463a56e5a1482249220516c1c3a815220d2420145a93560a2482805620516a2d0a595a2ad65aa1453e6d462160a908628513f381789582ad21aa14453541b2140a58822051142bade8180a9018a143b04c7081608b4840850be00db801822d01021425f419841608b58408509147590812029050814241ec7c01402c886005052aef4715822d6122140db49306140ad986205032519fe15a08924a2140b541ed90688341048502d4ec5f8102ad418814075b1da80402c80600501ce99830500b261801401c8915e0682a516285006a114185202965081), (68, 78, 2, 26, 7, 21, 0xf87fab032a0c29880a07dfc88174ac256121aa1f7d36635020868804207c6647eb82830a620001efd9df6f020d19402207ae1d48882c216121021e5c3c2ef0a0d5948620786e6aa64a8408a20281dd927d0e2a08688848075d736a7ca8306520281d5b153bc0a0d29882007559423e40c3165010a1d1c0a4b7030858404287409e492c08256101881cece4f3902091840220739867dd88825a201a01cdb25a560210228000072e1993944825a211881c6b031640a08688840070dccc5a84825a211801c2c463cb12086884420702d8a2000830a600001be2a41422b0d19482886f272169c28246120881bc48a3c0020968806006dd7b0a80ac216121221b3bd64b00b0818480086c40e55140c3465008a1b08f1f1d020d59406206bb2862448825a201a81ae9708742a0c29880806ba22809028408a20001ae66e3c12b0818480a86abc32d6c8c346500aa1a8e7f07f220868804a06a244c824a8216121281a450cfa52a0d29882a0690249694c821a211281a38e6a99325022850a068d1e2bb4ac346520aa19b791251020858404206683d39908820a200201994e87d10209288022065a23d0dc4834a61088195db99bc2a0d194828065541f8222830a62010194b7073c120d6984600650b81fd80834a6008019415c976030c594040864fd44a388830a600201935c288a2a0d6988680647cd28142830a620081901537192a0828880a063a245c5c28408a200818bdd14dc2b09184828862cb72a0c29408a240818b13dc7d020d698062062ae37e74a9418a252818982c957020c6980420625525fb0c830a61020188c1be7d220c29800a0622be6cfa2820a220101876c5c1e2a0d298828061b3b3b002821612100186c2ccba320d698468060da7a13c29418a25081823ed9fd220d19402a0603c1fa1cac356521aa1), (71, 79, 2, 26, 7, 22, 0x1fd13058e020d19502007f03626244412d120d00fd844c2ec08316541081f4b058b115868cac1443e7e4aa8e030918502087c6eccde4461230a0510f8ad86c3888356541a01f130d5291504344c2403db0560ae2b0858584887b00428141412d130c00f393fc87c2c2461608a1e53386b50586acac3043bf4261070b08585842877a094306561832b0150edbf3abc808356541801db699d1f05862cac2043a9401f7e030d5950608746546cee541ad330d40e7127cc880c316541021cc248aa31106b4c83403940af0b20b09185820872548f9cc0412d120c00e478f161c28256161881be5db2031504b44c34037a3697830a0d59586206f127a3bc0610b0a0810dcb2b5c2ca8206160281b5ffc49785860cac01436954f003020d19502206cb8615764412d120d40d965e8cd88821a241201b0aa8b0d0106b4c8300360c535620a0958586006b85c30a41418b2b0800d6f385938a8346560a01ac1d3ce105842c2c204357eaa9a7020d59506206aa184b8e4412b0a0d40d432d89880c256141821a85cc6a5110614c80403505e18d30b09585862868f2347ee0618b2a0850d1d5849588c256141a21a396bc8d11049448140347125706030c195000868cee786c5412b0b0d00d120ddce80c206140021a1c23ef595848c2c15433fc1e87a2308185008867e805c9e0410b0a0840cf34f7e4828346560801985e736581842c2821432e7c9ddf0a0d699862064403205e4410d120940c808625688c356541a218f4fb99915048c2c14031ddff34b0b081858028639ce385c0418b2a0800c693d1dccac2161612a18d273e0105040c2c0003195f66bb030d59506286326ea01e54185330140c52de5aeca834a660a8189dd35a3850634cc210310a77bff0309585062862094c42c441030a0100c3fa0d6488831a64120187a9ee2f0584ac2c30430bf0f01a02091850200615338736461a32a0550c194a058c8c356541aa1), (67, 77, 2, 26, 9, 20, 0x7caa1b5a4ac412084a87e380811016209042043edee45ef0b0d64618a1f574098995849030550fa5dbb3248c258006a87c731482c1412c0c3003e219e0a70a092060881f0e59a2215843010910f30876a8c282081802077757d43856209042443b87415390a0d6421881d968d30205a82412810ebe665778a835918680757acc9c056a0904a443ab598ecd33096011aa1ce96456911861220110e6f3006940c2580062873398e0965610c0c25439329eeb9030860010a1c8b3f5859506b230d40e4357c900282580860071ba066585412c0434038c64e9c623082040221c24eb74b15849030510e0870f460ac309080886fb7deb661412c0c3103754ab1430a0d2460881b9fb6c9a11861200110db58ee65cac208180a86d7fbca52141240411036bdc3e41130960118a1b3c9e2838506b230c40d80f35328ac218184886bfe754ae541a48c15035f2122570a0c2460081af79081f05063230800d6bb1d98c8c208100a869fec229a56a0904a54346c10269335008142a19fd8326b91849020550cfc492328a83191848067c418722561ac8435433beb8acb030c24400a19c6c715195061230140cdab12464ad402090a866c62851a461ac803543351a36e22a096061a019943372f05069230400cb753dcb4ac208080a8655892d764618c88254329b2f87b2a086061281936a9a6685063210840c7ce61be42d41209428633626bc25418484050315435d93030920408a18990b18a91843000950c45bdc2808c3490028862134676e4610c08254310411fef030860410a187bd1e491184b020d10c3ce8865c8c309100a86180eb3841612c0c30430937fdd1320d6411a8184037af905049030400c17a92c440c359006286022fe5d40610c08204300803327030820400a1), (59, 81, 2, 26, 7, 22, 0x5c6f348ab2a0c59584a06c1d6efb39506acac35032cb15671cac3165612a183e989fde1418b2b0840bcac2e71e2b0d59586885cc397c319586acac3542dece3b5c8ac3165612216b89ed014541ab2b0d00b34a10acb2a0958586a059a34abd585042c2c2102c9438630ca8346560a8163d1351a61618b2b0850b0d93aebd0a09480862057a62bf1791062ca82502bcc59b50ca831a66128157fff74dc161a32b0410abd7da32f2b0d19582a855e8ccdfd9106aca83502adb11c19cac252061aa15664f87b64618b2a0950aafe6557f2a0858584a055651cc4501868ca81042a6a4b5a40ac252021a21506a11ace541832b0140a7d387b550209688062053df7e92d85048c2c1102995e3d6c42c2520218a14aacc73721412b090c40a53ef25bd2b0948086a852585d0851584ac2c344291c4e4b702c252021821489dbd1a6141832b0040a409baacb0b0d195822851fa2761395048c2c15028fbba8678a831656120147d02a9ee54189230940a3d96774f220d19502a051eabe3380584240420428ee380840a825a221a01471604fa4141a9230c00a35bc0c0f0a08481842051a8a802711868ca814428bb380284ac2120212a14553b529c141ab2b0c00a29e0d2632b0d49186a8514092b5385040c2c010287fab6e142c2120210a143ed6412a16208410850a19c1600d2b0858484a850af4cb7b85068cac110284fa269a428212021081427abc6121412d110c40a134c04550a085848420507adbc6a0504b4443002831fefc142821a2210814154a5c021610b090850a09d564150b095848628504b7362d8506248c210280121d898ac252061a21), (56, 67, 7, 16, 7, 22, 0xfa01b3cc428034423e6c56ac0a40564347cd8477990802d04af9150df92101580d5f06f20ac1202b6183dba8ba04a50164a57b52565590a0ad16af620bf1301405a285e22f6ef10100b0115c3e3a76ca5056cb577d5104704800d800ee384eca21405a291d3d1a70a52803242ba3c5707c84056835737197f090a0ac16ae2e1819500c018206c18c847c528036423829ff754250564b170150da204802c840dfcc3f45014058285bd89caa00282b0583717ab09825056cb06df5ef5b10808d028dbc9d2ce20c11a252b60668640200b410360275dac040568316ae6172094a08c92ad1c79df300811a046a36372844282344a337c1cdc0830560b4a6ea9a6e0480ac860c9b9f678094019201863008b45282b65a2f32c711c25056cb15dedf0d000a02c140bb66a6f600c05a2826e75475c128036402c23977b80304689097c6175310602d149275e5f592900190154cc48258128232482887efd60a40164244faae5b880a0ac1629c49881a29015b0d1381d03d25282b25aa5006ed6882056834884d6b678040ad063106e33442100180111fcdc3a60200b410a3aad20d8020168208752a80410608c1290da145da20c15a2d21a170cd41282364821ced1b68a5046c9442fea3a990a02d14a852bc8c609405b281), (45, 68, 7, 16, 7, 22, 0xfa3bb0c80101580c1f3e07b5700801a006f0816d69094019205ead4b49a09005b081e7f957fa01415a2c1e7a51751208118056e67e5c6e01015a0c1e0b6eb7200811a042de77a42c290119051ddc4375b00c01a206dab3efbc890059089da31ca2721401a215d70884ff00c05a286d5beabf4094059281d2ed7b68890019009d08755e0290019011cf185121008018006cbfc5d2629005b091c9c0c8de21415a2d1c97fc46a09011b041ba7d78c5210018015b621c86a21001a011b40fd23a21015a0d1af6090d00941592c1aea9497b21411a255ae31e78229001b011ade745e8210118051ad91dbc8090119041ac43156721011a055aa59107621005a091a8980ace01405a281a6f6d8ba20805a092a6427899010058085a607dfd300c15a2c6a5df82f200c15a2c2a12e64c52900590959fccef2e29011b0519d6a431821005809196ab47f701415a2c58ed528352080180168d5ea03229405b2918ceefef509405928587ddf58e20811a05281347c6d290119055802ada3b21001a015), (36, 68, 7, 18, 7, 20, 0xf749d888241169081e6a67e5c851068211dfaf26b80215680c2df7ae604841168091d750b1048315682d2cf9612a8251069201cbb93a48851468251c2da180a02116808abffc39c4a41169091bfcc3824841468051b0a3900c031168282acff890c0415680c1a64d9d540511682818d8cac5803146824275182bcca511692916efcc5740515682c16c3852a402116808267ebb88a251169289659b7fe62411690895ddc84688211680925823c152241069009479847fe2510692093dcf28000411680813c6302ac2415690c136ecae540315682c2329714d083146825225dac084a5146925121d0adf4a410690111ce41b9ca510692111afcf4342515692c1154534c603116828a10934e020411680891027cc80251169281091b4dbe05106820901b9c0fa05116828901a1a710a415690d1), (85, 70, 7, 18, 7, 22, 0x3f898fd64821068016fcc0f89900c55a0b1bec9041f4831068216f569264d21045a0257cdaf26ec05156a2c5f21c3b0220c55a8b4bc67e6bd825106b201eee3aa3300841a801bb4434e348415680d5e340582700c45a8a1b8cd57894841468055d85adc8901055a0317608e82cc24146b045d0876d0509051a411732f6a304851168295cc0dac8621451a894726fc157803156a2c2c69aa59e20855a834b18662cc824156b0c1c161f2fd20851a015afbae31c42415690c5be546f1f21441a8856d875770c03156a2c6b51191b909451a4916d35d886805116a281b475360909455a4b16c3caca14031168286ae2971e200c45a8a0ab19161d40515682c5a7d94a9d20c55a0b5a973c6f6885156a2d1a4e66d3b00c51a891a906d2c0ca5146b2559f2ef76120855a035a75b7f57883116a29299d5bd2220851a814a5d7e578c82146a05693f66ddb21045a82564a70a35c04116a0858c46ef8b21451a89562d3890c425116928584dc136f20c55a8b59f9d5f15882116a0927cd047bb21051a8155ee395b84051168285775989fe01455a8b05d9836d4c25146b2457517a41f20c51a8959c8c295a40214680466b4f390129455a4b55acdc93bc02156a0c66accbd5f09455acb15a892a5c4831468256676fda7e09455acb059aea762804156a0c1661aa28621445a8a45974d252885106a211635611b700851a811983d1f3b802146a0425bc85c2721055a83556c3e307c85156a2d554551f4621041a80453f99fcd824146b0414734f99f20855a8358f5d0f41884116a0913a7f815320c41a8858b8b0386c03106a20628a631c500841a00189d2acc8c04156a0c52596caff21041a805490525db803146a2421cbe946321445a8a5469e0437883146a2521a6dc78a21055a8344604c933404116808518050d7521441a08545ca1989825146b24114bcab2a21051a81444b717e0804116a0810f644b5f20c45a8a5826e6b13403106820606da437121451a095414ed1f9802116a08203fb64dd21455a0b5404129ce4031468246), (54, 66, 8, 17, 8, 19, 0xff5c0a104314e1487e84151920c438109eaa225a44211e110782ec412108168461dd393340c215e11a705af6d6308478449b13c19808214e00a6596992220c47814992e116ae0310e0416218f6ed20c538129814605e00300a0405f3446e80084780417ab0cf0cc301a1525e5ca27530c478549691d9e208200a002597927fc10c12852163685c788315e05a58a78c3720806804955584f70c300a14253032c128084380054b49e5d04301a15052aa897000c1681614986f23c0301a050524009b310c16856147c433de4300a14151d9627b00c578161447b90d00214e0084fe68ddc9084784453eb321d08301a0524e495c8a30843840937ea93ae0311e0514dc4efa900857806132774d364210e1014c5ffe5e10c5785612fb053748300a0424ac50b79008168061296dd7ec8211e0124a503e8e30806844926ebc5cc4215e118456c510190c4785451546984a0211e01144a672ac8080680451167c1084300a140435c01979080684450cd2c75e0301a0514306e35480c0281050bbc25a20200a0014224bef900806804107419ede4301a15141c89ff590c438505047b81ec0314e04840eed840108068441015652940304a04840339827908028405), (90, 68, 8, 17, 8, 21, 0xfe440baf20c06914bf93e7f8620c479149f89e513d10c578563f774758a008579061f2249f89108578463f0bd3fbf008539023ea25105520802800be89394aa20c539129e704ec1530c02850be56bb8e500c438103dcb6ccb6008539021d86af463008129023d66bb08a208479049d1ec2f7f00c069143d0ce7bff008029003cff3495510c128523cd3a41b510c068543ca7ecd5620c029109c5e1b54b20816906bc43e4cd320c02910bc413560300c169163c21966e520857806bba1b351930c12852bb005d5d9108128423af8890e2008439001aec0242920847804ba594d80d20843800ba49e1e4e208539029a1f0115f20c43910ba08f90250085780639f5df1f91080684439bd68c7920c57816b97b39b2f00816906396f3abc110853842396543c8200c02910194e856a520c47814b94077d2720857906b93270ecf20806904b919b60420081290218dfee0c50085380238d72b62930c57856b8cb54ac220c0691498af76c7130857846b84a8d85e00816906183df263100847804383170796208439009811f0fab20c47914b7cf65f5930c53852b77728f7100c57816375ac3fd110847844375a86de300c0291037482b03930853842b70a304af20c16916b6e4f793d20853802b6d16687200c1691616ca96b9100c5381236b91d77720843900b6867da6700c579163671363c510c538523661942fe00c439101654ffbce2081690695c4812ca00c47914156866ceb20847904b51552b030084790435067236200c539121500a171b20c57916b4c1b342920c02810b4b906dd500c47814347801e6930c47854b461706fe008029001428aaaba208129029423afa6510c4785433af1d05d30847844b360ddc0600c1291212cc112290080280032a3c793e208029009269223e700c47914323a36ce920c53812b239c32722080690491e26411510c0285031c438c0e00c5791611bddfd7e00c06914119929f8930843840b14130d8b00c43910311d5e6e30084390030aa999f510802840306da2e2200806904103301f8e20c16916902f830ed00c0281030184a9db008579063), (51, 61, 7, 12, 9, 19, 0x7da4872121004257eab312e48803113ec5734704301a82edfd3cae210242374d09992810042278922cca9860b5adc4146d90c505ad1defb54fa418094b6e3f514300c04a1ae77ce5f8040a18d73589604c404855b617c002010084359d964ce10c16b0abc91e1598a094ab5159bee4c2048569cf5df206182d694b1cfa1e30c06a4a452183b88a0350b1f1e2e3cc4018958e18aa26420286ac1e0fd223080624a06830b28860350cecd996804304a4275e5a90e6102c6b3a8b505611406a05a48b5d59880b1aac9df7e00c4018916064d39c6202428ad132f0620814349652cc21186094a4ac713e740501285550e89d6618252b27b28bb501414b1509b53cc9840312c8011483404050c53f5717422200c429cb5a2da31412944d96540188a0b58a55603d7483052d6235fed9c610242910d837f331406a5482e2e0d9040a1ac29d1c67c8204056127ebe76428296a8912ffd72080425845d5abd8840310c22c23170c2058d20c02f7d2418212b05d5154921404a542cf9aec98a0b5aa0e89ef7c0401085), (78, 64, 7, 14, 9, 20, 0xfddfbaa429405291f5db505b00c12246ed2cc95a008160c2e75a223b294172d5db549f0809405281d060d54e01006081cac7a4f7208160d6c6b2082221012051b88aabd709413245b50b80e929405295b3c925c9094152c5a9163a2e00812042a8246d9d294152d5a6babf2e290130519fd022f6008060829fcfa27e294172d19d62ff0f0080608699e023c82901105199590a6b2941325595da15522081205293a0406d2901105592397c9a214162d18d023a0f290130558cdea127008120468a50d612094172c185f76f2600c162c28574079320c162d680507bee094072817b430267094172c576da96d700c162c675eb90fb21012055750fd7232900709571a4fb7b00c06286713b89d6014162c171313aa2010160c16fa28b46210160d16e1fd424294112516be864a30100608569f3a19b014162c569420f77010160c5687156f10941124566fc7c2a0900708162a8ce4b214062955d34f19a014062815525d1a30900708553202ef8090150c152f8d0e4094152c151c0c597090170c5501214170940728543ea30ca00c0628242829164290150d13fe116cd090110453b4221ba090170c13ac3f57f214122553967cb72290170d136cd3bd6094132413433c36e20806092342a3fcd0940528532f1c389090150c52dd5021e214062912d5a5b19090050852c96c89e294072912be0c378090050812b04c4b220c0629226e31e3720c062961e7e3e88290050911d596e4a20c122521b10c76609013041164823b200c122421571822f29407295145663d220c162d213aefd3929411255129d41cc094112411201019f014062850ceb97c3008160c60917ef36208160d204b2ee1c0901104102d306ba29007091), (33, 56, 7, 14, 17, 12, 0xf51329d8895209edee9c8930ca16cf9ad6a7093005c6c3eb8c891009bfc7146d310815bd812d4300a006ba88c9fa293011b662d539291015ac21ce28091001a23265fe093001a019a2cc0952019825054830ca1292bcadc509100590dd21130972058338c9e5295215823508b829521181f37faf00e20681a0dcb729721570c33bd530881670c1d4132930156a3f8da9095205661ef63b20e2165bdaa534291011401226950080063d828ee520c2163be4452100c20637b8c4b0314a112da5c02510ca06162f68803088121432cfdb21201511dd2b4b2162150afc5941108806028c1b85208016), (45, 66, 7, 18, 9, 20, 0x3e8dc628114560ac1f15f5560841180247c373b50314560ad1ec6c0bf4031580b1b773f782214462291dd243c74431182a1b6b89dd030c560ad2d6b35650251584b07597936320c462296d463ee9c031588b1ae3640f50105600c5a51a1054451582b1684b58f22944632919f1ad1a4031180a1a632a7f9010460085969f93e8031588b0a51da3dc2905610d1918aeba082118024a2d3ef2f2085620d6859cb4d2031180a2a14fe81d20c5602d681b7d3b4831180a59e5764c0290461091772256f825158cb05d7fd8310145602c574422ccca4118c255b79302b0104620856b686870431582b0979f1cf52084600965e3dafc2251184a255cee2952945612d5530a3788031188a0940502122085620d23fa03878a4158c344fb7eae30944632853c6c2adc841188254b0795f62084620922aabdec8051188a047aa56cc1084608821150a3108415803443d4cdd080846008a0876aaec02158831811fa4932945632d503e1177c8415883540577cb32905630d5), (68, 68, 7, 18, 9, 20, 0xfde32e2130c460a96f0c21640294461291ec9ba50d2905610d5e9ce4b991105608c5da30009c814460289d72cb65f214462295d6e362e3014462285d6239dad0945612c5cbb909a3008462086c760eb34308460892c0e3307020c5602d2bfe6562f090463085bf9ff94090c460a8ab8f8d9212105600d5b5f583f30945632c5af0bb3bd308460896ac85dea6094463281ab2e524c10c460a82aa407ab70105620c5a83f15fe2145622d19e20abe60085620c296d10cb32145622d594ce65b40085600c2930faec93085608d68ff11f650905610c58e523ad42945612d18e2da5bc31046089188fb04603105608d187858f712144602958552ecea090463081834ee25b00c462286824ca0e01085608c27decab630905630c57a8a43e02145602d17a60abbd2944612957a038f520105620c17750e1870145622c5760d07e92145602d573c8ddb83085608d270ff4a2e0104620816e4da4550084600866b124b7320c5622d669ec6f6c81046008966a2e840314460a9165bd1414090461081659a67a4890461089647cb82490846088a6159758c0145602c16155bdc030c460a925f52b1ab2944632955c9cf87a2945632d15ad3b87e290463091590be10510846088657b4a8d000c5602c25712a4b200846208255e473510085600c6542cd1a82085600d252f3a74e2105620d150dc5c100084600824f0b86900905610c14e4caded3104608954c6351e60905630c14c1726d091046088947fdc3ea0145622c1454e2219314460a9544d36cd221046209142d864ea20c462292403f15da20c5622d2), (85, 66, 7, 18, 11, 18, 0x3da7f1440c4160851f5be758700848801b98e0c554c2160856dbaba64d09448481767ebbf94c4160855d90b82e22145889474442aa2043120a02cd2f6bcd21448085731594144c2120816c2c4be8b09048c01708e3394084120011b6329c7b00858811ac78e191042160842b160ce0500c58091aadbd204802162042a881c224214580946a12771d0c3120a12a3eb39bf09058c1168f9e0ca483160256a1b4c9b52904840567ff51680a41210119bb5a3648944848266e9e4f70a5121211996b516900c48081a5696cf580316224293e9d01629048c0464bf0672883162252906bd9dc90848202a3e029dbca51632558b6a72f620858814a182544e8a416305184c4bb5910858211a12803e80c5120a118151092409458490600c8305c841620557739af6d30c482859dbeb09b8a516325175e5bdd9294484855cfbfb53c0312220673ba363a210588145ce969f9c031622466cb1329329058c155ac5fb5fc8516225568cb82702085801498e437884c3160a5662739d6520858015988b4bdaca412301560ed5f0e2144888457d683534a51612555ca98b7809058410560e086b443160a46582aebe93145829553c013082241210094c4d1ba831458294529a579682516324146034b7b20c588958ffc3c5a243120a0a371bd55c210580144d9e3a1a42412100533e755a8094484804c71493fc831222162fcabaea29448c844bdec33f8841220112b034c1010c582908a8ce6ff48312021629f1711d210580154a4ac5cdca51232152723474d210480054894e25d442120806213d4ba510c4828186f61bc40c2160852177a001709448c8144179a53003160242104181bf2104880543a380974021600460d02012a09448c804328032d8241230010c9e75a52084800582e6fb2f4c5120a150aed263720858815825a65cd402120006086bc40c00858010815cd513c25163245044b963d2145809540a4e507824163041), (73, 68, 9, 16, 7, 22, 0xfe13a8048840524a2fd345d0120051a015f1c79bc520445a0a5eccd4225084012481e9fab9ff00455a8b1e500b6bf28451ac95da5fc7290041520b1d87b8ac9280152435d5c8ae9d28045a425d56abeb128041a405d24bb56120045a025cfc54a3f080152c31ceb75f452841524b5cb5317f50841524b1ca41d55128451a495c9695590880052422c852029528051a415be21694d200052025b66ca1ff20051a815b1e1529b00445a8a1afe276ab2041528b5a95ab5472040528a5a9209c4700045a821a5fe052f200012805a49323088840124829f6122db284112c959f1f8f612001520359f0193cb20401288597087579200012005955faeb7284152cb592d76e37084112c918bdcd02d20451a09583368cb320441a8857c0f752120055a035777a24b708451ac9174ef702d28055a4357299c10320055a8356b3089cc80445a0a2698a7e6d20041a0055fa298c50040520a15ca857d888045a4225bdb41d500455a0b15b3212c120455a0b557f6f3ab084152cb1511cd16100055a03150dd3a6488445a4a24efb231d00045a0214ee3f8c320451a8954e4cc83c88041a4024ab6837300055a831460d25af00015283142175a5b0041528b140bf4c1d0001520313d737c7b20445a8a53d21beeb08055ac3135c928b920441a085344c8bdd2840524a52fc529e100445a0a12b9cc5a880045a02228cf2c3128001240526cc03ec880012402225fb75f20455a8b51f395b912801124151d55f2d888441a4821c6545ab0040528a11aae46112841124951a615f6128455a4b5178739ff08051ac1116b9aa8128401248511fdb3fd0000520210f02222b08455acb10895460d280052425067c4c0f20041a805), (87, 65, 9, 16, 8, 20, 0x7e6d006a600000817eef3b9520445014beb8a1888400b4431f3bf197a2110e2417959862a5088a1297c8fcf4c880438805da934f0880228221eb6234e4c0010112f082d39510005100b7c7df8f30010042bb9dedbe942080495dc78483a2011e2116dad75760080d02876a233c3084410903b2af9d0942094495d43d5be48114404ae9b24512100a21047486f4e2900450445a13beb284021c401cc6f737a4010e1016474bde22088f0a8722971b530051042b8e80d8c480034222c6103a2c21144248e1d0642640805021703c0f3720441010b811ad2a9020340a5bddc33aca004a20adcca4abe508821216dc2a55e804438105612631a4020340a2acb7f9b40111e050d5db8e3e4088f0296a63ccbd10445054352881c54820342a2a905cf7cc114e14ad4625de6600aa08d67c133b488441090534dd66c84003442196852ee44115e158ca198a924008700164d73ffb28402890b24855349820202a591f99f8c2015e218c77bb6461088f128629f6f27084438903126777f9820a02b585b652540001a010c11cfb2a1088a12860638d3520414016af5d89d78022280a179f04c3441010150bc862d710088f0289e14f48f084168962f06b2789020940957387fd442101a250b87b426a608200a55b40365b080000802d9d96448422bc4b16941d0d4c010e102afd3e42e2080d0a8563fe34e884478944ad243aa98221c2854f7bfb8cc005011aa59405a90008f008926b0bd330447854a882e6b298023c22544135874a10002429eac84364008f0094f2aed50880410804608a9f88002bc0312ef0633c810100529269eefa200aa08c486ed7a70840009024031bc890221c0851e8723ca411141510e7691ca108aa12c45beaa63100068442206f3d99820342a50b36ca8a20000201054b8d4520005080828e95cd20453812a13cc0ab9822bc2b508b91284400501188368b46a0008f00840fe401f0040401420566acb4422284a2), (55, 66, 9, 16, 8, 21, 0x3e4d6ead840288c11ee9c3a26408822217b2fa1bb9002bc835ea357fce108af32c7a24a9619400a0c35dbfe172e0000d2087694f44b9420a0cb5d9b1472e508253257560c4c59422bccb5d39019ce1082532474be3e858020348a1d0cd57b6008af22c74285a2d940094c15c8a7635640887221721f08ad900094815c7a58b7e0082d22c71bb54f98000b4831c1e4a2be100aa30c6f7022718420b4cb1ba5771ee508823216b2e769394221cc85aa75681e10887320696dba1d9402bcc3596be62065080532164bd301d940288c1588f78ebe4082522562139ca58422a8cb1800c3b2e0082822c5f4c0ceb94223cca57c424efe508aa32d5c27de6584021cc016b2947e6400052015a4aa5f994229cc9567db6f56108a73245775ce6b9020008855b61be0610805320563403fb842288c91574330964082022551e3b617942288c95390a4bce408a22254de976298022a88b133df461e400a72054cf2959590023c8252d6c57c6508203254a8c01ff8022288a1286fb0c6500823014976c37b940034c2525ace1e6100af30c48a9f4858002bc83121589c7e408aa22d472d01f5940014c050ef8bfa6008082284295a04d84029cc110a4fde6e408af22d4039cdcd9402a8c35), (87, 67, 9, 16, 8, 21, 0x1f4efdef11000d108bdf93843c2011e610fbb7c737940000c05f72c1bed080140863e19ce01110805120bc23c4bdca014e60af6fa37ff840208c01ebdf2ba328047984bd36fba22208280ac7a0d8e09ca005a61af28d17f09002bc035e481b279084128923c601d4da6002d08d78a0e0184a101a252f05d37819420b4cb5e00cc780884040945bd12adfa10808128777d639a4a0010212ee538cdb9020208a5dafcba69080450843b54e88726008a089758e5ec14c1000142eb048cfc940208405d5eb647920457816bab2f622e0088f22874ee743b44105a158e9a142248402a8431d33e2683080069843a5a4178a20008088744ba7e824100a14167f95588940080415cfca3d9720416916b90a96d16108823207194656e4c100a142e16adf00842014481c2c8b65d20053802b7f539ac9208870a0afe95b2ec8005a41adfb958b98400a0c31bee20c2b20445114b7a9668ca608250a56effa474c8105045add92aef694223c4a5ba087b3708406994372d61e2a5082d12d6d9273df44015e118dacaaffc9422bc4b5b1a4950b28400190b607d2946500083096be993d6c21040648d4969d5440021c002a8569e5b00047904350a93c5e4000d2096a0a2df822011421153e22a3e8020a00b1a46fdaa128451092b435b811e40805221680c44d024111e1514e5d62664000340229b841e010045501633699f9b90088a028a6acab6a4c014e10acd3878129802082059958b2950801288233217e1ca0002d00c6618858bc2000a600cb747c988402084019687c07530451052b2be08c692008f088a579a93fc8010e402c9929e0b942020ca59168053f28406994b20c023b1208820a0a39c5052c8114e44ac66b5c429022a80b58bc0782130441050b1649c3e610025304628a485e421050258c43da550980034225882d04870801698630f7e560a5080812961ea7071c21050658c3afb67d942228ca58705237328010182b0d2fc43210008108617591f5221000241424a6e42900034025), (64, 62, 11, 14, 7, 18, 0xf963a432041640b7e384da3a1014929f3f78482040520a7ba4ccd0c10400a5ed33c8fe84508497a223b1f81010029e5f82a62041400b7810b76fc10590addb2322f704508297681a723c0049085d430dc9a8445a4a725c55a1a015690dc558148a840124871238c3dc110b0a1c3704962801404370c402a18115b02dc2fea6fa0056c036f099135a115692db637663b040402a6cbc28dbc11520adb024beb70056c23695cee048115682d9a775d828045a42664c0257a011b10998bf646b0446c2a641a7540c00190898997871b00548236229269aa0142105844ce827041402b5e98bd2ea00149097962799704408285d88b47f8114682574aba14200112015c47241bc011b0896d69cfae8451a4959fe75f3c00400856599f5ee0046c02595a4873a104492562a19616000640258681f58c005908d5c7648fa040640a56d40adba110692158b1b6ce801644354b91beca015b10d50f46aea045080952572426c005008d42eab6b6805484350671694c10490a53818dbae041520b4dff6c46810448252b04f27b00508214a40bda5c10190a9191676b60055a0345b2e5f08110b02111806eca0045a02443df072c115b0ad1038bf82001520343de7a568114b0250a1e36be801524342379e5e80014809051140bf04024284134ac038115202d0111fef60446c0a40252da4a0044905), (44, 59, 13, 12, 7, 17, 0xfa145e31080c895e2d43ac2005910fbe221da420a025f2f28a2e8446c4ae40ebeb500ad887c773af72115b12f73f5c24402ad21e6da071e841524bc98ee3c808ad8177698bbf4115b0aed3c9e87022a405d90f7e5c84508499cc98bec082c81733a9516a011690a5bc267f400a021c9436bc08451a4979324f88088d814e90649f2110692191e267080236112d0a06c3000642258a6668108ab496b072e30210449254fc03c6420292528560e260045a024e9d65f5000c88487cfe910011b008fa23f0c402a4219d551e9b001642338307954082a4166d1f881a0044904d0e475d002ad0199f00e43045482b272e8629008d88446649e30005900c78a6af24222d250ef2bed480152431b44690400ad80633bbac1410590ac46f94dd4002921053f47c0040640a090c31d808ab4160e46b0cc015b08c130292942009240215b52d040642a), (62, 66, 11, 14, 7, 22, 0xf907b22e284448ca7dc547898a0009301f3bc8802284064ca7aa104c288010b201e86fb4fe284052ca779c0e3d8a1156b2ddd10e582284140cb767ddea18a015b30dd64f43a228055ac3750c85a78a1009321c3d0da322044488a6f8551698a1054b2dbd755536280012c06dc3a6bc8a1044b25ac8c847a2040248869825386881146a25a37acd2a284040ca65c45d848a115b32d874dcb26280064c261d0a3bf881116a2987255f5e2040648a6157610e8a1049325840ac2522041248960119fd788005920d7fd8dcbe200124815e71fa078a004030576fbf6c6204508895db65f028a1004b2175853a9e20455a8b5af7892288105922d69ac81162041408b5a362f18880044a0564b56a9220446c8a58f2d0f388115222d61e006ea20452c8958275fe6880156a0d5f49a0de280140c356e090e98a1040325595ae562200064825477986e8a1146b2551dbf93e2000528253bd93c28a0106b014aa9444a2041528b505d2f468800092013c625df620052c814eb779a68a015230d3746ea722040528a4bd0e4028810402252f30001e28446cca4b17b75e8a0054b0d2c26530a280124c1499ab5fb881010229250e672620056c83485fad79881044a251d683022280112c146cee91088115b22d193f11ba28046cc2459fd5118a115232d143fd1ce20046c82440a0517880054a0d0a04889628051ac1426e241c8a1102321), (61, 64, 13, 12, 7, 22, 0xd9598b82084152cbd3970bea08452cc9cce9f4b2084024c8c67adc1e08446ccac531b1e208055ac3c447350a08441ac8c2723e3a00015283c0373ec608041ac0bad4188a00446c8ab9d32e3208451ac9b4d297fa084164cbb2fd52f2080100c1ab6cb11e08052cc19aea17de00055a8398c193a6084140cb905cf1b60041528b8e01910600045a828b80e72e08051ac187ff3272080012c0870f7d6e080112c184e6853e0044488a837702ce080152c38107b6c208045ac279da62fa00455a8b6e2c5d5608042cc06632e7aa080508c162a872ce084112c9623aa53a084052ca6079842e080052c25ff78ac20041408b5713a1ee084064ca53a0f65e08455acb52113d3208046cc24f8b6786080124c14728bace00445a8a44b8224600046c82443c202a080024c0407d476a0040528a3ff53ff20045488b3e93d42a084548cb3d7d0ef608456ccb38b846460040408a379a1b5e00456c8b33092e7208056cc332544722084100c92f33231e084124c92cb4fe72000164832ac2dad600005282293e83f6080164c3268e4eae084040ca231e425e0041648b1d851332084012c81c61ebc6000064821a89f10208442cc819ce19c6084000c81389fc5e080548c312e70a5a084408c81091e9020040648a06fa0432080140c3052a9f9a080064c202d566e200056c83), (57, 65, 7, 14, 9, 20, 0x1d72f2ea510c14ac6d49630d20880a460e8e4e6380440122073f8852922102918d98ac091628403210cbb0e57c0060a161650dbb644c500285727fa32a90080851183089dbd00c10246c01692839060912b600ae580420044112f880b84042808523742ffdcc10414ac0b92ddc3110a01108dc23bc9c205010a26df80baa6100060096be06fde21412251b401adc80840842158abba64c2101ca12af687c6a5002a1a95748e75629403211aa3854ab8400982254b445e4c8204815aa1afc298218014054e64ef1c89405289a64f17a39040100b52f16dc7c2001c21294d621dc4200402349e9020721006095a420f91c8860852351792da5083050b4a7efa4ff0418085253da2a473210160d59cbceab914a09928cd74236f085050b466b7982820102008d2d52d51529005095966d88349480a86acaacd11d0a1054b424840f7d0420281a322c87faf290170d590779a6618a02548c6d332b20a5054b46344a3ea25082a5a91524f3fb0901304589edd6769860254b44de7d68403050b1a24a24e011200a1130e39872708403204852e50ea44002844428cc92c82500c806125b51f8620291a308a30255110148c5844f106790a0b16ac1f0dab08840182460cef26564100c12d030dd73c108148c2), (85, 69, 7, 16, 7, 22, 0x1e0987dd42941592d1edf07ce084802c842f66294660850560b47b07ba4ae52003602bd0539d3720c15a2d6e539820d94202d94a7265242d402046011b8d2ace884102300a5b8ac7f9708405b284dbb1573800608c1216d8afd78402056031b632b24ce4102340adac41f87f09401b205d612004890202c14a6ad91bee4a4056435755858fc65202360aba080f06708001b004cf880a7594802d84ae745823a4200564313395083f90280b051399dc9e9c00c1582c2cc55d7a98480ad862e58326b820401602272a7cdc1a0182b058d907471382081580d2c50bd00a10602c14962228b3f08405603470be61c6a4002300a9840c397b00805a086be4d08a29040ac06b5ee28716ca0006c052f6be76a24082304a97a4a8c51214018215bb82bd3984200d9025d93d7f1402016021ae84781b24182b05ad6d19a82729411b255b2fb475a90a02c14ad948b1fbca5016ca56ca2e7aaa1000b21095fca8aec214058291ab993bc090808c02ad5b71f0e482016025aada857f91280324135580175728401b214aaadf73814a02c948d3f09062c80046815298c9d0221080b25094b6f9fb720411a254a2bcfc9e90200c10a511d21534810560b527fb448380200b01033e1ea6610901190459ee5ed5c40202c1444ee19965082016024a74fad3711280b25133a1f3a9100c05828698b3f52984a08d922cb9864a40a50464946597193005082b25a12bd1522328015b0d4951f5dab9480ad86ac959ba84483006085a4823133c0102b4185235322a720c01a2168fea0c2c10a00c108c7df2f87c03046891a3dcb76e85280324231de9bb7a28005b0908de7739a8080ac062c4eed612c20046c11226e3ff2a12003200b1276d87d0901590c587e862cf9000ad06a43e6c34c42000640121e8b1c461280b650b0f0f003b20c05a296863507d590002d04a42db9abf08504609461667335a4182304ad0b006a55214118255841a0e8090802c04ac1c5263dca0046c1520503c84a12823248b01c1610300005a084), (34, 68, 8, 16, 8, 21, 0xf622b28f90409902bf5a358c490409802be6e5e8788860b8563e09ef9c21060b8169df57d85e9040b806bddfdc2869860b856bd9f32e7990609912bcad75e481860b8569c911cecc184098429c89b1920806098123c6a4009c98401840bc594e92e98409842bc4720d78106098129bdbbc7c6104098029b9ef6cda90609812bb7cf1ea28060b8163b62661049840b846bb1f2c5448040b8063b142d2ea98403844bae8b3bd498603854bac60b8061840b8469aa120c8c9060b816ba790bc66804098023a11a401e0840984219d50d9761840184099ae22cb690603814b99555eea186098529925da2871060991298e26376c8060381438d87c1978060991238410870680403804383d9e38190401900b8229cc2090403804b80d96b11804039043), (94, 71, 7, 18, 7, 22, 0x3f2bf691c5288b5948fde154b74821168096f32766368042ad018de452205d30c5482b5ba963e51c1208b5840f3a0f5794241121085e13ba8e394828d60abc00c403129441a48577923c9e8228890540ed92b18a00310b0202d6dd840390420d402da6d6e3ed29055a43574aadbe64528835908e89c1a6ec8214b2056cd4e4c92106224052597ea1d8910c5482b1b24a782604188b4149649175770c41020811c8e92c7e10a22405238fb473209144482a271f2f0ce8618ad856963d7952fc8314b2256c1cd9369806296448d828ee78309441ac816fc7018082188585015de077b5ca5156b2d5bba0447414a2ad25a377316c4821055a0346ea7655be41089104b5d1429e94a51169295b6dc4a0c84a284248b66bfbe1229455acb46cd789d402188d85415916c9d74441120885ae64970010428d00a5586e09f529041a4056a2289934120835800d3800eaa0a51421251a67237bc90622d052d4b22169c21455a0b468eebba30618a10529517523b9c24156b0c5a2da8448948224212b3f79121d29451a49567eeb9962120834802cfb2d69588315b22d29f390d9300423641053de9708830c42c284a7577c441028810104ce2db913c02116a0869af78ab714820d6023348a19d509441a481668f0ef28618a585294ccfd44ec851022215991c276104a22d650331ff306c91440828265ea318e2228890542cbb4afc9025146924196f558ad0042ad41852de74aed0144480a165b93f9204288b4148cb54a8ec88310b22129685bb4298a2a415ab29d1c03c00c46c0a0a502dcac4410ad906949ebacc848410680159190a311904204402d221e873900842c001a40eea7da210a9046347fa09df08314202528ee1a59094822d212b1cad72ac0944484a063872553a21085840346d9f21700214680428d788c7894828d20ab19d8bc4229051ac14632b2385e0288b5142c5ce9737c25116b2858a0c960c906216042d1225e865090508411624168882410a9006b44672b204c415208d588493f6410a204042310178cd5210448025619e76448520a10828c2ec8c9642511212858474c92a1042ad01a507c77ca131040820560cb776d2520a1082ac16c8c634c310b0a1682cac628886216140d04d11a6800c4480a0a0945024c528a35928c0c71c3f08215b00d2), (82, 69, 9, 16, 7, 22, 0x3fb8510ba1088b4943f53f77f030452c294f1f342b2940216202f821b61bca0106b017be45f718108a58921d85b133e284164cb4e94d4db584020d600f2b950454a114b125782de9922108a58923c0ced62708441ac81de83ab4014229624a6e68160d8a114b32536c278136100891843ae998f5108045a421d235cd8d902032452e87ab9048a014b305341b14a185080c89499e7fe4d908441a481ceef13f5142216642677366f744011b088732c3bbc05000c884993c7046128046c425c5d74e5e980012102e1cc7851ca0156b0d70d12a89c500859809850fd0ff280448c25c049523790022d412de8745f54a11069216e362ac182088d85416e60e0e328455acb5b6d1a5b494222d252dad6b3ad02105912c2d313694a600ad846b679dccb2280164c34b2568ab29020b205ad8a37df74a01121096b445714c1088b594158f222ad08046c421a9398da9042224650546b15d08a114232529937d5705082c89694c9077a128442c485a4c95e93842224650d2507a754a001910968c86e69c108a11921460f093800445a0a0a25fdab498009210acfec323e4a005910d67bfa58fc5088359093dafe4513045482b59dee242c8800b2118cdab0610ca0146b056692358d8108a909613368918108051a4119968decc1422362524c9bd75442115692c663129ba8508ad89692ea3625d00456c0b1973304881800121024b43118bc8111b22964e0ddb6a60889054b2556da882845484b491fb078a90009200ac88e620a40105902c63eb1ae524002c806b1ec34cfd08451a4918eedb9d1842236650c6f1d5214a01421056366989b84088b414919cac7013041642b58bacb4e2142216242455d9b4f8a0142305223a57adc4088591090f71c24220045a8248760d31a8822a4158c398d3294a115212d61a805a284002c80690917e32e20051a814839afa4818222415241bfa63342010690060b9cea291080c894500de946b28042cc05), (49, 72, 7, 18, 7, 22, 0xfd209462ca0116b094d295293d203014828ac400aabe203010028abdb1a1652430100a8abd4333f9ca1116b294bce796ffca4116b095afdde7d72450100a89ae0269d8c24116b085adb1d0f5c20116b084ad8d4a1c2410100a88a8a0ee908a4116b091a35fa070ca5116b295a2bfc3944a014b1054a23f6cf24021168086a1b5ebbe08205900d2a171d58c00511202819f60f7efc24106b0059d3398f9ca0014b0949adf24f4c83044a2569a282a958a0116b09097419cf82430000a0a96f02749ca5106b215958809c5c82014a096952fdb2aca4156b0d594cdb4d94210401244914916348a1116b2909061c65a0450500ac18f915988c21116b2848f1a6e8b42004490448e05447cc24004b0058dc74fe1c24014b0858d456c0d8a4156b0d18a78b696c20014b08489f0c669c24044b045898dc7faca4106b01589372c4542015690c488f3f0b144205908c688b3146d4a015b10d487016422ca1106b214862cbc164a015210d485c3823ec82054a0d685595bbec82004a0168507882aca5004b21584609dd542014b1044840df0d3483014829683a4b1954241169085814841f24210449244807fd12e40304482468006e75ac82116a096), (57, 66, 7, 19, 8, 17, 0x3f09fabc8241d0092fa520c32850744a43e6d33898240d0012d5e9077e150500a472b7293e844140091c7e6575b09034204b19b26e1a041d1090b093f7860d0740a4a9a1f082454140a81a4a0213b09050224a5e6f271824140092877698a9050502a02068365c0341402827e8c15b7010342041f2081a52141d128079099330810744201c8927ebc041408906125f1580d0740a097ff361aa541412915ca08fcb0d0742a49707ebf6c141d0a90592a94f6850504a41508622b4341d0a825088121401074020138323938340d021246bedc5705034284117620024041d088045c81efc090740209152b09bc44140891405299c6910504244fdb83d2c54140a913d242b78090340008e9bc1080340d020237fc8814850504a00d4778078341402922e26b2f2810504240b025cbec041d08902a21c114050740a009157366c14140a902086ca7105034280078be1cc2541412811e2883c0910504204755745f8141402901caf5df1090742208649afaf434140a82183f59748105042005bdec914441408811592bcdd050742a005071097024140082140bf8dd090342008464c86b4340d0a02119171560107402403b491844241408820b561656050740a4023d383b4040d0800064e37530d0502a4808701bdc340d0a12), (61, 69, 7, 19, 8, 20, 0x1fb63908c0341d0286fa538b222020a04427cbb88eb209074025bcbaad1e988828112bdfe8e65c204141084efc98bfa20a0e8542777eef07309034205b88dc0f590081a0029c1b7b2acc341d0a96dd06fc526120e844b6e3b72e500d0500a1b5f23b1d98082811299adbc0b48240d0016c6825a1a52a0a094adbbb3d5710d0502a1add54abe80483a010d678bcc54c54140a95b046f57a60206840a56322d012050340852b064d8294083a212953ef5b4c4041d0884a750b10660a0e854a4e3ea06f29105042564b56048848828210b1779becc25414128587e1938e60a0a054a4327ae0d2050500a52161332f984828112cfa81c8ac8541402957c55bf2a0220a0042b683e03f0090500219aba7c2098681a142cc5065e4ca141412945f27395a21a0e85432d3eaae11150502a1567aac12904828012cade40adca140d12145299f62e4220a004aa8a343752050740a5140f6a0794283a25289ff69a8c8340d02164d7f239a10a06890220e98809301074225106ca3fd88081a10086738c5944240d08063248b02e02a0a01429659f69b2010740250b29b31784283a250858ec3c244241408862b4b8f3600a0a014214da7d1528105042508ecec0a80083a01083be1833cc140d0a141dd1665e20a0685020e342d2308107442106e6db418828281508233aca2c0240d00061058d09e2120e844308154d5b00d0340818300676580283a05080281589c4340d0a06), (44, 62, 7, 19, 15, 13, 0xfaf0ef3821b0280bb314ba7842c1204e4ec282461b0284b5dd397a942c1214cc762d2662b02856fc1baac08ac0a01bb33f79041b0084ae7ae6ee04ac1201b422c7fc62b02846ca8727c90ac02159c5ed9ca12304016467b879940c101489e1046e61b0285a26d955810ac0211862ba9b222302015fe324c9908c00157ed5bbc241b00859efc3c47084c080279e2cc5a10304011dd78e22104c001276eff76c52b04845d88b24f048c100169a9aec260b028518fc2f5780ac02055c722448603020416635d5b980c08144d628f7e12b048152f8e1a2984c081642b13ad6023000150680d79884c08063d39f6ae41300058e3b580e886c0a062f0a1aa860b02840b612348880c0804292a444e623020548bf940f948c10151e5ae0a220b02810704bdc194ac121514bbd5c852304044467472a804c00060d6f525601b008182cd14a088ac0a05099eafd4623020441099959184c0812), (72, 73, 7, 21, 7, 22, 0xf976f65400885840417cb04a758044ac2831bdf024bc4822061002def4eb07a0112b080c6f535deb1208958406b78fa140180468ca811bc79700488430654023e34ee6041218b2b081ef12b6e62108185008f470e79894848c24157927ef92c043565418bc3040e4e021a32a045dfd986ad290818480aefa8f1919484ac2c3576befc9fc022461408dabefc9b20110b08086c734d9cf210818500ae392ed4484840c2401710fae0c8243565618387fea4740110b0a082c0d99962290c195808dfb40bd704868cac106fc26c47804246140836ec0bb785212b090d1b284411e0909585860d470721c44860ca4026a0a6c99c843165412b4d11e2c6021230a045a67c71c08088584045514243811044ac2834a89efb5c882246140a543c997cc011230a042a1bbefcd0909584862cc6397e390842c282564bf3a1c2043165011320f6bb3c021832a001900274a6208d19502946ffbb2104842c2c2061edd225824206160030a1e1844421ab2a0d1833164f3210958506ac0f9825304860cac005f34fc4d884256141a2f21372b6121a32b0457800c6860909185820b9b173d990868ca8155c8405db8a420616022e2a289000112b080c26f83e3430909585862b7aa745b9086aca8355aa7172a4a42161212ac2f2bba60210b0a0855ef7077a00895850612eb30e3f1484ac2c34573a915f80235654184b6183636421230a05558f68d562908585848abb9becb00862ca820551adb054842161012a7eef62be021832a00537c3d8a8810c1940049b0cfbf910862ca8244b4da6bac82356541ac48f2d0ce421832a0151b812f102088584049077e504100468ca8108367fd14c023565418c17fce86c411ab2a0d206f2069b01081850028316a3fb90468ca81580d6721d8a4246160a205698034521a32b051), (39, 71, 9, 19, 7, 22, 0x1ee8db4045012b0b0d3c79dd3d4802061002f1dc0ce184068cac11e1f5b06b200d19502bad444f800012b080c33a2e3dec002161410e70245f244062ca422c6afa341280818480b75d5e9240018b2a082decfa2220021610115b0d9dc514068cac14a8556782200d5950694f25ed16001832a0069e08bdd4002561018ccd2106b0004ac2830975c0440080958486126c643d25012b090d64c212c18a0246160a466be0870404ac2c3089c83c6f00081850030cc25c510018b28089faf61b5880246140a3e52349b80068ca811769eac10880c194804dae10a56001ab2a0c5aa13f598203465608331b9c5f1004ac28345fae6561200958406aa99f35091010b0908905b985e8002161410201b8b7044040c24023f119fbf200c19500a694a1376001230a044b52ea34880216141210dc5c8f00048c28101e0a3d8a000d1950203978df204012b080d07242497c00256141889516fcf0006aca830), (92, 71, 8, 20, 8, 21, 0xfec465a70088712087f99a7b26401ae641abe26ea2008235cc034fc02f0b50044b89061f3179fed30897108d7dfe2a84a211262108fb3140f640025c403175f4d8a90046999021eacecee72808313015d41355091010e221139f8c0b2c0231cc821f3b54a3e4406198804e6b4c1122089312053b3cf3eee5012e261ab5fff03b48221c4025e93b5ede9004b8806acd59571d208d7300d7983dc379001062001321a0bc840221c4021e3753d6b8404989822c5f73a68900c7308897bbd9aee411062402ef265b51c8225c4835dd2546a9900619900ab9e7207a00883120036f62e7ee011866400ecf7374f4a025c4435599db1d58044b89063b0b511d300883120075b1cb80a60126210aab0255acca024c4c15520365d444063988449b79473f000c73208520b3323e501a6660aa3e4d554c0021c4821474137c71046b990698e79e59490087108891b8724c26012e211aa2cfd04120230cc002c225c2c08046b9806383c35ebb08083130050340e19e011262408e05db5bf88220c4804c0b9513e0844b88461803c6e7b280c333014fb6eb7c12118661015f5a8e2f44025c42313df8ce73900699902a705aad2f080c333004dfb713da611a6610adbd07b61c2035ccc31323b5965104619900962eeee3030897108d2bf6d91110118e601157c5723424221c4222aed4e0d5904438904b5cd070a88008710088b89eed5e0012e241896f29b1980221c4820aaf458f0404418800553de495f008d7320c6a2e7a1de40126240a92a42c42c2034ccc112426b762900438804a461e0cd9308c3308168a59e042211062100d0ae9de04c231cc2259e9379fc0046b980613a2c6cc9200931005470d3585e4010624028c7cbf2e00221c4020974ba3f8980438844a2dfed69f000c3320045b9945464012e241a898b6f6f20221c40229215161380069990221eac5c9c00897100c239eeb5664010e241286dc705ac8235cc8358cebe23f1044b8906913165e5f000d7320c424a1a08920186610102fe59d520031cc02205acde76900418800a0a2ea138900831080813b7207921106210142724b7180230cc80084b1443310469990290757a328800c3300080dbf8dd64018e641280bab7e188221c482480d28eb01044388049), (35, 68, 11, 17, 8, 21, 0xfefdfd2020097100df6804672280831301d5fbfc3a200d33205c88a50fa080c33300a9dee78a080931304a239dc7a0808713089df50606280871309988c9986080c73308982f3a5a280c333018bde20ae280d333056e94b1aa280c733096e7e41862809313056d8f807408097110c59dbed02080d7330c52d3304e08097130c4f714352000c732084c92b1ae280d7330d4c9025fe000d332044c03eff22008712094459d0b2080d333043e0f110628097130d387bd98a200c732093741f3e410097108c2f8d982a2008312012f1f494e0808313002ce6afb030097108d1dd3d3da2009312051d5ea37600097120c1a6743fc28097110d1a0faede00087120811e6af4e000d7320c110fd04e000c332000cf6250800097100c0ac18a0620097120d087f382e200d7320d), (34, 69, 7, 21, 9, 18, 0x3f02b98a31096011a3ef651a41404b010d0e3e165600235900616fe28ea4421ac80347277b86521096001a37bcca560486b210c1b8eaa55cc43590468d4eac51f0218c802269f575bf308d6411a54db2a100886b208c19ef0cefc242580860cebfc06c2112c0230a5b3a6b5290d6421a32d4b73080843000818b9db47c442580460c2650d9b2110c02229eae461c0908602102e7bf92c8044b000c26f8502a240218044433c54c1d1010c042219db6a332908602122b0ec0679844b008d24f2e9716022180045276605240212c0030513b59d230096011a07377a6c8846b208c22f41d564a42580868947886291018c84220a035cc1010d6401824dfc07d8804b008c01a8ed9720231900450b5127361012c0430012407741088601104075f4e1c806320888), (69, 71, 7, 21, 9, 20, 0x7ea94a1b0406b230c0f79fec2329096061abe9be6a7c1010c0c203d0c8f48c84218104af48e3a408084300085e86497ea090c646103cb24006a2112c0231b8696d6ac84359106aeecb778c8086b200c5d85ba579108d64118daaa6e62a121ac843173c6031740235900636781a5f29844300896c2c11d52008c64410583eb058c121ac8c306e975df188225810695cf276928044300086b246400b010960418b635178bc0110c0820abf371edc84319104ad0e026a71404b030d09f4c6a5f21096041ab3594ac024212c003565cef39f420218084248d0da0f8086b220c58fafaa66010c6441031f1051021212c043163d00f358242181840c78d53c50404b030c08e48bb5910086011091b1ecb52621ac823562db40004a0258086a4454626b1486b230d186a773f7290d6461ab03eca4b44218c88245ec1d4c3482258006b3c0c112d0084302081773b9633290c64612aec01909e5210c0c255d6cdb8c4a0319084a3a98be66980430089474eabae7090c64610ad2bf13b26018c822519d73bb6c043191042b39ca86488443008866518471d210d6401aac59704ea5010c0425173d70b3c042181042ace7d24d8046b220c657e51856290c646122ae15c57c1212c0c30555d3e808043591060a9409ae784843030854cdd1d71208c64012c8bb80ccc4210c0824509b85484c2319044b1fd130d50044b020c239e2c73e29086061227147ff6e411ac88358d6304e74c0258046a19e011bf1086b220d13320f595280d6421a86091ae7c011ac88308aeda860482359006b13e2511a9806b208d422e86f87090960618a2973fc3a2012c023102317e584c4258046a82331b270084b020c1), (40, 69, 7, 21, 11, 18, 0xffd8719a208d910297fc30e168044c0011bfd730494a436420abfe74fb2e101b23044d0b1262a008981021681c907c9086c8015733fdb8180236440859809d352411b20056c69145f329098182adda455f78046c8811ad64a06088436440a33e6e9972501b2105493f65211110980422c883d48b8484c0c11630e17b744026010891801071a62130085588e24832090981820c311d25b9486c8c155f7432324c036410a8f716c96a50130105478f7d9df20898102b3c104c689484c04155c120e6fc8436440aadf0e9a224113000566f3ade7a28098182834c018bf9084c081558eb4bbc4c236410acc336df4e411b220565152f63300898102328358da50486c8c1051accdc54c436410aa813b50cc521b2305138505c2930098042a1be6c1eb8486c8c1149465e8ec04364408a4973dd04101b2304022817152280d918280a6b89088484c041144978eb0804364408220792ce2421300055), (44, 67, 7, 21, 13, 16, 0xfad25b89290e4202be30784bc121c8c007adc5a984c228040b6deed895040503000db644fda290e460239d8aab8122140202721346c9c022810035eb7eb24988500815b3a2ffc6080e4600148a3a5ea52140405675bea23884391008cd590a269847208168d04083c910e4101314b55bfa501c8405225da13e804391000bf53ea3a8845008067ceb415f290a0602aedcbeed2101404011d7266934c028040a39420ddc8805008046dd6ac8c880a02010da9d6a46421c88055a7e6368204390004b199102a48072080858a00f39090a0200aa223209a421c8005533d2e47ca439180aa46bd5a290472001645469252280e460207f7de099201402020fa76f092203908041b51d5229887208153171bfab090e4600a5d016f22601c82050b1b6220242280405156a04fa88850080522fcbd9d210a0002a42d1220250140405084abb7bc043910028c68e24e90450001615a5abe3090a0600a18d6488642140805423a8150402280003035a73fc48472080a), (69, 74, 7, 21, 7, 22, 0x3f684e9684112b080d2fb529e4244840c24027df7b677c5218b2b091f5bc907e1086aca0347cc5dd4be411030a016f0bc6d401046aca034ba23679a90210b08089e6dfc0808046aca031b8bd793c91218b29089e15c06cb94848c2c15784f7cd0a6110510816d8f4ac7184860cac0175f676e80021ab280c1d512498290448c2015b4d5bdeae5210b0b095d0f15af510462ca824b41fc64d4521ab2b0d1cce1d11000842c202072fdef65c421a32a051c6f752b494860ca405715b2ebf24112d100d6c48d478900840c280071217bb4a521a329055c0b2cbd60046aca030aff839c5c0210b0a081b84067a08844b44231ae0fb936e521ab2b0d5b766bb1d80440c2801ad5900a06011a532046b19b2ad30044944810ac5dd6f2c021ab2a0c1b06f688b904694c815ab334735e011832a006ab4ec1838084ac28316a4e1f9ee121030b005a758ea0d00868ca81069ad721ac0118b2a082a4e079b690848c2015686cc443a5212b090d5a08af0d89086aca0356758dacf40118d320829d5d72ff0046b4c830a753f9d9a5218b290959d3a5e76484634c222a72cda056411832a0169ac7aa5984848c2c116667dedd2411051001698481a2510842c282465ec08d04421230a05197560daa8044b44031a57689db60218b2a08592b892789844344225a45d817ea1212309045912e8ddf8486acac3163fb5b04102103080098fbe7c9b904634c825a39d953e6411230a0568b8e5d3594868cac1562d1dd6d6411251205689d7d36240462ca022a22b0f70c4110b0a09288aae74f104634c824a20072806411853201686ccebb184842c2c216191c0f12421030801584ed64640484ac243060da4ee0a411ab280d682a089b090683140a5a001d20986120c50892), (37, 72, 9, 19, 7, 22, 0xfeb2779a8404ac2431fbd40d678406acac31f5286e1c90048c2015eda5f3458404ac2c31e183e50a8404b44431d8338bff90042c2825d6eebfd99004ac2835c7bea3b69408114405c7a626bf80062ca821c64a06708408114401c22e3e6390048c2815c1d2034b14042c2c24b256ca138404344c21af71cbf79006aca835ac5e80ab10062ca824aa20354a1404ac2434a9968edc90042c2025a9485af99404344c25a645216d04048c2c10a57fc1dc9404344425a222ec5e94048c24159ec1e81c44041444029dd2eaf904042c2c209d4b5a8590040c28059cf0f2e914040c2c0497fa1aa704040c2c0097a2429b14060cac0492f79b1e940414440592a25e4d8404b44c319147179c94049444158dbe7dc498041442058b075cca94042c24258734c8610406acac3086c3c43d10068ca81483264577100614c8048308a455840634cc2181f137119406b4cc35), (69, 72, 7, 21, 9, 20, 0xfb2b62c39404303094f9900b571406323090f636f5004484101009f187c6d79044302096eeda18b38046322086ea947fd90406323080e67ad6a19404103014e3d02d091406b230d0e2a4cc3f8404b030c4dee70ef29886320895dbf504c48884b008c5d8f24a641044b000d2d8a97fee9084300095d51d0e911084102011d4491d3e8484301085d3b2e12d8404903044d29c0b1e4884300889d0a84d6b8404103004ce88db748404b010c4cc2b300a9484b010d5cbb129b84486321089ca347b631046322092c599b21a8886b208c5c436e3689884300895c2e97b4e1046b200d2bfe0518e8884300885be3f11291484b030d1bc93fd459044b020d6bc48c0cf1084902051ba5698218406b230c4b82d12ca8404901044b0e0c6991404303090a872ab649868240a96a836d3268888240885a8277578484632088aa66b24b79046122016a3ee5d798406123004a3bdf1529844900856a20ffc958486b230c5a140cc7b94049030549fd2a95f8044b020c69e3bbbd088449008469d4b7e7314841030119c294ef290280402149bf292191046b220d29a32fc4914849030519894a4db940612301498944fff0404903040979ef1b1048410300196d1f86f104490205295da2c099404b030d494a4aadc4886320889914cb6bd1044302092911733431084b020d190973f809844b008d68fe5dec29846b208d68f7baad218443008928f0f181590441020168dbc9ce89486b210d58a0084ea8084b000c588d5579c8428241284852dd556906824029684fe146e44861210098410c35d940692305483d71bb08044b000c683c953dc088430088181ee6c398046122006811053f49044300096801f92fc4084300089), (54, 76, 7, 21, 7, 22, 0xbfdbf0bee5018b2b09492e70c2c61018b2b0848776237b6501ab2b0d472c8e86665010b0b0946cd9f54020212b080c568e6221345018b2b09068d73a0cc1018b2b0806817342a65218b2b09567efcb3d84210b0809166dbf930650189230945f36b040e1010b0b0845d606d216501832b014599a5605e101832b00454b703dea521892109554a3fb23e501030b014541ac519e5012b0b0d4540ef6e08621090089151044de4252109010954f8619dba4110b080964f50fe28a41125100564db761eae501a9230d44cacfa916521030b0154c8656c2c501ab2b0d04c6b30a2e0110b0a0864c2d80c2e10189230844b6f9402a4212b080d54b62bdf411210b090894b06124964110b0a0964ae15ceba021ab280c54a71a74ee5018d3309449d83fb964018b2a0944912bb5a6101030b00448d5085084112d100d248cf3b8004212b080d148c9493fe4112b0a0d6482f3c326101090308447920ae6a0210b080854743b1806411892209646381666e4118b2a0964563e65060118b2a08644fc6fc1e1218b2b085441841000421090009143e6b095c501010301042df7b14e521832b0154254405d4101832b000423cd82be501a32b054420a0281e101230b04441ff2f572421892009541f53e2080212b080c141b3ce0e9121090108940c2e14d40212b0a0c140826f2d601109020864081b5f26501230b054403fbd7826112510856), (71, 78, 2, 27, 2, 21, 0x3e9226ff24540c405801f96f4472c21438484087df7f56134140c005821e933b46680543048600793eddbaa0140c021801e1540e248154314060077a7240224110c104801d9c35540c410320040874318e1d35040c805021cfbe93a4c254384060873a97d0034150c105821cab25d6c90103001400704ae98cb0450c521021c00a8d06d05430496086e52866c34450c505021aea05558c21038004086b6ad2a435000c804021ad471cbec25438486086b288867a1000c820001aca181e2d140310920869850fd125000c804001a10af3849144314120067a662db30100c000821997fce00d01030014086373c253b4410c52402188474c88911031014006121c8ff24400c40400183f6e2d4c0443040208607ef17da0500c4208017dbabf94804430402005f4cc1bc24140c0058017d294632825438486005d742d7eb4050c12502174b17542815431486005cc2f6f224410c5040016f152620825438406005b7fc27fa0540c4218016de827e0c00030000085b464b7130940e00182166c98f74d014304140859a8cd2330150c101821663d4748d044304120857b9044bb4110c1248215905b174d1403101208557876ce31000c80002152a0f174d144314120853af886e25040c8050014d8aa640c2143840408534f985e24000c0040014cca9c429144314920051ac2aa2b0110c1208214622bedec3543948608502f84c3b0550c52182139e8fc4cd00030010084d6ca99a30d40e4018212d05f576c00430480084b18799530500c40082126df4320d104314100849a8544fa4410c5240011de13a74c154314060846e5803c34400c4040211b0308dad154314960846ac329024500c40480119dbcda8904030012004632e67ba0100c02080116982626d00430490084478334434100c004821089731fcd0043041008420efd00b4450c525021082d3ffcc00430400084157acdba0110c120801), (42, 78, 2, 27, 2, 23, 0xf6fe2cccd15031056887af57b6f24540c415a01da9b1d04805030046007637d83230940e001a21d108fdead040300928871e440af34440c415221c5160f6a804430482806fff93a734140c015a21bce1349c940032050806eb99ad120540c411801b532958a914031092806b0ffaf334500c414a21aafd4a1a8254384868068670f2a24100c004a019a05b50891003101080654fc822b4450c5252217e50add8c00430400885ef3a87e34110c104a21732bca34d14031052085b30117520100c0108016c221008c214384048859bc600e35040c80522166ad3394d040300520859a072e524440c4150016395039c804030042805758900630110c100a21567980e4d00030050085564dc1ab0500c420a215415809cc14031042885336350b25040c8152014ae0f664914031052005269dca130100c010821497cbf9c8350390468050a1dcd530940e0118214182eac8d11431414884ba0febf34100c014a21277451ac81403104280494d5d2e24500c404a012335d79891043141080480bf2f530840e011021087fb7f89400320108040c9da3a30950e101a21), (40, 79, 2, 27, 2, 23, 0xff67accd680218248443f842e94c821038044807eccbd1e92820640a800fd5608bea0100c020a01f9fadbd24a0019028003f3d765eac00430480887e77500f122206202900fcae61d724040c015201f90419fe400018020403e90c8768c35439406887ba5e9bd180006000110f4b6ff2a25040c805201e84b860268881882a043bffd5dac84003204080777cc39d920a0600ad00eb27dd9230d40e401a21d5d97544680218208443a6458f9ad0143049488747681e59a000600a110e8af92b921040c811001cc68cb4c68081800a4439890889cc400320408872df05119a800640a110e597af3530d40e411821c61a9b6d6880188484438bdef56890003001080712f12ab180806000510e214536724000c014201c16493546a001900844369455278c14431402886ce9d4071a2206202910d14575e730940e011a21a17b6064680a1820a4433cc62ff490003005000672a75ad980006008110cd015b5324440c415201939e7c126200190200431a1d06aa84003208080623513eb92080600a500c1b425ab30100c010a21), (65, 80, 2, 27, 2, 23, 0xff07ae5ea5000c824201fe2b73b920440c411001fdbc720b20540c411a01f8b94b0d31040c811021f79b05d935040c815021f7448f8eb4000c024221f6623ffaa5040c825201f0f4a5b720940e011a01ef2c4c5924040c015001ee674af6a0050c121201ed7029f520040c011001ecaddbe934400c414021ea90a49e20950e101a01e9aa9e56b0850e121221e3a4f47634540c405a21e1c5a12634500c404a21e0390a9e34410c504221df69060e31040c801221dce88c76b0d50e521a21dcc8799520840e011001d60f496a34140c005a21cded0c6234510c504a21cc8e1ebd20500c410801cadbe756b0450c521221c94b6776a0550c521a01c8f193f6b0110c120a21c47f5c56a4040c025201beac417a20050c101201bba46ba130540c411821baf0e7e920000c010001b8996cf631000c800221b2e445e534040c015021b2ccea7334040c015221b21eb70524140c015801aed7f7c330840e011221ad9d0b9234400c404221aac75e9924540c415801a74c975634000c004221a461653f20140c011a01a2b9457a24510c504a01a25b3ab234100c004a21a1dccb0734400c414221a0caa26e30840e0012219fb88bd535000c8140219c9c395aa4000c0242019b37258d30140c01182198c2285124100c01480197b9a08735040c81522193f1d17220110c100a01931c6abaa0500c420a0191854fe721040c81120190452f56b1000c8202218f008d1e24040c0052018ecdc93f24500c414a018c91cc5630440c4012218ba0c22d30000c0100218ae8ea7ea4410c52420189cd4abaa0150c121a0187b5c0b134140c0158218380f8ba30500c400a21832e83f6a4400c42420181c6ade2a4110c124a01819f6a9930500c41082180da7d0524400c4140018091869d21000c810001), (85, 82, 2, 27, 2, 25, 0x3fdfa267824040c005101fb1366b60800430400407d3cd85b8b0c40e421121f45a1fee2830039080407985ec98834410c504121e3c25da628000300804078be4209834400c404121e1c44d8a2801030084407742d711920800e010101da0641622810431480407592fca5924440c415101d62ada064c0103004448755e10108a4440c425101d566f2fa2c1103108448750c046c820050c101101d1d9043a091103101440737276418a4010c124101bfe179d62821038084406fd6d582830410c500121bd48b0a22820038080406dc04c768a0c40e421101b1a316be0831439404406bd405e3830440c401121a563e9c648000300404068462568930000c010121a044cc06081043140040647a19778a0450c5211018ad74a524c110310444862488164820850e101101890e58520c3143940448623050a8830810e10012185e793ca090043041040601a431e830040c0011217ef00f8e0c30439400485c7e0b90820c10e500101719f75c22c30039080485c001671830850e1011216fcd8a660c10031000485bd1c2c6820450c501101695076262d00430490485a17e938824050c105101619fbe3e09114314144057a4a322834000c0041215b854c420c300390004856d34161834040c00512156cbf636480103004440556153b2830c40e4011215421a00e4d00030050485423c2b2930800e0101214ada293e0c014304044852b58a068a4450c5251014824c1524810031040404f7facb0830450c5011213d2e7eb24d10031050484f196fbb830840e0011213afe591a0900030010404d53e2b1924000c01410134b37c960c00430400484cc6e6048a0050c121101329dd7620910031010404c10f7fc830800e0001212e9d4e5a4811031044404a5bebe9834010c104121285941464d01030054484a13b4578a4410c5241012758bf424910031050404963065f824410c5041012543f8f229014304944048c038838a0440c42110122f056d628214384844047c3e4cb930840e0111211ca664464c100310404846dffa89930c40e4111211932c19a281003108040461cafff8a0810e120101162c41a62800430480404531e0e28b0400c4201210f2e1afa2d014304944843131766820810e1001010ba242aa0c000300004842a2a651834050c10512109c2e3224d1103105448423149018b4410c524121077f8672283143948440401df7dd8a0c10e520101), (95, 81, 2, 27, 2, 27, 0x7e052bf48c14031002a87ef456f64608218a80543f106e560a0450c561001f88098f95040870b0140f5f4daf80d04030112087a114722540aa18a43503ccc603b0a0100c060881e564e4115808860b0510f1265c982915031196007846d3ba2400018020103bd4b171120140c011881d7facb48500206010840eabd72880805430506007448272c148a0188c90039b675420a4440c465001ccdd16d11a0806022510e3bfbabcac10031180a87064ba06048081808a1037d80776230400c440221be1b1919122006222140dcbd4dacac30439580a86e1f34d224208190221036f91976230000c040221b7c1ecb0120006022000da636ea88c21038104886b9ff7f41402a182c30035ad845d2b4500c424aa1ac3b3718582206230850d1a0d32c8914031112a068bd8f1a1402a182431033a317192a0150c121a819b630088500a06010c40cd0d1d1449140310522066672f7a048221820910331b9ddd230000c0002a198cabad95228862b2540caf7359889000301108064946e04048881888a003204d073020550c5418818ff08679120006022140c62338fc2c010301842862e7008e048201808910315d4a3d230100c000aa187bf2fa9188206400950c3c27a78a9114315948061cb965414022182c1003081c5e3230050c1412a182bf0170182a06220c10bff574f82800030180005f9eaaf61402a182c3102f7c5191024050c105081759cabd95a0806032550ba5a02740d10031010285d1e96da548081804a502e74cac10a1040c82108172a10710180006020010b83faa94c941032054a05bb77d4c5600a182c2442d714135234410c5042a16799a1a8520206012840b1bd2804a801030084a058c107f25682218249542c4b94232a0950e161a816172b1f9582206230950aeadeac8280143058400574bbd0c048281808b002b8dc52f220010c1402815c6a7fe9122086282140acd52f1449000300502055e00f8a440aa18a03502ae5b86f0a0510c5608814b8ef6f1580a860b0d10a3ce6eac8c05030106a85120ba4454000180c040286daf26230150c141a21411475195028862b05409f9661840d04430412284fa376ce54008180c25027001e63030140c0418a1372e31185a08060324509b1dea4ca821038184a04c6f54ec44880188884025ebac6a0b4100c0648212b325c511a08860a251093b953a809040301120049772182240081802210249d2d16034040c0450211ee26dd91828062205508dfd716c8805430506a046f4ace60680a1828a142362e5fb2a0800e0602811a3717081880064000508b50e76cac21438584a843f24dfc060281808304205508a6024410c544001), (89, 82, 2, 27, 2, 27, 0x3fdbfcdf034140c0458a1fcc9fc882d14031192087eb9bc9b034100c0448a1fa0b91b48d00030010a87e3542bf024050c145081f656534c2805030186207d92131d0b4110c1248a1f1ff84ec2914431592207c7242eb034150c1458a1f1b502e8ad00430590887c6067da234040c045221f0e83c542d01430494287c2f7e9d130500c4108a1f06945d4c901030054a07bd62981234040c0052a1ef0c926c8904030112a07a2ed1730a0550c561881e76b70748910031010a079474059320040c011281e283de480d05430516087878af22020110c140801e03b5ca42c140310822877c13709324000c014281de789bf44904030052207760864f234100c044aa1dcab41388c01030104887706ea85224010c104281dbb7b41c8c14431502a876bf2be20a0100c060801d9144d888c1143150488760c46dd120100c010881d7bd838ca830039180a075b7133a230110c140a21d5e862a4ac04030082a8756bc1760b0d40e461821d2b240aca800430580a0745fd356024500c444801cee5a3044901030054207394bdba0b0050c161021ce4012c428110310842072aeb39d324440c415281c75a180c09044305122071c73c29024100c004881c6900378891443151280710b510a024010c144001c265f7388d004305108870139b96030510c540821bfb46a882c00030180086f9f460e2b0d40e461a21be0f279cac25438586a86f8215bd320d40e411a81bd15a1788d11431514886e4c6eab024010c144081b8cfdbc40d41032014286dd87702020450c541001b5080c8c0900030110206d08c577230040c0412a1b0aa74642815431486206ba3696e224410c544201ae0f14040901030014206a32b8fb034500c4448a1a8ae7fdc09144315122069f7714a224100c044a01a4e725fc2d0143059428690c26f52b4050c1252a1a36c431ca835039186a06824bf6d125040c8150819fdee6e48d14431412a867aea44a034140c0458219b209df809114315140066c49211321040c81128197eb7ad40c350390062865c4a85f0a0410c560081965eb9e80c044305020865212e6b0a0000c060081943479e42c154314862865014ab1124440c4150819340201cac00030180a8640d15fb234050c1452a18da37e24291503109620634e4cc7020110c1408818bfff94809014305140062d055c60b0150c161821899a921c8d01030114a862631181224050c10528182bfe09ca910031190a060590dd6034500c444821803999c8ac11431584886009b7be2a4100c064a01), (53, 82, 2, 27, 2, 26, 0x3f5c56eb134400c4140a1fb931eacad11431494a87ee06f2f320140c011a81f97de034ad00430490a87d1d0aa50a0000c020081f20425ec2840032080207bc53a81025040c805081edaec16ca815031086a07a9d636f024010c104081e873fdccc905030056a079a32a5d034010c1040a1e0657cd48d14031012a877990385024440c405081dce82dcc283503908620772b4551230550c501aa1da69eeecc815031046a07675fb8f334040c0152a1d9c8ece40c14031002287544f8d7030150c1018a1d5012ddcad10031090a87521d5692b1000c8202a1d2b67924091003101020745ab3d9030850e1010a1d1448cec49400320502073bf55f7324500c414a81caa040dc4d00030050287259db9d2a5000c824281c8e58304ac05430486a8710926af230950e101aa1c3d9bf5cc840032040a070b3c027034410c5040a1c1484f7c0d04030012287049cdf9124400c414081be34a0a4c804030042a06f7ee083320840e011281bde887cca914031092a06db56329034440c4050a1b5def16c4915031056206cd32d05224000c004281b11e34144840032040206bcb8f03024500c404881ad6709dc8c05430406a86953229f135040c8150a1a43c8a3cc814031042a0688696d9234540c405aa1a07cf3dca900430490a0677ff26b2a4400c4242819a1fd9fccd11031054a8662e7d870a4400c4240819095d7f48c00430400a862e374d9034500c4048a18aac9b1cc800030040a061d848450a4500c424881), (96, 83, 2, 27, 2, 26, 0xebbb304e4610a1c202543d49178cc29110310942079d9ef0c8122086282040f3aad19f120540c411881e27a34e2641281c023503c2e852cc09154314162078556fe38500806010440f08347eb034040c0050a1e03d646254a081904a503bd6c1f542d1003109028777107f28520006012040ee9f3d9b2b0050c1212a1dbf8fd624600a18202543b64660d44c0003004028761835728504a07010c40eb80e649030940e0018a1d6eac266068a81880b143acf07a74c811031044a0755337279500286090940e823b101230440c4012a1ce0b339e1602a182431439b8455fc8914431412a0734130778504207010840e6250e292a1000c820281cb707462648201802950395c9854c0c41032004287184c5518180086080050e28063d1330100c010aa1c492541a248281802b10388aed844cd05030056a870826aa39980006008150e00bf3e32a0110c120a81bfb67cba068a218a091437f2de00ca800030080a06fd1136e8580086090050df4272e12a4540c425a81bd86fe62560a0188415437896996cc910031050a06efc6b278180006000050ddca0623024450c505081babeff36548001804850372c64474ac11431484a86e1e946a85a2086292050dc2b609d230510c500aa1b80f0412568881884a5436e43ff942d15031096286d4889cc9186a07200d50da7e04f7224100c004a81b4de969e448881880a50368259d34cd14031052a86ca62af29520286092940d8223bd1020150c101881af113b82241081c0221035ca618144c35039046286b6974f29100886080540d648b6832a1040c821281ac811f76268881882a143548b963c2940032090206a4c42aa91a0806002550d45ce1db220150c101a81a74cc1ce56002182405434da1ec548914031012a06975ce738180286080850d2020563134500c4148a1a282267a4488a18a0a50343caefac8c04430402a868410b2f8528206412840d078696d325000c814281a049c3da46802182085433e2e0b9c4c0403004228679b75c291a8206402950cf1b37972b0550c521aa19bd87d92261081c02214336d687bc4c250380462866aed71489a020600a850ccc6ee65335040c8152a1993df81a262081902214331aca97c4c400320402865d2ffc68128006402040cb6cd139024540c40588196d28df2448081800a5032d43ee7c481103104420652aeb7785a2806212450c8ca9abf0b4010c1240a191719d12148221824910319ac06ac09144314122062f530399128006402140c40788bd134100c0148a1860e8a06548a218a495030970c98c28150310862060e4f0398120006002040c1587231034000c0040a181924dd26680018028543012ed07ca805030086a06018da838104a87080c40c021d6dd231000c8002a1), (11, 83, 2, 27, 2, 26, 0x1fd036ee40c11431404287f5f7f518588006410050fe85e727234400c4042a1fbc353aa461081c002543f222d384cd10031050a87d6468c28500286090840fa8c1267331040c8112a1f14467d21688a18a4a143de1d4f048d40032010a87b84bfed8504a87090c40f6dc4b27230940e001aa1), (93, 83, 2, 27, 2, 27, 0x7f93090b2a4410c564281fc55ba56048881888a103f58471e82914431592007e9d00bb0502a862b0c00fbdb49e7020010c140081f738790c0608a18a82043ec224a682c04430582087d82aa391502206230900fac8fad3034400c4440a1f3e8460e14002182c0103e6efbb68ac00430580887cce00ab0120206022800f8e7963f0a0540c461881efdcc5a456828180cb443de9991980d11431514087bcb461b1500206030900f6c0d267230100c040aa1e7e7435e448081808a503ce634a688c040301028879abb5d991a0006022150f2cf4497034440c4450a1e52456f60488a18a8a103c9dfbc5c0c140311022879090ca50122006222000f1fa128e0a4450c565001dec59f84048a218a89003ba3f4b6888254385068076f24fe70520206032800ecbdf59a2a4040c065201d7223afc16802182c8043ae300078a91503119680758ee3771582806230510eaedb6ef024540c445881d5ae74ec068a81888b043aa662538890143051480751664d10520a06032c00e9243393234400c4442a1d2382b5e448aa18a8b503a43925dca914031192a073e6061191a00860a2150e70c830a230440c441221cbd956860682218289143939e2fec09050301162071d0376d01a00860a2010e2a61277230850e1412a1c3ec0274468a81888b443875ca8580d104315100870b804c981a0206022850e14bc5a6034050c145021c1d5e2cc568aa18acb44381e2db282d05030196086ffe10f98502006230040df6ba59f2a4100c064a81bea770d64410a1c2825037ce071988c14431502886f21a75585a2a862b2c50ddb0f967034540c4458a1bac63c94060aa18a830436f327ae8a801430584806d562e6795a02860b2950da3ce75e0b0450c561021b46f8dc6048a018889103666577e80c01030104086cbbde7391048870a0540d79be7ee230540c441a21ae13dfa44680a1828a4435b9863788900430510806aa5f4c305a2a06232c10d13304f2230140c041a21a155ea0646088188825433fe8aee88d10031110886794686b0180806020410cf17dcb7034450c5450a19dc80bdc1680a182ca0433ac75f7c8914431512a0672730b385822862b0850cdeed572234440c445221962ecf9456820180c944327bc7a08280103018400646cf00f95020862b0140c8c17566024110c14480191686fd60408218a801032141e9982910431590006335c19911000860a0100c5bf8463224010c1442818a5f65f6448a81888b50313cd1e48ac0403018288621cb06505a0a860b2c10c401b95e030940e04182187aa860c54880188c84030de5e8dc291043159020614af7eb91202860a2940c0d8babe224500c444a01), (96, 84, 2, 27, 2, 27, 0xccde52b62b0950e161a21c9f93cbb0b4540c4658a1c8feadc30b0000c0600a1c8fb9fc70a0040c061081c8e51253030840e0410a1c6f951b72b0500c460aa1c6a49727034000c0440a1c68f38370b4040c0650a1c6539113030440c4410a1c60561ce2a0150c161a01c5ef560b2a0850e161281c5bb181b020510c540881c53307fe2b4110c164a21c357152b0a4010c164081c0798ee2234500c444a21c0593f9b0a0440c461081c02ac4120a4000c064001c02a05cb2a0150c161a81be971806034400c444021bdd29143030940e0418a1bd5d799b2b4410c5642a1baf3debb230110c140aa1bacc816e0a0440c461001ba5892b72b0410c5602a1b907912a034510c544821b874c002224110c144a01b721c5a7024410c544081b5ee291a030500c440821b5e06c472a0d00e460a81b56b664a0a4050c165001b50a029e0a0140c061801b339b0da220450c541201b2a51b2e034110c144821b19df49a2a4410c564201b143c8720a4550c565801b0d2706b0b0840e0610a1ad5a3cf20b0500c460821acf33afe030440c441021acd49857234150c145aa1aac9eaff0a0500c460881aaa9221a0b4110c164821aa06d862020550c541801a8c557de030850e141021a74323d7224140c045a81a5f5cb2f0b0540c4618a1a5a5ba5e030150c141821a4c90a27220810e140281a473ecea024150c145801a3fc64132b0050c1612a1a2e7b453224410c544281a083aea32a0000c060281a077d543234450c5452a1a005e19f2a4450c5652819fd127ba034550c5458219fa185df020150c1418819db965f3220550c541a819db29273034550c5458a19c47495e2a4110c164a019b7437fa2a0110c160a019b6795f6020050c1410019b162a2e2a0450c561201984a6f77034010c1440a1973a3ab22b4050c165221956723df2b4150c165aa19530b5de020950e141801940a1363234110c144aa193e2daa7030000c0400a1924f54520b0140c0618219201b1da224140c045a0190cb2bfb2a0910e160a8190024d0a0a4110c1648018fb41d0a034440c4450218d7e571a224450c5452018d269be62b4400c4642218c8580060a4010c1640018b353952024540c4458018b0265ef2b0040c0612a18ae7837b0b4500c4648a18a79cf93030100c0408a1897fd54f024400c444081893995fe220110c140a01891f0fd60a4100c064801889c0b6b234140c045aa1880ba556030840e041021878a873e0b0100c06082187531f8f2b4010c1642a186a3bd372b0c00e4602a1861209772a0110c160a8185ea5ef3220050c141281857e92432b4500c464aa1845fb7df230400c4402a1845c8f3b024550c5458818444fc722a0400c46020183e6c2ce0a4400c46400182494d932b4140c065aa180c9c7eb2a4540c465a81), (41, 84, 2, 27, 2, 27, 0xfea1bcb70b4410c5640a1fe2478872b0550c561aa1fb797ebb0b0500c4608a1f9c0a1bb030510c5408a1f97c72ee234550c545a21f9347c1b0b4150c1658a1f857754f030040c0410a1f66e93e6224440c445201f329d2b6230500c440a21f310ee5a2a4010c164201f2eb79e32a0900e060a81f18870e60a4150c165801f17e62fa030050c141021ee14e55e2a4550c565a01ee0688c2220050c141201ed0257172a0940e061a81eafc7a4b230000c0402a1e679a0c2230010c140221e4dc9426234000c044221e47023472a4040c065281e2521f5b2a0140c061a81e20ef6962a4000c064201e04aba730a0110c160881df993dd7024150c145881de46a45e2a0010c160201dbc8fceb030800e0400a1d957c016030010c140021d8f47ebb220110c140a81d86f79e7224450c545281d7d274de2b4150c165a21d6e2c682234150c145a21d427899a034000c044021d35143da2a0100c060a01d2a9808e2a4140c065a01d140240b224440c445281d09393f2220150c141a01cfe75f922b0400c460221cf36e5fa0b4450c565021cf0d3a4e2b4440c465221ce6215d3020950e141881ce1328222b0410c560221), (46, 80, 2, 27, 2, 22, 0xfcd9be76b0000c020021fc2a0e8aa4000c024001f92e147aa4140c025801f625999ab4100c024821f4dbcf5624010c104001f1c45ec0a0050c121001e9a9af5f20d40e411801dfa5a0a830510c500821df84dbba24150c105801de78ac1424550c505801dc18cf7834540c405821dbffa35230040c001021d7a71b2e34550c505821d751bbbca1040c821001d6dbf1a2b4540c425821c2c5a30aa4110c124801c19e8f0aa4440c425001bd5f5a9930040c011021bc84cd1ea0940e021801bb1a9c3ea4550c525801b6f94482b0510c520821b6afaf9c30440c401021b38cf816b0050c121021b369961eb4400c424021afeb157224450c505001af43e7f820450c501001aab4b53e30540c401821a4bde924a4450c525001a0e4254ca0d40e4218019fd6bfbb34540c4158219ef9972430050c1010219e17233730440c4110219d3cd026a0450c5210019d042148a0440c4210019c4da39430d50e50182197b350b630450c50102197a390d4b0150c121821969a6a7ab0500c42082192bf8b6c30140c0018219276e0b8b1000c82002192209708a4540c42580190eb848aa4500c4248018b280f98b4510c52482188ea236c20150c10180184ebd2ed20940e011801803967f234440c405021), (51, 81, 2, 27, 2, 23, 0x7ad2b7e4ac14431482887cb0d796448a81880b403e445bf96a4540c425a01f1a7a24f102286280900f588bcc2cc350390468878d85687548281804b403c18ff066a4150c125a01e0a63995180206000910ee07d18aac350390868875fefa86540a818843403acf0bea2b5000c824221d63934015a2806212510e9f148fb8c050300068873dd74fb66088188224439e019e06a1040c821201cb5062e5180a86080d10e573a7068c114314048872a98dcbe60a81882344394f7245624140c005a01c592a4cd522a86292d00e15f83d2cc41032044886ef8ce7bc402a182034036cec54ce30050c101221b45e70ab580a86090d10d8fa0ab4c801030044806c3769afc60aa18a034435c5b9326a4010c124201acdea4975a0a06012d10d3db4af98901430414806977fc29560aa18a4344348365c56a0d40e421a01a19b2cd9504a07010d00cfe4cb27a9040300928067041d49568a81884b44331f1927ea0140c021a0195f60751580006010110ca546a468c1503100688650d105dd68881884a443238463a2b4150c125a219143adf9580286090910c7933080cc0503004688636f646bc4822182094031b37fbaab4110c124a218879898f580806010510c42c3008c9100310508061881e0b44802182084030c1bf4c6b4550c525a21847e5b95122286282900c236e12cac254384868861129339548a218a49403025992caa4440c425201), (23, 83, 2, 27, 2, 25, 0x1e9908f1e2c01030084487cfa655cc5a2206212890f647e6dc920840e011101de49bb011600218240243a88b014a2c114314844871809464c586287290890e0841ab8924040c015101b82d93e3161021c2402436ced3c960d11431414486c8eea3ac580286090890d7d8d95d8a4400c424101ae79358d161081c0422435a7e3ec64831039044406adaf6554584287090890cf5a6bb28b4450c525121938f10e51600018040243256ff3ca483003904040644c596945a2006212090c4ddc6f18b0800e02012189a1bfdb148081804a20312dabd920d1103101448617104e94586087290090c1e96ff5930c00e410121), (96, 84, 2, 27, 2, 26, 0xf959d82b2b0140c021aa1f852d1f12b0540c421aa1f69ca4010b4100c0248a1ee050ddb0a4150c125881eb54a7772b4150c125aa1ea8e111b0b0540c4218a1ea4ce0c50b4150c1258a1e8e87c1f0b4140c0258a1e8af71412a4410c524281e88b46cb0a0450c521081e740580b234110c104aa1e42b1f59024150c105881e20d009d0a4450c525081e177c869234450c5052a1ddceefd70b0450c5210a1ddcafe952b0d50e521aa1da0804f5134540c4158a1d1cef0db130040c0110a1d180e8372a0440c421281d148292b030140c0018a1ce3146ff2b4100c024aa1cbbc410b0a4410c524081caca64f50a0110c120881ca6bcaa7034450c5050a1c8c02583334100c014aa1c7fc9b6f0b4550c5258a1c7bdffe92a4100c024a81c6b69efb2a0940e021a81c49a69e72a0500c420a81c3eefac1130140c0118a1c3d4d7f9330040c0112a1c27f1aa12a0d40e421a81c1a358b5030550c5018a1c01ff9332b4410c5242a1befeb7e3330840e0112a1beaf9737030840e0010a1bd5614f7130540c4118a1bd1bb9bd230d50e501aa1bbecc42b2a4110c124a81bb835adb0b0110c1208a1bb7ab0d30a4100c024881bb4ca4850a4550c525881bada6231030110c1008a1ba989a0d0a0500c420881b9c2819f0b0850e1210a1b920ca7f0b0100c0208a1b812bf172b0440c4212a1b6963f3d0b0000c0200a1b20087552b4140c025aa1aeedb225030540c4018a1ae47734f224540c405a81abfb29b1020450c501081aba9e85d0a4140c025881ab5a743f230540c401aa1a9c8f07f234050c1052a1a77cc84f120940e011881a5a3b8ff230040c0012a1a5931051120500c410881a51e30c7024140c005881a4b46157020550c501881a4979a9d220050c101281a3411491224110c104a81a1953a5b134140c0158a1a1223085034140c0058a1a00f99792a0100c020a819f80543b020110c1008819e54f743020050c1010819ae47b072b4540c425aa19acb04a5135000c8140a197cf5867330500c410aa1974761b7230450c5012a194c6fac92a0840e02128192fb7c090b0d40e4218a192982a090b0050c1210a19200b0a10a4510c52488191fe77b3220450c5012818febfd73225040c8052818fe1792b234140c005aa18f1dfa71324540c415a818ecb84850b0950e1218a18cd0995f035000c8040a18a2611132a4140c025a818989ff8f0a4050c12508189404ebd224140c005a8187da1769030950e1018a186c305b32b0000c0202a186457b39331000c8102a185f79e4b0b4510c5248a185e12ea1034050c1050a185c8c91b334540c415aa185c0e959234440c4052a1840f6d1d230140c001aa183d99c35030100c0008a180f2f6c70b4440c4250a180bd2c490a4010c124081809cabf90b0d50e5218a1), (6, 84, 2, 27, 2, 26, 0xfffc1cff335000c8142a1ff924ed32b4040c0252a1fca765430b4000c0240a1fc9894c5034550c5058a1fc8f56b52a0950e121a81fb63af65120d40e411881), (96, 85, 2, 27, 2, 27, 0xb4ee53b31502806230500da5fa7368a914031192806d18e55de56022182c1543684f018f230800e0402a1b283bd791500a06030d00d8e5cb43c8c31039104a86c1b49b6c548a218ac9403601f609e2b0140c061a21afbf53d18580a06030c50d7c6cc78ca915431596a06be09e286461a81c8835435e78616e2b0440c461221ae43991b9180a860a0d50d707abeb82c01030184086b5ca1cb454888188ca4035acbea570a4000c064081acd9d2ab81a28862a2450d61ac168c8c21038104a86b09d0f3e160a218ac1143582efb272a4010c164281ac0ee44581822862a0850d5a52d61ca815431586a06abfd521e561a21cac1543551e8dcb0a4400c464081aa6300450582a862b0c10d4d543cccad04430592a86a383c22c1412a1c2c30035096235f230910e140aa1a81523d381802860a0850d3e89d61cac21038184a869e99d6e60688218a881434e72e9cf234550c545aa1a4d2a0750186a07220c10d1fd3469c08114315042068f44a15c160a8188c304345e0797f2b4450c5652a1a178856d0502a06230c00d0547533c8d11031114a867d51417656888188ca5433d4dc4e20b0950e1618219dc8237785800860b0050cee28aa9ca801430584a0673e71b860608018880143394b7b7a0b4400c4640219c2b991d1186a872a0d10cdde5143c2d114315942866e67a7d61400a182c210335f3de8f0a4050c16508199b5318b9506207230940ccd65c49c0c2403810228665812bae54080188c0503314f35fb020050c14108198603c458182a06220c50cbc9f9bf82d110311940865c611c1e148a0188c91032bba415e0b0940e06182195b882f99520a06032d40ca6126c388c2543850688651798a8c56000180c044328ba20330b0950e1618a19438f7ab11a0a06022d10c97ec5c48ac150311868864bf53e8e141281c0c3103251277c60b4550c56582192794f5995800860b0150c93515facac20038180a86421b5e4416808180ca0431dc354be0b4510c5648218e03000391208860a2540c6ff6fbfc2c1003118028632137b1e161281c0c31431900a9ef0b0800e0600a18c74ce7911842870a0910c6281b5d88c014305048863011c7ee4408a18a8250317be5c53230900e040aa18b5e17811120206022900c5a98c9dc8d10431510a862cd3b86c448a81888b403155fbf1b030850e1410a188fe0a2905a20862b2010c4419ed280c254385060861f2d9d9e460a8188835430eae1e5f0b4110c1648a18740d0791182a862a0d10c35821be88d104315108860e4bdabc5480a182ca4030719c7e3230450c5412a1835088b30122a862a2c00c1554a48ca900030190a0609be43664408218a805030493ebd7030410c5400a18226d9958504807030440c104f555c28200381802060481b8161600a182c214300214b530b4010c1640a1), (73, 85, 2, 27, 2, 27, 0x1fffd7fc3234540c445aa1fefa3d2591840870a0150fe4717a4cad01030194a87eb2d7f0e1602a182c3143f1db6b33030150c1418a1f5e5bb179522206232940fada3613cac05030186a87d31625964482a1828b503e48655a32a4050c165281f0c6daef9104a870a0d40f6f8b334ca811431584a07b1ee02cc061aa1ca83043d60938db2b0150c161aa1eadfb3f11580206030910f56a1b4682825038186007a9bc0d4656880188c8543d4130f462a0540c461a01e9e203591584a07030d10f4b36ae0c2d11031194287954c1304161081c0c2043c8eebd7b2a4110c164a81e4742df11122a862a2d00f04b30b6ca814031182a0779edde461488a18aca103bae691c70b0910e1608a1dcf7b3f385a2006232050ee2a75c7c290443059220769e7bd4416088188c2043b4ae697f0a4440c465081d90ceebf1186a07220d10e9a53edcc8c15431506a874c1b92ae1408a18ac2103a5b752ff0a4550c565881d2c676838520a06032c40e8625836cac31039184a87417a054e16828180cb1439b20a9ef0b0100c0608a1cce02f4b91028862a0540e60b67eb82d000301900872f36e21c4482a1828b403968a2727230940e041aa1ca3f7d1795840870b0150e4cfc586c2c1043158028720d06cfe540a8188c35038cfb18ff230010c1402a1c53dcdd391a2806222550e287d1808a82543858680712ac751e5608a18ac254388656c5b0a4100c064881c2a058a181800860a0050e14c03548ad11431594887036be286148a8188cb10380697b230b0810e1600a1c0039fe91502a862b0d00dff33cf78ad14031192886fd1f113616022182c11437bad4c9b2b0100c060aa1bda613e985a0006032050de89e5f188d14431512886f1df8af6141081c0c2103779261ee2a0940e061a01bb10e58185a28862b2450dd79da13c8c34039102a86ea5f4ece060221828114374a756a3230c00e4402a1b9e438439500806030540dcb3aa16c2825438586206e1350604461281c08344370893d0a2a4150c165a01b69688758520206032840db21ad2ec2c15431586286d49c138c560aa18ac34436a0fea5b2b0510c560aa1), (47, 82, 2, 27, 2, 23, 0x3c904e8b8b0040c021021ea1ee3cfad41032094887a226c2c2b0140c021a21e87c02c1290143049400797c0486eb0040c021221e5d78a0d2c0503008608776cfc8eab1040c821221d63911682d41032094087567ebaa6b0540c421a21d1e48db52c410320840873a5ab2b624550c505a01cb3899f7ad144314928871a3cea14b0840e021021c61dd6ab2d010300940871836558824050c105001c559ae902c250380860870bd540b2b0840e021221be86f229ac25038086886f7287e50b0540c421821bb978fe08905430416806edc90c14b0440c421021a29133c42901030094006831c4a32b0440c4212219eac9b232d4003209008678b9270ab4040c0252219d51fc722905430496006538c47d8b4440c425021944183e7a911431494806501b68daa0450c521201938431da2d000300900864a83317aa4050c125201923447d42904030092006451eedf0b0100c020821902d1bac88154314068063a555f4ab4410c5242218e15d8d30801430404006373e0db8b4140c0258218d881d7a2940032090006356a97aea0440c4212018c5f533b2c35039086086298eeea730040c01122189aef8488d154314168861f4caa6e34150c105a2187733edf29410320940061d8b3170a4010c12400181f84d6429100310900060266d99f20440c411201), (49, 85, 2, 27, 2, 26, 0x1c78112a5234150c105aa1e28a4c269502286290940ef1ed1a6c0c3543940628772e0cf32660a818823543b5c04b0b330d40e411aa1da1c2d6f8580206010850eca76bf9ca911431494a0758f3c296468aa18a0b54381e67313030510c5008a1c023ce1a9580206010950dc65e2d8cac21038084a86dad848c6560a218a415436b88adfd2b0940e021aa1b5a8d94245a0206012890d84fa9234ac21438484a86bff16182161081c0421435d720db68b4000c024121acd5b6e28582206210850d5f29de742d40032090286a4861272448aa18a0b503481894290b1040c8210a1a35362428580a06010c50d0a1111dcac25438486a867ae496b2548881884a50338e4af5f2b0d40e421aa19b8da23595a8006412150cc8d7e984ad14431492a86633729564482a1820b50331000e6d0b0510c5208a1969ab8e29520a86092d40ca88c6cac0d0543041628650f407251608218a402432333c14d2b4550c525aa1910db53c9104a87080d40c8375565ca915431496a0640972d1a168081804a1431e5fcccd330940e011aa18a3f0c8f9982206208950c4900d01229000300904061f67af4206008180021430f1c7d19130440c4110a186b17c7b9588206410950c31f5df3c0c110310042861077f5f2560221824154306a242d70b0940e0218a182d8755b9980a06008d50c0ef5e7d4ad00030090a8603871ba256a081904a5430148ef570b5040c8250a1), (30, 87, 2, 27, 2, 27, 0x2590b54158186a872a0c50c713f2b472b0d40e461aa17dfe903ae568a8188cb542f3f81201c8c35439506a85dda71e519584a07030d50ba4ed7d9f2b4510c564aa16e518fd165618a1cac2542d1e98aebcac24038182a8592ca8a2515a28862b2510b221a37af030550c5418a1623964366161a81c8c3142b75ac9aecad15431596a856b05a5b195848870b0550ac3028a2f030950e1418a15569ba2564612a1c283542a82776f38ad104315908854ba72b239520a860b2d40a707bf1f72b4000c0642a14c27c22ae061a81c8831429500c6638881543150680528eddd0d9502206230940a409022cb2b0540c461aa14588703e6468a218a895428a624be98ac2103818488511d766f715a0206032910a2335bb630a4150c1658814448f3a66561a01c8c1542886d2638c2c240381822850f6f647d15a2a06232d10a0abdef2a2b4000c064221), (92, 76, 7, 22, 2, 26, 0xffa29e8906288628256fe3495c48420062080afd591bc006220620282fcfde3880a2a86282c5fc031b3108800640011fb6fefc40460872800af965f1540a220620289f7edd709060a06002d6f483610448020601089f026431906088608256ef82fb4806000600206eed3cf784a200621205ec3161b004800640002eb996f0906280620256eac1de880a220620285e56079990a220620295dc302de906000600216d6daf87986280620a56d54a26098a200620a15d2fa3dd486200620a0ad0efeb504a0a86092c1d0977a714a800641211cf91128906800640216cc19a5b84a2a86292c5c7c83bd808800640005be59e8d848800641005b71e02800a228628281b51e475004820640082b3781dc086000600a02aedb6f5804820640086a82965500a0a86082c1a73b8c810a208628211a191bb794a008609215a060042086820640a82a053b1444a0206012899fe33a304a2006212019ee178b88a280620a459dba3aa9062a86282d69bf830e80a088608245959023d806020600286943566510a0a86082d1936925088a020600a858fee70d086020600a828ee38778888006408058d699061088206400918cf322a84a0a06012c58af03d190622862829680eb3b680608060024680758be40a2286282897b3c3768060a86082c6791b8008060886082466c993da186820640a926b077e99060286082966988b701062a86282d25f0764194a0286092955dc18d344822062108957e3594904820640096575d95f98882064089555c8609886820640a8654a75c890600860821649b1b4288482064088648a91e784a22862928548a444680a0206002854784969808820640085453a5c610a2806202514414e979068206402963fd44181062806202523e02ca1186200620a123b310b244a2006212093aca84a84a00060120536fdde090608060025636145c408480064080235a07aa40400060000a335e9d640420062000a332baf488a220620a852727b9940a2086282092250a4c84a28062124521a3e33984800640816209108290a2086282151dd75f98048006400061d6063f18a080600a511bdaa1340a00860820919a931540822062008919460c40860a0600ac2147195c10a088608251144717690480064001613464ca88480064080611d585094a2a86292d505c2ca488a000600a0502e265f10a0a06002d102d0e92104800640012003554e14a020601291), (79, 77, 7, 22, 2, 27, 0x7ec7deb4428881888a47e7ea7f3294050c1652bf03530914a08860b251f73f02e824000301800f9eafa14420001808047cbe2016094150c16583e5d5ca390a200622215f24937a80310431510179080784418281808b4bc1ec787208510c540add42a08504a00860b201e7bbfb28a5004305908f381e3f452020180c1479221e2a208010c14025c2c1b49908280622055da317a2c8415431506aec8dc47e418281808b5b56e756a00c550c54585a840d0f90620862a216d3f1eb0ca415031186ae8be51bc42022182814735e75eb090500c4608b99181d9104020602092c920370805010301140e2ef984652020180c156ff2ed9b210100c040ab794f90314a20862b211baed77a8831043151095c69b73e420081808256e1a890b094100c0648b601273d948600723015aba1f3bc8505430516ad59e993e42802182885690f4df3210140c041ab436205d00a2a862a2c19df5beb8030443051214ad4ce46411081c0825a3b13072094410c564031d80b8b948280623055841ffb6c04010301042c1d869e6520a218ac15605dac6600c100c04484f15206f10a08860a251748707cc25014305942b910483c4282a1828b45abe7683208940e041acd301a9f80402860a08665ca742c24210381842b164c7de12020180c11581b7cdb00c010c1440cbf2e1f580620862a2065e6ad5cca400430580aae74e61c0182a1828b095ce1fbb090510c5608aa3820dd8060006022064b5b05ac8300030110b232003861208218ac015124a9e3014540c4458a7bf184d10a0a06022d13cb42d58820443050291c3b7984418081808a48d1c01f2294450c5652268248a190a000602215337d458ca511431594a9995474c12828180cb04938a563290910e160aa47f651b90a0806022551e5f7f58030103011410da9b5de018081808a186d1d6c6094540c4658228601439040a860a0d608332b2883140311129037b755e0202818083141983a27290000c0602a0c68fbb90600860a216060424ec8414431502a82c0318e411201c081580a48582014140c045820447b3984800860b005), (75, 75, 7, 22, 2, 23, 0x1fbeed26428881880a47e6b248d05144314120fc32fd018a220620a91f4d3b19094100c02483dfe8152c1a00190084baa73d7a25014304940f403919c8a220620a81e3e399c20c140c005a5b24f27a0282218209076307cf125140310920eb46d1f188800640811d58df92f0c540c415a5a6ba7f9528aa18a4b474d2bcc485150310168e97b61cb86000600a12d17257ec94010c124039837cf3d28a01884947296e59c03154314161639a5f1b4a0a86092d1c6a2f7740d040c80505873288561a00190284aff01a41c5050300568dc6815470a800640211b07caee80c040c005055d2d7ec5288a18a4a46b018f9aa4400320808d3d6c5a286800640a02a7ad243894440c425034164f92c1880188084a7acd0b445150310560ceae532c0a0086082019cd553cb14500c414a32f1cd65e2208190224654ffead05110310140ca2115a44a8006412018e4760bc94000c024030b3021fc288018808460b2a3ff85114314148c0a3c8600a20062020180df07b70c500c414a50172603128081804a0601389f3030443041213f79267886200620a027e4a15ff15000c81422f063154218201802909db80bf4c5010300548bb39fa854a288629251751ec1aa0c540c405a4e55781e212081902209a57d4a8c24003204093470e6694a20062121168d873b514500c41482cf182bec182a1820b499d4c552a5000300908b2c803cb0a2a86282d164d2813094110c12482c3c680c618081802a4967d8a3da5110310948acafadb38a200620a11567a845614510c504a2ac1a89362a081902a45526e085a5104314908a9b5cf9b4a088609251522bf27c91000c82002a1201c7618201802949403d34e25104314900a728faa2062006202024daba7ca09040c801249adffcd42a081900a452b93b93c5000300508a4e7a21d06088608252464d951414410c5040289eff1e018281800b0910fdbc0831443141292159b2f406800640202), (32, 77, 7, 22, 2, 25, 0xfd933a0e0221038004579f90cc3221001c02027c4d0ab8810450c50113d0522d340462072008ae19d8c8224300390804f0a32b4521088188222b437c913908800e010158edec0044a220621289c69c1e3224014304844e1b3facf218881882a2ae2923f2894450c525134162f22c0860072000998dcec36022043840054680014b2208018820262131e1a810010c100130c337e740620862820a815ef28a24000300804bb2ac297028801880825d27d4b080c400c40414e28d49bc084207000896e2a78f20230039000536b55805211801c82029ac6dde1908040c01114baea22040600060020a59bf459e25000300904aab5cfb7011001c000292d4f979810410c500128dcb06840820062000945b7053e4200030040522403d590100218200291137f66890400c420128890fc1c0420862800a), (70, 78, 7, 22, 2, 27, 0xffb720de521281c0c357f9602b19480a860b0d5fd31e42e4200a1828257debcbb900a08860a241f724cf02228281802b17d0c5b73848000603005f28720a4520a0188c147bbf89d5908200622015eee313fe52820180c957b4b148184802860b085eb301d920280a1820a17a8006ba90a228628295e838937e420a81888357a0d5f7194a2a06232d5e6e19b964208a18a825797b0ba194a220623295e4ef4ae40288018888078816f7304a000603201e1abca52428a01880957840917694a208629215dc87e74e1288218ac817641a49e80a228628285d8cc2f4c128a0188c9076062f53948420703095d6a45cdc428081808a474d5b4c594a08860b255d1dc7cca4282018009574117a4a84a208629205d026bebc028a218a89073f3debd94840870b015cd40cd4c5280a182ca472287bbd8480a860b0c5c7d94466020aa18a83171abb49b94842870b095c5c28f6e028881888a17114ca17948620723095c333b4b652080188c05709d921090a200620215c2438a6222a081902a1707847e490a2a86282d5c0bee12c12020180c10701f5efa94a280621255be09f03e020881888216f19195510a000602211bc1f5082428001800856c811ed38480a06030c5ac58e07612808180ca16ad785b91080a860a0d1aace821c52800180c846a64133b9080a860a0d5a4abcac2128881884a1691a628d848200623005a1c9cd66020a81888316867b4fd04a02860b281a071d75e0208018880167ece82d8482a06230c59f28cb060288018888167c2723184a00860b2059cd11dbe521a01c8c15671de8b700a2806222419a7f1a56028a01888916608410b10a02860a29193f17e7a1282218249164b66d4310a200622211902006925288a18a4a563dcbdb584a22862b2858f3517b4028a81888b061b4e3fa9088206400958656d01e428a018889561663c8e94a088609255), (41, 77, 8, 21, 2, 27, 0x1ef9c5e3883154315169f2f7b17a61a00190285f966711d20c040c0052fc071b38906208628217ddf58ae403100310103eeda3a56010aa18a831f726e39d00c510c5048f9a24edf9042a06220d7bfa3525883150311169dd4d380e0102a182831ee47b0bb00c440c4450f3debf1f0060a06022c39dd7068883114315149cdf479fe01022182811e0dd680b20c510c544af024f7f28060a06002c78077a534c341032054bbde2df2e418081808a5de45993200c400c44406ee1611a8062206202877660137443100310503b849636221a00190281da8f4081309040c8112ed4108171060a860a2d3677dd71403400320103a0ed1e9e018a81888b1cf8b3c3d30c000c0142e7c1631a9060a86082d73552eb64031543141639a5430ac41028180834c91797c900d040c8050e42739528062806202471db70e3c030543051638e3a8a1e4188a18a8a5c666d5e320c150c145ae32cb8f8806208628207114ba4a88200030100985d295d261880188285c2af9d3510c040c0150e14999b2886000600a0704c0f62882014305049), (96, 79, 7, 22, 2, 27, 0xffae27ee290400c46023fb7cbb5a028801880817f61160cc25100311902fc74ea9310800860a011f5f0e5d7010450c5410be75e3b96020221828117ce0d56248505030016af984d1ab848020603085f0f9c3fe294140c065a3e194d4de520aa18ac357bcfa5704a505430496af48aff4b90820862a015e82aac05311000c8102bcddeaeda2282018029179a1e66ec8505030116af23f4dcf94820862b015e3676261094010c1240bc4f47a5a528a218a4957899d43348515031016af12d5baf14a220623291e1e7eb9f214110c144abc2456376120aa18ac317846cd2d824050301860efd567fd84a2a862b2c5df284b69114400c4140bbd9d62a642022182815773361b2884010301048ee4ed46380a0a06022c5d90f2861214050c1052bb1cfdbbc4288218a88476355ca1c8515031116aebc9c8ab90a28862a255d6c16e7a294500c464a3acea98ce4200018080575857714c8510431510ae8a29c61848220623085d0c8bb3f094500c4648b99f802765282a182cb572eaf4c4c8400430500ae4da9b4698a220620a95c76f9bf2014050c145038a64032a428081800a570ee83c5ca420038180ae188977484a288629245c277f16d014150c1058b80623e02528801884856f4e08aec8425038106ade7d4f8700a220622281ba28eb7d014140c0058b6d99c004128a218ac906d57c292c25044305922da6f99d080a800640205b250bf75095000c8240b62e87c1a228a81882b16c59f899805114315140d6c11a1d90a02860a295abc5cb9d091040c8210b539950e2422001900056a6bcaef425150310962d41096ff108080602051a364c8df210840e0412b4687d8aa22a0019028168cfadb5405410320142d09351a114a0a860b2d19fa5c0f6094400c464033ecced7a0280218208167701bdb805054305160cebe5f8080a2a06202c59d6983d6294540c465a3344a215e52828180cb5665e420e405140310122cc42922d80a02060228597c72d9d094100c0248b2dc337c4428021828846590e71b4a511031094acb0e68639480a06030d595aefdaf010500c4408b2b58472e5200a182c2565535c67c25150311962ca89be5504a2a862b2c193cc2ab1094150c1258b26cb50e64208818882563f37262c24044305822c7e4019910a2a06222d18e28c449214510c504ab1bc120a452880188c846355d274825040301920c56cbf8284a02060128589d8d6f2294550c565a311722f5e12800180c81621bcb67c8501030114ac3c16f9910802860a09186fc95ae214500c444a30b6816fa1280a1824a160b442d1825044305920c0396ec2948800641015), (45, 78, 8, 21, 2, 27, 0x3dfa013fc02050301063f5f647f100c540c4058fbe1a19b403114314143ef57861510c100c0148fb2c5cf94c305030056bec6abd6b20c400c4442fab7a500803150311161eada211f20c540c445af9d1b220c02114315043e741f65600c010c14407745b3ecc8205030106bdc907d7b008010c1400f6a252e548310031010bd794625b208910e140af495842748315031016bd1e923c110c140c0158f474e6ddc8215431506bd01b887300c110c1448f3273657c8311031114bc8a3cfa620c510c544a703195d2c8201430504bbd4ba90620c050c14526ef37d99883000301109bbb58e7720c500c444aeeae3ef8883044305129b605707900c050c1050ec3e5265c03154315163ac47e7b300c140c0458ea8db50f882054305069a17d9c6e20c400c44426786ddc0c021443150239dff1c8200c000c0440676b4e00c8301430514b9993cf6f208800e0402e5c601b9c031003111039534bd5700c050c1450e532e0e98820403010299427d03d00c010c1040e3fc3da18031403111218ecfd77220c100c044a638bc38c4c304030052b8c371c7220c010c144260f96d2fc8220438500b828a09a3208500c440ae0859e39803110311141), (61, 75, 9, 20, 2, 26, 0x7e7f98bd10080188402fadf04c4a100430490bedbc30144222862928bd3f177d284410c5242f96d634a4082a1820b5f0654fd441110310543dd81556980800640817b4add86880040c021172db59891088218a482de81ee3220110310845b729eb544042070108b5ec6109304000c0142eaa6709a0082a1820b1d289aa7a203003908059b81527982800640a170acfb9b104400c4140dfcc10ce10200190401bc3f53144105030056375ec291902088608256e275e5b104500c4148d968cb9a50a081904a5a9fd91240141032014352ce69f48020062080a9225431304440c4152d14caf2a00822182091a1c05ffc404003204033d253e684222062128663615a1304140c015aca9f6832408881880a5944d53848101030014b1b45cbf8420086092061c3beb3284110c124ac1f01926508081804a580c16ef441400320502febcd2f902820640295f6c06dc880050c12113c4ff96e608081802a5756395ac21144314922e71fb95982200620a15cd37d81281040c8212b179da751008a18a42262401cf220004304804a6b69e3440000601009431c479281000c8202a56ad88a408021820854a6c70c48110431410a924da17802220620285086cc94804400c40411fe09c2e008081800a13967eef4a115431496a6f99d72842088609244de8347d104000c01409bb26299108081804a232c07e9220104314804593fa78942288629254a06dbf3204510c504a8a5698e21020819042113ff416cc141032054a2771a309020286082944d410b3084410c524086f7a44a108081804a1), (56, 76, 9, 20, 2, 27, 0xfed6e50e0000a182821fe88e0d61002a182c31fcf5dabe4008218a805fabe07d6501801c8c05fa2b227600022182811f92b6e3600880188881f4ff219e10022182c11ef24010e40820180895ee84fb7e4088218a885ee0414f640800180885ed5b9e2e000a218a811dfb5a46e10822182c91dde01cb6008281808b1d75d3ae6408a81888b5ca72f796501221c2c15c86603d6508a8188cb5c654bb2640802182885c646654e5080a182ca5c47e1d5e4000a182825c1b4ea464082a1828b5b322ab8e50002182c05a1de1c6e508a218ac959d0223e6401021c2805919a8b3e501281c0c358e67050e508aa18acb58de6a99e400aa18a8358de38396100a218ac117fa52fc6101201c0c117f9ec806101001c0c017ad36cd650822182c957882febe5082a182cb577b6bfce008a218a891732bfb6e50080188c056c01fd6e100a0188c1167241e6e508a0188c95669733a64012a1c28355c559eb650028180c3559fb4e1610020180c1156ccc806501a01c8c1555d7b29e50000180c054fc84b26108a218ac914b81c38e10000180c014641732610080188c0143c229d6501001c0c053f83ff8e50828180cb53ee679560000218280131e00d7650022182c1529cc4bf60002a182831285ee29e501021c2c0523630ac61082a182cb11715c62e000aa18a8311545128e5002a182c3512788a76500a218ac15077324c6008a81888b105085c5e50820180c95023b9926408a218a895), (70, 77, 9, 20, 2, 27, 0x3f6f89f7c8021438504be977fcae1000a182c21f0a13e87004150c1458f31d2c529420806012579475c3eca101030194bca2f163e00802182881e3cafe45204500c404af0dbc43c8420a86092c781443dcc8005430506bc00861221080a1824a1dd1da338884050c12516de9cf5f94028062305768f0fb148105030016bafc7968a0080a1820a1d116a9bb204040c0452e7441a868022a06202c7349cea544101030054397774e9e50008180c25c99596ad084500c4248e485242584000860b007206e138c21154315963898e5d365000a182c25c41d8c59301040c8112e1fc206690200060021704fc77eca021038184b8279c5be0008218a801c13cbc63280100c060adfab6c5e482200620a0afb969764a114031092b7c04dfce50888188ca5bd9288a8900800e01015e1705fa48022062088aef641754a105430496b756e6aa2408aa18a0b5b914eb60804010c10415b76a06a44200860920ad8a3f8fc210403019236b1fc55a108aa18a4b1b556e45c884440c425159b0aaac902080600256cd52d54c8114031112b65d2c7d220820180291b2350365304100c014ad85467a7902220622296c05777ac210503019635cdd4341101881c8422ad6e6ff3000450c5410d5a382c7802020602286ad18f35c8105030116b536775ca50a00190485a895d84f084010c1640d21eb7149022a06202d68b055514a111031094b44d8263e500a8188c359e807911204400c4042cd9e728190000860a0165daaa3944115031056329a0180e008a0188891901efc3b200450c5412c6de90ad84202860b28635829092000043040051929f29e408801888858bf00291105040c8150c5504ec28428206412862176b68c8104430512b0a00440600822182891822e1ab3284010c1642c093001194042870b09602a68f6c011103111430030009a608a81882b5), (56, 71, 11, 18, 2, 23, 0xfeb2ca7a84100c024bea83f66108a0188493c5e3edba100430490f82f311382020600a9efa3858a04010c1043d90a17f0080a1820a380dc12921054304966d75f36f0220862821d53d41f104500c41498cad3f860208190226df015dbc111031054d9592ee10202060029affca44b04000c01435ba1239108881884a2b5ee0eaa041032084d3d73594022a06202c9f9c9ae284110c124b3d76f44e02001902065f93f6001054304164ad4c413420a06012d95516c0a84540c425b0b3480410200190401f8471a8c105030056bef519d842228629287c069f9e81000c8202e163f23608a81882b59cd3aff8115031016b3064b8142800641215f9af93604510c504ab4216c95082a1824b53ffac5f8110031010a7d01c21020a06002d4ec7d9be84040c02528e880801088218a4810e07f1721014304942135ff7b42820641293d478db084010c12407432e95408a0188094dcca71a41150310561a94a3eb82280620a530e38fde04150c105a5c7440c5088218a484958d1fcc10403005291c93925422806212522d435d684550c525a3f12913608801882847c82178a1110310948eeb2665020886082513d17e0b05040c8152180855660a00190284229d5c5011543141602ee82c7022a86282d04fd1c7e05040c8052085eec9908221824900f66ed7814003201080299ad74228862925), (69, 75, 11, 18, 2, 27, 0x7f2772cd10008860a05fd93fd1e284110c164bd49f815c4088a18a8a79ff87268210003019071c7d48300202860a28dea7b112080140c0619ac72434450888188ca754ddc9388005430506ea577e6314008060305d27d2ce2284410c5643a4a0a22410822182c9323fc23e801004305105fee9ca114228862b25b972eefa084450c56516af17db4408aa18a8b6d573e5782114431592570bb18504228062324a1b35752204050c145327b9008450002182c0630b886d88104430512c3ed5ccb04220862b2082ff03ea080100c0608ff3470ec0088218a881f62ae7c8a101430594bc376e331400006030175e5e812284140c065ae3f38adc50028180c35a487d018011543151632c75f550422006232060827a9e084010c1640baf0d7fc008a218a891736c9b988104030112ad9f9f6710000860a015a3dbcf6204010c1442b3d51934508a8188cb565337f7821054305962c9d633114200860b2152d9c942004150c1458a298a454500a8188c3527eb5178011003111024524faf0420a06032c427fa752204400c44427aebf90c008a81888b0f4c6b4e801140311121e4185dd10002860a09397cf2fa204410c54426715b86c1080a182ca0cba2bbc88100030110988908f3042080603242fe1bdba280400c46025b8f9794408a218a894afdb38180101030114156add4d0422a862b2c29213aca204150c145a5146009450800180c849b2cb8680105030116130cb7a310222062229212778da204040c045241cbc0ac50022182c147193d0d881140311128be8423d00222062228161f0a5e284550c565a2477a354108a8188cb0278e03e8a00543058683f2c32b1022a06222d03e04136204140c045a073a4c2450880188c8408ed7ab8010443051200dbb9771420a860b2d), (67, 78, 7, 22, 2, 25, 0x3ffb733d408428708089f6f159de0180a1820a0bd660da2c8a220620a89f56f6b290108a18a022bce6a25894a2a06212d1f0546f00018a0188090bbe69b9c906020600292e56192d8028aa18a0b078c4c1a7488220620889d804548c218a81882b0b5dc3882806288628242d6cb9e13021021c20027410a1df106220620292cc9b40744280a1820a472938d4bc48620721089ca493181211081c0222b20eee5d906008608212c77a7fb0528281804b471cf044c106208628212c6276e8f0200a1820227163724e408608728009c454ded1221081c02227113bf7cc0600860820ac060e16d121081c04226ffa5c06c8462072088abd3610f8618881882a4aeb6e54e40442870808ab7f943ae218a0188290adb25e2cc0402860808ab268d6b641820180094abecd35614a820641291af2551471280a1824a26b2849c6c0422062008aaa53dd265220819042469c94f8a006228628282a6c3de62128281804b0698d86ccc86000600a0aa4eb871212a081904a068eb61a4984820640892a17e33671200218240267dd3eb5886220620a829e8d235042800180084675d96870060a86082c29c52455001802182080a6a73b8390a00860821199acd641018881880a2a600ab7000a28062024196e99c9d1208218a40265b1aa1d80a028608281938ba79e1288a18a4a064dd927fc482286290899166b262528201804946415119088a200620a018f37bd020188218a080a3c4a602c4a2086292098e20b2a6428081800a463522b8c4086207200898c4e9140128a218a49062bc974a44a0086092098a2a13e65280a1824a4627584ca9860a0600ad28788190d01008180022a1a7e97310682064029286013bd6128aa18a4b060bc82f214a00860921181ab37e812208190420600e227098a2a0620ad1), (84, 80, 7, 22, 2, 27, 0xff59c26d80a22862a285fbf6c9e380a20862a205f47724e59484a870b0d5f412b74a94a0a06012d5f2bec13d90842870a095ec96485298a280620a55ea598e3b908480702055e8cad49904a220623281e8bb24059486a07230d5e6c9f74384a0a860b2c5e178526d94a28862b255e1481e5098a080600a55df350f639084a870a0d5ddc1f60180820862a005ddac02c984a0a06032c5d85fef6494a020601295d745c471048020603081d67174f880a208628205d4e684de98a820640a95d360c2bb94a200623215d28bdfbd90a2a862a2d5d05fb4b114808860b051cc6c8d1780800860a005cbed087110a080602251c67f422194822862b095c3877a9d80a0a860a2c5c1ffd72f1482a06230d1c0cd68a994a000603215bf63850594a20862b215bf13afc794a2a862b2d5bea8999514a020603291bd31f2e698a0a0600ad5bc990da71080a06020d1bba6dadd948020603095baff8c18948820641095ba5ada75908400702015b6eec30b14a080603251b609f69b80a02860a285b56f1dc1948480703055b2ab0c9494a2a06212d5b276ae0484a820641285b149221898a020600a95af3e93af848480703045ae7bc0af10a2a862a2d1acd8f1ca98a000600a15ac674d4490a088608255aaab0f1980a00860a205a848779910a28862a251a7395283948220623095a66a2f4e90a800640215a48e71ef14a28862b251a42f5b7f94808860b055a342156f1480a860b0d1a1e14a0b8080a860a0c59ba2d97180802860a0859a447db290a0a86082d59a0419dc94a800641215990f404f94a00860b21596cf7e3180a28862a245956418f594a2806232559313c3ab84a220623285920006398484007030059047591784a28862b2458e7255cb94a0206032958cef2c9704a020603281895a5dc780828862a045893b13ab80a2a862a2c5890da91990a220622295885a5eb384822862b08587d4f29d8484a07030c58764419590848870a055869d3e2f14800860b01186904f3910a22862a29186441e5700a00860a201860bc2e890a820640295857b3d3e90a0086082158570c59c88882064088584804925148000603011846c412f80a08860a2458367f5e304a22862b2818337fd1100a20862a2018173e13c94a0806012558094f5e294a00060121580433e3914802860b091), (33, 79, 8, 21, 2, 27, 0x78ecd0fe4c315031056beae83b6b804220622087c879619f208450c5412f39cf5b1e41080188805dcc4636ac8210431500bb5e1d6b980628062224768266a3f208010c1402ecc82d126418aa18a8b5d49e7503c8204030102ba3dbc5fb80628862a247449e95ef208040c0412e87abb132218a0188291d09856cd803114315141a0e578759060806022573f65192f20c110c144ae7affa816010a8188831ce3e3775c021403110239c60948d904000602017309b531930c040c0152e5bbd4ce2218881882a1ca8a5b90c020403010239283ed998040206020872312f2bb008400c4400e42dcc962418881880a5c7f5f884c8221438504b8a7db59590408860a05712d4241a00c510c54486238223ce01000180801c39bf60cc031143151438485b067806080602247083c0a4220c440c445260f9e420e0108218a801c12837d4803014305141), (32, 75, 10, 19, 2, 25, 0xffdb7bc24080a1820a5d4047c742110031090345e64e3c4040870900e6eed0ea900c40e4111caa1aed5208881882a3907c782601110310146f85d798142028609295ed4d0c7284450c5252bbf8150610820180491703b4a2200204384006d5a827640002860808da47923d880c50e5211b45189ad1010a1c242367a5f42e40210380446b693e65c8060072080d642d02b085000c8240abae4b2c10a081904a14f2d68ca001043140068f2cd31c0060872800d15b400c880800e02019f36eafe108a218a4913b23789a2110031090676284a3142200621214dc3f56c084140c02589b174f19101821ca403341559fe2100030090663c64c60422a86292c4aa116c9204440c40528c6471f2108081804a112c500760110431410605388128422a06212c4022b65b081040c8210), (68, 78, 9, 20, 2, 27, 0xf27c3a3794220862b217acdff69e501881c8c25e4209c4584022862b0877bc8193610888188ca1dcd49669140020603093732b09b65088a18aca5d9b0a8959402206230974a888f720088a18a0a1ca5acfff9404807030571a6cafde40022182815c635861194020862b01706d1bc5e108a8188cb1c19f53528420a06012c6fdc49db610008180c21bdb3628b842020603286eb07a37e10880188c81b87d89ec942228629296e10c68340088a18a8a0b67068f7840420703086caec12661088218ac81b245c209942200623216bfff59664088a18a8a5af7451b89420a06012d6b85b0cae10088188c21acb96888842200621206b0c7f88c10008180c20aa97b0179404a870b0d6a8b7a80210a00190481a9fa9e5f9022a862a2d69ebcd2e60080a1828a1a7032cff8402a862b0c69bbe29be1088a18aca1a6af4eb580220862a20694177fbc50808180ca4a50303fc8422a06212c68d4e037c5088a18aca4a29bea5c8020a06002c6894cf27610800180c81a1100aad14028062305281868112108201804919bd7f2471422806232526b06697a008aa18a0b199db68e70422206232826422449c10000180c0095b4ee90982280620a5656a35776500aa18ac3592b7d1510420206032823fb4a07a508801884858f20cccf8400a06030c63a9137ac5000a182c248e257ffd8402a06230c637f5c9ea202081902218ce770f58022a862a2c628edafd6401221c28158a17248690222862829623a0509a5080a1824a588bbebce8422286292861d0d524a508a81884b586adb80b84020862b006185eecf6400a218a81584d144bd8404a07030c60a7746ba1080018048182975c798422806232460732b1ce50800180c8581c6483114208060325203b8b2e240a0019008580987df49420006012160033459e4080a1828a5), (48, 82, 7, 22, 2, 27, 0xa1f50cb310180a1820a2a029ccec4448628729089778efdb81228081802a25c648d3be482020600a88712b92ff1218081802a29c0c5576a40602060028a6e062b0d1121021c240259d60879b94022862b09465a929629121001c04025771aed924484287090895da52f5d90080a1820a216d545d521062286282925831ea6c64108818882595d506bce448608729009571bb76e04088a18a0a4150391c5010602860829253dbd41c90218a1ca022547dbec9648a000600a0951019cc380088a18a0a0142fe664314802060309150bae702452088188c2453b7659784022286282884eaa1ae090188a18a0a293a4d68fd1480a06030d14b18050f10280a1820a252a115fac4006287280884a230c32c50088188c2412830923390840870a01549f50b7da52a081904a5522d540299406a07230d447972ce3a028a218a09151d01c308482000600a08471e5cd690118a1ca02291c43b5e448a200620a0946a3913c9221881c8222519236f58488600720809462b25d390010a1c202210e7c5a8f80222862a28442dd4f46e4112a1c283590aec857b90a22862a29542b5b6150128a81884b0509c6aa1098a2a0620ad541f060eb8018a81880b0904d1400a4002286280884129a98c8028a81880b05029c75d898a800640a15401ad549a218a81882b1900312d56986220620a96)],
  [(36, 63, 2, 20, 3, 22, 0xd23420910022800da2cc310200450012d4556290008890257f4489200281208aa241920007204114fa3900040a80002961392400088003c6588082002810088c04190400722010fb73e12200a10019f6a5821001408023d1e044a002810066a81c92400722410c6d0724040a808218794a28001c81022d45504200111004578b690020540010a968d12000440019508c50400140001aa0b2c440011800453e6a080002200089609a25000a20821004582a0014410218c75454001182042b7640980023000c4c54815000e60810852670800140100902b845200391204102bc10800510010177f224000a0082019ac02800088102030c9240001100050352c8a40050240800a8f14000a00810001a224001400030003204c00288006), (46, 65, 3, 20, 3, 24, 0x3f29bd09000210047f412880000348020f6d4dc20401a50117ad33e20000d20093ca2ff09100484047e448c84080242022df93cc214012141168f52e1300043008f14ca7094006910477076a88000240024b6d51c20002400115b0d021100121008ad4a230a8004882455fd1284800480023afd7940440121010d7530e1300121008eaca9b018004880434cc4b81200240920a33aec02001a60103e237210000d20089ed7ff08800698044ef74c8520010892275a53c24001a4011ba64aa14000900489d2f7909000480046e8bcf84000240022741cb426001a6011b9f00e1300091008dcde9d08800488044b9236850004801225c4d54020012201025dd0a050009104812c4fb128004882487f130850003481222f35f42a0008609115c06a1280042208ca8535018006980425052084a0024082322f9d421001204110dc36e20a00d2a0906aeff124004812481c15d8540034c1220c20cc480012009205945a0400090048013bcf0a00021024408b1a84200108822), (54, 68, 2, 21, 3, 26, 0xf447ec09100694406ebb64c088204a8404e92e3c09100904406dd1c9408100904404d3b36c09800908406d3872c09100214406c7c78409000900406c0400408100694404be6f9408100214404bd5464008204a8400bd10fc40400211401adb7cc09400481406aaed9400400691400a8fc6c0a0204a060493bd6c0880021840488730c090209204067f3bf40140069140277bd8c0110048440277460401000480402755f940a0009006047118ac0a40048160470079c105006954086f36ac0840069140468188c0a8002186046761a40900048040665672c0a00021060462586c081204a4404601054028004886005c909c0a8004886045c2fd4108004884085ad0340a0004806045a3664080002104044dd454080204a04044c2904480209204054b9f24024004816004b03440200021060047d15c0880048840446ee0409800218406462ad4480002104053deabc01800488402394634020204a060037839c08800908404309424088209284042ee8f40200048060026a224120004806081b2a9c098004884061b244c091209244061aee1401400481402107bbc09000210406103a5c080009004040edf040802092040403a3bc100004804080055a40800048040400326449020920407), (44, 68, 2, 21, 3, 22, 0xfb826542000690201f9f9fa50400481009ef6bfb41100484003e7b2ed49100694007e2d1eb4a800698205e273cf8a100694204d1d7410a4204a1204bdc65a90500695008bbc75ac8120924005bafaec41100694003b21cf5c91204a4007acf5b68a500695204ab507e48800488005ab364049000690007a8a362c9800488007a70785d28002182099f3744921004842089a1329c9100484007840306c04204a1001704ad10a1004842045d302bc95006950075787c9c80204a000557877ec900048000757827448000480005515dcd490204a00074fffe34a0006902054519c348000900005431b07c94204a1007407b070a5004852043e90daca0004802053b39808a500215204360f7d0a100214204302daf094006910062fae6e415004850032e91960850021500427492e4800069000526689a8950021500622622849020920007217c8a498006980071938b84280069820118af998940021100616a1cfca000900205149e6fc802092000510dba290800698008), (88, 72, 2, 21, 3, 26, 0xffc04390a100214244fd27a8452500485609fd0635c418204a8403ec17adc10500485408e8dc90c40000690401d824f6412100484608d24e8cc49000480407c9c2a6c48000480405c9b94a912800218248c13e5b448400481405b6db23c4a400691605b2f4074104204a1408b18017448120924405b0d9db450500695409afe4f94484204a1405ad8511c49500485407aa7da2c48100484405a54f26409800698406a12d0b40a800698604a05fb61104002110489d3336c0880069840490341f9095009050467f0985c095006954067d49c0c011204a44027cee5111050048504872bec6c0a10048460469fe3bc408204a840165ea2840940090140660bb3010a4004812445ca72dc091204a44065c23edc4980021840757a52c1015006950425630ee40a40069160452fd5dc4a00021060551baf61095002150465010334480204a04054e485e908500215044447d0e40a1204a46043dfe604085004854043dc5b0c491204a44073daaffc0840048140438b2d34481204a4405384e174408006984013783951091006940462ff2ddc094006914062fbbaf9095006950462db9ebc018204a84022d87001015004850422cd54911200069024827c9a0c010006904022303cec4900021040722fefb4098204a840621f4cfc4910069440720f7d2c49000900407209480c084204a14041e071440a0006906041dcebd4105009054081da3fac080006904041c744d9084006910441b59f19101004840481956dac120204a060818efa9c091004844061833d140900069040618056c10810021404417e6fd11080069804817a0f790910021404617479c4100204a040816f0849014004810421635454010204a040215379d412400481608136c1940a8204a86041337501081009040441334dc90110069404213056fc0a02092060412c01490910090404612ac1f1014006910421282e7c090204a0406127b9291040048104812740f4081004844041152b891080048804811183040812092440410b0714014204a140210a407448000900405105417909400901046102cb69080002100441021881088002180441020ce101000480042101912901000690042), (21, 65, 8, 14, 3, 26, 0x1cb7301804a40a958e4896b90050072a0e885b2a00280395431f16ab00908150b1375fbe800840a8507c95669021005084b9aec8e012003916115150100100140a08205f4200a00a1413c7d06c02000720c1b902e20000039040ce1e02408001c8124ba70c204800e449206ff3c02100508c10227b081400398245b7a68400401ca022c2aad805040aa18147192400800510809171148020039104482f544010014082236099800200e510), (32, 56, 2, 16, 14, 15, 0xdbab04c4a41605bac39ac0a14604ba749900a14204b5591c84a8820565d11544988407619dc5809550063b15b30085500430e36a908550441a5d1f449004071807c790814044179beb109140461720bc849880071552bec4800405153d1010841044129ccb40914406102cf510800044102136908880440fc088909000460fb586109880460d1b3a809140060d1ac8008140040cccc9c08144040c142640a886040a928910a882440a856c90a002440a80a980a8820405d0c0c090040605abd440800404054221809880060484684088840401602f409884060004ddc0a00604), (32, 61, 2, 18, 11, 18, 0xff2bfe048834002f5920222441a10174dc4e61254ca00f9b0a3d890264405cc6f2c048132002e3e6dd424899001f1114f00294ca4097f90e8892264407ba6326448532a02d762c94050990812957afd0284c8c0924247e8908614056280cd008430802255613a24c1a101c55612c1200c000a26d4cd815068604119f62c09132203074cec604c1a101832f3b90240c080c174e970140602040ba50a40a03030205a121a0409910101f71060240c000c0c70ba0150682040613000091320030302f2c04099001013c4c71200c080a095eca011068004042e7880983400301b276a24818101c0838ed0220d0808016c6b810060404), (58, 69, 2, 20, 3, 22, 0x3b3f62a4910022800fcafb9765400118205e3ede9940001c8004f089de925000e60823812db8c250072a403bf3c81a8080394009ddbc3172100140802eab7a8e80800a0400752bd0a4952054a00f9b8c7c894102a8208cca7f674900140904e2a0c70948004448170c23d5420205404037fe94fa54102a8205b5c40db01001c8800da419c782000e4000eb36cb5c940022200f57ff82a12102a1201a8f2ba105001c8801d3eb8d885000a2080692d2764082055000344cc3aa5200281205a18131f2148152802d059c0f83040aa000e77d1e54812054800b35a8bf29000110209999a5fb0900140900cc450a212a00a1401a5452ff4102054000728d940a02902a50019122ef32808150102c80e248a0840a840263c197b120002204111d79d0092102a12088e3ca1b0448152001c52084f82840a8400e031ae2ca80051040b0026f6282803950097cd500f48001c8104be060d081000e60005eb06a74a00022040af290b8a0a00281003755753325001c8803b85a14592800a0401db4b9e0c1800730006c8c0a3e4a802850076245c3941001c8804b042f9493040aa001d7f2caac882055000abe29e5604002880015ec10e72908150902aeb02fb910004600155f7bb341800510006a6ae54e4c00118007520d36c414014280423327fd91000e6001517c3ce4810050800a848c6ee4080114005), (55, 71, 2, 20, 3, 22, 0x1fa5d2d994a40a94817e8a05d54208154004f928f34e82902a5009f106f2cc250050a403cdd115b248004448239b6d89f4140142804f2ebabb090902a4208e3fc54bd0400222013c5f9df7a5040aa08277b8703f4948152904ece9d29e9080284209d5fc704c150072a007aa8dda220a40a9402329bb4b849401ca90463eb1bba90902a4209c0098a852400222413543849a84a40a948069e771810140142800d3235f828080284009a5d176f5280051041346a64b290a00e5401673d0fa329401ca902caca9152088011400394cf8304a12054840b13e951724a40a948221be172a40481520043f5430fe52801152057e96ae9c152054a006eb61c8f94200450815d1c6f990840142100b8f399ee5080284205713e26890820550010e1a185a25000460821b403afd28401ca102b5e38f0e520039120567063724050072a002cb88ed420000e40021934965f4808150104b04d093a52802852055af749052000500412b3a691a84800e44805667fa830848152100acb8f5ce800028000958a49b2c850050a00aa68bd5da4800e44825445c11a41081508042803374e42001110054f7e291c810072800a9a8002124a00a148211f4ff6c484008a10423d0db3a0c0011800345a69754842054200a8b407b690800e440150c7da470a08154100a02ff5a292102a1209), (29, 72, 3, 19, 3, 24, 0xde1affec49401ca924d19b66440400088021d1870dcc08401ca120cff6ab74054008a821b588ee54494008a92493e157e449000889248eb498ec404008a0247f5d066c484008a1247186582c044008a0215c91b9dc094014292057b7ad2409401ca9204ac3b46440401ca02446902e14494014292440da7f24400008802440a68c0c420008c02436919fd44a001cc124352d60e428401ca122339ae0344840142124296c1b5421401ca82227e728d4294014292225cbe1cc294008a9222591268c254014282323c0530c4800088124227a67a4060008c021211f528c29401ca9221ae70fdc41001c882418498a9c2840142122174ce0b449001c892412dc02ec29001c8922), (51, 72, 2, 17, 3, 26, 0xefc5b6d45010034409e7ab510c1280038608e0ca81ec4140031403dab355dc5000030409d7442bdc0010034400cf4962244050035401cf1a2b6c0950035406c5733e240850035404b11290ec1240031608aa7057240210034600a5cd51c44010034401a131431c00400314009e6aca0c485003540592a5448c00500354009255eb1c4950035407904fe69c42800386018e64d41450800384098b8ff07c411003440384fc7e3c12100346088404bb940940031406702b87cc08400314046a64c23c420003060166f795f448400314056564c0e40a4003160465037bb44a4003160564b118044a10034605634cd714120003060860e6ca6c12500356086023c5d44a500356055d845af402800386005b1cc89452000306093fd08f8c0a100346043e213ad410800384083bd0b13402500356003bcb63fc4910034407385f63e402400316003612ee8440800384013489bd7c10400314083350997c524003160932e0b62c4180038403324fea24425003560127b86a64528003860925c3e68c40000304012576d66c008003840024e6eb0c4210034601203ea89441000304031aeb6fc448800384051a2e65a44940031407198fd6f40180038402128151e4481003440510d349c44a80038605), (48, 73, 2, 20, 3, 26, 0xfc5175b10a00144300fa57d808a4200a11827cdd7cec5050050a813dbae27e25000280605ed4853f12608154203f6244e7882800e4500fb0013f40a100728c09bf5a006250902a4605debbe6910100140a00ec3dab6884000e418075335e1c0952054a80da129f3220400288401ce314b1121001c8a02e0b2718804240a91802e85651c4980073080f62df426092102a1608adf0a6f00548152a0153a9ffa825000a218228880cdc41100508807412603604a802854069f7b1b102908150b024d02b18882a00a1500e672f0bc418005108072f92226092803956089108b4d104001c8201c6b4031894840a8581634fb25c4050072a803188ace2082002814087c5dfab12808150302b7beaa2892200a1101db9e57a44a400502c0ad4d20360840039840867d4a7d02508150a0333d8186882000a0100d9cc401c4900072080ec42d7c2042902a540461a40fb002001cc20030b013a802a00a150097bb6fd402800730c00b9e272e20a803954035c14e0d006001cc2012d4698b883000e6100d6861ba44940072280ea57c222042803954044f6558300140142a0025ef659892040a8101d25a7f3c42800730c02824dce601280285600), (65, 75, 2, 20, 3, 26, 0x7c5e5ede25080394605f7ba4e2442820550c03eeaa7b7824240a91823c37b22304148152a0472c4aa2629400288609dcd999bc50820550813b08ce3d892840a8501f3ceb19914200144204e77e9f7e20280285401c9726e0c52400502c1390f80fe890200e510171efc4df10840142300e1b11eae25400398605c0204e3c50100728813729500e8a0040a81026c9cd819122001cc202d6c0774a05280285604a9b722144a800510c0b4367815884800e4580684c34cf10808150300cfbce2ea250802846059c678b9452820550c1334da0e88a4000a018263e8d3850404815220443a8d7c620a0028140381ab472c4880051080aff65f17895040aa1815f3326bd12500140a03bde40ec6208102a04037ad3521c4800072080af3ed1a78a4040a81825e54f86d10448152201ba849b62212102a16017453739450120548812e66ab5b820000e41021c482cd5128001c8302b7c57e92084102a84086f0f64c44980051080edb053bc891040aa1015a80095f148001c8304b4363cf60108039460067d4ee144250072ac02cf75a2a824800e458219c79e1f10108150a00b272c8a200a8039540260a6e50442100728c02bf1854c882200e5100d711299704a081543042dc354560088039440259fd70d440400722802afebbeb824000e41821576bae900148152a002992d6be21200281601525ae72c0250072ac00a477c7f8a0840a8502545a4ff104a001cc3042503043e0820039140849c6542442000500c029236233814a00e5581118a26130404014220422a7eb2224a80395407454e482410100728810873482f824a00a158210cd536512140142a02a02e3f9e20080394401), (26, 59, 2, 15, 14, 15, 0x3cde90e44416824774f56fa252d605eb615399125a490fbfa08722484921ad52f3b0250a033170c5be052d6045adcf71c4a00c0a88ca8e8812b5018e4dd1241296902996c500884ad046328209010a184886241b3789431814c4748c642508231380f0f8240c00526b349f8491800e4bb84b0890b5014940bdf402969020f61aade24ad4071b343c540a42c083587810214849106548e4c42969220c8c18aa24a1407145366dc085a808258c6e189031014486a8c912462038816e1c8250c205), (28, 65, 2, 18, 11, 18, 0xe19be558094308036371a28c25299481695c98c91290c2c0b2cb607b812a6540691395f540a430b022d8af5520429950115d2c1fb1294cac0aa713ce0894264605516e28c048532802a804afaa2541a181514890561284c840a8106d83892a6540740292920484308029ea0299c042994010f4ae2430210c2808776e8df09306800736f4abc04a030102999c500c2541a0814c927f600254ca00c64851ef8940606052ffbbb500a43090216e46918244020014b175f381240c000e55c384e09286100722a1ef844a8043028f326cce24a18501c754aeff0294cac0833d336f891008405), (70, 74, 2, 21, 5, 24, 0xfd88b0bc49420c8501ff11642810408320003fb4232bc4a400c05817e44ffc314840304609f6a1e8a44a800c21817c7ab15910108321401e9998fec52520c9582793ca4f512608328407e4a36f3c40120c910078dee17b10208328401df23187841820ca000f4a5e44612208328005d22b7f0c4a820ca18174758e3110940305601c6ebb60c4a420c858171ab865412848324205c613fa484a100c10817101256614a08328209bfaaf7d450800c21026e64017e14840304209b8718bdc4a120c91816bd73b1512208328405ac3bb89852000c00826a90fc9912548325407aa01bac448400c05016a11170f00448324402a3fcd07848520c940168cead2112840304605a1e9ffb04a420c84816522b9d8122003080058fa8e48048500c140163cf96d312200308405886be3b849520c9401df1b272f129403056057bedf4a44a020c81815d298c741404832400973d32a484a020c80815b1bb390129483252055d5292a441820ca100d7392091121083214055a3f060c41020c8100d6840984142083280095861f1a440020c810055a0d30b10808320601529e8b5c09500c15019349cfe91420832840948833dc401020c810091f6ac8f1050832140345ede63449400c0501d08d4c27126003084073ed5a4f048400c04014dda76db02608328406354cc0cc50120c91024cfa029b00608328402330ad96049420c8401cc5e7874129403052052a3981e442520c95804a44039b148083206092748042848100c100149bee9dc1244030400722300df441120c9100c7caac42105483250031d863ab048420c840146268da11214832540516cd249c49120c9101c5981f981244832400712b747d448100c110144978a2f1244030440710dbd6144a000c01814403159212400300007), (53, 72, 4, 19, 5, 24, 0xfe8e40cc12500c1582fbd8e71012000c0082f1c94ab402420c8580dba6886402100c1180d68696a412100c1182bdf22d4408500c1501b2d0aa8912000c0092acafabf812500c1482aae0a41c12000c0182a94b96e410420c8502a8596fec08400c0501a1fa563c12420c8582a170c7e110800c20129b06e0b402800c2180958df5110a500c1491942c5f4c10100c1102932cad9402000c01808f9ddbb90a100c10918d93891110400c041285b63cbc08520c95017ba4e51c12800c218279bf28ac10020c810278eee2f912800c209277edcf390a400c04917201e8fc0a800c218171376f090a800c2091700935cc0a100c11816bc075e402120c91806929f78410800c21025fd19d0812800c20825d111b2c0a520c9581554a0dec08420c850154a829ec0a120c91814cd2af9c00120c91004c6e9d9400020c81004b42e5e410820ca1024a19db2812100c108243921afc02020c81803d93692412400c05823c817abc12120c918237b6a54912400c049235ecaba40a400c058134c659540a820ca181304cb86c00820ca1002d11a54108500c141128f2ed5c02400c05802807d21402820ca18027b45ec40a500c1581222ab03110000c00121b4f934908400c04111a135aa812400c0482171baae400420c850010801ddc0a420c8581), (53, 75, 2, 23, 2, 25, 0x7df51f480c003c98042f33298b09800591008ddfa952e02001340010baa39b2125000e08803f4b6cc6280801c14009ddd60e04a420184240bb5995e612201341011b667f85924080610003e715fd6252102ca1205c947a8d09400792208d67af66ca0800b204026b20cf6c2400060002355f3fe680c002c88042aa1af3501400792208551ac0de12000f24011a7f785a4260006040234fba34d24a002c810079c7bdf049800383000f386a79890840308401668d853948001e48104cc6e404848002c80046973ecc449400792200f2df866a12200b21011a461043120400e0a002c314bf9292802c85209810fb1249100180800ed0c146094000b2008158dc48c120400602002aaa02b124c000c08007549ac16500007920012a92d4549000070400153b13d7424401e4a02325cf8e8254001c1820544ce50050820595001283c75fc910003020014fd6a2414a001e4c1049d1291f248002c8000737080ef09100180808c63d879e02800b204108bb7600c26000e0c0231766938248801c140071fbbcb909000382008c3d549b490040308001475da1e1400816500048de2201848801c1404614aaae650420594201226d133ca0800f244024428788404001e4802106fc0ab808002c800420b2274c49800591000e1278094a4001340082417d0ae129000e0890282d5d0b244001c18005), (65, 77, 2, 23, 2, 27, 0x1fa79d42244100c28405fc3551b120401642202fafcf93812000704101bd1fe58c09120594880de39e9de204002c88401eddfcfd140401642204f602a948910013421017956b464018005910805b6201ee250801c14605d830665102001e4c200ea9dfaf8a0040b2810274373744505009a0a81390a5fd6290803c94609c678f37120480612202e2355b3803040b2a100ad09b03c4180059108075db04b620c102ca8403abe3455005001640a01552a93889004030810169c306c4098009a1080d4baa852240904d24405a3aa551120400602202d14a70d88000070410065aaebf448000382080b2d32ede240000c004059412295004001e48201480eaf5892000300101e2ff8e7c49000590080f0e29ae224c102ca8407827fe2f02408061020340fbd9d8900413481015fc356f409000590080cfa9519a252001c116057c19ae1124400602203bde89b88940013401815d00400c491009a0880ee694596200003c904017341b5710a000e0c300b8561a2892a00f25501db8033a4480009a0080ad3bc462048102ca0406631e111122081654202ab7e42c88000134010054570564410009a008069c47002248802c844074951ad3100401e4a200a49ae4c802840b28500910471bc09100590880c847c492242800c054054010469149481652b049f4af07802200f251008de5a31409100382880c55f9dfe00a902ca540228648c5024402682203119c735882200f25100c86dbc4409820185080c4355e7600c001c184021bac4df005001e48a010b7e79d812200301101833cb7bc09100792880c16b0e8e048000c004060945835129000600b02836e52389080134050141af3fcc49100382880e063261e008002c80402), (48, 77, 2, 23, 2, 25, 0xff8ae4a940401e4a004fac8fa5090a403094017bf20921094009a0208dd232f1a254003c98205e6642a5149081650904f235a25094800f2448177e4ae0e501005908013b8e725080c001c18042d7e7625128480612102eb05a8c212a00b21411b31e94a8525009a0a41391263e1250800c04205bb7e6b2c260026840235c7a4d00a0240b290026e37e3cf014009a020856e7b187254002c88205b498b27128400e0a102d99c06b0a08007044026a33aa8248120184800b49435e6284003c980099f6be82928401e4a102c8a8207094200b2108162f1671a48820185000b171cf4284a800c0504687f3287425000e08823420fd940a4a40b29482602d2a50520003820412e7b61f0290102ca02096ff44f3140001640004b556f52494800b204815a53ed344a800181040ac66a495290002c802095fe668f924000e08003af2cf25494000704081577ae065090009a0008cb5cfc1c242001c1100559cbc93c254026828232b98e25612800b204119526e7f0521005908412a4d4a82242002c81005518f39f142000e0c004a7247fae12a00f2541192b99c1f09400180208c9226431292002c8120948dd966928080610102a3ee0e0494000f2408151c66b8449100590800e85b0bbc84c003c98046), (57, 78, 2, 23, 2, 27, 0x3fd50fb2008004d00402fa65c75892041348101fe2eb49e240801c14405f56094e8940403081817d336242048104d20406f38353f884a00f255807c89ba9e244002c88405edf95e18950013421817b19b51e20c104d28403e3203e6892000f24101f7761202240803c94405db7385b89020134110176c6777a280004d00409d8047c3880800f245007530e412250800c04605d3bf3a8812800300501b42103ae00a802c85402ce8c83c892040b28101f330c70e254001c18605cc1539d802040b28100b2fdb0c624a000c01407c421830882800f24500f0be68fe250000c00605be9fc20892000704101eec2c31e20a002c81403b2240e7802200b21100ac785126202802c85401b0574e8892001340101eb511e02048003c90406acac64b880a00f255006a29ea16242902ca5405a665ebc893000706101e942754e04a003c91406a09bee2890000b2010167e01e16250900c246059f3502d884040b28180677d505a212801c156019ce87f08908003005016727906a04c102ca84069b2a4d7882040b28100e60ae73e240003c9040597d3b31893000302101e59d7cee24c104d284079543706882a01341500e524c866280001c104099410ced882240b29100e4ce0cc6048004d00406914f59a812240309101a3b53772210004d006018d21de4802000704100a2dd0486244001c184058a15246892801340501e2038022244000c08405873d716881040b2a100606964ea280803c94409813a168892040308101e00d2dc600c003c98402), (77, 79, 2, 23, 2, 27, 0x7f6c5dce04c104d28406fba3f89c48420184280bef1287c882000f24100fc9bed8d005401e4aa01793056ca24c002c88407f0738fb4428007930c03e0c8371882000b20100fbe7566f00408269020177c24d7e24c100c28407ee68d31c4a0005900c0bdb97d09812840308501bb4911bd140082690204f60db78a282802c85409eba024dc418007930807d56b14a894a40b2958178f620a5128401642302ef459d86242904d25405de72f68c524209a42c13b7cce0f88480070458075e841c9005402682a016ab3edba250001c10605d4838b444a500180ac0ba7b8b5c812a00f25501b4ceabeb122082694202e96e30ba20c004d08403d1f1883448500792a80b9fdf4e38a080134050273b6aa67120081650202e650fb2200a004d01402c9da9c44420005900c038b4d142802240b29100b128dc8712a080614302e1dfb5aa20c001c18403be86b064520205940c137a099ab802200705100ae8a6b95025081650a035cb9c6f604c002c88406b8001c0c4100038208076f36743892200f25101ed061b01125402682a03da08ba7a24a800c05407b094ac74520003820c135e0735d803001342100ab76338302448269220356be6de2252100c21605ac153cbc4a8001810c0b4ec8e1a894000f241816949c3c3109402682b00d20caf86248900c24407a40feedc49120594880f44ee5ce893001342101e887da29101001640a00d0d13b46210802c846019d370c4c011009a0880534f46f9881000706100657cb3c9025401642a034aeb5d0e250104d2060595b1295448400382280b279891e8a4000f2418264925aa5104402682201c86ba072244003c9840590b188ec09520184a80d1fad459813000706101a3b94659026001e4c203472bf10e04a804d054068dc506ac50500792a8131b04fb88842007051806311e227025001640a03460efde6280003c904098ba26264404009a028031094a1c813000302101a1e8cf7b101402682a00c27edf7a208104d204038497e2fc420007920c030705d3988080070450060d124c7025000e08a034011f4ee210803c94601), (81, 75, 4, 21, 2, 27, 0x7fe0f63221001342012fb7c957041082690a05efc7f58840801c14047d30f7f11200079204979247d1814040b28181f012c5a420401e4a023d79e7c6090003c9060ba56e504081009a0880f424229820000b20102e48e162441401e4a825c6f5e88854001c182476b273c908800793008ed419f4824801340582d8fda7c422001644023aab1644882002c8104b534dab108500382a08dd6717a811000f26101b7a2f5c449000e0892569777ba050104d20606b5e7461124005902495676b7b214800300491abd3eb5041001e48a055259f92040803c944068a6947908400792208cee7b4e224200b210929c414b302200268420331e8ed2050100c206064aff8f110000590009482bd1b220000f240128cd0fc2420000e08023199fa10840000c0004632a4af90a000382048c5fd7ef215000302091834c1d8448401e4a12505a3510854002c882460b21b8908800181008bfc51622110007060117a85aea420001640022f2b70b8850000c00245e40ee7108000792008b9e3e5b810240b291017251857020001640202e15e362054003c98605c0f0b7c0a500382ac0b733d4181504134a1816b0f85d020480612202d5cf83e050802c8460592a48d40a1205948c0b110298210800b204115cdc3da420401642022af68cac850801c142455b572a108100180808aa3dba8214000f240915413e190204016422028e44dd6042900c25404ff42759120005900491c458d8210a00b214113764555040001e482046a1f5f4852003c91244d3c36310a40038224898dd37181024134910130f66710200026802025ad10ea050800c04604aab761c080209a4080949e37081020030110126b3834428401e4a122485a7f6080104d204087abf0fc124007922c10d4b831814200f2518118c598d028400e0a3022af91d2050001c10604555314c0a0005900c08a8581f81400030018110dad0f02008165020217f1242050900c246042e37a8c088209a5080845823d22400070409205871530200006002020afa8e4854003c9824410a48940800038208080423d5810040308101), (86, 77, 4, 21, 2, 27, 0x3f3993cf040401e4a205f593e7e820001340102f999a76408420184280fa2bce34852801c15247c7d5aeb021081650a03df1f0be221000706012ecfe95e11010059080975c499e6050004d00607a06c8bd021000e08a03cfb9855214801340491e17eee31088009a1008f0bb5d78894002c8824b7e07814421002680823bc2e83981504030a181d9d5cb0c124005902c16c89af5e042802c8540763aad40428002680123a93b4b4820a00b21502d45b7e140a8205950c0e8e2359e050904d246073582e99021481652a03970de99814800704581c6b091990a5009a0a48dffee310880001c1004aff8481a44a001e4c1257a9d229820200b21102b9bde65412500590ac15bf2b6bc854004d08246dcb6eff029002680b035d1cfe1820200705102ade2f8fc0a500590ac0d52454b4842804d050468cf8330429400602923428e3cf2208007044129f116c91104001802094ead8016084104d2840a63af3d30480816503052f8e9de814840b28581972c435908400180208cb254620850802c8424641cad23029001e48b031f6dea7810a00f255018f207d9410020594081452d82ec842803c950461d2b9410404826922050ceef492142003010918470b5e40a520594ac0c1ddf844892003c9124a02e9524442001644024fce42ac210a003014117e609729080009a0008bf1b5992080001c10409de8b947048002680304ed9ae6c81480030058176c1c87c08000792080ba72defe054002c88605d2a4e2a44a000e0c124e0e5d8281104030a1016ed56b341040059028134ee4966044102ca8405a223680429001640922ced8c53814a4030958160eeba2108400382208b049d98a044002c8840581eaa8702a000e0c302c022b9c8150003021815fc154d40a0007920c0af6dd3f0840804d040457a96677042001644204b3e3fcc820a00f2550259ce8231101003828092b49924a052002c816054f8bcb7048000e08304a053264810800b205014f9c9a0408500382a80a7240ff8882003c9104931bda49021400602a0294498548102007051014a22c6fc121005908c123e58912044001c184051a524ea4280016401228b812f4810800f2450145973004124205942c122c13366044000c0840513e3e6842840268212288d6ace814a41349581), (13, 71, 8, 17, 2, 25, 0x7d57001a05000f2609f5e36b0408401e4a13e115ba0812802c8525be7cf3d0240079224aadca8fe04000f240940731f2c02001e4c026dd996d810802c84248ce776900400590208fb5144600800f24411aa2230c090016409229d235b804002c880444fd17d00000792008000015e04000b2009), (37, 70, 11, 14, 2, 27, 0x3d0d94fd000400e0a2eb12eabc021009a08f9a2f89d0020026842e657800c004009a02b6b17963008401e4a3d828f1a4028005910f0068557009482692bba4d438c001209a48aaf23d710004026822a9bdc28400500792aaa579a750084016423a70cce14020007920e4886ea100800268038f9c1a7c028007930e0b2e5c7009001e48b7f6d187c0040038229e54d40900208165427815ebac020005900da79463f00208269425cb0d594020205940d4a9383300a0816543521f4be4024005902d40646ef00200164424ee9349c000009a0091c59ef9000082690240b1b8e40042059428e44ff85001001640a32fc9004005009a0a8b848a53001001e48a2167ed4400100792887c83d39008400e0a31dd47e240080079308370dcc7009081650b0d85731c00500590a8316becd002000e0c208bd650c000007920804652df000000e082), (56, 73, 2, 25, 3, 26, 0xfd3896008122850201794c50424410c05011bbccd9820048a140811d7fd5c090049100406eae1c084a82180a823756ff30204124411013a284c812208602880dcd5cac091041004406e44a2a04c0228442036a0a64420010c04011346ed6802808e1228059e41b9090043010046ca7b4884802080002361c487026010402101afea4e812048a14080d7a6f11094047091046b8cf2620a922852a01db94c50204104011012bd9b9210808200208958a6d4090041000406a669c60409208122024e04eb024010c04101a6cd95212808a10208d3383cc088249128404992fa204002384820249942d020010c0410123e80981100922108091439290910450840467df9860408228422023de49a4200104000111ed2398110086030808e15eb10840450810446e9ef60440228442023393a500001142010018a884212808602208cb20ecc0910450844065784160480228402032b6d6902001244010113b0e2812248a14880c9ce4240002450a04004e5fba04c02180c2031ef6750220104021010f23288110482050808627e1c010045080402308b5c84c02284402312c90d02009040810109598b210808602208848d17c0800410004041669460800228402040998d9020411c25101049700890048204080a1ea6ac08124912440408e0ba04002284020202649842401142001181167c810048a14080804846c080249120404), (67, 77, 2, 25, 3, 26, 0x7d438471220104021017e86477802848a142805bd1159c480249120405dbfa00a248824882203ea90d890014124415003481706801008e130801a2a7204488047098405cdb25ee282022840a04e48dd97101011420500724092e812249224880d8f035cc490249120407c478d26240022840202e21f645124011420101f0be0ec890a48a14a80b7c0c3cc008249128400a66d32a080822842204525755b00609142a100a8c5f71800a08a10a8013c5e77c4052450a540195a55fe08402180c20449e9b5d12041244110164a3442221008a1100910249cac1080450884087bd4e6604a024880a033ca3bc104209244a1021dc8ebd221008e130090cdb078c0180470984025d271960009248922002e17129022011c261011700f7c2110082010088b6c9c0c4150450854035950f7484402180c0222a8182500501142050094c4e53800808e122800a3c750c000249120400510108e00802384820123e123a441011c2441211d15d98a020860288128bfcd74481047094405452967a04882384a203226eded12609142a101d0901f5213008201008c77e4fec0812450a44043bbeb2084c02180c0231d5c645040411c251020db6d95880208a1088026c574bc098047098406319eb3e0480238482031850728421410c054110bbf945801048a15080059d160c008043018400293e95204282384aa02144cf3f100411c2510046f87ca813048205080c3553a6c0902410204061a5589a0489208122030cd2041024092448101865ccd5801008a1108003063ab108504100504417edcae0000238482000a98d1302209142a101050d9c38102086028808282485908104301404414031e884082080202209c26f902601244210184d2918803008a11080422a2479091041004046), (37, 78, 2, 25, 3, 26, 0x3f46c9f40152450a5402f69b311141011c245027d552a14494045081407f33dc51124411421101fcbfb664404047091401f2b7c1500049142910036fa17d4508045088409d7b166244141142141235224519014043011042d406871124010c04101f40238fc400045080401ce92c48441411c254123365fc74488045088405cb8dc1b02141142150131806584018043018402c4a2787004411421100b113599c095047095406c34e13d104411421100efcdfccc001045084400bbb4a8b120010c041016d23cb94084045081404b0820f50010914285002adf182c481043014405a679259042011c26102292b7851095045085046a36f811001491429500284b20b448504301540596097f5102011c261006528dbc4480047090405947e0c302609142a101a510905110404508104893ad264440411421012243761f910004508004890904c8440011c2401223cb391c4840450814058977805122010c0610161ca1384100047090408), (73, 80, 2, 25, 3, 26, 0xfbfba91c4012450a4401f892559c508047098409f588eb4c418047098403f184e1ac494043011407ee000a4c414047091403eb762609100043010048eb5f251c5002450a0409e7f411b4504043011409e319dab4410047090403def615ac500043010409dc8bb2045082450a8409d49718dc491047094407d1d415344182450a8403ce18dbb44812450a4405cbad42cc494047091407c27d6d6c094043011406bedc8f2c501045084409ba31c504005047095400b3aa2344084043011404b30c7c6c1042450a1408ae8d3af4495043015407ae41f214485047095405a67a87e40942450a1406a1cc5ffc4102450a04039cfbaaec4050470954019af31c84414045081403921de1e450004508040990d539240940470914068fd2d58c4802450a04058fa724744850450854058cb17adc5052450a54098aa0a91c09404508140686158bb44080450884018449979c49804709840784121a1c4942450a1407810c6cbc1050470954087fa31c344900470904077e5029e44980430184077e4912645012450a44097e11e2544882450a84057d84ee244950470954077c3ce8ac0842450a14047bfcab1c0952450a54067b2201a44840430114057a61a63c00104301440079bcd3241050450854087234a35c0112450a44027129461c5050430154096e3a1fbc1082450a84086b36dab40150450854026af47e3c0840470914046af23fac4952450a54076a05ee3c10404508140866ba58c4095045085406657ec2cc4912450a44075d5bf05c4142450a14035a4e23ac00104709440058c63d14505047095409569adbf44050450854015662c6291010470940485150f6d41040470914084d8ab17c4000470904014c97f1ac48104508440549f56e1441804508840348b1d464484047091405477698a400404508140046fc76844902450a0407440249340852450a540443a9ba24491043014407435db7745050450854094155a60c410045080403411e3e2c5000470904094069ac2c498045088407), (64, 78, 2, 25, 5, 24, 0xfebc977c084044005013f919c53100413104401f59b2f1448824c4a1017bd4ae27021491025404e3a8edac48404c4050177a90e31122013108405d7c3c62410104c41102332d5d3d004493124402c3445e8c10804c421022e6b4b9b005413105402b8e29c6c485044015016e088bd1025413105406b40c0cfc09504401501aae0d70f106093128403a300f44101504401410a4ac933f1260110084078cdba91449124409101e2b7cab30040931204027fdb3d94484044005015e1cf13b0060131084026f9648dc08504c415011baa44411240131004076d2dafac48004c40101596fde2b104013100403633adb6441104c41100d7f36b610210931214045f4fe6e40940440050197abeb8f1004931244015bf512b40842440850115ee925f12601310840756f7352c49024408101d4fe872112049312440553993c8401004c401009451a7fb1210910214054efba12449524c49501d3b0b4210214931254044eb1c2a401824c4a10093302be51000131004014bee07dc49124c49101d2896bc30000131004004882ce2c41024c48100d03fd15d121093121405400973d4085044015010f5dea791250910214073af15089095044014118e4e3ba5102093128401372ec26c481244091014d5c39310020131084003542baa409824c4a1018ce6fa9f12501310140731297e3c49004400101cc21cf5500041310440030854e51094044004118bd02cc30244131044062f18bf64480044001014b7cf2871254131054072c98751410004c401020ae6f4c912041100440529e6e82c41124c49100c9dbdedf12441100440725fd57d401104c411008977a93900501310140225dcb33410024c48102091bb3f9125011001407), (62, 81, 2, 27, 2, 27, 0x3f7acf0c5204098a00c13eaae7ba0842014018408eceb70f1491016240b04f2d90bb8a0880500450278d5b98c0244028022c01bb06c7a240200c400405db1d157121100e208a02ec852c28a0280310110274d444944204068120c039ddf74e2902014010609cb32227125500a00aa03e41261281028050051012de0573c108406813081164f2a0a284202c488409aa87599122100a00c202d4e49248920805004101ea3539fc498403883080f4ff6146248a00c404407a6f23c1128501e24a302cfd11248a00c0b12810265bead844214018808c032dc6f76012a01401560093002b51291016240b02c78526980508050061802369e9e4498401881080f1aed342092a03409560889b20b3105100a008a01bfc9a04814a80d0255811ed5bc1c481401880880aeacea82208a00c404403680b539109101a048b00b26196e892a803101501d88b7074098402803080cbb3b9e220820340904035589dc3106101a04c201aa17e28881080d0261005498cba40204028020c009e8b73e280201c410409483a4651491816250b04a3cf25e8a0a80d02550250f123ec4a84018810c0a779ab8a24a20140114073b1819314858162523049ce9fa2882a803101500cdc4b53441840280308066b02232050a01401460434e67bf10810062003009a6a151892080d024101c9307f545284028030c123ec0176244200c40840518f544b02a101a04c3020c5ae848920807104101c45bcc4c0a04068120c08136c2e6242a00c405405099e307024100a008203049d5ac894280b1211814182710c498402803080e0a0867e05420140186040486a8f020100a008202023e2c0814080500418100c82a8c10440681228100034f7a0442014018404), (49, 83, 2, 27, 2, 27, 0x7f7e4ed624a203c491407fb956c8c5206058940c13f22d5658a488031005827d9e9fbf1415816252a04fa770c22254300c428605ef8ae4fc5016058948813ddd381d8828807104500f87cb4f112a101e24c302effd383e252302c4a1605df33acc45004078920813b9d84eb8a10c0b12a10275076c2f1411006200a04e1c7e7d6292204c501609ba9cd89c490405890080f6269124894a8031015816b9bdfe11251016240a03d7186786248a02c484407ad10e90c480403882080b5644d8b8908c031085016a60de9f148101e248304d2b6f49224ab00c425407a30d1f84491601884880f45a53bd8a0a80b1215026464a21d1405016242204c8a1fdbe282a00c40540990831a44505407892a8131d635fb8a408031001826250f3491411806210a04c2c38a1624c202c48840781bd15445086018850812f729e2f8830803102100dcf757071491806210b04b7d09cfe242202c4814056d7596dc5204038820c12d7cdefd89028071051015ac5e7d31211006200a02b3a8ad96202200c401401648ca9bc4a06018840c0aba6aaae884a80710558057466c991485806212304ac9d90a6214200c408601531358844a16018848c0aa517b498922807105101d44533611281006200302a692dc76240b00c4244054bbea4ac5084018810812958563b8a00c031081025255a2b51201806210202a3bb285a20a200c401403), (51, 82, 2, 27, 3, 26, 0x3fe9dc37104501c094403f93143e45044070245027c7af165048101c090608efa08e241044030045023bb88e17049500c015608e75245b4101403005102390b6a8d140100c010409e3b2d164498407026101f7e018a3041501c095408dbe0eee4100407024102353b3ed9040501c094408cd7f5b2c48440300450172b75f41125101c091407ca7d2dcc508407026102725aa4f5021100c011404c3a9d1ec4004030041006fa2130f121101c091405be1c957c4044070245006f73a3ad121501c095405b60eb87c1284070261822c335fdd101100c011401aec4bf044804070241016b95a0e1005100c011402ad245744501403005102690937b7140101c090409a3bce55c52440702458268cbb39d121500c0154059d8182744a040300418164e3dcf1108100c0106019082d97c094407024501a40df465100101c0904018ed06d2c491407025101e3ad198b148101c0906098d00218c410403004100e255fa53105101c091403872ed14c0a440300458120be3d2f104500c014403820c08bc5284070261825f5f79d1108501c09460179d61c0c0214030051801cbd62e5120100c01040570b9fc8c0914030051019b0ae559102100c01840165b94edc508403006102595e23ef100501c09440164b71b244284030061805758f20d028501c094604583a93cc0a440702458113b2a4b9109500c0156014cf503fc428407026180512fff9b124500c014407), (40, 79, 2, 27, 4, 25, 0xee3d0191021818150803dc656fe2903030281827a3f73b412140604230470435198942c14124605de8c75104a1028210c11b57548e248305048101f3a360ac0a1406042302655c72b8902c14124405b9e11d51061018110807735704a2822030205026da15c7c1086060542045376e4a8a1080c088409a1f2653126101811080f1a1003e20420302210062c322cc42140a082300c429bf08910c14128405825bcf5125581814a80f0265a5a2402050401015ce2226c0a4606050b0236531ba8a4080c08060967c88eb121582824a80abaf5742212b0302958055e64cfc491606052203aac64638848c1412160146c942714010181008128c3b7de25020504018150f642cc524406040b04a0f41b3892ac14125407341f081125502820a80e6523c862423050485014c81f2cc41060a0902019194c51813080c08840620206d70481818140c10175c466048203020101829f752410060605020402a2ee1821080c08840802e5edb02a1018110c080228b62080203020102003f666c120406040304004ed7e814080c080604), (75, 81, 2, 27, 4, 25, 0x7f0a80d6090b030291823dcd05d3049501810ac11ee513d88840814100601f725fea4484406040a02fb8967ce29430504a1827cd6113b105501810a807ceb3a4a8248814101608e65de3c442440a080b00f30b9d26208203020100f950e4ff1011018102803c0459618950814108605d6b1b1cc4a8406044302eadaba82210a0302118075036a0d10058181488039e1fdee8850814108601ce3e9d8c42560a092b00e67fa276252203020581732128611091018102c0398c6f0e8820814100403cc5dffac101406042204631f27b6290a050411826f28335b029501810ac0973014a68a48814101609afd179f4488406044202d7a852ea090a050411822b922d3910418181408075aa88dd8942814104605ab8d0434415606052a01d59430fa080b0302910228c18139100101810080343d53718908c0c0a1405a188490c480406040202cf83c086294203022182675279c3109501810ac0338f54ec894080c0806059c561474491406042203cc53de4625030504818164ae5b99120501810880b22be973892a80c08540790bb7b8c500606050204c50f989e2102030201806180a921126181815080f0936388812880c08140683297824485606052a02c0ab286a210b050491805fb34265120182824080af8d65f18902c0c0a44057c59807449040a080203bc091346280b050491025d7624ad120181814080aeb7283a880ac0c0a5401724ed3b4508606054204b626e1fa0823030285021b132569120502820880ad4adf9d8840c141206016a52ae8412860605430433705c6a2023030285005960895d149582824ac12ca4b78d820880c0814086294141c0914060422032e0c293e248303028101d6aced411411818142812b197783812a80c0854065845a11c084406040a022b1f640229420504218254f6be5b0481028200c10a1eef118800c0c0a04014c7deebc418606054201a5c9405229230302858252c5a3ff04a1018110c10910063c814880c081604472cfa7c49140a082203a3691372092305048582115963450491018102c1082e91ee892080c080407), (46, 72, 2, 27, 11, 18, 0xfb724ef1251c021407e20e21d00a14008600de5b8c50491c021608d068f1b1051c021403cb54cc702554005406c6bb0e102454004406c2c81070251c021406b7525031215c025405b3f60c104a1c028608b0ea8870245c0244069c13e871285c0246059718369029140016049713d430091400160095056bb1401c0204099020407122140084058c74a331261c028407887be031411c0214097e092dd1001c0204017d7b7c502954005604704746f106140084036cbe293100540044016c74165120140004056bc62b50261c028406678dac302514001406676abcf14154005409674f7870261400840666882770401400040851ea1050061400840246e8723100140004013574d831011c021401242bab51251400140718a7db10255c0254061857adb0281c02060417f17e902a1c02860416b8a7b1281c02060512ad36f0241c0204060f32ee1024140004060a137c30085400460004960710221400840403c39270221c02840401fa1c30401c0204080198cf302814000604011cb0702014000404011c15102a1400860400429df0201c020404000f59d00814000600), (58, 74, 2, 27, 11, 18, 0xf92563bc42150011807d83f6bb04114001408f50008ac4155001500fcc26caf14014000409e649a56c4a8700a181791702b514114001409e3e217a44a85002181786433bf14054004409ddc4935c124500058236af394d0485c024608d275be5c4207008180728459951085c024601c8fc33a45285002182722588570291c021604c404db0c52070081827033573b10454004403be6a2fbc08450005012f39e9e11061c028403b23fc10c0a170091812c850c970215c025404a9fd423442050001806a72b30b12154005405a541d0ec428500218068845257009540056009d2672e4085500150126462a011005c02440190c7425c125700958223e32549121140014058d8d27dc5247008582631a858f04854004608874837b4108700a10220d5f32304a1400860882106a044907008101de57f96f1421c0284097388514c48150011015c7762350295c0256046b53291410470085021ac413a70481c0206086b0c485412050001821a6e3b4d1205c02440568b3f14c4a0500018159f961571055c025403655b8564024700858018d8f4a312414000407633c53dc4045000500588ac01d105140014035fa4cbd44915001101d720ce291021c028401576cecc4488700a10155c0f6590405c02440854b74f9c520500018254d432df126140084074f18d48c0815001101134e1db90211c021404481e02440817009101118e38d91201c0204054515886c4847008501507a6d9902854004604), (64, 77, 2, 20, 3, 26, 0xfc659d450054008aa0173edd7f8820a00455022f9a9954c101002288116aecfa2e00a00111402b4c03ce512948152b02da4ce6f00a4a0045482657d7c34c011002288052865ec18290803942098e833a0e149401ca904c446cb0d8a4200e5182621d6d5e04950022a00f057d248e212902a56017d992d1112548152a03bce6a4350a4200450825d9be8fd45250072ac12de27f172080001104086955634714848152304b42cc70d082a0045400d9d09790c5050022a812c9839226282003914096469989e4050008882130dc4dd8894a00e5581586b2be2c4852054a80abe25c4ca280003904095e7f596d004000882012d61e04e8a5000e61825666e95a452100228c12ada031a4090803942085608e3ff0294008ab022ad701d08a4800e45825551748dc4152054a806aa4cf08a20a102a140353f66ed91054008aa01a89aed7a884240a9180544a7252050800730012a19dfc7829280285209502831a714000140204a7b6bcb50a5000e608253b8f922c5250022ac129c4fc1a4280102a00094dc9feec14048152004a55f30de884a00a158052aa2313c0a52054ac0894df2ece24280395405496d142a4414008a824248bd1408a4a40a958252133f9cc4a50050ac0a8f7d5e0428400288009472e405e1414008a804a3674b838a1000e610251af6c17452420542c128d569d72282001114094691ea0c448401ca124222fc84a880a40a9500510161f484850022a00a86ac79ca090803946084302ce9f10900088b00a15c9f408a0200a110250ad3a2b84210072840285535fe6282902a5409423f07d20494008a904211cd697020200e5002107752a441252054ac1082107b5a28200281409), (64, 76, 2, 21, 5, 24, 0xf86d2b5244140305048ef9c7f9014948325209ec89413310148325401eba58b5b14900301609eab2167f14a08328609dcf5154f04148325408cf1c2baa14148325009cc8559ac14108321009cc6daf3b14108321409c021c73114908321609bb32021514800300609adf6289910a08328601ad7767e300548325402a53f4de4141403050099d3b6bcd005083214029a08fea24484030424899a47729109003016018b5dab2b025083214068b109547109083216018abd101b10a003086018735c0b51294832560584cbf4be10508321003780784950014832540077d7d62914a0030860977579bd312140305405773787944494030524876f1c17a1250030100773434975140403044096eefc416121400050056e819e30149403052096d32e4bc14900301209693484c4125400050076825ea0710800300601675abd621400832000966102dcc1480832020964624be80490832120860b4430502548325406608dbf95140083204095cba8d55105483254035c36a951021000014045968e07c14848324209588f9cfc4404030404855e034d5040483244085526c4221420030800953ea887412600308007535ab55f1210000140550d38908125403050074ebddfc2129080212054dca338d04a083286084c4705b8129003012054aa8132b108403046014898c36a10448324003487b786300940305600486739e412a0832820547a85091049483256084738473e14a00308209467b984700948325600465b49dd02508021406462bc022140403040094481864612a003082054410c96b048083206084337944f1254030540742fa21911494030560941fc1d5212608328007), (48, 79, 2, 23, 2, 25, 0xfad857ce521007928413cb3c1b6c92a00705401f6daaab2925080610803e9b15540290801c14209c956304701500382a0858aba77d8a420134108270562033141400e0a804df1f044624a900c25007b7db8ebe524009a02413628be46202a00f25410ac232cbd404400e0a021579ef6ef292801c15209aa22581c52820595041351884e8602200f25010a80f2d3f149401e4a904ce27faf2242801c150059abc206c50500590a0132bd5c18c94a0030148164f264d6c0540268282144e451fe808802c84042869a149a49500180a00f0d242020a08013404025ec54f40129400e0a902bcb6a16e252802c852057947b5a5014003822084ec990994a0a00f254025baebe47105000e08801b684410380a802c8504265df9ae449500590a00eae54c584a5000b22082559cec85405400602821292dada3292001c1120950c23ab25280038304129c79a89ca50013420825371f2dc12a080614102a673e281252900c252054cd5a8c1011009a08084975d4594a4240b2908252a633bd121400602802a5339ff424c100c280074a468eba4a500792a40a940436b8a1000b2200252602b7dc04000e0802124a59daa292003c9120946b7738b09500382a08c8c6dfa9e028003004109157d275124480612003a159dc8c80c004d08042), (64, 80, 2, 23, 2, 27, 0xffc5c5f6212004d01601ff7b358a284004d08409ff7940de294004d08609fadfc492212102ca1601fa49e5be242002c81405f9bc834e284003c98409f9653a7a00a801c15402f83c1ee2252004d01605f7eecc0e212002c81601f746b70a250904d24605f61135ae292001c11609f581d64a210804d04601f2c797f2202904d25401edbb803a214004d08601ece330ea252803c95605ec65c85e292102ca1609eb831416292003c91609ea6dd6fe254102ca8605e0f002e220a802c85403dc298206284002c88409da8bee96252003c91605d311a5ae204004d08401d18075ba202801c15401ceefd7e6252904d25605cdc0a32a242802c85405c6770282240902ca4405c3a1e8d604a004d01406c3773dfe04a801c15406c23acb5a20a102ca1403bf624d9a212003c91601ba8a67f6200104d20401ba2619c6242801c15405ba0e2c8a208801c14403b7c36812290802c84609b4208b3e254003c98605b3d2e396200801c14401b23e2d7e24a900c25407b188f02a250102ca0605ae2998be20a004d01403ad888ca624a003c91407ad0e1d66202104d21401ab3300ce202102ca1401a7454576250804d04605a5a0003a294003c98609a557d8ee282902ca5409a5133c26290902ca4609a25b55b604a902ca54069dd88a6e24c003c984079dbaa9be250803c946059a90bc26290004d0060998317bf624a001c11407971d961e202902ca540191a808e200c104d2840290e9ccde00a001c114028e6b95ba210001c106018d978f4a242804d0540589864cea284102ca8409885b181a04a800c054068832edc2208802c8440385ee32e2280002c80409851ad64a248904d24407850a3e5a214102ca860181f66fe220a902ca540381d295ba242003c91405), (59, 81, 2, 23, 2, 27, 0x7f5f6a19892841348501ff539b80448420594280be737c722212802c85601f385d609149002680b04f50fade5894840b2858178a8035cc520209a40c13c213ce8a24a801c15407e0ed54fd149001640b04eac03f188a5000b2218271ecc7dfc4a500590ac0b8ab78d76252104d21605c464e725129480612b02e011e2828908413485016f448d684501009a088137954a18a292803c95609ba81be4714a081654304dc10c8b5885000b221806d989554c528003830c136af843ae24a802c85407b46f70cd141082690a04d9fa760a8802413491006cf41a3ec014209a4280566d921ee04a904d25406b312d153105400e0aa01d951a1eb8a104134a1026c3f280fc42520594ac035d6ebda224a100c21407ade9e865102082694200d5e980c8884a413495806af1adb14420209a40c0351896b06282002c81409a69170a3105401e4aa01d2b9affc884240b29180690ab14a450120594881345af61ba00a904d25402a264e819129001640b02ce9f42c38a0a41349502673e9a57c4a500382ac0b37878f9a282102ca140997ba3b7d149402682b04cbc0a55c895000b2218165df07a0c415209a4a8072d756296242900c2540595d17261105082690a01c95f22088a0200705102640f33a7c520005900c131cf2b89a282001c114098e56c831142000e0c204c7036820884841348580636e4b7e44140038228071b2613b2282003c914098c3478af128481652302c61577c489504134a18162a061f4c401009a088030f6636ee208904d244038758ce4d00448269220143a5d36d894a013415816166fc93449520594a80f03149af224a002c81407), (66, 79, 4, 21, 2, 27, 0x3d80db3e9101009a0809792d014d820240b29102ecfedb3b049402682b05b4aeb4d6092801c1560b23dbe171105009a0a0963748822824240b29182c6126e2f041000e08a0586b11a32052104d216070cb3f5c9120009a00495ebddb7f220a00301412b4317dab021082690a035cca866e090904d2460aae0779d1124009a0249514f72e2820a013415029d1c564904840268230539ac08ba090104d2060a6a5d1891100009a00094b379719220801340412922be1db040402682205205214ee084004d0840a321f645c128007930c1438a93a482500070618284e0d942401401642821084b8a46084102ca840a0c1bf28100500792a0840f19b1c824200f251828023b936449401642924faa290d2094004d08609f0445014124003822c13daf15438248413485827a0b38a7029402682b02e5c8e9e4892801c15249be5d7bac12500792ac1379c8741824a40b295826f0edf5844a002684124dd3a9bda094102ca8609ab93be24085209a4a80b43c67cd82504134a1826835c465042001e4c204ceb46aae082004d014099901c414105209a4a81320da884224a00f2549260f57c1b021000600a02c1a047fa052800c0560579b6c4bc104205942812d1e030582100070610258f6d5b4441401642824b0c8b380882801c150494ebe14f90280059104829ba1f5b214a00b2149150c74ead021002680a029d961236052100c216052c52df99124001802492578dbb52242007050924aaa257304a001644304930d026c800803c9404125a5e4c40a1009a08c0a449611e81500134218148835379029401e4ab028c79dbae042804d0540513839f9910800793009225052dd204a00f25490448f7781048400e0a30485b2ed12090002c80609092940010a500792a48a073cc7d220200f25012), (19, 72, 11, 14, 2, 27, 0xd1cfec5f0084816523abe9c781009481652b95984e1f001482692a817647ad001082690a7dc35fbd00a08269437ba083d3001481652a745eb001009000e08b70702fc5009401e4ab6b694f0f009401642b6318fc93009082690b5fa92a45009402682b5d77cde500a000e0c35872856700808269035611919d009002680b4e995c93008000e0834dbfee1f00a00268434c46e007009400e0ab449d36db001400e0aa410852cd0084826923), (27, 83, 2, 23, 2, 27, 0x192e80d828a42413491826740fb25f149482692b04c20d6db38890804d042487ca8ce15c421209a48c02d978251d224a013414921913eb95d14a082694304b1ee7a1ee214104d28601625ca0b0450520824a812b96adaf78a0a0104150255c9b29c7148482092304aa7f96bca092904d2560854ad74850524209a42412a71ec3e4224a0030149214994b819149400e0ab04a7d8cf3ea2109041246014d2f5295c501209a48812991d9ebf8a4a00b21582531717e87148400e0a304a3cd4ba0c29210412120946429e34410520594a8108b5b07b18a0a007055025136a94eb148402682304a22e3d5fc282902ca500944287766410500382a81088405b70892a41349501d0b564df9025082690a03204d7985624a102ca1407), (30, 81, 2, 25, 3, 26, 0x3cf2ce278802086028803caba0d5c408043018401d886d322282122850a04e6ab0485106010c06100f3498aec800008602080199cc9be4400043010401bc2751ce00a82384aa015d7c034d025410c05501aebaaf91881048a15080374a8b47c404043011401b46bcba6080021808204576465f90414914295022af506c622080860220914c013db4104043011408a3f04aaa20a82384aa01d1143639004410c05100a872e8e7892a08a10a80f3ea72fc40110470944029cedb6ee0080218082014b37bbe912109142850164ce81e68a0208e12881323a8a5c44112450a4403915a4bbe202122850a00c8975269100091428100642832ae2202086028091171b18dc0850430154048865212088402180c0244380bc9f104411c25100e16e1cb8880a08602a80303b47c7c1012450a4408), (95, 84, 2, 27, 2, 27, 0xfe70aa52280a024084409fb0ed52e252b0240a5605f6f33196292a02c485609f5eb2b4a2542034098605f060073e212201c411601ef27f5ca24a201c411407eee69e6a25430240a8605ec37587a04aa014015406ea40213a292b02c4a5609e84dc8ea242a01c415405e5fa048a282202c481409e2ecb19e0802014010408e1925a0a252a014015605e030532e082b0240a5408df7031fe280a01c414409dc69a54a250b0240a4605dbf66da2082a024085408db53b9fe280a03c494409d745a41e212300c421601d67ce33a24aa02c485407d61fe1b6090a034094608d12d4b7a2522034091605d0fa6ad2280b00c424409cfcfe4a6200a024084401cd76560e282302c4a1409ccd6f76a202a034095401ca645076210b0240a4601c9e2439e250a014014605c7b39d42282204c501409c6276b7e210201c410601c5f628b6250a024084605c59b4e2a24aa034095407c4bc31c6290a014014609c460f7762442034098405c3b7a1e225230240a1605c3a4653624a200c401407c295952a20a2024081403c0b49c22252a024085605c019e35a20aa014015403bfed6112290a02c484609be0de77a290202c480609bce28b7e292b00c425609bb167f9a210a01c414601b8fe428e2502034090605b6e8265e250203c490605b3d4774e244201c418405b2640dde252a01c415605b1b5dad6248300c420407ac5ab966042a014015404abafc93e2542014018605aac83c76214201c418601aa00012a0922014011608a974cf82202a024085401a8deaa7e290a03c494609a370bb1a24a30240a1407a2b88f0604a2014011406a212cbda29430240a8609a19ac282200a0140144019e67c33a252a02c4856059d760226250201c4106059b94896e09020140106089a125162092b0240a560899b6b17e24a202408140798ff000a208a02408440397d2d8ce282203c49140997595c02280200c400409975505be240a03409440596f1f3ae250a00c40460596b88ab6294200c4086099656c092052a01401560494b3a2ba248200c4004079496d41e25030240a0605948ee95a250202c480605939dfa9e21230240a160191508536208200c400403910c18fa24a300c42140790f1b682290300c4206098f782b1620aa0340954038e635af6282201c4114098db421ae208b0240a44038cbb69fa24c300c4284078bafe076280a0340944098b886d56252203c4916058a92335609230240a160888f53eae242a02408540588f48d9e20a30240a140386b0c66624430240a840586189dd6280202c48040983ff3212240a014014405836c5dc6212a034095601835fed2e0922034091608829fc6ca21030240a0601825d573a2142024088601812087fa0942014018608810c87aa282a014015409), (54, 85, 2, 27, 2, 27, 0x3e449885c495403882a80fee0256aa20a0211011403f09f0f8d149100e208b04f44759948a4a805005582790ebbe245214098a08c13b142257e292a034095609d7c7dadb1485012042304e9b626e2884880310058074da617f4525404810ac13a3bbc916254202c488605cc783445129100e208b02e5167bc08822084405100f281048cc505601884a813936574ba2122014011601c9944af7005410880aa016389b9718a02c0902910271b7bbd045246098a42c1389b65a3a0028211015400c2a50bff101500a00aa00e0a97333884a80310158070131ae79105042202a0917ac19fca252300c421605bb0422df1295806212b02dcfb965b894a80d0255816cca35e0c410042202080763113b0a252a03c495605b0685629142101e24c204d6c43d418a428031011826b0073f64505403882a813511a0f0e210a014014601a8554c8314a1806214304d2c7bbd78948803100581692779bf45284098a10c1348e4abee294203c498609a3489cd1040410880a20450cb48748a50c0b12a1826859cab9c4a44028022c0b41215c7e292203c4916099fedd7d31221806214202cf66594b800808440450026abc3494485601884a80b303a6346284201c41840993e80863149100a008b04c9b412958850c0902a18063d3e00f44a14038828c0b1e21f66a254201c4186058c137d43041500a00aa0445a3782e8a42807105182628a3ad940140422022805127c3dfe294202c48860987d0397d048500a00a30441cde78d8a0a80902150260bdfc0245080422030813012295c2250a034094605), (87, 82, 2, 27, 5, 24, 0x3e642c13c504049101409eb701a931015030415007a6da4994418049108403e93b0f2f1411030405027986221d450540c105409e4c6bd7312618304a101f7e2f96ac50840c108409cf24399b129583049581734c9f42441860c128403c70e47d114118304850270d62987c408049108401bee71c89005492449500aedd4d68c40460c121401bb62ded30014924495002dd7a3d2440440c101401b49998611291830485816cfb3ea9c415249125403b2e267091401030401026c6f9b43450860c128409b0d94f8f005092448500abd9044b1105041005048aca540831400924481026ab0747c440840c108401a9b099fb1095030415806a2f652f44a540c1056059d602425041012440502263d9c02449840c10840793c4205b10218304a10063eedf6e452540c1056098d2b8aab105583049500e3148431452160c12460986a9622704950304158220e815834094249121406808986430410924485021fc29997c0040491014007e69ce4b106103042100deefc1ae440140c10440178bf08951010124405005d4fc963c40504910540172c0863f1491830485825c999103450124912440972641c1b1405030411025c888a4044850491054056d0b80491481830481825b32d3a6c52040c1006096b7cff2112a18304a1815aad77cec40160c124401674777eb105103040500d994d6d6c48440c101405653f530b02549244950199102de6c4a440c10160563888d3b10010304010058bd42fc450804910840962c1aa9910009244810057ea6597c48840c1084055f62c8a314018304810257cde72744982410284075c9c3acb105012440500d703d444448540c1054055bfe888514001244010256fc4e02c4882410284055a91ac2f0404924491021680fc3d410440c101408586702a244101040041216179c6cc09424102140656903bc9105092448500d598dc71449504100540756605e31121490409501557c2a65449424912140752675dba40501040041094691f2b440060c1204015150eef7125103040501d3ec0ab240042491214004e1aeacb10a18304a180535b05f6c4952410254074c675b3f12149244950153031f7f449460c1214074c0761ed105183048500d2ecdd7144150491054034b7d5dd914209244a10252c4199340952410254064a50d26444101244041211a26b17c49160c12440745f56f1b14041244110251278020441160c12440343f50af902101244050110e9bd48c498249128407), (35, 76, 2, 27, 11, 18, 0xfa4e6bf110954005601d03d612f10914001601ca1b64bd1091c021601bf3a0c9d14854004609b283c37d00454004402a576ac5b1485c024609a35eb62712954005605a257d8f51295c025605a0064fcf1095c0256019debc24b1291c0216059cbc016d00514001402965426cf1015c0254018a968faf1041c020403890cfcf51495c025609791034a91415c0254096f7b1159149140016096e5ac63f0415c02540863fac4f5049540056086208e471129140016056191a9bb041540054085b4f968d1405c0244095a620e1112854004605587f4b79101540054015823e1611045c02440352d4a8371245c024407521c9d7d04054004408512b686510a1c0286014ba0a76110414000403496204111255c02540748524037004140004024371690114214008409428949eb04214008408412c17d11255400540740e244a114a1c0286094089996710214008401), (24, 87, 2, 27, 2, 27, 0x91ce9875c505248224a812d8806f748a084904485025a422b1191014920892a00b35ca8ee2292a03c4956095eeddf0b4525401880ac12ba552fd88a42c090291825746d73d91055022082a01ae10d5066292a01c4156095a3bb48245284038830c12ad1ec641820a08440550214866e8ab1495026282b04a6be44e76292a0040056094b3823fd4405608824a80294c084f08a4280d0251825275769ff1045022082201a3c0885ae0828241105408461d87d6c525604814ac128c059a51880849044850051530d057105410880aa01a2923d54e00aa0040054024274c8414505048220a812837a46d38a0ac1104950250540e5d50414920892a0420762d522282b0240a5409)],
  [(31, 64, 2, 12, 5, 22, 0xfd104a1d00881c12f334172e00181e08e95dbbc640981e19de76a9e640111a89d36af3f200981e18b703d8f240091e81b44aba7a40181e098fca269240901a198ba5166e00991e98744930b540081c036e005a5a40991e996cf2747800991c986a0e776200191e8868d4f95900081c02657b05c240191e8956b3e47640881e11541b14e200111a8850521b4200811a903f28f17e40911a993c550cc440091c8134d102cd00891c922dd2037e00911a982c36614940891c93273f98ba40891e9125e579d140091c8317ab865a40801a110d36135e40811a910ccfa7b940881c13068e130900091c820354856600891e9002afe66200091e80), (77, 68, 2, 16, 5, 22, 0xfca07cdd400034803f98758a840c926491f4b89cfa409934e99ed17213e009834e18e9d51170410818c01e2c614ea409124299dfd3223a408034a11d54826c1408924493d29cb99a401034a09cc143cfc409934c99c707c7da410918e81c553a9de408934e91bbc6d3e2411118a89b3ade2a6409034a19b33b7dad008134892b0f0a9e2001834e08af8511f1400834c03a53bcaa9410918c839b254972011818e089701a89c410918c8195a4e9dd000834c0294e21e2d4009244839070d50c4110188098c65635d410818c038ab7bf0d408934c9389f830bd00c926492834b1932001934e88815c03c6010818e007bb6c5d2001034a0875917a25404126083660c795e011918e885f05982e0009246805e4424304041260815d2020a44111188895b4aa765408834c13586bec4a00812429057fcb599008034812566f87be008134a905282c1dd00092448251babe96011118a884eada072411818e094e4e44d6401834e094d000501400934c834afaf19541001880349b52aee410818e0148b92da6009934e9847a9fa09404926483477cc89e400934e814260253c4049264813fcb93e2409834e193f7238d90101188823d8dddc10089244923d111135010818c023b4f5ae440c12609139d27a0a408834e1137c1fcba00992469837784b3a4009246813577eac140c9264932e6b2f410049264822e608fae0089246902c84c4f50100188022839997600912429823389382000934e8019599de900013488218808062001924688186423fa001124288143f466d40c12609312d36241000934c821108a15a411018a090f56000a008934e900f008cc94001348830dd83139008934c920c0aee98400934c810b9bcc8941011888307ac510a010918e8004d35eb1010918c82023a2d8d000034802), (85, 70, 2, 18, 5, 22, 0x3f7c73f411064a4489f7ff03d9440118220fb710cbf4100460882ecb695504410182027a5c7b104140468882e936379d448018204fa279b814140068802d51864d9448818304f43bbe0e51000e4803ccfa1e49448118224f29d899f91244a4299c4c38d05040918320b0957d5791220e4e11b78599e64408393806cc3fe1f4122060c12b1160e504488393046b13777d5102060c03abd96fc44489393246abdaeec51024a4483aaeb34744449299206a87a30841304a6092a685bd69048039204a9933ea751224a4493a40b7a58448929124685dde3a11204e48919f3caadd440939320e600be6641220e4c1296889eed440139220e5914fb951304a609395a8283d040929120a365440f4142068c028b115352440818380621f02d5510006080387e154764409291a0611d98fe41124a6482833149390441298209ffc509e9120460a917f1e7f2905091a3209f94411e1126060c197bb4e241440918320dedec0a491200e4a117898813845091a3205d9bb584112046089176032ea84408393005d04e5d841024e4c82734a1f51448039204dc36cf4f1106060c09709598184409183205c2061b24102060c026ba7db71440839300da72f9c341020e4c02699c320545011a220d97661b251204a409363f943aa441039282579fe65a9106060e095cc13765048129024961680a551324a649354ad34224411290a25410b19d41324a6492503e1884441039202533b7670112006081149d4fd444409393205262b8af1102060c0146eee31104892912490abb88e11024a448134f93c804488183044ceaeee511324a649132894a4945001a200cc2d2e0741204e48922e36f6284499393264b3d767741204608922cebff7844891832449b036091126460c99236d24e50401290208706ab679102460e811495aff044c12982443afebff41200608120c9a3878441839302429c4f0191024e4e810a25bc804481290244258ecc451124a6483094e1eb64488183844192b1c511260e4c1904a8bc9644183938240596aa911200e4811), (40, 67, 5, 15, 5, 22, 0xf6d5471e0411392a3ed2f714c0a3034707c5c849981060e4e0e123c13802480c103be5fef620491182a776396f3809223044ea39a25281064e4e8cf9e4445020c0c1c199162bba05191a3a32ad847c40820725064fc256381224e4e947f1294102840d1c084f508a404992912703e6880c081272741d3761f781064a468b856efd602448c1926d15f83a0489183a4cd93ad5409207250d818fb6e0126460c9add1338702848d1d05b7968f4049818306b0f3ff7c08323074560405fc81024a4682511aa5f024094852423b56920491392a680a3d30409307270cefe535781204e4a91de37dd702888d15136d1aef204101828269de2394082252144c7099da8104460a89407e20502408c1522508d67e0499393a63f7b85cc09323074c5faf27481224a4690ba870d50248948531659a3d20409183a0252d743c09303070c24fce938144068a081d86863024c948d3), (50, 64, 2, 16, 9, 18, 0xee63cd8640090681eb2f35c240810291d472f81040190489d1ed0f22410886019b7ac6b040c120918c7884304148a40177ad3660400904816f6009e4409904996a77b48800c92490596fc0ca00890690505f5d714140a0034d2cb11c404924814b8b37ed0141a0824938b96940492483485e26090089049243f76f6a01198688428b7db14041208337086d3e4019068936c4871c001904883444c83d0149a48232b5ef414141a0832f0af8bd400904832e8ffa5e01188608292ac14940c9249328f2dbd540890493280b88a94101808324cbbf76009906981f11b3590148a4021eef871d410984831ea2708d40c120931e1b2666009102981d69905c011984881d151d89010180821d0015ee408906911a529e610109848213c8ebd10049248213b8c71c41098481124a3bca010986801026ec7e001906880efa802e409906990d3e67344149a4810c9daf2c00c120900aac8501000904820a81edf20009068009dcfc5500c9249208281c300099049807859d264109868105945fbd4149a48302abc3f14100800301d039154148a403), (53, 66, 2, 18, 9, 18, 0x3ec865ed51506a083f55a98790501a020bd567fe3414268482eadc9a0d04498920b9c2fa72112660499e66e42fa440981a07963493b912660699de5cd5b14548a900f6b3e40b914228601d89693d14501a020f5e18659113062091cbbfc18104098120ad678caa111262481aa70f1a844c98924698a708d812460298a553ecd50548a900a9171f1541506a082a422b8594509a120e73c76125110620839bf2ff0804c188242658185951326249395b62f9d4500a000e4e351d71106604899352fcec440981205ff128d30132624907cf320a90540a8009f1281469122606917573e3144549a9205ce6ab330126604986cab1f5a441981a25aaf5b1511522a4016781fe780518a1021842b74f112260491595eeef10441882093e8cbaa8120602904f76ce3a049981a613a415230146684884bfb9f5544098120d20a42a681066068841411260048981240f83e5d28146286083785b59e048981a40c4a19ae1142684812c26610e448180a4492ebcf351126248318cdf392449180a6463354ed51526a48317cff13e040981a005e277cd814668688151d83c00419812204d9f16a9142686810eb0a1154540a800c13f0e79814268680), (35, 69, 2, 18, 5, 19, 0x4eda44ea411802102672ee010e2489c913325c5149d0064c4c898f0ae4b6882272444c75e1cc7c4111822262d78b5422888d11130f6a94f1146068c098774d8c78a2034404c2cc4125c10802100610797ebe00c881912fe29818314602840974bb05b489223044cb5e3d856c5191a3225a5f188fa08c891912cc91cedd14642848961841c01811220648af46eda7449129026575dbcf4204c881932b06eae77046408489518f995909225204c28a5ca42c49929126543ab243a2840508029e0845631240608194dcdd0b1883272644a6b0b40c848118224134cb027a0489891329909b6410240c48194bba7ae0888253040a58cbb63c01131222525ee352e08c0918128d762219106460c8945b82107882252044a22fa1c54490392065038781de06480492280c5a177142068c01), (77, 72, 2, 18, 5, 22, 0xb8bba06c9124060a19b196baa091244e4a99ab850ff39146068e09a5ed60329146468e89a3dd9cdd91240e4a199f4b8cc89144068a099e8ed9739144468a8996fe3f0d9124460a9985f26d509104460a8985eaa157914642868983c3879191044e4a89815120d190244c4a997bf9dd3e91264a46997b34843890044c4a897b217a4a91064e4e8971cdb74b90064c4e89711338839106460e896eff00a691460286096e9ee53d51220e4c136e19875c91224e4e916dfbecd590204842916d44137d514202840369590ada4122460c92688bd46180240c4a18664d3c4b9126060e1966385d0a5142068c036568b8a59046448e89647ed5cb90044842896386a04151204e4893634d585451004a40836322a5c391264e4e996275825f91204e4a915e161f2850420084035ceff4b450204c48935c6664a890020c4e015aeebac951104a60835a709fb691260e4e1959d7db625130422093593001115122460c9358eee0dd413042209256d20d27904600860954da175690204c4a91547e58f98020400290547cc6519002040e01535fde038124060a185170c271902648469950f956889046408689507c5ed391224a46914fb81a5941224204924f073fbd9142468e814ea3b9d79004040a094e5872dc40220c4c124dccaca251224e4c934c37b8bc41324224924bab216490244002994b90b08391064a46894ab4d4e740420084024a815b9480244c4a984a6dda3941000e48024a4b56be9126460e994a3f1e0741224e4c9249d377ce90224846914949f70441420284024881c60e41004e4882478df30b5142468c83478275da50200c4813474ce31c415242a4824739cdb69142068e0145e72c314140028002458001429006484689456330465122420493454807499120060a1144fafcea410006080244da9fdc91204a42914432e5b19122460e91429a125d9104060a09403e434580044c4a88), (65, 74, 2, 22, 2, 24, 0x3f9b01f481820602091fd9f57982240188900be73910602002608802f8ec73582041989300bceea29a09004624012f385d20a2a4018a900fb7bb3820a100628402ecebcd2a0441981304f852a2ae88106624c03d5fe46c82040188100b2fef50688820622083cbd4c00208c01821027282458a81804606013c509dd680800182000b138eeba09800622012bd7441a80a08182820adef4b6e82120608483b58b3daa2408988224ec4a1b620a002628802b013942a2449189124eb162ada818006020139e793a5a0049181120e756e3e20110060041299eb595a2409989224e5b04dfa88122620c83960c6f922481189006653e2ae20212060848292b711aa0040180100e4983eee891006204138b2a97f82441189104a18eaa6609106624c128603c35802401809009f8052de0a80062a0027750f38a2600188804dd914e1e090066248126f21578800481801209b293c04890026208116a3583e80808182020986ee36a089046264025c993a4a2240188900d633cb768a10062840351cb843a2a0818a820d323221e82102608c034c6c3bb826081888249251a2568a022628883423c23aa0a08182820d088baa20900262081241ed6f8a2248188920cfeabc9e009206024823c249c182a4018a9008e0b3e0281102600c1334fbee9822001888008cdaab520000260080230b5182a0208180820cb792dc88192060249125f140b80009981220896e44da08102620c0223907d7a0241181900c681817489122620c9118c1501a2040988300c5409b1209102620c12149e0d4a0048180120c484c064892026208190915bea80a48182920800c2f0601002600812), (74, 76, 2, 22, 2, 24, 0xfca7164c89102620c11fc53e4d680126604c83fa85857281004604013f106c12e89104624413efa37fa889120620491ef4df69681900602413ec649b8682002608803eb76a14a81022600893e5d1836689102620c13dcca1ee280924606483db3038c680004604003d41626da89122620c93d3cca54a8280060a003cdb9a49a80824606083c8b3e7d281100600413c6c28e0089100620411c2658e0a80122600c83bb23bc2689006624813b7db558e88006624803b1cfb43c89900622411b10c229a89920622493b09f31708a300628409a936882288124624483a629a8fa81122600c93a57facc488300620409a0b71790883206204899e0eb28e8a1206284839dec79f2899046264139d7ed18a819046064139a49a24280106604c03998c73c689126624c9397beb6a688804626003966a3e2c8922462409992e2659e820006080039169bc468290060a40390be1c34823206084898ca4faba890026208138c0330668a80062a00389cec15e81126604c9388a0b156889046264038895f37e82122608c838571dab28812062048384bd97668010460440384b95ac28a122628c8384a98fde8202060808383782fde8810062040382a91fc68a002628803818506ba890246240937d3264d48a32062848976f2075c89324624499744f221e8092060248370c1c7d28a0206280836ef06408892226208996d24d2de811046044136842bd5a8a102628c03658de8aa888006220036464526889302620c195f4528b28a92062a4835dda0dde808006020035bdbc138893006204195b5438ba8292060a4835ae1a7c680102600c03578461e48932062049952aabda089304624419526ea4dc898006220114ffac33e808046060034e8b7602899006224134956a2ca80900602403489aa3568900462401346bf7a8a82100608403459c3e5689820622093457180ba8980462601344b8d1ca8a0006280034259a2a688126624c83), (51, 75, 3, 21, 2, 24, 0x1f266934c0024cc09907c4afa9482008988220f402c00d05000314001e7a5184e08120620483caf3fc0c12048c48127869f0a680048980320ef386c0b05081314601d8f698d601920602493b1096d9c13248c4c927591109280409181024e9d51f9100c10301049d09a8a5209122620c939b3b775414240c509070dfac9682449189124e070887f00081300601be0eeba20892462648374186c8401208c0c806be4b69d82648188924d642e9f900003302401a3db16ea01102600c134511898c03208c0c82689eaf6a80a40182900cfbc7fbf000113004419d6087e20a122628c8327b784ac04200c1080642b396280041981300c73702d7040013104018c6586020912062049315f3c1b404044c111061d01b3d82001189000c11f91d100890300249821b85620180060201302551ae410048c48105dfe2dd980041181100b9a9d1e1040033124016e192f8a08804626002db7323dc10208c48805abe617882641189904b0e94da7008133024495fe98eb60a022628882b66acc4413200c44825604186182440188104abe10e4d00882302209554bbe6608820622082a2b9115c10244c4190538f7a3180441981304a4204cab0140030500146dce6b6001006004028855ac3c13008c4c0250f9a93782049189120a0bb281500c80301209), (78, 77, 2, 22, 2, 25, 0x3fca8931912600c40c33ecaddc4c81024604291f5484c6a41090304340f9ada561220c01881827cae3e6f902440c00533e3d766ec88100620601f05975b644112312144f3f1223d220c91891a27663965f900648c08d13aeb5d04c82320608689cddb7a5e40883302708e5f88e1b204481801a472ece66d902008c08423931e8d8488124624681c8743f724091230214ce2b59983224091890a46ffc8bb6912608c48c337f6485cc81306604e19bc84059640093302740dc8ac945200c11811826cf67b06910404c414135978872c80222600a89abbbe92e41091304740d474d3eb224099892a4699930f4900200c00c033f91105488226624a899add426640893302748cd2044d12288898a2a26624c24b90240cc094332982de2489302620e1993d1f5fa44091310740c9d33f75204c81801a664a7de73912240c40d231a0c4a6c8a102628e018a3f2c2240190300344c319b5672284818a1a06130966a910408c484130918f37482202608a097e0c0fa640181300704be93c6a1208409823805d09c89191224cc49d22e217c87481020600291703b602e44181310704b7f405f5224401881845bde7c73912644c41d32db2d1d6c81002600a116d72ba2245091314740b64057d9224009882845a982564902000c00422cf7dc55c89122620e9166abbeea40092302340b3223179204491811a4597eb57590244cc09532cbed978482222608a89659dced64499231234cb238384b224899892a65655062f904604c11c12b209c4c4813046046195325359e40081300700a62d9d69204c99813a652e7a786902204c01c228cc6254c80202600a09447ae61644081310700a0663203200481801a04f60de8f900408c08412795b2b9c8110060061136cdd36a4491231214c97105799200c89803a248628abb900600c00c1237931d5488222620a891915a4b2440903103408aa749a7200489803a0451eeb69904644c11d121abc2acc89102620e11097e5bee4491131054c8330f80f220499893a04137d02e912248c48d2205feb60c81324604699), (76, 74, 5, 19, 2, 25, 0xfcf2d98e0081030014bf29f256800404c0141f55b72de00190300347cbde250812408c4843ef969bd20481331254bb9c9e5080224cc09d2e9756a3e0089130074b8258571812644c41d3d7e5b57a0498331270f4a16dcd802448c0853cc33a72e0109130474330abf22814200c50c0cae9f7ce041123121472727525804604c11c1c8c8280e0089230234b090b410800240c00d0c11562c204193312747031435380064cc09d1baf419ea04191310746eaf765a810608c48c1b7ed0f6a0498031030ec1646ff802404c0143acdf25960490331250eb0fd887804240c10d0a949578e04091310742a407dac804600c10c1a3f652ee0409031034283bc26c81024cc49d0a0aacb3a0090030010e713ecaa810640c40d1982c2ca6041033125065e282a3802608c08c390db718a00182302306297a993812640c40d387dea5ee041813107061e26f6d800644c01d1868521360098130070dfcee03b81264cc49d37c1befe205090314341e5008e880260cc09c374fbe0ae04812312149cd8ce6f810600c40c17266330a0099030034dc16a72a802648c08d36ffb0b260498231230da462542800444c015167d3bbf20489231234994b0b1b80244cc095362b697a20018330270583b4cf5810648c48d159d251de011013045054b1bd70812440c40534cd101320018130070501eae16810408c48413d13a15a04890310348f35cee1800648c08d13a06592e0099330274cc608bf4800244c01d02906ff36051803143048a89726810404c41411c73211e0498131070c6d7ac23800448c085119cfd7c20499231234c625970f800408c084116e1108a0090230210c5649370800600c00c1118b0a36040923123403e2c7d681060cc49c10e1131ea051903143442cb1d5e800248c08d00ada02ba0091030014c263757c804640c10d108b6e47e0098030030c1ecbad4802240c00d207abb0ea01111304544133429180024cc09d0), (65, 77, 2, 24, 2, 25, 0x1fafd0baa0a08280a083fb42c1a900649d02344f8ce274a01120a00124bba46365454005054007d5a8f7d220c83a20689e93a89541200141000973e5cbb489224e890a679ecfe96448127448523c7802fe824082820092ddf511b4032014012096eb5552480304a01182773a9a264010050004139aa1816a00412804403c9a28fa904241404340de0d488a09900a08904ae04c99d44c02504c0276fee632a22002822003b25e8f64122014102095784a28281924a01924eba63f0e408107400523582d09ea02402802403a81da98914441d14144d323146280100a00100e8997506400907400d0344c3d2f2088028082099ffc009501249403241ce6ec18289800e88804e7321482411907410d1337c21baa24403a204139b8d60f914241414340c80f6aac81220a000a662d5914544412504c1071681f84a24492824493872636f910601d10304bd012d7a88024a09020de10433e410105010502efa3bc1220492824681763b60f912601d1030cb8833e3a89800a08804da403c1a400925008d02cdf48c8a080028080036424ed2514201414201abef6a6282020a02020d5e33e2d440005040006a3af008a0a00280a0035189617912009d12108a506f32c81304a0118652567d52450907450d0291f562c80440280041242e6346914001414100a15b4e1489020a080a45033f08a4480250484227d7f698a2a40282a403384c52e910241d103409871209282120a02120cbc9df2940c8050048265805442a06483a0249328682724032414012491425491482020e820a049c8701944800504002636793b0a2001282400314b7e9a502201400209846444ba80904a01900c061dbea441025048412002661d204002800211), (43, 79, 2, 24, 2, 25, 0x1f4141d4c82200e820827ab11791902609d0230cedc0a66b208003a08201d9b840b2408907400d2393f6139c8a320e8a1a271a3df0f910449d12144dcfb2cfca06083a02093b90f5872401127408513718e270488324e891a26d109d24912209d12308da029e1f200403a00601b3f10c1e4011074005136619ca3c89324e891a66c03732a512001d10009d41aeb85220403a206019e8ca6a245000745040336f553e289900e88904e6cbcf1f904241d04340cd6d73bea04403a0041399573716441827448c132e77c6c481324e811a665627df4910401d10104c6815f0f228803a282098cf3af914089074009271836335482220e820a2615719d4513041d11049be7d8ff7224c83a206997ae0ccee448807440c22e9bf607c81124e811a45bb8ea82912249d12348b5b09f4b200493a0468169be41fa450107450502cf23a00489120e881a457e32ad5900601d00304af372c6d204403a00611587436d6408007400422a7b466ec89204e8908654e307be900641d00344a7e1d504a04083a000934f6db99d40800740002693e6064c81004e810845264c26e503201d01209a4c607b5200c13a04609), (72, 78, 2, 24, 3, 24, 0xfb2f723e441826091827ea4b6a3514041828083f727a1e944c80608904fdc65e24912641820699f6aa2afd44492609920fd353e01912441820299f131549944482609900fc081be6902401800219caf0814d41080602100f147683e512041820093bfc1b87a449006080866f56268e912201820611b7058d8144402609800ecdea839510241820483ad98a3e941480602900e9f0d345511201822403a782259244082609180686300ff910401820209a0f382f540892601124e830ebb85122098244139ce1442e4408060818066a048f090224180069195b7af16448906081a464e8178490444180828992c32c8a408106000a46481dc3e51424182848390453812400906001a063cac5d24130418220928ee829ba4510060a082621a9fdc503209806413853f688a408026010846148ccc590020980460184edcfa6401106000a260c893e9912409824219818f24ed44082609100e04da09451400182800380d75556409126010a6603119155132098264137bf478b2401906001a25ef434079120498242917aafc006440906081a05e3dc59191404182828178b5f88540c90600924dd3edce590264180069973c35c4944c92609924dc1dec355012418024836db1c10e441906081a25a2aa346910441820289659d172a4008060018058f6d9b65100418200836394b066408126010a455b724d791044982428955c7478644800608084553fe5275110418220835431cb46401806001825509400e90260180061952c2ae9140890600124d46f60c850024180048351221d6944080608100d40c01404122418204924ed1ae964511060a0a2534a77065002498044834c46727144092609120d2ebc8d950220980441349dc1aa504c906089249205a82a513241822493472afde104c0060880491c899c4904001808201440958624010260108250c91a6d51224182049341b211d141490602920d04ad923512009824013), (80, 76, 5, 21, 2, 25, 0xfff0b026051907450d1f1aa6cc604112504851f01dce8a04812744852e42111aa049927448d3db465f8a051905050d1c279d3aa04910504053b7e5550605100505041b6a3c77e00900740043b18d3306049925048d3abfb106a00100740041ab30bc0a008927408d2913baf8e041007440418eb1e6c6001105000518b177be2001907400d18859740e01100501041877fa54a049905040d38101249e009125008537f3c3b0e009927408d37e700a02041107440517d5e132e049825048c37d29c9e6049807440c378c8e7ee048905040d278789e3a0011250085174694eb20511050505170fd3d6a008125008526d5f65d6009107400536bff542a0090250084369b31cb2009807400c366f0eb22008925008d265f22ec6048927448d262c4f9fa00102740841629d0012051807450c1611984d6041825048c15d7337d6049907440d35cc8de3e04910744053595e9932041907440d15796b9ba00910500053573d5b7a048907440d2539bb11604812504852538d5a06009827408c3530e2aaa001927408d14f2ea0f6008905000d24ee023be011007410414a2030ca011907410d148a4668e009925008d347c4490a01110501051468e9e22008105000524470b516041025048414304b736001807400c141cc4782001005000414192038a001825008c1417cded60411050405141735a1e008907400d2385aae3e001805000c138033dc2009825008c33760c82604902744843349da38e0090050004332372aba009905000d331b815fe011905010d12f5f0476001925008d129bc066e049827448c326ec6e4a049805040c31e616226009907400d31d8a5a4a041805040c11ca00232048925048d21a54031a0491250485318eb282e00902740843171834fa001905000d1171148d6051805050c116c3404e011805010c11626be86041827448c116027a9e0011074005114381172051007450410f262a02009805000c30e3f076a0111074105107fe22ba011807410c107b3164e001827408c106ee6de2041807440c102d1c90e0511074505100a333fe04810504052), (21, 72, 9, 17, 2, 25, 0xd0317e32050805050cc6ee77fe0500074504bab54e52010807410cb7bb7bf60500050504b6418cde050905050da97899f2040905040d9dfef392040927448d93dd85a6000907400d82ebc95e010007410476fa7ee2050105050570f9d202010907410d4e6a071a010105010545f1aac2000925008d412a64b6010107410535369cde010005010427c9d0f2040907440d1f1ebf52050907450d120b3902000927408d09b367de010805010c07e7531a010905010d0047136a000905000d), (89, 78, 2, 22, 2, 25, 0x3eede37a209026624892f9ea6bb8a2209189820fe76ac68489022620a91f8b01a5aa0649181924fded0971c89220620299f6e6d44f224c19893867d747fce489326624e99f3ca76ec80649181924bbf96ea8281006604813ec176e4e204889802267914d34548a302628e09e3923e69220c19893827899d56cc89006624a11d7a98942a0409181024f5c21be1a88924626483d29442a12248018808673e0248e288026624883cde8995480449981324b2beb1c0c80104604601ca71c3fe82449989324b27572f0a89120620493c964e7ab220c118918271a57ffba81002600813c5fb0aad2204118918070fdd209481006604a11c3d6f63e80848982320b0be4195481122600e91bfc7a8ce80449181124afd52d29209824626092bd906ba4226081888246f3a16f8a81026604893bc7a330a80448980324ae97263c481026604a91b89fd726a2008988220ed52fa57a00924606482b3b031ca204c81801266cd76cf2c89000620211b3317939208c01821826c8f9d64a0a020628082b1cfa6252284018a1806c1198be488322620e89afde347aa2609189824ebc3cd90c89204624219ab5f190282009989220a9d9dacf480106604e01a679ab9e82a4818a920a9396d4ea80006604803a3bdc6ff2288098a28267f15e982010226008929f66d4be82408988224a7cba59b2800246040839e99039d204801800866764ddffa010066048129d233377220c81881a266eef4cb281124604493999ce379200891810a26666192128992462649399859a48a0609181824e655817dc8120460421997bb7a24a0648180924e5ead096c80306604e09960ad7eea0448180124e52e1d22a80022600883949214192044118118464d62551c8130060061992d48d7682209189820a4afb59728202260888392626310a0009981220e4334357889920622491907e901e224c8988326641c693d2800026008038f853ed5224c81881a663c44f61c88206624a098ed4921720840182180638212c2a818206020938ddce73b224411891846377076c2880046240038daa72e22240898822462e2559f202102608c028a6c1e90200c81801226269b6fac88106624e01859936c082a0818a820a147958520892062248284f97ff12240118908460bff0792881046244038255b94c80049181120a0887cb2208126624c8281ac40c8a2000988200e03e8845c81202600a19), (25, 75, 5, 19, 2, 25, 0x7ce434ea814604c51c1eedb35ab0284098a381c3ec236a04113312547854ceecc00206604a0ed11d1b4812444c4153d4b3f203024899892a76ce3494200113302546c4a3d0640922462429d74646a0802644c01d3adb32683004889802a7595293a60490031010e988e5e5402322608e8d20338f3814644c51d1a2e1002d024489883a5429e696a0090330250e7445a2340a122628e84e26abc9812040c40529bb59ed5024809882873543899e0081330254a47a09d9c0210060860481383ad81224cc49d28f45516b024089882a5157fb38e0510131450611d1133402102608e041d5f130802048c0852), (21, 79, 2, 22, 2, 25, 0x66fb15fb481222600a99c77ecb3f91064cc49d1389d0dbaf228c018a1826e3dfab364099130074cdb195462c8a322628e89b58b6ffe102644c019336515991f204089802a46b431db7245190314344d29a6f83489206624a19a50b080c90064cc09d133ed9b3c5004089802a4274fdfc1a40103302504ccd9c084a88024624083963456bb912404c41433266d439f020889882a22465ef56a44883312708c65553704890206202918c1b7fe8902604c01c33175c5c2d0288898a2a222e45c86640113302544c150c615289106624c13), (75, 82, 2, 25, 2, 25, 0x3025d730e451804828609aaadb9c4902409a8108665a7e6dfa451806a28609889d1b54912441a880a661501c23e049126a24298834837d1902449a810a660b8ecd52009126a04298801345679126492091a65f75787b2041126a24288785daf01900409a810825dad7fdd144c124826093736663ac9126092091865cc7c8c26448106a202917170c49e8106492091a21ba1116124508048286016dc76cfd513241a88924db13d120e409006a00219668ff1e3912601208186593fbe5b6450806a286016415b0d2900209a8118058c87a9e5448106a2009360edd93f91220920918458168aab64090248042195de60122912609a89186576d70b424118048086095ca57cfb8124012080861724db08a4519048286895c5a54b6904201a82180570441132401006a00209580b3ce1513041208824d5531459a409806a0061954f6b6f7512049209024d513b5436041926a246885444d0d7802049a810a414dba8449448906a204935304aecc9124492090a654bfd77aa441026a242095228d2fd910209a89180548988bae050806a286005223e36e9122492091a4548814faa448006a2021150f2c90a802041a800a414264b556411904808689506e9507904601a8218253ecd6a7545490482a4834e2069ff9022492011a4537298e3a4419248246894daf3ac59006492011a2532c51a02048106a202904be6e59081240920908612f263e724099248046994bb03c5690220920118452dd10da6441106a202894a5ae0bf910249a891a0526e3bfa604092482468049828bce810401208082124fefbb2401124804289484bc419912401a88086520930b36410804808601476f1e0190220120018451b3bc66145410482a08346b285658106412081a211a6febc2409106a002994525d204511241208920d1383e71600102480420844e090ae814041a8a0a010ce6ba86001126a04288430f20bd902209a81184508f558fe041026a2420841f7a42d902641a801a65079e7d52049006a202184146ea01512201208104d020a9c6a441804820609405991ca902049a810a45007c9e20000411000800)],
  [(73, 71, 2, 23, 2, 18, 0x7bec95440b00108001f345f3e61401811003cfc917448c034022079784dbd0186482410eea0a17f2a00c08881dac1e96a0419809043a4f23688280682200745e11018582684410e4f91fa11201e00811c4cb6a2c16012110037b9501dcac03422206e91ab281502004050dbb855d12b04d088a1b6bc954854034111036394b0808c10400286c0cb25a9100b00040d69a0fa33208c04891acd56ee64600a00103426c47508c124022868283f398102600410cf2dcd0f0208c048019dffafae5608a10143350a85e8a800020206594d4711580084040cade51c31200c008118b3cc5821403c1100315405a1c0831010085fdcf3489800b000483e814f9b2a016080817c51890a0611a09002f559deec8811000285e0746029184282040bb00d4a12209e0488175228ba45409011142d0dea93c0811000085842858c0182480410afd356a302016000015ea271b21608a10042adb5763448230120455b40b530582084010aa29812d300840409051900da40608200042a2df932ca8110202853654383980020004822a52cf73200c00891423c4e2856082101428293153c0c1140008503935058900b000089cdfca593209e0489135e8aa2a1402c100026abea14cc801000244bc3cdb28100f0040096d1dc1f02096040012b4126f660018011204e4566e428010200048fe9271018608201091a850670300d00801227797f2540081010244581e9c8825810204882c47881826804108de4cf25320960409117c33932240080002229770ccc4825810044517f57c01840820008a0173c33201e008910f2578b62410808022191a49a4c0230122402f40eb59804b02048058d50532a01e08881094b7b865600a101020e70063c2811020084161ae3a9900b00048824944cb0a04c08821), (92, 76, 2, 23, 2, 23, 0xf36b410202201a40881ea91c4d202a00848881e8a46d2e02201240081e17d0ae202b00148081e1588e660230c1440a1d8acd97210304540021d6b697860220c8448a1c6761c3600300140001b512c87200b00948801b12bad1602a00048081af4c742612300540081aeb3751613208c44891addefda210300d40801ada4bcee00b04948821acbb1b3e02308944881a7db545202300940881a2b7a24e1020cc44821911ab3be02209a448818a94205a00a048488218964348e0020404002185f770b6102084440018574dbc20220884488182484c5a0030494082181c3ed7610b00d48801811eb23e02a01a488818098382a10209e448017e0736620220c0440a17d8c2a9210208c448017ab93b4a112096440117ab596d61320164009179e4d15612b00d4888173eee03610a04c4882173b0cdb200209a44801722561be00a012480016d87e372003009408016b38a24210200c40801697bbe5a01201a40811670859920030c94482164e1293203209a44891619b9a4212a04c488a15f20b76e1030054000158f41c9210a0164800158936a9600200840801586bfd8601209a44811551437c20320124009153dd0e3a00a01a48801516d380e00209244001512dd09600a008488014f7ad4ee102016400014e30aea6032008408914259d01a023081440813e00d9ee12a004480813d4e03e6012088448113c52244a032088448913a7bbdde12204c408a13718e58a103085440013689aabe10a01e4880134df914a10b0054800133e4f94a0020124000131b0f2d60030c14402130af421e112084440112fe612e21020c4440212eae1e2e03201a408912e4ade52112016400112c6cf312012092440112a2e0e0611200c4081128d7b3ea00a0004800128d7557e00b0014800127ea4c720120084081127cd41b61020964400127acc3ce11208c448112722b6be0020c044021268072f6112004400112180b36613200440091215796b600201a408011d23003a0020c8448211c5990fe12208c448811a786db210a00c4880118e8fad611201e4081115d51f32122044400a115356b2e0120124001111398a261030c5440211029bde6002088448011014072e10201e408010c367202002048408210bc114be003081440010907987a00308944801074129da10a0044800106657dfa003041400210606a9a612b00548081025c765e10204c4082101ef567610204440021), (28, 72, 6, 19, 2, 23, 0xdf16772a1100044001cee149da11009e4481a3ec0a3a03001a40898f51ca4611008444018f1a8cf613001e40898ed7f7a213008c44897b6f30e203009244097aac25e613009644096281f1f613000440095bca8cca1300164009568e868611008c44814ae4e45a11001e40814a2ec3ae11001640013fb348be01001a408139fdd92a010088448139511352010012400133a2e2f601000840812b28c82603009a448927baaca60100924401243cb96e11009644012123f9fe030088448920ccbd2a13008444092051cfa603000840891ce864ea0300124009149614f211000c408112fe9a0e01009a4481102314ae13000c408909bfd54213009e4489), (54, 78, 2, 23, 2, 25, 0xfab7a36e000832052087c9bd3b6800a04018021eeb3521e002812062087a8e5491802a040180a1db9320fa0408130420876729a0e812201e10881d72947720028068620074f301d28122044100a1d2c7864a040831050087490c78180220c8148a1d1ecdf1e04281106008735d41ec802a00818881c3e4c166042807862006fe948fd812209614081b779af06040823052006bce42a1810a00c18801adb3290200080204200689f66a6810201e10801a145f5860488130422867f07a9e8022012100819f54604e00880004020676b0cd3810200c1080195c8fc9604a8010602062625a878002012100018513b552040821050005f3b53b18002088148017ab7df1e048827852205ea6f60b81020161000173a8ab1e000812042085ae5ded4802209214081602ba9aa00a8048602057df5619812200c1088155b1ec7604882305220545ee416800209214001460ca93a0088300502850536f888022040100a13e0b7aea000800040004e9e769b81220cc148a134433706008820050204be1aa118102004100012e40e9be00a812062284b74802b8122016100812a0830d204a80786220481dd6ba80020c0140211e1c65d600a8000602047626792810a016180011a141d9204a8058602045468251800a012180011417a09a040811040084476303c800a008188010d1fadba00082685200422a679e810209614001052fd15204083305208412ac686800204010021), (32, 74, 2, 23, 2, 18, 0x930ed20548c334122862716401a0a048088218951f9ee08c22412205a69f13832308d0488157cb11b5c8c3141028556eae232230c9048a14b40369fc0c334120851f116fbc2b009088813cbdffa6c0827812004e9bdb5da23081040813a1f9d314a813022284dd97706b3009e0489031683ed248823012204bdbc3989220c4040a12e408779c8833012284b437988c0b049088212aa3e2178a802022204a103d4013001e00890267e5404c88078022049652d5af2208404081258603a2c8c1340228495bb575d030850400124b7828908c3041028490c891f50b0050800123e97bae42c034220048e2a0195320840409122f75bfd448278120448b8332522b049088a122c62caf40c3141008486354c912204c008a120e90cfd80c22412004837392c923045000a1), (68, 81, 2, 23, 2, 25, 0x964201099095826a4450c23e20c80848c13502285e538730a426403c81122edba947d21230cd448a16fdb74f3c0950260c450b5c6098f884ac11520285ab0701b4405609291142c912fff9202b041480a15e1778d0109900620448ae4c5022084c82791224562aa696a404609281142a69a9c1d212200c4088151c0b89a909104f22440a8a1638920488210502053fe8a0e04054080901429d81122c2122084440814e65bfba408104f0a400a5a0b34708488079022052c326fed02540183110291a1ab0d212a01e4888147b4a2dfc0910620a050a3b68acdc840c135020850fca185f00540343110285e0cdde210b04d488214262acc0c01104d0a440a0e123970848c31510285057753c900440342110282755191202a048488a140da61cf1011864a24509e6ab14a6000820050004f0a5be0e421608a900427416c5728022088148813944baee1081866a24109c4d8aca8808c10500284df2d0cc50044090211426f8d5590810a04c18821372c09081091846a24409aaaa5f84848c21510204cf1de42240440808014267578c0121220964408132b7ca71c01100408440993cee89884a803122204c842ee2a42540889014261a539392123045400a130bb0e791011800a00409819c1e8084c825910244bc51c4e24264108881225b09daaf21220c4440a12d13e3091005820a40109606e9b1080a804920204ae50694a40440108110255d378542022048408a128b5c1c49081846a24009443367088488331122849d9239b70014000300024e276027200a04048021267193ed909500b2404092749732204a81106028490395d4842140889004247d8a82a20220924408123796463c09100208040919308fb480ac025222048c412d4300040342100244f081c7211209e4481122566688c0850020c00090c02ec2c80c824910244838b3460424402c8010240b2af31212300d40881), (62, 67, 7, 18, 2, 18, 0x3cec1eeb400330120ecf07b53900660245cf9d61b12801e088976059e04500341112e6e5505884104002db8234a8808668241b51760ff0004c00835e3dc4240209201069ed12c18a0100202d08363018002200019e160f500801a0881235991d25209a11163f23202c00310100c6b10c9d9080680448d06a39d2004c008b173ff75452012111213dac7ec24134220ba60e5d290046024470c1e42f2009e0488e16853464012c0811c28f3ad004324120b61f9899940260445684df43721045000ac8fe35ec0218208057da12e5480310102ad59a78e84026044153fb4ad92900d0888a7d108de5200a101126f7f20084304102a47f3f189002200054805c0d70801e08808fef28ca5008810151bac0d9c20110200a2aac5938086282013bb4c269280040808761426320209a0104ea432cfca00302221cef2ee8848228401393770cd2104d008a6a060950120921104c742ea60a41242229896b54d048208401307652b3210cd048a5cad59720208a0004b8cc1e9ca411420296256c689086282052a21a708210c9048a535c6978520021010a2e74a6884124022942102f604024044127b6a415210850408410541224211a09107e1f18d0a41042028fb2c6f61400404441a6e42132001e008832e651d21002c10005c340a44200302200ad59dfd848068440154cd801280160808162fda6e401080810221ec8c8a0000202001aedf3140240445), (77, 75, 7, 18, 2, 25, 0x549844f540900660a45994b1f5a210904d4883315572d7004003421124a82e65e0420130620c18716c5109002620457afa5d04812804c188af50f0aa0424012c8811ea094f9c8080069022357b8683c09400f0c446a9f6a82212001e4088c3ec8b17004009021158277bf2080a0121222af3d349f40040240c415ad0b17280200081088b2c2e52240401248811598087548080121022a735338bc0800660a414e550143212104d408a9633ab4d005003431112a99fbca008026852223e149e6409000608444773514d210804c48828ebe9e0c40420928115033c852880802691221fb79979c01000908043dbb5f1780200881488783658f900000902104dd28bb6884a007922219b4ae43c0900460a443118ea7a200104940825ee04f96424013c8910b9a29ecc808402502216f2aa5cc09000b08042d791cb4212900d48885725413f02400982114adf5c7f88484035022145c8c59c09000f0844286e63202008048488250dba252424002c80109c7352da04802785221337a3889014824a4452666da0e802009214084b82fe4e425209a911496ff486c848433512292b5dfaa9080826a041246fc2a7212800c4888477c5c2040401908914882bb8cc84001310209023b10f10000242041200d9f43202008844883c78761c424211a891076e2193484a00592020e4ef463909000620441be659382021089448833d96ad4405001091106775299480003211208ce2afccc0940060c4419c2ec052009049488232695d6a400219289045cc2a82c84003311208a8dfcf79010864a24514f1883b212804c488a25f86347000019029043cbbfe388404335120873e14ef409400b0c0409e9de142020012400812c4d7a3024012c2810241502e880a0049202042ac64bc0140240c45076c141d202801a48880c7144050050010311012ef00fa0080320522814b79a01014804a44402767297212008c448802984c3d0200098210403c81a4e00a0048602006e28c210900662245), (45, 71, 7, 18, 5, 22, 0x7b92989b21200a2204b8ae40e642401c440b4e451d220420183006979fb999090031002d188ac01210906a4019fc2c8f442421d440b31aeef0084841a801644675464014020602c7df970f8128060c058d3e89c442000c400307f92d4600801020160a94512c090030402c0be5f522108062401801263e24042114408fb17731c8004128005dd78e1a1014825202b90f6f9c20010ca2016e0fda784242054008ce17f0d484a00890118ca5d239004021200ada02ebd20280024045562467d0040001008a8f21c0c84a01890152fc3af140900505022508fe7521010ea2013d2359d2404209400a77bc65260400382804e4d24a8909483520293ade496200904a40126fa554302401c140a4896226084a40a90108b5eab490108050020ec44f2080200c0a051bc81da8405008480a35abdd38840038880464368ddc0100405020896e94b21210aa20410fe1ba242020d400219ac235604a00830103083d6c408003040084d2eaf8812002080406acc0f6405201480805ce22088084328814090b293c014000602007ede8e8008040c01), (45, 69, 13, 12, 2, 25, 0x19a24eddb020013c297ac7bf5720080124834e8af7040800460a5a33b91b4840003102b149dad2421003c9154fdad65800008814aa38e7df40040040c526fe87420400078428cc9b615020012c2842adf9f4800009a149e2db19e40840060c4ef0d32988404015006be9a4f9020002c2034197757810800418166e1691108000b200a75c159084042151051d5913c42100189128dfe4a1210900d489331c51d908000f2048a6428448400259104218d1c4421002c901deba7902100084440e52ff1b408400f0c46ee5a7b200000684235e9e86700000102119ff0d66210100d408b505c67100400d244584ff5dc840423512285177f7021002c3013b857e4200009a4489ce074b400400d0c43f59074c8000249101ef064ca4012002900ed5540420000884486dcf96d10800462242ce8a648842401520153af3a6420013c89094c728020010094084a4e0e1900000d204234629e0800422512111f1520421000890071994fc800009214012aa4c240040090c002db72aa04000304200be7524401201291)],
  [(24, 59, 3, 14, 3, 14, 0xf589f7e50024041a7bd695ee04a285e4e9f1dd8494522b5704e7b806a8155aeab39610d508a8fb1c20e012a052e7bd1758035402350739dca0660944111492708952269c2dedc6010a04c30b0c65c2354897bb4f33a8428112cfafb8c30885223b88fb5928118246fe4e7e4c031408b86ce03b80288113432668402104024cbdba6e10a2443caa7df5823548053d56f53044a90060ef5b861095080a879f5a6118a4409c0e799c204488049056c9086284), (48, 71, 3, 16, 3, 26, 0xfd0343640058495149e4de8c980038422247c5152290001424210f6fed79e0000218204e30c9dfc0041494849bf80cc28002842204750dab95000700c540e69ca8d6002421a284cb9145dc00580355018a9e2f18008a0698070441d33001410d5025f8ec7de0002018201bef61c940050495049634e63280022863812add92e9000610c542525e12a60000a186049f7efbdc000423042330b8b608009826ca065698931001308d148c39a194e000280840183700f3c0004132402ff1666880018264a05e9fca6d001408d5083993c9f20006118291730173bc0010491048e565da380010860a11c77f729001200d140367264aa002a81ae016535446c0014231422bc3175b80018060a055d3ba59001004d9002524d7ae000a908c1144ff64c40000490048885ea69800b046aa4107a1a950006124452203a7456002011a2103f9105dc004413640277df4c38009026ca00e901eb3000148c3089a3ddace00042480a4344bba740005030c0264a5e5480082469840b4fc24b000410c50212cc480a002601a28124fbeb1c0041434c082b9b45a80090468a4044224f1001700d54082721dba0000a48424), (48, 74, 3, 16, 3, 26, 0xad1cb0b6800b842a24657d5e9e6002e00a881936a58a8800b812a2863b04a0c6002290a4118859f06f800a286b811ddb5e152002a90ac11646b3898800aa12b085807a8bde002284a4215edfa58e8008a0290057b0adb3e002a10a8115dabcf8d800a806a8056dea593e002a91ae115852bea6800a802a0055dcac036002891ae10563fb66f800aa02b0054eb8a872000a018a015380441d800b846aa4547da43be0028a4ac245098ce0380010460a41373ad286002a04a8214b9ec2388008806880520a6591a002021a20447c26be3800b086aa1118b385d20008018a0044d7536e8008a46984500e8304a000a918e11358a0cc380020462840d5c3de4e000a848c2134fb3686800a206b800cb295eaa002024a024302c5e4780010264a00bfcd73b200040182802daba25380002461840b682616e002424a0a42d846f5a80082069800a88bee7a0008a48c2429b37a2f80022063800a287e19e002211a2112835f6538002a0638049a0a9c8a000009920025dd3f8e800a846a844954b92ea00008186002540fbbe8000a42104492643452000c118a90244dcfe980030062a00899ae762000a808c0122012b6280038462a44871751820008918e10), (67, 74, 3, 20, 3, 24, 0x3fd71062802a1082811f6f9cd6200984608a47b3e47ff800c24808a4dd04710600a8460a8473480315800a9180e11c9cc29f600aa420b0472479f058028a482c24c586602200aa120b0870697d1a800e0080881b2a97ff2008a0209006c82850d80041180290af40ca66008a1209086b5d787d80229082411abaf54e200aa020b006ad9eaf9802604820a1a7db5ab200180600a067bee11d800609812819d0e4f2a00804608842719b33c800c208088498a0408a00100600a025cc58ab80228182601946a099a00109200292512c69080240182280934c9c660038120228623a3909802091826107bbc8faa002a0603805d8d9126802c1182a907010676600108200211bf51e7a802021822046eb88b9e008286098117a0cdab802e1182a915d5df8e600380602a0573c8c0b802e008288159be8fee00aa060b8054b75d798020a08240450a4aabe00300602a0127e02d780288182e00469f173e00a2460b8410d0fe4f80221182211416b924600204602840ed29d2b802c0182a803ac8c78a00284602844e256b2080040981280349d1fc600384602a44cf74d55802e108289132a2ac4e00a0460a840c051ca780229182611299358a60090260ca009c7124d8020a482424268d07e6002246038408fd3385800c1180a9020c90062000a12010847d067b2800291806111eb9813a0028420204474b59c9802421822841bb9786600108600a1060f5bfa8002908041117ef5af2002a120308457d15d1802424820a41082221e00184600a44351023a8002818060108d88d8a002a420304421f6f64800e108089105969c32008092080900cc8b13802411822900231a54200084600844053c8c9800c2180a84), (18, 76, 3, 20, 3, 24, 0x9f2653228028a082c048b2524de802e04828a17f7a4e3880208182600798a5de380282082804761e74ba802a9182e116f7debf38028a182e046c140906802824828246b0097a280282182a0462c3eb42802c24828a45dfe131b802601822815ad75f18802c20828845570903f802420820844ce9b2ef80060c810a14c0c2e8a802e0182a8148fb394280260c830a1434d7bcc8026098328142aaad85802c2182a8440051710800604800a1), (48, 80, 3, 24, 3, 26, 0xfb40397c882611882291eca3a77608260180a281dc46f07e080a01808a01d72547ce08242180a284cf529bba082a8180ae01c6ac5dfe40282140aa04b0a276920800a1808604aaddc66a082e0180aa81a7391dc6082a1180aa11a3f43aca080421808284a03968ea080a81808e0198e12f52080a11808a119298d0f0880e01880a817e30130608220180a201709149ac880e11880a916f203a920802018082016d5ee04a0806018082816a27eadc88242188228469cd402c882e01882a8163dac1820802918086116341232a08221180a2115ce3450e080e01808a815a7810aa400821408a0453d66c560808a1808e044ddf4d8640202140a20446cf3526080c21808a8445fb63ae400021408204372b41a2082a0180aa0136bab2e6402a0140aa01353532c640220140a201335360aa40220940b2012de614bc880601880281271aa71888061188029126e50e5a40021140821124e72d1a4002094092012054c22c880c21880a841e17f9488826018822811b65438e080821808a0418203c9e08021180821116b6a9a6080281808601134bd72608228180a601127232ee4002014082010fd8e99e0806118082910e6cb36a08261180a2910bf43c00880421880284062eeada400a11408a11056217f60820a180a6040201ab36400a01408a01), (74, 78, 3, 24, 5, 24, 0xfc1c6ad240220d02c087e11dcbf900a8040a801e7c55be0880c262022937cf747d8203098088a4df00adba08282602a0935129748900280408801c709a7e488060620028709a4c5c8201098080a4c12aaa38402a1100a046f27566b220308880884badb9328880e06202286d9d95c3820aa180ac21b5ccab92082602028206c90ccd4820084808011ade10e4a082a1202a046b3bf4ad220380880881ac9dee5e400a05022086b1a3b268203818088a1abe4cf3e400a1102204682f5b8d90088140a0219b659636080a1202204656eb98c82008180802194134d3e082a9202b04649cf9a282038480889191d3705608061202024646af5ca2209848820918cc22a660824260282922948b5390080940a0248a07f01e0820260280921caa5138203808088818384bc9a4002050200860c5c88a8202a1808c217a6f00a8882606208285e063cb0820b0980a8a477c9789a082286029085d655aa18201818080a175515c26080026020091c5a37e02201808800816c52e1c6080292021045aa1dbf282002980842466d5b76e0802860210859017775900083409021639c15a2082a8202b0058a9e9609000844080115c9342fc402a0100a0057116d6222038488089155684166080a8202300542477f282082980a4244c6ab0560822820290052039a28820a8180a821473705ec88042620029117d14ab10028040080144418e9a08082602209110818f9220084880011431c9006080602020204fde6d80900a8140a8213f14f7ce080a06022084f4ba5908200a08084013b1f6e18400a05002084e72f50f2209098820a4368be618882602208204d39a1f890020940882434bb4280880422200210c54ea0f8202a4808c112decda18882212208044a4a142e82098180a0a1284ab26c880a1220204486cf4bd100a814028211f0cc538882e1220a24472372f6100284400811062e2f6640282502a09017cf579900009408024036643c0880612200244018d2c8220b80882881), (51, 76, 7, 20, 3, 26, 0xf1dee56608208480a42edc29062400811408a1ecbabe8c880c1088089ea7ecbf2080881808e0e93937c640001140821e5285b2a08289180ae1e17d925e08001180821e16ce09c882c0088288d99e3ad608008180860d4596aa488240088208d17d846208009180861c844374608281180aa1c5fe442208240180a28b4b77dc2080811808a1b418beae08240480a0ab105b87208201180a21ad28518640000940920accd67d240000140820a8a3aeae400801408a09f74f74240200140a2096a78c920804048080a95de9c8640200c40b02929dc26608241180a2987bc9e38880c11880a97fcb9d92080c01808a874f5dc5a080884808c2710bc47c8804048800a5f2aacee08208180a6056f3f7fe082c1180aa954d8d80a08288480ac2535cad9e080084808424d3fbf9e40201140a214bbf56a4880c048808a499a964640200940b203f4c9f7e080c048088a3eab69d0882c01882a83e3ba9d208209180a6139cd2f86080891808e13820837c8824048820a31ee593240281140aa12e1db24e080c11808a92bb8305640280140aa0274f865c88041088009212c8cf4880401880281970b46c88240188228184907a488241188229139105ce082c0180aa807c57cd888041188029054fdf4a40000c40902010e1614880c01880a80071b60088241088209), (34, 82, 3, 24, 3, 26, 0xd1525530220b01220a282db0c49e2082a9180ae11a07b8d6e820a28602b812519418ec882e048828a18eca25d9820b84202a24617ca268a0828a480ac2482e7739d8208a460298460244dfc8882c21882a847d9769e68209842028245f3bc3ee6080a91808e117b28a69c820b01202a281e99e2522082e1180aa9171032623820b81202a285a5e5559208229080a411664a4d05820a20602b801980ab524882c248828a45e5cff32820b08602aa115cf7f090882e11882a9157064748820b80202a2055bd01d3a40221140a21155a1713d90088410280454955580a0804118082904fc3665782088420280453de3a4a6402a1140aa114f61ccb822090822082113705b930882c108828904a3038b382022920230912794b6ac882a10882811476c454e22030022022011bbf1abc882c20882884446c4b91220b04620aa4110767e7e080401808280439b29ad8203846022a4506995932402a1040a811), (52, 85, 3, 26, 3, 26, 0x88e1bf8ec015c21005448ba67f5ede00ae04802a285cab142710057004015102bbc0f390802984200a0915b45293b401584300554228a64cf6a00aa10802a0452066346b005108401402284401719902a84240a8114101f13f4014c090050509f104329a00ac11802aa40f84c6c630053004014102789e98d290228424088113c487557c0148230051481d4600faa40a2109028044c3f91c97004610c01150860f65293802b00600aa8030422e4ec014843005142181055c3a0084118020a40bd36a3c700450840110225d5b00fc802900600a2802ea409b5c010c21004048971e323b6408a009022004b1f2b5d1004708401112254e013d780238020088812a18c93c481540120540094e224f664082109020044a21a559100430040101024e9b48c28023006008a8024984967c010c09004050923ec280e0084018020a0085766fc300561240151483f05874890208024080011d9d2c6240104210040088e26702320084218020a10711d625720550248150423879641d902880240a0011b0c8b5448144092050108d03cd836008c118022a40622a623d0047024011142308acdad8023806008a811667bed948114092044108ac035bbe40820490200843bfb44ed004708c0115221c804df980218460082910b89677bc014c0300514084fe8c0520086018020a041f9d507d005708c0155220f1c2ba680230920088a4029a7168c014849005052006e46c0600a6118028a44011a7445005700c01550200016d2b80210920080a4)],
  [(65, 62, 2, 18, 7, 14, 0x3cc38dc7c8448609edb22c93250a102775c2b4cd1060618d7f43fd20518180752e5aa891060610d2fb7485240a0023391962f890a8402cce5bca2252a100f14c1d6a51460219c1b51cf1241a08230116a8a91020410b9c4ae6320021022ba55869d0040618ac09e46e411018469adf4dbc0400409a590b6fe4528104e7aac1c5410602089bd1d2d144180862688ea1d880486009908f9ae250a10066299cce884486019637835504080022301c930094a80038934feaf240a10221175cd3c10204087f4b83ad20920921fab0e9c514200197e3b60ae45081045f77ab1e890284007d36d31900900921ef284b9c906860878d1b658242a0009cdcbc50114602117222fe6744081061b3c8dbc810606006ca35b3045080045a741133810a0402670ac961051808259ab3de381420401645831b5250a00258acb763484482095872544f45181865591f400d14204194ffc584d251a0825182a676d040041943c450564428104903625ddc14204093e73d926241a1800f43086bc00406083befd7a00528000ced0458f900406103ac9955521020024d8821fcd000041835c5edd105080024cf37576114a001332eaac0920820120b9c12ee40040208224f853044180840885fa1a500402181cd2109f0418182067a59f4914606110f145b3b00001020230c7bac804860807cd20f9411008640e9c445d0440619), (11, 64, 2, 18, 7, 14, 0x804d6a59c840840971b16ba2c94686096e513372104402115bc9b96f894686015802cd7cc044060956df039b8044060150850a77510200184eb82f5e814a040347b5fdc3c14606094577f69940440209456b443048048208), (58, 71, 2, 18, 7, 21, 0x376a87b56008222108dff39e8bc0c040440978b06cbf81a0888c32f0837ee90241111845ada8fae206802230c3430c0b1c0d1064618675621fe81a0808832ce6519c5000111080598f6c84e068a1220cb27813b540d10244185d4e475a8180008810b4393123020529100d63490dda060a32304a5736f3fc0114a401345f263e081228488228b27410f024011184112967ec2068a3230ca1d2ed8340c14244094293c52181a0008830849b7591014409006107ddf13600885200920c2c92fc04106420840f841dc81820c8c107efcba970245191844fd65d8a6028a1200c9efa952640800446003c00f7218182048810756e2feb0000910900dfa9bf46008a321089bbb0c7d4040244248361e08108082048010666e05ef0205191804a9861e9a04085220113e29f0640114240112724cc4e80a28c84324742195f014011086084334126040a122008e45f470c0910244101ab92e3c8002148004352e052500440900405aa9cb060602223048b499dbfc051064218167ea4cc80a08884322261d52d00051908043f761db2020a321048780d09940804446010efd4d6a808008841015a8860d02442910482a6b3262000a52001851aabad40910646100896d2db80028480020e7373cf02041918001b689a52020a12004832fff14c0914a441305a3336580220c84200ae034bf0101110824112733a60201020240091048bc0c0044608), (83, 74, 2, 23, 7, 22, 0x3fe2cbdd80004404040fcf4594402023000827e54376100128c28201f7c4797404023001807cb074ad00a00c00218eec6f22e06083091823799774100229420013d87aaadc004a50a000f611f1b700804400048d6411714064230218274ea784781228c24611d2c6ec3602083090823273910d81a20c24618c4c21a06028030108630d3a7df00029420003bd5b1f2c004850a000aef9c81700104408040a939e61e040a509100e9f54dd700228c20211a3c5df04060230018268adacd300104c082409dd250240482500104e6d7e9d380000c0420099542ff4068830818624e38ced01129428403925b883600023010806471076701100c086008e4d22ec0442502100e35149a901920c28608887b19de06803011861f8f5d9f01220c2061076f141e606003011821db628630010140800272a8ee7c048a508104dac7aa41000054000426a5a194400423020805a6e36eb80808c0420967d145fc020a30808259bd37d90112142840266e737340402500100d9b82d9380800c042086542b0d4044230218057f31c1f81028c246015eaffb16020a30908256b8d2fd8122942441356dfe41c0608308182149dc57900220c2021045be5c24060a30818250ee5b3b01020c206004393111e048050110490b359a381008c0460140038c660482501104cfc9a465810214244023e593d9c04803001840f59d28981808c046093c6819260402501100cedcd7f380004c04240390cda6c00823000844e3012c580a08c0421937f600e404885081048d65ce7d81220c24610348963b6060a3091824b208c89812214244122c5d7c9c04005001008af20f8780028c242012b679a5604803011840a39a58b01228c2061123b3155e0088309084088c249981208c04611208cc154048050010487e14d03810014044021ab9273402413020920592d99300004c0024015dd458e008230108444f4ea5b01a00c00618106064bc020830808203090ca900008c0020109f80704048230018441e192a500028c2020104dea5ee068230118641175555010214204020370b0140282300086409ce6f901101408402), (38, 70, 2, 23, 11, 18, 0xfc811ac406430210277a32c970010408000d8a074ec044b0a100760833e581a2c24419c639866406490a1022fabf7dd8122424410b977d6ce060b091026d610d070182c20409aadf974e04810110428222e5300a242001897b17d84068300106645198a30180c004098ed91abe04830110461cec40301a0400418806cd4c40409081001e6af18d01a24204187913de9e0689091061e3186e7818242440875d9c68c068b081065be678ab81a0c044196ae60d540401001001a49ad6f0120c0041165e736c4044302100586e260b0012c280015f2cfadc000908000155f17cf8180c0440950f7647e048b09104538cdafb0102c2040142a9d2f40243020025049b17d0122c204113aeec7d6028b090064cb0ee0d81804044082e95f6a40043020004ac9b957011040840029713fa6008b0900447493e030192c284091d04da7606810110602fe6ac90022c20011), (69, 77, 2, 23, 7, 22, 0x11f09c9c300928c2820989b50425c04026021244473fbba4024a10a0025a90c69e202251850c02d13c77970022142001268306c94c0800602300311de770e0088109004181f712ef01451848432bfa73ed3009204280085dbcc31380c94614304aa76ef2ae00803010841528b800e03000800810a87af2dd0002142000254090af68001061010029560c694004810a00012b57ac4b000418484009566985980a20c2421849b7d24e801102100082439559b4024830a082121ac9ade002418504008946ff8d01900408408449fc9848008060410021a86fc46068a3091864ffa12dd6010508400127e5f5321810284244013c339ebd80084a040019e06fb72e000a1090004e72dc1cf020108088027305c3ff01900c0860838bd3702c01146121089c37bb81c02003000820e04f572f004528480266f0557078082042400836e0d9dac04142120049b472f16c02411020120d833704301008808090690a1c7100820420008343e6d4980480204004195cc206400803000840c973d19b0005284800660445e9380a204240182e8b4121c0002a0202116f97109e00081090000b3dbc1120121181041258bc5a87001054080422c06106f8048060410415c1fdccc04003001800aad29fc602051840c0254fbea2f810004044002a7be21980d1461030c94caa54ee04081091000a269ad9a0145084003250728a11010084004012778553ec0010a12001139852ea4000a10800049b00f90f02041848c004cf90fd701029420403258f67ae80c102102041269d927406003001820926b8f3e01441840430490a25f101120c2860024076dfa8040260012411a30c354068230018648ce286d6000088000804626bc9d012004004102308ebcf80910210208117ccbcfc044810a100088142e2a01451840432415a3a8980221424012), (52, 73, 2, 25, 8, 16, 0xc0c804b78229810009c0df3f42c5044000065c7e71fee2422010012d171e7f322530284035a2bab2c8808800004aace1441449440a0025468a311a44a2050802a0d92ee904510200114f7ddc559928814204a3ea9eba4014c08000d1e1def3a08860400248a5f935d000b0000423d43280d90288102009e688cb5cc044001024f31dc62a042201000265b7e13d00030000023029cb8090088002009783bf68c09440a0004babe83a6042601000657a391d104130000132b64425a9908804204953337aa4c144081024a146945a00860400044b5a829d224302840224852fbb882881000491d1d307440240001208d0c629e00a20400023d66dccf22110084011e4df0db81218140010e974546cd144081064721af77a28a204003231d7f21b200300040218a8959092298102098bd3b770c080c02000854016c0a0412010080286f669f241300041313d3e6fd902181020109e8d1674814c08100c49c0090e24120100901ec6675124030004120e41f40f820180000906e6865f4094c0a000c359e0bc6482200082218b63fdd22030084020b55eba29228810208853391bcc884c02100c1f13329a488604082407b8fab1041100001103d2de4590098002018111d7ec4082c020108019c0e4a002600000600365d073411000419), (35, 77, 2, 25, 8, 20, 0x4d1584a044114c09004e3256214e200a604800693044361130110044094432d09789221812209211981bd445044010064fbedb152268a20488327c61a42f130510244093dafcb69882288120089d3ecb16445144090064df496732200a20480026ac8b13b10009004040335ef2f18922881220898876585c4d044011064b52d1d0a240a604880656a1211711011004009235ea11289208802208914eb60a44800c0110088a27be72200220080024235c7d91205102440120f669ea892298122098feb5fc044100c01004875f490e2220a204801239f33601124030044121ccbf68e888048020240e30b31fc41044010044696d29e62402200880233dfda671201300440319b0ed8e880058020210c0e3cd9c4110c0900484393a976240860488041ec1a4af104130040130cf6a5c788009802001861d7714c4010c09000821857bfe248260088260843edbb10003004002), (37, 68, 5, 22, 13, 15, 0xf78cad0e124200082b2e07be3110604801a4ef9b5b1346048839ab1a9d01126050019732728a11060400181ade4601122010015926d18112460488256ad3b271146048034ea280141142000034721e85c1306040814568d1f01342000834374db211046048023d3ef547124200882342d40941222010802fec03591202008802dfd13e71142008032b4816e012460408227944c9413460408325222d501022010002323c30913060488123103c2612020008022c57f061302000811de425a51302008811dc321d41102000011d60bd6f12060488019136e6d13420088314d14d331042008020fdf2d6a1026050000fc04cfe1146040030f06bbae1326050810d4b93781206040800c6a01f012260508005afe02413220108104b94dbd10020080004264683110200801016a3f2d10060480000ff47b2104604002)],
  [(50, 75, 2, 19, 2, 27, 0x3f67e55190040060c40f46ea0cd200000c1800d77953344010040110b95185394802401028070bf459f90048120542e107d4fd200800c1801bd4c7c52400205834096b1a94dc00200b04216b9f37e800048100102d6df58be20090200a85a9da16c4400204015094357626c00200900216807a30590048160d42ca733aae0009020028592a0aef4400205035091c70b03400200900016369601b10000140c424381a29b200002c18847a7c1d1240020183400cc290a8800040a04a11600025c90040160c02a9e21245200902c1a05501efc72401201834029eec9624002409008152a7fdc890048120502a348805420090281a0542f2fe56400204815088068052400200b04014ffeb70c800481609029f7a4b2d000102c12043dfe91be0002048050878e3ffb200000a04410a8d0853800081609421463ca172000024088428c73698400204014083a63de18800008022106f3a12b80048120142898d7deb200802408851089dca04012040140a0762c134802009020140c2ebc890000160c0200fb60f920010240a04015778290010040020a02aa2f948000090201002e6d8210008140d020059eb8b0000024008400a9e33c4010050310a00b51a3200000800410015b64680008120102000e267600010200284), (63, 80, 2, 24, 2, 27, 0xf9cca064400a00400a80f473051e401804440885f2090404400801401880e954fd56400804440884d3ea9764801001801081cf471d3e400a04440a84c5cca9f2400a05441a04c20fea94001a04400285b99ddd96400a00440a80abc7bd04400805401884a8146edc001a00400281a705ddc4800005801084a47576d10018054011059dc58512001a004402019da90ff6401a01441a8194e082b480120480028593045a2a401a00440a01927a5a96000a0144128088cef1bc40180140188182ef23d8401a00400a0181daa066001a044402857bfdd2890008054011047bb2d39a001a044402057b81457c001a05401285730bbec6001a05441285715e7ff440180440088570f4f802401a05441a0562feca6c400a05401a845e5910ae400a01441a805c973e9c4008044008845bf67382001a0544120558fff03880120480020556b0a80240180444080550d81a8e4008054418844c7f29110018014011014898ac1c80100580108540ce7c7e000a05441284379e715e40080144188033cf2dd100080140110032b136624018054418052df3871240180144180125cf750c000a0540128424598e8a400a01441a002372eb4c401a00400a811fb30fda40080144180015fa2bc2400a04440a04136a106840180440080511d4e346000a044402840da19c52401a01441a010a64a142400804440804081ac6d480120180128107767bdc400a04400a84064a1f9e00180444008503b14e8a000a04440204016218aa000a0544120400deeb4c401a05401a8500d2fecc000a0440028400833ecc80100480008500563cc100080440010400561939001804400105002b5bac8000048000840021f59480020480028400003448801004800005), (72, 83, 2, 27, 2, 27, 0xfc0805860012818082503e839d41c00310b1104217cf95d559000a16020d42799492bf000942c041285ed52dff64408054883109d2d45a7888300a90062179b6bb779106815220d42f109d11a220100a001a80def27d56000a858882509bceed4c808300290042076bc9c8b01028052009406b9bc71a220402a401884d16c03de440a054883509989309b808000a800421324aa2e38102005220840642a2a2a020900a001281c7adff12001101208200387e14b4880220240062070412b998106015220842df9c5c27000540c441280bf284f5e0001052082109666ac3b48820028106006bedc2819100a17020d4257ace0dd220102a041a04a49cd6f2441005408300b4869d60888000a80062128a42a5d9100217020c424ec5a3f2200042c0018849a06010c040205400250932ce6fdc00050b0104a126257ad71104015000c42cbcec8ea020802a00108590bfd0a6001085808210b1f0e7fc480020241060023d69b219000a06020d404791585f020502a4412848de9f8ea401101208300308c61ba880020240062020a013779000414820c424041bb36020402a4010847d45103e0402054082508f1ea33cc8830029106205c4887819002a06220d40388accb7020402a4410846e76bcbe0011012082102d880ba4c8825038106a059db6da39106805220d40b2f5c443220840e04188160979a560008858882108a07f15dc08200a81042153e455f5810001502084226c4470a20008290018844a48371400010520021088c4bd1ac80210301062050060dad1004414800c429ea4988e020100a0012803a52992e4400054083108635cb52c00010b01042109d7e2ed1100815000d42113aeefe200142c001a8417f7081e40008580831082dcbe1fc80020241062003dbbb529104815020d028670561b220c02a4418850bf997ae441005408310a12b1840c881002910620020b7da89100005020c0003c6f639220002a041804068bbcbe040001408210006c2c23480020a41060100768fff9100005020c40008549890000829041004), (80, 81, 2, 27, 4, 25, 0xffdb43ee001086020042f8dc7ccb0208438100217b497636800441208000bd5ca35b8882402000a81e9afd17e041001020040f2c246370209438100a177ba7f4f8004a1808050ba5048f2c88140a440a84cf962034801086400042e344bbab2208028102217171b7fb0106804800503869340a4002201040001be6e724c041801200040dd21ce9e2001430002a12ce471ef910600488110366acc7cc083002440081b173f9ee041a01220140d47ee9ab2209438102a168728b31910681488150b3b87107c882402040a8192a504ee44000502044245bbbe3a0009430000a162d55939910601488110b0feeee6c88040a040a8485cc3022401100820400c2d8491b2005431102a12041788f900021808110902051aa880210c0008857cd4ab3e441a87220542bdafa45d2208028102015d6fb167100441200110ae946645c80110c44088474820004441005000442b1402bed220d02910281581f1cf99000412081108c0497e7c08240204028159118ba44408052004422c06284d220c02910201545e3fa9910621c88110aa2df25cc00310c44008550b90434041a05200142a6d1776502090281008152ed2d7b8102814880508958a758c00220904008545a9912c0412050001429f84d8c30001430100a10e19f15b11000140011086dc5a0f880250c000a8533627d3600088622004218669e51220c009102004c13fe7b11008140015085fef465888140a400a842d5df9b6041205020142959b27660008824000214a20b1e6400441200020a49758adc08100a4400841dab673a4410010204008e0ee00a020c02900021457cd75d810601488010a1c1d0f7888240a000a850dcd78d2041005020002849eedb7020802810021424667fb10002180011080eeccde800210c00008505147e524400050204020283437d22010281028101317bd58100814080508091869f88002090008840364a6fc0410050000428104e58e020402900021003f2e549000412081008016952fc00010c04008400af7b9c0402050001420057a977020002810021002bb551010001400010800ff42ac0002090400840071ee8e40108602044280364aa60205029000a10015aeca800041208000800a56428000209000084), (91, 84, 2, 27, 2, 27, 0xf9c6844b2008801040881f82c8027200542c441a84f4a6ae9b2009000040a81ef0e11ab200c40c441881ebf6bef72008829041885eb35d81d0008829041005e5093bde220c00a401881e275f693220500a441a80e254d4962005008401a80deebeb272001000040a80de78e9ef0008801040081dd8e215f2208426040885dc42e67e220502a401a84da1505920009028001285d6e0c6b50005008441200d6519c8b220902a041a85d57998a20008809001081d51ef287000140c041280d3a45382020502a401284cc2179262009028001a85cba91fcb2000008041880c7785263000040c041080c7760597020c00a441081c6ad72e62208002000881c546c073000d000440281c5136b4e4009424800285c4c55c56200c028401885c34141b3220102a041a84c25b5c83000d424440285c0c81135220900a041a01bfad9ca24009404800281bf7c76b7000440c441080be7a74fe220c022400885be6d4946220900a001a81be49732b200d020440a85be0ea4bb020902a041285bb72699f200d000440a81b9fb8686220902a001a85b9d61a2b2009424040a85b48cfb4b000d008441281b452a7620209002000281b225008b020d02a441285b1f83d2a2000801000880b1cc73864008404800081af436a920005008401280adba0937020d022440285ac72c2232200426040884abb8989b000c40c441081ab5fd8572209022040a85aacbe1db2009008041a81a7ee123a220d022400a85a7131427000d40c441281a6946d6b2208002040881a565be5f0005424440284a4fd48f30000809041080a453dcfe200d020400a85a430fa8e020902a001285a3207a360000809001080a20a2a79220d002440a01a1ae97cf2001008041a809d82c316220d002400a819d33a54300090280412859ce9c94720080280418859b4bbe0d200d020440a059b468b77220842e0418859b37755f220942e041a859a8a7d5e40090288012859812ebba200942c001a8597bb3977020900a041281974554232005028441a8496851ab32001424040a84965ec00b200c00844188193e580de220000a001880933c6efb200940c041a81930eb8fd2209002040a0192dff5bf200080104088092c53ac6400102880128492043cf12209022040a0591acab6500008090410008fc43a9d20040284418048e0ade83220d002440a818c08cd7f22040224408848be3690a020c02a4010858a69c980200d020400a058994c743220900a041a818924c4f3200c0284418858793791f2008809041881871932ce200d424400a8586c57e2a200c4244008858600c21b020100a041280832791b6200842c001885), (41, 86, 2, 27, 2, 27, 0x3e5e28833200d42c441a85bc1fa365c80310b1106216585dad7e000d00840128188276f7e88034021006a061623e9af200942c041a857d96ce4f800220a4004215f619f097000d42c44128575e7c4d2888340a9006a15b645151300088290410856b5574ac88820028006205a2632107200d40c441a815f7b282788834029006a056eeafd7f2201426040a845892efb14003402110480558af02ae020d02a401285559d9ef580820028004205544322cb200442c4418845397a400c08200281042053db84a7120088290418054f6dc7d62003000100040537f8137b020d00a4412814d0e2eeec8031091102215333a30a2020d00a4012814ad394ee888300090022052a55e4f7220800a0418814a405561c8804028106a0126318717200d028441a8548fce1ebc0021030104205235e5276400000880108045f9974988022004002205173793bf200d424440a8544741d2048804028106801109b75ab200842c0418854397c757480220841020150d73f6672001028041a844272990e8002200400020509b6155a020800200008141f55adf200200a000441507b04cba400100880128041a611e5c0814029104a0104ed3ceb2008821040885)],
  [(80, 73, 2, 23, 6, 21, 0xfcc2b9cc0930682050f845fd7cc40c3242207c1e8566200e1021143d8338ca80021100101ea04cbb28990702448f3e023a4841c52404877ace290a2201c01121bc7289011020c00881dc186b190130842090e714f000809c225028720c3130024c18081438e94f3590020900881c5574c240930a82090e1c2645504403800242fc7426460061121103797877e91260d048a1bc5432ba0018508040dc5f627240182402286ce189068046242820364d40b780061100121b03c5d710830a40090d215e660041c5040486857dc54420c19001433d8de30100308108819db81a51813844a450cd7657e2040854004065cc1274a2601c091212d36d8741221604101968935e00910a02080ca8c75ec001c20402864e3be9a622419011231d9073741230e140818e7c84aa0890700048c3588d2500084800406091df52a0061421103032207b91220d048817e2927b0893860a450bcd98f40040c5040405e683e3d020c1a00142eae83580007101012174b019180810a00080b9f2ebb0c08c2252205cc8deed204c1209142e5037c421270c940a1714fa7198980642448358044b0049c5050485abc886a420e1920142d0ad21911100c0089068346a9c8830680450ae154118008c405040566149ec20461029102b2da10511300c04890544faf42891870a440aa0b3bd4440c30422054141a2e800624202029e092ee2027109412149b3e7410910a42080a34f24ec4488301220513800b480442408202826b2a3802609040a13fd369a0013880a0909923f4c404183000284bc4383722041a0110259d237f11230c14881273fb2d18880640448120985a0840c5240404881baf2424c29082423fdb36e810615001211d66f0000830a000908d360a09444838022445493cc8226418091222a32492800609000a11351cc610038848090861b45514488381220415b8c5422241801122065885a2006108012102502169001084008080fb00e0800c42404040778d10400e112014201185a721021480101), (39, 76, 2, 23, 6, 21, 0xea65ea3a31260c848a199bd779531220c84881661d648801270c140a15ff3ff3211070c108a15eb8228721260c840a15175e9d131270c948a14fc26f63902209048814c87329341320e04091429fd441802611041214223844b31060c808a138c52a9901070c100a13794126b51020e008813644913a31020c8088135777304802211041013453d17d41231614101344b31290126140412133da0bd631320c8489130c02eb831230c948812fbee3b9102708148a12fa64ad2812215041012e42cd6a41020e000812c4ae49c40230a140812b9e24fc41220e040812b93150311260c048a12aeb4dc541030e100812a909df2410216001012914bc8b41300e040902908831401231414101279b14a62022108410127016f9541031610101264b806550230a1488125bd01c851030e1088125a7cb0b2123149410124cb1dce31070c908a1246083d7300708908a122dae54920231094101223b49e711060c008a1209bb48d002708140a12017360e21271494121), (77, 70, 2, 23, 11, 16, 0x30e6f2894893504821c0e5e39c204e05208670699614811104801995df500a0468520066141e548883c10821962ac540800480000645bca9088934048216dbe3af42247052005b12eb2b88118148016c2408be424f250085ab4adf7a08160000166e655caa2078420058ec6f0e28816008015f83a58482078400056f946ca80038100215a1ca0eb200c4020855b0256b0893c14821538488c6626121204140d968fa891e148014ecab4348261810041384e3e3a89860481044fcb77862472520050fb467810934840213de620de024f050084eedb77840131040213aa8f100024d010084e85e40320916040013a10d83e2221002040e7cf64f188848081039b077892004402004e444cecc08350002139082c34420f240084e2bb7000083400021354f94a82261012040d52adeda011a140013426dc1a624f252084cdf88f8908348002132b89cce6046252004ca4d19b2091e1400131df61e82207042004b5bcc4d48835008212c184c962205002004a9730b40083c100212a4baafb024d410084a38ef03880181080127ae7aa3000c400084965043e2099604011246bfb64200e0420848703cc32801a1080120d603d52245412004810a32228886008101f5005d88225800044797ff1ca8916048011d6ff037204c4120846caec6c989348482117a9c084404e2500845aabef6089140480114093a0a620f242084498374580138140211080e852a2658120443f65bb608834008210fa75c2a22650120442c4ea4c2001a10001080a6a4062252020441a985a0c88150080106474918620724200414f88c4a08860001005114232a2258020441302434181389482104bb9bd6400e2400841174b091803890821040046aa62652120440f75cf618914848010347cdc6620d2020840b9456988894008110089e568600624200400a63e71881480801), (54, 68, 7, 18, 6, 19, 0xea7c1e9e880860844c1e0c3140928a0a09bd649aba0920a0209aedd75808028408459defc457880064044988cfed588206404597543b27892064245966721f40820a00099563e37a0900a020892ffc0368820600459206260c0920602058f34d622092860a058db6cc5989006424482a4aa140028408057b563848890860a4467b1e3040808a080863307970812840a455f1d7919012844a055ecdab860828a08094a8ee4bb0928a4a094a7e4096892860a4546e7810808286080541ddb05e810840a443f6273788920602453f507dcf812844a4538b8cd9d0920a420937dc9ac2012840a052ffd3c868900602442feb4bf68008408442e6fe0c90908a4a082c1644d9890864a442630aad9012884a091dfaa4220820600051bfde299092864a051a5cec370900a420819454adb882864845191f42490828a4809166e2835800844844100bcf3b892864a450eab181a0908a0a080e099e870820a40090d0c59998808648440c26f7bd8028448450ac15cbb0808a48080986708e882860845088b20190920642050876114b0820640050679297f810844a44038817b908286480501d8cf01010884a08005447970800a4008002b32550028448050028e8230008848080002cc27002884809), (39, 71, 7, 18, 6, 21, 0x10272892522481a0915fdee1d9e049034102a702558848120482454bfed8668024110412791d4340a002142110ef33add64480341221d56094fc0820a8009360d52d541000e000865f89cfca2021c2110c8ed54a204103400298e98dfc40000880082d53d0478004110012581e24c72000120110af9b0e8104803810215a39a5ea00009000829943055900409008a50aab79c82422c2820941a097104805810411f06f7ea0800b0008211de9bc812415041240c63a8d00081200147deb29254484385220f8cae9aa8800700441c6302584001121010385ea51c82021c20106ffa5e760090241028ddc12764810048244169db2c891000d008828487a2322081a01144b21aed104045840407842808c0900a82080e35f4de802011041017242a4ca2401c09102a49d4c500844850404c435ef200085080407de457850210a148809e9f86682421c281003f4c521008428502003e03752010090208), (26, 66, 7, 18, 11, 16, 0xc11872641104801068bc18e0c44920241528ef63b9124a09052540496a4010804143b0608b902420904f2b476c20492820136642242012480804a0c0d3f4849242011b1d3b0b3124909046aeca8e084964a011a80e1b01125829046863c406441280411903c3692025128045d03331440140841154910ea0125828043e66b150c0944a410addb62b10250290429860c38c416484107a1d7483125929041cd0f968c4124041048ddc0a8104a00040ce7960c84164801025117d5210490004074fd92a009082010000063220051200400000760c0144841), (23, 59, 13, 12, 11, 16, 0x144c1b8890403001e4abc112890e14b753537f4101c2064ac3aed2241412c14470dd40850a55d708cb2010204269e5bcb31219294c72e86e82418108a8c30b44482024ead4e4b0890c149c9e657f500142137d3f31e62412125fadff0544070849c247c6c81010491c7606f5120c0921edfe7c62012022cbda0e4c4064843f0c090081081487d44b0d4121c280b27a73e6042252123dd2d100850a01fb20542880600800002843001121)],
  [(61, 70, 2, 17, 5, 22, 0x3922dc280014438280de4583c100410e088327cf5bd9014038088c85dec0b00510e0a8285bba0710140080889bdbdae701500e02866e5106440544082a191fea14700410208822508c5b9020030108864611100150020206151ed7d90540080897b1f1e3080500e8201e65a0c0a05403a08174f14bed01510e0a85cd1ae1dc0040300a06da31d8441500e0225b294a2d905443828968ba4bd500110c0a8198ccbf4406003012164a2b85d01010c08858b7fc5510600301095ee5751c01400e000576b898940440300a15a51856b01110c0a855e46f784050008021570f73720051020a0137c75b110544082894a61f49041410e08252428dc42060032101474a22908150028205144bb00c0504382213ec8ef3b0141020884f1ab57e00540380813acd62bf01000c0084cbb0c15005043820132a72cae40410e0820b1ad94ea01400a0802c030c8641400e00249a84bf490444002892468b6b841010c08248f8eb6cc04040022122fa7b9e80800c84006cc5dd790144082881af9f4cc01110c0a046294eff00544082811895332c40010c082060a9834a04003200116fe789881100c82044b6cebbc0444002a111eb272301500202843d1e61110044302880f3fa60d01400e00843ccc6f5a0040320800e5fc76e81400e80043703f2340140080a00d672a6841110c0a2426aa0a6c0144082a0084fdf2a01510e0a0412c2740901443828804661e3200110c0a00031bbc5201003a000), (41, 70, 2, 18, 7, 20, 0x289b1f3288300601099117426400881802062d5a9ee20300601215a51aa9b80a89a0a85604114e481006010852a4011420281a022131b6efac02a06808149c8fa2680289a0a80f9f30bfe00a0680a03bf219f000281a0200eb6055fc802060088334fb9d04008188200b43721620282682212678e30c80809808848b7867a00022602801ca60bb840a01a800470e0071482a0680891af0c8ee40a81a82046af99e150220620811a66480340281a8200668d560402a268281191259f1808018008461dca048822260289183213a98008980a805a5703c903006210116255b7720289a0a204a46196a0082682200f778c8440401884003bfda92602a0680a10dee2067804018048036ae54da0020600a00ce2166840801880042d1456c80222602810ac8d50d00289a0a00292b316602806802109d7b2e880881802841fca103c82a26828906e96df340201a80001990c4088022602880635d6072088180224026ace120222602a1), (72, 78, 2, 22, 5, 24, 0x8a040d1a8828248a0825e66452aa00a8922828175a7d0218028248a0805d0c5912620a892282896ff0a1c4882224880a25630f88e620a806180895888014888280186002557dd133a00a082082015372447c880a0186022115d5cafa00a8861828145088841802a20820a05045a5e66208092202093f861114880024880820f4d74e0220a812280893c67fa078808248a0820e09b17ee2000122000835edd8428808048a0020d0a6b80a40a8061a081303aaa00882201840224c0b5597600a806180812e771efc880204880220b4fc17ae202882082882ad7d66d880a048a0220aabca4ae208082002092a432d83883001840424a741d7b600888610281297ae2c4880a21860a20a3553b2620a01228009264781e6880820820820877f252620208618208202e5ddb9028048a80047f13dbd600a086182011ee33538902a048a820477af09d6208006100091d5d7abe8802018402207146291a008092202011c4b5d2380200488000469923586200892202881a3cd36c880a248a0a2068d36c4200c0122010119734e0188300488042460208aa6008082002011704da0f882a21860a244c6cd9622040122010812e60d6190280186800444c2f09200c006101010f4a085888282186082433cadada008812200810c9422c08028048a0004308b3f2a408012220010ad48c268810018404202a7f0b520088061008109efc998903004888404266a28f600a8122808109413fc8903001848404218a864220a0820820906afe01a88220488022419ec455e20801220009065e3846802801860004148f27ea2088820028904f2d7d29020018480041197a20a20a88208289045e4a6e8800218408200dc7765600808610201036188aa8020018400040cd706d24088122208102bc8e43882221840a2408dfb7e62008861028801df4d55802220800a0406a3204e2080861020901a7307d802224880a0404a17f0640880612081), (22, 70, 9, 15, 5, 24, 0xba6604510010430c12dbb60e3c00510c305879636a52010030d01f75124a400512450575ba98d10014030c05c083c2bc0051041055bc7d4e1201009150159ce489c80500c3413df8d9972000030900bfc1121c001124405227a49eb2004091104698ee68400100c20119217b85000409100453c4486c80502454114077f67202009110844ea3dbc00010c2041107eb4f2020030908436826d40050245010d1f708f00044308141a31f58400800c202050fe29120040309040f245844800024440), (84, 81, 2, 25, 5, 24, 0xce89f991083104810084e5d1d44d401580c860206f962fad4802c0603014174116364006209020101aadd284a000b0180c04051be08ae101580c0602865a7d10ce002c06430101100b04210012032180008321c42d002b0180c040bf8a771b4400824880021f694ae76002c12450100f6c08a3610620301010974070824002b04814040b8c6ca8d0408824080421b76551b4202c12050110d7f6ba31005609228081694db2b9880304910044316b80f8901180c040285789cc5f8802406030040b9dd926e4062030101215bc4f98e002301808040ac75203904018240802215ecfeacc208c06020112a29cf8ff00520922800150f37e36003101808080a761bdf310158240a028535fce9fc008c1204010294f98dd110460321008949a4d3bf880904914004237422ce101080c0400851338ddb620ac0643011288760fc3102209220108408f13c98003019080401eeb1e939018824080484f6cf84b08044120402407b5b3cd51016092280883c0c91ed200b048140501b9d14b4c4158248a0224dbd5b834008406020002684ee6c810420301000933dcb13e000b0481404019b008c1c41480c860024c62101f8000c060201006145f43c4002090200203087291180230190804095df69674418824880424a8119d9020a406030012516a7f5910160321808824887d420803018080441214c806440080c8400208ea6facc80a41205004245517e7e4046090200a1206d3f8a2003018080500ecdf63ec0188248804047462a3a4202c0603011039d385a51046092200891a671f5b8803019080440cfc3aefc001824880200620fce8e2084124400123044e49300220321010017e4ea068001019080000ae09852441080c8400245287a5b400a40603000223b0101b102203210108118d0f6420210481001087fa6ebac01080c84000437324628800c1204014019bd62cf1012032180080cc1ffdd082b0481404485f73d45040880c0404202bec0bf080440602024015d20d9640520301802107afcb4e80210491000083cd062ec0048248a000018a0494c20ac0603011209d8883c00060902008004e73e28802304910040820aa4d9401480c8600040eddc57220a41245001206064c71106203210109023747a820010180801000f97c6190048240a0080033173e8208c120401120078720d006203210101), (49, 73, 2, 25, 13, 16, 0x12d828f24106300010987c8f0fd002b804040bd159eea4414c820025b82433f2002e410100a87ed76b105020800948ee40cd2029804010a1572bc00415c020224fabb5efa20a8410112798d24c910202001083c33f965802b9040409a96a93a44100800024cac1779e00284101006310e424406300012130e53dbc900a10504014bf245dc408c800420a545c1024040404200513372cc402300012027f9476a800990400013b1a6981011c000284908a7fb62028410110471fe6ea001700808022dc74af80221000408f4737b9c415c82022477045f46208840011239d7954310602001091b4021af90301010808d6425fec410c8000246007d7d2008040000228f40e7b205420a081141d5cca200b804050097cf16b4404c8200204acfead24088404102232d4b3c10470000890fffaec6202b80405086f601f1c405c820220357b781e00c04002021762256710632001090a3f0e0d802a10404084e818ab8405c0202202642301200a041000211dc976d205020a001080bbd34803190008083ecb401c81008080041e9ad3ea008e4001020d06b09900532080010606bc2a802190000082a00b954411c8002240ff36ee880860000420719f681201020a000)],
  [(21, 62, 2, 15, 2, 15, 0x359bf86fe600c8819db64519882222266b01036e20488916d0641a189323265a94f5022604c8916560e99598332265700dfcfa20c8899547ef92c084202854895165a610c8a142c932168922322503f4d5a6200888136e1a24880422084d86a999621088a1352af95e81423084b140911a408c8092b42688799233224a128397c248848920e48cd08912324441b4c55e2408c810a509edc982322240625e0c62508ca1), (21, 56, 5, 12, 5, 12, 0x962fe1ed9819127b6afaec8811126c388e498831136a9db775804104632cddde88211160efb7788801105fe361c99829114a91e1389809103e59c07898391339e8d9a90840143297f3158841141fa9ba2281418416db093c89219114cefcdf89019014bfc97c092091149e3c0590290112d79d2e9849140e6242ec89119209d74a1f99299103d3250d89319301c01d3c894194), (64, 79, 2, 20, 2, 27, 0x8ebd2c69800913309832a72805170013226132453e3edb4a000644c2248a1d124a7400488984c113f48f11f8008943019427c4843b9001326613264f667c81600064cc224c9cc9a3b5c00488184c01333d235d800984309142666a3e31000228611084c6278fb2002448c260498843918c004c0984891310505888008903019025b812f93000028601084b4dabc0a00240cc240c94f0678740008998441928e3abd08009143098424e6b705d0000266010649a9dc092000040c020093184f214004421808a12419fdc58001903089024749a2d30011006022048c4009ba002408c2404907590ecc00408980c1120dfd9bf8000123008123fe73cd70012086120847d6145f2002600c24408e132cc9c00449180c891c1d8ecd80009130092236ced1f700100660206464578bf6000648c22448c3c8d654004c1984899181e072f8000113008222fa1697500132061320458042d1200204cc060c8931a89e4004801848011231ca9380010430804222afb4090011026022443db5f24a00224cc064c874c2025c004ca184ca10e952c4e80081430184219dddc2500030861028433622f56000444c2208861f5421400408180c010c09bb018009013090221311a4f9000124601224211d38f2002244c064883b4f196c0008818440106e5bcdf8009923099120d0f10dd00012860128413ad7c46000448c2204826e95b1c000421800a104b8cdde80019430894208bc42bf00110460222410cab056002008c0404816c498dc0040018080102c31e3a800801301022035918330001266012640646ee06002608c244480769be1400409180c0900ae485180088330113200cb4db3000008600084016ac51a002010c041080270c26400048180481), (36, 72, 5, 17, 5, 24, 0xb2085da70012070903af1b2605001227098395c7225900022508818caa312b00022708838939231f00122509818232d289001127019381c9594300110501117d86537d00022308827949e5410013230992790c476b0011250191763c636f001327099375660cb700122309827173308f00130509116db01a0900132509916bc3188500120509015f45cd5d001307091354b4bd8f00112301924c2c2071000325089148af05350010070103455b85850003230892290b94e700032708931b911887001107011317722ef1001005010115e200b100130309120fed523f00102701830f17515700002500810e4d523100002700830c9e055300120309020a7e2235001103011209fb1b450010230182093cb8e3001025018106123c03000125009105499ea90001270093011645a5001003010200d0019500002300820092131f0001230092), (28, 69, 7, 15, 7, 22, 0xeb404efc800906120e79ffd0ec0048109019951693e000418402c97b3e6700130c2454d9f6baf800086002a34e11fcc004c909910aaff6ca00221808a7d0590230002242203c8b55778008820221d498bd84004890980dc043cc20026584ca6338c38b00100c04131155b4c80080202016d0870140008b0884a7761a3a0022480c84a86763d0013042441d579e4e8001961128bc67e03c0044b01945c02d7c60020580c222edfa3f00122c2611068d99b800192112049459e64000c308140b1fc5da000018002022b384b00102406000184d49800016010800b7e9cc000090080004d959a00025804a0025c7f3000124024), (28, 76, 2, 22, 2, 22, 0x91be464e810066008198cecdbc78130260489189ba7f9c8130660489983165b62813006048816b4dcab4801026000915e67511581304604889524627ad81024600c094f3536a8812046048094275158c81120600c813949c06481324604c89369abd18811026008913555cbee81020600c0133caca9181026600c19333f332b81124600c89311b5372800046000092f8735af811066008992e2698dd8100260081126494cbe81126600c99231bdf0b811006008811da6c65f810046008091b7c32be80104600089159160b780100600081151ab009801066000990c017bc0810006008010a778a908110460088903995ada8012460048901aa03f981022600c1100f4499481122600c91), (28, 70, 5, 19, 5, 19, 0xcdae77f4813030244afacbc3d60440c011272c08a5f8000500005b49ef8d204c9409915efe3d3581125006456210da4a0448c0192579a23498100500405305e6ebe00414001149edf621813070244d1ec9a19a004040010471c496d813010244114e51a5a04c1409113d274140810070040cd66e0fb604814090133d2f8358102300608c8d1cf4a0441c0113249b21fb801070004c8d1146a20449c019321c395a581101004407598c2d20408401801d28068c801030004864e288120400c01021045bf8480125002443d302952044840190098d707081025006041f5cbe9204414011106f9b918810010040009bfb11a0409c0183), (34, 86, 2, 27, 2, 27, 0x847c90ed81098430212285aa5aa492042600c08488167fee76b810981302122458ee24746042648c084c8962a22679810814302030857a5ed31e042048c080c0956e59c0c810892302032253f2e673604224cc080c99487b1dec81081030203004e71354aa042204c08089135e0ffb181098230212224b2b88e5a04260cc0848992c0e0fac810894302032848dd375a6040204c0800911c8118538108113020304471b34b86042200c0808811c15d8cf8108903020320467f1e9e2042210c0808a11672fc728108023020202450bedb26040248c08048912b0b5f88108043020208443e7dc56040208c08008910a47a4f81008430200284424dcd22040200c0800810fce7fc3810882302022243cfddf2204200cc08081907c3128c810883302022641da85e56042408c084809060d5c0c81008330200264104d1d02042000c0808010379a5b58108013020204409dcc9c204204cc080c1901c257238108913020324400b0d2da040008c080009), (34, 78, 5, 24, 5, 24, 0xf45a193a04264a042647bf8d1dc810981810912d635e96e04220e04044f045253c810902810901a31d423a04220604044a444ab618109828109117f0a6e2e042012040411da454358108908101907104276604200a040405a8face28108848101146725e5820426120424516c449fe8108928101915815fc16042046040609600ca228108038101034756726a04220a040444f6476758108808101103c21ae5a042246040648d7aa11481081281018134fd73d6042602042440c9af0c88108948101942eb9ab6e04224e04064c8fef09c810810810180225fb18604260e04244c319f3ea8108138101830c083e3e0420520406100b94b4181008381001302b1122a04020a040044082ecdf8108018101020084c32204200204040000d11ec810080810010002d212604024a0402440094ee88100818100120007d0ee040212040050000045f810002810001)],
  [(35, 70, 2, 22, 6, 17, 0x37b4065a0105000121cabdf79b0424080426dd3b6adc105020121b61685a90824080066d2dfe611081200003acb7003e061400048ea664145c009020009905f8cfb482488006608fc9c111006001407d4fb6e94024880025e5b5828418502012373239bad4804880045a08fb9010006000406553128340048800057a8e0ea91812001035061579e44218005213a4b5d5d28122001338f530db420488000cd65850d110920010931416ad64024800024ae7635312092000192496cb53442488042490eb475d1012201012254ede1460488040c85e36ab92812000131f013194440480040460403320109000109156f5a1b00140800843bdee2690012000010e7e82f2042100052030ec1a7120120001106c6e23f021408008c184b11e1180600142009485f44021800120005782f1080600042), (69, 75, 2, 25, 8, 20, 0x7efa4cba2a013220009efc91c1854a06440027d93fd2d4a042c08028fa01c30691281900049f3663be528103020083e21a39dc40826000033bf8e83dc2042808028f69326d211109900084e9984e2220003000001d199cb4450216040047a18986308004c000027306d55d84081010041e5d349c920413000099cb24501444026400013935847fc8804c80022718dfae890001800040e2285b4622403200011c0ae009604204400107696fb5908040c00000ecad5d4c85001110040d3819fdb0000a0000a1a4c2d09c50a06040027434a4b4880c2c00048e5983b5510005800010ca913d9f00502000093916d3f1c508260400332102b1a0a0c2c08048e343610a9120990004cc66d4ad9024122000998c153cea10804040123149bfd5ca800c88020627c736311081900001c47ee2a5001020000838663b3464480640012306e33ba42004808022606fbabd81009100044beb765a620303000103788bd68040416000242e847c8c8a082c080485b59650d90085800051b62f7f282a0032200015c7e011e40a06000126b5c592148040c00020d660c5e415081910001ac8f13590010a0000a34e2a848a1420444010692b5e3f8a040c08000d105485e900058000509e4a5d062a403220011327f7bc64400640010262fd4f9408008800204b38ee3b110019000009601fa0b024022000912be57efc544264402124f3abda08042c00008c9b57e201118190008192c7ce32222032001012273434040a0600002643324840a904c88006474bff39151019100808de2b025221032000831b56b8685002604001235756bb40940880024c67a58af1128190000989f131132040300009108fbb3f0546064402060d8bd2dc8004c0002240a9959b14001810000809145092a103220083), (27, 77, 2, 25, 8, 20, 0x5b1ac8ac0a084c0804269f7d36ee548264401334608e02d2a0132200899f2e070b85201110048cbdf20428a080c0804063b5ee1744042600021317997aa90a41222009983771af010101800080bfcbf4f4ca940c88024df90dc49614024440112f57111cc2241320001974f0742c85281110049b820b053ca002c0802859aaea8fa54806440122afcc0cfc2800b02002151ae8fcb94201810048a855683a4a140c08024d3f355072500060401029803ebdc284030200114bd5e66584281010049a5b16b4ac200080802052d8b4232100140401428985dfcd28413020099431b4b8310201800008a159e19eca004c080225081b242e1082404013280c6a11428303020103), (24, 77, 3, 24, 6, 22, 0xb5eb538a20100c00010b8965c89101086000291bea9a5f088043200048dd7ac1ba00021000064621e71eb020108800322e7cefa31110864002911f3bdb14080022000c07e3c3ffe440219000643e2bffd922000c80030185541f9900086000190a89b0c3080c03000142542a51a8400218000242872b549000008000300f51ed011100064000807a6a27d888c03200142377b20c0444019000a0185d571c22100c800108ac2d41590080600018448ec221c884032000c2223893f8404018000a010d934d220000c000100435da649000060001801815e314084022000c200151aaa00201000061), (52, 74, 3, 24, 10, 18, 0xab6a84771520a440031fee62fc044429000846da1e5661120a400031a47e1216508281004c5f0cd29c05208440031679e0e0a548291004c53d34b978120840013132e22082108201004c43e8b2201420a0400310d619c14504281008440529d2704084040044fd3aeba040428000843cdc7e651100a400010f2df08bc108201000c3c0e96be9000a000110e2962de8106101009131f8a4d204108040210c44a952810410100902e6ab8761500a440010b89de6c414021100042e0cc6c210006000040b18d027010020100042bcf6e71852084401309da626324402900044271767fc9400604014098e33b1c100101001025feb6991510a4402109586270e448290004c24b33ebf10106000240897ce36040028000042211ddb114106040240881c814c40218000111e0cb68201208400030718e31ee40218000511bc17898101860002446e8a63a2140211004418a76e3e051084402105e794ab45001810010167bd9f51400a04001055da3a2a5021810051111c003c140860400443f23331c50618100910da0235284004040140356e27e6408280004c09e275fe1020a00003026df155e5402910044086b960b840080401101f8ad6fe002100005106eda9329000600014019fd8b98044210008405ce511a84084040144065057d25002810044), (62, 68, 3, 24, 15, 13, 0xcc04e4fe021100001bef2f9d5201800041bd74b9c92a0910040a4702f6922090004095ee9a0d0a41100488a7ea71a024100008873f73ed08501004987159515021100041818e7e5d02410004866df91930010000416009dea80a51100095ec9fefb2008000405cf4285c2a29100805ceb880d0a01100405bffb26b28581004959c7411602210008058ca1d1f02510004956a9b4890a111004154989da60a111000153cb7b142219000014e92ac6c2028000804e02c5df22490004848a1215f0a51100493e754ccf2219000413e19b6982a49100083d42af092259000493bf5f83e20180000138e699bf0810100413765fb7628081000034cf4ea628381008134a7ea59284810048330680c00a311008132a9fbb120580004931e75ee62828100802d8db4f62249000082d4afedd0050000492d3ed6f32a49100482bb8cbd80a211008028336cb6203800081264d451920480004820c643620a411000820039cfa2209000001d19489f2808100401b3effac284810008193066672a1910041170fcb28023100081165d06ae2a591000914a9f21622290008012411e9022390008111d7aa5602510000910637cb82818100010f5af0282048000080edd1a550840100480c49256e2259000090c47ed0c2a09100000bbd10252818100410b27a2e12a59100490aeb83cc2a19100010842e43c0a011000007e52b8428581000902653ab02a391008100b42dec205800009)],
  [(39, 65, 2, 20, 2, 21, 0x7efb3ea002611004b934b168010328003b7fa8a8401040090dba0d7800440a00159df632002211000a29ff250012688032ea98708001040010734a006000ce0009b5f404a00061000498e035d0010688012bba04cc4011c009155953c400482200824640c20004d00064e7382100100880005cec9744000900802bbe5b420092004c15dc2521000900220a85bf5800138000651ddbac4012c0098156fbe40001200040ab4deb000630004854d64988031801241a4806c4002c00880c7bf8400492200c062c4a200021000082a16ce8000120000150a8e80003400090a811f400092000c053cca3000230000829db92800112000414e82740009900030a2e5d620046004102ae9f51000a402200db855880038010202a48a80082440080149a3a200448041001b3f50022250008001f518802180120000016c4000c0080), (39, 69, 2, 20, 2, 21, 0x7ff5f0c2100610024bf4b95c50801080105f395b390000310009e08dbf5a2044ca041ef72c9fa1004500247683dfae8810328103a46bc834008394009ca13465a00014800464e32dbb100670024f1c9c1be80007200135bce46d0408014080a6d3063a20444a0414e528d9b102231020a6c7c9cd081048811135df1ae800094000399058de4000ca0009cc222f8c100244020e407a81a0800620113163cfd8c4089c40838ac2ccc42041a2044c4aa31d210201102021f29cc1880138010706aaeec840014008174887a7800010800439be1873102671024dc0945028801320106cd1ceba000190001359c161562009e004ca75e945d1000640204f8af5f988131881245f1678080011400112f8ae5f40000a000094fde5ba1000d002249dd3181080268013246606e680081440011bfd9c34200ca0049893b1d1d000064000448953d18800780112234c2bb4008094000), (17, 62, 2, 15, 2, 15, 0x297dc3c8a00180898261a6d18113020dc2ed12760088091621dac3f00300049666094ca04cc09356656869800402211277307e00c00923be4fb3480240260bfbd3010004800327d2926c8012020c9eaf6b3a00c809326d7a8da8026026489723cfa000808122536f1d8131024873822a0a00800901c2c2131801002086bce40aa0444082), (37, 74, 2, 20, 2, 21, 0x2403b9fe8840004008054d82b33400204500051ee83a4d00080140003cb58a264102245020ced017f0f00089140033038c995c10000402008cbc3b5304081140811fcfe993410220502087ce4dda484088440821b0b56f851020e5022460272124840904409017f420efd10202502005d2d9b56800894400316d7b337c0020c5002457833987440039008915628f9ec000044000453fbe476840984409214b5c221c100204020851ee69d50400110081140cd93751020a50220499ad4c484009400830f4e899c2102251020c39bdf22304083140890e07c11bc0002040008345a68c880099440130ccb8724a10205102042f3413eb04002100880b4fd5315002265000c27bf2e9e840994409309c93e1ca0024510044271249b4840914409109bf97fd2102491026026630c61040821408808f66aa4a1024d102642106594900082140080810fe04c000244000c20180ba14008294008), (49, 75, 2, 23, 2, 23, 0x7c87f03e42008c40091ec01185c84089888107b73bb459880073002276b23f3521024622048ecfef64aa2001490088cfb868dc800198800279b5772e908105110222fe7b6af20024622008df65fb1240004c40003b1e5a79c84081888103613bbe99880033002066a24f9720004e2000ccc1f343a80041c1400995f0f0c40401180012323aecaba8010525002245c84fd41020a0a044465242826200ccc00938b043e2d000828280110cc667290000710002615b131b21024a2204c410c751aa0001c9000977a036dd40001920002e76f411a88007240225b65f46d20004620008ac367ddaa0004c900035771cb9404001800102adddf5498800530022158b9d1320020e22004a852cc6e40049444018509b6a65040098201069f254bf9001051100212fe356b31004660048a5c67c16a0041c940094a89131c040098001068bd483390000310000504b40d9210266220499b50833ea2004c90083334bf5b48008988800657c9b1380001300000c7a48de940000a080040e363b5aa2000c900811b3d0924c40099801062f162ada000070400244204c89200206220008333d2fe6000ccc001304614b254000292001008401ec98001330000c0e1353320000a200040195814a40009440018), (34, 71, 3, 22, 5, 20, 0x3fbd3df121021110207e8daada800460a001f991a1e48400c40083ca0461e808118081075d9507d200251100469646552a20424a040cfc7996540084940019b8543590013888026cb526630000700004d950936a6200260040afb7c55d00004100012d97dc1988019801063008e8b410210502045cbf68e80006080017b991c7d4400c90082f078aca9880298012155e82ff20005100042109f17e40046220013f0b3ae4800844400075a0140a8800920100e272bfb000030000098ae865a4204e220492f455d0504004100804313c679880398012464452a550001240000bd5de624204a220481394f79c80004400001fb768e900018800043f6575b200071000482f9a1d6420462204103ea1e8c0401c000920654bffa800192000402a4a8930007300048029f2ee6000660001), (53, 78, 2, 23, 2, 23, 0x270a2b7c6020004000808c2ec542a0011305000e1d693c4682041c1408979e9eaf0808021000241a944dd8ea0044c940036197a353a001010500018446df8202001c0008960e868d5a0811105020952e984d680040c14001545ae9cf9080071002254bc0fe4aa0040c940014d63ca96a881112502092ca2364282000c1008149366ac480813301024d1ed96a7e82044c14083470d73ea90802710026518fac94e02004400082458e4935988131310249060e6cca620444c40823abc7020988027300264e97fe58ea2044c94083393f1367908107110224e44ab392a00444940023907ae40908005100220e25b3f7ea2040c940813826f58880003300004cd99407460204c4040923606f5fea88107250224d74a624a42049c440993572e82298813331024cc62914eea20414940882fac0e8d90801310020cbceeb3424004cc440132f3904a798811331020cb433df42820014100882c6cc428a00003040004b12c0fd6420094400982b9a1079988025300260ae5909fa42000c400812b816c79908031100248ad1b81c2420004400802b32c38da0001304000c9f7653ee82001c1008926cee0f7808027000264991598ca4200cc4009325d91f89a0810305020496869ebe42008440090228b71d4a0801104020888ca3f960200cc0009321f1cc10808005000220854f6f6e02044c04083207e89908080250002608014056240049c44019)],
  [(61, 86, 2, 27, 2, 27, 0x29b53574f220440e001a816169fd37900250291082055d7437a4220c408041a8153b8fc2a88011028002a0544af68b82201408401281505784df8082102810420531a2c16e220940a4412814abd4c0ec8831038106a051fb0b7a2000940a440081432dbc5bc0801038004204fc3c124b220040e0012813bf312d7c8001038000a04eb67027c2204408001a813a6a9fc290021028108204df7d01c2220440a001a8137cdd2e310021020108204db4fe05f220840e04128136b6017580835029106204c9d22492020c40a041881326c02bd80035029102204c70c2b46220040a0012813170e98b88015029002a04c25c2a92020040a0010812df4de1fc8805039004a04b47eb44e020440a0018812c180a7308815021006a04ab9bd346200940a4402812a66bcb690005029008204a90717d7200440e000a812a10fe7988831028106a0491243a0c02044080018812403bcae88021028100a048ee8353a220840a04128121c720c980805029004204852f287b220540e401a81204fbd338000102800020480c5432b200c40e040a811ff18e02100050210082047bb047dc200c408040a811c5664e280011028002204637bfe9a000540a40088118aafd5c100250211082046274ec4e400040a002081187f8cfd88031028102a045fa5f8004000408002081169848e688805029004a0452fd51ca220540a401a8113d17097800210281002044cdc84ec820040900108111af9bda80815029006204427ae846200040a0002811096bbc8c08110380062043b1299fc820440900188109c2dad888005029000a041a47450a020940a44108105e0298d8000502900020410f954d6000c40a04088103eb10e9c8021038100a040ec5e40e220d40a441a810380376d88035029102a04080a331c2004408000a81), (59, 79, 9, 20, 2, 27, 0x132d6bfaf1104005020963a03a5ca220c00a041abddf81038400801000156c16ac80c8820038104ac2ed3e85110000500095794c9c1a220900a4412ae6ec8654041001408215910919f100040210082b1b112281102004000d562c4eb2b220100e4012aa6249c3c440201480255323201fc8800038004aa56b4c5a1102804200d546cfc46f220c00e041aa7661c57c440801400354c1b640c2081002400629798574b0106005020c51f75ee6a220500a401aa3d2adf24001a0148811478c54d30081002000628e89c29d9102007000d518b366b8200c008040aa222ccb5044020108025438add42c08000380042813f9771100400502015004e62f2200100a40029f1df36ee440a01c80353bf865fb88834029106a76ade6250102005000c4d0392cb7020400e001898608c00c400001400052f271dc08080402900425d090fa7100480522014ade4150e020000a001095243cd540002014800128a6b45f88034029102a4892c81d0006005020448e8f7b9e000900a44008f6a642fe401801c08151bb43ced8081402900623483a8279004007020145aa58d92400800a04208a191477880100100841131aaf2f20800024004225f9e4122000004001044b188a02020d00a441888d7ac96e400801c00150d41beb3c8000038000a0d5d3f8f0104805220841a974cae000500a4008832878a008012010884105236afb88030028102a09035def2000805201040df5e3b2200500a400a815d8a8dc80120148841029ff45008830020106a02f9bdf710020050005403b6291e000800a0400804232c8480000140041), (21, 75, 2, 25, 9, 18, 0x50d6e696400230008017889095622094882402e2af3d2440029000804edbebeac80152005009c61d2f4a004a442001301d980122014802402571df22480108108004ac1fe056082182080092ae156810022000a01215346714001480400241e7d1368020a0080046fa965088811000d008ce7e48a90062040a01188a5463220d48834022e4f2d720408800600454ba339e0811800c00864b2c34c100300100109bfed68820c608300212cf0a04041881060040b429c848831020d0080e076c39102a401a01), (55, 78, 2, 27, 9, 20, 0x349ccfb2c4010a040201c16cfdeb100228002806f4c5aaae4018e040a01abdfe9011004a91008067949f2760410e04100196c829871104a91048065105ae64001aa4408018fa86ddb1006a91028062445033e4002e40020188ff9a1101062810600620f086164418e041a017ecd326d000228002005f50c86f44018a040a017b1abca1900438100805e6c1233c041aa44180176a02fff0004a9100005d6ed714c000aa400801739ac511910238006805c3fde18e0418e0418016fe3ac2b000628102005be37a6a64000e0002016f869f151002a9002805b130e0c64402e40120169dfc2ef910038004805a5a447440010a04000162ff8ca900002800000569dfa5fe440ae401a015769c20d1106a91068055c4097948012a44200154a160e19002380028054ac28844040aa4018014f60ce0b2004281080050aaff95c4408a001a013aa070699104b9104804cf90642e0008e00080132ac27290104a9104004c5c1f4b44000a0002012f523e35810238006004b7a1b7fc0410a0410012cea878d910438104804aff9b64c0002a400001281438a11106281068048a30b86e0000e0000011e5029af0102280060045d58d8ac0402a40100112b950631102a90068044ad35c644002a4002011146e2c11100280048043a06c4e44402a4012010d2fcfdd9106b91068042ea6530e0400e0010010af571792000a900800420faf38c0400a001001020ba48111042810480405a41ec6400ae400a01), (55, 67, 11, 18, 11, 18, 0x19fdc6982000948803156a443844080006d4ad315788831020d94f6a1018100600111897d8e4400800841ffc738e444108104be8bc55f808252208755da1c0410210018d6407c7c200c00815a92149408012110832cff523c8823020964499693010420410b6f3df882004000156c6e3404041a91062d442883808010008598a3916010200018ab9d02da20094880554db2a890400400429f23e44c8813000d53cb858390026000aa567dcbc4001080412c113bbe440b9006a3df2b098803522053ff0bf2d2000a40207f9cd242220d48834e90f1d04801081081d16f5d988001000136cb5a619100e401266e0c7472008c0804c9fc925c0018810218c1b472c800300012c6df2a70102a401848b41e1b200cc081489db983c801291080fd9ccc680811000c1e76d8911004204023af12bbb0204c00305fd39214401881028a0491ef88005200113a795f591066041a218cf4fa22094882441dfea2c040290040770a93a80831020c0e7dabbb0002a40081809bc6022010802419f55974400a900282f19088c8803000904fc0aa611060041a07514972000d4881008e7b3e4440a9006811be0c5888052009020dc0a711022001a0417c96222004002407e1f5d8440a100680556fec880110005)],
  [(39, 62, 2, 15, 2, 15, 0x3ff41c84a0014001dd5a5e1dc027024f5d25ccbd0090091c281bbd082050086cdd866c3001c08384f007684026024db501c3bb00040806a13c1534006020d8c8730af00140815ffe4e864002020977b6eccc08180235d016741802500455b7ef7cb008c0924e9648bf420002813716a7f90080090473d3797402202490f0499d609141213ce794e98207008ce476e55708040a03564b0d3c0210240bb875a1b00940912b27307d82010080ab2b9dcb08140a124bf7f2a820300888b55e4c808100211f5fb1f80202008873c6f71304160811ceb1dc202440484515e731508100a111eeef2d4004020446742c7f080c0a20e418bdb4202028834600b1704960910afee974c207028c27922ff5041208109bfa7dbc0030208253c799c009001104f25bfe4124824411093b5508180a3), (30, 73, 2, 21, 2, 21, 0x2902f2d141840608145101cef5e04205000a1850056f9021008005040f2dc748100140020602b1ae3c0800e00106e6597a5e0c1050608172e71bcd0010280010b85574f183081c1028d790963fc0000a00002b57cef6a0020100020588e17f704101820112bb0083f8300041020152bed1a41000a080029d36307a04207000a32d7e2e99020018004114d52b428308141028497eb23041040208040475f2bde0c201040a0237e301304122820909177004081041408204820cd4ec1800e081063216d35e0c0030408214fadd2d00103800118a231be582081c1008c2f4a3b441800a081021683559a00245001210b1711870410282010857bc83381080c0028824d404d4004060004408b6500e0400100080), (80, 79, 2, 24, 2, 24, 0xe1a9573d00c026408127a103b11601004c81004f3e2bc25c0100090004165f75e70800001200002af46c4350001264040275b9d9ec681824a8182469e71c32402011102080d36d803f8060832060839af4c39d00800640800729e73eca01800881020652edbc9c02051103080c8b3de5b806091206092848dbd3f40c02340812502f6c5ba81820a818205fd0e0b1c02001102000b6b2a6dea06001a040826c6c75fd000146404206d8af20ce00020c80800da88ba9a403040903041329710e180009120201264ded53f40c025408122c535755601804481024980d5a07501049501048ace48a85802013200093598b7a5500810440c002b164ee720182488182455131bc2c02049903009a7f027a68020832020834e01c9cb00012440402291bd5c7e0182088182051e3892ac03001902041a0d33b9d8040232041033e3c44fd4040234001247b353016008204808208ec624a14010019000419aec09e2806093206093345bbbc7004024400122685fbdba008008800204d03f5b4d01000d0004119b7c822a02013a0009331bca0f9408025408022622363de00000c80000cc3e3be4401048901049181b8a788000222001012d24520300812440c02258e656a6018048810244a98fbda40000890000914ea360d8020932020932622857f0080424082044c42d532010004810008945d210c020409030011280e2668040a120610223a455dd00814640c2064701dad201020c81800c8b1800fd0100150004090fd289d8060012040821f1a58d90000244000223db3188e000008800004755c90bc000411010008e91263d8000212001021c9096ab40c0074081063845647e0102448180486e05a6f4010089000490d96e25c8040112040121a74d8e94080054080022e0ae7e20100488100445472f52501009500048883174a68000232001030ea08aef0000264000261b9e4af680820a80820436b80edd03009d0204986b7676a8020922020910c8e909f0001444042021757f70280000a8000042e5512540004090100105bf50378000a1202102094442cd40c005408102073e340e0082088082040e418aa501001d0004180f42668a00012a00011), (20, 71, 6, 20, 6, 20, 0xb4887ed300c0040810ef9bf87a8180681025c1fbd4ec000090000b78b03088020820208684a77d900c0240812bfc74d1e00800800216c4de374000490100a48c3c2e806082060840969fe30081440c2068d72d9a8180281020bef4c48d0100d000496b8c0ab80409206012baeaf33000144042054a43d42010208180097b87c6c0304903049096718780209202091faaafa500402400121693c3f601004810041316109d01005000401fe018a8000820200)],
  [(50, 62, 6, 15, 12, 16, 0xba6053b69327a38a157dd53c041e0817c54ed9513479385a5af9c920c9e8c267cfe68b034793058efe6cd24c1e0e25d4af2848324a30968847d724d1e4e257ea77fa8307830946b159624c928e2519f72ac9323238924bfa784441e0a144a9896293030389095a4b540d0c4c1401604cc9224a188cd6610ba088c8423311857a8224a108c7b860ba090c442319bd0a901479204c3970892490c46230aff33503078304acf0cb1a0d1e4c229e7412f03030304a6b024c4451e4a1298eb41702479104a610fb820d0c4c227dc850902078104925e2af20c8c8c21d6d70948247910866d05d944c1e0e11808aed3130303845f3288b2481e06216557bac82030108570b506c491e461149e7a1e924791884c4eedec450c4a1130da65492232188482f0f3a480c0620f1f992c8227a108303dc8f24d0c4e20a9a6fd88303030827190f32489e862084d75cf134313841fbcfb3c440c0a1056ce06e82078108072105bc480c06101c6d37b1207818405f37e34490c4610050ec130243110401439014080c041), (17, 53, 11, 10, 12, 12, 0x10698bae264f474ff117db30783a23b9b9399191d086a4facd0c4e6e6d916868f262eaf2e2d303039503fb5d913d0ca5bb7f48d0c4c52b6aa7a48623205a24c3247918a2ef0cc91190c4a6c01a8c8c8c21d1820060606097b094b2078181e81f4690180c08a0c0e4d1e4e00000ec448622), (31, 67, 6, 18, 11, 17, 0x151e301bb134799386617aba72248f3230be9042f040d1e64c17b179b308983cc1c2ea2048cf130390385cf7a4c9226872270b954b1a3c481e60616d3ceb838921c88c2d0ec940303439130566502dae060f3060a87e95854480e40614ca2c0998123cc88289abe5e5030390304f32568ce228f325099fe2b964090e44412ba973d009a3cc9c051e7a10510479908495bc9a3e028f324091e0811b4041e6081209549380991c91c03ce1f2e4134391380746a1162040f30208d068a0684c0e40e00c6a7eaa8883cc14213214a3f1043910841ea3b4122207205083957cc6c401e602103ef37490921c88c006821bb302039010409c969ce22872250800d5923c400e4021), (58, 75, 6, 22, 6, 22, 0x3436137fc0d1c493260d069695081a189244c1a0a4854f13060c0c1c3167913e2240c18181862be317844404310050c291b0da818389260c17e38fdc310060c0c042f608170e06062490305d0153422089084142134a92f054912108286261a8fe490147124c902bdb3742a048c24191057517f5920d184832612d1cc1d9818309060c157a66f3511040c04142ab91da0a048e249910540bd71fc081c493020a17064b78121090444140685c5913050c441c27c9b2aa602842411204f8436584050c4922409d3cc9488802060202136243cf503020c081826b49623202042410204c7f9d1340d18483260985a7d31812189244412fc71e04922021010c45e6c55d226061890384b91612544c0830207096f10520890286220612daca23a830212081845627aec2028c2419204a57cec220c8048046113fd1b9e808309060812712253111060c0c1424b694efe260218803848d678522408084041110f12fdb808389260811f8536c30103124810237e3fd310684241130868dd6dda08804804210cfaf33d898206020e1183aed3f12040c040c23004728106442412308596b585408084820208a2047f048121082822133b5b550302120818218da6cf2240218801843165765c08184830208445118589010604061080fa753020312480820c20048a0684241130417a43f82089048142101aa61cb888106040a10323352703040c04182060de63204081808104065a9baa09084822210058ea23419209028c2)],
  [(52, 59, 2, 15, 2, 14, 0xfb8f98c80110007f6576ae9020020be1223740054801f5bee81ca025200eb4ac1e90052403b3343f7400a440748a5ffe6004140e4832ede604c091c7f5e58c8080121894a3114020040b0a783e830020405db68d16a02d201ac97e0fd808052157ea53f200848028b551257006140d0787dc4c029281986460be0010203232b03048030406214a61f30420413cdc73de408808373c2bbba4008200dc26a54802840099f07f788054881b325d6ec60440905c72f3444098022ae0fb81c02844090a5f2672054841a125ef5ce02d28141887c18818012482638d5b8094a00fea59d610220081dc0ae5ac0002802d6a5f0881421044bacd45882b400c96239ce9056881921511e820c40121dda0f10419802637a4f0918310248669b70c30528410a2841ac60ad0830e017b2c81901260516552080940000873d3d40201080108dcaee004280007e97f4405a002009fb8fb8110a4000f6cdb30168408019d68320a510200243b4a405a20200478cec80944000041fdc30128400003242020a5002), (23, 62, 2, 15, 2, 14, 0x24ede4ad4a04c2116d63a2438803000560b4992c208c0034f1b3221100842012fba878f208c10349cb57c9200208051d9086c5002110040c61961c022040d027cae74e04c291407182d4b0120a45003a4516c0212803e499b2510020204da2efc3240290813426158f18030204b33097e280482112c68db681833024cb06f0db0a0442102ab0f60f28030804a609d85d2084102281e64a9a8010800964a93e4208400221b167631012024485aee992608c083), (48, 77, 2, 19, 2, 27, 0xeb4d75f500000060000f58376e3800200300806a720f4b4000805821033d731b36000e02c528197a56b3700020660049c1d0cbbe8001013002459eaaac6c00081582106bcfbbaa200000cc00135a2198b900020460041acd7e61780000230000d6126025c000410880049af4af6a00060ac50834cccc90500010262008a40812f58001813102451b988a0c000c058a10282a92cda00020c440123b73c1c9000101628009d1ab379800300300a04e5ee1764000810801046ec149ee000004c001130f0a5b1000602601489614850f80008331004c9eb61dbc000c18881244ecfdfca000400c008121888e63000401609008d348899800000b04004618b555c0004158a0062c10d702000208c40031144758900050062100885863e380018291420842219f9c001409884221eef5ca600060cc40930df306d50001006200086e377ea80008291400836454654000015820061a7af55600000c400120be3f53d0002062004905866fc780018031020429ad1ac4001c0188502129a260a000608c408306ed559300000420001027070c68001029042081046effc001c09885220573f20a000c02c1281011b3dc1000304220410067d49a800280b14804017be16c001009804220088901200000a41002), (23, 73, 6, 15, 4, 25, 0x433e4353600040100210923f89500000280027b0149f1800100c108361496b4400180609416f2215fe000c0100a0a71160c1000602805243a7b17180010140091d85e68c4001c062940e288a41a000003040054cdbbbb0005008840269c114e800200402010f29b5ec000c02204083a7589600020510043afac52900010088001c89794280028144210bc1efdac001c0a21485b12debe00060510242cc2128f0004018240150663e380020140210a52b2a9c00140629003e0137b6000e0110a00b2c54510003018a100000513e800080c500)],
  [(59, 70, 2, 22, 2, 16, 0x354e03b78904e04019d45284c004018000226dd8d5b610060010897d61b3824118100624ee6e0d91046000988ab8a2b480030004261170cb4c10460001876de1498a001010421dab0f0b4104e0001968c57aac1042020085a2ab947481080402166d3098964108102418c57fbf0900a040015a5bb52d64028102056618a8749042040104baf023744108002410476693d4004080883e396f7a5401820220f7a9ac28100e000093b1827165003020224eb0604040108000213a4ca8a31401820020e3bc01bd4108080a138d6c34f6403810224e1ed9efe100e0010937d343bca403810424dea2e3e4900e0400932b08d664403800224ac95e4e0104a0001129ec09115403820224a46e805440080800128aea5f410030200249a56d62c100a00001201e4f0510010200208065bf7e800c041091f8476b7a4028104047c066ef4904a040111e83367144138002647695fcf5904e040991ae1561944028002046b398d0d904a040911a216608440180022062bda03e100a00101180e80b5404200028455114ed18108040a1140e5d9e14038200244525da52000800101106a60135002020204395826529006041080df5ee45800100042032c552768108041210c04b6a244128002442b913b7990060408806b34885a0020104040f3bb3dc9006040080311204854028202040a0e3b55904604098012aa0b6140282000400831f7e010800121), (44, 75, 2, 22, 2, 21, 0x8678ae7a83201c2811307d43bf105403860225d38e93260880708044b8f563f3c1500618088713a5eee82800830110be6e6c39050420602853e8e672a140020a084260482344200041010849e083038102102804279f68f9900042040084f22beaee020840c0109dc917fd4281081412139550026808010300027017332304042040284c398affe028070c004981e95cf42100e101092eb7cab9840210202425c8eb2b906042050284a8216852020020c00414e7529bc280081410129843e99822014201024fefae110a4028504049b7284120080508000914bbdc5c2100a101011f968d5a850018282123e9fdf650800204040475c47396020060c0048d876b07c2900e141091a3166e980200c20010323f573f01402860004647c938610006080848ae75e7ec0900a1400111990f9c80201c2001221f8dc9f0640185022042a31d8e048070a0048661aa8f405006180080a4624f78280183011213c59baf0a40185042024b77e6a048030a00402ee31f14210061010805dacd3d82200c201100a8d82c9050020602040f758bae0a8050c0408109298341900a14081), (15, 58, 7, 12, 8, 15, 0x346fca7e0141405a6bf791c04040164f55f28020100990f3ccf30507015ecec5af8081201729e53f70606815bed5a1c41018055ea298a40a0482569b173101812053a3e869e0105004af41e7dc2018091558914d00060043f10e194281a0906dd367902068040d57cbcc041c01), (20, 57, 9, 15, 12, 11, 0xf93616f4066040f05d04a580b0c036c50cf602180052a288ca408c00194394a49046100c4e2edcb8330a05e838ef70158202b2eab46c14008254e02d8e0a604128112fe08080c012b77c65c2184045eef69e60a030128d35317080101140b01b98500a0889af2d10058200411f4a5604c2801c81e879056180874c1b168030800390074cc29850408999e5404c080)],
  [(39, 68, 2, 16, 5, 21, 0xf7b9663aa08018620efa019c8808010620e2534ecc800110601be9d6e0e209018c20b732ad12c000146009d76e6e4c001146019d5928a620811842194e97692a09118e218609aaa8201018c007e30a4e2c09114e217a61d976801010e0078bcb84ca01018e00767e4474a000186006dcbbeb54000145006025b75b0080105205d22dde8809110e215b0cdf4b400114501568ae79aa00118601556d6390801110e015322e6b8a09018e204e185c6ca081186214b579d3ac01114e014819beb2a01118e013ffbc880c09014e2039d6e6c42080184203127c578201118c012da81cdd0081105212a7fb63e80811062120ed29222001184011dbbf326209118c211c2841eb000110501193b458cc081146211937d42ec0801462014a93f32c01014e001167ced8809010e200cacfecb4080145200a027aa500001050003cc2804800010600000b51f3408114521), (28, 66, 2, 16, 9, 17, 0x894aa938b000508056cca0e48a080822059ea11ad082462084b5c5efcb008101212bd37519080462004ac22c6f2c0114a0127ea5de10820200808f650225408141211ee11d238820600846a969ab4a00182011956a5b008242208055ca6356a0108a0013afbc29b024528844d67ea3cc081422111e71b3aa02402880432e15d080910a210fbdbe152800208003b151c3ca0908a200ad60cc128046280429b82b54c0104a00095591f4a020408841da0846b40014101057d77735020104800eb4e3f4c0804220027492b7d0001040006dd28b8c0904a20011b54f7a82060884000d3e34a0918a21), (32, 81, 2, 26, 5, 24, 0x860b86f1201021000090c190c7e88a01108022806054fe664404084000442f100cabe0020420000216d0e1015001221000410b580478388091080028856f3fe39c504884011442b2df3ffe080446008c0158644953140021004100ab38e3c282091180230853d4b603450088c011c029ea45a4228204200822138e03b3b0410210040109b66bea68a08118021884d4d8bd0c10088401100261ed0a56002446000c212ed9310f000023000200976bc3828008118001084affa74041048840110424930410e282446008e2123c772db1000230003008eddfaf882001180210046ec4299480408c000a4236e0551e4000420001011962815f1012230007108be6c8118a001180218044f2569dc00088c00180222a5e6aa2020460006210aa7881f20002300028083b4621a88011180038041932a56410008401000207d1f236082046008421), (30, 77, 7, 21, 5, 24, 0x21473360a28200600862fdad828d140001004107bfafc878a080080208bdfb29bec00000c00081684bbd06080406008c0a0004a31041203004614cb944f190080080004a500eac7400080c001810bf0eb160020060004274670e431400030043034b456a7880801800189965eb43c50480401144ba35dbae282406008e256f8a05b001203000612abe51f28809008002893f34cc4c800004000209e989c3e402006000524e9dfa11041001004012344d43d820000802000e0496614100804011006eb5b0c240000600050313563ed1402010045013c542d98800018001809052bc2410000c010802dfce70e280406008e011a325850412010044108c0f2588801018003804044813c10400c010841700d37a202002000220b5ee4f510120300071)],
  [(11, 54, 2, 18, 2, 5, 0x359af1ce6080408b581f017a08060d0fe64d482016ba7537f2a000132e8fe06482404772ec96380800e1f75f0c4820036dde802900900a214f4b5a80011a215b3e78080464916584e8200), (22, 70, 2, 26, 2, 13, 0xd88482c90878084806e6e7e15c21a0210016ed4566f007008480569bd64082520080015a01c0010090004901631f6db026200804056b09e9208980009014d60196822200004052bf1250095802080515e8f81422200104041c894100998020900f05359d40100010013639aa320868080004c7666240216000201316d86ea09780a0804b2e7b0640180210012a4c356c0878080804611029e422600124008d84cc908480040041586272421600120102fcf5e609680a0004007a4d70212000001), (13, 62, 11, 17, 2, 13, 0x338b295dc123004176d60e60040c0005058a649e1030009362b635e84040020a653e91012100401fe26acf841c04247d987f2812701411d7c3e75041404006456c36e006010911c4594484140420163af38e004010802f2d551041c04040a31513c1250140), (24, 82, 2, 27, 2, 23, 0x882dd30f80210f8084805c9a924c200843602100161953a2380200d00840054cd9710e00842e001201399326a480200f0084804aad9261e000436020001287cf9718001098000004909c415a00042e0002012405316280000d0080004893ccbda0004a60080011ee0d45680000b0000804715901320084260010011b8c85fd80012f80a08046018683e008024001001167fba2f80012b80208045226a0620000a40080011045648380200b00048043c69400e00003c0202010e4efc6280002d00a000436b192820004b60280010a53794c80002b00208040f1f843a00043e02020101d8b39680002f00a080401eeadda000024000001), (35, 76, 8, 21, 2, 23, 0xdf952cc380010380008bc294861800101800006567a70e800003000085ffe655c80200500840455d5cd5800005008003f118d0e8020010004038394e2080002500a0033a2facd802003000482c4d1a6b8021038004827e6c77c8021078084827c18afb8021058084024b3f8d280002100200247fe2e680210180040201a5ad3802113800491f58a792800113800091e0ef889800107808081972dcae80010580800192677578001118000116592c6d8001338020915d095c080012780a0813b100f0800007008081169c97b800013000091160f93f80012580a000e19fcc2800033002090de89896802111800410cfcc474802011000410c51704b800023002080a0d86d48000110000108cb860d8001238020808196f2e8000310020107b064458001218020006facb9880002700a080462016b8020070084800dc7eda8020130004900dc3db780013180201)],
  [(58, 78, 2, 27, 6, 20, 0x967a2cb28010300010822a42b35b0260c004c218a28db0b40c020813021df40641d03208204c0976de4e5100c820803025d39d91a50100820440874312f94909838003085c0a8207b0200c004c006ca95c2d4008208110058294f8ea4060e0004215f666458c0c0300130217c25450b0320c004c095c28de468088300030056dffcf5a0300c000c08545578c700882080300542806f8c002082004014dea6c6a9090380030812111c2d30220c004c0145acbcf040c82001302516959f724040e0004203d3b5d88801830001084e701c4f44320a200c093854d1b3004820801024e101c2b30060c004421379f3909404820811024dba08e720120c00040936926523400020811000cf5cf9730240c004c20300ede6a809830003084b46c6f824020e0004012c63e4c290803800300094c0279903008004c0820f18f1690483800102482fb2aa20020c00040120264e12c0083001100473a9d19b0100c0044081954a6a4900038001000640b5d520240c000c20161d6e6510482880102456278b6b0040c004420157ee274c04830011024547661e84120a000409100b0eb410c8280030243eb4b1120320c000c090c1d496110802880300030692b6c4300a200c080c19837c10c0280030202ad258944220a200c0105c6234290c8380030241571cf9a4300e000c08053616794088208130041478583d02008204c00043c2c16908838003004036d61e24100e00040800d5944a10402800102003564f044100a20040800d5938b1000288010000205d18c4020a200401), (42, 72, 2, 27, 12, 14, 0x885a5332909e00082163dee2ff4008204001539865fec04400400845881c3140c820480941ae02f740482040093ac56060c08c0048013a2d80a310ca200809369de512c09c0048212f14602b00c82008092118cf08901e0000212030608c104a0000091fe50b8b104a2000091b77581c90c60008081755bef8901600002017411db2c00c004001156590d8c01c00402112b13b50804c00000910e8953610ca00080910d5788cc04c0040091082fcfe900e0000011074467690ce0008090fc2c21100482000090c547c6c80c40008080c423ec8801c0000210c2dd49680cc0008090bf802fb10c22008080a934d6ac0cc0048090a8544e8c0c40048080a16224010c200080809e96a5a90960008200997f8c3408820480108e96073108a2008010844e846809c000821077143fb008820080106174dba904e00000903d4f5d7108220080002b3425a908e00080100299e1d100220000000299a8810420000080027a74f100a2000010013c46c90460000080013c18d1042200008)],
  [(38, 66, 2, 18, 3, 16, 0xb6a9eb7920810804a8f478f8a824620138537c04aa08080049feb77066824200137b652833a08188049ed807c408244201376654d47a0118800d920e7efa8006200258e68c0c2108041092c24efbc052011403edbd32aa0108000cf5f5edd40124214036470af8a1508440ccad0468c8044200331aaa241a0508040cba1030f2840210022d5695a3204108408aaf871ca81062102293ea7c3805188404a46346c2800200022737ede18041884009a994ce20046200123a1d843a1108400c8a32970a014201012250935d8091880446ea61f96010201001b453bf82049085085f05d0f88520114215cb4cce20510840c55f5e1be00420001126c72aba040804083cf70d0e054211010f1d86d48100840003bac4f46850211020a22311c8090800441b43083a8146210305cdc4c4814084400165d7fa204421001), (34, 66, 2, 17, 3, 18, 0xe86a5a7710204040ad0218dc440210003a7daabf1108444109ff629124029111407bfce6db00a044401e2ca6c3c4011004275e0f5bf10a444509a18b22a44281110259a2fbad10284040d5b21936c409321425300892f1000c80094401dc040011004050bfe14b002440501167ecd1c42a111033bce84891004c8108eed379d44091014238498ff7108044008d936dc0c0021000135c9da7b00a844404cf92058c02111040329fcaed008044000b5207d24400100022a3e5c251020c8408a38459e4009321402510323d0088440048aea8c54422110031cd644910020c84006ea3908c00a3210117d9901500284040429e1e22c001320400909b8931028c840c193842840003200004141dd31008c800c02eec4ec00232001)],
  [(46, 74, 2, 21, 3, 22, 0xc532dfc55042110421ea07cfe8d410874108799f70f8950021d0401e67a19ffd4100440087977fa62b5002110401e2fb4aee441088110858bdccc6d50401d0021e2ab40e7540004400078a6c419b50001d0001d917069ed410881108762c8bea704420c04225546659150108301083489dcd2d4002110400d1c4f935d00087410033bacc41f4042110420cd64cd7c54108301087316f84c104421d04224b066f4744108301085286cc78d10400c00214879d88c410084410091d875e8504422044224731b97c901088110821af3c163044211042245f845c3d010881108315350f4f50400c0021c4ccdae3c10087410090f6ba90e4042110420837e1df1c41007400850de4d46540421d0420c36d984f941084410860c49170b5040204021c30a1bf7441008100850b81d46e50420c04218278be518410881108409c45de110421d0421421b45bcc4000740005084d252d10021d040140f4aa74941088110860041dfbe5002110401800f740d94100810086003610ce5040110021800cc55c04100810084001ef89a50401d0021800582ed1400044000600103dde50400c00218003074010008441002), (14, 78, 2, 23, 2, 23, 0xb2c2c5bd8821130442168f6f908aa0844c110876adea63ca0210b10420d3cbba1f6a0842c4108749937879a8000b10001d05dc5812a0802c400872d102598a8010b10401ca9491e7220804c100852700a54fa0211304420c975b595e80042c410032477326ba8200740021c68be6326a0804c100870f262bf9a8200f50021c0e188a6ea0841d01087)],
  [(23, 56, 2, 14, 7, 10, 0xad7d7fd28120107ed29e838160117c6e4e760560056f90ab0a8240196791617b1040035328e4571160034f37c0bf8400143e5ceafa84401537a77b0790401336a01b4d91201233659c631400062e6543fa90001227d4801f15200626fbcf458520141e667fc49520161602c1c691601315c4c89d95601713cee83014400711285cfd9440170d4189981560070bf1912d94001605d4f24485601503fbad0e112002), (35, 66, 2, 18, 7, 15, 0x24a5e76ab08020010773894ea42418004dcf236073091620136aea8b0bc240800494ef6a421091220124796481440458800d120278cf0112200236d50560c2018004499cfbd5b0016200124593939420588044636261af010600031895144d40408000834142ddf08122010061deb45c2118005415d67589082600190407ca784215880540f2ffd0d0956201702df3a7ac0518001c05fcb9bb09460017016e629c40018000402b59cb1082200180082d2f7c0048800001380d2709420016002ae585425488058003efdf708522014000c22b1405488018002bad1908420014000a7105c00980024002591a30142000600059536c0158801400134ac5005220040000b8b640108001000028bd70156200700007cb4c0088002000001db100460005)],
  [(16, 69, 2, 20, 9, 20, 0xf08a527c5004c004aae79fdea280a602254f891c44140130002a4595b6b02029808141c065ec85014c040a8b3b785c200260001459d6d44100530100a2c68f10820298089415c118cc4014c04428ab64ec220026002140217def0401300128000321f8002980884000039b40004c0042000004e4000260001000001bc040130002800000ba0002980804), (20, 82, 2, 27, 4, 25, 0xce72b3e6280a4302022560f418170a0290c0808154b9c44220808430002250f9c0a64820290c08089428d2e232200a4302022149e8731f8a0010c00009521eb72a220024302002147346cbd080290c0808051ab860f2280243020025461cc7288a0210c0008950a866bd0080a43020205024bf02b800290c08088400d5688028024302000540213291000290c0808040052fc7c2002430200014011764f820010c000094002d690c080243020005000b5802000090c080004001857ba080243020025000265ff800090c080084)],
  [(34, 82, 2, 27, 2, 23, 0xf8db4e388001020006006b371eb0220840c0018054b193bd300200b800200123f14a7a2000000010043fbeb8258800020006010fe23ea062084040010053afe28678820010004010bd2142b02004080008051b7e0a1500210b800200468e1940620842e0018051744097b88000a8006010550832e220802e0018041505402100010a800200453c3822a00802e001800129188f780010a80060044697987a20042a00180510e0b4c68001088004004423d74d42084260000050f4e499f80210b80060043a60473a2084260010050de20f4208210b8002014315b33fe2080260010040a29c7bd08010a800201415232b4600002a00180004dd1e0888010200060140ea75de620042200100503a9d594880008800401006cbf80820002a00080401a5ecab08200b800201002454f0e20040000100500302457882003000601000aff45820802600000400214ca00801088000014002b5bd4200022000004)],
  [(30, 77, 2, 23, 7, 22, 0x2f13048470204580210f3766ec2981002c010866cedc3d9c080060080331173d89a0400b004209420e52df0000500210c7baa2a49800228010873b9a6c3dc00104008039dc2d2f420408b00420ceba7a9b60200580010c6f07746701120c000173580aeb2c081060080392b43b1a404003000018918036520220580012c41abe3d101120400015205df254440010008440fe82e1bc0048a00025c7a236a6a0004500010e36bb15b2890024010881afd9891800014000430b5a9acb60000200401850317dd20220080002828079f4d01020c000070e8ab7448088060000b06d0ded44044090002502caa72960224580012e128477328802200108904d364b08081160004382560b4ba2408900422409189cba0224480012a02beec7700102800096)],
  [(29, 70, 2, 16, 3, 23, 0x3f75665b2120811609dafd7f7a808204182710633cc20a0818609a2f5044c040100408284cdbd6c0a001840380414891028002000d44829fda10040122034db505c8002041820d0cb84841004114222e06f213048004500cb2ade48a0808186082a4301b50200061008a340c6841204010232865c4ff040100408895627c5a120801209243af285028102008c8d217c4210041162021457e7a8481045884802d54c21204012211ed1ab35028106108c73a5d0bc100011402172a56fe04810040845247add21008012080818d5a0840204582019b176b8120411421066146d1020106108811b3fd5c08040802201e9e73604010450800648216c120411423)],
  [(29, 74, 2, 21, 6, 21, 0x22af3bf6a4881301c095357db4112204c030254a7e239a0881101808454b1cdd30204823025117ef60e48811018094296753832204c230250081c9562881101848391c790f82200c05020bc0794ee0881301c082ecab13e82200404020ac7ecc24c8803084092863ae6b92004c070049e7258104801300c012099af3e8a200404120745c12fe48801010091c6a939c32000c2100466dffe024800301401190696b520204823020559aaa2cc801308c0112ae09c322200c210203cba50f648803014090bc395a922004c230002afbd8ba080030140009e179b402204c030201236d1362080001048038a128e22204c230200cf04cc20801301c0002b6429188204006120000c903c0801300c00)],
  [(27, 75, 2, 21, 7, 22, 0x10ea88e700012102800565044c930044084404293c643120088408809505b85ac80110a100129ec030d1001214280052a9583c3004018042423078c9ce00883088483ec3dfba4010040109074e86af300021420004c2f301770044284404983cdf59400405020012e4ff14bc0010a1100252d67e1700200c00120924b7071004410442410644b1ba00880088081873e55d400104110802fe0adc500220c2012055d3dc5700041844200a804fa1a00084088011216f70740000401080207f680e0022082012040a85ece004408400407e311446000030084007b505dc400100110000c66a4260022102002415527f340044004004016093ec60008108800)],
  [(27, 75, 3, 23, 5, 23, 0x1a7bd298402013108041833d238414010410421fc1671600804c43000329dde700d00108410263de1ed81a00210c204c6659210240042180098cc91dc0480084200129ae08e40100108600047307140120131080048cf7a73024026218008d24917080804c4200416bcddca090010840222c1a8b241a0021082442b784b0824026210088519ae6a02800843080012455620000988002001eaef4800013104000038f68682002620008805d126004004c40001009b26740400108210000cc9db810013104004015f07082000420008802bbcfa040008410010052d4c1000098800080006c13018002100204000b43c8300042004880015fe206000841081)],
  [(26, 72, 3, 22, 5, 20, 0xc5dd394a4a40684421bcb9b9230208495001aab7d7890a406050218406c4144a406044217f9095464840680421703876d8484060042162116a370a40685021528b3b7f0a086950014cad49764a0869440146e81268420841440141f0bba4404040042137d50f17000849100137886732424048442135b9aa4508406010212a4399144a0861440127803c4a420849440121a1767b08086910011a289c644240404421196ce943080068100118d632cf0a0068500113d7651308406810210ed65a22404048042101175cc2480869040100cfe2d64008490401002af7884008410401000667384808610401)],
  [(25, 66, 2, 18, 2, 16, 0x223efa715286201236bbab93048180048d889b0e89282640234d2d89b24a119040d15053a91282200233f64fa9f0a0990084f0b025c12064412335b01c954a199048cc9aa6f01092280222cd5901b8a0990884b315d2e2282202212761ec2f4209900888f57354e2922822120bc577442119040881d05b9d292280231ebe00c142199048870106404282200211b3ca3290a119040462e152f8286201211225c9560a48a0084465ae1f4286641210dc3e3100219904800bb1cd612120802300f5547b60111050802ec7f0e08220220)],
  [(25, 77, 2, 22, 3, 24, 0x1b99f165402c00600508a9a3a3e081600300284bdd6fad200b000001421b5b5ca0209004c1101280bb65da048006080483660c1fa822003042009af283b200d001809400d5f3b45a06800c04a024fcadde50540000a4012741438081a0000128092c826018040018081008c5437ca05800000a1240588a95024000005011ae5f660818003010808d26cb53404001808004556eecc20a800c14802294ece6a0500060a04013b1e7b8826003042048963075700c0018084003f04342a04800c00a02137686ca03000602140081c7e8a82601304604834c478d812009822120143103a202800c0480207c59bb10500060a001)],
  [(23, 67, 2, 19, 12, 17, 0x12247ba824023109019e775bdc800620202b41e6288909e5201431ebb220413c0420801716c6282790844f9397324500f20089620a6b789092520126207bd90413c84203792f6862407940046b4236b4084f29000d04863d8809e420119ae0a481403c002229743b12080790040513306b48840292009ed9e4f8109252000a8955a30203ca0001165fa6c080780040213ec694400f2000840b726e9108c5240016e72341413c042200dc6396240494004005ab40c8800282000098eb29100c5040)],
  [(22, 60, 2, 15, 2, 12, 0x919f05c5c44cc018228a660044c801625a6216084c84051062e08c48c4213b381caa409052033628cc94440c012ed4c82644ccc21237341234480421221177d7c4c0c2121b185f0449c5211ac6b5a3c01050011ab18eec09c5200ee5291dc4905210e6d4dd544105010e52090cc01c5000b4eac5cc1125000abdd924c41c5010884713f451e501043d7f94c50e40102d7128ec512501020a811784cc82100cdacc1411e500)],
  [(22, 73, 2, 26, 11, 16, 0x3b16684e90600009081d6ea06fc8c26008a01a47ae2cc4611004400c224d8f020c10012901ea9064a41844014002ea5cae600c2600820172027de64483000520365f9cd78340802810185a514910448009402c279f4fa090200204045f280b241020025001f361f8d20880012004df94c6f418040140006a7cb57e02200060012a7b57d646010044001535748123418022900a1018a91180c0114004e054b908d0200884023797ebd01000030000cc9539f00c1001090041d2344c060000c0801ccbeda40c22008001)],
  [(21, 66, 2, 23, 2, 13, 0x36588e04942ca4400c175895220b210102fbcbd20d02ca4001af28d78f50b2910050f5f8f21028a400040962cc450a291000ff25df7d424a04013d33ec6550a291004d0a825b5028a40012ac1cc36409280000a45b5ae5420a04011f02d12f10b21100476aa6d39424a04001d10280b1092010045cf4751d024a000114997ea420a210100504b4195020a00010922106e209200100184ff64902ca40000080f9fc208200100001dd4e1420a0400)],
  [(21, 71, 2, 23, 11, 17, 0x53fa97cf80214020107a99c769214380402e8a51a75e4285008054f5edd54c81040100b1c86a0239081c020073876942d210280400a5238581a428200805c9984017c010e0100911240abe902000201420e7bc23210100400e3e8b383200070080086a54b694050e010098828109480a14020110b84149b210000400a16c4fb9602050080042d515d3c040e0100184e076fe902140201408fc61eb204380402c06a2d55a428000805403e256d4800a0100200712de59001c02006)],
  [(19, 86, 2, 27, 2, 27, 0x370431e8a0004006000000a43e6ac68003001800080257ffc03a000c02e001201887c6a0b80010038004001ec0c346a00040260000017919e57600030030004801b1c3b12e000c02600020149226dcc000400240040011d5656b2000c00e001200405e5e6400030090000804f4d7b848001002900100138b6bb7180000088000004d47a77cc000c02c001201342a9aef00030010000800ca14ed4c0010021000001264db6dd800200a800480491ca9cde00080220002011ef42c7b800100b800400403efbdda000002a001001)],
  [(17, 69, 2, 22, 2, 15, 0x1a812737b800e04408b2475c58c02702604574d4382a4138120260fda068b2014008129d9f3270104e048014893f689480500004a39d017a64100030250f34b98b209c09812877fd107100e0440140a312a5c022026041e435550a41101202491158a7b201c0881246798e8d104e04c01187b91aec822026048a5b7a2cc4238190042f467e28211c0c00211bc9935008e06400)],
  [(15, 76, 5, 24, 6, 21, 0xa350acd7064000209016072ccba660018811014a19247d0640182090147485a0c664018a11013c9eb7364640182110134a663042600188010120155bff264018a09011d967b4e564002211011d11319c264018a01011cca35b116400220901199334df260018809011637b430664000a11010e4962e44600180110109103a4416400220101082b878b264000a0901)],
  [(14, 80, 2, 25, 3, 24, 0xfe91c07e0002a1000101b46b01e70000a04001018630a37500008240200170c28ff62000820020816eb8594a2002810000815ff860592000024020805d17a52020020900088053a1b7ef200088400881385e42062002890008812a9a949e00028900080129aadfdf0000a2402101162d9b9b200082402081149148192000084008800ff250d2200201000080)],
  [(14, 73, 2, 21, 3, 22, 0x25910d9ea110060200ef0590a8c08803010065642237c80c0181002a81f7c0f40400c0800d21265ff2110060200a78730b8d080030100332b8461a004018000310b77d6400600c0801078590292010060000a1b5b85d008803010040d27341280c01810038157ac7b40200c0001c01772558030060400c005b2ea00080300004)],
  [(14, 73, 3, 22, 3, 22, 0x3744b60512200940883a4e74b7a91006a04419d56d5654800340220cad8d18624441291105d9958d502220948082c8bb705801104a40014a4ba9d548083422209df8a75e24001201104cfc727a122008408826730c65881104a440132f76de84808202220849886b2040412101041f83479120209088820001d61881004a0401)],
  [(13, 72, 5, 19, 6, 22, 0xa3a9d5b110420400298cfc0f8b001204080876b158cd10020c0019765375d9005204082872c6f58300020c001866b43a6f1002040009622d8cc900120c081852c06a6300100808184af1bc2310120c0819444873f71000080019434b245110120408093bff1fb51010080819214d08af1052040829)],
  [(12, 74, 2, 21, 5, 20, 0x81784a3460008402200bbfea8f980001000802d6d7352e0008c022048d6d31e18000300081168c400de0001c002243aa0247d00027008090dd1ba44c00094020202d258db700023008010a8634eb600094022202334ccaf8000500088080a29e460009c022241a1e6cb90002100800)],
  [(12, 74, 2, 21, 7, 21, 0x80ba254600018c04005a96f6432008630140961ade1a180010c050017b7b6560000430100047e051cb00210c04020e84e009400863010092d27dce380018c05004b15b2782008430140823f0ee91802184010248f9df08e00041004001f7b244b80018401004118043c20084100408)],
  [(12, 74, 3, 22, 2, 21, 0x8bd5ab6908c2184c205cccbf16823084130816611617d0842084420160c3d33c21086110814fbc53df004208042010dd9b50c0308603081353060b308c2084c200b0daf3b42900615001241b9ddf024018140047535241403082030801305e385004218042040f5d36b02308013080)],
  [(12, 74, 5, 22, 6, 22, 0xb386998e06001908801e04a29e908006402205dc9772e22001900805439ea7f898006422013e79bd7266001908884a1d77e89800044022127d7506e6400110888496c28b79180064222020c87336620019008847fc3a0a890004422010fafb4560200190080030a70a344804221004)],
  [(11, 76, 3, 23, 3, 23, 0xc7cc2ffe01810803281bad5752a010108012815996c35201104c0120945b5a7ce008108022813062594e01100c0120126a426e202100c002111e526d2a020108002911a7a10e202008804211151bf47a02810802291124722ba0001080028102dc00ba02900c02211)],
  [(10, 68, 5, 19, 6, 20, 0xb0d81d3c4a0420909951eba5d0a044090962b42f044204a098141c599ed0804408093d95426442042090106bf2f7c4a002090805b7a6a440042080102575b8c4004a08810126110c48042080900000ecc480020808)],
  [(10, 68, 2, 26, 2, 12, 0xee87fc4e216000881b4491c58252000021ab2af1e4256000821592c467601200008048f726b22560008a141b617fa0160008803e762abe0520000a0263f52d22520000a115641c6621200008106b0fbc60560008a0)],
  [(10, 75, 3, 24, 6, 21, 0x379d1d808a20440045252d875790440180082160241d26088010010409fe1a75c5100200209125f6397882080004921b98d12d104080008a4229c9922088110011401cf04c4c11026002284145ff588800800048200bd056504009800881)],
  [(10, 77, 3, 23, 6, 23, 0x2f3d3f2606200144420151cbd08221000a2200133cecb6a18900519080193477d10848028c8000aaa5714482800418002530b80d450c0040c1002931bed9109005190008f25074f9048028d00046d180bac404010640022e4c2bbe01200a30001)],
  [(9, 76, 2, 22, 6, 23, 0xfa600bc5001106005087fc8b1eb201106005096fea18a520100400509543c82670010040050846856de52001060050143533a38040902008403054b37d0001060050025fff644041902008481046599920000400501)],
  [(9, 65, 3, 16, 5, 17, 0x168aade870911b081ae0e75dc8489d850bb152349c240ec2818b62a7d212036100c4fcdc6b0912a0a157f18c958089d810a53d15044044a8085040cff2202076040460fd23a091330a1)],
  [(8, 67, 2, 22, 2, 15, 0xb68c20e8211404002f5f5c704422809005b7f8b170843010082ac074da108e0201130a8bb582104040005cd4b55c4218090406932fac8841012000a1d7949108e02411)],
  [(8, 65, 2, 15, 5, 19, 0xf2c029830240645075bba0b1012030283ad73d16c01109003045fd68a0088c8817c2231d602446050baa211d88122322859cd4cc2409009040468c945a04884821)],
  [(8, 60, 2, 12, 8, 18, 0xd9ae6a9602008107b91323a0081803432b16d600018023ff2538e02818133805c80a02808113154dd5e0181823119ecc22010182207b3d6f20201812)],
  [(8, 75, 3, 23, 3, 23, 0x94c3c7cc0c0440480a3094a1b78180230201451396aef0301000202896dc1dea0202800c0412c3def2c0c0500180a254ef4858100a00300448806591020110120088748aace06020c04051)],
  [(7, 55, 2, 18, 2, 5, 0x1dd36ef58580041619ef2e6f000999e99be0d200023370177b3400025513e3e55800488203ae6ed00018f1928181e0011)],
  [(7, 70, 2, 17, 3, 22, 0x2faa0ec8400091010288f5dc3b00024c040e148b6d7c0008301017fcbfcb50002040401b7fe6e3c0001300035d4638bd00000c0004f50fc2b4000110002)],
  [(7, 70, 2, 26, 2, 12, 0x26df43d22014040201880125e9804010000580f3e4be206040200493f0d6088581008050f3b92ca2020400000dee9ab480101008000dff79f6212040001)],
  [(7, 71, 2, 18, 5, 22, 0x19ea154da000018000601fc38040002102002148eb98900006400134eb48032000048000683217ca4001091000ad227d348002322009104579c8000460401)],
  [(7, 59, 5, 9, 5, 19, 0x194ee11b40140c25f0f3827002808424acfde7804001817905e4500a06321da569200100824279ac6fc02010c8086455f8050118)],
  [(7, 65, 3, 24, 15, 12, 0x75a836dcc2e0c0026f01e99860706001122f99b290a810081670ff9c085c18000af5e37a882c0c00252d3c8e2a1706800250eb0da509824001)],
  [(7, 73, 6, 23, 8, 19, 0x421081fd50412106810e9a20ae08814880042739e7da90104801a0423303871220522101091461809010290000848398423282010834002d48e68a040a402021)],
  [(7, 65, 6, 19, 7, 19, 0x5b950d1490232028ab83df4a48501214406c24c520280902202abb2110046401080d379d89020202840567c2c40101004202907662408c80a1)],
  [(6, 57, 2, 11, 3, 18, 0x2a827dc64001a0303b50e5a000d09731f2a18008681398f89c4804340d2c268070001a10849847d0000d00)],
  [(6, 74, 2, 23, 9, 19, 0x9256e7471000b080005b52fca364402c244014779b2ea9000b081004d7a5abee0002c0040127db49708100b01100479d79d104402c24001)],
  [(6, 58, 2, 16, 9, 13, 0xee309a5c24610260002a930818408005a04ec44610140165655101840400541c54402001000003b11108005)],
  [(6, 69, 5, 20, 2, 17, 0x235e559ce820781006eec3c6414123c090358d1f8c3a011e0081a75b3ed3d08870440423a4abc202470120608673583002380103)],
  [(6, 66, 9, 20, 11, 16, 0x9d635b608ca2242053389ba8832891081476b0e6c8ca6242443057f6c2228890010bfd096488a62404400af0ad822891001)],
  [(5, 61, 2, 15, 2, 15, 0x13eae8d60411081245b4d2ef20084019ecd7bd79047204cb1e2bafc822102641b9c36a4090823)],
  [(5, 78, 3, 24, 3, 24, 0x22de18be8080a08080813211c3010004800800249b7dfb382000940812026df1f920800050200807ea41af820021408021)],
  [(5, 78, 3, 25, 3, 25, 0x38a30bf2020103004011b11017f808000c00004564b307a0280030000910b6519580a008c0402440000676008003000081)],
  [(5, 74, 5, 22, 6, 22, 0x3f06356a800306422009e1a57160008190080195af1ca800286402013c13063e00061108804cd2596880038642201)],
  [(4, 72, 2, 25, 10, 16, 0xaa9db6d820224001015a55d1ce023100008130a7fc0b02008000800c3c0abd0220800081)],
  [(4, 73, 3, 24, 10, 18, 0xc0a888131046405040cec5efdd4801488800555d1b854401900410200db16122005822001)],
  [(3, 51, 2, 10, 2, 10, 0x1476be6712108d7b133cca80211251f68188201)],
  [(3, 60, 2, 17, 2, 13, 0xad668bf6c010201527fc66280312000848e1c6c031201)],
  [(3, 70, 2, 21, 5, 20, 0x3128274204403040017bffa7a41000c0000d00f58730440304003)],
  [(3, 69, 2, 21, 2, 18, 0x7c40a40e8880c060055d415c58440603080311a46e4220001840)],
  [(3, 67, 2, 21, 10, 17, 0x1295e4f2800ac080153a64ddd000580002a1110764002b02004)],
  [(3, 80, 2, 25, 2, 25, 0xc3772c7e0422100211096c1f0d3204220300110934f2d7de042200001109)],
  [(3, 76, 3, 22, 5, 24, 0x8a963ed430400610801874f9f5a200008090017f76cada20000e09001)],
  [(3, 75, 5, 23, 5, 23, 0x12bb83b6882013100425ddd47db1044060088499c56c3620800c00109)],
  [(3, 67, 9, 20, 9, 20, 0x1614f30e2440604444511307c48880488880ad25d8111009101)],
  [(3, 63, 12, 17, 12, 17, 0x1a793063c011c108ebb2a2a984034211d3a907bf08028421)],
  [(2, 82, 2, 26, 2, 26, 0xcda801e200200080004014f7a1218008006000101)],
  [(2, 62, 2, 18, 3, 13, 0xb885f307002810013ea41c0c00e0401)],
  [(2, 55, 2, 16, 5, 12, 0x2288c98c14c011c4266b88098022)],
  [(2, 68, 2, 26, 12, 12, 0xa49a1c9a1060004013c58ac38106000001)],
  [(2, 70, 2, 23, 11, 16, 0xb1433d49021502000e40fd7288085c08009)],
  [(2, 73, 3, 20, 6, 23, 0x2a48f30180400300802329248348200180441)],
  [(2, 61, 4, 23, 8, 18, 0x2760ee20018800022f6f61010c00005)],
  [(2, 70, 7, 21, 8, 19, 0xc62e295e08809010851f050cf40c0300128)],
  [(2, 49, 16, 10, 2, 10, 0x234f6e750ac52014ed4085228)],
  [(1, 45, 2, 10, 2, 3, 0x1cd3774a7601)],
  [(1, 77, 2, 23, 2, 25, 0x155accc6800000c00001)],
  [(1, 62, 7, 19, 10, 14, 0x388457c7130c4205)],
  [(1, 82, 2, 26, 3, 26, 0x26754d518000006000001)],
  [(1, 56, 2, 13, 6, 14, 0xd9a5bcd4083801)],
  [(1, 45, 3, 8, 5, 9, 0x1cd1d76781a1)],
  [(1, 50, 3, 13, 12, 5, 0x2039c02973021)],
  [(1, 72, 5, 20, 5, 22, 0xd60dbc42400a190111)],
  [(1, 73, 2, 25, 10, 17, 0x11ee47a820023001001)],
  [(1, 77, 2, 27, 4, 25, 0x146b124800110c000085)],
  [(1, 64, 2, 25, 13, 10, 0xc9d42ee407001001)],
  [(1, 52, 2, 14, 17, 9, 0xa64c2ec40e101)],
  [(1, 67, 2, 26, 7, 12, 0x79444e56086020001)],
  [(1, 82, 2, 26, 3, 26, 0x2e84c19c8000046020001)],
  [(1, 69, 3, 24, 11, 15, 0x113a7835c0a1810801)],
  [(1, 50, 4, 4, 1, 25, 0x2bb9910000019)],
  [(1, 64, 4, 21, 9, 16, 0xd26466b201320021)],
  [(1, 66, 5, 21, 5, 21, 0x2d2fac68001310003)],
  [(1, 70, 5, 24, 12, 17, 0x2c4503418021801081)],
  [(1, 54, 7, 19, 7, 15, 0x3ef5ae402c4801)],
  [(1, 45, 7, 8, 0, 13, 0x106551500181)],
  [(1, 65, 7, 22, 7, 19, 0x12469131001640401)],
  [(1, 59, 12, 16, 11, 18, 0x5bc513a40418089)],
  [(1, 65, 10, 18, 10, 18, 0x11a8bda5808862021)]]

end SnailCoordinates

namespace SnailCoordinates

private def rowChunks : List (List CertificateRow) :=
  (singletonRows.map singletonRow) ::
    (chunkedMotions.zip rowBlocks).flatMap (fun (_, blocks) => blocks.map unpackRows)

private def allRows : List CertificateRow := rowChunks.flatten

private def rowCheck : Bool :=
  (chunkedMotions.zip rowBlocks).all fun (m, blocks) =>
    blocks.all fun block => (unpackRows block).all (rowFits m)

private theorem allRows_valid (hrow : rowCheck = true)
    (hmotions : chunkedMotions.all motionCheck = true) (r : CertificateRow) (hr : r ∈ allRows) :
    BoundedRow r ∧ Congruent (proofRow r) := by
  obtain ⟨batch, hb, hr⟩ := List.mem_flatten.1 hr
  rcases List.mem_cons.1 hb with h | h
  · subst batch
    obtain ⟨p, _, rfl⟩ := List.mem_map.1 hr
    exact ⟨singletonRow_bounded p, singletonRow_congr p⟩
  · obtain ⟨⟨m, blocks⟩, hm, hbatch⟩ := List.mem_flatMap.1 h
    obtain ⟨block, hblock, rfl⟩ := List.mem_map.1 hbatch
    have hg := List.all_eq_true.1 hrow (m, blocks) hm
    have hb := List.all_eq_true.1 hg block hblock
    have h := List.all_eq_true.1 hb r hr
    have ha := List.all_eq_true.1 hmotions m (List.of_mem_zip hm).1
    exact ⟨rowFits_bounded m r h, rowFits_congr m ha r h⟩

private def denominator : ℤ := 1000000018

private def numerator : ℤ := 4000716307

private def termBlocks : List UnitDistancePacked.Terms :=
  [(0, denominator), (1, -numerator)] :: rowChunks.map (·.flatMap rowTerms)

private theorem flatten_terms (chunks : List (List CertificateRow)) :
    (chunks.map (·.flatMap rowTerms)).flatten = chunks.flatten.flatMap rowTerms := by
  induction chunks with
  | nil => rfl
  | cons rs chunks ih =>
    simp only [List.map_cons, List.flatten_cons, List.flatMap_append, ih]

private theorem termBlocks_eq :
    termBlocks.flatten = completeTerms denominator numerator allRows := by
  rw [termBlocks, List.flatten_cons, flatten_terms]
  rfl

private def edgeMasks : Array ℕ :=
  #[16, 16, 256, 2080, 35, 32920, 4605312, 8421728, 528580, 1024, 34744896, 67142664,
    256, 33588224, 163904, 335571104, 134348800, 83008, 5767232, 262400, 33817600,
    12582912, 44302400, 274727040, 100663296, 223355904, 453019648, 100728832, 75530240]

private def adj (v : ℕ) : ℕ := edgeMasks[v]?.getD 0

private theorem adj_fin_check :
    (List.range 29).all (fun i => adj i == edgeMask i) = true := by decide +kernel

private theorem adj_eq : adj = edgeMask := by
  funext i
  by_cases hi : i < 29
  · exact beq_iff_eq.1 (List.all_eq_true.1 adj_fin_check i (List.mem_range.2 hi))
  · have hlen : edgeMasks.size ≤ i := Nat.le_of_not_gt hi
    have hz : adj i = 0 := by simp [adj, Array.getElem?_eq_none hlen]
    rw [hz]
    apply Nat.eq_of_testBit_eq
    intro j
    cases e : (edgeMask i).testBit j
    · simp
    · obtain ⟨a, _, hai, _, _⟩ := edgeMask_dist e
      exact False.elim (hi (hai ▸ a.isLt))

private theorem mass_flatten (blocks : List UnitDistancePacked.Terms) :
    UnitDistancePacked.totalMass blocks.flatten =
      (blocks.map UnitDistancePacked.totalMass).sum := by
  induction blocks with
  | nil => rfl
  | cons row rows ih =>
    simp only [List.map_cons, List.flatten_cons, List.sum_cons]
    have hr : UnitDistancePacked.totalMass (row ++ rows.flatten) =
        UnitDistancePacked.totalMass row + UnitDistancePacked.totalMass rows.flatten := by
      simp [UnitDistancePacked.totalMass]
    rw [hr, ih]

private abbrev MassBound : Prop :=
  (termBlocks.map UnitDistancePacked.totalMass).sum < 2^44

private abbrev Good (free : List ℕ) (fixed : ℕ) : Prop :=
  UnitDistancePacked.NonnegativeOn adj free fixed termBlocks.flatten

private theorem checked_leaf (hm : MassBound) (free : List ℕ) (fixed : ℕ)
    (hlen : free.length ≤ 15)
    (h : UnitDistancePacked.checkProjected 64 adj free fixed termBlocks = true) : Good free fixed := by
  apply UnitDistancePacked.checkProjected_sound (by decide) adj free fixed termBlocks _ h
  rw [mass_flatten]
  calc
    _ < 2^44 * 2^free.length := Nat.mul_lt_mul_of_pos_right hm (Nat.two_pow_pos _)
    _ ≤ 2^44 * 2^15 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide : 0 < 2) hlen)
    _ < 2^(64-1) := by decide

private theorem checked_branch (free : List ℕ) (fixed v : ℕ) {lf rf : List ℕ} {lk rk : ℕ}
    (left : Good lf lk) (right : Good rf rk)
    (hl : (UnitDistancePacked.omitVertex free v, UnitDistancePacked.exclude fixed v) = (lf, lk))
    (hr : (UnitDistancePacked.omitNeighbors adj free v,
      UnitDistancePacked.includeVertex adj fixed v) = (rf, rk)) : Good free fixed := by
  have hlf : UnitDistancePacked.omitVertex free v = lf := congrArg Prod.fst hl
  have hlk : UnitDistancePacked.exclude fixed v = lk := congrArg Prod.snd hl
  have hrf : UnitDistancePacked.omitNeighbors adj free v = rf := congrArg Prod.fst hr
  have hrk : UnitDistancePacked.includeVertex adj fixed v = rk := congrArg Prod.snd hr
  apply UnitDistancePacked.nonnegative_branch adj free fixed v termBlocks.flatten
  · rw [hlf, hlk]
    exact left
  · rw [hrf, hrk]
    exact right

private theorem finish (hrow : rowCheck = true) (hmotions : chunkedMotions.all motionCheck = true)
    (hroot : Good (List.range 29) 0) : OMA.R_Erdos1070_erdos_1070_parts_ii_R1.H1 := by
  refine certificate_sound denominator numerator allRows
    (fun r hr => (allRows_valid hrow hmotions r hr).1)
    (fun r hr => (allRows_valid hrow hmotions r hr).2) ?_ (by decide) (by decide)
  intro I hb hi
  rw [← termBlocks_eq]
  exact UnitDistancePacked.nonnegative_unconstrained adj 29 termBlocks.flatten hroot I
    (adj_eq.symm ▸ hi) hb

end SnailCoordinates

namespace SnailCoordinates

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def rowAudit : PLift (rowCheck = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def massAudit : PLift MassBound := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a0 : UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 7, 9, 11, 12, 13, 17, 19, 20, 22, 24, 27, 28] 0 termBlocks = true := by decide +kernel

private theorem n0 : Good [0, 1, 2, 7, 9, 11, 12, 13, 17, 19, 20, 22, 24, 27, 28] 0 :=
  checked_leaf massAudit.down _ _ (by decide) a0

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a1 : UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 7, 9, 11, 12, 13, 17, 19, 20, 24, 27, 28] 2097152 termBlocks = true := by decide +kernel

private theorem n1 : Good [0, 1, 2, 7, 9, 11, 12, 13, 17, 19, 20, 24, 27, 28] 2097152 :=
  checked_leaf massAudit.down _ _ (by decide) a1

private theorem j0 : Good [0, 1, 2, 7, 9, 11, 12, 13, 17, 19, 20, 21, 22, 24, 27, 28] 0 :=
  checked_branch [0, 1, 2, 7, 9, 11, 12, 13, 17, 19, 20, 21, 22, 24, 27, 28] 0 21 n0 n1 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a2 : UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 7, 9, 11, 12, 13, 19, 20, 21, 22, 24, 27, 28] 16384 termBlocks = true := by decide +kernel

private theorem n2 : Good [0, 1, 2, 7, 9, 11, 12, 13, 19, 20, 21, 22, 24, 27, 28] 16384 :=
  checked_leaf massAudit.down _ _ (by decide) a2

private theorem j1 : Good [0, 1, 2, 7, 9, 11, 12, 13, 14, 17, 19, 20, 21, 22, 24, 27, 28] 0 :=
  checked_branch [0, 1, 2, 7, 9, 11, 12, 13, 14, 17, 19, 20, 21, 22, 24, 27, 28] 0 14 j0 n2 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a3 : UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 9, 11, 12, 13, 17, 19, 20, 21, 22, 24, 27, 28] 32 termBlocks = true := by decide +kernel

private theorem n3 : Good [0, 1, 2, 9, 11, 12, 13, 17, 19, 20, 21, 22, 24, 27, 28] 32 :=
  checked_leaf massAudit.down _ _ (by decide) a3

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a4 : UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 9, 11, 12, 13, 19, 20, 21, 22, 24, 27, 28] 16416 termBlocks = true := by decide +kernel

private theorem n4 : Good [0, 1, 2, 9, 11, 12, 13, 19, 20, 21, 22, 24, 27, 28] 16416 :=
  checked_leaf massAudit.down _ _ (by decide) a4

private theorem j2 : Good [0, 1, 2, 9, 11, 12, 13, 14, 17, 19, 20, 21, 22, 24, 27, 28] 32 :=
  checked_branch [0, 1, 2, 9, 11, 12, 13, 14, 17, 19, 20, 21, 22, 24, 27, 28] 32 14 n3 n4 (by decide +kernel) (by decide +kernel)

private theorem j3 : Good [0, 1, 2, 5, 7, 9, 11, 12, 13, 14, 17, 19, 20, 21, 22, 24, 27, 28] 0 :=
  checked_branch [0, 1, 2, 5, 7, 9, 11, 12, 13, 14, 17, 19, 20, 21, 22, 24, 27, 28] 0 5 j1 j2 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a5 : UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 7, 9, 11, 12, 13, 14, 19, 20, 21, 22, 24, 28] 65536 termBlocks = true := by decide +kernel

private theorem n5 : Good [0, 1, 2, 7, 9, 11, 12, 13, 14, 19, 20, 21, 22, 24, 28] 65536 :=
  checked_leaf massAudit.down _ _ (by decide) a5

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a6 : UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 9, 11, 12, 13, 14, 19, 20, 21, 22, 24, 28] 65568 termBlocks = true := by decide +kernel

private theorem n6 : Good [0, 1, 2, 9, 11, 12, 13, 14, 19, 20, 21, 22, 24, 28] 65568 :=
  checked_leaf massAudit.down _ _ (by decide) a6

private theorem j4 : Good [0, 1, 2, 5, 7, 9, 11, 12, 13, 14, 19, 20, 21, 22, 24, 28] 65536 :=
  checked_branch [0, 1, 2, 5, 7, 9, 11, 12, 13, 14, 19, 20, 21, 22, 24, 28] 65536 5 n5 n6 (by decide +kernel) (by decide +kernel)

private theorem j5 : Good [0, 1, 2, 5, 7, 9, 11, 12, 13, 14, 16, 17, 19, 20, 21, 22, 24, 27, 28] 0 :=
  checked_branch [0, 1, 2, 5, 7, 9, 11, 12, 13, 14, 16, 17, 19, 20, 21, 22, 24, 27, 28] 0 16 j3 j4 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a7 : UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 7, 9, 12, 13, 17, 19, 20, 21, 22, 24, 27, 28] 8 termBlocks = true := by decide +kernel

private theorem n7 : Good [0, 1, 2, 7, 9, 12, 13, 17, 19, 20, 21, 22, 24, 27, 28] 8 :=
  checked_leaf massAudit.down _ _ (by decide) a7

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a8 : UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 7, 9, 12, 13, 19, 20, 21, 22, 24, 27, 28] 16392 termBlocks = true := by decide +kernel

private theorem n8 : Good [0, 1, 2, 7, 9, 12, 13, 19, 20, 21, 22, 24, 27, 28] 16392 :=
  checked_leaf massAudit.down _ _ (by decide) a8

private theorem j6 : Good [0, 1, 2, 7, 9, 12, 13, 14, 17, 19, 20, 21, 22, 24, 27, 28] 8 :=
  checked_branch [0, 1, 2, 7, 9, 12, 13, 14, 17, 19, 20, 21, 22, 24, 27, 28] 8 14 n7 n8 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a9 : UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 7, 9, 12, 13, 14, 19, 20, 21, 22, 24, 28] 65544 termBlocks = true := by decide +kernel

private theorem n9 : Good [0, 1, 2, 7, 9, 12, 13, 14, 19, 20, 21, 22, 24, 28] 65544 :=
  checked_leaf massAudit.down _ _ (by decide) a9

private theorem j7 : Good [0, 1, 2, 7, 9, 12, 13, 14, 16, 17, 19, 20, 21, 22, 24, 27, 28] 8 :=
  checked_branch [0, 1, 2, 7, 9, 12, 13, 14, 16, 17, 19, 20, 21, 22, 24, 27, 28] 8 16 j6 n9 (by decide +kernel) (by decide +kernel)

private theorem j8 : Good [0, 1, 2, 3, 5, 7, 9, 11, 12, 13, 14, 16, 17, 19, 20, 21, 22, 24, 27, 28] 0 :=
  checked_branch [0, 1, 2, 3, 5, 7, 9, 11, 12, 13, 14, 16, 17, 19, 20, 21, 22, 24, 27, 28] 0 3 j5 j7 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a10 : UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 5, 7, 9, 11, 12, 13, 14, 17, 21, 24, 27, 28] 262144 termBlocks = true := by decide +kernel

private theorem n10 : Good [0, 1, 2, 5, 7, 9, 11, 12, 13, 14, 17, 21, 24, 27, 28] 262144 :=
  checked_leaf massAudit.down _ _ (by decide) a10

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a11 : UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 5, 7, 9, 11, 12, 13, 14, 21, 24, 28] 327680 termBlocks = true := by decide +kernel

private theorem n11 : Good [0, 1, 2, 5, 7, 9, 11, 12, 13, 14, 21, 24, 28] 327680 :=
  checked_leaf massAudit.down _ _ (by decide) a11

private theorem j9 : Good [0, 1, 2, 5, 7, 9, 11, 12, 13, 14, 16, 17, 21, 24, 27, 28] 262144 :=
  checked_branch [0, 1, 2, 5, 7, 9, 11, 12, 13, 14, 16, 17, 21, 24, 27, 28] 262144 16 n10 n11 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a12 : UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 7, 9, 12, 13, 14, 16, 17, 21, 24, 27, 28] 262152 termBlocks = true := by decide +kernel

private theorem n12 : Good [0, 1, 2, 7, 9, 12, 13, 14, 16, 17, 21, 24, 27, 28] 262152 :=
  checked_leaf massAudit.down _ _ (by decide) a12

private theorem j10 : Good [0, 1, 2, 3, 5, 7, 9, 11, 12, 13, 14, 16, 17, 21, 24, 27, 28] 262144 :=
  checked_branch [0, 1, 2, 3, 5, 7, 9, 11, 12, 13, 14, 16, 17, 21, 24, 27, 28] 262144 3 j9 n12 (by decide +kernel) (by decide +kernel)

private theorem j11 : Good [0, 1, 2, 3, 5, 7, 9, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 24, 27, 28] 0 :=
  checked_branch [0, 1, 2, 3, 5, 7, 9, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 24, 27, 28] 0 18 j8 j10 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a13 : UnitDistancePacked.checkProjected 64 adj [2, 7, 9, 11, 12, 13, 14, 17, 19, 20, 21, 22, 24, 27, 28] 16 termBlocks = true := by decide +kernel

private theorem n13 : Good [2, 7, 9, 11, 12, 13, 14, 17, 19, 20, 21, 22, 24, 27, 28] 16 :=
  checked_leaf massAudit.down _ _ (by decide) a13

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a14 : UnitDistancePacked.checkProjected 64 adj [2, 7, 9, 12, 13, 14, 17, 19, 20, 21, 22, 24, 27, 28] 24 termBlocks = true := by decide +kernel

private theorem n14 : Good [2, 7, 9, 12, 13, 14, 17, 19, 20, 21, 22, 24, 27, 28] 24 :=
  checked_leaf massAudit.down _ _ (by decide) a14

private theorem j12 : Good [2, 3, 7, 9, 11, 12, 13, 14, 17, 19, 20, 21, 22, 24, 27, 28] 16 :=
  checked_branch [2, 3, 7, 9, 11, 12, 13, 14, 17, 19, 20, 21, 22, 24, 27, 28] 16 3 n13 n14 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a15 : UnitDistancePacked.checkProjected 64 adj [2, 3, 7, 9, 11, 12, 13, 14, 19, 20, 21, 22, 24, 28] 65552 termBlocks = true := by decide +kernel

private theorem n15 : Good [2, 3, 7, 9, 11, 12, 13, 14, 19, 20, 21, 22, 24, 28] 65552 :=
  checked_leaf massAudit.down _ _ (by decide) a15

private theorem j13 : Good [2, 3, 7, 9, 11, 12, 13, 14, 16, 17, 19, 20, 21, 22, 24, 27, 28] 16 :=
  checked_branch [2, 3, 7, 9, 11, 12, 13, 14, 16, 17, 19, 20, 21, 22, 24, 27, 28] 16 16 j12 n15 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a16 : UnitDistancePacked.checkProjected 64 adj [2, 3, 7, 9, 11, 12, 13, 14, 16, 17, 21, 24, 27, 28] 262160 termBlocks = true := by decide +kernel

private theorem n16 : Good [2, 3, 7, 9, 11, 12, 13, 14, 16, 17, 21, 24, 27, 28] 262160 :=
  checked_leaf massAudit.down _ _ (by decide) a16

private theorem j14 : Good [2, 3, 7, 9, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 24, 27, 28] 16 :=
  checked_branch [2, 3, 7, 9, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 24, 27, 28] 16 18 j13 n16 (by decide +kernel) (by decide +kernel)

private theorem j15 : Good [0, 1, 2, 3, 4, 5, 7, 9, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 24, 27, 28] 0 :=
  checked_branch [0, 1, 2, 3, 4, 5, 7, 9, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 24, 27, 28] 0 4 j11 j14 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a17 : UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 3, 7, 9, 12, 13, 14, 16, 17, 19, 20, 21, 22] 67108864 termBlocks = true := by decide +kernel

private theorem n17 : Good [0, 1, 2, 3, 7, 9, 12, 13, 14, 16, 17, 19, 20, 21, 22] 67108864 :=
  checked_leaf massAudit.down _ _ (by decide) a17

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a18 : UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 9, 12, 13, 14, 16, 17, 19, 20, 21, 22] 67108896 termBlocks = true := by decide +kernel

private theorem n18 : Good [0, 1, 2, 9, 12, 13, 14, 16, 17, 19, 20, 21, 22] 67108896 :=
  checked_leaf massAudit.down _ _ (by decide) a18

private theorem j16 : Good [0, 1, 2, 3, 5, 7, 9, 12, 13, 14, 16, 17, 19, 20, 21, 22] 67108864 :=
  checked_branch [0, 1, 2, 3, 5, 7, 9, 12, 13, 14, 16, 17, 19, 20, 21, 22] 67108864 5 n17 n18 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a19 : UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 3, 5, 7, 9, 12, 13, 14, 16, 17, 21] 67371008 termBlocks = true := by decide +kernel

private theorem n19 : Good [0, 1, 2, 3, 5, 7, 9, 12, 13, 14, 16, 17, 21] 67371008 :=
  checked_leaf massAudit.down _ _ (by decide) a19

private theorem j17 : Good [0, 1, 2, 3, 5, 7, 9, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22] 67108864 :=
  checked_branch [0, 1, 2, 3, 5, 7, 9, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22] 67108864 18 j16 n19 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a20 : UnitDistancePacked.checkProjected 64 adj [2, 3, 7, 9, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22] 67108880 termBlocks = true := by decide +kernel

private theorem n20 : Good [2, 3, 7, 9, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22] 67108880 :=
  checked_leaf massAudit.down _ _ (by decide) a20

private theorem j18 : Good [0, 1, 2, 3, 4, 5, 7, 9, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22] 67108864 :=
  checked_branch [0, 1, 2, 3, 4, 5, 7, 9, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22] 67108864 4 j17 n20 (by decide +kernel) (by decide +kernel)

private theorem j19 : Good [0, 1, 2, 3, 4, 5, 7, 9, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 24, 26, 27, 28] 0 :=
  checked_branch [0, 1, 2, 3, 4, 5, 7, 9, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 24, 26, 27, 28] 0 26 j15 j18 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a21 : UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 5, 9, 11, 12, 13, 14, 17, 18, 19, 20, 24, 27] 8388608 termBlocks = true := by decide +kernel

private theorem n21 : Good [0, 1, 2, 5, 9, 11, 12, 13, 14, 17, 18, 19, 20, 24, 27] 8388608 :=
  checked_leaf massAudit.down _ _ (by decide) a21

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a22 : UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 5, 9, 11, 12, 13, 14, 18, 19, 20, 24] 8454144 termBlocks = true := by decide +kernel

private theorem n22 : Good [0, 1, 2, 5, 9, 11, 12, 13, 14, 18, 19, 20, 24] 8454144 :=
  checked_leaf massAudit.down _ _ (by decide) a22

private theorem j20 : Good [0, 1, 2, 5, 9, 11, 12, 13, 14, 16, 17, 18, 19, 20, 24, 27] 8388608 :=
  checked_branch [0, 1, 2, 5, 9, 11, 12, 13, 14, 16, 17, 18, 19, 20, 24, 27] 8388608 16 n21 n22 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a23 : UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 9, 12, 13, 14, 16, 17, 18, 19, 20, 24, 27] 8388616 termBlocks = true := by decide +kernel

private theorem n23 : Good [0, 1, 2, 9, 12, 13, 14, 16, 17, 18, 19, 20, 24, 27] 8388616 :=
  checked_leaf massAudit.down _ _ (by decide) a23

private theorem j21 : Good [0, 1, 2, 3, 5, 9, 11, 12, 13, 14, 16, 17, 18, 19, 20, 24, 27] 8388608 :=
  checked_branch [0, 1, 2, 3, 5, 9, 11, 12, 13, 14, 16, 17, 18, 19, 20, 24, 27] 8388608 3 j20 n23 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a24 : UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 3, 5, 9, 12, 13, 14, 16, 17, 18, 19, 20] 75497472 termBlocks = true := by decide +kernel

private theorem n24 : Good [0, 1, 2, 3, 5, 9, 12, 13, 14, 16, 17, 18, 19, 20] 75497472 :=
  checked_leaf massAudit.down _ _ (by decide) a24

private theorem j22 : Good [0, 1, 2, 3, 5, 9, 11, 12, 13, 14, 16, 17, 18, 19, 20, 24, 26, 27] 8388608 :=
  checked_branch [0, 1, 2, 3, 5, 9, 11, 12, 13, 14, 16, 17, 18, 19, 20, 24, 26, 27] 8388608 26 j21 n24 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a25 : UnitDistancePacked.checkProjected 64 adj [2, 3, 9, 11, 12, 13, 14, 16, 17, 18, 19, 20, 24, 26, 27] 8388624 termBlocks = true := by decide +kernel

private theorem n25 : Good [2, 3, 9, 11, 12, 13, 14, 16, 17, 18, 19, 20, 24, 26, 27] 8388624 :=
  checked_leaf massAudit.down _ _ (by decide) a25

private theorem j23 : Good [0, 1, 2, 3, 4, 5, 9, 11, 12, 13, 14, 16, 17, 18, 19, 20, 24, 26, 27] 8388608 :=
  checked_branch [0, 1, 2, 3, 4, 5, 9, 11, 12, 13, 14, 16, 17, 18, 19, 20, 24, 26, 27] 8388608 4 j22 n25 (by decide +kernel) (by decide +kernel)

private theorem j24 : Good [0, 1, 2, 3, 4, 5, 7, 9, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 23, 24, 26, 27, 28] 0 :=
  checked_branch [0, 1, 2, 3, 4, 5, 7, 9, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 23, 24, 26, 27, 28] 0 23 j19 j23 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a26 : UnitDistancePacked.checkProjected 64 adj [0, 1, 5, 9, 11, 13, 14, 17, 18, 20, 21, 23, 24, 27, 28] 256 termBlocks = true := by decide +kernel

private theorem n26 : Good [0, 1, 5, 9, 11, 13, 14, 17, 18, 20, 21, 23, 24, 27, 28] 256 :=
  checked_leaf massAudit.down _ _ (by decide) a26

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a27 : UnitDistancePacked.checkProjected 64 adj [0, 1, 5, 9, 11, 13, 14, 18, 20, 21, 23, 24, 28] 65792 termBlocks = true := by decide +kernel

private theorem n27 : Good [0, 1, 5, 9, 11, 13, 14, 18, 20, 21, 23, 24, 28] 65792 :=
  checked_leaf massAudit.down _ _ (by decide) a27

private theorem j25 : Good [0, 1, 5, 9, 11, 13, 14, 16, 17, 18, 20, 21, 23, 24, 27, 28] 256 :=
  checked_branch [0, 1, 5, 9, 11, 13, 14, 16, 17, 18, 20, 21, 23, 24, 27, 28] 256 16 n26 n27 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a28 : UnitDistancePacked.checkProjected 64 adj [0, 1, 9, 13, 14, 16, 17, 18, 20, 21, 23, 24, 27, 28] 264 termBlocks = true := by decide +kernel

private theorem n28 : Good [0, 1, 9, 13, 14, 16, 17, 18, 20, 21, 23, 24, 27, 28] 264 :=
  checked_leaf massAudit.down _ _ (by decide) a28

private theorem j26 : Good [0, 1, 3, 5, 9, 11, 13, 14, 16, 17, 18, 20, 21, 23, 24, 27, 28] 256 :=
  checked_branch [0, 1, 3, 5, 9, 11, 13, 14, 16, 17, 18, 20, 21, 23, 24, 27, 28] 256 3 j25 n28 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a29 : UnitDistancePacked.checkProjected 64 adj [0, 1, 3, 5, 9, 11, 13, 14, 16, 17, 20, 24, 27, 28] 4194560 termBlocks = true := by decide +kernel

private theorem n29 : Good [0, 1, 3, 5, 9, 11, 13, 14, 16, 17, 20, 24, 27, 28] 4194560 :=
  checked_leaf massAudit.down _ _ (by decide) a29

private theorem j27 : Good [0, 1, 3, 5, 9, 11, 13, 14, 16, 17, 18, 20, 21, 22, 23, 24, 27, 28] 256 :=
  checked_branch [0, 1, 3, 5, 9, 11, 13, 14, 16, 17, 18, 20, 21, 22, 23, 24, 27, 28] 256 22 j26 n29 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a30 : UnitDistancePacked.checkProjected 64 adj [3, 9, 11, 13, 14, 16, 17, 18, 20, 21, 22, 23, 24, 27, 28] 272 termBlocks = true := by decide +kernel

private theorem n30 : Good [3, 9, 11, 13, 14, 16, 17, 18, 20, 21, 22, 23, 24, 27, 28] 272 :=
  checked_leaf massAudit.down _ _ (by decide) a30

private theorem j28 : Good [0, 1, 3, 4, 5, 9, 11, 13, 14, 16, 17, 18, 20, 21, 22, 23, 24, 27, 28] 256 :=
  checked_branch [0, 1, 3, 4, 5, 9, 11, 13, 14, 16, 17, 18, 20, 21, 22, 23, 24, 27, 28] 256 4 j27 n30 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a31 : UnitDistancePacked.checkProjected 64 adj [0, 1, 3, 4, 5, 9, 13, 14, 16, 17, 18, 20, 21, 22, 23] 67109120 termBlocks = true := by decide +kernel

private theorem n31 : Good [0, 1, 3, 4, 5, 9, 13, 14, 16, 17, 18, 20, 21, 22, 23] 67109120 :=
  checked_leaf massAudit.down _ _ (by decide) a31

private theorem j29 : Good [0, 1, 3, 4, 5, 9, 11, 13, 14, 16, 17, 18, 20, 21, 22, 23, 24, 26, 27, 28] 256 :=
  checked_branch [0, 1, 3, 4, 5, 9, 11, 13, 14, 16, 17, 18, 20, 21, 22, 23, 24, 26, 27, 28] 256 26 j28 n31 (by decide +kernel) (by decide +kernel)

private theorem j30 : Good [0, 1, 2, 3, 4, 5, 7, 8, 9, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 23, 24, 26, 27, 28] 0 :=
  checked_branch [0, 1, 2, 3, 4, 5, 7, 8, 9, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 23, 24, 26, 27, 28] 0 8 j24 j29 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a32 : UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 3, 7, 12, 14, 16, 18, 19, 21, 22, 24, 27, 28] 1024 termBlocks = true := by decide +kernel

private theorem n32 : Good [0, 1, 2, 3, 7, 12, 14, 16, 18, 19, 21, 22, 24, 27, 28] 1024 :=
  checked_leaf massAudit.down _ _ (by decide) a32

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a33 : UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 12, 14, 16, 18, 19, 21, 22, 24, 27, 28] 1056 termBlocks = true := by decide +kernel

private theorem n33 : Good [0, 1, 2, 12, 14, 16, 18, 19, 21, 22, 24, 27, 28] 1056 :=
  checked_leaf massAudit.down _ _ (by decide) a33

private theorem j31 : Good [0, 1, 2, 3, 5, 7, 12, 14, 16, 18, 19, 21, 22, 24, 27, 28] 1024 :=
  checked_branch [0, 1, 2, 3, 5, 7, 12, 14, 16, 18, 19, 21, 22, 24, 27, 28] 1024 5 n32 n33 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a34 : UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 3, 5, 7, 12, 14, 16, 18, 19, 21, 22] 67109888 termBlocks = true := by decide +kernel

private theorem n34 : Good [0, 1, 2, 3, 5, 7, 12, 14, 16, 18, 19, 21, 22] 67109888 :=
  checked_leaf massAudit.down _ _ (by decide) a34

private theorem j32 : Good [0, 1, 2, 3, 5, 7, 12, 14, 16, 18, 19, 21, 22, 24, 26, 27, 28] 1024 :=
  checked_branch [0, 1, 2, 3, 5, 7, 12, 14, 16, 18, 19, 21, 22, 24, 26, 27, 28] 1024 26 j31 n34 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a35 : UnitDistancePacked.checkProjected 64 adj [2, 3, 7, 12, 14, 16, 18, 19, 21, 22, 24, 26, 27, 28] 1040 termBlocks = true := by decide +kernel

private theorem n35 : Good [2, 3, 7, 12, 14, 16, 18, 19, 21, 22, 24, 26, 27, 28] 1040 :=
  checked_leaf massAudit.down _ _ (by decide) a35

private theorem j33 : Good [0, 1, 2, 3, 4, 5, 7, 12, 14, 16, 18, 19, 21, 22, 24, 26, 27, 28] 1024 :=
  checked_branch [0, 1, 2, 3, 4, 5, 7, 12, 14, 16, 18, 19, 21, 22, 24, 26, 27, 28] 1024 4 j32 n35 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a36 : UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 3, 4, 5, 12, 14, 16, 18, 19, 24, 26, 27] 8389632 termBlocks = true := by decide +kernel

private theorem n36 : Good [0, 1, 2, 3, 4, 5, 12, 14, 16, 18, 19, 24, 26, 27] 8389632 :=
  checked_leaf massAudit.down _ _ (by decide) a36

private theorem j34 : Good [0, 1, 2, 3, 4, 5, 7, 12, 14, 16, 18, 19, 21, 22, 23, 24, 26, 27, 28] 1024 :=
  checked_branch [0, 1, 2, 3, 4, 5, 7, 12, 14, 16, 18, 19, 21, 22, 23, 24, 26, 27, 28] 1024 23 j33 n36 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a37 : UnitDistancePacked.checkProjected 64 adj [0, 1, 3, 4, 5, 14, 16, 18, 21, 22, 23, 24, 26, 27, 28] 1280 termBlocks = true := by decide +kernel

private theorem n37 : Good [0, 1, 3, 4, 5, 14, 16, 18, 21, 22, 23, 24, 26, 27, 28] 1280 :=
  checked_leaf massAudit.down _ _ (by decide) a37

private theorem j35 : Good [0, 1, 2, 3, 4, 5, 7, 8, 12, 14, 16, 18, 19, 21, 22, 23, 24, 26, 27, 28] 1024 :=
  checked_branch [0, 1, 2, 3, 4, 5, 7, 8, 12, 14, 16, 18, 19, 21, 22, 23, 24, 26, 27, 28] 1024 8 j34 n37 (by decide +kernel) (by decide +kernel)

private theorem j36 : Good [0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 23, 24, 26, 27, 28] 0 :=
  checked_branch [0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 23, 24, 26, 27, 28] 0 10 j30 j35 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a38 : UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 5, 7, 9, 11, 12, 14, 16, 17, 18, 19, 21, 28] 33554432 termBlocks = true := by decide +kernel

private theorem n38 : Good [0, 1, 2, 5, 7, 9, 11, 12, 14, 16, 17, 18, 19, 21, 28] 33554432 :=
  checked_leaf massAudit.down _ _ (by decide) a38

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a39 : UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 7, 9, 12, 14, 16, 17, 18, 19, 21, 28] 33554440 termBlocks = true := by decide +kernel

private theorem n39 : Good [0, 1, 2, 7, 9, 12, 14, 16, 17, 18, 19, 21, 28] 33554440 :=
  checked_leaf massAudit.down _ _ (by decide) a39

private theorem j37 : Good [0, 1, 2, 3, 5, 7, 9, 11, 12, 14, 16, 17, 18, 19, 21, 28] 33554432 :=
  checked_branch [0, 1, 2, 3, 5, 7, 9, 11, 12, 14, 16, 17, 18, 19, 21, 28] 33554432 3 n38 n39 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a40 : UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 3, 5, 9, 11, 12, 14, 16, 17, 18, 19] 41943040 termBlocks = true := by decide +kernel

private theorem n40 : Good [0, 1, 2, 3, 5, 9, 11, 12, 14, 16, 17, 18, 19] 41943040 :=
  checked_leaf massAudit.down _ _ (by decide) a40

private theorem j38 : Good [0, 1, 2, 3, 5, 7, 9, 11, 12, 14, 16, 17, 18, 19, 21, 23, 28] 33554432 :=
  checked_branch [0, 1, 2, 3, 5, 7, 9, 11, 12, 14, 16, 17, 18, 19, 21, 23, 28] 33554432 23 j37 n40 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a41 : UnitDistancePacked.checkProjected 64 adj [2, 3, 7, 9, 11, 12, 14, 16, 17, 18, 19, 21, 23, 28] 33554448 termBlocks = true := by decide +kernel

private theorem n41 : Good [2, 3, 7, 9, 11, 12, 14, 16, 17, 18, 19, 21, 23, 28] 33554448 :=
  checked_leaf massAudit.down _ _ (by decide) a41

private theorem j39 : Good [0, 1, 2, 3, 4, 5, 7, 9, 11, 12, 14, 16, 17, 18, 19, 21, 23, 28] 33554432 :=
  checked_branch [0, 1, 2, 3, 4, 5, 7, 9, 11, 12, 14, 16, 17, 18, 19, 21, 23, 28] 33554432 4 j38 n41 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a42 : UnitDistancePacked.checkProjected 64 adj [0, 1, 3, 4, 5, 9, 11, 14, 16, 17, 18, 21, 23, 28] 33554688 termBlocks = true := by decide +kernel

private theorem n42 : Good [0, 1, 3, 4, 5, 9, 11, 14, 16, 17, 18, 21, 23, 28] 33554688 :=
  checked_leaf massAudit.down _ _ (by decide) a42

private theorem j40 : Good [0, 1, 2, 3, 4, 5, 7, 8, 9, 11, 12, 14, 16, 17, 18, 19, 21, 23, 28] 33554432 :=
  checked_branch [0, 1, 2, 3, 4, 5, 7, 8, 9, 11, 12, 14, 16, 17, 18, 19, 21, 23, 28] 33554432 8 j39 n42 (by decide +kernel) (by decide +kernel)

private theorem j41 : Good [0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28] 0 :=
  checked_branch [0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28] 0 25 j36 j40 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a43 : UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 3, 9, 12, 16, 17, 19, 20, 21, 22, 23, 24, 27] 32768 termBlocks = true := by decide +kernel

private theorem n43 : Good [0, 1, 2, 3, 9, 12, 16, 17, 19, 20, 21, 22, 23, 24, 27] 32768 :=
  checked_leaf massAudit.down _ _ (by decide) a43

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a44 : UnitDistancePacked.checkProjected 64 adj [2, 3, 9, 12, 16, 17, 19, 20, 21, 22, 23, 24, 27] 32784 termBlocks = true := by decide +kernel

private theorem n44 : Good [2, 3, 9, 12, 16, 17, 19, 20, 21, 22, 23, 24, 27] 32784 :=
  checked_leaf massAudit.down _ _ (by decide) a44

private theorem j42 : Good [0, 1, 2, 3, 4, 9, 12, 16, 17, 19, 20, 21, 22, 23, 24, 27] 32768 :=
  checked_branch [0, 1, 2, 3, 4, 9, 12, 16, 17, 19, 20, 21, 22, 23, 24, 27] 32768 4 n43 n44 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a45 : UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 3, 4, 9, 12, 16, 17, 21, 23, 24, 27] 294912 termBlocks = true := by decide +kernel

private theorem n45 : Good [0, 1, 2, 3, 4, 9, 12, 16, 17, 21, 23, 24, 27] 294912 :=
  checked_leaf massAudit.down _ _ (by decide) a45

private theorem j43 : Good [0, 1, 2, 3, 4, 9, 12, 16, 17, 18, 19, 20, 21, 22, 23, 24, 27] 32768 :=
  checked_branch [0, 1, 2, 3, 4, 9, 12, 16, 17, 18, 19, 20, 21, 22, 23, 24, 27] 32768 18 j42 n45 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a46 : UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 3, 4, 12, 16, 18, 19, 21, 22, 23, 24, 27] 33792 termBlocks = true := by decide +kernel

private theorem n46 : Good [0, 1, 2, 3, 4, 12, 16, 18, 19, 21, 22, 23, 24, 27] 33792 :=
  checked_leaf massAudit.down _ _ (by decide) a46

private theorem j44 : Good [0, 1, 2, 3, 4, 9, 10, 12, 16, 17, 18, 19, 20, 21, 22, 23, 24, 27] 32768 :=
  checked_branch [0, 1, 2, 3, 4, 9, 10, 12, 16, 17, 18, 19, 20, 21, 22, 23, 24, 27] 32768 10 j43 n46 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a47 : UnitDistancePacked.checkProjected 64 adj [0, 1, 3, 4, 9, 10, 16, 17, 18, 20, 21, 22, 23, 24, 27] 33024 termBlocks = true := by decide +kernel

private theorem n47 : Good [0, 1, 3, 4, 9, 10, 16, 17, 18, 20, 21, 22, 23, 24, 27] 33024 :=
  checked_leaf massAudit.down _ _ (by decide) a47

private theorem j45 : Good [0, 1, 2, 3, 4, 8, 9, 10, 12, 16, 17, 18, 19, 20, 21, 22, 23, 24, 27] 32768 :=
  checked_branch [0, 1, 2, 3, 4, 8, 9, 10, 12, 16, 17, 18, 19, 20, 21, 22, 23, 24, 27] 32768 8 j44 n47 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a48 : UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 3, 4, 8, 9, 12, 16, 17, 18, 19, 21, 23] 33587200 termBlocks = true := by decide +kernel

private theorem n48 : Good [0, 1, 2, 3, 4, 8, 9, 12, 16, 17, 18, 19, 21, 23] 33587200 :=
  checked_leaf massAudit.down _ _ (by decide) a48

private theorem j46 : Good [0, 1, 2, 3, 4, 8, 9, 10, 12, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 27] 32768 :=
  checked_branch [0, 1, 2, 3, 4, 8, 9, 10, 12, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 27] 32768 25 j45 n48 (by decide +kernel) (by decide +kernel)

private theorem j47 : Good [0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28] 0 :=
  checked_branch [0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28] 0 15 j41 j46 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a49 : UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 5, 9, 11, 12, 13, 16, 19, 20, 21, 24, 27, 28] 64 termBlocks = true := by decide +kernel

private theorem n49 : Good [0, 1, 2, 5, 9, 11, 12, 13, 16, 19, 20, 21, 24, 27, 28] 64 :=
  checked_leaf massAudit.down _ _ (by decide) a49

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a50 : UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 5, 9, 11, 12, 13, 16, 19, 20, 24, 27] 8388672 termBlocks = true := by decide +kernel

private theorem n50 : Good [0, 1, 2, 5, 9, 11, 12, 13, 16, 19, 20, 24, 27] 8388672 :=
  checked_leaf massAudit.down _ _ (by decide) a50

private theorem j48 : Good [0, 1, 2, 5, 9, 11, 12, 13, 16, 19, 20, 21, 23, 24, 27, 28] 64 :=
  checked_branch [0, 1, 2, 5, 9, 11, 12, 13, 16, 19, 20, 21, 23, 24, 27, 28] 64 23 n49 n50 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a51 : UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 9, 12, 13, 16, 19, 20, 21, 23, 24, 27, 28] 72 termBlocks = true := by decide +kernel

private theorem n51 : Good [0, 1, 2, 9, 12, 13, 16, 19, 20, 21, 23, 24, 27, 28] 72 :=
  checked_leaf massAudit.down _ _ (by decide) a51

private theorem j49 : Good [0, 1, 2, 3, 5, 9, 11, 12, 13, 16, 19, 20, 21, 23, 24, 27, 28] 64 :=
  checked_branch [0, 1, 2, 3, 5, 9, 11, 12, 13, 16, 19, 20, 21, 23, 24, 27, 28] 64 3 j48 n51 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a52 : UnitDistancePacked.checkProjected 64 adj [2, 3, 9, 11, 12, 13, 16, 19, 20, 21, 23, 24, 27, 28] 80 termBlocks = true := by decide +kernel

private theorem n52 : Good [2, 3, 9, 11, 12, 13, 16, 19, 20, 21, 23, 24, 27, 28] 80 :=
  checked_leaf massAudit.down _ _ (by decide) a52

private theorem j50 : Good [0, 1, 2, 3, 4, 5, 9, 11, 12, 13, 16, 19, 20, 21, 23, 24, 27, 28] 64 :=
  checked_branch [0, 1, 2, 3, 4, 5, 9, 11, 12, 13, 16, 19, 20, 21, 23, 24, 27, 28] 64 4 j49 n52 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a53 : UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 3, 4, 5, 9, 11, 12, 16, 19, 21, 23, 28] 33554496 termBlocks = true := by decide +kernel

private theorem n53 : Good [0, 1, 2, 3, 4, 5, 9, 11, 12, 16, 19, 21, 23, 28] 33554496 :=
  checked_leaf massAudit.down _ _ (by decide) a53

private theorem j51 : Good [0, 1, 2, 3, 4, 5, 9, 11, 12, 13, 16, 19, 20, 21, 23, 24, 25, 27, 28] 64 :=
  checked_branch [0, 1, 2, 3, 4, 5, 9, 11, 12, 13, 16, 19, 20, 21, 23, 24, 25, 27, 28] 64 25 j50 n53 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a54 : UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 3, 4, 9, 12, 16, 19, 20, 21, 23, 24, 25, 27] 32832 termBlocks = true := by decide +kernel

private theorem n54 : Good [0, 1, 2, 3, 4, 9, 12, 16, 19, 20, 21, 23, 24, 25, 27] 32832 :=
  checked_leaf massAudit.down _ _ (by decide) a54

private theorem j52 : Good [0, 1, 2, 3, 4, 5, 9, 11, 12, 13, 15, 16, 19, 20, 21, 23, 24, 25, 27, 28] 64 :=
  checked_branch [0, 1, 2, 3, 4, 5, 9, 11, 12, 13, 15, 16, 19, 20, 21, 23, 24, 25, 27, 28] 64 15 j51 n54 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private theorem a55 : UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 3, 4, 5, 9, 12, 13, 16, 19, 20, 21, 23] 67108928 termBlocks = true := by decide +kernel

private theorem n55 : Good [0, 1, 2, 3, 4, 5, 9, 12, 13, 16, 19, 20, 21, 23] 67108928 :=
  checked_leaf massAudit.down _ _ (by decide) a55

private theorem j53 : Good [0, 1, 2, 3, 4, 5, 9, 11, 12, 13, 15, 16, 19, 20, 21, 23, 24, 25, 26, 27, 28] 64 :=
  checked_branch [0, 1, 2, 3, 4, 5, 9, 11, 12, 13, 15, 16, 19, 20, 21, 23, 24, 25, 26, 27, 28] 64 26 j52 n55 (by decide +kernel) (by decide +kernel)

private theorem j54 : Good [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28] 0 :=
  checked_branch [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28] 0 6 j47 j53 (by decide +kernel) (by decide +kernel)

private theorem full_certificate : OMA.R_Erdos1070_erdos_1070_parts_ii_R1.H1 :=
  finish rowAudit.down chunkedAudit j54

end SnailCoordinates

private theorem certificate : OMA.R_Erdos1070_erdos_1070_parts_ii_R1.H1 :=
  SnailCoordinates.full_certificate

theorem OMA.solution : type_of% @Erdos1070.erdos_1070.parts.ii :=
  OMA.R_Erdos1070_erdos_1070_parts_ii_R1.main certificate averaging
