import FormalConjectures.ErdosProblems.«107»

-- Reduction Erdos107.variants.su_bound.R1 of Erdős Problem 107 — su bound
-- Credit: @mucoucah
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-! The target (Suk 2017, ES(n) ≤ 2^(n+o(n))) is reduced to a purely coordinate statement
about finite subsets of ℝ × ℝ (distinct abscissas, no flat x-sorted triple; strictly
extreme points), for every ε in (0,1), split by the parity of n. The o(n) bookkeeping, the
floor/sInf handling, the passage from EuclideanSpace / convexHull / Collinear to coordinates
and the range ε ≥ 1 are all proved below. -/

open Filter Asymptotics Finset

namespace OMA.R_Erdos107_variants_su_bound_R1

private theorem from_eventual_epsilon {g : ℕ → ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, g n ≤ (2 : ℝ) ^ ((1 + ε) * n)) :
    ∃ r : ℕ → ℝ, r =o[atTop] (fun n => (n : ℝ)) ∧
      ∀ n : ℕ, g n ≤ (2 : ℝ) ^ ((n : ℝ) + r n) := by
  let r (n : ℕ) : ℝ := max (Real.logb 2 (max (g n) 1) - n) 0
  have htwo : (1 : ℝ) < 2 := by norm_num
  have hpos (n : ℕ) : 0 < max (g n) 1 := zero_lt_one.trans_le (le_max_right _ _)
  refine ⟨r, ?_, fun n => ?_⟩
  · refine isLittleO_iff.mpr fun ε hε => ?_
    filter_upwards [h ε hε] with n hn
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h₁ : (1 : ℝ) ≤ (2 : ℝ) ^ ((1 + ε) * n) := by
      rw [← Real.rpow_zero 2]
      exact (Real.rpow_le_rpow_left_iff htwo).mpr (by positivity)
    have hm := max_le hn h₁
    have hl := (Real.logb_le_iff_le_rpow htwo (hpos n)).mpr hm
    rw [Real.norm_of_nonneg (le_max_right _ _), Real.norm_of_nonneg hn0]
    exact max_le (by linarith) (mul_nonneg hε.le hn0)
  · apply (le_max_left _ _).trans
    apply (Real.logb_le_iff_le_rpow htwo (hpos n)).mp
    have hr : Real.logb 2 (max (g n) 1) - n ≤ r n := le_max_left _ _
    linarith

private theorem from_epsilon_cardSet
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ⌊(2 : ℝ) ^ ((1 + ε) * n)⌋₊ ∈ Erdos107.cardSet n) :
    ∃ r : ℕ → ℝ, r =o[atTop] (fun n => (n : ℝ)) ∧
      ∀ n ≥ 3, (Erdos107.f n : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) + r n) := by
  obtain ⟨r, hr, hrb⟩ := from_eventual_epsilon (g := fun n => (Erdos107.f n : ℝ)) (by
    intro ε hε
    filter_upwards [h ε hε] with n hn
    exact (Nat.cast_le.mpr (Nat.sInf_le hn)).trans (Nat.floor_le (by positivity)))
  exact ⟨r, hr, fun n _ => hrb n⟩

/-- The threshold set is upward closed: pass to a subset of the right size. -/
private theorem cardSet_mono {n N M : ℕ} (hN : N ∈ Erdos107.cardSet n) (hNM : N ≤ M) :
    M ∈ Erdos107.cardSet n := by
  intro pts hcard hnt
  obtain ⟨Q, hQ, hQc⟩ := Finset.exists_subset_card_eq (s := pts) (n := N)
    (hNM.trans hcard.ge)
  have hQ' : (Q : Set (EuclideanSpace ℝ (Fin 2))) ⊆ (pts : Set (EuclideanSpace ℝ (Fin 2))) :=
    Finset.coe_subset.mpr hQ
  obtain ⟨S, hS, hSQ, hconv⟩ := hN Q hQc
    (fun a ha b hb c hc => hnt (hQ' ha) (hQ' hb) (hQ' hc))
  exact ⟨S, hS, hSQ.trans hQ', hconv⟩

/-- It suffices to find, for every positive ε and every large n, SOME threshold
below 2^((1+ε)n); no floor is needed. -/
private theorem from_epsilon_exists
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∃ N : ℕ, (N : ℝ) ≤ (2 : ℝ) ^ ((1 + ε) * n) ∧ N ∈ Erdos107.cardSet n) :
    ∃ r : ℕ → ℝ, r =o[atTop] (fun n => (n : ℝ)) ∧
      ∀ n ≥ 3, (Erdos107.f n : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) + r n) := by
  apply from_epsilon_cardSet
  intro ε hε
  filter_upwards [h ε hε] with n hn
  obtain ⟨N, hN, hmem⟩ := hn
  exact cardSet_mono hmem (Nat.le_floor hN)

/- Reduction to plain coordinates. -/

private theorem finite_image_pullback {α β : Type*} [DecidableEq β] (L : α → β)
    (X : Finset α) (Z : Finset β) (hZ : Z ⊆ X.image L) (hL : Set.InjOn L (X : Set α)) :
    ∃ Y ⊆ X, Y.image L = Z ∧ Y.card = Z.card := by
  classical
  let Y := X.filter fun y => L y ∈ Z
  have hYX : Y ⊆ X := Finset.filter_subset _ _
  have hYZ : Y.image L = Z := by
    ext z
    constructor
    · intro hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      exact (Finset.mem_filter.mp hy).2
    · intro hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (hZ hz)
      exact Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨hy, hz⟩, rfl⟩
  refine ⟨Y, hYX, hYZ, ?_⟩
  rw [← hYZ, Finset.card_image_of_injOn (hL.mono hYX)]

private theorem planar_coordinates (X : Finset (EuclideanSpace ℝ (Fin 2))) :
    ∃ x y : (EuclideanSpace ℝ (Fin 2)) →ₗ[ℝ] ℝ,
      Set.InjOn x (X : Set (EuclideanSpace ℝ (Fin 2))) ∧
      ∀ p q, x p = x q → y p = y q → p = q := by
  classical
  let bad := (X ×ˢ X).image fun uv : (EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)) =>
    (uv.2 0 - uv.1 0) / (uv.1 1 - uv.2 1)
  obtain ⟨t, ht⟩ := bad.exists_notMem
  let x : (EuclideanSpace ℝ (Fin 2)) →ₗ[ℝ] ℝ :=
    EuclideanSpace.projₗ 0 + t • EuclideanSpace.projₗ 1
  let y : (EuclideanSpace ℝ (Fin 2)) →ₗ[ℝ] ℝ := EuclideanSpace.projₗ 1
  have hjoint (p q : EuclideanSpace ℝ (Fin 2)) (hx : x p = x q) (hy : y p = y q) : p = q := by
    change p 0 + t * p 1 = q 0 + t * q 1 at hx
    change p 1 = q 1 at hy
    apply PiLp.ext
    intro i
    fin_cases i
    · change p 0 = q 0
      rw [hy] at hx
      exact add_right_cancel hx
    · exact hy
  refine ⟨x, y, ?_, hjoint⟩
  intro p hp q hq hx
  by_cases hy : y p = y q
  · exact hjoint p q hx hy
  · exfalso
    apply ht
    refine Finset.mem_image.mpr ⟨(p, q), Finset.mem_product.mpr ⟨hp, hq⟩, ?_⟩
    change p 0 + t * p 1 = q 0 + t * q 1 at hx
    change p 1 ≠ q 1 at hy
    apply (div_eq_iff (sub_ne_zero.mpr hy)).mpr
    nlinarith only [hx]

private theorem orient_ne_in_image (X : Finset (EuclideanSpace ℝ (Fin 2)))
    (hX : EuclideanGeometry.NonTrilinear (X : Set (EuclideanSpace ℝ (Fin 2))))
    (x y : (EuclideanSpace ℝ (Fin 2)) →ₗ[ℝ] ℝ)
    (hjoint : ∀ p q, x p = x q → y p = y q → p = q) :
    ∀ a ∈ X.image (x.prod y), ∀ b ∈ X.image (x.prod y), ∀ c ∈ X.image (x.prod y),
      a.1 < b.1 → b.1 < c.1 →
        (b.1 - a.1) * (c.2 - b.2) - (b.2 - a.2) * (c.1 - b.1) ≠ 0 := by
  intro u hu v hv w hw hab hbc he
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hu
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hv
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hw
  change x a < x b at hab
  change x b < x c at hbc
  change (x b - x a) * (y c - y b) - (y b - y a) * (x c - x b) = 0 at he
  have hnab : a ≠ b := fun h => hab.ne (congrArg x h)
  have hnbc : b ≠ c := fun h => hbc.ne (congrArg x h)
  have hnac : a ≠ c := fun h => (hab.trans hbc).ne (congrArg x h)
  apply hX ha hb hc hnab hnbc hnac
  let r := (x b - x a) / (x c - x b)
  have hden := sub_ne_zero.mpr hbc.ne'
  have hxb : x b - x a = r * (x c - x b) := by
    dsimp [r]
    rw [div_mul_cancel₀ _ hden]
  have hyb : y b - y a = r * (y c - y b) := by
    dsimp [r]
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hden).2
    linarith only [he]
  have hdiff : b - a = r • (c - b) := by
    apply hjoint
    · simpa only [map_sub, map_smul, smul_eq_mul] using hxb
    · simpa only [map_sub, map_smul, smul_eq_mul] using hyb
  apply (collinear_iff_of_mem (show b ∈ ({a, b, c} : Set (EuclideanSpace ℝ (Fin 2))) by simp)).mpr
  refine ⟨c - b, ?_⟩
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · refine ⟨-r, ?_⟩
    change _ = (-r) • (c - b) + b
    rw [neg_smul, ← hdiff]
    abel
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩

/-- Bridge: a coordinate statement about finite subsets of the real plane (distinct
abscissas, no flat triple, strictly extreme points) gives a member of the threshold set. -/
private theorem cardSet_of_planar {n N : ℕ}
    (h : ∀ X : Finset (ℝ × ℝ), X.card = N →
        Set.InjOn Prod.fst (X : Set (ℝ × ℝ)) →
        (∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, a.1 < b.1 → b.1 < c.1 →
          (b.1 - a.1) * (c.2 - b.2) - (b.2 - a.2) * (c.1 - b.1) ≠ 0) →
        ∃ Y ⊆ X, Y.card = n ∧
          ∀ p ∈ Y, ∃ u v : ℝ, ∀ q ∈ Y, q ≠ p → u * p.1 + v * p.2 < u * q.1 + v * q.2) :
    N ∈ Erdos107.cardSet n := by
  classical
  intro pts hcard hnt
  obtain ⟨x, y, hx, hxy⟩ := planar_coordinates pts
  let L := x.prod y
  have hL : Function.Injective L := fun a b he =>
    hxy a b (congrArg Prod.fst he) (congrArg Prod.snd he)
  have hinj : Set.InjOn Prod.fst (↑(pts.image L) : Set (ℝ × ℝ)) := by
    intro u hu v hv he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hu
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hv
    exact congrArg L (hx ha hb he)
  obtain ⟨Y, hYX, hYc, hYconv⟩ := h (pts.image L)
    (by rw [Finset.card_image_of_injective _ hL, hcard])
    hinj (orient_ne_in_image pts hnt x y hxy)
  obtain ⟨Z, hZP, hZY, hZc⟩ := finite_image_pullback L pts Y hYX hL.injOn
  refine ⟨Z, hZc.trans hYc, Finset.coe_subset.mpr hZP, ?_⟩
  intro a ha hmem
  have haY : L a ∈ Y := by
    rw [← hZY]
    exact Finset.mem_image_of_mem L ha
  obtain ⟨u, v, huv⟩ := hYconv (L a) haY
  let Λ : (EuclideanSpace ℝ (Fin 2)) →ₗ[ℝ] ℝ := u • x + v • y
  have hsub : (Z : Set (EuclideanSpace ℝ (Fin 2))) \ {a} ⊆ {q | Λ a < Λ q} := by
    intro q hq
    have hqY : L q ∈ Y := by
      rw [← hZY]
      exact Finset.mem_image_of_mem L hq.1
    have hne : L q ≠ L a := fun he => hq.2 (hL he)
    have hlt := huv (L q) hqY hne
    change u * x a + v * y a < u * x q + v * y q
    exact hlt
  have he := (convexHull_min hsub (convex_halfSpace_gt Λ.isLinear (Λ a))) hmem
  exact lt_irrefl (Λ a) he

/-- Suk's planar theorem for even n. -/
def H1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ᶠ n : ℕ in atTop, Even n →
    ∃ N : ℕ, (N : ℝ) ≤ (2 : ℝ) ^ ((1 + ε) * n) ∧
      ∀ X : Finset (ℝ × ℝ), X.card = N →
        Set.InjOn Prod.fst (X : Set (ℝ × ℝ)) →
        (∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, a.1 < b.1 → b.1 < c.1 →
          (b.1 - a.1) * (c.2 - b.2) - (b.2 - a.2) * (c.1 - b.1) ≠ 0) →
        ∃ Y ⊆ X, Y.card = n ∧
          ∀ p ∈ Y, ∃ u v : ℝ, ∀ q ∈ Y, q ≠ p → u * p.1 + v * p.2 < u * q.1 + v * q.2

/-- Suk's planar theorem for odd n. -/
def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ᶠ n : ℕ in atTop, Odd n →
    ∃ N : ℕ, (N : ℝ) ≤ (2 : ℝ) ^ ((1 + ε) * n) ∧
      ∀ X : Finset (ℝ × ℝ), X.card = N →
        Set.InjOn Prod.fst (X : Set (ℝ × ℝ)) →
        (∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, a.1 < b.1 → b.1 < c.1 →
          (b.1 - a.1) * (c.2 - b.2) - (b.2 - a.2) * (c.1 - b.1) ≠ 0) →
        ∃ Y ⊆ X, Y.card = n ∧
          ∀ p ∈ Y, ∃ u v : ℝ, ∀ q ∈ Y, q ≠ p → u * p.1 + v * p.2 < u * q.1 + v * q.2

theorem main : H1 → H2 → type_of% @Erdos107.variants.su_bound := by
  intro h1 h2
  apply from_epsilon_exists
  intro ε hε
  have hall : ∀ᶠ n : ℕ in atTop,
      ∃ N : ℕ, (N : ℝ) ≤ (2 : ℝ) ^ ((1 + ε) * n) ∧
        ∀ X : Finset (ℝ × ℝ), X.card = N →
        Set.InjOn Prod.fst (X : Set (ℝ × ℝ)) →
        (∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, a.1 < b.1 → b.1 < c.1 →
          (b.1 - a.1) * (c.2 - b.2) - (b.2 - a.2) * (c.1 - b.1) ≠ 0) →
        ∃ Y ⊆ X, Y.card = n ∧
          ∀ p ∈ Y, ∃ u v : ℝ, ∀ q ∈ Y, q ≠ p → u * p.1 + v * p.2 < u * q.1 + v * q.2 := by
    set δ : ℝ := min ε (1 / 2) with hδ
    have hδ0 : 0 < δ := lt_min hε (by norm_num)
    have hδ1 : δ < 1 := (min_le_right _ _).trans_lt (by norm_num)
    have hδε : δ ≤ ε := min_le_left _ _
    filter_upwards [h1 δ hδ0 hδ1, h2 δ hδ0 hδ1] with n hE hO
    have hmono : ∀ N : ℕ, (N : ℝ) ≤ (2 : ℝ) ^ ((1 + δ) * n) →
        (N : ℝ) ≤ (2 : ℝ) ^ ((1 + ε) * n) := fun N hN => hN.trans
      (Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg n)))
    rcases Nat.even_or_odd n with he | ho
    · obtain ⟨N, hN, hX⟩ := hE he
      exact ⟨N, hmono N hN, hX⟩
    · obtain ⟨N, hN, hX⟩ := hO ho
      exact ⟨N, hmono N hN, hX⟩
  filter_upwards [hall] with n hn
  obtain ⟨N, hN, hX⟩ := hn
  exact ⟨N, hN, cardSet_of_planar hX⟩

end OMA.R_Erdos107_variants_su_bound_R1
