import FormalConjectures.ErdosProblems.«1088»
import Mathlib

/-! Proof of Erdos1088.f_isLeast by induction on dimension via hyperplanes and spheres. -/

open Finset BigOperators
open scoped RealInnerProductSpace

namespace OMA_Erdos1088

private lemma pairwiseDistinct_of_inj {X : Type*} [MetricSpace X] (A : Finset X)
    (hinj : ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
      a ≠ b → c ≠ d → dist a b = dist c d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)) :
    distinctDistances A = Nat.choose A.card 2 := by
  classical
  unfold distinctDistances distanceSet
  let f : Sym2 X → ℝ := Sym2.lift ⟨dist, dist_comm⟩
  have hEq : (A.offDiag.image fun pair : X × X => dist pair.1 pair.2) =
      (A.offDiag.image (fun p : X × X => s(p.1, p.2))).image f := by
    ext r
    simp only [Finset.mem_image, Finset.mem_offDiag]
    constructor
    · rintro ⟨⟨a, b⟩, ⟨ha, hb, hab⟩, rfl⟩
      exact ⟨s(a, b), ⟨⟨a, b⟩, ⟨ha, hb, hab⟩, rfl⟩, rfl⟩
    · rintro ⟨p, ⟨⟨a, b⟩, ⟨ha, hb, hab⟩, rfl⟩, rfl⟩
      exact ⟨⟨a, b⟩, ⟨ha, hb, hab⟩, rfl⟩
  rw [hEq, Finset.card_image_of_injOn]
  · exact Sym2.card_image_offDiag A
  · intro p1 hp1 p2 hp2 hfeq
    simp only [Finset.mem_coe, Finset.mem_image, Finset.mem_offDiag] at hp1 hp2
    rcases hp1 with ⟨⟨a, b⟩, ⟨ha, hb, hab⟩, rfl⟩
    rcases hp2 with ⟨⟨c, d⟩, ⟨hc, hd, hcd⟩, rfl⟩
    have hd_eq : dist a b = dist c d := hfeq
    rcases hinj a ha b hb c hc d hd hab hcd hd_eq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact Sym2.eq_swap

private lemma dist_eq_iff_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x a b : E) :
    dist x a = dist x b ↔
      2 * @inner ℝ E _ x (b - a) = ‖b‖ ^ 2 - ‖a‖ ^ 2 := by
  rw [dist_eq_norm, dist_eq_norm]
  have h1 : ‖x - a‖ = ‖x - b‖ ↔ ‖x - a‖ ^ 2 = ‖x - b‖ ^ 2 := by
    constructor
    · intro h; rw [h]
    · intro h
      have hnn1 : 0 ≤ ‖x - a‖ := norm_nonneg _
      have hnn2 : 0 ≤ ‖x - b‖ := norm_nonneg _
      nlinarith
  rw [h1, norm_sub_sq_real, norm_sub_sq_real, inner_sub_right]
  constructor <;> intro h <;> linarith

private lemma sphere_inter_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x c a : E) (r ρ : ℝ) (hc : dist x c = r) (ha : dist x a = ρ) :
    2 * @inner ℝ E _ x (a - c) = ‖a‖ ^ 2 - ‖c‖ ^ 2 + r ^ 2 - ρ ^ 2 := by
  rw [dist_eq_norm] at hc ha
  have h1 : ‖x - c‖ ^ 2 = r ^ 2 := by rw [hc]
  have h2 : ‖x - a‖ ^ 2 = ρ ^ 2 := by rw [ha]
  rw [norm_sub_sq_real] at h1 h2
  rw [inner_sub_right]
  linarith

private lemma exists_subset_of_isometry {E F : Type*} [MetricSpace E] [MetricSpace F] [DecidableEq E]
    (g : F → E) (hg : Isometry g) {n : ℕ} {T : Finset F} {S : Finset E}
    (hT : T.image g ⊆ S)
    (hA : ∃ A ⊆ T, A.card = n ∧ distinctDistances A = Nat.choose A.card 2) :
    ∃ B ⊆ S, B.card = n ∧ distinctDistances B = Nat.choose B.card 2 := by
  classical
  rcases hA with ⟨A, hAT, hAcard, hAdist⟩
  refine ⟨A.image g, Finset.Subset.trans (Finset.image_subset_image hAT) hT, ?_, ?_⟩
  · rw [Finset.card_image_of_injective A hg.injective, hAcard]
  · rw [Finset.card_image_of_injective A hg.injective]
    have hEq : distanceSet (A.image g) = distanceSet A := by
      ext r
      simp only [distanceSet, Finset.mem_image, Finset.mem_offDiag]
      constructor
      · rintro ⟨⟨x, y⟩, ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩, hne⟩, rfl⟩
        exact ⟨⟨a, b⟩, ⟨ha, hb, fun h => hne (congrArg g h)⟩, (hg.dist_eq a b).symm⟩
      · rintro ⟨⟨a, b⟩, ⟨ha, hb, hne⟩, rfl⟩
        exact ⟨⟨g a, g b⟩, ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩, fun h => hne (hg.injective h)⟩, hg.dist_eq a b⟩
    unfold distinctDistances
    rw [hEq]
    exact hAdist

private lemma exists_of_hyperplane {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {k n H : ℕ}
    (hdim : Module.finrank ℝ E ≤ k + 1)
    (ih : ∀ (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F],
      Module.finrank ℝ F ≤ k →
      ∀ T : Finset F, H ≤ T.card →
        ∃ A ⊆ T, A.card = n ∧ distinctDistances A = Nat.choose A.card 2)
    (S : Finset E) (v : E) (hv : v ≠ 0) (c : ℝ)
    (hcard : H ≤ (S.filter fun x => @inner ℝ E _ x v = c).card) :
    ∃ A ⊆ S, A.card = n ∧ distinctDistances A = Nat.choose A.card 2 := by
  classical
  set P := S.filter fun x => @inner ℝ E _ x v = c
  by_cases hH0 : H = 0
  · subst hH0
    have h0 := ih (Submodule.span ℝ ({v} : Set E))ᗮ (by
      have hspan : Module.finrank ℝ (Submodule.span ℝ ({v} : Set E)) = 1 :=
        finrank_span_singleton hv
      have hadd := Submodule.finrank_add_finrank_orthogonal (Submodule.span ℝ ({v} : Set E))
      omega) ∅ (le_refl 0)
    rcases h0 with ⟨A, hA0, hAc, hAd⟩
    have hAe : A = ∅ := Finset.subset_empty.mp hA0
    subst hAe
    exact ⟨∅, Finset.empty_subset S, hAc, hAd⟩
  · have hPne : P.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨x0, hx0⟩ := hPne
    have hx0_in : @inner ℝ E _ x0 v = c := (Finset.mem_filter.mp hx0).2
    let W : Submodule ℝ E := (Submodule.span ℝ ({v} : Set E))ᗮ
    have hWdim : Module.finrank ℝ W ≤ k := by
      have hspan : Module.finrank ℝ (Submodule.span ℝ ({v} : Set E)) = 1 :=
        finrank_span_singleton hv
      have hadd := Submodule.finrank_add_finrank_orthogonal (Submodule.span ℝ ({v} : Set E))
      dsimp only [W]
      omega
    have hmemW : ∀ x ∈ P, x - x0 ∈ W := by
      intro x hx
      have hx_in : @inner ℝ E _ x v = c := (Finset.mem_filter.mp hx).2
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
      rw [real_inner_comm, inner_sub_left, hx_in, hx0_in, sub_self]
    let T : Finset W := P.attach.image fun ⟨x, hx⟩ => ⟨x - x0, hmemW x hx⟩
    have hTcard : T.card = P.card := by
      rw [Finset.card_image_of_injective]
      · exact Finset.card_attach
      · intro ⟨a, _⟩ ⟨b, _⟩ h
        have hsub : a - x0 = b - x0 := congrArg Subtype.val h
        exact Subtype.ext (sub_left_inj.mp hsub)
    let g : W → E := fun w => (w : E) + x0
    have hg : Isometry g := by
      refine Isometry.of_dist_eq fun a b => ?_
      simp only [g, dist_add_right]
      rfl
    have hTsub : T.image g ⊆ S := by
      intro y hy
      rw [Finset.mem_image] at hy
      rcases hy with ⟨w, hw, rfl⟩
      rw [Finset.mem_image] at hw
      rcases hw with ⟨⟨x, hx⟩, _, rfl⟩
      simp only [g, sub_add_cancel]
      exact (Finset.mem_filter.mp hx).1
    exact exists_subset_of_isometry g hg hTsub (ih W hWdim T (by omega))

/-- Greedy construction given uniform upper bounds `Hb` on bisectors and `Hs` on spheres. -/
private lemma greedy_distinct {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : Finset E) (n Hb Hs : ℕ)
    (hbis : ∀ a b : E, a ≠ b → (S.filter fun x => dist x a = dist x b).card ≤ Hb)
    (hsph : ∀ a ∈ S, ∀ r : ℝ, (S.filter fun x => dist x a = r).card ≤ Hs)
    (hS : n + n * n * Hb + n * n * n * Hs ≤ S.card) :
    ∃ A ⊆ S, A.card = n ∧
      ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
        a ≠ b → c ≠ d → dist a b = dist c d → (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  classical
  have hstep : ∀ j ≤ n, ∃ A ⊆ S, A.card = j ∧
      ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
        a ≠ b → c ≠ d → dist a b = dist c d → (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
    intro j
    induction j with
    | zero =>
      intro _
      exact ⟨∅, Finset.empty_subset S, rfl, fun a ha => absurd ha (Finset.notMem_empty a)⟩
    | succ j ih =>
      intro hj
      obtain ⟨A, hAS, hAcard, hAinj⟩ := ih (by omega)
      -- Collect all bad points x ∈ S: either x ∈ A, or x on a bisector of A, or dist x a = dist b c
      let badBis : Finset E :=
        (A.offDiag).biUnion fun p => S.filter fun x => dist x p.1 = dist x p.2
      let badSph : Finset E :=
        (A ×ˢ A.offDiag).biUnion fun q => S.filter fun x => dist x q.1 = dist q.2.1 q.2.2
      let bad : Finset E := A ∪ badBis ∪ badSph
      have hbadBis : badBis.card ≤ j * j * Hb := by
        calc badBis.card
            ≤ ∑ p ∈ A.offDiag, (S.filter fun x => dist x p.1 = dist x p.2).card :=
              Finset.card_biUnion_le
          _ ≤ ∑ _p ∈ A.offDiag, Hb := Finset.sum_le_sum fun p hp =>
              hbis p.1 p.2 (Finset.mem_offDiag.mp hp).2.2
          _ = A.offDiag.card * Hb := by rw [Finset.sum_const, smul_eq_mul]
          _ ≤ (j * j) * Hb := by
              have h1 : A.offDiag.card ≤ A.card * A.card := by
                rw [Finset.offDiag_card]; exact Nat.sub_le _ _
              rw [hAcard] at h1
              exact Nat.mul_le_mul_right Hb h1
      have hbadSph : badSph.card ≤ j * j * j * Hs := by
        calc badSph.card
            ≤ ∑ q ∈ A ×ˢ A.offDiag, (S.filter fun x => dist x q.1 = dist q.2.1 q.2.2).card :=
              Finset.card_biUnion_le
          _ ≤ ∑ _q ∈ A ×ˢ A.offDiag, Hs := Finset.sum_le_sum fun q hq =>
              hsph q.1 (hAS (Finset.mem_product.mp hq).1) (dist q.2.1 q.2.2)
          _ = (A ×ˢ A.offDiag).card * Hs := by rw [Finset.sum_const, smul_eq_mul]
          _ ≤ (j * j * j) * Hs := by
              have h1 : A.offDiag.card ≤ j * j := by
                rw [Finset.offDiag_card, hAcard]; exact Nat.sub_le _ _
              have h2 : (A ×ˢ A.offDiag).card ≤ j * j * j := by
                rw [Finset.card_product, hAcard]
                calc j * A.offDiag.card ≤ j * (j * j) := Nat.mul_le_mul_left j h1
                  _ = j * j * j := by ring
              exact Nat.mul_le_mul_right Hs h2
      have hbad_lt : bad.card < S.card := by
        have h1 : bad.card ≤ A.card + badBis.card + badSph.card :=
          le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right (Finset.card_union_le _ _) _)
        have hj2 : j * j ≤ n * n := Nat.mul_le_mul (by omega) (by omega)
        have hj3 : j * j * j ≤ n * n * n := Nat.mul_le_mul hj2 (by omega)
        have hb1 : j * j * Hb ≤ n * n * Hb := Nat.mul_le_mul_right Hb hj2
        have hb2 : j * j * j * Hs ≤ n * n * n * Hs := Nat.mul_le_mul_right Hs hj3
        omega
      have hne : (S \ bad).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hemp
        have hsub : S ⊆ bad := Finset.sdiff_eq_empty_iff_subset.mp hemp
        have := Finset.card_le_card hsub
        omega
      obtain ⟨x, hx⟩ := hne
      rw [Finset.mem_sdiff] at hx
      rcases hx with ⟨hxS, hxnot⟩
      have hxnotA : x ∉ A := fun h => hxnot (Finset.mem_union_left _ (Finset.mem_union_left _ h))
      have hxnotBis : x ∉ badBis := fun h => hxnot (Finset.mem_union_left _ (Finset.mem_union_right _ h))
      have hxnotSph : x ∉ badSph := fun h => hxnot (Finset.mem_union_right _ h)
      refine ⟨insert x A, Finset.insert_subset_iff.mpr ⟨hxS, hAS⟩, by
        rw [Finset.card_insert_of_notMem hxnotA, hAcard], ?_⟩
      intro a ha b hb c hc d hd hab hcd hdeq
      rw [Finset.mem_insert] at ha hb hc hd
      have hno_x_eq : ∀ u ∈ A, ∀ v ∈ A, u ≠ v → dist x u ≠ dist x v := fun u hu v hv huv heq =>
        hxnotBis (Finset.mem_biUnion.mpr ⟨(u, v), Finset.mem_offDiag.mpr ⟨hu, hv, huv⟩,
          Finset.mem_filter.mpr ⟨hxS, heq⟩⟩)
      have hno_x_old : ∀ u ∈ A, ∀ v ∈ A, ∀ w ∈ A, v ≠ w → dist x u ≠ dist v w :=
        fun u hu v hv w hw hvw heq =>
        hxnotSph (Finset.mem_biUnion.mpr ⟨(u, (v, w)),
          Finset.mem_product.mpr ⟨hu, Finset.mem_offDiag.mpr ⟨hv, hw, hvw⟩⟩,
          Finset.mem_filter.mpr ⟨hxS, heq⟩⟩)
      rcases ha with rfl | ha <;> rcases hb with rfl | hb <;>
        rcases hc with rfl | hc <;> rcases hd with rfl | hd
      · exact absurd rfl hab
      · exact absurd rfl hab
      · exact absurd rfl hab
      · exact absurd rfl hab
      · exact absurd rfl hcd
      · by_cases h : b = d
        · left; exact ⟨rfl, h⟩
        · exact absurd hdeq (hno_x_eq b hb d hd h)
      · by_cases h : b = c
        · right; exact ⟨rfl, h⟩
        · exact absurd (by rw [eq_comm, dist_comm, eq_comm] at hdeq; exact hdeq) (hno_x_eq b hb c hc h)
      · exact absurd hdeq (hno_x_old b hb c hc d hd hcd)
      · exact absurd rfl hcd
      · by_cases h : a = d
        · right; exact ⟨h, rfl⟩
        · exact absurd (by rw [dist_comm] at hdeq; exact hdeq) (hno_x_eq a ha d hd h)
      · by_cases h : a = c
        · left; exact ⟨h, rfl⟩
        · exact absurd (by rw [dist_comm, eq_comm, dist_comm, eq_comm] at hdeq; exact hdeq) (hno_x_eq a ha c hc h)
      · exact absurd (by rw [dist_comm] at hdeq; exact hdeq) (hno_x_old a ha c hc d hd hcd)
      · exact absurd rfl hcd
      · exact absurd hdeq.symm (hno_x_old d hd a ha b hb hab)
      · exact absurd (by rw [dist_comm, eq_comm]; exact hdeq) (hno_x_old c hc a ha b hb hab)
      · exact hAinj a ha b hb c hc d hd hab hcd hdeq
  exact hstep n le_rfl

/-- Main induction on dimension `k`: uniform bound `m(k, n)` independent of the space `E`. -/
private lemma exists_distinct_subset_dim :
    ∀ k n : ℕ, ∃ m : ℕ, n ≤ m ∧
      ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E],
        Module.finrank ℝ E ≤ k →
        ∀ S : Finset E, m ≤ S.card →
          ∃ A ⊆ S, A.card = n ∧ distinctDistances A = Nat.choose A.card 2 := by
  intro k
  induction k with
  | zero =>
    intro n
    refine ⟨max n 2, le_max_left n 2, fun E _ _ _ hdim S hS => ?_⟩
    exfalso
    have hsub : Subsingleton E :=
      Module.finrank_zero_iff.mp (Nat.eq_zero_of_le_zero hdim)
    have hle1 : S.card ≤ 1 := Finset.card_le_one.mpr (fun a _ b _ => Subsingleton.elim a b)
    have hge2 : 2 ≤ S.card := le_trans (le_max_right n 2) hS
    omega
  | succ k ih =>
    intro n
    obtain ⟨H, hHn, hIH⟩ := ih n
    let K1 : ℕ := max 2 (n + n * n * H + n * n * n * H)
    let K2 : ℕ := max n (n + n * n * H + n * n * n * K1)
    refine ⟨K2, le_max_left _ _, fun E _ _ _ hdim S hS => ?_⟩
    classical
    -- Case 1: Some hyperplane contains ≥ H points of S
    by_cases hhyp : ∃ (v : E) (c : ℝ), v ≠ 0 ∧ H ≤ (S.filter fun x => @inner ℝ E _ x v = c).card
    · rcases hhyp with ⟨v, c, hv, hcard⟩
      exact exists_of_hyperplane hdim (fun F _ _ _ hF T hT => hIH F hF T hT) S v hv c hcard
    · push Not at hhyp
      -- Every hyperplane has < H (hence ≤ H) points of S!
      -- Case 2: Some sphere contains ≥ K1 points of S
      by_cases hsph : ∃ (c : E) (r : ℝ), K1 ≤ (S.filter fun x => dist x c = r).card
      · rcases hsph with ⟨c, r, hcard⟩
        set T := S.filter fun x => dist x c = r
        have hTbis : ∀ a b : E, a ≠ b → (T.filter fun x => dist x a = dist x b).card ≤ H := by
          intro a b hab
          have hv : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
          have hsub : (T.filter fun x => dist x a = dist x b) ⊆
              S.filter fun x => @inner ℝ E _ x (b - a) = (‖b‖ ^ 2 - ‖a‖ ^ 2) / 2 := by
            intro x hx
            simp only [T, Finset.mem_filter] at hx ⊢
            refine ⟨hx.1.1, ?_⟩
            have h1 := (dist_eq_iff_inner x a b).mp hx.2
            linarith
          exact le_trans (Finset.card_le_card hsub) (le_of_lt (hhyp (b - a) _ hv))
        have hc_not_mem : c ∉ T := by
          intro hcT
          have hr0 : r = 0 := by
            have := (Finset.mem_filter.mp hcT).2
            rw [dist_self] at this
            exact this.symm
          have hTle1 : T.card ≤ 1 := Finset.card_le_one.mpr fun x hx y hy => by
            have hx0 : dist x c = 0 := by rw [← hr0]; exact (Finset.mem_filter.mp hx).2
            have hy0 : dist y c = 0 := by rw [← hr0]; exact (Finset.mem_filter.mp hy).2
            rw [dist_eq_zero.mp hx0, dist_eq_zero.mp hy0]
          have hK1ge2 : 2 ≤ K1 := le_max_left _ _
          omega
        have hTsph : ∀ a ∈ T, ∀ ρ : ℝ, (T.filter fun x => dist x a = ρ).card ≤ H := by
          intro a haT ρ
          have hac : a ≠ c := fun h => hc_not_mem (h ▸ haT)
          have hv : a - c ≠ 0 := sub_ne_zero.mpr hac
          have hsub : (T.filter fun x => dist x a = ρ) ⊆
              S.filter fun x => @inner ℝ E _ x (a - c) = (‖a‖ ^ 2 - ‖c‖ ^ 2 + r ^ 2 - ρ ^ 2) / 2 := by
            intro x hx
            simp only [T, Finset.mem_filter] at hx ⊢
            refine ⟨hx.1.1, ?_⟩
            have h1 := sphere_inter_inner x c a r ρ hx.1.2 hx.2
            linarith
          exact le_trans (Finset.card_le_card hsub) (le_of_lt (hhyp (a - c) _ hv))
        obtain ⟨A, hAT, hAcard, hAinj⟩ :=
          greedy_distinct T n H H hTbis hTsph (le_trans (le_max_right _ _) hcard)
        exact ⟨A, Finset.Subset.trans hAT (Finset.filter_subset _ _), hAcard, pairwiseDistinct_of_inj A hAinj⟩
      · push Not at hsph
        have hSbis : ∀ a b : E, a ≠ b → (S.filter fun x => dist x a = dist x b).card ≤ H := by
          intro a b hab
          have hv : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
          have hsub : (S.filter fun x => dist x a = dist x b) ⊆
              S.filter fun x => @inner ℝ E _ x (b - a) = (‖b‖ ^ 2 - ‖a‖ ^ 2) / 2 := by
            intro x hx
            simp only [Finset.mem_filter] at hx ⊢
            refine ⟨hx.1, ?_⟩
            have h1 := (dist_eq_iff_inner x a b).mp hx.2
            linarith
          exact le_trans (Finset.card_le_card hsub) (le_of_lt (hhyp (b - a) _ hv))
        have hSsph : ∀ a ∈ S, ∀ ρ : ℝ, (S.filter fun x => dist x a = ρ).card ≤ K1 :=
          fun a _ ρ => le_of_lt (hsph a ρ)
        obtain ⟨A, hAS, hAcard, hAinj⟩ :=
          greedy_distinct S n H K1 hSbis hSsph (le_trans (le_max_right _ _) hS)
        exact ⟨A, hAS, hAcard, pairwiseDistinct_of_inj A hAinj⟩

end OMA_Erdos1088

theorem OMA.solution : type_of% @Erdos1088.f_isLeast := by
  intro d n
  have hne : (Erdos1088.cardSet d n).Nonempty := by
    obtain ⟨m, hnm, hm⟩ := OMA_Erdos1088.exists_distinct_subset_dim d n
    refine ⟨m, hnm, fun S hS => ?_⟩
    have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) ≤ d := by
      rw [finrank_euclideanSpace_fin]
    exact hm (EuclideanSpace ℝ (Fin d)) hdim S (le_of_eq hS.symm)
  exact ⟨Nat.sInf_mem hne, fun m hm => Nat.sInf_le hm⟩
