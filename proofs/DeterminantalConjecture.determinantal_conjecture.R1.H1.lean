import OMAReductions.R_DeterminantalConjecture_determinantal_conjecture_R1
import Mathlib

/-!
Two-row marginals for the Marcus–de Oliveira determinantal reduction.
Lean formalization by @sobrien032 using Codex, for the reduction by @desenyon.

For two distinct marked rows we compare linear scores on their two images and
on the unordered image pair. Swapping the images can only improve the signed
mean score after integration over cuts. The best score is constant on each
unordered pair, which has nonnegative total mass. Convex separation then gives
nonnegative normalized weights with the original marginals.
-/

/- The signed mass crossing a cut from the first marked row to the second is nonnegative. -/

open scoped BigOperators
namespace DeterminantalCut

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem cut_nonneg (w : Equiv.Perm n → ℝ)
    (h : ∀ I J : Finset n, 0 ≤ ∑ σ : Equiv.Perm n,
      w σ * (if ∀ i ∈ I, σ i ∈ J then (1 : ℝ) else 0))
    (a b : n) (A : Finset n) :
    0 ≤ ∑ σ : Equiv.Perm n, if σ a ∈ A ∧ σ b ∉ A then w σ else 0 := by
  classical
  let pre (σ : Equiv.Perm n) := A.map σ.symm.toEmbedding
  have mem_pre (σ : Equiv.Perm n) (i : n) : i ∈ pre σ ↔ σ i ∈ A := by
    simp [pre]
  let choices := Finset.univ.filter (fun I : Finset n => I.card = A.card ∧ a ∈ I ∧ b ∉ I)
  have good (σ : Equiv.Perm n) : pre σ ∈ choices ↔ σ a ∈ A ∧ σ b ∉ A := by
    simp [choices, pre]
  have weight (I : Finset n) (hI : I ∈ choices) :
      0 ≤ ∑ σ : Equiv.Perm n with pre σ = I, w σ := by
    have hc : I.card = A.card := (Finset.mem_filter.mp hI).2.1
    have iff_sub (σ : Equiv.Perm n) :
        pre σ = I ↔ ∀ i ∈ I, σ i ∈ A := by
      constructor
      · intro he i hi
        exact (mem_pre σ i).1 (he.symm ▸ hi)
      · intro hs
        exact (Finset.eq_of_subset_of_card_le
          (fun i hi => (mem_pre σ i).2 (hs i hi)) (by simp [pre, hc])).symm
    have block := h I A
    rw [Finset.sum_filter]
    simpa only [mul_ite, mul_one, mul_zero, iff_sub] using block
  have totals := Finset.sum_nonneg weight
  rw [Finset.sum_fiberwise_eq_sum_filter, Finset.sum_filter] at totals
  simpa only [good] using totals

end DeterminantalCut

/- Weighted bounds for payoffs on the two marked rows. -/

open scoped BigOperators
namespace DeterminantalCut

variable {n : Type*} [Fintype n] [DecidableEq n]

open MeasureTheory

theorem layer_nonneg (w : Equiv.Perm n → ℝ)
    (h : ∀ I J : Finset n, 0 ≤ ∑ σ : Equiv.Perm n,
      w σ * (if ∀ i ∈ I, σ i ∈ J then (1 : ℝ) else 0))
    (a b : n) (f : n → ℝ) :
    0 ≤ ∑ σ : Equiv.Perm n, w σ * max (f (σ b) - f (σ a)) 0 := by
  classical
  let layer (σ : Equiv.Perm n) : ℝ → ℝ :=
    (Set.Ioc (f (σ a)) (f (σ b))).indicator (fun _ => w σ)
  have integral (σ : Equiv.Perm n) :
      ∫ t, layer σ t = w σ * max (f (σ b) - f (σ a)) 0 := by
    simp only [layer, integral_indicator_const _ measurableSet_Ioc, Real.volume_real_Ioc,
      smul_eq_mul, mul_comm]
  have hi (σ : Equiv.Perm n) : Integrable (layer σ) := by
    exact (integrable_indicator_iff measurableSet_Ioc).2 (integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top))
  have pos (t : ℝ) : 0 ≤ ∑ σ : Equiv.Perm n, layer σ t := by
    have := cut_nonneg w h b a (Finset.univ.filter fun i => t ≤ f i)
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, not_le, layer,
      Set.indicator_apply, Set.mem_Ioc, and_comm] using this
  have hint : 0 ≤ ∫ t, ∑ σ : Equiv.Perm n, layer σ t := integral_nonneg pos
  rwa [integral_finsetSum _ (fun σ _ => hi σ), show
    (∑ σ : Equiv.Perm n, ∫ t, layer σ t) = _ from Finset.sum_congr rfl (fun σ _ => integral σ)] at hint

/-- The total weight with a specified unordered pair of images is nonnegative. -/
private theorem pair_mass (w : Equiv.Perm n → ℝ)
    (hb : ∀ I J : Finset n, 0 ≤ ∑ σ : Equiv.Perm n,
      w σ * (if ∀ i ∈ I, σ i ∈ J then (1 : ℝ) else 0))
    (a b : n) (hab : a ≠ b) (r : Equiv.Perm n) :
    0 ≤ ∑ τ : Equiv.Perm n with ({τ a, τ b} : Finset n) = {r a, r b}, w τ := by
  classical
  have iff_pair (τ : Equiv.Perm n) :
      ({τ a, τ b} : Finset n) = {r a, r b} ↔
        ∀ i ∈ ({a,b} : Finset n), τ i ∈ ({r a, r b} : Finset n) := by
    constructor
    · intro h i hi
      rw [← h]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi ⊢
      exact hi.imp (congrArg τ) (congrArg τ)
    · intro h
      apply Finset.eq_of_subset_of_card_le
      · intro i hi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl
        · exact h _ (by simp)
        · exact h _ (by simp)
      · simp [Finset.card_pair (τ.injective.ne hab), Finset.card_pair (r.injective.ne hab)]
  rw [Finset.sum_filter]
  simpa only [iff_pair, mul_ite, mul_one, mul_zero] using hb {a,b} {r a,r b}

theorem support_bound (w : Equiv.Perm n → ℝ) (hw : ∑ σ, w σ = 1)
    (hb : ∀ I J : Finset n, 0 ≤ ∑ σ : Equiv.Perm n,
      w σ * (if ∀ i ∈ I, σ i ∈ J then (1 : ℝ) else 0))
    (a b : n) (hab : a ≠ b) (f g : n → ℝ) (k : Finset n → ℝ) :
    ∃ σ : Equiv.Perm n, (∑ τ : Equiv.Perm n, w τ * (f (τ a) + g (τ b) + k {τ a,τ b})) ≤
      f (σ a) + g (σ b) + k {σ a,σ b} := by
  classical
  let P (τ : Equiv.Perm n) : Finset n := {τ a, τ b}
  let payoff (x y : n) := f x + g y + k {x,y}
  let F (τ : Equiv.Perm n) := payoff (τ a) (τ b)
  let E (τ : Equiv.Perm n) := max (F τ) (payoff (τ b) (τ a))
  obtain ⟨m, _, hm⟩ := Finset.exists_max_image Finset.univ F Finset.univ_nonempty
  refine ⟨m, ?_⟩
  change (∑ τ, w τ * F τ) ≤ F m
  have hE (τ : Equiv.Perm n) : E τ ≤ F m := by
    apply max_le (hm _ (Finset.mem_univ τ))
    simpa [F] using hm ((Equiv.swap a b).trans τ) (Finset.mem_univ _)
  have same {σ τ : Equiv.Perm n} (hp : P σ = P τ) : E σ = E τ := by
    have heq : ({σ a, σ b} : Set n) = {τ a, τ b} := by
      simpa [P] using congrArg (fun s : Finset n => (s : Set n)) hp
    rcases Set.pair_eq_pair_iff.mp heq with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
    · simp only [E, F, h₁, h₂]
    · simp only [E, F, h₁, h₂, max_comm]
  have hgap : 0 ≤ ∑ τ, w τ * (F m - E τ) := by
    let pairs := Finset.univ.image P
    have maps : ∀ τ ∈ Finset.univ, P τ ∈ pairs := fun τ h => Finset.mem_image_of_mem _ h
    rw [← Finset.sum_fiberwise_of_maps_to maps]
    apply Finset.sum_nonneg
    intro J hJ
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hJ
    calc
      0 ≤ (∑ τ : Equiv.Perm n with P τ = P r, w τ) * (F m - E r) :=
        mul_nonneg (pair_mass w hb a b hab r) (sub_nonneg.mpr (hE r))
      _ = _ := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro τ hτ
        rw [same (Finset.mem_filter.mp hτ).2]
  have diff (τ : Equiv.Perm n) : E τ - F τ =
      max ((f (τ b) - g (τ b)) - (f (τ a) - g (τ a))) 0 := by
    dsimp [E, F, payoff]
    rw [Finset.pair_comm (τ b) (τ a)]
    simp only [max_def]
    split <;> split <;> linarith
  have hgain : 0 ≤ ∑ τ, w τ * (E τ - F τ) := by
    simp_rw [diff]
    exact layer_nonneg w hb a b (fun i => f i - g i)
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw, one_mul] at hgap hgain
  linarith

end DeterminantalCut

/- Realizing a finite family of support inequalities by probability weights. -/

namespace TwoRow

theorem convex_weights {α ι : Type*} [Fintype α] [Nonempty α] [Fintype ι]
    (v : α → ι → ℝ) (z : ι → ℝ)
    (h : ∀ L : (ι → ℝ) →L[ℝ] ℝ, ∃ a, L z ≤ L (v a)) :
    ∃ t : α → ℝ, (∀ a, 0 ≤ t a) ∧ (∑ a, t a) = 1 ∧
      ∀ i, ∑ a, t a * v a i = z i := by
  classical
  let B : (α → ℝ) →ₗ[ℝ] (ι → ℝ) := ∑ a, (LinearMap.proj (R := ℝ) a).smulRight (v a)
  have B_apply (w : α → ℝ) (i : ι) : B w i = ∑ a, w a * v a i := by
    simp [B, LinearMap.sum_apply, Finset.sum_apply]
  let K := B '' stdSimplex ℝ α
  have hK : Convex ℝ K := (convex_stdSimplex ℝ α).linear_image B
  have hclosed : IsClosed K :=
    ((isCompact_stdSimplex ℝ α).image B.continuous_of_finiteDimensional).isClosed
  have hv (a : α) : v a ∈ K := by
    refine ⟨fun b => if a = b then 1 else 0, ite_eq_mem_stdSimplex ℝ a, ?_⟩
    funext i
    simp [B_apply, ite_mul]
  have hz : z ∈ K := by
    by_contra hbad
    obtain ⟨L, u, hK', hu⟩ := geometric_hahn_banach_closed_point hK hclosed hbad
    obtain ⟨a, ha⟩ := h L
    exact (ha.trans_lt (hK' _ (hv a))).asymm hu
  obtain ⟨t, ht, ht'⟩ := hz
  exact ⟨t, ht.1, ht.2, fun i => (B_apply t i).symm.trans (congrFun ht' i)⟩

end TwoRow

/- Record both row images and their unordered pair as coordinates. -/

namespace TwoRow

open scoped BigOperators

variable {n : Type} [Fintype n] [DecidableEq n]

private abbrev Coord (n : Type) := n ⊕ (n ⊕ Finset n)

private def mark (i : Coord n) : Coord n → ℝ := Pi.single i 1

private def features (a b : n) (σ : Equiv.Perm n) : Coord n → ℝ :=
  mark (.inl (σ a)) + mark (.inr (.inl (σ b))) + mark (.inr (.inr {σ a, σ b}))

theorem joint_rows (w : Equiv.Perm n → ℝ) (hw : ∑ σ, w σ = 1)
    (hb : ∀ I J : Finset n, 0 ≤ ∑ σ : Equiv.Perm n,
      w σ * (if ∀ i ∈ I, σ i ∈ J then (1 : ℝ) else 0))
    (a b : n) (hab : a ≠ b) :
    ∃ t : Equiv.Perm n → ℝ, (∀ σ, 0 ≤ t σ) ∧ (∑ σ, t σ) = 1 ∧
      (∀ i : n, (∑ σ, if σ a = i then w σ else 0) = ∑ σ, if σ a = i then t σ else 0) ∧
      (∀ i : n, (∑ σ, if σ b = i then w σ else 0) = ∑ σ, if σ b = i then t σ else 0) ∧
      (∀ J : Finset n, (∑ σ, if ({σ a, σ b} : Finset n) = J then w σ else 0) =
        ∑ σ, if ({σ a, σ b} : Finset n) = J then t σ else 0) := by
  classical
  let z := ∑ σ : Equiv.Perm n, w σ • features a b σ
  have test (L : (Coord n → ℝ) →L[ℝ] ℝ) :
      ∃ σ : Equiv.Perm n, L z ≤ L (features a b σ) := by
    have h := DeterminantalCut.support_bound w hw hb a b hab
      (fun i => L (mark (.inl i))) (fun i => L (mark (.inr (.inl i))))
      (fun J => L (mark (.inr (.inr J))))
    simpa only [z, features, map_sum, map_smul, smul_eq_mul, map_add] using h
  obtain ⟨t, ht, hsum, hmatch⟩ := convex_weights (features a b) z test
  refine ⟨t, ht, hsum, ?_, ?_, ?_⟩
  · intro i
    simpa [z, features, mark, Pi.single_apply, mul_ite, eq_comm] using
      (hmatch (.inl i)).symm
  · intro i
    simpa [z, features, mark, Pi.single_apply, mul_ite, eq_comm] using
      (hmatch (.inr (.inl i))).symm
  · intro J
    simpa [z, features, mark, Pi.single_apply, mul_ite, eq_comm] using
      (hmatch (.inr (.inr J))).symm

end TwoRow

/- Recover all marginals supported on at most two marked rows. -/

namespace TwoRow

private theorem enclose {n : Type} [DecidableEq n] [Nontrivial n] (T : Finset n)
    (ht : T.card ≤ 2) : ∃ a b : n, a ≠ b ∧ T ⊆ {a,b} := by
  classical
  by_cases h2 : T.card = 2
  · obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp h2
    exact ⟨a,b,hab,Finset.Subset.rfl⟩
  by_cases h1 : T.card = 1
  · obtain ⟨a,rfl⟩ := Finset.card_eq_one.mp h1
    obtain ⟨b, hba⟩ := exists_ne a
    exact ⟨a,b,hba.symm,by simp⟩
  have hz : T = ∅ := Finset.card_eq_zero.mp (by omega)
  obtain ⟨a,b,hab⟩ := exists_pair_ne n
  exact ⟨a,b,hab,by simp [hz]⟩

private theorem pair_subsets {n : Type} [DecidableEq n] {S : Finset n} {a b : n}
    (h : S ⊆ {a,b}) : S = ∅ ∨ S = {a} ∨ S = {b} ∨ S = {a,b} := by
  have hm {x : n} (hx : x ∈ S) : x = a ∨ x = b := by simpa using h hx
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S
  · right; right; right
    exact le_antisymm h (by simpa [Finset.insert_subset_iff] using And.intro ha hb)
  · right; left
    apply le_antisymm _ (Finset.singleton_subset_iff.mpr ha)
    intro x hx
    exact Finset.mem_singleton.mpr ((hm hx).resolve_right fun he => hb (he ▸ hx))
  · right; right; left
    apply le_antisymm _ (Finset.singleton_subset_iff.mpr hb)
    intro x hx
    exact Finset.mem_singleton.mpr ((hm hx).resolve_left fun he => ha (he ▸ hx))
  · left
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact (hm hx).elim (fun he => ha (he ▸ hx)) (fun he => hb (he ▸ hx))

private theorem singleton_images {n : Type} [Fintype n] [DecidableEq n] (w t : Equiv.Perm n → ℝ)
    (a : n) (h : ∀ i : n, (∑ σ, if σ a = i then w σ else 0) =
      ∑ σ, if σ a = i then t σ else 0) (J : Finset n) :
    (∑ σ : Equiv.Perm n, if ({a} : Finset n).image σ = J then w σ else 0) =
    ∑ σ : Equiv.Perm n, if ({a} : Finset n).image σ = J then t σ else 0 := by
  classical
  simp only [Finset.image_singleton]
  by_cases hj : ∃ i, J = {i}
  · obtain ⟨i,rfl⟩ := hj
    simpa using h i
  · have hne (i : n) : ({i} : Finset n) ≠ J := fun he => hj ⟨i, he.symm⟩
    simp [hne]

theorem finish (n : Type) [Fintype n] [DecidableEq n] (w : Equiv.Perm n → ℝ)
    (hw : (∑ σ, w σ) = 1)
    (h : ∀ a b : n, a ≠ b → ∃ t : Equiv.Perm n → ℝ, (∀ σ, 0 ≤ t σ) ∧
      (∑ σ, t σ) = 1 ∧ (∀ i : n, (∑ σ, if σ a = i then w σ else 0) =
        ∑ σ, if σ a = i then t σ else 0) ∧
      (∀ i : n, (∑ σ, if σ b = i then w σ else 0) =
        ∑ σ, if σ b = i then t σ else 0) ∧
      (∀ J : Finset n, (∑ σ, if ({σ a,σ b} : Finset n) = J then w σ else 0) =
        ∑ σ, if ({σ a,σ b} : Finset n) = J then t σ else 0)) :
    ∀ T : Finset n, T.card ≤ 2 → ∃ t : Equiv.Perm n → ℝ, (∀ σ, 0 ≤ t σ) ∧
      (∑ σ, t σ) = 1 ∧ ∀ S ⊆ T, ∀ J : Finset n,
        (∑ σ : Equiv.Perm n, if S.image σ = J then w σ else 0) =
          ∑ σ : Equiv.Perm n, if S.image σ = J then t σ else 0 := by
  classical
  intro T ht
  cases subsingleton_or_nontrivial n with
  | inl hn =>
    refine ⟨w, ?_, hw, fun _ _ _ => rfl⟩
    intro σ
    have hu : (Finset.univ : Finset (Equiv.Perm n)) = {σ} := by
      ext π
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      exact Equiv.ext fun i => Subsingleton.elim _ _
    rw [hu, Finset.sum_singleton] at hw
    rw [hw]
    norm_num
  | inr hn =>
    obtain ⟨a,b,hab,hT⟩ := enclose T ht
    obtain ⟨t,ht0,ht1,ha,hb,hab'⟩ := h a b hab
    refine ⟨t,ht0,ht1,?_⟩
    intro S hs J
    rcases pair_subsets (hs.trans hT) with rfl | rfl | rfl | rfl
    · simp only [Finset.image_empty]
      by_cases hj : (∅ : Finset n) = J
      · subst J
        simpa using hw.trans ht1.symm
      · simp [hj]
    · exact singleton_images _ _ _ ha J
    · exact singleton_images _ _ _ hb J
    · simpa using hab' J

end TwoRow

theorem OMA.solution : OMA.R_DeterminantalConjecture_determinantal_conjecture_R1.H1 := by
  intro n _ _ w hw hb
  exact TwoRow.finish n w hw (TwoRow.joint_rows w hw hb)
