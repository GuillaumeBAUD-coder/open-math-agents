import OMAStatements.S_mo_275621
import Mathlib

/-!
A proof of the claim of MathOverflow question 275621 (see statements/mo-275621.lean).

Raising every success probability of a Poisson binomial variable can only lower its CDF.
The proof is by induction on the index set, splitting off one coordinate: writing
`cdfOn u p k` for the probability that at most `k` of the Bernoullis indexed by `u` succeed,
one has

  cdfOn (insert x u) p (k+1) = (1 - p x) * cdfOn u p (k+1) + p x * cdfOn u p k,

`cdfOn u p k` is nonnegative and nondecreasing in `k`, and if `p ≤ p'` pointwise then both
summands can only grow, which gives `cdfOn u p' k ≤ cdfOn u p k`.
-/

open OMA.S_mo_275621

namespace Mo275621

variable {ι : Type*} [DecidableEq ι]

/-- `P(#(successes among u) ≤ k)` for independent `Bernoulli (p i)`. -/
noncomputable def cdfOn (u : Finset ι) (p : ι → ℝ) (k : ℕ) : ℝ :=
  ∑ S ∈ u.powerset.filter (fun S => S.card ≤ k), (∏ i ∈ S, p i) * ∏ i ∈ u \ S, (1 - p i)

/-- The same sum with the cardinality bound as an indicator. -/
lemma cdfOn_eq_sum (u : Finset ι) (p : ι → ℝ) (k : ℕ) :
    cdfOn u p k =
      ∑ S ∈ u.powerset,
        (if S.card ≤ k then (∏ i ∈ S, p i) * ∏ i ∈ u \ S, (1 - p i) else 0) := by
  rw [cdfOn, Finset.sum_filter]

lemma term_nonneg {u : Finset ι} {p : ι → ℝ} (hp : ∀ i ∈ u, 0 ≤ p i)
    (hp1 : ∀ i ∈ u, p i ≤ 1) {S : Finset ι} (hS : S ⊆ u) :
    0 ≤ (∏ i ∈ S, p i) * ∏ i ∈ u \ S, (1 - p i) := by
  have h1 : 0 ≤ ∏ i ∈ S, p i := Finset.prod_nonneg (fun i hi => hp i (hS hi))
  have h2 : 0 ≤ ∏ i ∈ u \ S, (1 - p i) :=
    Finset.prod_nonneg (fun i hi => by
      have hiu : i ∈ u := (Finset.mem_sdiff.mp hi).1
      linarith [hp1 i hiu])
  exact mul_nonneg h1 h2

lemma cdfOn_nonneg {u : Finset ι} {p : ι → ℝ} (hp : ∀ i ∈ u, 0 ≤ p i)
    (hp1 : ∀ i ∈ u, p i ≤ 1) (k : ℕ) : 0 ≤ cdfOn u p k := by
  rw [cdfOn]
  refine Finset.sum_nonneg ?_
  intro S hS
  rw [Finset.mem_filter, Finset.mem_powerset] at hS
  exact term_nonneg hp hp1 hS.1

/-- Removing a fresh element from `insert x u` leaves `insert x` of the difference. -/
lemma sdiff_insert_eq (u t : Finset ι) (x : ι) (hx : x ∉ u) (htu : t ⊆ u) :
    (insert x u) \ t = insert x (u \ t) := by
  have hx_t : x ∉ t := fun h => hx (htu h)
  ext i
  simp only [Finset.mem_sdiff, Finset.mem_insert]
  constructor
  · rintro ⟨rfl | hi, hit⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨hi, hit⟩
  · rintro (rfl | ⟨hi, hit⟩)
    · exact ⟨Or.inl rfl, hx_t⟩
    · exact ⟨Or.inr hi, hit⟩

/-- Removing a fresh element and its insert from a set difference. -/
lemma sdiff_insert_insert_eq (u t : Finset ι) (x : ι) (hx : x ∉ u) (htu : t ⊆ u) :
    (insert x u) \ (insert x t) = u \ t := by
  have hx_t : x ∉ t := fun h => hx (htu h)
  ext i
  simp only [Finset.mem_sdiff, Finset.mem_insert]
  constructor
  · rintro ⟨hxi | hi, hit⟩
    · exact absurd (Or.inl hxi) hit
    · exact ⟨hi, fun h => hit (Or.inr h)⟩
  · rintro ⟨hi, hit⟩
    refine ⟨Or.inr hi, ?_⟩
    rintro (h | h)
    · exact hx (h ▸ hi)
    · exact hit h

lemma prod_sdiff_insert (u t : Finset ι) (x : ι) (p : ι → ℝ) (hx : x ∉ u) (htu : t ⊆ u) :
    (∏ i ∈ (insert x u) \ t, (1 - p i)) = (1 - p x) * ∏ i ∈ u \ t, (1 - p i) := by
  rw [sdiff_insert_eq u t x hx htu]
  exact Finset.prod_insert (show x ∉ u \ t from fun h => hx (Finset.mem_sdiff.mp h).1)

/-- The induction step at `k = 0`. -/
lemma cdfOn_insert_zero (u : Finset ι) (x : ι) (hx : x ∉ u) (p : ι → ℝ) :
    cdfOn (insert x u) p 0 = (1 - p x) * cdfOn u p 0 := by
  rw [cdfOn_eq_sum, Finset.sum_powerset_insert hx]
  have hzero : ∑ t ∈ u.powerset,
      (if (insert x t).card ≤ 0 then
        (∏ i ∈ insert x t, p i) * ∏ i ∈ (insert x u) \ (insert x t), (1 - p i)
        else 0) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro t ht
    have hx_t : x ∉ t := fun h => hx (Finset.mem_powerset.mp ht h)
    rw [Finset.card_insert_of_notMem hx_t]
    simp
  rw [hzero, add_zero, cdfOn_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro t ht
  have htu : t ⊆ u := Finset.mem_powerset.mp ht
  rw [prod_sdiff_insert u t x p hx htu]
  by_cases hc : t.card ≤ 0
  · simp only [hc, if_true]
    ring
  · simp only [hc, if_false, mul_zero]

/-- The induction step at `k + 1`. -/
lemma cdfOn_insert_succ (u : Finset ι) (x : ι) (hx : x ∉ u) (p : ι → ℝ) (k : ℕ) :
    cdfOn (insert x u) p (k + 1) =
      (1 - p x) * cdfOn u p (k + 1) + p x * cdfOn u p k := by
  have h1 : ∑ t ∈ u.powerset,
      (if t.card ≤ k + 1 then
        (∏ i ∈ t, p i) * ∏ i ∈ (insert x u) \ t, (1 - p i) else 0)
      = (1 - p x) * cdfOn u p (k + 1) := by
    rw [cdfOn_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro t ht
    have htu : t ⊆ u := Finset.mem_powerset.mp ht
    rw [prod_sdiff_insert u t x p hx htu]
    by_cases hc : t.card ≤ k + 1
    · simp only [hc, if_true]
      ring
    · simp only [hc, if_false, mul_zero, mul_zero]
  have h2 : ∑ t ∈ u.powerset,
      (if (insert x t).card ≤ k + 1 then
        (∏ i ∈ insert x t, p i) * ∏ i ∈ (insert x u) \ (insert x t), (1 - p i) else 0)
      = p x * cdfOn u p k := by
    rw [cdfOn_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro t ht
    have htu : t ⊆ u := Finset.mem_powerset.mp ht
    have hx_t : x ∉ t := fun h => hx (htu h)
    rw [sdiff_insert_insert_eq u t x hx htu, Finset.prod_insert hx_t,
      Finset.card_insert_of_notMem hx_t]
    by_cases hc : t.card + 1 ≤ k + 1
    · have hc' : t.card ≤ k := Nat.succ_le_succ_iff.mp hc
      simp only [hc, hc', if_true]
      ring
    · have hc' : ¬ t.card ≤ k := fun h => hc (Nat.succ_le_succ h)
      simp only [hc, hc', if_false, mul_zero, mul_zero]
  rw [cdfOn_eq_sum, Finset.sum_powerset_insert hx, h1, h2]

/-- The CDF is nondecreasing in the bound `k`. -/
lemma cdfOn_mono_succ {u : Finset ι} {p : ι → ℝ} (hp : ∀ i ∈ u, 0 ≤ p i)
    (hp1 : ∀ i ∈ u, p i ≤ 1) (k : ℕ) : cdfOn u p k ≤ cdfOn u p (k + 1) := by
  rw [cdfOn, cdfOn]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro S hS
    rw [Finset.mem_filter, Finset.mem_powerset] at hS ⊢
    exact ⟨hS.1, le_trans hS.2 (Nat.le_succ k)⟩
  · intro S hS _
    rw [Finset.mem_filter, Finset.mem_powerset] at hS
    exact term_nonneg hp hp1 hS.1

/-- Main induction: raising probabilities coordinatewise lowers the CDF. -/
lemma cdfOn_mono (u : Finset ι) (p p' : ι → ℝ) (hp : ∀ i ∈ u, 0 ≤ p i)
    (hp1 : ∀ i ∈ u, p i ≤ 1) (hp'1 : ∀ i ∈ u, p' i ≤ 1) (hle : ∀ i ∈ u, p i ≤ p' i) :
    ∀ k : ℕ, cdfOn u p' k ≤ cdfOn u p k := by
  induction u using Finset.induction_on with
  | empty =>
    intro k
    have hpow : (∅ : Finset ι).powerset.filter (fun S => S.card ≤ k) = {∅} := by
      rw [Finset.powerset_empty]
      simp
    have h1 : cdfOn (∅ : Finset ι) p k = 1 := by
      rw [cdfOn, hpow, Finset.sum_singleton]
      simp
    have h2 : cdfOn (∅ : Finset ι) p' k = 1 := by
      rw [cdfOn, hpow, Finset.sum_singleton]
      simp
    rw [h1, h2]
  | @insert x u hx ih =>
    have hp_u : ∀ i ∈ u, 0 ≤ p i := fun i hi => hp i (Finset.mem_insert_of_mem hi)
    have hp1_u : ∀ i ∈ u, p i ≤ 1 := fun i hi => hp1 i (Finset.mem_insert_of_mem hi)
    have hp'1_u : ∀ i ∈ u, p' i ≤ 1 := fun i hi => hp'1 i (Finset.mem_insert_of_mem hi)
    have hle_u : ∀ i ∈ u, p i ≤ p' i := fun i hi => hle i (Finset.mem_insert_of_mem hi)
    have hp'0_u : ∀ i ∈ u, 0 ≤ p' i := fun i hi => le_trans (hp_u i hi) (hle_u i hi)
    have hpx0 : 0 ≤ p x := hp x (Finset.mem_insert_self x u)
    have hpx1 : p x ≤ 1 := hp1 x (Finset.mem_insert_self x u)
    have hle_x : p x ≤ p' x := hle x (Finset.mem_insert_self x u)
    intro k
    rcases k with _ | k
    · rw [cdfOn_insert_zero u x hx p', cdfOn_insert_zero u x hx p]
      have hAB : cdfOn u p' 0 ≤ cdfOn u p 0 := ih hp_u hp1_u hp'1_u hle_u 0
      have hA0 : 0 ≤ cdfOn u p' 0 := cdfOn_nonneg hp'0_u hp'1_u 0
      have h1 : (1 - p' x) * cdfOn u p' 0 ≤ (1 - p x) * cdfOn u p' 0 :=
        mul_le_mul_of_nonneg_right (by linarith) hA0
      have h2 : (1 - p x) * cdfOn u p' 0 ≤ (1 - p x) * cdfOn u p 0 :=
        mul_le_mul_of_nonneg_left hAB (by linarith)
      linarith
    · rw [cdfOn_insert_succ u x hx p' k, cdfOn_insert_succ u x hx p k]
      have hAB : cdfOn u p' (k + 1) ≤ cdfOn u p (k + 1) := ih hp_u hp1_u hp'1_u hle_u (k + 1)
      have hAB' : cdfOn u p' k ≤ cdfOn u p k := ih hp_u hp1_u hp'1_u hle_u k
      have hmono : cdfOn u p' k ≤ cdfOn u p' (k + 1) := cdfOn_mono_succ hp'0_u hp'1_u k
      have step1 : (1 - p' x) * cdfOn u p' (k + 1) + p' x * cdfOn u p' k ≤
          (1 - p x) * cdfOn u p' (k + 1) + p x * cdfOn u p' k := by
        have hprod : 0 ≤ (p' x - p x) * (cdfOn u p' (k + 1) - cdfOn u p' k) :=
          mul_nonneg (by linarith) (by linarith)
        nlinarith
      have step2 : (1 - p x) * cdfOn u p' (k + 1) + p x * cdfOn u p' k ≤
          (1 - p x) * cdfOn u p (k + 1) + p x * cdfOn u p k := by
        have hneg : p x * (cdfOn u p' k - cdfOn u p k) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hpx0 (by linarith)
        have hpos : 0 ≤ (1 - p x) * (cdfOn u p (k + 1) - cdfOn u p' (k + 1)) :=
          mul_nonneg (by linarith) (by linarith)
        nlinarith
      linarith

end Mo275621

theorem OMA.solution : type_of% @OMA.S_mo_275621.main := by
  intro N p δ hp hδ hpδ k _
  have hpc : ∀ i : Fin N, p i ≤ p i + δ := fun i => by linarith
  have hp1 : ∀ i : Fin N, p i ≤ 1 := fun i => by linarith [hpδ i]
  have hp'1 : ∀ i : Fin N, p i + δ ≤ 1 := fun i => hpδ i
  have hmain : Mo275621.cdfOn (Finset.univ : Finset (Fin N)) (fun i => p i + δ) k ≤
      Mo275621.cdfOn (Finset.univ : Finset (Fin N)) p k :=
    Mo275621.cdfOn_mono Finset.univ p (fun i => p i + δ)
      (fun i _ => hp i) (fun i _ => hp1 i) (fun i _ => hp'1 i) (fun i _ => hpc i) k
  have h1 : cdf (fun i => p i + δ) k =
      Mo275621.cdfOn (Finset.univ : Finset (Fin N)) (fun i => p i + δ) k := by
    simp [cdf, Mo275621.cdfOn, Finset.powerset_univ, Finset.compl_eq_univ_sdiff]
  have h2 : cdf p k = Mo275621.cdfOn (Finset.univ : Finset (Fin N)) p k := by
    simp [cdf, Mo275621.cdfOn, Finset.powerset_univ, Finset.compl_eq_univ_sdiff]
  rw [h1, h2]
  exact hmain
