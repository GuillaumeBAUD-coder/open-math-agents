import FormalConjectures.ErdosProblems.«156»

/-! Each integer skipped by the greedy procedure is determined by a pair or triple
from the final set. Counting these witnesses gives the cubic estimate. -/

open Finset Filter
open scoped Asymptotics

def OMA.sidonPrefix (k : ℕ) : Finset ℕ := (Finset.greedySidon.aux k).1.1

lemma OMA.sidonPrefix_nonempty (k : ℕ) : (OMA.sidonPrefix k).Nonempty := by
  cases k with
  | zero => exact ⟨1, by simp [OMA.sidonPrefix, Finset.greedySidon.aux]⟩
  | succ k =>
    rw [OMA.sidonPrefix, Finset.greedySidon.aux]
    simp

lemma OMA.sidonPrefix_step (k : ℕ) :
    OMA.sidonPrefix (k + 1) = insert (Finset.greedySidon (k + 1)) (OMA.sidonPrefix k) := by
  simp only [OMA.sidonPrefix, Finset.greedySidon, Finset.greedySidon.aux]
  ext x
  simp [or_comm]

lemma OMA.sidonNext_le {k x : ℕ} (h : (OMA.sidonPrefix k).Nonempty)
    (hx : (OMA.sidonPrefix k).max' h + 1 ≤ x) (hnot : x ∉ OMA.sidonPrefix k)
    (hs : IsSidon ((OMA.sidonPrefix k : Set ℕ) ∪ {x})) :
    Finset.greedySidon (k + 1) ≤ x := by
  rw [Finset.greedySidon, Finset.greedySidon.aux]
  dsimp only
  change (Finset.greedySidon.aux k).1.1.Nonempty at h
  rw [dif_pos h, Finset.greedySidon.go, dif_pos h]
  exact Nat.find_min' _ ⟨hx, hnot, by simpa [OMA.sidonPrefix] using hs⟩

lemma OMA.sidonNext_ge (k : ℕ) (h : (OMA.sidonPrefix k).Nonempty) :
    (OMA.sidonPrefix k).max' h + 1 ≤ Finset.greedySidon (k + 1) := by
  rw [Finset.greedySidon, Finset.greedySidon.aux]
  dsimp only
  change (Finset.greedySidon.aux k).1.1.Nonempty at h
  rw [dif_pos h]
  exact (Finset.greedySidon.go _ _ _).property.1

lemma OMA.sidonPrefix_top (k : ℕ) :
    Finset.greedySidon k ∈ OMA.sidonPrefix k := by
  cases k with
  | zero => simp [OMA.sidonPrefix, Finset.greedySidon, Finset.greedySidon.aux]
  | succ k => rw [OMA.sidonPrefix_step]; exact Finset.mem_insert_self _ _

lemma OMA.sidonPrefix_le (k : ℕ) {x : ℕ} (hx : x ∈ OMA.sidonPrefix k) :
    x ≤ Finset.greedySidon k := by
  cases k with
  | zero =>
    have he : x = 1 := by simpa [OMA.sidonPrefix, Finset.greedySidon.aux] using hx
    subst x
    exact le_rfl
  | succ k =>
    rw [OMA.sidonPrefix_step] at hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact le_rfl
    · have h := OMA.sidonPrefix_nonempty k
      exact (Finset.le_max' _ x hx).trans ((Nat.le_succ _).trans (OMA.sidonNext_ge k h))

lemma OMA.sidonEnd_ge (k : ℕ) : k + 1 ≤ Finset.greedySidon k := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    have h := OMA.sidonPrefix_nonempty k
    have htop := Finset.le_max' (OMA.sidonPrefix k) _ (OMA.sidonPrefix_top k)
    have hnext := OMA.sidonNext_ge k h
    omega

lemma OMA.sidonPrefix_skip (N k x : ℕ) (hpos : 1 ≤ x) (hxN : x ≤ N)
    (hxk : x ≤ Finset.greedySidon k) (hx : x ∉ OMA.sidonPrefix k) :
    ¬ IsSidon (((OMA.sidonPrefix k).filter (· ≤ N) : Set ℕ) ∪ {x}) := by
  induction k with
  | zero =>
    have he : x = 1 := by
      change x ≤ 1 at hxk
      omega
    subst x
    exact False.elim (hx (OMA.sidonPrefix_top 0))
  | succ k ih =>
    intro hs
    have hsub : OMA.sidonPrefix k ⊆ OMA.sidonPrefix (k + 1) := by
      rw [OMA.sidonPrefix_step]
      exact Finset.subset_insert _ _
    have hxprev : x ∉ OMA.sidonPrefix k := fun h => hx (hsub h)
    by_cases hle : x ≤ Finset.greedySidon k
    · apply ih hle hxprev
      apply Set.IsSidon.subset hs
      apply Set.union_subset_union ?_ (by rfl)
      intro y hy
      rw [Finset.mem_coe, Finset.mem_filter] at hy ⊢
      exact ⟨hsub hy.1, hy.2⟩
    · have hall (y : ℕ) (hy : y ∈ OMA.sidonPrefix k) : y < x :=
        (OMA.sidonPrefix_le k hy).trans_lt (lt_of_not_ge hle)
      have hnew : IsSidon ((OMA.sidonPrefix k : Set ℕ) ∪ {x}) := by
        apply Set.IsSidon.subset hs
        apply Set.union_subset_union ?_ (by rfl)
        intro y hy
        exact Finset.mem_filter.mpr ⟨hsub hy, (hall y hy).le.trans hxN⟩
      have h : (OMA.sidonPrefix k).Nonempty := OMA.sidonPrefix_nonempty k
      have hstep : (OMA.sidonPrefix k).max' h + 1 ≤ x :=
        Nat.succ_le_of_lt (hall _ (Finset.max'_mem _ h))
      have heq := le_antisymm (OMA.sidonNext_le h hstep hxprev hnew) hxk
      exact hx (heq ▸ OMA.sidonPrefix_top (k + 1))

lemma OMA.sidonMaximal (N : ℕ) :
    Set.IsMaximalSidonSetIn (Finset.greedySidonBelow N : Set ℕ) N := by
  have hpos (k y : ℕ) (hy : y ∈ OMA.sidonPrefix k) : 1 ≤ y := by
    induction k with
    | zero =>
      have he : y = 1 := by simpa [OMA.sidonPrefix, Finset.greedySidon.aux] using hy
      omega
    | succ k ih =>
      rw [OMA.sidonPrefix_step] at hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact (show 1 ≤ k + 1 + 1 by omega).trans (OMA.sidonEnd_ge (k + 1))
      · exact ih hy
  refine ⟨?_, Erdos156.greedySidonSet_isSidon N, ?_⟩
  · intro y hy
    change y ∈ (OMA.sidonPrefix N).filter (· ≤ N) at hy
    obtain ⟨hyA, hyN⟩ := Finset.mem_filter.mp hy
    exact ⟨hpos N y hyA, hyN⟩
  · intro x hx hxnot
    have hxnot' : x ∉ OMA.sidonPrefix N := fun h => hxnot (Finset.mem_filter.mpr ⟨h, hx.2⟩)
    have hle := hx.2.trans ((Nat.le_succ _).trans (OMA.sidonEnd_ge N))
    exact OMA.sidonPrefix_skip N N x hx.1 hx.2 hle hxnot'

lemma OMA.sidonWitnessCount {A : Finset ℕ} {N : ℕ}
    (h : Set.IsMaximalSidonSetIn (A : Set ℕ) N) :
    N ≤ A.card + A.card * A.card + A.card * (A.card * A.card) := by
  let pairs := (A ×ˢ A).image (fun z => (z.1 + z.2) / 2)
  let triples := (A ×ˢ (A ×ˢ A)).image (fun z => z.2.1 + z.2.2 - z.1)
  have hcover : Finset.Icc 1 N ⊆ (A ∪ pairs) ∪ triples := by
    intro x hx
    by_contra hx'
    have hxA : x ∉ A := fun h => hx' (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    have hxPair : x ∉ pairs := fun h => hx' (Finset.mem_union_left _ (Finset.mem_union_right _ h))
    have hxTriple : x ∉ triples := fun h => hx' (Finset.mem_union_right _ h)
    apply h.maximal (show x ∈ Set.Icc 1 N from Finset.mem_Icc.mp hx) hxA
    refine (Set.IsSidon.insert h.isSidon).2 (Or.inr ?_)
    intro a ha b hb
    constructor
    · intro hab
      apply hxPair
      exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, by dsimp; omega⟩
    · intro c hc hab
      apply hxTriple
      exact Finset.mem_image.mpr
        ⟨(a, b, c), Finset.mem_product.mpr ⟨ha, Finset.mem_product.mpr ⟨hb, hc⟩⟩, by dsimp; omega⟩
  have hpair : pairs.card ≤ A.card * A.card := by
    simpa only [Finset.card_product] using Finset.card_image_le (s := A ×ˢ A)
      (f := fun z => (z.1 + z.2) / 2)
  have htriple : triples.card ≤ A.card * (A.card * A.card) := by
    simpa only [Finset.card_product] using Finset.card_image_le (s := A ×ˢ (A ×ˢ A))
      (f := fun z => z.2.1 + z.2.2 - z.1)
  have hN : (Finset.Icc 1 N).card = N := by simp [Nat.card_Icc]
  calc
    N = (Finset.Icc 1 N).card := hN.symm
    _ ≤ ((A ∪ pairs) ∪ triples).card := Finset.card_le_card hcover
    _ ≤ (A ∪ pairs).card + triples.card := Finset.card_union_le _ _
    _ ≤ A.card + pairs.card + triples.card := Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ _ := by omega

theorem OMA.solution : type_of% @Erdos156.erdos_156.variants.greedy_lower_bound := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨2, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  let m := (Finset.greedySidonBelow N).card
  have hN' : N ≤ m + m * m + m * (m * m) :=
    OMA.sidonWitnessCount (OMA.sidonMaximal N)
  have hm : 1 ≤ m := by
    by_contra! h
    have hm0 : m = 0 := by omega
    simp [hm0] at hN'
    omega
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hbound : (N : ℝ) ≤ (m : ℝ) + (m : ℝ) * m + (m : ℝ) * ((m : ℝ) * m) := by
    exact_mod_cast hN'
  have hp : (N : ℝ) ≤ (2 * (m : ℝ)) ^ 3 := by
    have h₁ := mul_nonneg (sub_nonneg.mpr hm') (show (0 : ℝ) ≤ m by positivity)
    have h₂ := mul_nonneg (sub_nonneg.mpr hm') (show (0 : ℝ) ≤ (m : ℝ) ^ 2 by positivity)
    nlinarith only [hbound, h₁, h₂]
  have hnroot : 0 ≤ (N : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_nonneg (by positivity) _
  simp only [Real.norm_eq_abs, abs_of_nonneg hnroot, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)]
  calc
    (N : ℝ) ^ (1 / 3 : ℝ) ≤ ((2 * (m : ℝ)) ^ 3) ^ (1 / 3 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hp (by norm_num)
    _ = 2 * (m : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num