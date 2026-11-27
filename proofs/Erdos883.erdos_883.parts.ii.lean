import FormalConjectures.ErdosProblems.«883»
import Mathlib

-- Problem: Erdős Problem 883 — ii
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/883.lean:72 (declaration Erdos883.erdos_883.parts.ii)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
--
-- Proof outline (fixed l, n large), following the strategy of Erdős and Sárközy
-- (On cycles in the coprime graph of integers, EJC 1997) adapted to K(1,l,l):
-- residue classes modulo a primorial Q control all small primes, large primes are
-- handled by union bounds, and a greedy argument finds K(l,l) between two classes.
-- * dense case (many elements of A coprime to 6): a window of 7 consecutive residues
--   mod Q contains three pairwise coprime residues on which A is dense;
-- * sparse case: A contains almost all multiples of 2 or 3, the centre x is chosen at
--   the least level R where its large prime factors are sparse, and a Wallis-type
--   bound on totient(primorial R) shows A is dense on the classes 2u and 3u mod Q.

open Finset SimpleGraph Erdos883

namespace OMA883

lemma adj_iff (a b : ℕ) : coprimeGraph.Adj a b ↔ a ≠ b ∧ Nat.Coprime a b := by
  simp only [coprimeGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨h, h' | h'⟩
    · exact ⟨h, h'⟩
    · exact ⟨h, h'.symm⟩
  · rintro ⟨h, h'⟩
    exact ⟨h, Or.inl h'⟩

/-- vertex labelling for the embedding -/
def G3 (x : ℕ) (eU eV : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => x
  | 1, k => eU k
  | _, k => eV k

lemma embed (A : Finset ℕ) (l x : ℕ) (U V : Finset ℕ) (hx : x ∈ A) (hU : U ⊆ A) (hV : V ⊆ A)
    (hUc : U.card = l) (hVc : V.card = l)
    (hxU : ∀ u ∈ U, x ≠ u ∧ Nat.Coprime x u) (hxV : ∀ v ∈ V, x ≠ v ∧ Nat.Coprime x v)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, u ≠ v ∧ Nat.Coprime u v) :
    (completeMultipartiteGraph (fun i : Fin 3 ↦ Fin (![1, l, l] i))).IsContained
      (coprimeGraph.induce (A : Set ℕ)) := by
  classical
  let eU : ℕ → ℕ := fun k => if h : k < l then U.orderEmbOfFin hUc ⟨k, h⟩ else 0
  let eV : ℕ → ℕ := fun k => if h : k < l then V.orderEmbOfFin hVc ⟨k, h⟩ else 0
  have heU : ∀ k, k < l → eU k ∈ U := by
    intro k hk; simp only [eU, dif_pos hk]; exact U.orderEmbOfFin_mem hUc _
  have heV : ∀ k, k < l → eV k ∈ V := by
    intro k hk; simp only [eV, dif_pos hk]; exact V.orderEmbOfFin_mem hVc _
  have hiU : ∀ k k', k < l → k' < l → eU k = eU k' → k = k' := by
    intro k k' hk hk' h
    simp only [eU, dif_pos hk, dif_pos hk'] at h
    have := (U.orderEmbOfFin hUc).injective h
    simpa using this
  have hiV : ∀ k k', k < l → k' < l → eV k = eV k' → k = k' := by
    intro k k' hk hk' h
    simp only [eV, dif_pos hk, dif_pos hk'] at h
    have := (V.orderEmbOfFin hVc).injective h
    simpa using this
  let g : ℕ → ℕ → ℕ := G3 x eU eV
  have hbound : ∀ p : (Σ i : Fin 3, Fin (![1, l, l] i)), (p.1.val = 0 ∧ p.2.val = 0) ∨
      (p.1.val = 1 ∧ p.2.val < l) ∨ (p.1.val = 2 ∧ p.2.val < l) := by
    rintro ⟨i, k⟩
    fin_cases i
    · left; have := k.2; simp at this; exact ⟨rfl, by simpa using this⟩
    · right; left; have := k.2; simp at this; exact ⟨rfl, this⟩
    · right; right; have := k.2; simp at this; exact ⟨rfl, this⟩
  have g0 : ∀ i k : ℕ, i = 0 → g i k = x := by intro i k h; subst h; rfl
  have g1 : ∀ i k : ℕ, i = 1 → g i k = eU k := by intro i k h; subst h; rfl
  have g2 : ∀ i k : ℕ, i = 2 → g i k = eV k := by intro i k h; subst h; rfl
  have hmem : ∀ p : (Σ i : Fin 3, Fin (![1, l, l] i)), g p.1.val p.2.val ∈ A := by
    intro p
    rcases hbound p with ⟨h1, _⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [g0 _ _ h1]; exact hx
    · rw [g1 _ _ h1]; exact hU (heU _ h2)
    · rw [g2 _ _ h1]; exact hV (heV _ h2)
  let f : (Σ i : Fin 3, Fin (![1, l, l] i)) → (A : Set ℕ) := fun p => ⟨g p.1.val p.2.val, hmem p⟩
  have key : ∀ p q : (Σ i : Fin 3, Fin (![1, l, l] i)), p.1 ≠ q.1 →
      g p.1.val p.2.val ≠ g q.1.val q.2.val ∧ Nat.Coprime (g p.1.val p.2.val) (g q.1.val q.2.val) := by
    intro p q hpq
    have hv : p.1.val ≠ q.1.val := fun h => hpq (Fin.ext h)
    rcases hbound p with ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
    rcases hbound q with ⟨b1, b2⟩ | ⟨b1, b2⟩ | ⟨b1, b2⟩
    · exact absurd (a1.trans b1.symm) hv
    · rw [g0 _ _ a1, g1 _ _ b1]; exact hxU _ (heU _ b2)
    · rw [g0 _ _ a1, g2 _ _ b1]; exact hxV _ (heV _ b2)
    · rw [g1 _ _ a1, g0 _ _ b1]; have := hxU _ (heU _ a2); exact ⟨this.1.symm, this.2.symm⟩
    · exact absurd (a1.trans b1.symm) hv
    · rw [g1 _ _ a1, g2 _ _ b1]; exact hUV _ (heU _ a2) _ (heV _ b2)
    · rw [g2 _ _ a1, g0 _ _ b1]; have := hxV _ (heV _ a2); exact ⟨this.1.symm, this.2.symm⟩
    · rw [g2 _ _ a1, g1 _ _ b1]; have := hUV _ (heU _ b2) _ (heV _ a2)
      exact ⟨this.1.symm, this.2.symm⟩
    · exact absurd (a1.trans b1.symm) hv
  refine ⟨⟨⟨f, ?_⟩, ?_⟩⟩
  · intro p q hpq
    simp only [completeMultipartiteGraph, SimpleGraph.comap_adj, top_adj] at hpq
    simp only [f, SimpleGraph.comap_adj, Function.Embedding.coe_subtype]
    exact (adj_iff _ _).2 (key p q hpq)
  · intro p q hpq
    have hpq' : g p.1.val p.2.val = g q.1.val q.2.val := congrArg Subtype.val hpq
    by_cases h : p.1 = q.1
    · rcases p with ⟨i, k⟩
      rcases q with ⟨j, k'⟩
      simp only at h
      subst h
      simp only at hpq'
      suffices hk : k.val = k'.val by
        have : k = k' := Fin.ext hk
        rw [this]
      rcases hbound ⟨i, k⟩ with ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
      rcases hbound ⟨i, k'⟩ with ⟨b1, b2⟩ | ⟨b1, b2⟩ | ⟨b1, b2⟩ <;> simp only at a1 a2 b1 b2
      · omega
      all_goals first
        | omega
        | (rw [g1 _ _ a1, g1 _ _ b1] at hpq'; exact hiU _ _ a2 b2 hpq')
        | (rw [g2 _ _ a1, g2 _ _ b1] at hpq'; exact hiV _ _ a2 b2 hpq')
    · exact absurd hpq' (key p q h).1


lemma greedy (Y Z : Finset ℕ) (bad : ℕ → ℕ → Prop) [DecidableRel bad] (l : ℕ) (N : ℝ)
    (hY : N ≤ Y.card) (hZ : N ≤ Z.card) (hN : 2 * (l : ℝ) ≤ N)
    (hB : 4 * (l : ℝ) * (((Y ×ˢ Z).filter (fun p => bad p.1 p.2)).card : ℝ) ≤ N ^ 2) :
    ∃ U ⊆ Y, ∃ V ⊆ Z, U.card = l ∧ V.card = l ∧ ∀ u ∈ U, ∀ v ∈ V, ¬ bad u v := by
  classical
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · exact ⟨∅, empty_subset _, ∅, empty_subset _, rfl, rfl, by simp⟩
  have hl' : (0 : ℝ) < l := by exact_mod_cast hl
  have hNpos : 0 < N := by linarith
  set B := (Y ×ˢ Z).filter (fun p => bad p.1 p.2) with hBdef
  let deg : ℕ → ℕ := fun y => (Z.filter (fun z => bad y z)).card
  have hsum : ∑ y ∈ Y, deg y = B.card := by
    rw [hBdef, card_filter, sum_product]
    refine sum_congr rfl (fun y _ => ?_)
    simp only [deg]
    rw [card_filter]
  set Y' := Y.filter (fun y => 2 * (l : ℝ) * (deg y : ℝ) ≤ N) with hY'def
  have hYY : ((Y \ Y').card : ℝ) * N ≤ 2 * l * B.card := by
    have h1 : ∑ y ∈ Y \ Y', (N : ℝ) ≤ ∑ y ∈ Y \ Y', 2 * (l : ℝ) * (deg y : ℝ) := by
      apply sum_le_sum
      intro y hy
      rw [mem_sdiff, hY'def, mem_filter] at hy
      push Not at hy
      exact le_of_lt (hy.2 hy.1)
    have h2 : ∑ y ∈ Y \ Y', 2 * (l : ℝ) * (deg y : ℝ) ≤ ∑ y ∈ Y, 2 * (l : ℝ) * (deg y : ℝ) :=
      sum_le_sum_of_subset_of_nonneg sdiff_subset (fun _ _ _ => by positivity)
    have h3 : ∑ y ∈ Y, 2 * (l : ℝ) * (deg y : ℝ) = 2 * l * B.card := by
      rw [← mul_sum, ← hsum]; push_cast; ring
    rw [sum_const, nsmul_eq_mul] at h1
    linarith
  have hY'card : (l : ℝ) ≤ Y'.card := by
    have hc : (Y'.card : ℝ) + (Y \ Y').card = Y.card := by
      have := card_sdiff_add_card_inter Y Y'
      have hi : Y ∩ Y' = Y' := inter_eq_right.2 (filter_subset _ _)
      rw [hi] at this
      exact_mod_cast (by omega : Y'.card + (Y \ Y').card = Y.card)
    have : ((Y \ Y').card : ℝ) ≤ N / 2 := by
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
      have : ((Y \ Y').card : ℝ) * N ≤ N ^ 2 / 2 := by nlinarith
      nlinarith
    linarith
  obtain ⟨U, hUY', hU⟩ := exists_subset_card_eq (s := Y') (n := l) (by exact_mod_cast hY'card)
  set W := Z.filter (fun z => ∃ u ∈ U, bad u z) with hWdef
  have hW : 2 * (W.card : ℝ) ≤ N := by
    have h1 : W ⊆ U.biUnion (fun u => Z.filter (fun z => bad u z)) := by
      intro z hz
      rw [hWdef, mem_filter] at hz
      obtain ⟨u, hu, hb⟩ := hz.2
      exact mem_biUnion.2 ⟨u, hu, mem_filter.2 ⟨hz.1, hb⟩⟩
    have h2 : (W.card : ℝ) ≤ ∑ u ∈ U, (deg u : ℝ) := by
      have := (card_le_card h1).trans card_biUnion_le
      exact_mod_cast this
    have h3 : ∑ u ∈ U, 2 * (l : ℝ) * (deg u : ℝ) ≤ ∑ u ∈ U, N := by
      apply sum_le_sum
      intro u hu
      have := hUY' hu
      rw [hY'def, mem_filter] at this
      exact this.2
    rw [← mul_sum, sum_const, nsmul_eq_mul, hU] at h3
    nlinarith
  have hZW : l ≤ (Z \ W).card := by
    have h1 : (Z \ W).card + W.card = Z.card := by
      have := card_sdiff_add_card_inter Z W
      have hi : Z ∩ W = W := inter_eq_right.2 (filter_subset _ _)
      rw [hi] at this; exact this
    have : (l : ℝ) ≤ (Z \ W).card := by
      have : ((Z \ W).card : ℝ) + W.card = Z.card := by exact_mod_cast h1
      linarith
    exact_mod_cast this
  obtain ⟨V, hV, hVc⟩ := exists_subset_card_eq hZW
  refine ⟨U, hUY'.trans (filter_subset _ _), V, hV.trans sdiff_subset, hU, hVc, ?_⟩
  intro u hu v hv hb
  have hv' := mem_sdiff.1 (hV hv)
  exact hv'.2 (mem_filter.2 ⟨hv'.1, u, hu, hb⟩)

/-- the residue class of `j` mod `Q` inside `[1, n]` -/
def cls (n Q j : ℕ) : Finset ℕ := (Icc 1 n).filter (fun y => y % Q = j % Q)

lemma mem_cls {n Q j y : ℕ} : y ∈ cls n Q j ↔ 1 ≤ y ∧ y ≤ n ∧ y % Q = j % Q := by
  simp [cls, and_assoc]

lemma card_cls_dvd_le (n Q j p : ℕ) (_hQ : 0 < Q) (_hp : 0 < p) (hcop : Nat.Coprime Q p) :
    ((cls n Q j).filter (fun y => p ∣ y)).card ≤ n / (Q * p) + 1 := by
  classical
  have hinj : Set.InjOn (fun y => y / (Q * p)) ((cls n Q j).filter (fun y => p ∣ y) : Set ℕ) := by
    intro y hy y' hy' h
    simp only [coe_filter, Set.mem_ofPred_eq, mem_cls] at hy hy'
    have h1 : y ≡ y' [MOD Q] := hy.1.2.2.trans hy'.1.2.2.symm
    have h2 : y ≡ y' [MOD p] := by
      unfold Nat.ModEq
      rw [Nat.mod_eq_zero_of_dvd hy.2, Nat.mod_eq_zero_of_dvd hy'.2]
    have h3 := (Nat.modEq_and_modEq_iff_modEq_mul hcop).1 ⟨h1, h2⟩
    simp only at h
    rw [← Nat.div_add_mod y (Q*p), ← Nat.div_add_mod y' (Q*p), h, h3]
  calc _ ≤ (range (n / (Q * p) + 1)).card := by
        apply card_le_card_of_injOn _ _ hinj
        intro y hy
        simp only [coe_filter, Set.mem_ofPred_eq, mem_cls] at hy
        simp only [coe_range, Set.mem_Iio]
        exact Nat.lt_succ_of_le (Nat.div_le_div_right hy.1.2.1)
    _ = _ := card_range _

lemma card_cls_le (n Q j : ℕ) (hQ : 0 < Q) : (cls n Q j).card ≤ n / Q + 1 := by
  have := card_cls_dvd_le n Q j 1 hQ one_pos (Nat.coprime_one_right _)
  simpa using this

lemma card_cls_ge (n Q j : ℕ) (hQ : 0 < Q) : n / Q ≤ (cls n Q j).card := by
  classical
  set r := if j % Q = 0 then Q else j % Q with hr
  have hr1 : 1 ≤ r := by
    rw [hr]; split_ifs with h
    · exact hQ
    · omega
  have hrQ : r ≤ Q := by
    rw [hr]; split_ifs with h
    · exact le_rfl
    · exact (Nat.mod_lt _ hQ).le
  have hrm : r % Q = j % Q := by
    rw [hr]; split_ifs with h
    · rw [Nat.mod_self, h]
    · exact Nat.mod_mod _ _
  have hinj : Set.InjOn (fun k => Q * k + r) (range (n / Q) : Set ℕ) := by
    intro k _ k' _ h
    simp only at h
    have : Q * k = Q * k' := by omega
    exact Nat.eq_of_mul_eq_mul_left hQ this
  calc n / Q = (range (n / Q)).card := (card_range _).symm
    _ ≤ _ := by
      apply card_le_card_of_injOn _ _ hinj
      intro k hk
      simp only [coe_range, Set.mem_Iio] at hk
      rw [mem_coe, mem_cls]
      dsimp only
      refine ⟨by nlinarith, ?_, ?_⟩
      · have h1 : Q * k + r ≤ Q * (n / Q) := by
          have : k + 1 ≤ n / Q := hk
          nlinarith
        exact h1.trans (Nat.mul_div_le n Q)
      · rw [Nat.mul_add_mod]; exact hrm


noncomputable def wt (R x : ℕ) : ℝ := ∑ p ∈ x.primeFactors.filter (fun p => R < p), (1 : ℝ) / p

lemma wt_nonneg (R x : ℕ) : 0 ≤ wt R x := by
  unfold wt; positivity

lemma dvd_of_mod_eq {Q j y p : ℕ} (hpQ : p ∣ Q) (h : y % Q = j % Q) (hy : p ∣ y) : p ∣ j := by
  have : p ∣ y % Q := (Nat.dvd_mod_iff hpQ).2 hy
  rw [h] at this
  exact (Nat.dvd_mod_iff hpQ).1 this

lemma coprime_of_gt {Q R p : ℕ} (hQR : ∀ q, q.Prime → q ∣ Q → q ≤ R) (hp : p.Prime) (hRp : R < p) :
    Nat.Coprime Q p := by
  have hpQ : ¬ p ∣ Q := fun h => absurd (hQR p hp h) (not_le.2 hRp)
  exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 hpQ)

lemma card_cls_dvd_le' (n Q j p : ℕ) (hQ : 0 < Q) (hp : 0 < p) (hcop : Nat.Coprime Q p) :
    (((cls n Q j).filter (fun y => p ∣ y)).card : ℝ) ≤ (n : ℝ) / (Q * p) + 1 := by
  have h := card_cls_dvd_le n Q j p hQ hp hcop
  have h2 : ((n / (Q * p) : ℕ) : ℝ) ≤ (n : ℝ) / (Q * p) := by
    have := Nat.cast_div_le (α := ℝ) (m := n) (n := Q * p)
    simpa using this
  calc (((cls n Q j).filter (fun y => p ∣ y)).card : ℝ) ≤ ((n / (Q * p) + 1 : ℕ) : ℝ) := by
        exact_mod_cast h
    _ ≤ _ := by push_cast; linarith

lemma card_noncop_le (n Q R j x : ℕ) (hQ : 0 < Q) (hRQ : ∀ p, p.Prime → p ≤ R → p ∣ Q)
    (hQR : ∀ p, p.Prime → p ∣ Q → p ≤ R) (hx0 : x ≠ 0)
    (hxj : ∀ p, p.Prime → p ∣ Q → ¬ (p ∣ x ∧ p ∣ j)) :
    (((cls n Q j).filter (fun y => ¬ Nat.Coprime x y)).card : ℝ) ≤
      ((n : ℝ) / Q) * wt R x + x.primeFactors.card := by
  classical
  set F := x.primeFactors.filter (fun p => R < p) with hF
  have hsub : (cls n Q j).filter (fun y => ¬ Nat.Coprime x y) ⊆
      F.biUnion (fun p => (cls n Q j).filter (fun y => p ∣ y)) := by
    intro y hy
    rw [mem_filter] at hy
    obtain ⟨p, hp, hpx, hpy⟩ := Nat.Prime.not_coprime_iff_dvd.1 hy.2
    have hpQ : ¬ p ∣ Q := fun hpQ => hxj p hp hpQ ⟨hpx, dvd_of_mod_eq hpQ (mem_cls.1 hy.1).2.2 hpy⟩
    have hRp : R < p := by
      by_contra h
      exact hpQ (hRQ p hp (not_lt.1 h))
    exact mem_biUnion.2 ⟨p, mem_filter.2 ⟨Nat.mem_primeFactors.2 ⟨hp, hpx, hx0⟩, hRp⟩,
      mem_filter.2 ⟨hy.1, hpy⟩⟩
  have h1 : (((cls n Q j).filter (fun y => ¬ Nat.Coprime x y)).card : ℝ) ≤
      ∑ p ∈ F, (((cls n Q j).filter (fun y => p ∣ y)).card : ℝ) := by
    have := (card_le_card hsub).trans card_biUnion_le
    exact_mod_cast this
  have h2 : ∑ p ∈ F, (((cls n Q j).filter (fun y => p ∣ y)).card : ℝ) ≤
      ∑ p ∈ F, ((n : ℝ) / (Q * p) + 1) := by
    apply sum_le_sum
    intro p hp
    have hp' := mem_filter.1 hp
    have hpp := Nat.prime_of_mem_primeFactors hp'.1
    exact card_cls_dvd_le' n Q j p hQ hpp.pos (coprime_of_gt hQR hpp hp'.2)
  have h3 : ∑ p ∈ F, ((n : ℝ) / (Q * p) + 1) = ((n : ℝ) / Q) * wt R x + F.card := by
    rw [sum_add_distrib, wt, mul_sum, sum_const, nsmul_eq_mul, mul_one]
    congr 1
    refine sum_congr rfl (fun p _ => ?_)
    field_simp
  have h4 : (F.card : ℝ) ≤ x.primeFactors.card := by
    exact_mod_cast card_filter_le _ _
  linarith

lemma sum_inv_sq_primes_le (R n : ℕ) :
    ∑ p ∈ (Ioo R (n + 1)).filter Nat.Prime, ((p : ℝ) ^ 2)⁻¹ ≤ 2 / (R + 1) := by
  calc ∑ p ∈ (Ioo R (n + 1)).filter Nat.Prime, ((p : ℝ) ^ 2)⁻¹
      ≤ ∑ p ∈ Ioo R (n + 1), ((p : ℝ) ^ 2)⁻¹ :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
    _ ≤ 2 / (R + 1) := sum_Ioo_inv_sq_le R (n + 1)

lemma card_cross_le (n Q R j2 j3 : ℕ) (hQ : 0 < Q) (hRQ : ∀ p, p.Prime → p ≤ R → p ∣ Q)
    (hQR : ∀ p, p.Prime → p ∣ Q → p ≤ R)
    (h23 : ∀ p, p.Prime → p ∣ Q → ¬ (p ∣ j2 ∧ p ∣ j3)) (Y Z : Finset ℕ)
    (hY : Y ⊆ cls n Q j2) (hZ : Z ⊆ cls n Q j3) :
    (((Y ×ˢ Z).filter (fun yz => ¬ Nat.Coprime yz.1 yz.2)).card : ℝ) ≤
      2 * ((n : ℝ) / Q) ^ 2 * (2 / (R + 1)) + 2 * (n + 1) := by
  classical
  set P := (Ioo R (n + 1)).filter Nat.Prime with hP
  have hsub : (Y ×ˢ Z).filter (fun yz => ¬ Nat.Coprime yz.1 yz.2) ⊆
      P.biUnion (fun p => ((cls n Q j2).filter (fun y => p ∣ y)) ×ˢ
        ((cls n Q j3).filter (fun y => p ∣ y))) := by
    rintro ⟨y, z⟩ hyz
    rw [mem_filter, mem_product] at hyz
    obtain ⟨⟨hy, hz⟩, hb⟩ := hyz
    obtain ⟨p, hp, hpy, hpz⟩ := Nat.Prime.not_coprime_iff_dvd.1 hb
    have hy' := mem_cls.1 (hY hy)
    have hz' := mem_cls.1 (hZ hz)
    have hpQ : ¬ p ∣ Q := fun hpQ =>
      h23 p hp hpQ ⟨dvd_of_mod_eq hpQ hy'.2.2 hpy, dvd_of_mod_eq hpQ hz'.2.2 hpz⟩
    have hRp : R < p := by
      by_contra h
      exact hpQ (hRQ p hp (not_lt.1 h))
    have hpn : p < n + 1 := Nat.lt_succ_of_le ((Nat.le_of_dvd (by omega) hpy).trans hy'.2.1)
    refine mem_biUnion.2 ⟨p, mem_filter.2 ⟨mem_Ioo.2 ⟨hRp, hpn⟩, hp⟩, ?_⟩
    exact mem_product.2 ⟨mem_filter.2 ⟨hY hy, hpy⟩, mem_filter.2 ⟨hZ hz, hpz⟩⟩
  have h1 : (((Y ×ˢ Z).filter (fun yz => ¬ Nat.Coprime yz.1 yz.2)).card : ℝ) ≤
      ∑ p ∈ P, (((cls n Q j2).filter (fun y => p ∣ y)).card : ℝ) *
        (((cls n Q j3).filter (fun y => p ∣ y)).card : ℝ) := by
    have := (card_le_card hsub).trans card_biUnion_le
    simp only [card_product] at this
    exact_mod_cast this
  have h2 : ∀ p ∈ P, (((cls n Q j2).filter (fun y => p ∣ y)).card : ℝ) *
        (((cls n Q j3).filter (fun y => p ∣ y)).card : ℝ) ≤
        2 * ((n : ℝ) / Q) ^ 2 * ((p : ℝ) ^ 2)⁻¹ + 2 := by
    intro p hp
    have hp' := mem_filter.1 hp
    have hpp := hp'.2
    have hRp := (mem_Ioo.1 hp'.1).1
    have hc := coprime_of_gt hQR hpp hRp
    have a2 := card_cls_dvd_le' n Q j2 p hQ hpp.pos hc
    have a3 := card_cls_dvd_le' n Q j3 p hQ hpp.pos hc
    have e : (n : ℝ) / (Q * p) = ((n : ℝ) / Q) * (p : ℝ)⁻¹ := by
      rw [div_mul_eq_div_div, div_eq_mul_inv]
    rw [e] at a2 a3
    have hpos : (0 : ℝ) ≤ ((n : ℝ) / Q) * (p : ℝ)⁻¹ := by positivity
    have : ((n : ℝ) / Q) ^ 2 * ((p : ℝ) ^ 2)⁻¹ = (((n : ℝ) / Q) * (p : ℝ)⁻¹) ^ 2 := by
      rw [mul_pow, inv_pow]
    rw [mul_assoc, this]
    have c2 : (0 : ℝ) ≤ (((cls n Q j2).filter (fun y => p ∣ y)).card : ℝ) := by positivity
    have c3 : (0 : ℝ) ≤ (((cls n Q j3).filter (fun y => p ∣ y)).card : ℝ) := by positivity
    have hm := mul_le_mul a2 a3 c3 (by positivity)
    nlinarith [sq_nonneg (((n : ℝ) / Q) * (p : ℝ)⁻¹ - 1)]
  have h3 := sum_le_sum h2
  rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul] at h3
  have h4 := sum_inv_sq_primes_le R n
  have h5 : (P.card : ℝ) ≤ n + 1 := by
    have : P.card ≤ n + 1 := (card_filter_le _ _).trans (by rw [Nat.card_Ioo]; omega)
    exact_mod_cast this
  have h6 : (0 : ℝ) ≤ 2 * ((n : ℝ) / Q) ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h4 h6]

theorem core (l n Q R x j2 j3 : ℕ) (A : Finset ℕ) (β N : ℝ)
    (hA : A ⊆ Icc 1 n)
    (hQ : 0 < Q) (hRQ : ∀ p, p.Prime → p ≤ R → p ∣ Q) (hQR : ∀ p, p.Prime → p ∣ Q → p ≤ R)
    (hxA : x ∈ A) (hx0 : x ≠ 0)
    (h2 : ∀ p, p.Prime → p ∣ Q → ¬ (p ∣ x ∧ p ∣ j2))
    (h3 : ∀ p, p.Prime → p ∣ Q → ¬ (p ∣ x ∧ p ∣ j3))
    (h23 : ∀ p, p.Prime → p ∣ Q → ¬ (p ∣ j2 ∧ p ∣ j3))
    (hd2 : x % Q ≠ j2 % Q) (hd3 : x % Q ≠ j3 % Q) (hd23 : j2 % Q ≠ j3 % Q)
    (hA2 : β * ((n : ℝ) / Q) ≤ ((A.filter (fun y => y % Q = j2 % Q)).card : ℝ))
    (hA3 : β * ((n : ℝ) / Q) ≤ ((A.filter (fun y => y % Q = j3 % Q)).card : ℝ))
    (hN : N ≤ β * ((n : ℝ) / Q) - (((n : ℝ) / Q) * wt R x + x.primeFactors.card))
    (hl : 2 * (l : ℝ) ≤ N)
    (hbad : 4 * (l : ℝ) * (2 * ((n : ℝ) / Q) ^ 2 * (2 / (R + 1)) + 2 * (n + 1)) ≤ N ^ 2) :
    (completeMultipartiteGraph (fun i : Fin 3 ↦ Fin (![1, l, l] i))).IsContained
      (coprimeGraph.induce (A : Set ℕ)) := by
  classical
  have hAc : ∀ j, A.filter (fun y => y % Q = j % Q) ⊆ cls n Q j := by
    intro j y hy
    rw [mem_filter] at hy
    have := mem_Icc.1 (hA hy.1)
    exact mem_cls.2 ⟨this.1, this.2, hy.2⟩
  set Y0 := (A.filter (fun y => y % Q = j2 % Q)).filter (fun y => Nat.Coprime x y) with hY0
  set Z0 := (A.filter (fun y => y % Q = j3 % Q)).filter (fun y => Nat.Coprime x y) with hZ0
  have hcnt : ∀ j, (∀ p, p.Prime → p ∣ Q → ¬ (p ∣ x ∧ p ∣ j)) →
      β * ((n : ℝ) / Q) ≤ ((A.filter (fun y => y % Q = j % Q)).card : ℝ) →
      N ≤ (((A.filter (fun y => y % Q = j % Q)).filter (fun y => Nat.Coprime x y)).card : ℝ) := by
    intro j hj hAj
    have e := card_filter_add_card_filter_not (s := A.filter (fun y => y % Q = j % Q))
      (fun y => Nat.Coprime x y)
    have hsub : (A.filter (fun y => y % Q = j % Q)).filter (fun y => ¬ Nat.Coprime x y) ⊆
        (cls n Q j).filter (fun y => ¬ Nat.Coprime x y) := filter_subset_filter _ (hAc j)
    have hb := card_noncop_le n Q R j x hQ hRQ hQR hx0 hj
    have hb2 : (((A.filter (fun y => y % Q = j % Q)).filter (fun y => ¬ Nat.Coprime x y)).card : ℝ)
        ≤ (((cls n Q j).filter (fun y => ¬ Nat.Coprime x y)).card : ℝ) := by
      exact_mod_cast card_le_card hsub
    have e' : ((((A.filter (fun y => y % Q = j % Q)).filter (fun y => Nat.Coprime x y)).card : ℝ) +
        (((A.filter (fun y => y % Q = j % Q)).filter (fun y => ¬ Nat.Coprime x y)).card : ℝ)) =
        ((A.filter (fun y => y % Q = j % Q)).card : ℝ) := by exact_mod_cast e
    linarith
  have hY := hcnt j2 h2 hA2
  have hZ := hcnt j3 h3 hA3
  have hYc : Y0 ⊆ cls n Q j2 := (filter_subset _ _).trans (hAc j2)
  have hZc : Z0 ⊆ cls n Q j3 := (filter_subset _ _).trans (hAc j3)
  have hB := card_cross_le n Q R j2 j3 hQ hRQ hQR h23 Y0 Z0 hYc hZc
  have hl0 : (0 : ℝ) ≤ l := by positivity
  have hB' : 4 * (l : ℝ) * (((Y0 ×ˢ Z0).filter (fun yz => ¬ Nat.Coprime yz.1 yz.2)).card : ℝ) ≤
      N ^ 2 := le_trans (mul_le_mul_of_nonneg_left hB (by positivity)) hbad
  obtain ⟨U, hU, V, hV, hUc, hVc, hUV⟩ :=
    greedy Y0 Z0 (fun u v => ¬ Nat.Coprime u v) l N hY hZ hl hB'
  have hUA : U ⊆ A := hU.trans ((filter_subset _ _).trans (filter_subset _ _))
  have hVA : V ⊆ A := hV.trans ((filter_subset _ _).trans (filter_subset _ _))
  refine embed A l x U V hxA hUA hVA hUc hVc ?_ ?_ ?_
  · intro u hu
    have h := mem_filter.1 (hU hu)
    have h' := mem_filter.1 h.1
    refine ⟨?_, h.2⟩
    rintro rfl
    exact hd2 h'.2
  · intro v hv
    have h := mem_filter.1 (hV hv)
    have h' := mem_filter.1 h.1
    refine ⟨?_, h.2⟩
    rintro rfl
    exact hd3 h'.2
  · intro u hu v hv
    have hu' := mem_filter.1 (mem_filter.1 (hU hu)).1
    have hv' := mem_filter.1 (mem_filter.1 (hV hv)).1
    refine ⟨?_, ?_⟩
    · rintro rfl
      exact hd23 (hu'.2.symm.trans hv'.2)
    · have := hUV u hu v hv
      simpa using this


lemma dvd_primorial_of_le {p R : ℕ} (hp : p.Prime) (h : p ≤ R) : p ∣ primorial R := by
  unfold primorial
  exact dvd_prod_of_mem _ (mem_filter.2 ⟨mem_range.2 (Nat.lt_succ_of_le h), hp⟩)

lemma le_of_dvd_primorial {p R : ℕ} (hp : p.Prime) (h : p ∣ primorial R) : p ≤ R := by
  unfold primorial at h
  obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 h
  have hq' := mem_filter.1 hq
  have e := (Nat.prime_dvd_prime_iff_eq hp hq'.2).1 hpq
  have := mem_range.1 hq'.1
  omega

lemma primorial_succ_prime {k : ℕ} (hk : (k + 1).Prime) :
    primorial (k + 1) = primorial k * (k + 1) := by
  unfold primorial
  rw [range_add_one (n := k + 1), filter_insert, if_pos hk, prod_insert (by simp)]
  ring

lemma primorial_succ_not_prime {k : ℕ} (hk : ¬ (k + 1).Prime) :
    primorial (k + 1) = primorial k := by
  unfold primorial
  rw [range_add_one (n := k + 1), filter_insert, if_neg hk]

lemma totient_primorial_succ_prime {k : ℕ} (hk : (k + 1).Prime) :
    Nat.totient (primorial (k + 1)) = Nat.totient (primorial k) * k := by
  have hnd : ¬ (k + 1) ∣ primorial k := fun h => by
    have := le_of_dvd_primorial hk h; omega
  have hc : Nat.Coprime (primorial k) (k + 1) :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hk).2 hnd)
  rw [primorial_succ_prime hk, Nat.totient_mul hc, Nat.totient_prime hk]
  simp

lemma wallis : ∀ R, 2 ≤ R → (primorial R) ^ 2 ≤ 3 * R * (Nat.totient (primorial R)) ^ 2 := by
  intro R
  induction R using Nat.strong_induction_on with
  | _ R ih =>
  intro hR
  have p1 : primorial 1 = 1 := by decide
  have p2 : primorial 2 = 2 := by
    rw [primorial_succ_prime (k := 1) Nat.prime_two, p1]
  have p3 : primorial 3 = 6 := by
    rw [primorial_succ_prime (k := 2) Nat.prime_three, p2]
  rcases (by omega : R = 2 ∨ R = 3 ∨ 4 ≤ R) with rfl | rfl | hR4
  · rw [p2]; decide
  · rw [p3]; decide
  · obtain ⟨k, rfl⟩ : ∃ k, R = k + 1 := ⟨R - 1, by omega⟩
    by_cases hk : (k + 1).Prime
    · have h2k : 2 ∣ k := by
        rcases Nat.even_or_odd k with ⟨r, hr⟩ | ⟨r, hr⟩
        · exact ⟨r, by omega⟩
        · exfalso
          have := hk.eq_one_or_self_of_dvd 2 ⟨r + 1, by omega⟩
          omega
      have hk1 : ¬ k.Prime := by
        intro hp
        have := hp.eq_one_or_self_of_dvd 2 h2k
        omega
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      have ihm := ih m (by omega) (by omega)
      rw [totient_primorial_succ_prime hk, primorial_succ_prime hk,
        primorial_succ_not_prime hk1]
      set P := primorial m
      set φ := Nat.totient (primorial m)
      have key : (m : ℕ) * (m + 2) ≤ (m + 1) ^ 2 := by nlinarith
      calc (P * (m + 1 + 1)) ^ 2 = P ^ 2 * (m + 2) ^ 2 := by ring
        _ ≤ 3 * m * φ ^ 2 * (m + 2) ^ 2 := Nat.mul_le_mul_right _ ihm
        _ = 3 * (m + 2) * φ ^ 2 * (m * (m + 2)) := by ring
        _ ≤ 3 * (m + 2) * φ ^ 2 * ((m + 1) ^ 2) := Nat.mul_le_mul_left _ key
        _ = 3 * (m + 1 + 1) * (φ * (m + 1)) ^ 2 := by ring
    · rw [primorial_succ_not_prime hk]
      have := ih k (by omega) (by omega)
      calc primorial k ^ 2 ≤ 3 * k * Nat.totient (primorial k) ^ 2 := this
        _ ≤ 3 * (k + 1) * Nat.totient (primorial k) ^ 2 := by gcongr; omega

lemma markov (n Q R j : ℕ) (η : ℝ) (hη : 0 < η) (hQ : 0 < Q)
    (hQR : ∀ p, p.Prime → p ∣ Q → p ≤ R) :
    η * (((cls n Q j).filter (fun x => η < wt R x)).card : ℝ) ≤
      ((n : ℝ) / Q) * (2 / (R + 1)) + (1 + Real.log n) := by
  classical
  set C := cls n Q j with hC
  set P := (Ioo R (n + 1)).filter Nat.Prime with hP
  have hwt : ∀ x ∈ C, wt R x = ∑ p ∈ P, if p ∣ x then (1 : ℝ) / p else 0 := by
    intro x hx
    have hx' := mem_cls.1 hx
    rw [wt, ← sum_filter]
    apply sum_congr _ (fun _ _ => rfl)
    ext p
    simp only [mem_filter, Nat.mem_primeFactors, mem_Ioo, P]
    constructor
    · rintro ⟨⟨hp, hpx, _⟩, hRp⟩
      exact ⟨⟨⟨hRp, Nat.lt_succ_of_le ((Nat.le_of_dvd (by omega) hpx).trans hx'.2.1)⟩, hp⟩, hpx⟩
    · rintro ⟨⟨⟨hRp, _⟩, hp⟩, hpx⟩
      exact ⟨⟨hp, hpx, by omega⟩, hRp⟩
  have h1 : η * ((C.filter (fun x => η < wt R x)).card : ℝ) ≤ ∑ x ∈ C, wt R x := by
    calc η * ((C.filter (fun x => η < wt R x)).card : ℝ)
        = ∑ x ∈ C.filter (fun x => η < wt R x), η := by rw [sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ x ∈ C.filter (fun x => η < wt R x), wt R x :=
          sum_le_sum (fun x hx => (mem_filter.1 hx).2.le)
      _ ≤ ∑ x ∈ C, wt R x :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun x _ _ => wt_nonneg R x)
  have h2 : ∑ x ∈ C, wt R x = ∑ p ∈ P, (1 / (p : ℝ)) * ((C.filter (fun x => p ∣ x)).card : ℝ) := by
    rw [sum_congr rfl hwt, sum_comm]
    refine sum_congr rfl (fun p _ => ?_)
    rw [← sum_filter, sum_const, nsmul_eq_mul]; ring
  have h3 : ∀ p ∈ P, (1 / (p : ℝ)) * ((C.filter (fun x => p ∣ x)).card : ℝ) ≤
      ((n : ℝ) / Q) * ((p : ℝ) ^ 2)⁻¹ + 1 / p := by
    intro p hp
    have hp' := mem_filter.1 hp
    have hc := card_cls_dvd_le' n Q j p hQ hp'.2.pos (coprime_of_gt hQR hp'.2 (mem_Ioo.1 hp'.1).1)
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp'.2.pos
    have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
    calc (1 / (p : ℝ)) * ((C.filter (fun x => p ∣ x)).card : ℝ)
        ≤ (1 / (p : ℝ)) * ((n : ℝ) / (Q * p) + 1) := mul_le_mul_of_nonneg_left hc (by positivity)
      _ = _ := by field_simp
  have h4 : ∑ p ∈ P, (1 / (p : ℝ)) ≤ 1 + Real.log n := by
    calc ∑ p ∈ P, (1 / (p : ℝ)) ≤ ∑ i ∈ range (n + 1), (1 / (i : ℝ)) := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro p hp
            exact mem_range.2 (mem_Ioo.1 (mem_filter.1 hp).1).2
          · intro _ _ _; positivity
      _ = (harmonic n : ℝ) := by
          rw [sum_range_succ']
          simp [harmonic]
      _ ≤ 1 + Real.log n := harmonic_le_one_add_log n
  have h5 := sum_le_sum h3
  rw [sum_add_distrib, ← mul_sum] at h5
  have h6 := sum_inv_sq_primes_le R n
  have h7 : (0 : ℝ) ≤ (n : ℝ) / Q := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h6 h7]

lemma wt_le_top (n R x : ℕ) (hx0 : x ≠ 0) (hx : x ≤ n) (hR : 2 ^ 48 ≤ R + 1)
    (hn : n < 64 ^ (R + 1)) : wt R x ≤ 1 / 8 := by
  classical
  set F := x.primeFactors.filter (fun p => R < p) with hF
  have h1 : wt R x ≤ (F.card : ℝ) / (R + 1) := by
    rw [wt]
    calc ∑ p ∈ F, (1 : ℝ) / p ≤ ∑ p ∈ F, (1 : ℝ) / (R + 1) := by
          apply sum_le_sum
          intro p hp
          have h := (mem_filter.1 hp).2
          have : (R : ℝ) + 1 ≤ p := by exact_mod_cast h
          exact one_div_le_one_div_of_le (by positivity) this
      _ = _ := by rw [sum_const, nsmul_eq_mul]; ring
  have h2 : (R + 1) ^ F.card ≤ x := by
    calc (R + 1) ^ F.card = ∏ p ∈ F, (R + 1) := by rw [prod_const]
      _ ≤ ∏ p ∈ F, p := prod_le_prod' (fun p hp => (mem_filter.1 hp).2)
      _ ≤ ∏ p ∈ x.primeFactors, p := prod_le_prod_of_subset_of_one_le' (filter_subset _ _)
          (fun p hp _ => (Nat.prime_of_mem_primeFactors hp).one_lt.le)
      _ ≤ x := Nat.le_of_dvd (Nat.pos_of_ne_zero hx0) (Nat.prod_primeFactors_dvd x)
  have h3 : 8 * F.card < R + 1 := by
    by_contra hc
    push Not at hc
    have a1 : 2 ^ (48 * F.card) ≤ (R + 1) ^ F.card := by
      rw [pow_mul]; exact Nat.pow_le_pow_left hR _
    have a2 : 64 ^ (R + 1) ≤ 2 ^ (48 * F.card) := by
      rw [show (64 : ℕ) = 2 ^ 6 by norm_num, ← pow_mul]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    exact absurd (lt_of_lt_of_le hn (a2.trans (a1.trans (h2.trans hx)))) (lt_irrefl _)
  have h4 : (F.card : ℝ) / (R + 1) ≤ 1 / 8 := by
    rw [div_le_iff₀ (by positivity)]
    have : (8 * F.card : ℝ) < R + 1 := by exact_mod_cast h3
    linarith
  linarith

lemma card_primeFactors_le_log (x : ℕ) (hx : x ≠ 0) : x.primeFactors.card ≤ Nat.log 2 x := by
  have h : 2 ^ x.primeFactors.card ≤ x := by
    calc 2 ^ x.primeFactors.card = ∏ p ∈ x.primeFactors, 2 := by rw [prod_const]
      _ ≤ ∏ p ∈ x.primeFactors, p :=
          prod_le_prod' (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
      _ ≤ x := Nat.le_of_dvd (Nat.pos_of_ne_zero hx) (Nat.prod_primeFactors_dvd x)
  exact Nat.le_log_of_pow_le (by norm_num) h


lemma fiber_mul_le (Q c d : ℕ) (hd : 0 < d) (hdQ : d ∣ Q) (hQ : 0 < Q) :
    ((range Q).filter (fun u => (d * u) % Q = c)).card ≤ d := by
  classical
  obtain ⟨Q', rfl⟩ := hdQ
  have hQ' : 0 < Q' := by
    rcases Nat.eq_zero_or_pos Q' with h | h
    · subst h; simp at hQ
    · exact h
  have hinj : Set.InjOn (fun u => u / Q') ((range (d * Q')).filter (fun u => (d * u) % (d * Q') = c) : Set ℕ) := by
    intro u hu u' hu' h
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hu hu'
    have h1 : d * u ≡ d * u' [MOD d * Q'] := hu.2.trans hu'.2.symm
    have h2 := Nat.ModEq.cancel_left_div_gcd (by positivity) h1
    rw [Nat.gcd_mul_right_left, Nat.mul_div_cancel_left _ hd] at h2
    simp only at h
    rw [← Nat.div_add_mod u Q', ← Nat.div_add_mod u' Q', h, h2]
  calc _ ≤ (range d).card := by
        apply card_le_card_of_injOn _ _ hinj
        intro u hu
        simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hu
        simp only [coe_range, Set.mem_Iio]
        exact Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hu.1)
    _ = d := card_range _

theorem case1 (l n L x u : ℕ) (A : Finset ℕ) (hA : A ⊆ Icc 1 n) (hL3 : 3 ≤ L)
    (hL : 512 * (l : ℝ) ≤ L + 1) (hx : x ∈ A) (hx2 : ¬ 2 ∣ x) (hx3 : ¬ 3 ∣ x)
    (hwt : wt L x ≤ 1 / 8) (hu : Nat.Coprime (primorial L) u)
    (hcls : (n : ℝ) / primorial L / 2 ≤ ((A.filter (fun y => y % primorial L = (2 * u) % primorial L)).card : ℝ))
    (hcls3 : (n : ℝ) / primorial L / 2 ≤ ((A.filter (fun y => y % primorial L = (3 * u) % primorial L)).card : ℝ))
    (hC1 : (Nat.log 2 n : ℝ) ≤ (n : ℝ) / primorial L / 8)
    (hC2 : 8 * (l : ℝ) ≤ (n : ℝ) / primorial L)
    (hC3 : 256 * (l : ℝ) * (n + 1) ≤ ((n : ℝ) / primorial L) ^ 2) :
    (completeMultipartiteGraph (fun i : Fin 3 ↦ Fin (![1, l, l] i))).IsContained
      (coprimeGraph.induce (A : Set ℕ)) := by
  set Q := primorial L with hQdef
  have hQ : 0 < Q := primorial_pos L
  have hRQ : ∀ p, p.Prime → p ≤ L → p ∣ Q := fun p hp h => dvd_primorial_of_le hp h
  have hQR : ∀ p, p.Prime → p ∣ Q → p ≤ L := fun p hp h => le_of_dvd_primorial hp h
  have h2Q : 2 ∣ Q := hRQ 2 Nat.prime_two (by omega)
  have h3Q : 3 ∣ Q := hRQ 3 Nat.prime_three (by omega)
  have hxA := mem_Icc.1 (hA hx)
  have hx0 : x ≠ 0 := by omega
  have hpu : ∀ p, p.Prime → p ∣ Q → ¬ p ∣ u := fun p hp hpQ hpu =>
    (Nat.Prime.coprime_iff_not_dvd hp).1 (Nat.Coprime.coprime_dvd_left hpQ hu) hpu
  set B : ℝ := (n : ℝ) / Q with hB
  have hB0 : 0 ≤ B := by positivity
  have hω : (x.primeFactors.card : ℝ) ≤ Nat.log 2 n := by
    have := (card_primeFactors_le_log x hx0).trans (Nat.log_mono_right hxA.2)
    exact_mod_cast this
  refine core l n Q L x (2 * u) (3 * u) A (1 / 2) (B / 4) hA hQ hRQ hQR hx hx0 ?_ ?_ ?_ ?_ ?_ ?_
    (by rw [← hB]; linarith) (by rw [← hB]; linarith) ?_ (by linarith) ?_
  · intro p hp hpQ ⟨hpx, hp2⟩
    rcases (Nat.Prime.dvd_mul hp).1 hp2 with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h
      subst this; exact hx2 hpx
    · exact hpu p hp hpQ h
  · intro p hp hpQ ⟨hpx, hp3⟩
    rcases (Nat.Prime.dvd_mul hp).1 hp3 with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h
      subst this; exact hx3 hpx
    · exact hpu p hp hpQ h
  · intro p hp hpQ ⟨hp2, hp3⟩
    rcases (Nat.Prime.dvd_mul hp).1 hp2 with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 hp3 with h' | h'
      · have e1 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h
        have e2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h'
        omega
      · exact hpu p hp hpQ h'
    · exact hpu p hp hpQ h
  · intro h
    exact hx2 (dvd_of_mod_eq h2Q h.symm (dvd_mul_right 2 u))
  · intro h
    exact hx3 (dvd_of_mod_eq h3Q h.symm (dvd_mul_right 3 u))
  · intro h
    have h2 : 2 ∣ 3 * u := dvd_of_mod_eq h2Q h (dvd_mul_right 2 u)
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h2 with h' | h'
    · omega
    · exact hpu 2 Nat.prime_two h2Q h'
  · have h1 : B * wt L x ≤ B / 8 := by nlinarith
    linarith
  · have hl0 : (0 : ℝ) ≤ l := by positivity
    have hL0 : (0 : ℝ) < L + 1 := by positivity
    have e1 : 4 * (l : ℝ) * (2 * B ^ 2 * (2 / (L + 1))) ≤ B ^ 2 / 32 := by
      have : 4 * (l : ℝ) * (2 * B ^ 2 * (2 / (L + 1))) = B ^ 2 * (16 * l / (L + 1)) := by
        field_simp
        ring
      rw [this]
      have : 16 * (l : ℝ) / (L + 1) ≤ 1 / 32 := by
        rw [div_le_iff₀ hL0]; linarith
      nlinarith [sq_nonneg B]
    nlinarith


lemma cop_off (m a b : ℕ) (hm2 : m % 2 = 1) (hm3 : m % 3 ≠ 0) (hab : a < b) (hb : b ≤ a + 6)
    (h5 : b - a ≠ 5) (h2 : 2 ∣ (b - a) → a % 2 = 0) (h3 : 3 ∣ (b - a) → a % 3 = 0) :
    Nat.Coprime (m + a) (m + b) := by
  have e : m + b = (m + a) + (b - a) := by omega
  rw [e]
  apply Nat.coprime_of_dvd
  intro p hp hpk hpkd
  have hpd : p ∣ b - a := (Nat.dvd_add_right hpk).1 hpkd
  have hple : p ≤ b - a := Nat.le_of_dvd (by omega) hpd
  have hp2 := hp.two_le
  have hd2 : 2 ∣ b - a → ¬ 2 ∣ m + a := fun h => by have := h2 h; omega
  have hd3 : 3 ∣ b - a → ¬ 3 ∣ m + a := fun h => by have := h3 h; omega
  have hp6 : p ≤ 6 := by omega
  interval_cases p
  · exact hd2 hpd hpk
  · exact hd3 hpd hpk
  · norm_num at hp
  · omega
  · norm_num at hp

lemma transversal_card : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
      (b0 || (b1 || b2)) = true →
      (b0 || (b2 || b3)) = true →
      (b0 || (b2 || b4)) = true →
      (b0 || (b2 || b6)) = true →
      (b0 || (b3 || b4)) = true →
      (b0 || (b3 || b6)) = true →
      (b0 || (b4 || b6)) = true →
      (b2 || (b3 || b4)) = true →
      (b2 || (b3 || b6)) = true →
      (b2 || (b4 || b6)) = true →
      (b3 || (b4 || b6)) = true →
      (b4 || (b5 || b6)) = true →
      3 ≤ (if b0 = true then 1 else 0) + (if b1 = true then 1 else 0) + (if b2 = true then 1 else 0) + (if b3 = true then 1 else 0) + (if b4 = true then 1 else 0) + (if b5 = true then 1 else 0) + (if b6 = true then 1 else 0) := by
  decide

lemma window (m : ℕ) (hm2 : m % 2 = 1) (hm3 : m % 3 ≠ 0) (D : ℕ → Prop) [DecidablePred D]
    (hD : ¬ ∃ a b c, a < b ∧ b < c ∧ c < 7 ∧ D a ∧ D b ∧ D c ∧ Nat.Coprime (m + a) (m + b) ∧
      Nat.Coprime (m + a) (m + c) ∧ Nat.Coprime (m + b) (m + c)) :
    3 ≤ ((range 7).filter (fun k => ¬ D k)).card := by
  classical
  set N := (range 7).filter (fun k => ¬ D k) with hN
  have hit : ∀ a b c, a < b → b < c → c < 7 → Nat.Coprime (m + a) (m + b) →
      Nat.Coprime (m + a) (m + c) → Nat.Coprime (m + b) (m + c) → (¬ D a ∨ ¬ D b ∨ ¬ D c) := by
    intro a b c hab hbc hc h1 h2 h3
    by_contra hcon
    push Not at hcon
    exact hD ⟨a, b, c, hab, hbc, hc, hcon.1, hcon.2.1, hcon.2.2, h1, h2, h3⟩
  have t0 := hit 0 1 2 (by decide) (by decide) (by decide)
    (cop_off m 0 1 hm2 hm3 (by decide) (by decide) (by decide) (by decide) (by decide))
    (cop_off m 0 2 hm2 hm3 (by decide) (by decide) (by decide) (by decide) (by decide))
    (cop_off m 1 2 hm2 hm3 (by decide) (by decide) (by decide) (by decide) (by decide))
  have t1 := hit 0 2 3 (by decide) (by decide) (by decide)
    (cop_off m 0 2 hm2 hm3 (by decide) (by decide) (by decide) (by decide) (by decide))
    (cop_off m 0 3 hm2 hm3 (by decide) (by decide) (by decide) (by decide) (by decide))
    (cop_off m 2 3 hm2 hm3 (by decide) (by decide) (by decide) (by decide) (by decide))
  have t2 := hit 0 2 4 (by decide) (by decide) (by decide)
    (cop_off m 0 2 hm2 hm3 (by decide) (by decide) (by decide) (by decide) (by decide))
    (cop_off m 0 4 hm2 hm3 (by decide) (by decide) (by decide) (by decide) (by decide))
    (cop_off m 2 4 hm2 hm3 (by decide) (by decide) (by decide) (by decide) (by decide))
  have t3 := hit 0 2 6 (by decide) (by decide) (by decide)
    (cop_off m 0 2 hm2 hm3 (by decide) (by decide) (by decide) (by decide) (by decide))
    (cop_off m 0 6 hm2 hm3 (by decide) (by decide) (by decide) (by decide) (by decide))
    (cop_off m 2 6 hm2 hm3 (by decide) (by decide) (by decide) (by decide) (by decide))
  have t4 := hit 0 3 4 (by decide) (by decide) (by decide)
    (cop_off m 0 3 hm2 hm3 (by decide) (by decide) (by decide) (by decide) (by decide))
    (cop_off m 0 4 hm2 hm3 (by decide) (by decide) (by decide) (by decide) (by decide))
    (cop_off m 3 4 hm2 hm3 (by decide) (by decide) (by decide) (by decide) (by decide))
  have t5 := hit 0 3 6 (by decide) (by decide) (by decide)
    (cop_off m 0 3 hm2 hm3 (by decide) (by decide) (by decide) (by decide) (by decide))
    (cop_off m 0 6 hm2 hm3 (by decide) (by decide) (by decide) (by decide) (by decide))
    (cop_off m 3 6 hm2 hm3 (by decide) (by decide) (by decide) (by decide) (by decide))
  have t6 := hit 0 4 6 (by decide) (by decide) (by decide)
    (cop_off m 0 4 hm2 hm3 (by decide) (by decide) (by decide) (by decide) (by decide))
    (cop_off m 0 6 hm2 hm3 (by decide) (by decide) (by decide) (by decide) (by decide))
    (cop_off m 4 6 hm2 hm3 (by decide) (by decide) (by decide) (by decide) (by decide))
  have t7 := hit 2 3 4 (by decide) (by decide) (by decide)
    (cop_off m 2 3 hm2 hm3 (by decide) (by decide) (by decide) (by decide) (by decide))
    (cop_off m 2 4 hm2 hm3 (by decide) (by decide) (by decide) (by decide) (by decide))
    (cop_off m 3 4 hm2 hm3 (by decide) (by decide) (by decide) (by decide) (by decide))
  have t8 := hit 2 3 6 (by decide) (by decide) (by decide)
    (cop_off m 2 3 hm2 hm3 (by decide) (by decide) (by decide) (by decide) (by decide))
    (cop_off m 2 6 hm2 hm3 (by decide) (by decide) (by decide) (by decide) (by decide))
    (cop_off m 3 6 hm2 hm3 (by decide) (by decide) (by decide) (by decide) (by decide))
  have t9 := hit 2 4 6 (by decide) (by decide) (by decide)
    (cop_off m 2 4 hm2 hm3 (by decide) (by decide) (by decide) (by decide) (by decide))
    (cop_off m 2 6 hm2 hm3 (by decide) (by decide) (by decide) (by decide) (by decide))
    (cop_off m 4 6 hm2 hm3 (by decide) (by decide) (by decide) (by decide) (by decide))
  have t10 := hit 3 4 6 (by decide) (by decide) (by decide)
    (cop_off m 3 4 hm2 hm3 (by decide) (by decide) (by decide) (by decide) (by decide))
    (cop_off m 3 6 hm2 hm3 (by decide) (by decide) (by decide) (by decide) (by decide))
    (cop_off m 4 6 hm2 hm3 (by decide) (by decide) (by decide) (by decide) (by decide))
  have t11 := hit 4 5 6 (by decide) (by decide) (by decide)
    (cop_off m 4 5 hm2 hm3 (by decide) (by decide) (by decide) (by decide) (by decide))
    (cop_off m 4 6 hm2 hm3 (by decide) (by decide) (by decide) (by decide) (by decide))
    (cop_off m 5 6 hm2 hm3 (by decide) (by decide) (by decide) (by decide) (by decide))
  have hc : N.card = (if ¬ D 0 then 1 else 0) + (if ¬ D 1 then 1 else 0) + (if ¬ D 2 then 1 else 0) + (if ¬ D 3 then 1 else 0) + (if ¬ D 4 then 1 else 0) + (if ¬ D 5 then 1 else 0) + (if ¬ D 6 then 1 else 0) := by
    rw [hN, card_filter]
    simp only [sum_range_succ, sum_range_zero, zero_add]
  rw [hc]
  have key := transversal_card (decide (¬ D 0)) (decide (¬ D 1)) (decide (¬ D 2)) (decide (¬ D 3))
    (decide (¬ D 4)) (decide (¬ D 5)) (decide (¬ D 6)) (by simpa using t0) (by simpa using t1) (by simpa using t2) (by simpa using t3) (by simpa using t4) (by simpa using t5) (by simpa using t6) (by simpa using t7) (by simpa using t8) (by simpa using t9) (by simpa using t10) (by simpa using t11)
  simpa using key

lemma sum_res_fiber (A : Finset ℕ) (Q : ℕ) (hQ : 0 < Q) :
    ∑ u ∈ range Q, (A.filter (fun y => y % Q = u % Q)).card = A.card := by
  classical
  symm
  rw [card_eq_sum_card_fiberwise (f := fun y => y % Q) (t := range Q)
    (fun y _ => by simp [Nat.mod_lt _ hQ])]
  refine sum_congr rfl (fun u hu => ?_)
  rw [Nat.mod_eq_of_lt (mem_range.1 hu)]

lemma sum_shift (A : Finset ℕ) (Q : ℕ) (hQ : 0 < Q) (c : ℕ) :
    ∑ u ∈ range Q, (A.filter (fun y => y % Q = (u + c) % Q)).card = A.card := by
  induction c with
  | zero => simpa using sum_res_fiber A Q hQ
  | succ c ih =>
    rw [← ih]
    set g : ℕ → ℕ := fun u => (A.filter (fun y => y % Q = (u + c) % Q)).card with hg
    have h1 := sum_range_succ' g Q
    have h2 := sum_range_succ g Q
    have h3 : g Q = g 0 := by
      simp only [hg, zero_add, Nat.add_mod_left]
    have h4 : ∀ u, (A.filter (fun y => y % Q = (u + (c + 1)) % Q)).card = g (u + 1) := by
      intro u
      simp only [hg]
      rw [show u + (c + 1) = u + 1 + c by ring]
    have h5 : ∑ u ∈ range Q, g (u + 1) = ∑ u ∈ range Q, g u := by
      have := h1.symm.trans h2
      rw [h3] at this
      exact Nat.add_right_cancel this
    rw [sum_congr rfl (fun u _ => h4 u)]
    exact h5

lemma sum_blocks (f : ℕ → ℕ) (q : ℕ) :
    ∑ u ∈ range (6 * q), f u = ∑ i ∈ range q, ∑ k ∈ range 6, f (6 * i + k) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show 6 * (q + 1) = 6 * q + 6 by ring, sum_range_add, ih,
      sum_range_succ (fun i => ∑ k ∈ range 6, f (6 * i + k)) q]

lemma sum_res (A : Finset ℕ) (q r : ℕ) (hq : 0 < q) (hr : r < 6) :
    ∑ i ∈ range q, (A.filter (fun y => y % (6 * q) = (6 * i + r) % (6 * q))).card =
      (A.filter (fun y => y % 6 = r)).card := by
  classical
  symm
  rw [card_eq_sum_card_fiberwise (f := fun y => y % (6 * q) / 6) (t := range q) ?_]
  · refine sum_congr rfl (fun i hi => ?_)
    have hi' := mem_range.1 hi
    rw [filter_filter]
    apply congrArg
    apply filter_congr
    intro y _
    have e1 : (6 * i + r) % (6 * q) = 6 * i + r := Nat.mod_eq_of_lt (by omega)
    have e2 : y % (6 * q) % 6 = y % 6 := Nat.mod_mul_right_mod y 6 q
    rw [e1]
    omega
  · intro y _
    simp only [coe_range, Set.mem_Iio]
    have := Nat.mod_lt y (by omega : 0 < 6 * q)
    omega

lemma window_sum (A : Finset ℕ) (q r : ℕ) (hq : 0 < q) (hr : r < 6) :
    ∑ i ∈ range q, ∑ k ∈ range 7, (A.filter (fun y => y % (6 * q) = (6 * i + r + k) % (6 * q))).card
      = (A.filter (fun y => y % 6 = r)).card + A.card := by
  have h1 : ∀ i, ∑ k ∈ range 7, (A.filter (fun y => y % (6 * q) = (6 * i + r + k) % (6 * q))).card =
      (A.filter (fun y => y % (6 * q) = (6 * i + r) % (6 * q))).card +
      ∑ k ∈ range 6, (A.filter (fun y => y % (6 * q) = ((6 * i + k) + (r + 1)) % (6 * q))).card := by
    intro i
    rw [sum_range_succ', add_comm]
    simp only [add_zero]
    congr 1
    refine sum_congr rfl (fun k _ => ?_)
    rw [show 6 * i + r + (k + 1) = 6 * i + k + (r + 1) by ring]
  rw [sum_congr rfl (fun i _ => h1 i), sum_add_distrib, sum_res A q r hq hr]
  congr 1
  rw [← sum_blocks (fun u => (A.filter (fun y => y % (6 * q) = (u + (r + 1)) % (6 * q))).card) q]
  exact sum_shift A (6 * q) (by omega) (r + 1)

theorem windows (A : Finset ℕ) (n q Q r : ℕ) (hA : A ⊆ Icc 1 n) (hq : 0 < q) (hQ : Q = 6 * q)
    (hr : r = 1 ∨ r = 5) (β : ℝ) (hβ1 : β ≤ 1)
    (htot : (q : ℝ) * (4 * ((n : ℝ) / Q + 1) + 3 * (β * ((n : ℝ) / Q))) <
      ((A.filter (fun y => y % 6 = r)).card : ℝ) + A.card) :
    ∃ m a b c, m % 2 = 1 ∧ m % 3 ≠ 0 ∧ a < b ∧ b < c ∧ c < 7 ∧
      β * ((n : ℝ) / Q) < ((A.filter (fun y => y % Q = (m + a) % Q)).card : ℝ) ∧
      β * ((n : ℝ) / Q) < ((A.filter (fun y => y % Q = (m + b) % Q)).card : ℝ) ∧
      β * ((n : ℝ) / Q) < ((A.filter (fun y => y % Q = (m + c) % Q)).card : ℝ) ∧
      Nat.Coprime (m + a) (m + b) ∧ Nat.Coprime (m + a) (m + c) ∧ Nat.Coprime (m + b) (m + c) := by
  classical
  by_contra hcon
  set B : ℝ := (n : ℝ) / Q with hB
  have hQ0 : 0 < Q := by omega
  have hB0 : 0 ≤ B := by positivity
  have ha : ∀ u, ((A.filter (fun y => y % Q = u % Q)).card : ℝ) ≤ B + 1 := by
    intro u
    have h1 : A.filter (fun y => y % Q = u % Q) ⊆ cls n Q u := by
      intro y hy
      rw [mem_filter] at hy
      have := mem_Icc.1 (hA hy.1)
      exact mem_cls.2 ⟨this.1, this.2, hy.2⟩
    have h2 := (card_le_card h1).trans (card_cls_le n Q u hQ0)
    have h3 : ((n / Q : ℕ) : ℝ) ≤ B := by
      rw [hB]; exact Nat.cast_div_le
    have : ((A.filter (fun y => y % Q = u % Q)).card : ℝ) ≤ ((n / Q : ℕ) : ℝ) + 1 := by
      exact_mod_cast h2
    linarith
  have hwin : ∀ i ∈ range q, (∑ k ∈ range 7,
      ((A.filter (fun y => y % Q = (6 * i + r + k) % Q)).card : ℝ)) ≤ 4 * (B + 1) + 3 * (β * B) := by
    intro i _
    set m := 6 * i + r with hm
    have hm2 : m % 2 = 1 := by omega
    have hm3 : m % 3 ≠ 0 := by omega
    have h3 := window m hm2 hm3 (fun k => β * B < ((A.filter (fun y => y % Q = (m + k) % Q)).card : ℝ))
      (by
        rintro ⟨a', b', c', h1, h2, h3, d1, d2, d3, c1, c2, c3⟩
        exact hcon ⟨m, a', b', c', hm2, hm3, h1, h2, h3, d1, d2, d3, c1, c2, c3⟩)
    set N := (range 7).filter
      (fun k => ¬ (β * B < ((A.filter (fun y => y % Q = (m + k) % Q)).card : ℝ))) with hN
    have hb : ∀ k ∈ range 7, ((A.filter (fun y => y % Q = (m + k) % Q)).card : ℝ) ≤
        (B + 1) - (if k ∈ N then (B + 1 - β * B) else 0) := by
      intro k hk
      by_cases hkN : k ∈ N
      · rw [if_pos hkN]
        have := (mem_filter.1 hkN).2
        push Not at this
        linarith
      · rw [if_neg hkN]; linarith [ha (m + k)]
    have hs := sum_le_sum hb
    rw [sum_sub_distrib, sum_ite_mem, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul,
      inter_eq_right.2 (filter_subset _ _), card_range] at hs
    have hN3 : (3 : ℝ) ≤ N.card := by exact_mod_cast h3
    have hpos : 0 ≤ B + 1 - β * B := by nlinarith
    push_cast at hs
    nlinarith
  have hsum := sum_le_sum hwin
  rw [sum_const, card_range, nsmul_eq_mul] at hsum
  have hid := window_sum A q r hq (by omega)
  rw [← hQ] at hid
  have hid' : (∑ i ∈ range q, ∑ k ∈ range 7,
      ((A.filter (fun y => y % Q = (6 * i + r + k) % Q)).card : ℝ)) =
      ((A.filter (fun y => y % 6 = r)).card : ℝ) + A.card := by exact_mod_cast hid
  linarith

lemma not_dvd_both {a b p : ℕ} (h : Nat.Coprime a b) (hp : p.Prime) (ha : p ∣ a) (hb : p ∣ b) :
    False := (Nat.Prime.coprime_iff_not_dvd hp).1 (Nat.Coprime.coprime_dvd_left ha h) hb

theorem case2 (l n R r : ℕ) (A : Finset ℕ) (ε : ℝ) (hA : A ⊆ Icc 1 n) (hl : 1 ≤ l) (hR5 : 5 ≤ R)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hRl : 512 * (l : ℝ) ≤ ε ^ 2 * (R + 1))
    (hr : r = 1 ∨ r = 5)
    (htot : ((primorial R / 6 : ℕ) : ℝ) * (4 * ((n : ℝ) / primorial R + 1) +
      3 * (ε / 2 * ((n : ℝ) / primorial R))) < ((A.filter (fun y => y % 6 = r)).card : ℝ) + A.card)
    (hN2 : 1 + Real.log n ≤ ε ^ 2 * ((n : ℝ) / primorial R) / 32)
    (hN3 : (Nat.log 2 n : ℝ) ≤ ε / 8 * ((n : ℝ) / primorial R))
    (hN4 : 8 * (l : ℝ) ≤ ε * ((n : ℝ) / primorial R))
    (hN5 : 256 * (l : ℝ) * (n + 1) ≤ ε ^ 2 * ((n : ℝ) / primorial R) ^ 2) :
    (completeMultipartiteGraph (fun i : Fin 3 ↦ Fin (![1, l, l] i))).IsContained
      (coprimeGraph.induce (A : Set ℕ)) := by
  classical
  set Q := primorial R with hQdef
  have hQ : 0 < Q := primorial_pos R
  have hRQ : ∀ p, p.Prime → p ≤ R → p ∣ Q := fun p hp h => dvd_primorial_of_le hp h
  have hQR : ∀ p, p.Prime → p ∣ Q → p ≤ R := fun p hp h => le_of_dvd_primorial hp h
  have h6 : 6 ∣ Q := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num)
    (hRQ 2 Nat.prime_two (by omega)) (hRQ 3 Nat.prime_three (by omega))
  have h30 : 30 ∣ Q := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h6
    (hRQ 5 (by norm_num) (by omega))
  have hQ30 : 30 ≤ Q := Nat.le_of_dvd hQ h30
  set q := Q / 6 with hqdef
  have hqQ : Q = 6 * q := (Nat.mul_div_cancel' h6).symm
  have hq : 0 < q := by omega
  obtain ⟨m, a, b, c, hm2, hm3, hab, hbc, hc7, d1, d2, d3, c1, c2, c3⟩ :=
    windows A n q Q r hA hq hqQ hr (ε / 2) (by linarith) htot
  set B : ℝ := (n : ℝ) / Q with hB
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hBpos : 0 < B := by
    by_contra h
    push Not at h
    nlinarith
  have hdist : ∀ a b, a < b → b < 7 → (m + a) % Q ≠ (m + b) % Q := by
    intro a b hab hb h
    have h1 : Q ∣ (m + b) - (m + a) := Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h.symm)
    rw [show m + b - (m + a) = b - a by omega] at h1
    have := Nat.le_of_dvd (by omega) h1
    omega
  set η : ℝ := ε / 8 with hη
  have hM := markov n Q R (m + a) η (by positivity) hQ hQR
  have hR1 : (0 : ℝ) < R + 1 := by positivity
  have hR' : 2 / ((R : ℝ) + 1) ≤ ε ^ 2 / 256 := by
    rw [div_le_iff₀ hR1]
    nlinarith
  have hex : ∃ x ∈ A.filter (fun y => y % Q = (m + a) % Q), ¬ (η < wt R x) := by
    by_contra hno
    push Not at hno
    have hsub : A.filter (fun y => y % Q = (m + a) % Q) ⊆
        (cls n Q (m + a)).filter (fun x => η < wt R x) := by
      intro y hy
      have hy' := mem_filter.1 hy
      have := mem_Icc.1 (hA hy'.1)
      exact mem_filter.2 ⟨mem_cls.2 ⟨this.1, this.2, hy'.2⟩, hno y hy⟩
    have hc : ((A.filter (fun y => y % Q = (m + a) % Q)).card : ℝ) ≤
        (((cls n Q (m + a)).filter (fun x => η < wt R x)).card : ℝ) := by
      exact_mod_cast card_le_card hsub
    have hη0 : 0 < η := by positivity
    have e1 : η * (ε / 2 * B) < η * ((A.filter (fun y => y % Q = (m + a) % Q)).card : ℝ) :=
      mul_lt_mul_of_pos_left d1 hη0
    have e2 := mul_le_mul_of_nonneg_left hc hη0.le
    have e3 : B * (2 / ((R : ℝ) + 1)) ≤ B * (ε ^ 2 / 256) := mul_le_mul_of_nonneg_left hR' hBpos.le
    rw [hη] at e1 e2
    nlinarith
  obtain ⟨x, hx, hxw⟩ := hex
  push Not at hxw
  have hx' := mem_filter.1 hx
  have hxI := mem_Icc.1 (hA hx'.1)
  have hx0 : x ≠ 0 := by omega
  have hω : (x.primeFactors.card : ℝ) ≤ Nat.log 2 n := by
    have := (card_primeFactors_le_log x hx0).trans (Nat.log_mono_right hxI.2)
    exact_mod_cast this
  refine core l n Q R x (m + b) (m + c) A (ε / 2) (ε / 4 * B) hA hQ hRQ hQR hx'.1 hx0
    ?_ ?_ ?_ ?_ ?_ ?_ d2.le d3.le ?_ ?_ ?_
  · intro p hp hpQ ⟨hpx, hpb⟩
    exact not_dvd_both c1 hp (dvd_of_mod_eq hpQ hx'.2 hpx) hpb
  · intro p hp hpQ ⟨hpx, hpc⟩
    exact not_dvd_both c2 hp (dvd_of_mod_eq hpQ hx'.2 hpx) hpc
  · intro p hp _ ⟨hpb, hpc⟩
    exact not_dvd_both c3 hp hpb hpc
  · rw [hx'.2]; exact hdist a b hab (by omega)
  · rw [hx'.2]; exact hdist a c (by omega) hc7
  · exact hdist b c hbc hc7
  · have : B * wt R x ≤ B * η := mul_le_mul_of_nonneg_left hxw hBpos.le
    have hηe : η = ε / 8 := rfl
    rw [hηe] at this hN3
    linarith [hω]
  · linarith
  · have h1 : 2 / ((R : ℝ) + 1) * (512 * l) ≤ 2 * ε ^ 2 := by
      calc 2 / ((R : ℝ) + 1) * (512 * l) ≤ 2 / ((R : ℝ) + 1) * (ε ^ 2 * (R + 1)) :=
            mul_le_mul_of_nonneg_left hRl (by positivity)
        _ = 2 * ε ^ 2 := by field_simp
    have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg B)
    have e1 : 4 * (l : ℝ) * (2 * B ^ 2 * (2 / ((R : ℝ) + 1))) ≤ ε ^ 2 * B ^ 2 / 32 := by
      calc 4 * (l : ℝ) * (2 * B ^ 2 * (2 / ((R : ℝ) + 1)))
          = B ^ 2 * (2 / ((R : ℝ) + 1) * (512 * l)) / 64 := by ring
        _ ≤ B ^ 2 * (2 * ε ^ 2) / 64 := by linarith
        _ = ε ^ 2 * B ^ 2 / 32 := by ring
    have e2 : 4 * (l : ℝ) * (2 * ((n : ℝ) + 1)) ≤ ε ^ 2 * B ^ 2 / 32 := by linarith
    calc 4 * (l : ℝ) * (2 * B ^ 2 * (2 / ((R : ℝ) + 1)) + 2 * ((n : ℝ) + 1))
        = 4 * (l : ℝ) * (2 * B ^ 2 * (2 / ((R : ℝ) + 1))) + 4 * (l : ℝ) * (2 * ((n : ℝ) + 1)) := by
          ring
      _ ≤ ε ^ 2 * B ^ 2 / 32 + ε ^ 2 * B ^ 2 / 32 := add_le_add e1 e2
      _ = (ε / 4 * B) ^ 2 := by ring


lemma card_S (n : ℕ) :
    ((Icc 1 n).filter (fun y => 2 ∣ y ∨ 3 ∣ y)).card = n / 2 + n / 3 - n / 6 := by
  classical
  have h2 := Nat.Ioc_filter_dvd_card_eq_div n 2
  have h3 := Nat.Ioc_filter_dvd_card_eq_div n 3
  have h6 := Nat.Ioc_filter_dvd_card_eq_div n 6
  have e : Icc 1 n = Ioc 0 n := by ext; simp; omega
  rw [e, filter_or]
  have hi : (Ioc 0 n).filter (fun y => 2 ∣ y) ∩ (Ioc 0 n).filter (fun y => 3 ∣ y) =
      (Ioc 0 n).filter (fun y => 6 ∣ y) := by
    rw [← filter_and]
    apply filter_congr
    intro y _
    constructor
    · rintro ⟨a, b⟩; exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) a b
    · intro h; exact ⟨dvd_trans (by norm_num) h, dvd_trans (by norm_num) h⟩
  have := card_union_add_card_inter ((Ioc 0 n).filter (fun y => 2 ∣ y))
    ((Ioc 0 n).filter (fun y => 3 ∣ y))
  rw [hi, h2, h3, h6] at this
  have h7 : ((Ioc 0 n).filter (fun y => 2 ∣ y) ∪ (Ioc 0 n).filter (fun y => 3 ∣ y)).card =
      n / 2 + n / 3 - n / 6 := by omega
  exact h7

lemma fiber_sum (Q d : ℕ) (hQ : 0 < Q) (hd : 0 < d) (hdQ : d ∣ Q) (M U : Finset ℕ)
    (hU : U ⊆ range Q) :
    ∑ u ∈ U, (M.filter (fun y => y % Q = (d * u) % Q)).card ≤ d * M.card := by
  classical
  calc ∑ u ∈ U, (M.filter (fun y => y % Q = (d * u) % Q)).card
      = ∑ y ∈ M, (U.filter (fun u => y % Q = (d * u) % Q)).card := by
        simp only [card_filter]; exact sum_comm
    _ ≤ ∑ y ∈ M, d := by
        apply sum_le_sum
        intro y _
        calc (U.filter (fun u => y % Q = (d * u) % Q)).card
            ≤ ((range Q).filter (fun u => (d * u) % Q = y % Q)).card := by
              apply card_le_card
              intro u hu
              rw [mem_filter] at hu ⊢
              exact ⟨hU hu.1, hu.2.symm⟩
          _ ≤ d := fiber_mul_le Q (y % Q) d hd hdQ hQ
    _ = d * M.card := by rw [sum_const, smul_eq_mul, mul_comm]


lemma num_aux (Q2 E l T : ℝ) (hQ : 1 ≤ Q2) (hE : 1 ≤ E) (hl : 1 ≤ l)
    (hX : 10 ^ 4 * Q2 ^ 2 * E ^ 2 * l ≤ T) :
    512 * l * E ^ 2 * Q2 ^ 2 ≤ T ∧ 416 * E ^ 2 * Q2 ≤ T ∧ 96 * E * Q2 ≤ T ∧
      8 * l * E * Q2 ≤ T ∧ E * (1 + 3 * Q2) ≤ 96 * E * Q2 := by
  have h1 : 0 ≤ l * E ^ 2 * Q2 ^ 2 := by positivity
  have h2 : 512 * l * E ^ 2 * Q2 ^ 2 ≤ T := by nlinarith
  have h3 : Q2 ≤ Q2 ^ 2 * l := by nlinarith
  have h4 : 416 * E ^ 2 * Q2 ≤ T := by
    have b2 := mul_le_mul_of_nonneg_left h3 (sq_nonneg E)
    nlinarith
  have h5 : E ≤ E ^ 2 := by nlinarith
  have h6 : 96 * E * Q2 ≤ T := by
    have := mul_le_mul_of_nonneg_right h5 (by positivity : (0 : ℝ) ≤ Q2)
    nlinarith
  have h7 : 8 * l * E * Q2 ≤ T := by
    have e1 : 1 ≤ E * Q2 := by nlinarith
    have e2 : 0 ≤ 8 * l * E * Q2 := by positivity
    nlinarith
  have h8 : E * (1 + 3 * Q2) ≤ 96 * E * Q2 := by nlinarith
  exact ⟨h2, h4, h6, h7, h8⟩

lemma cls_split (n Q j d : ℕ) (A : Finset ℕ) (hdQ : d ∣ Q) (hdj : d ∣ j) (hd : d = 2 ∨ d = 3) :
    (cls n Q j).card ≤ (A.filter (fun y => y % Q = j % Q)).card +
      (((Icc 1 n).filter (fun y => (2 ∣ y ∨ 3 ∣ y) ∧ y ∉ A)).filter
        (fun y => y % Q = j % Q)).card := by
  classical
  have h := card_filter_add_card_filter_not (s := cls n Q j) (fun y => y ∈ A)
  have h1 : (cls n Q j).filter (fun y => y ∈ A) ⊆ A.filter (fun y => y % Q = j % Q) := by
    intro y hy
    rw [mem_filter] at hy ⊢
    exact ⟨hy.2, (mem_cls.1 hy.1).2.2⟩
  have h2 : (cls n Q j).filter (fun y => y ∉ A) ⊆
      ((Icc 1 n).filter (fun y => (2 ∣ y ∨ 3 ∣ y) ∧ y ∉ A)).filter (fun y => y % Q = j % Q) := by
    intro y hy
    rw [mem_filter] at hy
    have hy' := mem_cls.1 hy.1
    have hdy : d ∣ y := dvd_of_mod_eq hdQ hy'.2.2.symm hdj
    rw [mem_filter, mem_filter, mem_Icc]
    refine ⟨⟨⟨hy'.1, hy'.2.1⟩, ?_, hy.2⟩, hy'.2.2⟩
    rcases hd with rfl | rfl
    · exact Or.inl hdy
    · exact Or.inr hdy
  have := card_le_card h1
  have := card_le_card h2
  omega

lemma cls_dense (B c a D φ m Q n : ℝ) (hQ : 0 < Q) (hφ : 0 < φ) (hB : B = n / Q)
    (hc : B - 1 ≤ c) (hsplit : c ≤ a + D) (hD : D * φ ≤ 5 * m) (hM : 10 * m * Q ≤ φ * (n - 2 * Q)) :
    B / 2 ≤ a := by
  have hn : n = B * Q := by rw [hB]; field_simp
  have h1 : φ * (D * (2 * Q)) ≤ φ * (n - 2 * Q) := by nlinarith
  have h2 : D * (2 * Q) ≤ n - 2 * Q := le_of_mul_le_mul_left h1 hφ
  rw [hn] at h2
  have h3 : (2 * D - B + 2) * Q ≤ 0 := by nlinarith
  have h4 : 2 * D - B + 2 ≤ 0 := by
    by_contra h
    push Not at h
    nlinarith
  linarith

lemma mbound (m Q φ L n : ℝ) (hm : 0 ≤ m) (hQ : 0 ≤ Q) (hφ : 0 ≤ φ) (hn2Q : 2 * Q ≤ n)
    (hW : Q ^ 2 ≤ 3 * L * φ ^ 2) (h300 : 300 * L * m ^ 2 ≤ (n - 2 * Q) ^ 2) :
    10 * m * Q ≤ φ * (n - 2 * Q) := by
  have h1 : (10 * m * Q) ^ 2 ≤ (φ * (n - 2 * Q)) ^ 2 := by
    have a1 : (10 * m * Q) ^ 2 = 100 * m ^ 2 * Q ^ 2 := by ring
    have a2 : (φ * (n - 2 * Q)) ^ 2 = φ ^ 2 * (n - 2 * Q) ^ 2 := by ring
    rw [a1, a2]
    have b1 : 100 * m ^ 2 * Q ^ 2 ≤ 100 * m ^ 2 * (3 * L * φ ^ 2) :=
      mul_le_mul_of_nonneg_left hW (by positivity)
    have b2 : φ ^ 2 * (300 * L * m ^ 2) ≤ φ ^ 2 * (n - 2 * Q) ^ 2 :=
      mul_le_mul_of_nonneg_left h300 (by positivity)
    nlinarith
  exact (sq_le_sq₀ (by positivity) (by nlinarith)).1 h1

lemma h300a (m n Q R0 E K : ℝ) (hm0 : 0 ≤ m) (hm : m ≤ n / E) (hE : E = 64 * K) (hR0 : R0 = K ^ 2)
    (hK : 0 < K) (h4Q : 4 * Q ≤ n) (hQ : 0 ≤ Q) : 300 * R0 * m ^ 2 ≤ (n - 2 * Q) ^ 2 := by
  have hE0 : 0 < E := by rw [hE]; positivity
  have h1 : m * E ≤ n := by rwa [le_div_iff₀ hE0] at hm
  have h2 : (m * E) ^ 2 ≤ n ^ 2 := by
    have : 0 ≤ m * E := by positivity
    nlinarith
  have h3 : (m * E) ^ 2 = 4096 * (K ^ 2 * m ^ 2) := by rw [hE]; ring
  have h4 : n / 2 ≤ n - 2 * Q := by linarith
  have h5 : (n / 2) ^ 2 ≤ (n - 2 * Q) ^ 2 := by
    have : 0 ≤ n / 2 := by linarith
    nlinarith
  rw [hR0]
  nlinarith

lemma h300b (m n Q L T : ℝ) (hm0 : 0 ≤ m) (hm : m ≤ 16 * n / L + 56 + 48 * T)
    (hL : 4000000 ≤ L) (hLT : L ≤ T) (hT : 400 ≤ T) (hTn : T ^ 3 ≤ n) (hQT : Q ≤ T) (hQ0 : 0 ≤ Q) :
    300 * L * m ^ 2 ≤ (n - 2 * Q) ^ 2 := by
  have hL0 : 0 < L := by linarith
  have hT0 : 0 < T := by linarith
  set a := 16 * n / L with ha
  set b := 56 + 48 * T with hb
  have ha0 : 0 ≤ a := by
    have : 0 ≤ n := le_trans (by positivity) hTn
    positivity
  have hb0 : 0 ≤ b := by positivity
  have h1 : m ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by nlinarith [sq_nonneg (a - b)]
  have hn0 : 0 ≤ n := le_trans (by positivity) hTn
  have h2 : 300 * L * (2 * a ^ 2) ≤ 153600 * n ^ 2 / 4000000 := by
    have e : 300 * L * (2 * a ^ 2) = 153600 * n ^ 2 / L := by rw [ha]; field_simp; ring
    rw [e]
    exact div_le_div_of_nonneg_left (by positivity) (by norm_num) hL
  have hbT : b ≤ 104 * T := by rw [hb]; linarith
  have h3 : 300 * L * (2 * b ^ 2) ≤ 600 * T * (104 * T) ^ 2 := by
    have : b ^ 2 ≤ (104 * T) ^ 2 := by nlinarith
    have : 600 * L * b ^ 2 ≤ 600 * T * b ^ 2 := by
      have : 0 ≤ b ^ 2 := sq_nonneg b
      nlinarith
    nlinarith
  have hT3 : 64000000 ≤ T ^ 3 := by nlinarith
  have h4 : 600 * T * (104 * T) ^ 2 ≤ n ^ 2 / 8 := by
    have e : 600 * T * (104 * T) ^ 2 = 6489600 * T ^ 3 := by ring
    rw [e]
    have : 64000000 * T ^ 3 ≤ n * n := by
      have := mul_le_mul hTn hTn (by positivity) hn0
      nlinarith
    nlinarith
  have h5 : n / 2 ≤ n - 2 * Q := by nlinarith
  have h6 : (n / 2) ^ 2 ≤ (n - 2 * Q) ^ 2 := by
    have : 0 ≤ n / 2 := by linarith
    nlinarith
  have h7 : 300 * L * m ^ 2 ≤ 300 * L * (2 * a ^ 2 + 2 * b ^ 2) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  nlinarith

lemma hC_aux (n Q T l lg : ℝ) (hQ0 : 0 < Q) (hQT : Q ≤ T) (hTn : T ^ 3 ≤ n) (hT : 512 * l ≤ T)
    (hT64 : 64 ≤ T) (hl : 1 ≤ l) (hlg : lg ≤ 6 * T + 6) :
    lg ≤ n / Q / 8 ∧ 8 * l ≤ n / Q ∧ 256 * l * (n + 1) ≤ (n / Q) ^ 2 := by
  have hT0 : 0 < T := by linarith
  have hn0 : 0 < n := lt_of_lt_of_le (by positivity) hTn
  have h1 : n / T ≤ n / Q := div_le_div_of_nonneg_left hn0.le hQ0 hQT
  have h2 : T ^ 2 ≤ n / T := by
    rw [le_div_iff₀ hT0]; nlinarith
  have hB : T ^ 2 ≤ n / Q := le_trans h2 h1
  refine ⟨?_, ?_, ?_⟩
  · have : 6 * T + 6 ≤ T ^ 2 / 8 := by nlinarith
    linarith
  · nlinarith
  · have hB0 : 0 ≤ n / T := by positivity
    have h3 : (n / T) ^ 2 ≤ (n / Q) ^ 2 := by nlinarith
    have h4 : n * T ≤ (n / T) ^ 2 := by
      have e : (n / T) ^ 2 = n * (n / T ^ 2) := by field_simp
      rw [e]
      have : T ≤ n / T ^ 2 := by rw [le_div_iff₀ (by positivity)]; nlinarith
      nlinarith
    have hn1 : 1 ≤ n := by nlinarith
    nlinarith

set_option maxHeartbeats 4000000 in
theorem main_thm (l : ℕ) (hl : 1 ≤ l) : ∀ᶠ n : ℕ in Filter.atTop, ∀ A : Finset ℕ,
      A ⊆ Finset.Icc 1 n →
      n / 2 + n / 3 - n / 6 < A.card →
      (SimpleGraph.completeMultipartiteGraph (fun i : Fin 3 ↦ Fin (![1, l, l] i))).IsContained
        (coprimeGraph.induce (A : Set ℕ)) := by
  classical
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = 2000 * l := ⟨_, rfl⟩
  obtain ⟨R0, hR0⟩ : ∃ R0 : ℕ, R0 = K ^ 2 := ⟨_, rfl⟩
  obtain ⟨R2, hR2⟩ : ∃ R2 : ℕ, R2 = 2 ^ 21 * l * K ^ 2 := ⟨_, rfl⟩
  obtain ⟨Q2, hQ2⟩ : ∃ Q2 : ℕ, Q2 = primorial R2 := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : ℕ, E = 64 * K := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℕ, C = 2 ^ 48 + R0 + 10 ^ 4 * Q2 ^ 2 * E ^ 2 * l := ⟨_, rfl⟩
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = 1 / (E : ℝ) := ⟨_, rfl⟩
  rw [Filter.eventually_atTop]
  refine ⟨64 ^ C, fun n hn A hA hcard => ?_⟩
  have hK1 : 2000 ≤ K := by omega
  have hR0K : 4000000 ≤ R0 := by rw [hR0]; nlinarith
  have hR0l : 512 * l ≤ R0 := by rw [hR0, hK]; nlinarith
  have hQ2pos : 0 < Q2 := hQ2 ▸ primorial_pos R2
  have hE1 : 1 ≤ E := by omega
  obtain ⟨R, hRdef⟩ : ∃ R, R = Nat.log 64 n := ⟨_, rfl⟩
  have hn0 : n ≠ 0 := by
    have : 0 < 64 ^ C := by positivity
    omega
  have hRC : C ≤ R := hRdef ▸ Nat.le_log_of_pow_le (by norm_num) hn
  have hpowR : 64 ^ R ≤ n := hRdef ▸ Nat.pow_log_le_self 64 hn0
  have hnR : n < 64 ^ (R + 1) := hRdef ▸ Nat.lt_pow_succ_log_self (by norm_num) n
  obtain ⟨T, hT⟩ : ∃ T, T = 4 ^ R := ⟨_, rfl⟩
  have hT3 : T ^ 3 = 64 ^ R := by rw [hT, ← pow_mul, mul_comm, pow_mul]; norm_num
  have hRT : R ≤ T := hT ▸ (Nat.lt_pow_self (by norm_num)).le
  have hCT : C ≤ T := hRC.trans hRT
  have hTn : T ^ 3 ≤ n := hT3 ▸ hpowR
  have hTr : (T : ℝ) ^ 3 ≤ n := by exact_mod_cast hTn
  have hCr : (C : ℝ) ≤ T := by exact_mod_cast hCT
  have hlog2 : (Nat.log 2 n : ℝ) ≤ 6 * T + 6 := by
    have h1 : n < 2 ^ (6 * R + 6) := by
      calc n < 64 ^ (R + 1) := hnR
        _ = 2 ^ (6 * R + 6) := by rw [show (64 : ℕ) = 2 ^ 6 by norm_num, ← pow_mul]; ring_nf
    have h2 := Nat.log_lt_of_lt_pow hn0 h1
    have : Nat.log 2 n ≤ 6 * T + 6 := by omega
    exact_mod_cast this
  have hlog : Real.log n ≤ 6 * T + 6 := by
    have h1 : (n : ℝ) ≤ 2 ^ (6 * R + 6) := by
      have : n ≤ 2 ^ (6 * R + 6) := by
        have := hnR
        rw [show (64 : ℕ) = 2 ^ 6 by norm_num, ← pow_mul] at this
        have e : 6 * (R + 1) = 6 * R + 6 := by ring
        rw [e] at this; omega
      exact_mod_cast this
    have h2 : Real.log n ≤ Real.log (2 ^ (6 * R + 6)) :=
      Real.log_le_log (by positivity) h1
    rw [Real.log_pow] at h2
    have h3 := Real.log_two_lt_d9
    have h4 : (R : ℝ) ≤ T := by exact_mod_cast hRT
    push_cast at h2
    nlinarith
  -- basic real facts
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hQ21 : (1 : ℝ) ≤ Q2 := by exact_mod_cast hQ2pos
  have hE1r : (1 : ℝ) ≤ E := by exact_mod_cast hE1
  have hX : (10 ^ 4 * (Q2 : ℝ) ^ 2 * (E : ℝ) ^ 2 * l) ≤ T := by
    have : 10 ^ 4 * Q2 ^ 2 * E ^ 2 * l ≤ T := by omega
    exact_mod_cast this
  have hT48 : (2 : ℝ) ^ 48 ≤ T := by
    have : 2 ^ 48 ≤ T := by omega
    exact_mod_cast this
  have hT1 : (1 : ℝ) ≤ T := by linarith [show (1:ℝ) ≤ 2 ^ 48 by norm_num]
  have hT2 : (1 : ℝ) ≤ (T : ℝ) ^ 2 := by nlinarith
  have hTT3 : (T : ℝ) ≤ (T : ℝ) ^ 3 := by nlinarith
  have hnT : (T : ℝ) ≤ n := le_trans hTT3 hTr
  have hn2 : (T : ℝ) ^ 2 * T ≤ n := by
    have : (T : ℝ) ^ 2 * T = T ^ 3 := by ring
    rw [this]; exact hTr
  have hTTn : (T : ℝ) * T ≤ n := by
    have : (T : ℝ) * T ≤ T ^ 2 * T := by nlinarith
    linarith
  -- the sets
  set S := (Icc 1 n).filter (fun y => 2 ∣ y ∨ 3 ∣ y) with hS
  set M := (Icc 1 n).filter (fun y => (2 ∣ y ∨ 3 ∣ y) ∧ y ∉ A) with hM
  set sT := A.filter (fun y => ¬ 2 ∣ y ∧ ¬ 3 ∣ y) with hsT
  have hMs : M.card < sT.card := by
    have h1 := card_filter_add_card_filter_not (s := A) (fun y => 2 ∣ y ∨ 3 ∣ y)
    have h2 := card_filter_add_card_filter_not (s := S) (fun y => y ∈ A)
    have e1 : S.filter (fun y => y ∈ A) = A.filter (fun y => 2 ∣ y ∨ 3 ∣ y) := by
      ext y
      simp only [hS, mem_filter]
      constructor
      · rintro ⟨⟨_, h⟩, hy⟩; exact ⟨hy, h⟩
      · rintro ⟨hy, h⟩; exact ⟨⟨hA hy, h⟩, hy⟩
    have e2 : S.filter (fun y => y ∉ A) = M := by rw [hS, hM, filter_filter]
    have e3 : A.filter (fun y => ¬ (2 ∣ y ∨ 3 ∣ y)) = sT := by
      rw [hsT]; apply filter_congr; intro y _; tauto
    rw [e1, e2] at h2
    rw [e3] at h1
    have h3 := card_S n
    rw [← hS] at h3
    omega
  by_cases hcase : ε * n ≤ sT.card
  · -- dense case
    have hs15 : sT.card ≤ (A.filter (fun y => y % 6 = 1)).card +
        (A.filter (fun y => y % 6 = 5)).card := by
      calc sT.card ≤ (A.filter (fun y => y % 6 = 1) ∪ A.filter (fun y => y % 6 = 5)).card := by
            apply card_le_card
            intro y hy
            rw [hsT, mem_filter] at hy
            rcases hy with ⟨hyA, h2, h3⟩
            have : y % 6 = 1 ∨ y % 6 = 5 := by omega
            rw [mem_union, mem_filter, mem_filter]
            rcases this with h | h
            · exact Or.inl ⟨hyA, h⟩
            · exact Or.inr ⟨hyA, h⟩
        _ ≤ _ := card_union_le _ _
    obtain ⟨r, hr, hsr⟩ : ∃ r, (r = 1 ∨ r = 5) ∧
        (sT.card : ℝ) ≤ 2 * (A.filter (fun y => y % 6 = r)).card := by
      by_cases h : (A.filter (fun y => y % 6 = 5)).card ≤ (A.filter (fun y => y % 6 = 1)).card
      · refine ⟨1, Or.inl rfl, ?_⟩
        have : sT.card ≤ 2 * (A.filter (fun y => y % 6 = 1)).card := by omega
        exact_mod_cast this
      · refine ⟨5, Or.inr rfl, ?_⟩
        have : sT.card ≤ 2 * (A.filter (fun y => y % 6 = 5)).card := by omega
        exact_mod_cast this
    have hR25 : 5 ≤ R2 := by rw [hR2]; nlinarith
    have hεpos : 0 < ε := by rw [hε]; positivity
    have hε1 : ε ≤ 1 := by rw [hε, div_le_one (by positivity)]; exact hE1r
    have hεE : ε * E = 1 := by rw [hε]; field_simp
    have hK0 : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
    obtain ⟨hbig, hbig2, hbig3, hbig4, hbig5⟩ := num_aux Q2 E l T hQ21 hE1r hl1 hX
    have hQ2r : (0 : ℝ) < Q2 := by positivity
    have hEr : (0 : ℝ) < E := by positivity
    rw [hQ2] at hQ2r hbig hbig2 hbig3 hbig4 hbig5
    refine case2 l n R2 r A ε hA hl hR25 hεpos hε1 ?_ hr ?_ ?_ ?_ ?_ ?_
    · have e : ε ^ 2 * (R2 : ℝ) = 512 * l := by
        rw [hε, hR2, hE]; push_cast; field_simp; ring
      nlinarith [sq_nonneg ε]
    · -- htot
      have h6 : 6 ∣ primorial R2 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num)
        (dvd_primorial_of_le Nat.prime_two (by omega))
        (dvd_primorial_of_le Nat.prime_three (by omega))
      have hq : ((primorial R2 / 6 : ℕ) : ℝ) = (primorial R2 : ℝ) / 6 := by
        rw [Nat.cast_div h6 (by norm_num)]; norm_num
      rw [hq]
      have hf : (4 * (n : ℝ) - 7) / 6 ≤ ((n / 2 + n / 3 - n / 6 : ℕ) : ℝ) := by
        have : 4 * n ≤ 6 * (n / 2 + n / 3 - n / 6) + 7 := by omega
        have : (4 * n : ℝ) ≤ 6 * ((n / 2 + n / 3 - n / 6 : ℕ) : ℝ) + 7 := by exact_mod_cast this
        linarith
      have hA1 : ((n / 2 + n / 3 - n / 6 : ℕ) : ℝ) + 1 ≤ A.card := by exact_mod_cast hcard
      have e : (primorial R2 : ℝ) / 6 * (4 * ((n : ℝ) / primorial R2 + 1) +
          3 * (ε / 2 * ((n : ℝ) / primorial R2))) =
          2 * n / 3 + 2 * (primorial R2 : ℝ) / 3 + ε * n / 4 := by
        field_simp; ring
      rw [e]
      have hD1 : 1 + 3 * (primorial R2 : ℝ) < ε * n := by
        have h1 : (E : ℝ) * (1 + 3 * primorial R2) ≤ T := le_trans hbig5 hbig3
        have h2 : (E : ℝ) * (1 + 3 * primorial R2) < n := by
          have : (T : ℝ) < n := by
            have : (T : ℝ) < T ^ 2 * T := by nlinarith
            linarith
          linarith
        have h3 : ε * (E * (1 + 3 * primorial R2)) < ε * n := mul_lt_mul_of_pos_left h2 hεpos
        calc 1 + 3 * (primorial R2 : ℝ) = ε * (E * (1 + 3 * primorial R2)) := by
              rw [← mul_assoc, hεE, one_mul]
          _ < ε * n := h3
      linarith
    · -- hN2
      have e : ε ^ 2 * ((n : ℝ) / primorial R2) / 32 = n / (32 * E ^ 2 * primorial R2) := by
        rw [hε]; field_simp
      rw [e, le_div_iff₀ (by positivity)]
      have a1 : 1 + Real.log n ≤ 13 * T := by linarith
      calc (1 + Real.log n) * (32 * E ^ 2 * primorial R2)
          ≤ 13 * T * (32 * E ^ 2 * primorial R2) := mul_le_mul_of_nonneg_right a1 (by positivity)
        _ = T * (416 * E ^ 2 * primorial R2) := by ring
        _ ≤ T * T := mul_le_mul_of_nonneg_left hbig2 (by positivity)
        _ ≤ n := hTTn
    · -- hN3
      have e : ε / 8 * ((n : ℝ) / primorial R2) = n / (8 * E * primorial R2) := by
        rw [hε]; field_simp
      rw [e, le_div_iff₀ (by positivity)]
      have a1 : (Nat.log 2 n : ℝ) ≤ 12 * T := by linarith
      calc (Nat.log 2 n : ℝ) * (8 * E * primorial R2)
          ≤ 12 * T * (8 * E * primorial R2) := mul_le_mul_of_nonneg_right a1 (by positivity)
        _ = T * (96 * E * primorial R2) := by ring
        _ ≤ T * T := mul_le_mul_of_nonneg_left hbig3 (by positivity)
        _ ≤ n := hTTn
    · -- hN4
      have e : ε * ((n : ℝ) / primorial R2) = n / (E * primorial R2) := by
        rw [hε]; field_simp
      rw [e, le_div_iff₀ (by positivity)]
      have : 8 * (l : ℝ) * (E * primorial R2) = 8 * l * E * primorial R2 := by ring
      linarith
    · -- hN5
      have e : ε ^ 2 * ((n : ℝ) / primorial R2) ^ 2 = n ^ 2 / (E ^ 2 * primorial R2 ^ 2) := by
        rw [hε]; field_simp
      rw [e, le_div_iff₀ (by positivity)]
      have hn1 : (1 : ℝ) ≤ n := le_trans hT1 hnT
      have hP0 : (0 : ℝ) ≤ (E : ℝ) ^ 2 * (primorial R2 : ℝ) ^ 2 := by positivity
      calc 256 * (l : ℝ) * ((n : ℝ) + 1) * ((E : ℝ) ^ 2 * (primorial R2 : ℝ) ^ 2)
          ≤ 256 * (l : ℝ) * ((n : ℝ) + n) * ((E : ℝ) ^ 2 * (primorial R2 : ℝ) ^ 2) := by
            have : (0 : ℝ) ≤ 256 * l * ((E : ℝ) ^ 2 * (primorial R2 : ℝ) ^ 2) := by positivity
            nlinarith
        _ = (n : ℝ) * (512 * (l : ℝ) * (E : ℝ) ^ 2 * (primorial R2 : ℝ) ^ 2) := by ring
        _ ≤ (n : ℝ) * (T : ℝ) := mul_le_mul_of_nonneg_left hbig (by positivity)
        _ ≤ (n : ℝ) * (n : ℝ) := mul_le_mul_of_nonneg_left hnT (by positivity)
        _ = (n : ℝ) ^ 2 := by ring
  · push Not at hcase
    have hR0R : R0 ≤ R := by omega
    have hR48 : 2 ^ 48 ≤ R + 1 := by omega
    have hex0 : ∃ x ∈ A, ¬ 2 ∣ x ∧ ¬ 3 ∣ x := by
      have : 0 < sT.card := by omega
      obtain ⟨x, hx⟩ := card_pos.1 this
      rw [hsT, mem_filter] at hx
      exact ⟨x, hx.1, hx.2⟩
    have hPR : ∃ x ∈ A, ¬ 2 ∣ x ∧ ¬ 3 ∣ x ∧ wt (R0 + (R - R0)) x ≤ 1 / 8 := by
      obtain ⟨x, hx, h2, h3⟩ := hex0
      refine ⟨x, hx, h2, h3, ?_⟩
      rw [show R0 + (R - R0) = R by omega]
      have := mem_Icc.1 (hA hx)
      exact wt_le_top n R x (by omega) this.2 hR48 hnR
    have hP : ∃ t, ∃ x ∈ A, ¬ 2 ∣ x ∧ ¬ 3 ∣ x ∧ wt (R0 + t) x ≤ 1 / 8 := ⟨_, hPR⟩
    obtain ⟨x, hx, hx2, hx3, hxw⟩ := Nat.find_spec hP
    have htle : Nat.find hP ≤ R - R0 := Nat.find_min' hP hPR
    obtain ⟨L, hLdef⟩ : ∃ L, L = R0 + Nat.find hP := ⟨_, rfl⟩
    rw [← hLdef] at hxw
    have hLR : L ≤ R := by omega
    have hL0 : R0 ≤ L := by omega
    obtain ⟨Q, hQdef⟩ : ∃ Q, Q = primorial L := ⟨_, rfl⟩
    have hQpos : 0 < Q := hQdef ▸ primorial_pos L
    have hQT : Q ≤ T := by
      rw [hQdef, hT]
      exact (primorial_le_four_pow L).trans (Nat.pow_le_pow_right (by norm_num) hLR)
    set U := (range Q).filter (Nat.Coprime Q) with hU
    have hUcard : U.card = Nat.totient Q := rfl
    have hφpos : 0 < Nat.totient Q := Nat.totient_pos.2 hQpos
    have hUne : U.Nonempty := card_pos.1 (hUcard ▸ hφpos)
    have h2Q : 2 ∣ Q := hQdef ▸ dvd_primorial_of_le Nat.prime_two (by omega)
    have h3Q : 3 ∣ Q := hQdef ▸ dvd_primorial_of_le Nat.prime_three (by omega)
    have hf2 := fiber_sum Q 2 hQpos (by norm_num) h2Q M U (filter_subset _ _)
    have hf3 := fiber_sum Q 3 hQpos (by norm_num) h3Q M U (filter_subset _ _)
    obtain ⟨u, huU, hu⟩ := exists_le_of_sum_le hUne
      (f := fun u => ((M.filter (fun y => y % Q = (2 * u) % Q)).card +
        (M.filter (fun y => y % Q = (3 * u) % Q)).card) * U.card)
      (g := fun _ => 5 * M.card) (by
        rw [← sum_mul, sum_add_distrib, sum_const, smul_eq_mul]
        calc (∑ i ∈ U, (M.filter (fun y => y % Q = (2 * i) % Q)).card +
              ∑ i ∈ U, (M.filter (fun y => y % Q = (3 * i) % Q)).card) * U.card
            ≤ (2 * M.card + 3 * M.card) * U.card := Nat.mul_le_mul_right _ (add_le_add hf2 hf3)
          _ = U.card * (5 * M.card) := by ring)
    have huQ : Nat.Coprime Q u := (mem_filter.1 huU).2
    have hs2 := cls_split n Q (2 * u) 2 A h2Q (dvd_mul_right 2 u) (Or.inl rfl)
    have hs3 := cls_split n Q (3 * u) 3 A h3Q (dvd_mul_right 3 u) (Or.inr rfl)
    rw [← hM] at hs2 hs3
    have hc2 := card_cls_ge n Q (2 * u) hQpos
    have hc3 := card_cls_ge n Q (3 * u) hQpos
    have hQr : (0 : ℝ) < Q := by exact_mod_cast hQpos
    have hφr : (0 : ℝ) < Nat.totient Q := by exact_mod_cast hφpos
    have hdivr : (n : ℝ) / Q - 1 ≤ ((n / Q : ℕ) : ℝ) := by
      have h := Nat.lt_div_mul_add (a := n) hQpos
      have h' : (n : ℝ) < ((n / Q : ℕ) : ℝ) * Q + Q := by exact_mod_cast h
      rw [div_sub_one hQr.ne', div_le_iff₀ hQr]
      linarith
    have hQTr : (Q : ℝ) ≤ T := by exact_mod_cast hQT
    have hT64 : (64 : ℝ) ≤ T := by linarith [show (64 : ℝ) ≤ 2 ^ 48 by norm_num]
    have h4Q : 4 * (Q : ℝ) ≤ n := by
      have a1 : 4 * (T : ℝ) ≤ T * T :=
        mul_le_mul_of_nonneg_right (by linarith : (4 : ℝ) ≤ T) (by positivity)
      linarith
    have hmM0 : (0 : ℝ) ≤ M.card := by positivity
    have hMε : (M.card : ℝ) ≤ sT.card := by exact_mod_cast hMs.le
    have hLr0 : (R0 : ℝ) ≤ L := by exact_mod_cast hL0
    have hR0r : (4000000 : ℝ) ≤ R0 := by exact_mod_cast hR0K
    have hLTr : (L : ℝ) ≤ T := by exact_mod_cast hLR.trans hRT
    have hW : (Q : ℝ) ^ 2 ≤ 3 * L * (Nat.totient Q : ℝ) ^ 2 := by
      have := wallis L (by omega)
      rw [← hQdef] at this
      exact_mod_cast this
    have h300 : 300 * (L : ℝ) * (M.card : ℝ) ^ 2 ≤ ((n : ℝ) - 2 * Q) ^ 2 := by
      rcases Nat.eq_zero_or_pos (Nat.find hP) with h0 | hpos
      · have hLR0 : L = R0 := by omega
        rw [hLR0]
        refine h300a (M.card : ℝ) n Q R0 E K hmM0 ?_ (by rw [hE]; push_cast; ring)
          (by rw [hR0]; push_cast; ring) (by exact_mod_cast (by omega : 0 < K)) h4Q (by positivity)
        rw [hε] at hcase
        have : (sT.card : ℝ) ≤ n / E := by
          rw [div_eq_mul_one_div, mul_comm]; exact hcase.le
        linarith
      · have hmin := Nat.find_min hP (show Nat.find hP - 1 < Nat.find hP by omega)
        have hL1 : R0 + (Nat.find hP - 1) = L - 1 := by omega
        rw [hL1] at hmin
        have hsub : sT ⊆ (cls n 1 0).filter (fun x => 1 / 8 < wt (L - 1) x) := by
          intro y hy
          rw [hsT, mem_filter] at hy
          have hyI := mem_Icc.1 (hA hy.1)
          refine mem_filter.2 ⟨mem_cls.2 ⟨hyI.1, hyI.2, by rw [Nat.mod_one, Nat.mod_one]⟩, ?_⟩
          by_contra hc
          push Not at hc
          exact hmin ⟨y, hy.1, hy.2.1, hy.2.2, hc⟩
        have hmk := markov n 1 (L - 1) 0 (1 / 8) (by norm_num) one_pos
          (fun p hp h => absurd (Nat.le_of_dvd one_pos h) (by have := hp.two_le; omega))
        have hc := card_le_card hsub
        have hcr : (sT.card : ℝ) ≤ (((cls n 1 0).filter (fun x => 1 / 8 < wt (L - 1) x)).card : ℝ) := by
          exact_mod_cast hc
        have hLc : ((L - 1 : ℕ) : ℝ) + 1 = L := by
          have := Nat.sub_add_cancel (show 1 ≤ L by omega)
          exact_mod_cast this
        rw [hLc] at hmk
        have hLpos : (0 : ℝ) < L := by linarith
        have hsT : (sT.card : ℝ) ≤ 16 * n / L + 56 + 48 * T := by
          have e : (n : ℝ) / ((1 : ℕ) : ℝ) * (2 / L) = 2 * n / L := by
            push_cast; field_simp
          rw [e] at hmk
          have : (16 : ℝ) * n / L = 8 * (2 * n / L) := by ring
          linarith
        exact h300b (M.card : ℝ) n Q L T hmM0 (by linarith) (by linarith) hLTr
          (by linarith [show (400 : ℝ) ≤ 2 ^ 48 by norm_num]) hTr hQTr (by positivity)
    have hMb := mbound (M.card : ℝ) Q (Nat.totient Q) L n hmM0 (by positivity) (by positivity)
      (by linarith) hW h300
    have hu' : (((M.filter (fun y => y % Q = (2 * u) % Q)).card : ℝ) +
        ((M.filter (fun y => y % Q = (3 * u) % Q)).card : ℝ)) * (Nat.totient Q : ℝ) ≤
        5 * (M.card : ℝ) := by
      have := hu
      rw [hUcard] at this
      exact_mod_cast this
    have hcls2 : (n : ℝ) / Q / 2 ≤ ((A.filter (fun y => y % Q = (2 * u) % Q)).card : ℝ) := by
      refine cls_dense ((n : ℝ) / Q) ((cls n Q (2 * u)).card : ℝ) _
        ((M.filter (fun y => y % Q = (2 * u) % Q)).card : ℝ) (Nat.totient Q : ℝ) (M.card : ℝ) Q n
        hQr hφr rfl ?_ (by exact_mod_cast hs2) ?_ hMb
      · have : ((n / Q : ℕ) : ℝ) ≤ ((cls n Q (2 * u)).card : ℝ) := by exact_mod_cast hc2
        linarith
      · have : (0 : ℝ) ≤ ((M.filter (fun y => y % Q = (3 * u) % Q)).card : ℝ) * (Nat.totient Q : ℝ) :=
          by positivity
        have h' := hu'
        rw [add_mul] at h'
        linarith
    have hcls3 : (n : ℝ) / Q / 2 ≤ ((A.filter (fun y => y % Q = (3 * u) % Q)).card : ℝ) := by
      refine cls_dense ((n : ℝ) / Q) ((cls n Q (3 * u)).card : ℝ) _
        ((M.filter (fun y => y % Q = (3 * u) % Q)).card : ℝ) (Nat.totient Q : ℝ) (M.card : ℝ) Q n
        hQr hφr rfl ?_ (by exact_mod_cast hs3) ?_ hMb
      · have : ((n / Q : ℕ) : ℝ) ≤ ((cls n Q (3 * u)).card : ℝ) := by exact_mod_cast hc3
        linarith
      · have : (0 : ℝ) ≤ ((M.filter (fun y => y % Q = (2 * u) % Q)).card : ℝ) * (Nat.totient Q : ℝ) :=
          by positivity
        have h' := hu'
        rw [add_mul] at h'
        linarith
    have hl512 : 512 * (l : ℝ) ≤ T := by
      have : 512 * l ≤ T := by omega
      exact_mod_cast this
    obtain ⟨hC1, hC2, hC3⟩ := hC_aux n Q T l (Nat.log 2 n) hQr hQTr hTr hl512 hT64 hl1 hlog2
    have hL512 : 512 * (l : ℝ) ≤ L + 1 := by
      have : 512 * l ≤ L + 1 := by omega
      exact_mod_cast this
    subst hQdef
    exact case1 l n L x u A hA (by omega) hL512 hx hx2 hx3 hxw huQ hcls2 hcls3 hC1 hC2 hC3

end OMA883

theorem OMA.solution : type_of% @Erdos883.erdos_883.parts.ii := by
  intro l hl
  exact OMA883.main_thm l hl
