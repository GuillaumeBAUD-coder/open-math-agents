import OMAReductions.R_Erdos687_erdos_687_variants_maier_pomerance_R2_H1_R1_H1_R1_H2_R1
import Mathlib

-- Credit: @carterleffen

/-!
# Finite stopped-tree expansion lower bound

Proves `OMA.R_Erdos687_erdos_687_variants_maier_pomerance_R2_H1_R1_H1_R1_H2_R1.H1`, the purely
combinatorial stopped inclusion-exclusion lower bound on `[1, Y]` survivors.

## Proof outline

1. The tree `T` of admissible prime subsets contains `∅`, is closed under descending initial
   segments `I u d`, and admits every odd-cardinality extension `insert p u` of an even node
   `u ∈ T` by a prime `p ∈ P` strictly smaller than all elements of `u`.
2. For any subset `H ⊆ P` (representing the primes in `P` dividing `n - a p`), we establish by
   strong induction on `#(below P u)` that at every even node `u ∈ T` with no strict stopped
   ancestor in `F`,
   `∑_{d ∈ E, I u d} (-1)^#d * 1_{d ⊆ H} + ∑_{d ∈ F, I u d} 1_{d ⊆ H ∧ below H d = ∅} ≤ 1_{u ⊆ H ∧ below H u = ∅}`.
   At a stopped node `u ∈ F` equality holds directly; at an unstopped even node `u ∈ E`, we
   expand two levels (even to odd, then odd to even), apply the induction hypothesis to even
   grandchildren in `T`, drop missing even grandchildren using nonnegativity of indicators, and
   collapse both levels via the exact minimum-element identity
   `1_{v ⊆ H} - ∑_{p ∈ below P v} 1_{insert p v ⊆ H ∧ below H (insert p v) = ∅} = 1_{v ⊆ H ∧ below H v = ∅}`.
3. Summing the `u = ∅` bound over `n ∈ Z ∅ Q`, combining with the stopping-ledger hypothesis and
   the pointwise error bound `(-1)^k * y - |x - y| ≤ (-1)^k * x`, and noting that every prime
   `p ≤ ⌊z⌋₊` belongs to `Q ∪ P` yields the target lower bound.
-/

namespace Erdos687H1Proof
open Finset
open scoped Classical

private def below (P u : Finset ℕ) : Finset ℕ :=
  P.filter fun p => ∀ q ∈ u, p < q

private def descInit (u d : Finset ℕ) : Prop :=
  u ⊆ d ∧ ∀ p ∈ u, ∀ q ∈ d \ u, q < p

private lemma descInit_refl (u : Finset ℕ) : descInit u u :=
  ⟨Subset.rfl, fun _ _ _ hq => by simp at hq⟩

private lemma descInit_trans {a b c : Finset ℕ} (hab : descInit a b) (hbc : descInit b c) :
    descInit a c := by
  refine ⟨hab.1.trans hbc.1, fun p hp q hq => ?_⟩
  rw [mem_sdiff] at hq
  by_cases hqb : q ∈ b
  · exact hab.2 p hp q (mem_sdiff.mpr ⟨hqb, hq.2⟩)
  · exact hbc.2 p (hab.1 hp) q (mem_sdiff.mpr ⟨hq.1, hqb⟩)

private lemma descInit_empty (d : Finset ℕ) : descInit ∅ d :=
  ⟨empty_subset d, fun _ hp => (notMem_empty _ hp).elim⟩

private lemma not_mem_of_mem_below {P u : Finset ℕ} {p : ℕ} (hp : p ∈ below P u) : p ∉ u := by
  intro hpu
  exact lt_irrefl p ((mem_filter.mp hp).2 p hpu)

private lemma descInit_insert_self {P u : Finset ℕ} {p : ℕ} (hp : p ∈ below P u) :
    descInit u (insert p u) := by
  refine ⟨subset_insert p u, fun r hr q hq => ?_⟩
  rw [mem_sdiff, mem_insert] at hq
  rcases hq.1 with rfl | hqu
  · exact (mem_filter.mp hp).2 r hr
  · exact (hq.2 hqu).elim

private lemma below_insert {H u : Finset ℕ} {p : ℕ} (hp : ∀ q ∈ u, p < q) :
    below H (insert p u) = (below H u).filter (· < p) := by
  ext x
  simp only [below, mem_filter, mem_insert]
  constructor
  · rintro ⟨hxH, hlt⟩
    exact ⟨⟨hxH, fun q hqu => hlt q (Or.inr hqu)⟩, hlt p (Or.inl rfl)⟩
  · rintro ⟨⟨hxH, _⟩, hxp⟩
    refine ⟨hxH, fun q hq => ?_⟩
    rcases hq with rfl | hqu
    · exact hxp
    · exact lt_trans hxp (hp q hqu)

private lemma card_below_insert_lt {P u : Finset ℕ} {p : ℕ} (hp : p ∈ below P u) :
    (below P (insert p u)).card < (below P u).card := by
  apply card_lt_card
  rw [ssubset_iff_of_subset]
  · refine ⟨p, hp, ?_⟩
    simp only [below, mem_filter, mem_insert, not_and, not_forall]
    intro _
    exact ⟨p, Or.inl rfl, lt_irrefl p⟩
  · intro x hx
    simp only [below, mem_filter, mem_insert] at hx ⊢
    exact ⟨hx.1, fun q hq => hx.2 q (Or.inr hq)⟩

private lemma ind_avoid_identity {P H u : Finset ℕ} (hHP : H ⊆ P) :
    (if u ⊆ H then (1 : ℤ) else 0) -
      ∑ p ∈ below P u, (if insert p u ⊆ H ∧ below H (insert p u) = ∅ then (1 : ℤ) else 0) =
    if u ⊆ H ∧ below H u = ∅ then 1 else 0 := by
  by_cases huH : u ⊆ H
  · by_cases hbe : below H u = ∅
    · have hsum :
          ∑ p ∈ below P u, (if insert p u ⊆ H ∧ below H (insert p u) = ∅ then (1 : ℤ) else 0) = 0 := by
        apply sum_eq_zero
        intro p hp
        have hpnotH : p ∉ H := by
          intro hpH
          have : p ∈ below H u := mem_filter.mpr ⟨hpH, (mem_filter.mp hp).2⟩
          rw [hbe] at this
          exact notMem_empty _ this
        have hnot : ¬ (insert p u ⊆ H ∧ below H (insert p u) = ∅) := by
          intro h
          exact hpnotH (h.1 (mem_insert_self p u))
        simp [hnot]
      simp [huH, hbe, hsum]
    · have hne : (below H u).Nonempty := nonempty_iff_ne_empty.mpr hbe
      set p0 := (below H u).min' hne
      have hp0_mem : p0 ∈ below H u := min'_mem _ hne
      have hp0_P : p0 ∈ below P u := by
        rw [below, mem_filter] at hp0_mem ⊢
        exact ⟨hHP hp0_mem.1, hp0_mem.2⟩
      have hcond : ∀ p ∈ below P u,
          (insert p u ⊆ H ∧ below H (insert p u) = ∅) ↔ p = p0 := by
        intro p hp
        have hplt : ∀ q ∈ u, p < q := (mem_filter.mp hp).2
        constructor
        · rintro ⟨hins, hemt⟩
          have hpH : p ∈ H := hins (mem_insert_self p u)
          have hpB : p ∈ below H u := mem_filter.mpr ⟨hpH, hplt⟩
          have hle1 : p0 ≤ p := min'_le _ p hpB
          have hle2 : p ≤ p0 := by
            by_contra hlt
            push Not at hlt
            have hmem : p0 ∈ below H (insert p u) := by
              rw [below_insert hplt, mem_filter]
              exact ⟨hp0_mem, hlt⟩
            rw [hemt] at hmem
            exact notMem_empty _ hmem
          exact le_antisymm hle2 hle1
        · rintro rfl
          refine ⟨insert_subset (mem_filter.mp hp0_mem).1 huH, ?_⟩
          rw [below_insert (mem_filter.mp hp0_mem).2, eq_empty_iff_forall_notMem]
          intro x hx
          rw [mem_filter] at hx
          exact not_lt_of_ge (min'_le _ x hx.1) hx.2
      have hsum :
          ∑ p ∈ below P u, (if insert p u ⊆ H ∧ below H (insert p u) = ∅ then (1 : ℤ) else 0) = 1 := by
        calc
          ∑ p ∈ below P u, (if insert p u ⊆ H ∧ below H (insert p u) = ∅ then (1 : ℤ) else 0)
              = ∑ p ∈ below P u, (if p = p0 then (1 : ℤ) else 0) := by
                refine sum_congr rfl fun p hp => ?_
                simp [hcond p hp]
          _ = 1 := by simp [hp0_P]
      simp [huH, hbe, hsum]
  · have hsum :
        ∑ p ∈ below P u, (if insert p u ⊆ H ∧ below H (insert p u) = ∅ then (1 : ℤ) else 0) = 0 := by
      apply sum_eq_zero
      intro p _
      have hnot : ¬ (insert p u ⊆ H ∧ below H (insert p u) = ∅) := by
        intro h
        exact huH ((subset_insert p u).trans h.1)
      simp [hnot]
    simp [huH, hsum]

private lemma sum_filter_descInit {P : Finset ℕ} {T S : Finset (Finset ℕ)}
    (hTP : T ⊆ P.powerset)
    (hT_closed : ∀ d ∈ T, ∀ u, descInit u d → u ∈ T)
    (hST : S ⊆ T) {u : Finset ℕ} (f : Finset ℕ → ℤ) :
    ∑ d ∈ S.filter (descInit u), f d =
      (if u ∈ S then f u else 0) +
      ∑ p ∈ (below P u).filter (fun p => insert p u ∈ T),
        ∑ d ∈ S.filter (descInit (insert p u)), f d := by
  let C := (below P u).filter (fun p => insert p u ∈ T)
  have hdisj : Set.PairwiseDisjoint (C : Set ℕ) (fun p => S.filter (descInit (insert p u))) := by
    intro p1 hp1 p2 hp2 hne
    rw [Function.onFun, disjoint_left]
    intro d hd1 hd2
    rw [mem_filter] at hd1 hd2
    have hp1b : p1 ∈ below P u := (mem_filter.mp hp1).1
    have hp2b : p2 ∈ below P u := (mem_filter.mp hp2).1
    have hp2_not_ins1 : p2 ∉ insert p1 u := by
      rw [mem_insert]
      rintro (rfl | h)
      · exact hne rfl
      · exact not_mem_of_mem_below hp2b h
    have hp1_not_ins2 : p1 ∉ insert p2 u := by
      rw [mem_insert]
      rintro (rfl | h)
      · exact hne rfl
      · exact not_mem_of_mem_below hp1b h
    have hlt1 : p2 < p1 :=
      hd1.2.2 p1 (mem_insert_self p1 u) p2
        (mem_sdiff.mpr ⟨hd2.2.1 (mem_insert_self p2 u), hp2_not_ins1⟩)
    have hlt2 : p1 < p2 :=
      hd2.2.2 p2 (mem_insert_self p2 u) p1
        (mem_sdiff.mpr ⟨hd1.2.1 (mem_insert_self p1 u), hp1_not_ins2⟩)
    exact lt_asymm hlt1 hlt2
  have hunion :
      (S.filter (descInit u)).erase u = C.biUnion (fun p => S.filter (descInit (insert p u))) := by
    ext d
    simp only [mem_erase, mem_filter, mem_biUnion, C]
    constructor
    · rintro ⟨hdu, hdS, hud⟩
      have hne : (d \ u).Nonempty := by
        rw [sdiff_nonempty]
        intro hsub
        exact hdu (Subset.antisymm hsub hud.1)
      set p := (d \ u).max' hne
      have hp_sdiff : p ∈ d \ u := max'_mem _ hne
      have hp_d : p ∈ d := (mem_sdiff.mp hp_sdiff).1
      have hdP : d ⊆ P := mem_powerset.mp (hTP (hST hdS))
      have hp_below : p ∈ below P u :=
        mem_filter.mpr ⟨hdP hp_d, fun r hr => hud.2 r hr p hp_sdiff⟩
      have hdesc : descInit (insert p u) d := by
        refine ⟨insert_subset hp_d hud.1, fun x hx q hq => ?_⟩
        rw [mem_sdiff, mem_insert] at hq
        have hq_sdiff : q ∈ d \ u := mem_sdiff.mpr ⟨hq.1, fun hqu => hq.2 (Or.inr hqu)⟩
        rcases mem_insert.mp hx with rfl | hxu
        · have hle : q ≤ p := le_max' (d \ u) q hq_sdiff
          have hqp : q ≠ p := fun h => hq.2 (Or.inl h)
          exact lt_of_le_of_ne hle hqp
        · exact hud.2 x hxu q hq_sdiff
      have hinsT : insert p u ∈ T := hT_closed d (hST hdS) (insert p u) hdesc
      exact ⟨p, ⟨hp_below, hinsT⟩, hdS, hdesc⟩
    · rintro ⟨p, ⟨hp_below, _⟩, hdS, hdesc⟩
      have hdu : d ≠ u := by
        rintro rfl
        exact not_mem_of_mem_below hp_below (hdesc.1 (mem_insert_self p _))
      exact ⟨hdu, hdS, descInit_trans (descInit_insert_self hp_below) hdesc⟩
  have hsum_biUnion :
      ∑ d ∈ (S.filter (descInit u)).erase u, f d =
        ∑ p ∈ C, ∑ d ∈ S.filter (descInit (insert p u)), f d := by
    rw [hunion, sum_biUnion hdisj]
  by_cases huS : u ∈ S
  · have hu_mem : u ∈ S.filter (descInit u) := mem_filter.mpr ⟨huS, descInit_refl u⟩
    rw [← add_sum_erase _ _ hu_mem, hsum_biUnion, if_pos huS]
  · have hu_not : u ∉ S.filter (descInit u) := by
      rw [mem_filter]
      exact fun h => huS h.1
    rw [← erase_eq_of_notMem hu_not, hsum_biUnion, if_neg huS, zero_add]

private lemma odd_ext_mem_E {P : Finset ℕ} {T F : Finset (Finset ℕ)}
    (hT_even_ext : ∀ u ∈ T, Even u.card → ∀ p ∈ below P u, insert p u ∈ T)
    (hF : ∀ d ∈ F, d.Nonempty ∧ Even d.card ∧ ∀ u ∈ F, descInit u d → u = d)
    {u : Finset ℕ} (huT : u ∈ T) (hu_even : Even u.card)
    (huE : ∀ z ∈ F, ¬ descInit z u)
    {p : ℕ} (hp : p ∈ below P u) :
    insert p u ∈ T.filter (fun d => ∀ z ∈ F, ¬ descInit z d) := by
  rw [mem_filter]
  refine ⟨hT_even_ext u huT hu_even p hp, fun z hzF hzu => ?_⟩
  by_cases hpz : p ∈ z
  · have husub : u ⊆ z := by
      intro r hr
      by_contra hrz
      have hlt : r < p := hzu.2 p hpz r (mem_sdiff.mpr ⟨mem_insert_of_mem hr, hrz⟩)
      exact lt_asymm hlt ((mem_filter.mp hp).2 r hr)
    have hzeq : z = insert p u := Subset.antisymm hzu.1 (insert_subset hpz husub)
    have hcard : z.card = u.card + 1 := by
      rw [hzeq, card_insert_of_notMem (not_mem_of_mem_below hp)]
    have heven_z : Even z.card := (hF z hzF).2.1
    rw [hcard] at heven_z
    exact Nat.not_even_iff_odd.mpr hu_even.add_one heven_z
  · have hzsub : z ⊆ u := by
      intro x hx
      rcases mem_insert.mp (hzu.1 hx) with rfl | hxu
      · exact (hpz hx).elim
      · exact hxu
    have hz_init_u : descInit z u := by
      refine ⟨hzsub, fun x hx r hr => ?_⟩
      rw [mem_sdiff] at hr
      exact hzu.2 x hx r (mem_sdiff.mpr ⟨mem_insert_of_mem hr.1, hr.2⟩)
    exact huE z hzF hz_init_u

private lemma no_strict_stop_insert {P : Finset ℕ} {F : Finset (Finset ℕ)}
    {v : Finset ℕ} (hvE : ∀ z ∈ F, ¬ descInit z v)
    {q : ℕ} (hq : q ∈ below P v) :
    ∀ z ∈ F, descInit z (insert q v) → z = insert q v := by
  intro z hzF hzw
  by_cases hqz : q ∈ z
  · have hvsub : v ⊆ z := by
      intro r hr
      by_contra hrz
      have hlt : r < q := hzw.2 q hqz r (mem_sdiff.mpr ⟨mem_insert_of_mem hr, hrz⟩)
      exact lt_asymm hlt ((mem_filter.mp hq).2 r hr)
    exact Subset.antisymm hzw.1 (insert_subset hqz hvsub)
  · have hzsub : z ⊆ v := by
      intro x hx
      rcases mem_insert.mp (hzw.1 hx) with rfl | hxv
      · exact (hqz hx).elim
      · exact hxv
    have hz_init_v : descInit z v := by
      refine ⟨hzsub, fun x hx r hr => ?_⟩
      rw [mem_sdiff] at hr
      exact hzw.2 x hx r (mem_sdiff.mpr ⟨mem_insert_of_mem hr.1, hr.2⟩)
    exact (hvE z hzF hz_init_v).elim

private lemma stopped_tree_pointwise {P H : Finset ℕ} {T F : Finset (Finset ℕ)}
    (hTP : T ⊆ P.powerset)
    (hT_closed : ∀ d ∈ T, ∀ u, descInit u d → u ∈ T)
    (hT_even_ext : ∀ u ∈ T, Even u.card → ∀ p ∈ below P u, insert p u ∈ T)
    (hFT : F ⊆ T)
    (hF : ∀ d ∈ F, d.Nonempty ∧ Even d.card ∧ ∀ u ∈ F, descInit u d → u = d)
    (hHP : H ⊆ P) :
    let E := T.filter fun d => ∀ u ∈ F, ¬ descInit u d
    ∀ n : ℕ, ∀ u ∈ T, (below P u).card = n → Even u.card →
      (∀ v ∈ F, descInit v u → v = u) →
      (∑ d ∈ E.filter (descInit u), (-1 : ℤ) ^ d.card * (if d ⊆ H then 1 else 0)) +
      (∑ d ∈ F.filter (descInit u), if d ⊆ H ∧ below H d = ∅ then (1 : ℤ) else 0) ≤
      if u ⊆ H ∧ below H u = ∅ then 1 else 0 := by
  intro E n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro u huT hcard_u hu_even hu_nostop
    by_cases huF : u ∈ F
    · have hE_empty : E.filter (descInit u) = ∅ := by
        rw [eq_empty_iff_forall_notMem]
        intro d hd
        rw [mem_filter] at hd
        exact (mem_filter.mp hd.1).2 u huF hd.2
      have hF_sing : F.filter (descInit u) = {u} := by
        ext d
        simp only [mem_filter, mem_singleton]
        constructor
        · rintro ⟨hdF, hud⟩
          exact ((hF d hdF).2.2 u huF hud).symm
        · rintro rfl
          exact ⟨huF, descInit_refl _⟩
      rw [hE_empty, hF_sing, sum_empty, zero_add, sum_singleton]
    · have hu_noF : ∀ z ∈ F, ¬ descInit z u := by
        intro z hzF hzu
        exact huF (hu_nostop z hzF hzu ▸ hzF)
      have huE : u ∈ E := mem_filter.mpr ⟨huT, hu_noF⟩
      have hET : E ⊆ T := filter_subset _ _
      have hfilt_u : (below P u).filter (fun p => insert p u ∈ T) = below P u := by
        rw [filter_eq_self]
        intro p hp
        exact hT_even_ext u huT hu_even p hp
      have hE_expand := sum_filter_descInit hTP hT_closed hET (u := u)
        (fun d => (-1 : ℤ) ^ d.card * (if d ⊆ H then 1 else 0))
      have hF_expand := sum_filter_descInit hTP hT_closed hFT (u := u)
        (fun d => if d ⊆ H ∧ below H d = ∅ then (1 : ℤ) else 0)
      rw [if_pos huE, hu_even.neg_one_pow, one_mul, hfilt_u] at hE_expand
      rw [if_neg huF, zero_add, hfilt_u] at hF_expand
      have hstep_p : ∀ p ∈ below P u,
          (∑ d ∈ E.filter (descInit (insert p u)), (-1 : ℤ) ^ d.card * (if d ⊆ H then 1 else 0)) +
          (∑ d ∈ F.filter (descInit (insert p u)), if d ⊆ H ∧ below H d = ∅ then (1 : ℤ) else 0) ≤
          -(if insert p u ⊆ H ∧ below H (insert p u) = ∅ then (1 : ℤ) else 0) := by
        intro p hp
        set v := insert p u
        have hvE : v ∈ E := odd_ext_mem_E hT_even_ext hF huT hu_even hu_noF hp
        have hv_noF : ∀ z ∈ F, ¬ descInit z v := (mem_filter.mp hvE).2
        have hv_notF : v ∉ F := fun hvF => hv_noF v hvF (descInit_refl v)
        have hv_odd : Odd v.card := by
          rw [card_insert_of_notMem (not_mem_of_mem_below hp)]
          exact hu_even.add_one
        have hE_v := sum_filter_descInit hTP hT_closed hET (u := v)
          (fun d => (-1 : ℤ) ^ d.card * (if d ⊆ H then 1 else 0))
        have hF_v := sum_filter_descInit hTP hT_closed hFT (u := v)
          (fun d => if d ⊆ H ∧ below H d = ∅ then (1 : ℤ) else 0)
        rw [if_pos hvE, hv_odd.neg_one_pow, neg_one_mul] at hE_v
        rw [if_neg hv_notF, zero_add] at hF_v
        set Cv := (below P v).filter (fun q => insert q v ∈ T)
        have hq_le : ∀ q ∈ Cv,
            (∑ d ∈ E.filter (descInit (insert q v)), (-1 : ℤ) ^ d.card * (if d ⊆ H then 1 else 0)) +
            (∑ d ∈ F.filter (descInit (insert q v)), if d ⊆ H ∧ below H d = ∅ then (1 : ℤ) else 0) ≤
            if insert q v ⊆ H ∧ below H (insert q v) = ∅ then (1 : ℤ) else 0 := by
          intro q hq
          have hq_below : q ∈ below P v := (mem_filter.mp hq).1
          have hqwT : insert q v ∈ T := (mem_filter.mp hq).2
          have hlt_card : (below P (insert q v)).card < n := by
            rw [← hcard_u]
            exact lt_trans (card_below_insert_lt hq_below) (card_below_insert_lt hp)
          have hw_even : Even (insert q v).card := by
            rw [card_insert_of_notMem (not_mem_of_mem_below hq_below)]
            exact hv_odd.add_one
          have hw_nostop := no_strict_stop_insert hv_noF hq_below
          exact ih (below P (insert q v)).card hlt_card (insert q v) hqwT rfl hw_even hw_nostop
        have hsum_q :
            ∑ q ∈ Cv,
              ((∑ d ∈ E.filter (descInit (insert q v)), (-1 : ℤ) ^ d.card * (if d ⊆ H then 1 else 0)) +
               (∑ d ∈ F.filter (descInit (insert q v)), if d ⊆ H ∧ below H d = ∅ then (1 : ℤ) else 0)) ≤
            ∑ q ∈ below P v,
              (if insert q v ⊆ H ∧ below H (insert q v) = ∅ then (1 : ℤ) else 0) := by
          calc
            ∑ q ∈ Cv,
                ((∑ d ∈ E.filter (descInit (insert q v)), (-1 : ℤ) ^ d.card * (if d ⊆ H then 1 else 0)) +
                 (∑ d ∈ F.filter (descInit (insert q v)), if d ⊆ H ∧ below H d = ∅ then (1 : ℤ) else 0))
                ≤ ∑ q ∈ Cv, (if insert q v ⊆ H ∧ below H (insert q v) = ∅ then (1 : ℤ) else 0) :=
                  sum_le_sum hq_le
            _ ≤ ∑ q ∈ below P v, (if insert q v ⊆ H ∧ below H (insert q v) = ∅ then (1 : ℤ) else 0) := by
                  apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
                  intro q _ _
                  split_ifs <;> norm_num
        have hid_v := ind_avoid_identity (u := v) hHP
        rw [hE_v, hF_v]
        linarith [sum_add_distrib (s := Cv)
          (f := fun q => ∑ d ∈ E.filter (descInit (insert q v)), (-1 : ℤ) ^ d.card * (if d ⊆ H then 1 else 0))
          (g := fun q => ∑ d ∈ F.filter (descInit (insert q v)), if d ⊆ H ∧ below H d = ∅ then (1 : ℤ) else 0)]
      have hsum_p :
          ∑ p ∈ below P u,
            ((∑ d ∈ E.filter (descInit (insert p u)), (-1 : ℤ) ^ d.card * (if d ⊆ H then 1 else 0)) +
             (∑ d ∈ F.filter (descInit (insert p u)), if d ⊆ H ∧ below H d = ∅ then (1 : ℤ) else 0)) ≤
          ∑ p ∈ below P u, -(if insert p u ⊆ H ∧ below H (insert p u) = ∅ then (1 : ℤ) else 0) :=
        sum_le_sum hstep_p
      have hid_u := ind_avoid_identity (u := u) hHP
      rw [hE_expand, hF_expand]
      rw [sum_neg_distrib] at hsum_p
      linarith [sum_add_distrib (s := below P u)
        (f := fun p => ∑ d ∈ E.filter (descInit (insert p u)), (-1 : ℤ) ^ d.card * (if d ⊆ H then 1 else 0))
        (g := fun p => ∑ d ∈ F.filter (descInit (insert p u)), if d ⊆ H ∧ below H d = ∅ then (1 : ℤ) else 0)]

private lemma real_signed_error_le (k : ℕ) (x y : ℝ) :
    (-1 : ℝ) ^ k * y - |x - y| ≤ (-1 : ℝ) ^ k * x := by
  rcases Nat.even_or_odd k with hk | hk
  · rw [hk.neg_one_pow, one_mul, one_mul]
    linarith [le_abs_self (y - x), abs_sub_comm x y]
  · rw [hk.neg_one_pow, neg_one_mul, neg_one_mul]
    linarith [le_abs_self (x - y)]

end Erdos687H1Proof

theorem OMA.solution : OMA.R_Erdos687_erdos_687_variants_maier_pomerance_R2_H1_R1_H1_R1_H2_R1.H1 := by
  classical
  intro Y w z μ P Q D g e T a Z I F hFT hF E hstop
  have hTP : T ⊆ P.powerset := Finset.filter_subset _ _
  have hT_empty : (∅ : Finset ℕ) ∈ T := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_powerset.mpr (Finset.empty_subset P),
      fun _ hp => (Finset.notMem_empty _ hp).elim⟩
  have hT_closed : ∀ d ∈ T, ∀ u, Erdos687H1Proof.descInit u d → u ∈ T := by
    intro d hdT u hud
    rw [Finset.mem_filter] at hdT ⊢
    refine ⟨Finset.mem_powerset.mpr (hud.1.trans (Finset.mem_powerset.mp hdT.1)), fun p hp => ?_⟩
    have hfilt : u.filter (p ≤ ·) = d.filter (p ≤ ·) := by
      ext x
      simp only [Finset.mem_filter]
      constructor
      · exact fun ⟨hxu, hpx⟩ => ⟨hud.1 hxu, hpx⟩
      · rintro ⟨hxd, hpx⟩
        refine ⟨?_, hpx⟩
        by_contra hxu
        exact not_lt_of_ge hpx (hud.2 p hp x (Finset.mem_sdiff.mpr ⟨hxd, hxu⟩))
    rw [hfilt]
    exact hdT.2 p (hud.1 hp)
  have hT_even_ext : ∀ u ∈ T, Even u.card → ∀ p ∈ Erdos687H1Proof.below P u, insert p u ∈ T := by
    intro u huT hu_even p hp
    rw [Finset.mem_filter] at huT ⊢
    have hpP : p ∈ P := (Finset.mem_filter.mp hp).1
    have hplt : ∀ q ∈ u, p < q := (Finset.mem_filter.mp hp).2
    refine ⟨Finset.mem_powerset.mpr (Finset.insert_subset hpP (Finset.mem_powerset.mp huT.1)),
      fun r hr => ?_⟩
    rcases Finset.mem_insert.mp hr with hrp | hru
    · subst hrp
      dsimp only
      intro heven
      have hfilt : (insert r u).filter (r ≤ ·) = insert r u := by
        rw [Finset.filter_eq_self]
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hxu
        · exact le_rfl
        · exact le_of_lt (hplt x hxu)
      rw [hfilt, Finset.card_insert_of_notMem (Erdos687H1Proof.not_mem_of_mem_below hp)] at heven
      exact (Nat.not_even_iff_odd.mpr hu_even.add_one heven).elim
    · dsimp only
      have hfilt : (insert p u).filter (r ≤ ·) = u.filter (r ≤ ·) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hxu, hrx⟩
          · exact (not_lt_of_ge hrx (hplt r hru)).elim
          · exact ⟨hxu, hrx⟩
        · rintro ⟨hxu, hrx⟩
          exact ⟨Or.inr hxu, hrx⟩
      rw [hfilt]
      exact huT.2 r hru
  have hF_nostop_empty : ∀ v ∈ F, Erdos687H1Proof.descInit v ∅ → v = ∅ := by
    intro v _ hv0
    exact Finset.subset_empty.mp hv0.1
  let U := Z ∅ Q
  have hcard_E : ∀ d ∈ E,
      ((Z d Q).card : ℤ) =
        ∑ n ∈ U, if d ⊆ P.filter (fun p => n ≡ a p [MOD p]) then (1 : ℤ) else 0 := by
    intro d hdE
    have hdP : d ⊆ P := Finset.mem_powerset.mp (hTP (Finset.filter_subset _ _ hdE))
    have hZeq : Z d Q = U.filter (fun n => d ⊆ P.filter (fun p => n ≡ a p [MOD p])) := by
      ext n
      rw [Finset.mem_filter]
      simp only [Z, U, Finset.mem_filter, Finset.notMem_empty, IsEmpty.forall_iff,
        implies_true, true_and]
      constructor
      · rintro ⟨hnI, hnd, hnQ⟩
        refine ⟨⟨hnI, hnQ⟩, fun p hp => Finset.mem_filter.mpr ⟨hdP hp, hnd p hp⟩⟩
      · rintro ⟨⟨hnI, hnQ⟩, hsub⟩
        exact ⟨hnI, fun p hp => (Finset.mem_filter.mp (hsub hp)).2, hnQ⟩
    rw [hZeq, Finset.card_filter]
    push_cast
    rfl
  have hcard_F : ∀ d ∈ F,
      ((Z d (Q ∪ Erdos687H1Proof.below P d)).card : ℤ) =
        ∑ n ∈ U,
          if d ⊆ P.filter (fun p => n ≡ a p [MOD p]) ∧
             Erdos687H1Proof.below (P.filter (fun p => n ≡ a p [MOD p])) d = ∅
          then (1 : ℤ) else 0 := by
    intro d hdF
    have hdP : d ⊆ P := Finset.mem_powerset.mp (hTP (hFT hdF))
    have hZeq : Z d (Q ∪ Erdos687H1Proof.below P d) =
        U.filter (fun n =>
          d ⊆ P.filter (fun p => n ≡ a p [MOD p]) ∧
          Erdos687H1Proof.below (P.filter (fun p => n ≡ a p [MOD p])) d = ∅) := by
      ext n
      rw [Finset.mem_filter]
      simp only [Z, U, Erdos687H1Proof.below, Finset.mem_filter, Finset.mem_union,
        Finset.notMem_empty, IsEmpty.forall_iff, implies_true, true_and,
        Finset.eq_empty_iff_forall_notMem]
      constructor
      · rintro ⟨hnI, hnd, hnav⟩
        refine ⟨⟨hnI, fun p hpQ => hnav p (Or.inl hpQ)⟩,
          fun p hp => Finset.mem_filter.mpr ⟨hdP hp, hnd p hp⟩, ?_⟩
        intro p hp
        exact hnav p (Or.inr ⟨hp.1.1, hp.2⟩) hp.1.2
      · rintro ⟨⟨hnI, hnQ⟩, hsub, hemt⟩
        refine ⟨hnI, fun p hp => (Finset.mem_filter.mp (hsub hp)).2, fun p hp => ?_⟩
        rcases hp with hpQ | hpB
        · exact hnQ p hpQ
        · intro hhit
          exact hemt p ⟨⟨hpB.1, hhit⟩, hpB.2⟩
    rw [hZeq, Finset.card_filter]
    push_cast
    rfl
  have hcard_surv :
      ((Z ∅ (Q ∪ P)).card : ℤ) =
        ∑ n ∈ U,
          if (∅ : Finset ℕ) ⊆ P.filter (fun p => n ≡ a p [MOD p]) ∧
             Erdos687H1Proof.below (P.filter (fun p => n ≡ a p [MOD p])) ∅ = ∅
          then (1 : ℤ) else 0 := by
    have hZeq : Z ∅ (Q ∪ P) =
        U.filter (fun n =>
          (∅ : Finset ℕ) ⊆ P.filter (fun p => n ≡ a p [MOD p]) ∧
          Erdos687H1Proof.below (P.filter (fun p => n ≡ a p [MOD p])) ∅ = ∅) := by
      ext n
      rw [Finset.mem_filter]
      simp only [Z, U, Erdos687H1Proof.below, Finset.mem_filter, Finset.mem_union,
        Finset.notMem_empty, IsEmpty.forall_iff, implies_true, true_and, Finset.empty_subset,
        Finset.eq_empty_iff_forall_notMem]
      constructor
      · rintro ⟨hnI, hnav⟩
        refine ⟨⟨hnI, fun p hpQ => hnav p (Or.inl hpQ)⟩, ?_⟩
        intro p hp
        exact hnav p (Or.inr hp.1.1) hp.1.2
      · rintro ⟨⟨hnI, hnQ⟩, hemt⟩
        refine ⟨hnI, fun p hp => ?_⟩
        rcases hp with hpQ | hpP
        · exact hnQ p hpQ
        · intro hhit
          exact hemt p ⟨⟨hpP, hhit⟩, trivial⟩
    rw [hZeq, Finset.card_filter]
    push_cast
    rfl
  have hcomb_int :
      (∑ d ∈ E, (-1 : ℤ) ^ d.card * ((Z d Q).card : ℤ)) +
      (∑ d ∈ F, ((Z d (Q ∪ Erdos687H1Proof.below P d)).card : ℤ)) ≤
      ((Z ∅ (Q ∪ P)).card : ℤ) := by
    have h1 :
        ∑ d ∈ E, (-1 : ℤ) ^ d.card * ((Z d Q).card : ℤ) =
          ∑ n ∈ U, ∑ d ∈ E,
            (-1 : ℤ) ^ d.card * (if d ⊆ P.filter (fun p => n ≡ a p [MOD p]) then (1 : ℤ) else 0) := by
      calc
        ∑ d ∈ E, (-1 : ℤ) ^ d.card * ((Z d Q).card : ℤ)
            = ∑ d ∈ E, ∑ n ∈ U,
                (-1 : ℤ) ^ d.card * (if d ⊆ P.filter (fun p => n ≡ a p [MOD p]) then (1 : ℤ) else 0) := by
              refine Finset.sum_congr rfl fun d hd => ?_
              rw [hcard_E d hd, Finset.mul_sum]
        _ = _ := Finset.sum_comm
    have h2 :
        ∑ d ∈ F, ((Z d (Q ∪ Erdos687H1Proof.below P d)).card : ℤ) =
          ∑ n ∈ U, ∑ d ∈ F,
            if d ⊆ P.filter (fun p => n ≡ a p [MOD p]) ∧
               Erdos687H1Proof.below (P.filter (fun p => n ≡ a p [MOD p])) d = ∅
            then (1 : ℤ) else 0 := by
      calc
        ∑ d ∈ F, ((Z d (Q ∪ Erdos687H1Proof.below P d)).card : ℤ)
            = ∑ d ∈ F, ∑ n ∈ U,
                if d ⊆ P.filter (fun p => n ≡ a p [MOD p]) ∧
                   Erdos687H1Proof.below (P.filter (fun p => n ≡ a p [MOD p])) d = ∅
                then (1 : ℤ) else 0 :=
              Finset.sum_congr rfl fun d hd => hcard_F d hd
        _ = _ := Finset.sum_comm
    rw [h1, h2, ← Finset.sum_add_distrib, hcard_surv]
    refine Finset.sum_le_sum fun n _ => ?_
    have hpt := Erdos687H1Proof.stopped_tree_pointwise
      (P := P) (H := P.filter (fun p => n ≡ a p [MOD p])) (T := T) (F := F)
      hTP hT_closed hT_even_ext hFT hF (Finset.filter_subset _ _)
      (Erdos687H1Proof.below P ∅).card ∅ hT_empty rfl (by simp) hF_nostop_empty
    have hE_eq : (T.filter fun d => ∀ u ∈ F, ¬ Erdos687H1Proof.descInit u d) = E := by
      ext d
      simp [E, I, Erdos687H1Proof.descInit]
    have hEf : (T.filter fun d => ∀ u ∈ F, ¬ Erdos687H1Proof.descInit u d).filter
        (Erdos687H1Proof.descInit ∅) = E := by
      rw [hE_eq, Finset.filter_eq_self]
      intro d _
      exact Erdos687H1Proof.descInit_empty d
    have hFf : F.filter (Erdos687H1Proof.descInit ∅) = F := by
      rw [Finset.filter_eq_self]
      intro d _
      exact Erdos687H1Proof.descInit_empty d
    simpa only [hEf, hFf] using hpt
  have hcomb_real :
      (∑ d ∈ E, (-1 : ℝ) ^ d.card * ((Z d Q).card : ℝ)) +
      (∑ d ∈ F, ((Z d (Q ∪ P.filter (fun p => ∀ q ∈ d, p < q))).card : ℝ)) ≤
      ((Z ∅ (Q ∪ P)).card : ℝ) := by
    have hcast : (((∑ d ∈ E, (-1 : ℤ) ^ d.card * ((Z d Q).card : ℤ)) +
      (∑ d ∈ F, ((Z d (Q ∪ Erdos687H1Proof.below P d)).card : ℤ)) : ℤ) : ℝ) ≤
      (((Z ∅ (Q ∪ P)).card : ℤ) : ℝ) := Int.cast_le.mpr hcomb_int
    simpa [Erdos687H1Proof.below] using hcast
  have hsurv_le :
      ((Z ∅ (Q ∪ P)).card : ℝ) ≤
        (((Finset.Icc 1 Y).filter fun n =>
          ∀ p ≤ ⌊z⌋₊, p.Prime → ¬ (n ≡ a p [MOD p])).card : ℝ) := by
    norm_cast
    apply Finset.card_le_card
    intro n hn
    simp only [Z, Q, P, Finset.mem_filter, Finset.mem_union, Finset.mem_range, Finset.mem_Icc] at hn ⊢
    refine ⟨hn.1, fun p hpz hpPrime => ?_⟩
    by_cases hpw : p < ⌊w⌋₊ + 1
    · exact hn.2.2 p (Or.inl ⟨hpw, hpPrime⟩)
    · exact hn.2.2 p (Or.inr ⟨⟨Nat.le_of_not_lt hpw, hpz⟩, hpPrime⟩)
  have hsplit :
      μ * (∑ d ∈ T, (-1 : ℝ) ^ d.card / D d) =
        μ * (∑ d ∈ T \ E, (-1 : ℝ) ^ d.card / D d) +
        ∑ d ∈ E, (-1 : ℝ) ^ d.card * (μ / D d) := by
    have hET : E ⊆ T := Finset.filter_subset _ _
    rw [← Finset.sum_sdiff hET, mul_add]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    ring
  have herr_le :
      (∑ d ∈ E, (-1 : ℝ) ^ d.card * (μ / D d)) -
        (∑ d ∈ E, |((Z d Q).card : ℝ) - μ / D d|) ≤
      ∑ d ∈ E, (-1 : ℝ) ^ d.card * ((Z d Q).card : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun d _ =>
      Erdos687H1Proof.real_signed_error_le d.card ((Z d Q).card : ℝ) (μ / D d)
  linarith
