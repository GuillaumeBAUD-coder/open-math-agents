import FormalConjectures.Books.BugeaudDistributionModuloOne.Problem10_6
import Mathlib.Analysis.Normed.Group.AddCircle

/-!
# Pollington–de Mathan theorem for lacunary sequences

A uniformly lacunary tail gives a uniform bound on the number of frequencies
in each dyadic band. Small integer neighbourhoods then discard only a bounded
fraction of the subintervals at each stage of a Cantor construction. The resulting
set has a Hölder map onto the unit interval with exponent arbitrarily close to one.
-/

namespace LacunaryIntervals

open Finset Filter
open scoped BigOperators

noncomputable def frequencies (m : ℕ → ℕ) (a b : ℕ) : Finset ℕ := by
  classical
  exact (Ico a b).filter (fun y => y ∈ Set.range m)

lemma mem_frequencies {m : ℕ → ℕ} {a b y : ℕ} :
    y ∈ frequencies m a b ↔ a ≤ y ∧ y < b ∧ y ∈ Set.range m := by
  classical
  simp [frequencies, and_assoc]

lemma frequency_union (m : ℕ → ℕ) {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    frequencies m a c = frequencies m a b ∪ frequencies m b c := by
  ext y
  simp only [mem_union, mem_frequencies]
  by_cases hy : y < b
  · constructor
    · exact fun h => Or.inl ⟨h.1, hy, h.2.2⟩
    · rintro (h | h)
      · exact ⟨h.1, hy.trans_le hbc, h.2.2⟩
      · exact (hy.not_ge h.1).elim
  · constructor
    · exact fun h => Or.inr ⟨le_of_not_gt hy, h.2⟩
    · rintro (h | h)
      · exact (hy h.2.1).elim
      · exact ⟨hab.trans h.1, h.2⟩

lemma frequency_disjoint (m : ℕ → ℕ) (a b c : ℕ) :
    Disjoint (frequencies m a b) (frequencies m b c) := by
  refine disjoint_left.mpr fun y h₁ h₂ => ?_
  exact (mem_frequencies.mp h₁).2.1.not_ge (mem_frequencies.mp h₂).1

lemma lacunary_band_card (m : ℕ → ℕ) (hm : ∀ n, 0 < m n) (hlac : IsLacunary m) :
    ∃ K > 0, ∀ p > 0, (frequencies m p (2 * p)).card ≤ K := by
  classical
  obtain ⟨c, hc, h⟩ := hlac
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  have hstep (i : ℕ) (hi : N ≤ i) : m i + 1 ≤ m (i + 1) := by
    have h₁ : (0 : ℝ) < m i := by exact_mod_cast hm i
    have h₂ := hN i hi
    have h₃ : (m i : ℝ) < m (i+1) :=
      (lt_mul_of_one_lt_left h₁ hc).trans h₂
    exact_mod_cast h₃
  have hplus (i : ℕ) (hi : N ≤ i) (r : ℕ) : m i + r ≤ m (i + r) := by
    induction r with
    | zero => simp
    | succ r ih =>
      simpa only [Nat.add_succ] using (Nat.succ_le_succ ih).trans (hstep (i + r) (by omega))
  have hgrowth (i : ℕ) (hi : N ≤ i) (r : ℕ) : c ^ r * (m i : ℝ) ≤ m (i + r) := by
    induction r with
    | zero => simp
    | succ r ih =>
      rw [pow_succ', mul_assoc, Nat.add_succ]
      exact (mul_le_mul_of_nonneg_left ih (by linarith)).trans
        (hN (i + r) (by omega)).le
  obtain ⟨J, hJ⟩ := (tendsto_pow_atTop_atTop_of_one_lt hc).eventually_ge_atTop
    (2 : ℝ) |>.exists
  refine ⟨N + J + 1, by omega, ?_⟩
  intro p hp
  let T := (Ico N (N + 2 * p)).filter (fun i => m i ∈ Ico p (2*p))
  have hTcard : T.card ≤ J + 1 := by
    by_cases ht : T.Nonempty
    · let i := T.min' ht
      have hi : i ∈ T := min'_mem T ht
      have hip : p ≤ m i := (mem_Ico.mp (mem_filter.mp hi).2).1
      have hiN : N ≤ i := (mem_Ico.mp (mem_filter.mp hi).1).1
      have habs (j : ℕ) (hj : j ∈ T) : j < i + J := by
        by_contra! hh
        have hjp : m j < 2 * p := (mem_Ico.mp (mem_filter.mp hj).2).2
        have h₂ : (2 : ℝ) * p ≤ c ^ J * m i := by
          gcongr
        have hgap := hplus (i+J) (by omega) (j-(i+J))
        rw [Nat.add_sub_of_le hh] at hgap
        have hmono : m (i+J) ≤ m j := by omega
        have hfinal : (2 * p : ℝ) ≤ m j :=
          (h₂.trans (hgrowth i hiN J)).trans (by exact_mod_cast hmono)
        exact (not_le_of_gt (by exact_mod_cast hjp : (m j : ℝ) < 2 * p)) hfinal
      have hsub : T ⊆ Ico i (i+J) := by
        intro j hj
        exact mem_Ico.mpr ⟨min'_le T j hj, habs j hj⟩
      exact (card_le_card hsub).trans (by simp)
    · simp [not_nonempty_iff_eq_empty.mp ht]
  have hcover : frequencies m p (2*p) ⊆ ((range N).image m) ∪ (T.image m) := by
    intro y hy
    obtain ⟨hlo, hhi, i, rfl⟩ := mem_frequencies.mp hy
    apply mem_union.mpr
    by_cases hi : i < N
    · exact Or.inl (mem_image.mpr ⟨i, mem_range.mpr hi, rfl⟩)
    · have hNi : N ≤ i := le_of_not_gt hi
      have hi2p : i < N+2*p := by
        have hp' := hplus N le_rfl (i-N)
        rw [Nat.add_sub_of_le hNi] at hp'
        omega
      exact Or.inr (mem_image.mpr ⟨i, mem_filter.mpr
        ⟨mem_Ico.mpr ⟨hNi, hi2p⟩, mem_Ico.mpr ⟨hlo, hhi⟩⟩, rfl⟩)
  calc
    _ ≤ (((range N).image m) ∪ (T.image m)).card := card_le_card hcover
    _ ≤ ((range N).image m).card + (T.image m).card := card_union_le _ _
    _ ≤ (range N).card + T.card := Nat.add_le_add card_image_le card_image_le
    _ ≤ _ := by rw [card_range]; omega

lemma band_bounds (m : ℕ → ℕ) {K : ℕ} (hK : ∀ p > 0, (frequencies m p (2*p)).card ≤ K)
    (e j : ℕ) :
    (frequencies m (2 ^ e) (2 ^ (e+j))).card ≤ j * K ∧
    (∑ y ∈ frequencies m (2 ^ e) (2 ^ (e+j)), y) + 2 * K * (2 ^ e) ≤
      2 * K * (2 ^ (e+j)) := by
  induction j with
  | zero =>
    have hnil : frequencies m (2^e) (2^e) = ∅ := by
      ext y
      simp only [mem_frequencies, notMem_empty, iff_false]
      omega
    simp [hnil]
  | succ j ih =>
    let p := (2 : ℕ) ^ (e+j)
    have hp : 0 < p := by positivity
    have hep : (2 : ℕ) ^ e ≤ p := pow_le_pow_right₀ (by decide) (Nat.le_add_right _ _)
    have hsucc : (2 : ℕ) ^ (e+j.succ) = 2*p := by dsimp [p]; rw [Nat.add_succ,pow_succ']
    have hcard := hK p hp
    have hsum : (∑ y ∈ frequencies m p (2*p), y) ≤ K * (2*p) := by
      have hh := sum_le_sum (s := frequencies m p (2*p)) (g := fun _ => 2*p)
        (fun y hy => (mem_frequencies.mp hy).2.1.le)
      rw [sum_const, smul_eq_mul] at hh
      exact hh.trans (Nat.mul_le_mul_right _ hcard)
    rcases ih with ⟨ihcard, ihsum⟩
    rw [hsucc, frequency_union m hep (by omega)]
    have hdis := frequency_disjoint m (2^e) p (2*p)
    constructor
    · rw [card_union_of_disjoint hdis, Nat.succ_mul j K]
      exact Nat.add_le_add ihcard hcard
    · rw [sum_union hdis]
      calc
        _ = (∑ y ∈ frequencies m (2^e) p, y) + 2 * K * (2^e) +
          ∑ y ∈ frequencies m p (2*p), y := by ac_rfl
        _ ≤ 2 * K * p + K * (2*p) := Nat.add_le_add ihsum hsum
        _ = _ := by ring

end LacunaryIntervals

namespace LacunaryIntervals

open Finset Filter
open scoped BigOperators

noncomputable def integerWindow (u v : ℝ) : Finset ℤ := Icc ⌈u⌉ ⌊v⌋

lemma mem_integerWindow {u v : ℝ} {z : ℤ} :
    z ∈ integerWindow u v ↔ u ≤ z ∧ (z : ℝ) ≤ v := by
  simp [integerWindow, Int.ceil_le, Int.le_floor]

lemma integerWindow_card {u v : ℝ} (huv : u ≤ v) :
    ((integerWindow u v).card : ℝ) ≤ v - u + 1 := by
  by_cases h : ⌈u⌉ ≤ ⌊v⌋ + 1
  · have heq : ((integerWindow u v).card : ℤ) = ⌊v⌋ + 1 - ⌈u⌉ :=
      Int.card_Icc_of_le _ _ h
    have hreal : ((integerWindow u v).card : ℝ) = (⌊v⌋ : ℤ) + 1 - (⌈u⌉ : ℤ) := by
      exact_mod_cast heq
    rw [hreal]
    linarith [Int.floor_le v, Int.le_ceil u]
  · have hempty : integerWindow u v = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro z hz
      have hzi := Finset.mem_Icc.mp hz
      omega
    simp only [hempty, card_empty, Nat.cast_zero]
    linarith

lemma card_nat_window {u v : ℝ} (huv : u ≤ v) (T : Finset ℕ)
    (hT : ∀ i ∈ T, u ≤ (i : ℝ) ∧ (i : ℝ) ≤ v) :
    (T.card : ℝ) ≤ v - u + 1 := by
  have hcard := card_le_card_of_injOn (fun i : ℕ => (i : ℤ))
    (s := T) (t := integerWindow u v)
    (fun i hi => mem_integerWindow.mpr (by simpa only [Int.cast_natCast] using hT i hi))
    (fun _ _ _ _ h => Int.ofNat.inj h)
  exact (Nat.cast_le.mpr hcard).trans (integerWindow_card huv)

lemma choose_spaced {b : ℕ} {G : Finset ℕ} (h : 2 * b ≤ G.card) :
    ∃ f : Fin b → ℕ, (∀ i, f i ∈ G) ∧
      ∀ i j, i ≠ j → f i + 2 ≤ f j ∨ f j + 2 ≤ f i := by
  classical
  let A := G.filter (fun i => i % 2 = 0)
  let B := G.filter (fun i => ¬i % 2 = 0)
  have hsplit : A.card + B.card = G.card := card_filter_add_card_filter_not _
  obtain ⟨P, hPG, hp, hpar⟩ : ∃ P ⊆ G, b ≤ P.card ∧
      ∀ i ∈ P, ∀ j ∈ P, i % 2 = j % 2 := by
    by_cases hA : b ≤ A.card
    · exact ⟨A, filter_subset _ _, hA,
        fun i hi j hj => (mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm⟩
    · refine ⟨B, filter_subset _ _, by omega, ?_⟩
      intro i hi j hj
      have hi' := (mem_filter.mp hi).2
      have hj' := (mem_filter.mp hj).2
      omega
  obtain ⟨T, hTP, hT⟩ := exists_subset_card_eq hp
  let e := (Fintype.equivFinOfCardEq (by simpa using hT : Fintype.card T = b)).symm
  refine ⟨fun i => (e i : ℕ), fun i => hPG (hTP (e i).property), ?_⟩
  intro i j hij
  have he : (e i : ℕ) ≠ (e j : ℕ) := fun hval => hij (e.injective (Subtype.ext hval))
  have hmod := hpar _ (hTP (e i).property) _ (hTP (e j).property)
  change (e i : ℕ) + 2 ≤ (e j : ℕ) ∨ (e j : ℕ) + 2 ≤ (e i : ℕ)
  omega

lemma choose_children (b : ℕ) (hb : 0 < b) (F : Finset ℕ) (a l ε : ℝ)
    (hl : 0 < l) (he : 0 < ε) (hehalf : ε ≤ 1/2)
    (hm : ∀ m ∈ F, 0 < m ∧ 2 * ε ≤ (m : ℝ) * l)
    (hcount : 3 * ((4 * (b : ℝ) * l) * (∑ m ∈ F, (m : ℝ)) + 2 * F.card) ≤ 2 * (b : ℝ)) :
    ∃ f : Fin b → ℕ, (∀ i, f i < 4*b) ∧
      (∀ i j, i ≠ j → f i + 2 ≤ f j ∨ f j + 2 ≤ f i) ∧
      ∀ i (x : ℝ), x ∈ Set.Icc (a + f i * l) (a + (f i + 1) * l) →
        ∀ m ∈ F, ∀ z : ℤ, ε < |x * (m : ℝ) - z| := by
  classical
  let Q := 4*b
  let parentLen := (Q : ℝ) * l
  have hQ : (0 : ℝ) < Q := by exact_mod_cast Nat.mul_pos (by decide) hb
  have hPL : 0 < parentLen := mul_pos hQ hl
  let Z (m : ℕ) := integerWindow (m * a - ε) (m * (a + parentLen) + ε)
  let cut (m : ℕ) (z : ℤ) : Finset ℕ := (range Q).filter (fun (i : ℕ) =>
    m * (a + (i : ℝ) * l) - ε ≤ z ∧ (z : ℝ) ≤ m * (a + ((i : ℝ) + 1) * l) + ε)
  let bad := F.biUnion (fun m => (Z m).biUnion (cut m))
  have hZ (m : ℕ) : ((Z m).card : ℝ) ≤ m * parentLen + 2 := by
    have hlen : 0 ≤ (m : ℝ) * parentLen := mul_nonneg (Nat.cast_nonneg _) hPL.le
    exact (integerWindow_card (u := m*a - ε) (v := m*(a+parentLen)+ε)
      (by linarith)).trans (by linarith)
  have hcut (m : ℕ) (hmF : m ∈ F) (z : ℤ) : (cut m z).card ≤ 3 := by
    obtain ⟨hm_pos, hm_len⟩ := hm m hmF
    have hml : 0 < (m : ℝ) * l := by positivity
    let lo := ((z : ℝ) - ε - m*a) / (m*l) - 1
    let hi := ((z : ℝ) + ε - m*a) / (m*l)
    have hdiff : hi - lo = (2 * ε) / ((m : ℝ) * l) + 1 := by
      dsimp [hi, lo]
      field_simp [hml.ne']
      ring
    have hfrac : (2 * ε) / ((m : ℝ) * l) ≤ 1 := (div_le_one hml).mpr hm_len
    have hlohi : lo ≤ hi := by
      have := div_nonneg (by positivity : 0 ≤ 2 * ε) hml.le
      linarith
    have hx : ((cut m z).card : ℝ) ≤ hi - lo + 1 := by
      apply card_nat_window hlohi
      intro i hi'
      obtain ⟨_, h₁, h₂⟩ := mem_filter.mp hi'
      constructor
      · dsimp [lo]
        rw [sub_le_iff_le_add, div_le_iff₀ hml]
        linarith only [h₂]
      · dsimp [hi]
        rw [le_div_iff₀ hml]
        linarith only [h₁]
    exact_mod_cast (show ((cut m z).card : ℝ) ≤ (3 : ℝ) by linarith)
  have hbSub : bad ⊆ range Q := by
    intro i hi
    obtain ⟨m, _, h⟩ := mem_biUnion.mp hi
    obtain ⟨z, _, hz⟩ := mem_biUnion.mp h
    exact (mem_filter.mp hz).1
  have bad_card_nat :
      bad.card ≤ ∑ m ∈ F, (3 * (Z m).card) := by
    apply card_biUnion_le.trans
    apply sum_le_sum
    intro m hmF
    apply card_biUnion_le.trans
    have h := sum_le_sum (s := Z m) (g := fun _ => 3) (fun z _ => hcut m hmF z)
    simpa [mul_comm 3] using h
  have bad_bound : (bad.card : ℝ) ≤ (2 : ℝ) * b := by
    calc
      _ ≤ ∑ m ∈ F, (3 : ℝ) * (Z m).card := by exact_mod_cast bad_card_nat
      _ ≤ ∑ m ∈ F, (3 : ℝ) * (m * parentLen + 2) := by
        exact sum_le_sum fun m hmF => mul_le_mul_of_nonneg_left (hZ m) (by norm_num)
      _ = 3 * (parentLen * (∑ m ∈ F, (m : ℝ)) + 2 * F.card) := by
        simp only [← mul_sum, sum_add_distrib, sum_const]
        rw [← sum_mul]
        ring
      _ ≤ _ := by simpa [parentLen, Q] using hcount
  let G := range Q \ bad
  have hg : 2 * b ≤ G.card := by
    have hb' : bad.card ≤ 2*b := by exact_mod_cast bad_bound
    rw [show G = range Q \ bad from rfl, card_sdiff_of_subset hbSub, card_range]
    dsimp [Q]
    omega
  obtain ⟨f, hf, hspace⟩ := choose_spaced hg
  have hfR (i : Fin b) : f i < Q := mem_range.mp (mem_sdiff.mp (hf i)).1
  refine ⟨f, hfR, hspace, ?_⟩
  intro i x hx m hmF z
  by_contra! hz
  obtain ⟨hzl, hzh⟩ := abs_le.mp hz
  have hiQ : ((f i : ℝ) + 1) ≤ Q := by exact_mod_cast (Nat.succ_le_of_lt (hfR i))
  have ha : a ≤ x := (le_add_of_nonneg_right (by positivity)).trans hx.1
  have hbnd : x ≤ a + parentLen := hx.2.trans (by dsimp [parentLen]; gcongr)
  have hma := mul_le_mul_of_nonneg_left ha (Nat.cast_nonneg (α := ℝ) m)
  have hmb := mul_le_mul_of_nonneg_left hbnd (Nat.cast_nonneg (α := ℝ) m)
  have hcut₁ := mul_le_mul_of_nonneg_left hx.1 (Nat.cast_nonneg (α := ℝ) m)
  have hcut₂ := mul_le_mul_of_nonneg_left hx.2 (Nat.cast_nonneg (α := ℝ) m)
  apply (mem_sdiff.mp (hf i)).2
  apply mem_biUnion.mpr
  refine ⟨m, hmF, mem_biUnion.mpr ⟨z, mem_integerWindow.mpr ⟨?_, ?_⟩, ?_⟩⟩
  · linarith only [hzl,hzh,hma]
  · linarith only [hzl,hzh,hmb]
  · exact mem_filter.mpr ⟨mem_range.mpr (hfR i), by
      constructor
      · linarith only [hzl,hzh,hcut₁]
      · linarith only [hzl,hzh,hcut₂]⟩

end LacunaryIntervals

namespace LacunaryIntervals

open Finset Filter Metric Set
open scoped BigOperators ENNReal NNReal Topology

abbrev UnitInterval := Set.Icc (0 : ℝ) 1

noncomputable def width (q : ℕ) (c : ℝ) (n : ℕ) : ℝ := c / (q : ℝ) ^ n

lemma width_pos {q : ℕ} {c : ℝ} (hq : 0 < q) (hc : 0 < c) (n : ℕ) : 0 < width q c n :=
  div_pos hc (pow_pos (by exact_mod_cast hq) _)

lemma width_succ {q : ℕ} (hq : 0 < q) (c : ℝ) (n : ℕ) :
    (q : ℝ) * width q c (n+1) = width q c n := by
  unfold width
  rw [pow_succ', ← mul_div_assoc, mul_div_mul_left _ _ (by exact_mod_cast hq.ne')]

lemma exists_digit {b : ℕ} (hb : 1 < b) (x : UnitInterval) :
    ∃ d : Fin b, 0 ≤ (b : ℝ) * x - (d : ℕ) ∧ (b : ℝ) * x - (d : ℕ) ≤ 1 := by
  have hx := x.property
  have hb' : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  by_cases hlt : (x : ℝ) < 1
  · let d := ⌊(b : ℝ) * x⌋₊
    have hd : d < b := Nat.floor_lt (mul_nonneg hb'.le hx.1) |>.mpr (by
      simpa only [mul_one] using mul_lt_mul_of_pos_left hlt hb')
    refine ⟨⟨d, hd⟩, ?_, ?_⟩
    · exact sub_nonneg.mpr (Nat.floor_le (mul_nonneg hb'.le hx.1))
    · have hh := Nat.lt_floor_add_one ((b : ℝ) * x)
      change (b : ℝ) * x - (d : ℝ) ≤ 1
      linarith only [hh]
  · have hxeq : (x : ℝ) = 1 := le_antisymm hx.2 (le_of_not_gt hlt)
    refine ⟨⟨b-1, by omega⟩, ?_, ?_⟩
    · change 0 ≤ (b : ℝ) * x - ((b - 1 : ℕ) : ℝ)
      rw [hxeq, mul_one, Nat.cast_sub (by omega)]
      norm_num
    · change (b : ℝ) * x - ((b - 1 : ℕ) : ℝ) ≤ 1
      rw [hxeq, mul_one, Nat.cast_sub (by omega)]
      norm_num

lemma full_dimension_of_children {q b : ℕ} (hb : 1 < b) (hq : 0 < q)
    {c : ℝ} (hc : 0 < c) {r : ℝ≥0} (hr : 0 < r) (hbr : (q : ℝ) ^ (r : ℝ) = b)
    (child : ℕ → ℝ → Fin b → ℕ)
    (hchild : ∀ n a i, child n a i < q)
    (hspace : ∀ n a i j, i ≠ j →
      child n a i + 2 ≤ child n a j ∨ child n a j + 2 ≤ child n a i)
    {X : Set ℝ}
    (hX : ∀ l : ℕ → ℝ,
      (∀ n, ∃ i : Fin b, l (n+1) = l n + (child n (l n) i : ℝ) * width q c (n+1)) →
      (∀ n, l n ≤ sSup (range l) ∧ sSup (range l) ≤ l n + width q c n) →
      sSup (range l) ∈ X) :
    (r : ℝ≥0∞) ≤ dimH X := by
  classical
  have hbp : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  let d (y : UnitInterval) : Fin b := (exists_digit hb y).choose
  have hd (y : UnitInterval) : (b : ℝ) * y - (d y : ℕ) ∈ UnitInterval :=
    (exists_digit hb y).choose_spec
  let next (y : UnitInterval) : UnitInterval :=
    ⟨(b : ℝ) * (y : ℝ) - ((d y : ℕ) : ℝ), hd y⟩
  let res (y : UnitInterval) (n : ℕ) : UnitInterval := Nat.rec y (fun _ u => next u) n
  let digit (y : UnitInterval) (n : ℕ) : Fin b := d (res y n)
  let left (y : UnitInterval) (n : ℕ) : ℝ := Nat.rec 0
    (fun k l => l + (child k l (digit y k) : ℝ) * width q c (k+1)) n
  have hres (y : UnitInterval) (n : ℕ) :
      (res y (n+1)).val = (b : ℝ) * (res y n).val - (((digit y n).val : ℕ) : ℝ) := rfl
  have hleft (y : UnitInterval) (n : ℕ) :
      left y (n+1) = left y n + (child n (left y n) (digit y n) : ℝ) * width q c (n+1) := rfl
  have hmono (y : UnitInterval) : Monotone (left y) := by
    apply monotone_nat_of_le_succ
    intro n
    rw [hleft]
    exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (width_pos hq hc _).le)
  have hanti (y : UnitInterval) : Antitone (fun n => left y n + width q c n) := by
    apply antitone_nat_of_succ_le
    intro n
    have hq' : ((child n (left y n) (digit y n) : ℝ) + 1) ≤ q := by
      exact_mod_cast Nat.succ_le_of_lt (hchild n (left y n) (digit y n))
    rw [hleft, ← width_succ hq c n]
    linarith only [mul_le_mul_of_nonneg_right hq' (width_pos hq hc (n+1)).le]
  let φ (y : UnitInterval) : ℝ := sSup (range (left y))
  have hpoint (y : UnitInterval) (n : ℕ) :
      left y n ≤ φ y ∧ φ y ≤ left y n + width q c n := by
    have hbound (k : ℕ) : ∀ x ∈ range (left y), x ≤ left y k + width q c k := by
      rintro _ ⟨m, rfl⟩
      rcases le_total m k with h | h
      · exact (hmono y h).trans (le_add_of_nonneg_right (width_pos hq hc _).le)
      · exact (le_add_of_nonneg_right (width_pos hq hc m).le).trans (hanti y h)
    exact ⟨le_csSup ⟨_, hbound 0⟩ (mem_range_self n), csSup_le (range_nonempty _) (hbound n)⟩
  have hmaps (y : UnitInterval) : φ y ∈ X :=
    hX (left y) (fun n => ⟨digit y n, hleft y n⟩) (hpoint y)
  have hprefix {u v : UnitInterval} (n : ℕ)
      (h : ∀ j < n, digit u j = digit v j) :
      left u n = left v n ∧
      (res u n).val - (res v n).val = (b : ℝ) ^ n * ((u : ℝ) - v) := by
    induction n with
    | zero => simp [left, res]
    | succ n ih =>
      obtain ⟨h₁, h₂⟩ := ih (fun j hj => h j (hj.trans (Nat.lt_succ_self n)))
      have hs := h n (Nat.lt_succ_self n)
      refine ⟨by rw [hleft, hleft, h₁, hs], ?_⟩
      rw [hres, hres, hs, pow_succ']
      linarith only [congrArg ((b : ℝ) * ·) h₂]
  have hclose {u v : UnitInterval} (n : ℕ) (h : ∀ j < n, digit u j = digit v j) :
      |(u : ℝ) - v| ≤ 1 / (b : ℝ) ^ n := by
    have hbprod : 0 < (b : ℝ) ^ n := pow_pos hbp _
    apply (le_div_iff₀ hbprod).mpr
    rw [mul_comm, ← abs_of_nonneg hbprod.le, ← abs_mul, ← (hprefix n h).2]
    exact abs_sub_le_iff.mpr ⟨by linarith [(res u n).property.2, (res v n).property.1],
      by linarith [(res v n).property.2, (res u n).property.1]⟩
  have hseparate {u v : UnitInterval} (n : ℕ) (hpre : ∀ j < n, digit u j = digit v j)
      (hne : digit u n ≠ digit v n) :
      width q c (n+1) ≤ |φ u - φ v| := by
    have hbase := (hprefix n hpre).1
    have hu := hpoint u (n+1)
    have hv := hpoint v (n+1)
    rw [hleft, hbase] at hu
    rw [hleft] at hv
    rcases hspace n (left v n) _ _ hne with h | h
    · have hreal : (child n (left v n) (digit u n) : ℝ) + 2 ≤ child n (left v n) (digit v n) := by
        exact_mod_cast h
      have hg := mul_le_mul_of_nonneg_right hreal (width_pos hq hc (n+1)).le
      rw [abs_of_nonpos (by linarith only [hu.2, hv.1, hg, (width_pos hq hc (n+1)).le])]
      linarith only [hu.2, hv.1, hg]
    · have hreal : (child n (left v n) (digit v n) : ℝ) + 2 ≤ child n (left v n) (digit u n) := by
        exact_mod_cast h
      have hg := mul_le_mul_of_nonneg_right hreal (width_pos hq hc (n+1)).le
      rw [abs_of_nonneg (by linarith only [hv.2, hu.1, hg, (width_pos hq hc (n+1)).le])]
      linarith only [hv.2, hu.1, hg]
  have hexists (u v : UnitInterval) (h : u ≠ v) : ∃ n, digit u n ≠ digit v n := by
    by_contra! he
    have hlim : Tendsto (fun n : ℕ => 1 / (b : ℝ) ^ n) atTop (𝓝 0) := by
      simp only [one_div]
      exact tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by exact_mod_cast hb))
    have hle : |(u : ℝ) - v| ≤ (0 : ℝ) :=
      le_of_tendsto_of_tendsto tendsto_const_nhds hlim
        (Eventually.of_forall fun n => hclose n (fun j _ => he j))
    have hv : (u : ℝ) = v := sub_eq_zero.mp (abs_eq_zero.mp (hle.antisymm (abs_nonneg _)))
    exact h (Subtype.ext hv)
  have hrate (n : ℕ) :
      (b : ℝ) / c ^ (r : ℝ) * (width q c (n+1)) ^ (r : ℝ) = 1 / (b : ℝ) ^ n := by
    have hqreal : (0 : ℝ) < q := by exact_mod_cast hq
    have hcp : c ^ (r : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hc _).ne'
    have hbp' : (b : ℝ) ^ n ≠ 0 := (pow_pos hbp _).ne'
    unfold width
    rw [Real.div_rpow hc.le (by positivity), ← Real.rpow_natCast_mul hqreal.le,
      mul_comm ((n+1 : ℕ) : ℝ), Real.rpow_mul hqreal.le, hbr, Real.rpow_natCast, pow_succ]
    field_simp [hcp, hbp', hbp.ne']
  let C : ℝ≥0 := ⟨(b : ℝ) / c ^ (r : ℝ), by positivity⟩
  have hbound (u v : UnitInterval) :
      |(u : ℝ) - v| ≤ (C : ℝ) * |φ u - φ v| ^ (r : ℝ) := by
    by_cases heq : u = v
    · simp only [heq, sub_self, abs_zero]
      positivity
    · have H := hexists u v heq
      let n := Nat.find H
      have hne := Nat.find_spec H
      have hpre (j : ℕ) (hj : j < n) : digit u j = digit v j :=
        not_not.mp (Nat.find_min H hj)
      have hsp := hseparate n hpre hne
      calc
        _ ≤ 1 / (b : ℝ) ^ n := hclose n hpre
        _ = (C : ℝ) * (width q c (n+1)) ^ (r : ℝ) := (hrate n).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (width_pos hq hc _).le hsp r.coe_nonneg) C.coe_nonneg
  have hφinj : Function.Injective φ := by
    intro u v h
    by_contra! hne
    let H := hexists u v hne
    let n := Nat.find H
    have hne' := Nat.find_spec H
    have hpre (j : ℕ) (hj : j < n) : digit u j = digit v j :=
      not_not.mp (Nat.find_min H hj)
    have hsp := hseparate n hpre hne'
    rw [h, sub_self, abs_zero] at hsp
    exact (width_pos hq hc _).not_ge hsp
  let : Nonempty UnitInterval := ⟨⟨0, by simp⟩⟩
  let inv (x : ℝ) : ℝ := ((Function.invFun φ x : UnitInterval) : ℝ)
  have hinv (y : UnitInterval) : inv (φ y) = y := by
    unfold inv
    rw [Function.leftInverse_invFun hφinj y]
  have hhold : HolderOnWith C r inv (range φ) := by
    rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
    rw [hinv, hinv, edist_nndist, edist_nndist,
      ← ENNReal.coe_rpow_of_nonneg _ r.coe_nonneg, ← ENNReal.coe_mul, ENNReal.coe_le_coe]
    apply NNReal.coe_le_coe.mp
    simpa only [NNReal.coe_mul, NNReal.coe_rpow, ← dist_nndist, Real.dist_eq] using hbound u v
  have himage : UnitInterval ⊆ inv '' range φ := by
    intro y hy
    let u : UnitInterval := ⟨y, hy⟩
    exact ⟨φ u, mem_range_self u, hinv u⟩
  have hdim : dimH UnitInterval = 1 := by
    rw [Real.dimH_of_nonempty_interior]
    · simp
    · rw [interior_Icc]
      exact nonempty_Ioo.mpr zero_lt_one
  have htop : (1 : ℝ≥0∞) ≤ dimH (range φ) / (r : ℝ≥0∞) := by
    rw [← hdim]
    exact (dimH_mono himage).trans (hhold.dimH_image_le hr)
  have hbnd : (r : ℝ≥0∞) ≤ dimH (range φ) := by
    have := (ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast hr.ne'))
      (Or.inl ENNReal.coe_ne_top)).mp htop
    simpa only [one_mul] using this
  exact hbnd.trans (dimH_mono (fun _ ⟨u, hu⟩ => hu ▸ hmaps u))

end LacunaryIntervals

namespace LacunaryIntervals

open Finset Filter Metric Set
open scoped BigOperators ENNReal NNReal Topology

lemma sq_le_two_pow (j : ℕ) (hj : 4 ≤ j) : j ^ 2 ≤ 2 ^ j := by
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases h : 4 ≤ j
    · have hj' : (4 : ℝ) ≤ j := by exact_mod_cast h
      have hstep : ((j : ℝ) + 1) ^ 2 ≤ 2 * (j : ℝ) ^ 2 := by
        nlinarith only [hj', sq_nonneg ((j : ℝ) - 2)]
      calc
        (j+1)^2 ≤ 2*j^2 := by exact_mod_cast hstep
        _ ≤ 2 * 2 ^ j := Nat.mul_le_mul_left 2 (ih h)
        _ = 2 ^ (j+1) := (pow_succ' _ _).symm
    · have hj₃ : j = 3 := by omega
      subst j
      decide

lemma dim_lower_avoiders (m : ℕ → ℕ) (hm : ∀ n, 0 < m n) {K : ℕ} (hK : 0 < K)
    (hfreq : ∀ p > 0, (frequencies m p (2*p)).card ≤ K)
    (J : ℕ) (hJ : 4 ≤ J) (hJK : 16*K ≤ J) :
    ∃ ε > (0 : ℝ), ENNReal.ofReal (1 - 2 / (J : ℝ)) ≤
      dimH {x : ℝ | ∀ n : ℕ, ∀ z : ℤ, ε < |x * (m n : ℝ) - z|} := by
  classical
  let q : ℕ := 2 ^ J
  let b : ℕ := 2 ^ (J-2)
  have hqb : 4 * b = q := by
    dsimp [q,b]
    rw [show (4:ℕ) = 2^2 by decide, ← pow_add]
    congr 1
    omega
  have hb : 1 < b := by
    dsimp [b]
    exact one_lt_pow₀ (by decide) (by omega)
  have hq : 1 < q := by omega
  have hqr : (1 : ℝ) < q := by exact_mod_cast hq
  have hJr : (4 : ℝ) ≤ J := by exact_mod_cast hJ
  have hJpos : (0 : ℝ) < J := by linarith
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hc : 0 < (1 : ℝ) / (48 * (K : ℝ)) := by positivity
  let c : ℝ := 1 / (48 * (K : ℝ))
  let ε : ℝ := c / (2 * (q : ℝ))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεhalf : ε ≤ 1/2 := by
    have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
    have hc1 : c ≤ 1 := by
      dsimp [c]
      rw [div_le_one (by positivity)]
      linarith
    dsimp [ε]
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hqbig : 16*K*J ≤ q := by
    exact (Nat.mul_le_mul_right _ hJK).trans
      (by simpa only [pow_two, q] using sq_le_two_pow J hJ)
  have hrate : 0 < 1 - 2 / (J : ℝ) := by
    rw [sub_pos, div_lt_one hJpos]
    linarith
  let r : ℝ≥0 := ⟨_, hrate.le⟩
  have hr : 0 < r := hrate
  have hqrp : (q : ℝ) ^ (r : ℝ) = b := by
    have hR : (J : ℝ) * (r : ℝ) = ((J-2 : ℕ) : ℝ) := by
      change (J : ℝ) * (1 - 2 / (J : ℝ)) = ((J-2 : ℕ) : ℝ)
      rw [Nat.cast_sub (by omega)]
      field_simp
      norm_num
    dsimp [q,b]
    push_cast
    rw [← Real.rpow_natCast_mul (by norm_num : 0 ≤ (2 : ℝ)), hR, Real.rpow_natCast]
  let F (n : ℕ) := frequencies m (q ^ n) (q ^ (n+1))
  have hF (n : ℕ) : (F n).card ≤ J*K ∧ (∑ x ∈ F n, x) ≤ 2*K*q^(n+1) := by
    have hp : (2 : ℕ) ^ (J*n) = q^n := by rw [pow_mul]
    have hp' : (2 : ℕ) ^ (J*n+J) = q^(n+1) := by
      rw [show J*n+J = J*(n+1) by ring, pow_mul]
    have h := band_bounds m hfreq (J*n) J
    rw [hp, hp'] at h
    exact ⟨h.1, h.2.trans' (Nat.le_add_right _ _)⟩
  have hchildren (n : ℕ) (a : ℝ) :
      ∃ f : Fin b → ℕ, (∀ i, f i < q) ∧
        (∀ i j, i ≠ j → f i + 2 ≤ f j ∨ f j + 2 ≤ f i) ∧
        ∀ i (x : ℝ), x ∈ Icc (a + (f i : ℝ) * width q c (n+1))
          (a + ((f i : ℝ) + 1) * width q c (n+1)) →
          ∀ M ∈ F n, ∀ z : ℤ, ε < |x * (M : ℝ) - z| := by
    have hp : 0 < (q : ℝ) ^ n := pow_pos (by positivity) _
    have hqp : 0 < q := by omega
    have hwidth := width_pos hqp hc (n+1)
    have hm' (M : ℕ) (hM : M ∈ F n) : 0 < M ∧ 2*ε ≤ (M : ℝ) * width q c (n+1) := by
      have hMlo := (mem_frequencies.mp hM).1
      refine ⟨(by positivity : 0 < q ^ n).trans_le hMlo, ?_⟩
      calc
        _ = (q : ℝ) ^ n * width q c (n+1) := by
          dsimp [ε, width]
          rw [pow_succ]
          field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hMlo) hwidth.le
    have hcount :
        3 * ((4 * (b : ℝ) * width q c (n+1)) * (∑ M ∈ F n, (M : ℝ)) + 2 * (F n).card) ≤
          2 * (b : ℝ) := by
      have hbcast : 4 * (b : ℝ) = q := by exact_mod_cast hqb
      have hFc : ((F n).card : ℝ) ≤ (J : ℝ)*K := by exact_mod_cast (hF n).1
      have hFs : (∑ M ∈ F n, (M : ℝ)) ≤ 2*(K : ℝ)*(q : ℝ)^(n+1) := by
        have hcast : ((∑ M ∈ F n, M : ℕ) : ℝ) ≤ ((2*K*q^(n+1) : ℕ) : ℝ) := by
          exact_mod_cast (hF n).2
        push_cast at hcast
        exact hcast
      have hqbig' : 16*(K : ℝ)*J ≤ q := by exact_mod_cast hqbig
      have hproduct : width q c n * (2*(K : ℝ)*(q : ℝ)^(n+1)) = (q : ℝ)/24 := by
        dsimp [width, c]
        rw [pow_succ]
        field_simp
        norm_num
      rw [hbcast, width_succ hqp]
      calc
        _ ≤ 3 * (width q c n * (2*(K : ℝ)*(q : ℝ)^(n+1)) + 2*((J : ℝ)*K)) := by
          gcongr
          exact (width_pos hqp hc _).le
        _ ≤ _ := by rw [hproduct]; nlinarith only [hqbig', hbcast]
    simpa only [hqb] using choose_children b (by omega) (F n) a (width q c (n+1)) ε
      hwidth hε hεhalf hm' hcount
  choose child child_lt child_space child_safe using hchildren
  let X := {x : ℝ | ∀ n : ℕ, ∀ z : ℤ, ε < |x * (m n : ℝ) - z|}
  have hdim := full_dimension_of_children hb (by omega : 0 < q) hc hr hqrp
    child child_lt child_space (X := X)
  have hsub (l : ℕ → ℝ)
      (hl : ∀ n, ∃ i : Fin b, l (n+1) = l n + (child n (l n) i : ℝ) * width q c (n+1))
      (hpoint : ∀ n, l n ≤ sSup (range l) ∧ sSup (range l) ≤ l n + width q c n) :
      sSup (range l) ∈ X := by
    intro j z
    let n := Nat.log q (m j)
    have hmem : m j ∈ F n := mem_frequencies.mpr
      ⟨Nat.pow_log_le_self q (hm j).ne', Nat.lt_pow_succ_log_self hq _, mem_range_self j⟩
    obtain ⟨i, hi⟩ := hl n
    have hpoint' := hpoint (n+1)
    rw [hi] at hpoint'
    refine child_safe n (l n) i _ ⟨hpoint'.1, ?_⟩ _ hmem z
    linarith only [hpoint'.2]
  refine ⟨ε, hε, ?_⟩
  rw [ENNReal.ofReal_eq_coe_nnreal hrate.le]
  exact hdim hsub

lemma avoider_not_dense {m : ℕ → ℕ} {x ε : ℝ} (hε : 0 < ε)
    (havoid : ∀ n : ℕ, ∀ z : ℤ, ε < |x * (m n : ℝ) - z|) :
    ¬ Dense (range fun n => (↑(x * m n) : AddCircle (1 : ℝ))) := by
  intro hd
  have hcl := Metric.mem_closure_iff.mp (hd (0 : AddCircle (1 : ℝ))) ε hε
  obtain ⟨_, ⟨n, rfl⟩, hn⟩ := hcl
  rw [dist_zero_left, UnitAddCircle.norm_eq] at hn
  exact (havoid n _).not_ge hn.le

lemma pollington_de_mathan_bound (m : ℕ → ℕ) (hm : ∀ n, 0 < m n) (hlac : IsLacunary m) :
    dimH {ξ : ℝ | ¬ Dense (range fun n => (↑(ξ * m n) : AddCircle (1 : ℝ)))} = 1 := by
  let X := {ξ : ℝ | ¬ Dense (range fun n => (↑(ξ * m n) : AddCircle (1 : ℝ)))}
  have hu : dimH X ≤ (1 : ℝ≥0∞) := by
    exact (dimH_mono (subset_univ X)).trans_eq (by simp [Real.dimH_univ_eq_finrank])
  obtain ⟨K, hK, hfreq⟩ := lacunary_band_card m hm hlac
  have hlarge : ∀ᶠ J : ℕ in atTop, ENNReal.ofReal (1 - 2 / (J : ℝ)) ≤ dimH X := by
    filter_upwards [eventually_ge_atTop (max 4 (16*K))] with J hJ
    obtain ⟨ε, hε, hb⟩ := dim_lower_avoiders m hm hK hfreq J
      ((le_max_left _ _).trans hJ) ((le_max_right _ _).trans hJ)
    exact hb.trans (dimH_mono fun x hx => avoider_not_dense hε hx)
  have hinv : Tendsto (fun J : ℕ => ((J : ℝ)⁻¹)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun J : ℕ => 1 - 2 / (J : ℝ)) atTop (𝓝 1) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub (hinv.const_mul 2)
  have hlim' : Tendsto (fun J : ℕ => ENNReal.ofReal (1 - 2 / (J : ℝ))) atTop (𝓝 1) := by
    simpa only [Function.comp_apply, Function.comp_def, ENNReal.ofReal_one] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim
  exact hu.antisymm (le_of_tendsto_of_tendsto hlim' tendsto_const_nhds hlarge)

end LacunaryIntervals

theorem OMA.solution : type_of% @Bugeaud06.pollington_de_mathan :=
  LacunaryIntervals.pollington_de_mathan_bound