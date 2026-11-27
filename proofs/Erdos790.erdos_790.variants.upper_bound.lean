import FormalConjectures.ErdosProblems.«790»

/-! # Choi–Komlós–Szemerédi: `l(n) ≪ n / log n`

Following the informal argument of Choi, Komlós and Szemerédi (1975). Take `A` to be the levels
`2^j [t, 2t)` for `j ≤ s`, plus a few negative fillers. If `B ⊆ A` has no element that is a sum
of distinct others, build sets `B'_j` of popular pairwise sums from the larger parity class of
`B_j ∪ B'_j`. Every element of `B'_j` is a sum of at least two distinct elements of `B`
(choose representations greedily, since each has more than `2^(s+3)` of them), so `B'_j` misses
`B_j`. Splitting off the lowest and highest `M` elements counts at least `2|X| - O(M + tT/M)`
popular sums, so `|B_j| + |B'_j|` grows by `|B_j|` at each level up to an error. It stays at most
`t`, so `|B| ≤ 3t + s`. With `s ≈ log₂ n / 8`, `t = n/(s+1)` this gives the bound. -/

open Filter

namespace OMA.CKS790
open Erdos790

/-- Level `j` of the construction: the integers `2^j m` with `t ≤ m < 2t`. -/
def W (t j : ℕ) : Finset ℤ := (Finset.Ico t (2 * t)).image (fun m : ℕ => (2 : ℤ) ^ j * m)

lemma W_card (t j : ℕ) : (W t j).card = t := by
  unfold W
  rw [Finset.card_image_of_injective]
  · simp; omega
  · intro u v h
    have h2 : (2 : ℤ) ^ j ≠ 0 := by positivity
    simpa [h2] using h

lemma mem_W {t j : ℕ} {x : ℤ} : x ∈ W t j ↔ ∃ m : ℕ, t ≤ m ∧ m < 2 * t ∧ x = 2 ^ j * m := by
  unfold W
  simp only [Finset.mem_image, Finset.mem_Ico]
  constructor
  · rintro ⟨m, ⟨h1, h2⟩, rfl⟩; exact ⟨m, h1, h2, rfl⟩
  · rintro ⟨m, h1, h2, rfl⟩; exact ⟨m, ⟨h1, h2⟩, rfl⟩

lemma W_pos {t j : ℕ} {x : ℤ} (hx : x ∈ W t j) (ht : 1 ≤ t) : 0 < x := by
  obtain ⟨m, h1, -, rfl⟩ := mem_W.mp hx
  have : (0 : ℤ) < m := by exact_mod_cast (show 0 < m by omega)
  positivity

lemma W_bounds {t j : ℕ} {x : ℤ} (hx : x ∈ W t j) :
    2 ^ j * (t : ℤ) ≤ x ∧ x < 2 ^ j * (2 * t : ℤ) := by
  obtain ⟨m, h1, h2, rfl⟩ := mem_W.mp hx
  have h1' : (t : ℤ) ≤ m := by exact_mod_cast h1
  have h2' : (m : ℤ) < 2 * t := by exact_mod_cast h2
  have hp : (0 : ℤ) < 2 ^ j := by positivity
  constructor <;> nlinarith

lemma W_disj {t i j : ℕ} (hij : i ≠ j) : Disjoint (W t i) (W t j) := by
  rw [Finset.disjoint_left]
  intro x hi hj
  obtain ⟨a1, a2⟩ := W_bounds hi
  obtain ⟨b1, b2⟩ := W_bounds hj
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · have : (2 : ℤ) ^ (i + 1) ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) h
    have ht : (0 : ℤ) ≤ t := by positivity
    rw [pow_succ] at this
    nlinarith
  · have : (2 : ℤ) ^ (j + 1) ≤ 2 ^ i := pow_le_pow_right₀ (by norm_num) h
    have ht : (0 : ℤ) ≤ t := by positivity
    rw [pow_succ] at this
    nlinarith

/-- The larger of the two parity classes (of `x / 2^j`) of `R`. -/
def par (j : ℕ) (R : Finset ℤ) : Finset ℤ :=
  if (R.filter (fun x => ¬ Even (x / 2 ^ j))).card ≤ (R.filter (fun x => Even (x / 2 ^ j))).card
  then R.filter (fun x => Even (x / 2 ^ j)) else R.filter (fun x => ¬ Even (x / 2 ^ j))

lemma par_sub (j : ℕ) (R : Finset ℤ) : par j R ⊆ R := by
  unfold par; split_ifs <;> exact Finset.filter_subset _ _

lemma par_card (j : ℕ) (R : Finset ℤ) : R.card ≤ 2 * (par j R).card := by
  have h := Finset.card_filter_add_card_filter_not (s := R) (fun x => Even (x / 2 ^ j))
  unfold par; split_ifs with h' <;> omega

lemma par_parity (j : ℕ) (R : Finset ℤ) {a b : ℤ} (ha : a ∈ par j R) (hb : b ∈ par j R) :
    (Even (a / 2 ^ j) ↔ Even (b / 2 ^ j)) := by
  unfold par at ha hb
  split_ifs at ha hb <;> simp only [Finset.mem_filter] at ha hb <;> tauto

lemma sum_mem_W {t j : ℕ} {R : Finset ℤ} (hR : R ⊆ W t j) {a b : ℤ}
    (ha : a ∈ par j R) (hb : b ∈ par j R) : a + b ∈ W t (j + 1) := by
  have hp := par_parity j R ha hb
  obtain ⟨m, h1, h2, rfl⟩ := mem_W.mp (hR (par_sub j R ha))
  obtain ⟨m', h1', h2', rfl⟩ := mem_W.mp (hR (par_sub j R hb))
  have h2j : (2 : ℤ) ^ j ≠ 0 := by positivity
  rw [Int.mul_ediv_cancel_left _ h2j, Int.mul_ediv_cancel_left _ h2j] at hp
  simp only [Int.even_coe_nat] at hp
  have hev : Even (m + m') := by
    rcases Nat.even_or_odd m with h | h
    · exact h.add (hp.mp h)
    · have : Odd m' := Nat.not_even_iff_odd.mp (fun h' => (Nat.not_even_iff_odd.mpr h) (hp.mpr h'))
      exact h.add_odd this
  obtain ⟨k, hk⟩ := hev
  refine mem_W.mpr ⟨k, by omega, by omega, ?_⟩
  rw [← mul_add, pow_succ]
  have : ((m : ℤ) + m') = 2 * k := by exact_mod_cast (by omega : m + m' = 2 * k)
  rw [this]; ring

/-- Number of representations `x = a + (x - a)` with `a ≠ x - a`, both in `X`. -/
def rep (X : Finset ℤ) (x : ℤ) : ℕ := (X.filter (fun a => x - a ∈ X ∧ x - a ≠ a)).card

/-- Sums with at least `T` representations. -/
def pop (T : ℕ) (X : Finset ℤ) : Finset ℤ :=
  ((X ×ˢ X).image (fun p => p.1 + p.2)).filter (fun x => T ≤ rep X x)

/-- The sets `B'_j` of the proof. -/
def Bp (t T : ℕ) (B : Finset ℤ) : ℕ → Finset ℤ
  | 0 => ∅
  | j + 1 => pop T (par j (B ∩ W t j ∪ Bp t T B j))

lemma Bp_sub (t T : ℕ) (B : Finset ℤ) : ∀ j, Bp t T B j ⊆ W t j
  | 0 => by simp [Bp]
  | j + 1 => by
    intro x hx
    simp only [Bp, pop, Finset.mem_filter, Finset.mem_image, Finset.mem_product] at hx
    obtain ⟨⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩, -⟩ := hx
    have hR : B ∩ W t j ∪ Bp t T B j ⊆ W t j :=
      Finset.union_subset Finset.inter_subset_right (Bp_sub t T B j)
    exact sum_mem_W hR ha hb

lemma rep_tree {t T s : ℕ} {B : Finset ℤ} (ht : 1 ≤ t) (hT : 2 ^ (s + 3) < T) :
    ∀ j, ∀ x ∈ Bp t T B j, ∀ U : Finset ℤ, U.card + 2 ^ (j + 1) ≤ 2 ^ (s + 2) →
      ∃ S ⊆ B, Disjoint S U ∧ ∑ y ∈ S, y = x ∧ 2 ≤ S.card ∧ S.card ≤ 2 ^ j ∧ ∀ y ∈ S, 0 < y
  | 0 => by intro x hx; simp [Bp] at hx
  | j + 1 => by
    intro x hx U hU
    have ih := rep_tree (B := B) ht hT j
    have helper : ∀ a ∈ B ∩ W t j ∪ Bp t T B j, ∀ V : Finset ℤ,
        V.card + 2 ^ (j + 1) ≤ 2 ^ (s + 2) → a ∉ V →
        ∃ S ⊆ B, Disjoint S V ∧ ∑ y ∈ S, y = a ∧ 1 ≤ S.card ∧ S.card ≤ 2 ^ j ∧
          ∀ y ∈ S, 0 < y := by
      intro a ha V hV haV
      rcases Finset.mem_union.mp ha with h | h
      · obtain ⟨hB, hW⟩ := Finset.mem_inter.mp h
        refine ⟨{a}, by simpa using hB, by simpa using haV, by simp, by simp, ?_, ?_⟩
        · simp only [Finset.card_singleton]; exact Nat.one_le_two_pow
        · intro y hy; rw [Finset.mem_singleton.mp hy]; exact W_pos hW ht
      · obtain ⟨S, h1, h2, h3, h4, h5, h6⟩ := ih a h V hV
        exact ⟨S, h1, h2, h3, by omega, h5, h6⟩
    simp only [Bp, pop, Finset.mem_filter] at hx
    obtain ⟨-, hrep⟩ := hx
    set X := par j (B ∩ W t j ∪ Bp t T B j) with hX
    have hbad : (U ∪ U.image (fun u => x - u)).card ≤ 2 * U.card := by
      have := Finset.card_union_le U (U.image (fun u => x - u))
      have := Finset.card_image_le (s := U) (f := fun u => x - u)
      omega
    have hp1 : 1 ≤ 2 ^ (j + 1) := Nat.one_le_two_pow
    have hpj : 2 ^ (j + 1 + 1) = 2 * 2 ^ (j + 1) := by ring
    have hps : 2 ^ (s + 3) = 2 * 2 ^ (s + 2) := by ring
    have hlt : (U ∪ U.image (fun u => x - u)).card <
        (X.filter (fun a => x - a ∈ X ∧ x - a ≠ a)).card := by
      have : (X.filter (fun a => x - a ∈ X ∧ x - a ≠ a)).card = rep X x := rfl
      omega
    obtain ⟨a, haF, hanot⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    simp only [Finset.mem_filter] at haF
    obtain ⟨haX, hbX, hne⟩ := haF
    have haU : a ∉ U := fun h => hanot (Finset.mem_union_left _ h)
    have hbU : x - a ∉ U := fun h => hanot (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨x - a, h, by ring⟩))
    obtain ⟨Sa, hSaB, hSaV, hSas, hSa1, hSa2, hSap⟩ := helper a (par_sub _ _ haX)
      (insert (x - a) U) (by have := Finset.card_insert_le (x - a) U; omega)
      (by simp only [Finset.mem_insert, not_or]; exact ⟨fun h => hne h.symm, haU⟩)
    have hbSa : x - a ∉ Sa := fun h =>
      Finset.disjoint_left.mp hSaV h (Finset.mem_insert_self _ _)
    obtain ⟨Sb, hSbB, hSbV, hSbs, hSb1, hSb2, hSbp⟩ := helper (x - a) (par_sub _ _ hbX)
      (U ∪ Sa) (by have := Finset.card_union_le U Sa; have : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
                   omega)
      (by simp only [Finset.mem_union, not_or]; exact ⟨hbU, hbSa⟩)
    have hdab : Disjoint Sa Sb :=
      (Finset.disjoint_of_subset_right Finset.subset_union_right hSbV).symm
    refine ⟨Sa ∪ Sb, Finset.union_subset hSaB hSbB, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Finset.disjoint_union_left]
      exact ⟨Finset.disjoint_of_subset_right (Finset.subset_insert _ _) hSaV,
        Finset.disjoint_of_subset_right Finset.subset_union_left hSbV⟩
    · rw [Finset.sum_union hdab, hSas, hSbs]; ring
    · rw [Finset.card_union_of_disjoint hdab]; omega
    · rw [Finset.card_union_of_disjoint hdab]
      have : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
      omega
    · intro y hy
      rcases Finset.mem_union.mp hy with h | h
      · exact hSap y h
      · exact hSbp y h

lemma level_disj {t T s : ℕ} {B : Finset ℤ} (ht : 1 ≤ t) (hT : 2 ^ (s + 3) < T)
    (hB : DistinctSubsetSumFree B) (j : ℕ) (hj : j ≤ s) :
    Disjoint (B ∩ W t j) (Bp t T B j) := by
  rw [Finset.disjoint_left]
  intro y hy hy'
  obtain ⟨S, hSB, -, hsum, h2, -, hpos⟩ := rep_tree (B := B) ht hT j y hy' ∅
    (by simp only [Finset.card_empty, zero_add]; exact pow_le_pow_right₀ (by norm_num) (by omega))
  have hyS : y ∉ S := by
    intro hyS
    have e := Finset.add_sum_erase S (fun z => z) hyS
    have hne : (S.erase y).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hyS]; omega
    have : 0 < ∑ z ∈ S.erase y, z :=
      Finset.sum_pos (fun z hz => hpos z (Finset.mem_of_mem_erase hz)) hne
    linarith
  exact hB y (Finset.mem_inter.mp hy).1 S
    (fun z hz => Finset.mem_erase.mpr ⟨fun h => hyS (h ▸ hz), hSB hz⟩) h2 hsum

lemma low (X : Finset ℤ) : ∀ M ≤ X.card, ∃ S ⊆ X, S.card = M ∧
    ∀ a ∈ S, ∀ b ∈ X, b ∉ S → a < b := by
  intro M
  induction M with
  | zero => intro _; exact ⟨∅, by simp, by simp, by simp⟩
  | succ M ih =>
    intro hM
    obtain ⟨S, hSX, hSc, hS⟩ := ih (by omega)
    have hne : (X \ S).Nonempty := by
      rw [← Finset.card_pos, Finset.card_sdiff_of_subset hSX]; omega
    set c := (X \ S).min' hne
    have hc : c ∈ X \ S := Finset.min'_mem _ _
    have hcS : c ∉ S := (Finset.mem_sdiff.mp hc).2
    refine ⟨insert c S, Finset.insert_subset (Finset.mem_sdiff.mp hc).1 hSX, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hcS, hSc]
    · intro a ha b hb hbn
      rw [Finset.mem_insert, not_or] at hbn
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact lt_of_le_of_ne (Finset.min'_le _ _ (Finset.mem_sdiff.mpr ⟨hb, hbn.2⟩))
          (fun h => hbn.1 h.symm)
      · exact hS a ha b hb hbn.2

lemma high (X : Finset ℤ) : ∀ M ≤ X.card, ∃ S ⊆ X, S.card = M ∧
    ∀ a ∈ S, ∀ b ∈ X, b ∉ S → b < a := by
  intro M
  induction M with
  | zero => intro _; exact ⟨∅, by simp, by simp, by simp⟩
  | succ M ih =>
    intro hM
    obtain ⟨S, hSX, hSc, hS⟩ := ih (by omega)
    have hne : (X \ S).Nonempty := by
      rw [← Finset.card_pos, Finset.card_sdiff_of_subset hSX]; omega
    set c := (X \ S).max' hne
    have hc : c ∈ X \ S := Finset.max'_mem _ _
    have hcS : c ∉ S := (Finset.mem_sdiff.mp hc).2
    refine ⟨insert c S, Finset.insert_subset (Finset.mem_sdiff.mp hc).1 hSX, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hcS, hSc]
    · intro a ha b hb hbn
      rw [Finset.mem_insert, not_or] at hbn
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact lt_of_le_of_ne (Finset.le_max' _ _ (Finset.mem_sdiff.mpr ⟨hb, hbn.2⟩)) hbn.1
      · exact hS a ha b hb hbn.2

lemma count_side (X P Q Wn : Finset ℤ) (T : ℕ) (hP : P ⊆ X) (hQ : Q ⊆ X)
    (hPQ : Disjoint P Q) (hW : ∀ a ∈ X, ∀ b ∈ X, a + b ∈ Wn) :
    P.card * Q.card ≤
      ((P ×ˢ Q).image (fun p => p.1 + p.2) ∩ pop T X).card * P.card + Wn.card * T := by
  set f : ℤ × ℤ → ℤ := fun p => p.1 + p.2
  set I := (P ×ˢ Q).image f
  rw [← Finset.card_product, Finset.card_eq_sum_card_image f (P ×ˢ Q),
    ← Finset.sum_filter_add_sum_filter_not I (fun x => x ∈ pop T X)]
  gcongr
  · rw [← Finset.filter_mem_eq_inter]
    apply Finset.sum_le_card_nsmul
    intro x hx
    apply Finset.card_le_card_of_injOn Prod.fst
    · intro p hp
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product] at hp
      exact hp.1.1
    · intro p hp q hq h
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product] at hp hq
      have : p.2 = q.2 := by
        have e1 := hp.2; have e2 := hq.2; simp only [f] at e1 e2; rw [h] at e1; linarith
      exact Prod.ext h this
  · have hIW : I ⊆ Wn := by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      rw [Finset.mem_product] at hp
      exact hW _ (hP hp.1) _ (hQ hp.2)
    calc ∑ x ∈ I.filter (fun x => x ∉ pop T X), ((P ×ˢ Q).filter (fun p => f p = x)).card
        ≤ ∑ x ∈ I.filter (fun x => x ∉ pop T X), T := by
          apply Finset.sum_le_sum
          intro x hx
          rw [Finset.mem_filter] at hx
          have hxI : x ∈ (X ×ˢ X).image (fun p => p.1 + p.2) := by
            obtain ⟨p, hp, hpx⟩ := Finset.mem_image.mp hx.1
            rw [Finset.mem_product] at hp
            exact Finset.mem_image.mpr ⟨p, Finset.mem_product.mpr ⟨hP hp.1, hQ hp.2⟩, hpx⟩
          have hlt : rep X x < T := by
            by_contra hc
            exact hx.2 (Finset.mem_filter.mpr ⟨hxI, not_lt.mp hc⟩)
          refine le_trans ?_ hlt.le
          apply Finset.card_le_card_of_injOn Prod.fst
          · intro p hp
            simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product] at hp
            simp only [Finset.coe_filter, Set.mem_setOf_eq]
            have e : x - p.1 = p.2 := by have := hp.2; simp only [f] at this; linarith
            refine ⟨hP hp.1.1, by rw [e]; exact hQ hp.1.2, ?_⟩
            rw [e]
            intro h
            exact Finset.disjoint_left.mp hPQ hp.1.1 (h ▸ hp.1.2)
          · intro p hp q hq h
            simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product] at hp hq
            have : p.2 = q.2 := by
              have e1 := hp.2; have e2 := hq.2; simp only [f] at e1 e2; rw [h] at e1; linarith
            exact Prod.ext h this
      _ = (I.filter (fun x => x ∉ pop T X)).card * T := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ Wn.card * T := by
          gcongr
          exact (Finset.filter_subset (fun x => x ∉ pop T X) I).trans hIW

lemma pop_big (X Wn : Finset ℤ) (T M : ℕ) (hW : ∀ a ∈ X, ∀ b ∈ X, a + b ∈ Wn) :
    2 * M * X.card ≤ M * (pop T X).card + 4 * M * M + 2 * Wn.card * T := by
  by_cases hM : 2 * M ≤ X.card
  swap
  · push Not at hM
    nlinarith
  obtain ⟨S1, hS1X, hS1c, hS1⟩ := low X M (by omega)
  have hc1 : (X \ S1).card = X.card - M := by rw [Finset.card_sdiff_of_subset hS1X, hS1c]
  obtain ⟨S2, hS2X, hS2c, hS2⟩ := high (X \ S1) M (by omega)
  set S3 := (X \ S1) \ S2
  have hc3 : S3.card = X.card - 2 * M := by
    rw [Finset.card_sdiff_of_subset hS2X, hc1, hS2c]; omega
  have hS3X : S3 ⊆ X := fun x hx => (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hx).1).1
  have hS2X' : S2 ⊆ X := fun x hx => (Finset.mem_sdiff.mp (hS2X hx)).1
  have hd23 : Disjoint S2 S3 := Finset.disjoint_left.mpr fun x h2 h3 =>
    (Finset.mem_sdiff.mp h3).2 h2
  have hd13 : Disjoint S1 S3 := Finset.disjoint_left.mpr fun x h1 h3 =>
    (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp h3).1).2 h1
  have hA := count_side X S2 S3 Wn T hS2X' hS3X hd23 hW
  have hB := count_side X S1 S3 Wn T hS1X hS3X hd13 hW
  rw [hS2c] at hA
  rw [hS1c] at hB
  set I13 := (S1 ×ˢ S3).image (fun p => p.1 + p.2) ∩ pop T X
  set I23 := (S2 ×ˢ S3).image (fun p => p.1 + p.2) ∩ pop T X
  have hdisj : Disjoint I13 I23 := by
    rw [Finset.disjoint_left]
    intro x h13 h23
    obtain ⟨p, hp, hpx⟩ := Finset.mem_image.mp (Finset.mem_inter.mp h13).1
    obtain ⟨q, hq, hqx⟩ := Finset.mem_image.mp (Finset.mem_inter.mp h23).1
    rw [Finset.mem_product] at hp hq
    have h1 : p.1 < q.2 := hS1 p.1 hp.1 q.2 (hS3X hq.2)
      (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hq.2).1).2
    have h2 : p.2 < q.1 := hS2 q.1 hq.1 p.2 (Finset.mem_sdiff.mp hp.2).1
      (Finset.mem_sdiff.mp hp.2).2
    have : p.1 + p.2 = q.1 + q.2 := by rw [hpx, hqx]
    linarith
  have hsub : I13 ∪ I23 ⊆ pop T X :=
    Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right
  have hC : I13.card + I23.card ≤ (pop T X).card := by
    rw [← Finset.card_union_of_disjoint hdisj]; exact Finset.card_le_card hsub
  have hX : X.card = S3.card + 2 * M := by omega
  have hC' : M * (I13.card + I23.card) ≤ M * (pop T X).card := Nat.mul_le_mul_left _ hC
  rw [hX]
  nlinarith

lemma chain {t T s M : ℕ} {B : Finset ℤ} (ht : 1 ≤ t) (hT : 2 ^ (s + 3) < T)
    (hB : DistinctSubsetSumFree B) :
    M * ∑ i ∈ Finset.range (s + 1), (B ∩ W t i).card ≤
      M * t + s * (4 * M * M + 2 * t * T) := by
  have hR : ∀ j ≤ s, (B ∩ W t j ∪ Bp t T B j).card = (B ∩ W t j).card + (Bp t T B j).card :=
    fun j hj => Finset.card_union_of_disjoint (level_disj ht hT hB j hj)
  have step : ∀ j, j + 1 ≤ s → M * (B ∩ W t j ∪ Bp t T B j).card ≤
      M * (Bp t T B (j + 1)).card + (4 * M * M + 2 * t * T) := by
    intro j hj
    set R := B ∩ W t j ∪ Bp t T B j
    have hRW : R ⊆ W t j := Finset.union_subset Finset.inter_subset_right (Bp_sub t T B j)
    have hp := pop_big (par j R) (W t (j + 1)) T M (fun a ha b hb => sum_mem_W hRW ha hb)
    rw [W_card] at hp
    have h2 := par_card j R
    have : M * R.card ≤ 2 * M * (par j R).card := by
      calc M * R.card ≤ M * (2 * (par j R).card) := Nat.mul_le_mul_left _ h2
        _ = 2 * M * (par j R).card := by ring
    show M * R.card ≤ M * (pop T (par j R)).card + (4 * M * M + 2 * t * T)
    omega
  have hch : ∀ j ≤ s, M * ∑ i ∈ Finset.range (j + 1), (B ∩ W t i).card ≤
      M * ((B ∩ W t j).card + (Bp t T B j).card) + j * (4 * M * M + 2 * t * T) := by
    intro j
    induction j with
    | zero => intro _; simp [Bp]
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      have h2 := step j hj
      rw [hR j (by omega)] at h2
      rw [Finset.sum_range_succ, mul_add]
      nlinarith
  have hfin := hch s le_rfl
  have hRs : (B ∩ W t s).card + (Bp t T B s).card ≤ t := by
    rw [← hR s le_rfl]
    calc (B ∩ W t s ∪ Bp t T B s).card ≤ (W t s).card :=
          Finset.card_le_card (Finset.union_subset Finset.inter_subset_right (Bp_sub t T B s))
      _ = t := W_card t s
  have := Nat.mul_le_mul_left M hRs
  omega

lemma four_pow (s : ℕ) (hs : 4 ≤ s) : 32 * s ≤ 4 ^ s := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ s hs ih => rw [pow_succ]; omega

lemma numeric (s t : ℕ) (hs : 4 ≤ s) (hts : 4 * s * 2 ^ (3 * s) ≤ t) :
    s * (4 * 2 ^ (3 * s) * 2 ^ (3 * s) + 2 * t * (2 ^ (s + 3) + 1)) ≤ 2 * 2 ^ (3 * s) * t := by
  have h4 := four_pow s hs
  have e : 2 ^ (3 * s) = 4 ^ s * 2 ^ s := by
    rw [show 3 * s = 2 * s + s by ring, pow_add, pow_mul]; norm_num
  have hA : s * (4 * 2 ^ (3 * s) * 2 ^ (3 * s)) ≤ 2 ^ (3 * s) * t := by
    calc s * (4 * 2 ^ (3 * s) * 2 ^ (3 * s)) = 2 ^ (3 * s) * (4 * s * 2 ^ (3 * s)) := by ring
      _ ≤ 2 ^ (3 * s) * t := Nat.mul_le_mul_left _ hts
  have hB : s * (2 * t * (2 ^ (s + 3) + 1)) ≤ 2 ^ (3 * s) * t := by
    have h1 : 2 ^ (s + 3) + 1 ≤ 16 * 2 ^ s := by
      have : 2 ^ (s + 3) = 8 * 2 ^ s := by ring
      have : 1 ≤ 2 ^ s := Nat.one_le_two_pow
      omega
    calc s * (2 * t * (2 ^ (s + 3) + 1)) ≤ s * (2 * t * (16 * 2 ^ s)) := by gcongr
      _ = (32 * s) * 2 ^ s * t := by ring
      _ ≤ 4 ^ s * 2 ^ s * t := by gcongr
      _ = 2 ^ (3 * s) * t := by rw [e]
  nlinarith

lemma guarantees_mono {n k K : ℕ} (h : Guarantees n K) (hk : k ≤ K) : Guarantees n k := by
  intro A hA
  obtain ⟨B, h1, h2, h3⟩ := h A hA
  exact ⟨B, h1, h2, le_trans hk h3⟩

lemma l_le (n t s : ℕ) (ht : 1 ≤ t) (hs : 4 ≤ s) (hts : 4 * s * 2 ^ (3 * s) ≤ t)
    (hn1 : t * (s + 1) ≤ n) (hn2 : n ≤ t * (s + 1) + s) : l n ≤ 3 * t + s := by
  set T := 2 ^ (s + 3) + 1
  set M := 2 ^ (3 * s)
  set F : Finset ℤ := (Finset.range (n - t * (s + 1))).image (fun i : ℕ => -(i : ℤ) - 1)
  set A : Finset ℤ := (Finset.range (s + 1)).biUnion (W t) ∪ F
  have hFcard : F.card = n - t * (s + 1) := by
    rw [Finset.card_image_of_injective _ (fun u v h => by simpa using h), Finset.card_range]
  have hdisjW : ((Finset.range (s + 1)) : Set ℕ).PairwiseDisjoint (W t) :=
    fun i _ j _ hij => W_disj hij
  have hUcard : ((Finset.range (s + 1)).biUnion (W t)).card = t * (s + 1) := by
    rw [Finset.card_biUnion hdisjW]
    simp [W_card, mul_comm]
  have hdisjF : Disjoint ((Finset.range (s + 1)).biUnion (W t)) F := by
    rw [Finset.disjoint_left]
    intro x hx hxF
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hxF
    have := W_pos hi ht
    omega
  have hAcard : A.card = n := by
    rw [Finset.card_union_of_disjoint hdisjF, hUcard, hFcard]; omega
  have hnot : ¬ Guarantees n (3 * t + s + 1) := by
    intro hG
    obtain ⟨B, hBA, hB, hcard⟩ := hG A hAcard
    have hT : 2 ^ (s + 3) < T := by omega
    have hc := chain (M := M) ht hT hB
    have hnum := numeric s t hs hts
    have hsum : ∑ i ∈ Finset.range (s + 1), (B ∩ W t i).card ≤ 3 * t := by
      have hM : 0 < M := by positivity
      have : M * ∑ i ∈ Finset.range (s + 1), (B ∩ W t i).card ≤ M * (3 * t) := by
        have : s * (4 * M * M + 2 * t * T) ≤ 2 * M * t := hnum
        nlinarith
      exact Nat.le_of_mul_le_mul_left this hM
    have hBsub : B ⊆ (Finset.range (s + 1)).biUnion (fun i => B ∩ W t i) ∪ F := by
      intro x hx
      rcases Finset.mem_union.mp (hBA hx) with h | h
      · obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp h
        exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_inter.mpr ⟨hx, hxi⟩⟩)
      · exact Finset.mem_union_right _ h
    have h1 := Finset.card_le_card hBsub
    have h2 := Finset.card_union_le ((Finset.range (s + 1)).biUnion (fun i => B ∩ W t i)) F
    have h3 := Finset.card_biUnion_le (s := Finset.range (s + 1)) (t := fun i => B ∩ W t i)
    omega
  classical
  by_contra hcon
  push Not at hcon
  have hP : Guarantees n (l n) := by
    refine Nat.findGreatest_of_ne_zero (n := n) ?_ (by omega)
    unfold l
    congr
  exact hnot (guarantees_mono hP (by omega))

theorem main : (fun n ↦ (l n : ℝ)) =O[atTop] (fun n : ℕ ↦ (n : ℝ) / Real.log n) := by
  refine Asymptotics.IsBigO.of_bound 32 ?_
  filter_upwards [eventually_ge_atTop (2 ^ 32)] with n hn
  set L := Nat.log 2 n with hL
  set s := L / 8 with hsdef
  set t := n / (s + 1) with htdef
  have hn0 : n ≠ 0 := by positivity
  have hL32 : 32 ≤ L := Nat.le_log_of_pow_le (by norm_num) hn
  have hs4 : 4 ≤ s := by omega
  have hpow : 2 ^ (8 * s) ≤ n :=
    le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) (Nat.pow_log_le_self 2 hn0)
  have hss : s < 2 ^ s := Nat.lt_two_pow_self
  have hkey : 4 * s * 2 ^ (3 * s) * (s + 1) ≤ 2 ^ (8 * s) := by
    have e : 2 ^ (8 * s) = 2 ^ (3 * s) * (2 ^ s * 2 ^ s * 2 ^ (3 * s)) := by
      rw [← pow_add, ← pow_add, ← pow_add]; ring_nf
    have h8 : 8 ≤ 2 ^ (3 * s) := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (3 * s) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [e]
    have : 4 * s * (s + 1) ≤ 2 ^ s * 2 ^ s * 2 ^ (3 * s) := by
      have h1 : s + 1 ≤ 2 ^ s := hss
      have h2 : 4 * s ≤ 2 ^ s * 8 := by omega
      calc 4 * s * (s + 1) ≤ (2 ^ s * 8) * 2 ^ s := Nat.mul_le_mul h2 h1
        _ = 2 ^ s * 2 ^ s * 8 := by ring
        _ ≤ 2 ^ s * 2 ^ s * 2 ^ (3 * s) := Nat.mul_le_mul_left _ h8
    calc 4 * s * 2 ^ (3 * s) * (s + 1) = 2 ^ (3 * s) * (4 * s * (s + 1)) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ this
  have hts : 4 * s * 2 ^ (3 * s) ≤ t := by
    rw [htdef, Nat.le_div_iff_mul_le (by omega)]; omega
  have ht1 : 1 ≤ t := by
    have : 1 ≤ 4 * s * 2 ^ (3 * s) := by
      have : 1 ≤ 2 ^ (3 * s) := Nat.one_le_two_pow
      nlinarith
    omega
  have hn1 : t * (s + 1) ≤ n := Nat.div_mul_le_self n (s + 1)
  have hn2 : n ≤ t * (s + 1) + s := by
    have := Nat.div_add_mod n (s + 1)
    have := Nat.mod_lt n (show 0 < s + 1 by omega)
    rw [htdef]; nlinarith
  have hl := l_le n t s ht1 hs4 hts hn1 hn2
  have hst : s ≤ t := by
    have : s ≤ 4 * s * 2 ^ (3 * s) := by
      have : 1 ≤ 2 ^ (3 * s) := Nat.one_le_two_pow
      nlinarith
    omega
  have hl4 : (l n : ℝ) ≤ 4 * t := by exact_mod_cast (by omega : l n ≤ 4 * t)
  have hnR : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hlogpos : 0 < Real.log n := Real.log_pos hnR
  have hlog : Real.log n ≤ 8 * (s + 1) := by
    have hlt : n < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
    have hlt' : (n : ℝ) < 2 ^ (L + 1) := by exact_mod_cast hlt
    have h1 := Real.log_lt_log (by positivity) hlt'
    rw [Real.log_pow] at h1
    have h2 := Real.log_two_lt_d9
    have h3 : ((L + 1 : ℕ) : ℝ) ≤ 8 * ((s : ℝ) + 1) := by
      have : L + 1 ≤ 8 * (s + 1) := by omega
      exact_mod_cast this
    have h4 : (0 : ℝ) ≤ ((L + 1 : ℕ) : ℝ) := by positivity
    nlinarith
  have htR : (t : ℝ) * (s + 1) ≤ n := by exact_mod_cast hn1
  rw [Real.norm_natCast, Real.norm_of_nonneg (div_nonneg (by positivity) hlogpos.le)]
  rw [mul_div_assoc', le_div_iff₀ hlogpos]
  have hsR : (0 : ℝ) ≤ s := by positivity
  have htR0 : (0 : ℝ) ≤ t := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hlog htR0]

end OMA.CKS790

theorem OMA.solution : type_of% @Erdos790.erdos_790.variants.upper_bound := OMA.CKS790.main
