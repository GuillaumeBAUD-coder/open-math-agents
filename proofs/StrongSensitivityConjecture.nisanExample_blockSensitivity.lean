import FormalConjectures.Paper.StrongSensitivityConjecture

-- Problem: Strong Sensitivity Conjecture (bs(f) <= s(f)^2) — nisanExample blockSensitivity
-- Upstream: formal-conjectures FormalConjectures/Paper/StrongSensitivityConjecture.lean:145 (declaration StrongSensitivityConjecture.nisanExample_blockSensitivity)
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- This formalises the classical computation of the block sensitivity of Nisan's symmetric example
-- (Nisan 1989). No new mathematical result is claimed.
-- Proof idea (n = 4m): flipping a block B with a one-bits and b zero-bits moves the weight w to
-- w - a + b. Disjoint blocks satisfy sum a <= #ones and sum b <= #zeros. If w = 2m every sensitive
-- block has 2 <= 2a + b, if w = 2m + 1 it has 2 <= a + 2b, if w < 2m it has 2m - w <= b, and if
-- w > 2m + 1 it has w - 2m - 1 <= a; summing gives at most 3m blocks in each case (the last case
-- uses m >= 2). For the lower bound take w = 2m: the 2m one-bits as singletons and m disjoint pairs
-- of zero-bits.
-- The predicate AccW and the lemma nisan_iff are adapted from the accepted proof of
-- StrongSensitivityConjecture.nisanExample_sensitivity in this repository (by @niclorusso).

namespace OMA.NisanBlockSensitivity

open Finset StrongSensitivityConjecture

/-- The accepting condition of `nisanExample n`, on the Hamming weight `w`. -/
def AccW (n w : ℕ) : Prop := 2 * w = n ∨ 2 * w = n + 2

instance (n w : ℕ) : Decidable (AccW n w) := by unfold AccW; infer_instance

-- adapted from the accepted proof of nisanExample_sensitivity (by @niclorusso)
lemma nisan_iff {n : ℕ} (x : Fin n → Bool) :
    nisanExample n x = true ↔ AccW n #{j | x j} := by
  simp only [nisanExample, decide_eq_true_eq, Finset.mem_insert, Finset.mem_singleton, AccW]
  have e1 : ((#{j | x j} : ℕ) : ℚ) = (n : ℚ) / 2 ↔ 2 * #{j | x j} = n := by
    constructor
    · intro h
      have h2 : (((2 * #{j | x j} : ℕ)) : ℚ) = n := by push_cast; linarith
      exact_mod_cast h2
    · intro h
      have h2 : (((2 * #{j | x j} : ℕ)) : ℚ) = n := by exact_mod_cast h
      push_cast at h2; linarith
  have e2 : ((#{j | x j} : ℕ) : ℚ) = (n : ℚ) / 2 + 1 ↔ 2 * #{j | x j} = n + 2 := by
    constructor
    · intro h
      have h2 : (((2 * #{j | x j} : ℕ)) : ℚ) = ((n + 2 : ℕ) : ℚ) := by push_cast; linarith
      exact_mod_cast h2
    · intro h
      have h2 : (((2 * #{j | x j} : ℕ)) : ℚ) = ((n + 2 : ℕ) : ℚ) := by exact_mod_cast h
      push_cast at h2; linarith
  rw [e1, e2]

/-- Flipping a block: new weight + (ones in B) = old weight + (zeros in B). -/
lemma weight_flip {n : ℕ} (x : Fin n → Bool) (B : Finset (Fin n)) :
    #{j | flip x B j} + (B.filter fun j => x j = true).card =
      #{j | x j} + (B.filter fun j => x j = false).card := by
  have h1 := card_filter_add_card_filter_not
    (s := (univ.filter fun j => flip x B j = true)) (fun j => j ∈ B)
  have h2 := card_filter_add_card_filter_not
    (s := (univ.filter fun j => x j = true)) (fun j => j ∈ B)
  have e1 : ((univ.filter fun j => flip x B j = true).filter fun j => j ∈ B) =
      B.filter fun j => x j = false := by
    ext j; by_cases hj : j ∈ B <;> simp [StrongSensitivityConjecture.flip, hj]
  have e2 : ((univ.filter fun j => flip x B j = true).filter fun j => ¬ j ∈ B) =
      ((univ.filter fun j => x j = true).filter fun j => ¬ j ∈ B) := by
    ext j; by_cases hj : j ∈ B <;> simp [StrongSensitivityConjecture.flip, hj]
  have e3 : ((univ.filter fun j => x j = true).filter fun j => j ∈ B) =
      B.filter fun j => x j = true := by
    ext j; by_cases hj : j ∈ B <;> simp [hj]
  rw [e1, e2] at h1
  rw [e3] at h2
  omega

/-- Disjoint blocks: the counts of a fixed kind of coordinate add up to at most the total. -/
lemma sum_card_filter_le {n : ℕ} (cB : Finset (Finset (Fin n)))
    (hd : (cB : Set (Finset (Fin n))).PairwiseDisjoint id) (p : Fin n → Prop)
    [DecidablePred p] :
    ∑ B ∈ cB, (B.filter p).card ≤ (univ.filter p).card := by
  rw [← card_biUnion]
  · apply card_le_card
    intro j hj
    simp only [mem_biUnion, mem_filter] at hj
    obtain ⟨B, -, -, hp⟩ := hj
    simp [hp]
  · intro B hB C hC hBC
    exact disjoint_filter_filter (hd hB hC hBC)

lemma sum_bound {ι : Type*} (s : Finset ι) (a b : ι → ℕ) (α β c : ℕ)
    (h : ∀ i ∈ s, c ≤ α * a i + β * b i) :
    s.card * c ≤ α * ∑ i ∈ s, a i + β * ∑ i ∈ s, b i := by
  calc s.card * c = ∑ _i ∈ s, c := by rw [sum_const, smul_eq_mul]
    _ ≤ ∑ i ∈ s, (α * a i + β * b i) := sum_le_sum h
    _ = _ := by rw [sum_add_distrib, mul_sum, mul_sum]

lemma bsAt_le (m : ℕ) (hm : 2 ≤ m) (x : Fin (4 * m) → Bool) :
    blockSensitivityAt (nisanExample (4 * m)) x ≤ 3 * m := by
  classical
  unfold blockSensitivityAt
  apply Finset.sup_le
  intro cB hcB
  obtain ⟨hd, hs⟩ := (mem_filter.mp hcB).2
  have hA := sum_card_filter_le cB hd (fun j => x j = true)
  have hZ := sum_card_filter_le cB hd (fun j => x j = false)
  have htot := card_filter_add_card_filter_not (s := (univ : Finset (Fin (4 * m))))
    (fun j => x j = true)
  simp only [card_univ, Fintype.card_fin, Bool.not_eq_true] at htot
  have hblk : ∀ B ∈ cB,
      #{j | flip x B j} + (B.filter fun j => x j = true).card =
        #{j | x j} + (B.filter fun j => x j = false).card ∧
      ¬ (AccW (4 * m) #{j | flip x B j} ↔ AccW (4 * m) #{j | x j}) := by
    intro B hB
    refine ⟨weight_flip x B, ?_⟩
    have := hs B hB
    rw [Ne, Bool.eq_iff_iff, nisan_iff, nisan_iff] at this
    exact this
  set W := #{j | x j} with hW
  set Z := (univ.filter fun j => x j = false).card with hZdef
  set SA := ∑ B ∈ cB, (B.filter fun j => x j = true).card with hSA
  set SB := ∑ B ∈ cB, (B.filter fun j => x j = false).card with hSB
  have hWZ : W + Z = 4 * m := htot
  by_cases hacc : AccW (4 * m) W
  · have hper : ∀ B ∈ cB, ¬ AccW (4 * m) #{j | flip x B j} := by
      intro B hB h
      exact (hblk B hB).2 (iff_of_true h hacc)
    rcases hacc with h0 | h0
    · have := sum_bound cB (fun B => (B.filter fun j => x j = true).card)
        (fun B => (B.filter fun j => x j = false).card) 2 1 2 (by
          intro B hB
          have h1 := (hblk B hB).1
          have h2 := hper B hB
          unfold AccW at h2
          omega)
      omega
    · have := sum_bound cB (fun B => (B.filter fun j => x j = true).card)
        (fun B => (B.filter fun j => x j = false).card) 1 2 2 (by
          intro B hB
          have h1 := (hblk B hB).1
          have h2 := hper B hB
          unfold AccW at h2
          omega)
      omega
  · have hper : ∀ B ∈ cB, AccW (4 * m) #{j | flip x B j} := by
      intro B hB
      by_contra h
      exact (hblk B hB).2 (iff_of_false h hacc)
    unfold AccW at hacc
    by_cases hlow : W < 2 * m
    · have := sum_bound cB (fun B => (B.filter fun j => x j = true).card)
        (fun B => (B.filter fun j => x j = false).card) 0 1 (2 * m - W) (by
          intro B hB
          have h1 := (hblk B hB).1
          have h2 := hper B hB
          unfold AccW at h2
          omega)
      have hk : cB.card * (2 * m - W) ≤ 2 * m + (2 * m - W) := by omega
      obtain ⟨d, hd'⟩ : ∃ d, 2 * m - W = d + 1 := ⟨2 * m - W - 1, by omega⟩
      rw [hd'] at hk
      by_contra hc
      push Not at hc
      nlinarith
    · have := sum_bound cB (fun B => (B.filter fun j => x j = true).card)
        (fun B => (B.filter fun j => x j = false).card) 1 0 (W - 2 * m - 1) (by
          intro B hB
          have h1 := (hblk B hB).1
          have h2 := hper B hB
          unfold AccW at h2
          omega)
      have hk : cB.card * (W - 2 * m - 1) ≤ (2 * m + 1) + (W - 2 * m - 1) := by omega
      obtain ⟨d, hd'⟩ : ∃ d, W - 2 * m - 1 = d + 1 := ⟨W - 2 * m - 2, by omega⟩
      rw [hd'] at hk
      by_contra hc
      push Not at hc
      nlinarith

/-- Labels of coordinates: one-bits (val < 2m) get their own label, zero-bits are paired. -/
def lab (m : ℕ) (i : Fin (4 * m)) : ℕ :=
  if i.val < 2 * m then i.val else 2 * m + (i.val - 2 * m) / 2

def blk (m k : ℕ) : Finset (Fin (4 * m)) := univ.filter fun i => lab m i = k

def xs (m : ℕ) : Fin (4 * m) → Bool := fun i => decide (i.val < 2 * m)

lemma mem_blk {m k : ℕ} {i : Fin (4 * m)} : i ∈ blk m k ↔ lab m i = k := by
  simp [blk]

def wit (m k : ℕ) (hk : k < 3 * m) : Fin (4 * m) :=
  ⟨if k < 2 * m then k else 2 * m + 2 * (k - 2 * m), by split_ifs <;> omega⟩

lemma lab_wit (m k : ℕ) (hk : k < 3 * m) : lab m (wit m k hk) = k := by
  unfold lab wit
  try simp only
  split_ifs <;> omega

lemma weight_xs (m : ℕ) : #{j | xs m j} = 2 * m := by
  have h : ((univ.filter fun j => xs m j = true).map Fin.valEmbedding) = range (2 * m) := by
    ext v
    simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_range, xs,
      decide_eq_true_eq]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro hv
      exact ⟨⟨v, by omega⟩, hv, rfl⟩
  have := congrArg Finset.card h
  rw [card_map, card_range] at this
  exact this

lemma sens_blk (m : ℕ) (hm : 2 ≤ m) (k : ℕ) (hk : k < 3 * m) :
    nisanExample (4 * m) (flip (xs m) (blk m k)) ≠ nisanExample (4 * m) (xs m) := by
  have hw := weight_flip (xs m) (blk m k)
  rw [weight_xs] at hw
  have hfl : ¬ AccW (4 * m) #{j | flip (xs m) (blk m k) j} := by
    by_cases hk2 : k < 2 * m
    · -- a singleton one-bit block: a >= 1, b = 0
      have ha : 1 ≤ ((blk m k).filter fun j => xs m j = true).card := by
        apply card_pos.mpr
        refine ⟨wit m k hk, ?_⟩
        rw [mem_filter, mem_blk, lab_wit]
        refine ⟨rfl, ?_⟩
        simp [xs, wit, hk2]
      have hb : ((blk m k).filter fun j => xs m j = false).card = 0 := by
        rw [card_eq_zero, filter_eq_empty_iff]
        intro i hi
        rw [mem_blk] at hi
        unfold lab at hi
        simp only [xs, decide_eq_false_iff_not, not_lt, not_le]
        split_ifs at hi <;> omega
      unfold AccW
      omega
    · -- a pair of zero-bits: a = 0, b >= 2
      have ha : ((blk m k).filter fun j => xs m j = true).card = 0 := by
        rw [card_eq_zero, filter_eq_empty_iff]
        intro i hi
        rw [mem_blk] at hi
        unfold lab at hi
        simp only [xs, decide_eq_true_eq, not_lt]
        split_ifs at hi <;> omega
      have hb : 2 ≤ ((blk m k).filter fun j => xs m j = false).card := by
        have hlt : 2 * m + 2 * (k - 2 * m) + 1 < 4 * m := by omega
        let i1 : Fin (4 * m) := ⟨2 * m + 2 * (k - 2 * m), by omega⟩
        let i2 : Fin (4 * m) := ⟨2 * m + 2 * (k - 2 * m) + 1, hlt⟩
        have h1 : i1 ∈ ((blk m k).filter fun j => xs m j = false) := by
          rw [mem_filter, mem_blk]
          unfold lab
          simp only [i1, xs, decide_eq_false_iff_not, not_lt]
          split_ifs <;> omega
        have h2 : i2 ∈ ((blk m k).filter fun j => xs m j = false) := by
          rw [mem_filter, mem_blk]
          unfold lab
          simp only [i2, xs, decide_eq_false_iff_not, not_lt]
          split_ifs <;> omega
        have hne : i1 ≠ i2 := by
          intro h
          have := congrArg Fin.val h
          simp only [i1, i2] at this
          omega
        exact one_lt_card.mpr ⟨i1, h1, i2, h2, hne⟩
      unfold AccW
      omega
  have hx : AccW (4 * m) #{j | xs m j} := by
    rw [weight_xs]; unfold AccW; omega
  rw [Ne, Bool.eq_iff_iff, nisan_iff, nisan_iff]
  intro h
  exact hfl (h.mpr hx)

lemma bsAt_ge (m : ℕ) (hm : 2 ≤ m) :
    3 * m ≤ blockSensitivityAt (nisanExample (4 * m)) (xs m) := by
  classical
  have hinj : Set.InjOn (blk m) (range (3 * m) : Set ℕ) := by
    intro k hk k' hk' h
    have hk3 : k < 3 * m := by simpa using hk
    have hw : wit m k hk3 ∈ blk m k' := by
      rw [← h, mem_blk, lab_wit]
    rw [mem_blk, lab_wit] at hw
    exact hw
  have hcard : ((range (3 * m)).image (blk m)).card = 3 * m := by
    rw [card_image_of_injOn hinj, card_range]
  have hvalid : IsValidBlockConfig (nisanExample (4 * m)) (xs m) ((range (3 * m)).image (blk m)) := by
    refine ⟨?_, ?_⟩
    · intro B hB C hC hBC
      simp only [coe_image, coe_range, Set.mem_image, Set.mem_Iio] at hB hC
      obtain ⟨k, -, rfl⟩ := hB
      obtain ⟨k', -, rfl⟩ := hC
      have hkk : k ≠ k' := fun h => hBC (by rw [h])
      show Disjoint (blk m k) (blk m k')
      rw [disjoint_left]
      intro i hi hi'
      rw [mem_blk] at hi hi'
      exact hkk (hi.symm.trans hi')
    · intro B hB
      rw [mem_image] at hB
      obtain ⟨k, hk, rfl⟩ := hB
      exact sens_blk m hm k (mem_range.mp hk)
  unfold blockSensitivityAt
  rw [← hcard]
  exact Finset.le_sup (f := card) (mem_filter.mpr ⟨mem_univ _, hvalid⟩)

end OMA.NisanBlockSensitivity

open Finset StrongSensitivityConjecture OMA.NisanBlockSensitivity in
theorem OMA.solution : type_of% @StrongSensitivityConjecture.nisanExample_blockSensitivity := by
  intro n hn hn_large
  obtain ⟨m, rfl⟩ := hn
  have hm : 2 ≤ m := by omega
  have hdiv : 3 * (4 * m) / 4 = 3 * m := by omega
  rw [hdiv]
  apply le_antisymm
  · exact Finset.sup_le fun x _ => bsAt_le m hm x
  · exact le_trans (bsAt_ge m hm) (Finset.le_sup (mem_univ (xs m)))
