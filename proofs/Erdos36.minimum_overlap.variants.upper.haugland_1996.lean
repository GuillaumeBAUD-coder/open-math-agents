import FormalConjectures.ErdosProblems.«36»

/-!
The new balanced word has 65,536 letters of each color and maximum directed overlap 25,034.
It was found using the symmetric step-function profile in Jan Kristian Haugland,
The minimum overlap problem revisited, arXiv:1609.08000, p. 2. The word is checked by
exact integer arithmetic in Lean, independently of how it was found.

The block-repetition argument and the digit-based verifier are adapted from @Genbox,
open-math-agents PR 1089, at https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1089.
The finite word and the final passage to the claimed bound are new.
-/

open Filter Erdos36
open scoped Topology BigOperators

namespace OverlapLimit

private def blocks (b : ℤ) (A : Finset ℤ) : Finset ℤ :=
  (A.product (Finset.Ico 0 b)).image fun p => 1 + b * p.1 + p.2

private theorem block_div {b x r : ℤ} (hb : 0 < b) (hr : 0 ≤ r ∧ r < b) :
    (1 + b * x + r - 1) / b = x := by
  rw [show 1 + b * x + r - 1 = r + b * x by omega,
    Int.add_mul_ediv_left _ _ hb.ne', Int.ediv_eq_zero_of_lt hr.1 hr.2, zero_add]

private theorem block_mod {b x r : ℤ} (hr : 0 ≤ r ∧ r < b) :
    (1 + b * x + r - 1) % b = r := by
  rw [show 1 + b * x + r - 1 = r + b * x by omega,
    Int.add_mul_emod_self_left, Int.emod_eq_of_lt hr.1 hr.2]

private theorem mem_blocks {b z : ℤ} (hb : 0 < b) {A : Finset ℤ} :
    z ∈ blocks b A ↔ (z - 1) / b ∈ A := by
  constructor
  · intro hz
    obtain ⟨⟨x, r⟩, hp, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hx, hr⟩ := Finset.mem_product.mp hp
    rw [block_div hb (Finset.mem_Ico.mp hr)]
    exact hx
  · intro hz
    refine Finset.mem_image.mpr ⟨((z - 1) / b, (z - 1) % b), ?_, ?_⟩
    · exact Finset.mem_product.mpr ⟨hz,
        Finset.mem_Ico.mpr ⟨Int.emod_nonneg _ hb.ne', Int.emod_lt_of_pos _ hb⟩⟩
    · change 1 + b * ((z - 1) / b) + (z - 1) % b = z
      have h := Int.emod_add_mul_ediv (z - 1) b
      omega

private theorem card_blocks {b : ℤ} (hb : 0 < b) (A : Finset ℤ) :
    (blocks b A).card = A.card * b.toNat := by
  unfold blocks
  have hInj : Set.InjOn (fun p : ℤ × ℤ => 1 + b * p.1 + p.2)
      (↑(A.product (Finset.Ico 0 b)) : Set (ℤ × ℤ)) := by
    intro p hp q hq h
    have hp' := Finset.mem_Ico.mp (Finset.mem_product.mp (Finset.mem_coe.mp hp)).2
    have hq' := Finset.mem_Ico.mp (Finset.mem_product.mp (Finset.mem_coe.mp hq)).2
    exact Prod.ext
      ((block_div hb hp').symm.trans ((congrArg (fun z : ℤ => (z - 1) / b) h).trans
        (block_div hb hq')))
      ((block_mod hp').symm.trans ((congrArg (fun z : ℤ => (z - 1) % b) h).trans
        (block_mod hq')))
  rw [Finset.card_image_of_injOn hInj, Finset.product_eq_sprod, Finset.card_product, Int.card_Ico, sub_zero]

private theorem blocks_partition {b : ℤ} (hb : 0 < b) {ones zeros : Finset ℤ}
    {L : ℤ} (hdisj : Disjoint ones zeros) (hpartition : ones ∪ zeros = Finset.Ico 0 L) :
    Disjoint (blocks b ones) (blocks b zeros) ∧
    blocks b ones ∪ blocks b zeros = Finset.Icc 1 (L * b) := by
  constructor
  · rw [Finset.disjoint_left]
    intro z hz₁ hz₂
    exact Finset.disjoint_left.mp hdisj
      ((mem_blocks hb).mp hz₁) ((mem_blocks hb).mp hz₂)
  · ext z
    rw [Finset.mem_union, mem_blocks hb, mem_blocks hb, ← Finset.mem_union,
      hpartition, Finset.mem_Ico, Finset.mem_Icc,
      Int.le_ediv_iff_mul_le hb, Int.ediv_lt_iff_lt_mul hb, zero_mul]
    omega

private theorem blocks_overlap {b : ℤ} (hb : 0 < b) {ones zeros : Finset ℤ} {c : ℕ}
    (word_overlap : ∀ k : ℤ, Overlap ones zeros k ≤ c) (k : ℤ) :
    Overlap (blocks b ones) (blocks b zeros) k ≤ c * b.toNat := by
  let pairs := ((blocks b ones).product (blocks b zeros)).filter fun p => p.1 - p.2 = k
  let residue := fun p : ℤ × ℤ => (p.1 - 1) % b
  let quotients := fun p : ℤ × ℤ => ((p.1 - 1) / b, (p.2 - 1) / b)
  change pairs.card ≤ c * b.toNat
  rw [Finset.card_eq_sum_card_fiberwise (f := residue)
    (t := Finset.Ico 0 b) (fun _ _ =>
      Finset.mem_Ico.mpr ⟨Int.emod_nonneg _ hb.ne', Int.emod_lt_of_pos _ hb⟩)]
  calc
    _ ≤ ∑ _r ∈ Finset.Ico 0 b, c := by
      apply Finset.sum_le_sum
      intro r _
      -- The residue and shift determine a single difference between the block indices.
      let d := -((r - k) / b)
      have hCard : (pairs.filter fun p => residue p = r).card ≤ Overlap ones zeros d := by
        apply Finset.card_le_card_of_injOn quotients
        · intro p hp
          have ⟨hp', hr⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hp)
          have ⟨hmem, hk⟩ := Finset.mem_filter.mp hp'
          have ⟨ha, hc⟩ := Finset.mem_product.mp hmem
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_product.mpr ⟨(mem_blocks hb).mp ha, (mem_blocks hb).mp hc⟩, ?_⟩
          have h := Int.emod_add_mul_ediv (p.1 - 1) b
          change (p.1 - 1) % b = r at hr
          have hRight : p.2 - 1 = (r - k) + b * ((p.1 - 1) / b) := by omega
          change (p.1 - 1) / b - (p.2 - 1) / b = d
          rw [hRight, Int.add_mul_ediv_left _ _ hb.ne']
          dsimp [d]
          omega
        · intro p hp q hq hpq
          have ⟨hp', hrp⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hp)
          have ⟨hq', hrq⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hq)
          have hpDiff := (Finset.mem_filter.mp hp').2
          have hqDiff := (Finset.mem_filter.mp hq').2
          have hDiv : (p.1 - 1) / b = (q.1 - 1) / b := congrArg Prod.fst hpq
          have hpEd := Int.emod_add_mul_ediv (p.1 - 1) b
          have hqEd := Int.emod_add_mul_ediv (q.1 - 1) b
          change (p.1 - 1) % b = r at hrp
          change (q.1 - 1) % b = r at hrq
          rw [hDiv] at hpEd
          exact Prod.ext (by omega) (by omega)
      exact hCard.trans (word_overlap d)
    _ = c * b.toNat := by simp [Int.card_Ico, Nat.mul_comm]

private theorem extended_overlap (A B C D : Finset ℤ) (k : ℤ) :
    Overlap (A ∪ C) (B ∪ D) k ≤ Overlap A B k + C.card + D.card := by
  let cut := fun X Y : Finset ℤ => (X.product Y).filter fun p => p.1 - p.2 = k
  have hsub : cut (A ∪ C) (B ∪ D) ⊆
      (cut A B ∪ cut C (B ∪ D)) ∪ cut (A ∪ C) D := by
    intro p hp
    obtain ⟨hmem, hk⟩ := Finset.mem_filter.mp hp
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hmem
    rcases Finset.mem_union.mp ha with ha' | hc
    · rcases Finset.mem_union.mp hb with hb' | hd
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha', hb'⟩, hk⟩))
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hd⟩, hk⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hc, hb⟩, hk⟩))
  have hC : (cut C (B ∪ D)).card ≤ C.card := by
    apply Finset.card_le_card_of_injOn Prod.fst
    · intro p hp
      exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
    · intro p hp q hq h
      have hpDiff := (Finset.mem_filter.mp hp).2
      have hqDiff := (Finset.mem_filter.mp hq).2
      exact Prod.ext h (by omega)
  have hD : (cut (A ∪ C) D).card ≤ D.card := by
    apply Finset.card_le_card_of_injOn Prod.snd
    · intro p hp
      exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2
    · intro p hp q hq h
      have hpDiff := (Finset.mem_filter.mp hp).2
      have hqDiff := (Finset.mem_filter.mp hq).2
      exact Prod.ext (by omega) h
  change (cut (A ∪ C) (B ∪ D)).card ≤ (cut A B).card + C.card + D.card
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add ((Finset.card_union_le _ _).trans (Nat.add_le_add_left hC _)) hD))

private theorem finite_bound {m n c : ℕ} (hm : 0 < m) (hn : m ≤ n)
    {ones zeros : Finset ℤ} (hdisj : Disjoint ones zeros)
    (hpartition : ones ∪ zeros = Finset.Ico 0 (2 * m : ℤ)) (hsame : ones.card = zeros.card)
    (word_overlap : ∀ k : ℤ, Overlap ones zeros k ≤ c) :
    M n ≤ c * (n / m) + 2 * (n % m) := by
  let b := n / m
  let s := n % m
  let B : ℤ := b
  let S : ℤ := s
  have hb : 0 < B := by
    change 0 < (b : ℤ)
    exact_mod_cast (Nat.div_pos hn hm : 0 < b)
  have hn' : n = m * b + s := (Nat.div_add_mod n m).symm
  have hnZ : (n : ℤ) = (m : ℤ) * B + S := by
    change (n : ℤ) = (m : ℤ) * (b : ℤ) + (s : ℤ)
    exact_mod_cast hn'
  have hS : 0 ≤ S := by
    change (0 : ℤ) ≤ (s : ℤ)
    exact_mod_cast (Nat.zero_le s)
  let L := (2 * (m : ℤ)) * B
  have hL : 2 * (n : ℤ) = L + 2 * S := by rw [hnZ]; dsimp [L]; ring
  let A := blocks B ones
  let C := blocks B zeros
  -- Append the same number of positions to each side of the partition.
  let P := Finset.Ioc (L) (L + S)
  let Q := Finset.Ioc (L + S) (L + 2 * S)
  have hcardP : P.card = s := by
    simp [P, Int.card_Ioc, show L + S - L = S by omega, S]
  have hcardQ : Q.card = s := by
    simp [Q, Int.card_Ioc, show L + 2 * S - (L + S) = S by omega, S]
  have hAc : A.card = ones.card * b := by
    simp [A, card_blocks hb, B]
  have hCc : C.card = ones.card * b := by
    simp [C, card_blocks hb, B, hsame]
  have hU : A ∪ C = Finset.Icc 1 (L) := (blocks_partition hb hdisj hpartition).2
  have hA {z : ℤ} (hz : z ∈ A) : 1 ≤ z ∧ z ≤ L :=
    Finset.mem_Icc.mp (hU ▸ Finset.mem_union_left _ hz)
  have hC {z : ℤ} (hz : z ∈ C) : 1 ≤ z ∧ z ≤ L :=
    Finset.mem_Icc.mp (hU ▸ Finset.mem_union_right _ hz)
  have hAP : Disjoint A P := Finset.disjoint_left.mpr fun _ hz hp => by
    have := hA hz
    have := Finset.mem_Ioc.mp hp
    omega
  have hCQ : Disjoint C Q := Finset.disjoint_left.mpr fun _ hz hq => by
    have := hC hz
    have := Finset.mem_Ioc.mp hq
    omega
  have hPart : Disjoint (A ∪ P) (C ∪ Q) := by
    rw [Finset.disjoint_left]
    intro z hz₁ hz₂
    rcases Finset.mem_union.mp hz₁ with ha | hp <;>
      rcases Finset.mem_union.mp hz₂ with hc | hq
    · exact Finset.disjoint_left.mp (blocks_partition hb hdisj hpartition).1 ha hc
    · have := hA ha
      have := Finset.mem_Ioc.mp hq
      omega
    · have := hC hc
      have := Finset.mem_Ioc.mp hp
      omega
    · have := Finset.mem_Ioc.mp hp
      have := Finset.mem_Ioc.mp hq
      omega
  have hFull : (A ∪ P) ∪ (C ∪ Q) = Finset.Icc (1 : ℤ) (2 * n) := by
    ext z
    rw [show (A ∪ P) ∪ (C ∪ Q) = (A ∪ C) ∪ (P ∪ Q) by
      ac_rfl, hU, Finset.mem_union, Finset.mem_union, Finset.mem_Icc,
      Finset.mem_Ioc, Finset.mem_Ioc, Finset.mem_Icc]
    omega
  have hEqual : (A ∪ P).card = (C ∪ Q).card := by
    rw [Finset.card_union_of_disjoint hAP, Finset.card_union_of_disjoint hCQ,
      hAc, hCc, hcardP, hcardQ]
  have hMin : M n ≤ MaxOverlap (A ∪ P) (C ∪ Q) :=
    Nat.sInf_le ⟨A ∪ P, C ∪ Q, hPart, hFull, hEqual, rfl⟩
  have hMax : MaxOverlap (A ∪ P) (C ∪ Q) ≤ c * b + s + s := by
    apply ciSup_le
    intro k
    calc
      _ ≤ Overlap A C k + P.card + Q.card := extended_overlap A C P Q k
      _ ≤ _ := by
        rw [hcardP, hcardQ]
        exact Nat.add_le_add_right (Nat.add_le_add_right (by
          simpa [A, C, B] using blocks_overlap hb word_overlap k) s) s
  exact (hMin.trans hMax).trans_eq (by change c * b + s + s = c * b + 2 * s; omega)

private theorem eventually_quotient_lt {m c : ℕ} (hm : 0 < m)
    {ones zeros : Finset ℤ} (hdisj : Disjoint ones zeros)
    (hpartition : ones ∪ zeros = Finset.Ico 0 (2 * m : ℤ)) (hsame : ones.card = zeros.card)
    (word_overlap : ∀ k : ℤ, Overlap ones zeros k ≤ c)
    {y : ℝ} (hy : (c : ℝ) / m < y) :
    ∀ᶠ n in atTop, MinOverlapQuotient n < y := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * (m : ℝ) / (y - (c : ℝ) / m))
  filter_upwards [eventually_ge_atTop (max m N)] with n hn
  have hnm : m ≤ n := (le_max_left ..).trans hn
  have hnN : N ≤ n := (le_max_right ..).trans hn
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hm.trans_le hnm
  have hBound : (M n : ℝ) ≤ c * (↑(n / m) : ℝ) + 2 * (↑(n % m) : ℝ) := by
    exact_mod_cast finite_bound hm hnm hdisj hpartition hsame word_overlap
  have hRem : (↑(n % m) : ℝ) ≤ m := by exact_mod_cast (Nat.mod_lt n hm).le
  have hMul : (↑(n / m) : ℝ) * m ≤ n := by exact_mod_cast Nat.div_mul_le_self n m
  have hProd : (c : ℝ) * (↑(n / m) : ℝ) ≤ (c : ℝ) / m * n := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hmR).mpr
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left hMul (Nat.cast_nonneg c : 0 ≤ (c : ℝ))
  have hErr : 2 * (m : ℝ) < (n : ℝ) * (y - (c : ℝ) / m) :=
    (div_lt_iff₀ (sub_pos.mpr hy)).mp (hN.trans_le (by exact_mod_cast hnN))
  unfold MinOverlapQuotient
  apply (div_lt_iff₀ hnR).mpr
  linarith [show (n : ℝ) * (y - (c : ℝ) / m) =
    (n : ℝ) * y - (c : ℝ) / m * n by ring]

private def shiftDown : ℤ ↪ ℤ where
  toFun x := x - 1
  inj' := by
    intro x y he
    change x - 1 = y - 1 at he
    omega

private theorem overlap_shiftDown (A B : Finset ℤ) (k : ℤ) :
    Overlap (A.map shiftDown) (B.map shiftDown) k = Overlap A B k := by
  unfold Overlap
  refine Finset.card_bij'
    (fun p _ => (p.1 + 1, p.2 + 1)) (fun p _ => (p.1 - 1, p.2 - 1)) ?_ ?_ ?_ ?_
  · intro p hp
    obtain ⟨hp, he⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpa, hpb⟩ := Finset.mem_product.mp hp
    obtain ⟨a, ha, hea⟩ := Finset.mem_map.mp hpa
    obtain ⟨b, hb, heb⟩ := Finset.mem_map.mp hpb
    change a - 1 = p.1 at hea
    change b - 1 = p.2 at heb
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨by
      rwa [show p.1 + 1 = a by omega], by rwa [show p.2 + 1 = b by omega]⟩, by dsimp; omega⟩
  · intro p hp
    obtain ⟨hp, he⟩ := Finset.mem_filter.mp hp
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨
      Finset.mem_map.mpr ⟨p.1, ha, rfl⟩, Finset.mem_map.mpr ⟨p.2, hb, rfl⟩⟩, by dsimp; omega⟩
  · intro p _
    exact Prod.ext (by simp) (by simp)
  · intro p _
    exact Prod.ext (by simp) (by simp)

private theorem bdd_overlap (A B : Finset ℤ) : BddAbove (Set.range (Overlap A B)) := by
  use (A.product B).card
  rintro x ⟨k, rfl⟩
  exact Finset.card_filter_le _ _

private theorem exists_min_partition (m : ℕ) :
    ∃ A B : Finset ℤ, Disjoint A B ∧ A ∪ B = Finset.Icc 1 (2 * m : ℤ) ∧
      A.card = B.card ∧ MaxOverlap A B = M m := by
  let T : Set ℕ := {MaxOverlap A B | (A : Finset ℤ) (B : Finset ℤ)
    (_disjoint : Disjoint A B) (_union : A ∪ B = Finset.Icc 1 (2 * m : ℤ))
    (_same_card : A.card = B.card)}
  have hT : T.Nonempty := by
    refine ⟨_, Finset.Icc 1 (m : ℤ), Finset.Ioc (m : ℤ) (2 * m : ℤ), ?_, ?_, ?_, rfl⟩
    · rw [Finset.disjoint_left]
      intro z hz hz'
      obtain ⟨_, hz⟩ := Finset.mem_Icc.mp hz
      obtain ⟨hz', _⟩ := Finset.mem_Ioc.mp hz'
      omega
    · ext z
      simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
      omega
    · rw [Int.card_Icc, Int.card_Ioc]
      congr 1
      omega
  obtain ⟨A, B, hd, hu, hc, he⟩ := (show M m ∈ T from csInf_mem hT)
  exact ⟨A, B, hd, hu, hc, he⟩

private theorem eventually_lt_of_value_lt {m : ℕ} (hm : 0 < m) {y : ℝ}
    (hy : MinOverlapQuotient m < y) : ∀ᶠ n in atTop, MinOverlapQuotient n < y := by
  obtain ⟨A, B, hdisj, hparts, hsame, hmin⟩ := exists_min_partition m
  have hpartShift : A.map shiftDown ∪ B.map shiftDown = Finset.Ico 0 (2 * m : ℤ) := by
    rw [← Finset.map_union, hparts]
    ext x
    simp only [Finset.mem_map, Finset.mem_Icc, Finset.mem_Ico]
    constructor
    · rintro ⟨z, hz, hzx⟩
      change z - 1 = x at hzx
      omega
    · intro hx
      exact ⟨x + 1, by omega, by change x + 1 - 1 = x; omega⟩
  apply eventually_quotient_lt hm ((Finset.disjoint_map shiftDown).mpr hdisj) hpartShift
    (by simpa only [Finset.card_map] using hsame) (c := M m) _ hy
  intro k
  rw [overlap_shiftDown, ← hmin]
  exact le_ciSup (bdd_overlap A B) k

noncomputable def limit : ℝ := sInf {y | ∃ n : ℕ, 0 < n ∧ MinOverlapQuotient n = y}

private theorem limit_bounded :
    BddBelow {y | ∃ n : ℕ, 0 < n ∧ MinOverlapQuotient n = y} := by
  refine ⟨0, ?_⟩
  rintro y ⟨n, _, rfl⟩
  unfold MinOverlapQuotient
  positivity

theorem tendsto_limit : atTop.Tendsto MinOverlapQuotient (𝓝 limit) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact ha.trans_le (csInf_le limit_bounded ⟨n, hn, rfl⟩)
  · intro b hb
    have hne : {y | ∃ n : ℕ, 0 < n ∧ MinOverlapQuotient n = y}.Nonempty :=
      ⟨_, 1, by decide, rfl⟩
    obtain ⟨y, ⟨m, hm, hmy⟩, hyb⟩ := (csInf_lt_iff limit_bounded hne).mp hb
    exact eventually_lt_of_value_lt hm (hmy ▸ hyb)

theorem limit_le_word_bound {m c : ℕ} (hm : 0 < m)
    {ones zeros : Finset ℤ} (hdisj : Disjoint ones zeros)
    (hpartition : ones ∪ zeros = Finset.Ico 0 (2 * m : ℤ)) (hsame : ones.card = zeros.card)
    (word_overlap : ∀ k : ℤ, Overlap ones zeros k ≤ c) :
    limit ≤ (c : ℝ) / m := by
  by_contra! hlt
  have hEventually : ∀ᶠ n in atTop, MinOverlapQuotient n < limit :=
    eventually_quotient_lt hm hdisj hpartition hsame word_overlap hlt
  obtain ⟨n, hn, hlow⟩ :=
    ((eventually_ge_atTop (1 : ℕ)).and hEventually).exists
  exact (not_lt_of_ge (csInf_le limit_bounded ⟨n, hn, rfl⟩)) hlow

end OverlapLimit

namespace OMA

open scoped BigOperators

private lemma powerSum_digit {ι : Type*} (s : Finset ι) (e : ι → ℕ) (q j : ℕ)
    (hq : 2 ≤ q) (hs : s.card < q) :
    ((∑ x ∈ s, q ^ e x) / q ^ j) % q = (s.filter fun x => e x = j).card := by
  classical
  let lo := s.filter fun x => e x < j
  let mid := s.filter fun x => e x = j
  let hi := s.filter fun x => j < e x
  have hpos : 0 < q := by omega
  have hlo : (∑ x ∈ lo, q ^ e x) < q ^ j := by
    cases j with
    | zero =>
      simp [lo]
    | succ j =>
      calc
        (∑ x ∈ lo, q ^ e x) ≤ ∑ _x ∈ lo, q ^ j :=
          Finset.sum_le_sum fun x hx =>
            pow_le_pow_right' (by omega : 1 ≤ q) (by
              have h := (Finset.mem_filter.mp hx).2
              omega)
        _ = lo.card * q ^ j := by simp
        _ ≤ s.card * q ^ j :=
          Nat.mul_le_mul_right _ (Finset.card_le_card (Finset.filter_subset _ _))
        _ < q ^ (j + 1) := by
          rw [pow_succ, mul_comm (q ^ j) q]
          exact Nat.mul_lt_mul_of_pos_right hs (pow_pos hpos _)
  have hmid : (∑ x ∈ mid, q ^ e x) = mid.card * q ^ j :=
    Finset.sum_const_nat fun x hx => by rw [(Finset.mem_filter.mp hx).2]
  have hhi : q ^ (j + 1) ∣ ∑ x ∈ hi, q ^ e x :=
    Finset.dvd_sum fun x hx => Nat.pow_dvd_pow _ (Nat.succ_le_of_lt (Finset.mem_filter.mp hx).2)
  obtain ⟨u, hu⟩ := hhi
  let rest := s.filter fun x => ¬ e x < j
  have hrestMid : (rest.filter fun x => e x = j) = mid := by
    ext x
    simp only [rest, mid, Finset.mem_filter]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, by omega⟩, h.2⟩⟩
  have hrestHi : (rest.filter fun x => e x ≠ j) = hi := by
    ext x
    simp only [rest, hi, Finset.mem_filter]
    exact ⟨fun h => ⟨h.1.1, by have := h.1.2; have := h.2; omega⟩,
      fun h => ⟨⟨h.1, by omega⟩, by omega⟩⟩
  have hsum : (∑ x ∈ s, q ^ e x) =
      (∑ x ∈ lo, q ^ e x) + (∑ x ∈ mid, q ^ e x) + (∑ x ∈ hi, q ^ e x) := by
    have hfirst := Finset.sum_filter_add_sum_filter_not s (fun x => e x < j)
      (fun x => q ^ e x)
    have hsecond := Finset.sum_filter_add_sum_filter_not rest (fun x => e x = j)
      (fun x => q ^ e x)
    rw [hrestMid, hrestHi] at hsecond
    rw [← hfirst, ← hsecond, add_assoc]
  have hupper : mid.card < q :=
    lt_of_le_of_lt (Finset.card_le_card (Finset.filter_subset _ _)) hs
  change ((∑ x ∈ s, q ^ e x) / q ^ j) % q = mid.card
  rw [hsum, hmid, hu, pow_succ, mul_assoc, add_assoc, mul_comm mid.card, ← mul_add,
    Nat.add_mul_div_left _ _ (pow_pos hpos _), Nat.div_eq_of_lt hlo, zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hupper]

lemma overlap_eq_digit (A B : Finset ℤ) (L q : ℕ)
    (hA : ∀ a ∈ A, 0 ≤ a ∧ a < L) (hB : ∀ b ∈ B, 0 ≤ b ∧ b < L)
    (hq : 2 ≤ q) (hcard : A.card * B.card < q)
    (k : ℤ) (hk : 1 - (L : ℤ) ≤ k) :
    ((∑ a ∈ A, q ^ a.toNat) * (∑ b ∈ B, q ^ (L - 1 - b.toNat)) /
      q ^ ((L : ℤ) - 1 + k).toNat) % q = Erdos36.Overlap A B k := by
  classical
  let e (p : ℤ × ℤ) := p.1.toNat + (L - 1 - p.2.toNat)
  have hprod :
      (∑ a ∈ A, q ^ a.toNat) * (∑ b ∈ B, q ^ (L - 1 - b.toNat)) =
      ∑ p ∈ A.product B, q ^ e p := by
    rw [Finset.sum_mul_sum, Finset.product_eq_sprod, Finset.sum_product]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp [e, pow_add]
  rw [hprod, powerSum_digit _ _ _ _ hq (by simpa using hcard)]
  unfold Erdos36.Overlap
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product]
  constructor
  · rintro ⟨⟨ha, hb⟩, he⟩
    refine ⟨⟨ha, hb⟩, ?_⟩
    have ha' := hA p.1 ha
    have hb' := hB p.2 hb
    dsimp [e] at he
    omega
  · rintro ⟨⟨ha, hb⟩, he⟩
    refine ⟨⟨ha, hb⟩, ?_⟩
    have ha' := hA p.1 ha
    have hb' := hB p.2 hb
    dsimp [e]
    omega

lemma overlap_eq_zero_of_outside (A B : Finset ℤ) (L : ℕ)
    (hA : ∀ a ∈ A, 0 ≤ a ∧ a < L) (hB : ∀ b ∈ B, 0 ≤ b ∧ b < L)
    (k : ℤ) (hk : k < 1 - (L : ℤ) ∨ (L : ℤ) - 1 < k) :
    Erdos36.Overlap A B k = 0 := by
  unfold Erdos36.Overlap
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨hp, he⟩ := Finset.mem_filter.mp hp
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
  have ha' := hA p.1 ha
  have hb' := hB p.2 hb
  change p.1 - p.2 = k at he
  omega

lemma overlap_le_of_digits_le (A B : Finset ℤ) (L q U : ℕ)
    (hA : ∀ a ∈ A, 0 ≤ a ∧ a < L) (hB : ∀ b ∈ B, 0 ≤ b ∧ b < L)
    (hq : 2 ≤ q) (hcard : A.card * B.card < q)
    (hdigits : ∀ j < 2 * L,
      ((∑ a ∈ A, q ^ a.toNat) * (∑ b ∈ B, q ^ (L - 1 - b.toNat)) / q ^ j) % q ≤ U)
    (k : ℤ) : Erdos36.Overlap A B k ≤ U := by
  by_cases hk : 1 - (L : ℤ) ≤ k ∧ k ≤ (L : ℤ) - 1
  · rw [← overlap_eq_digit A B L q hA hB hq hcard k hk.1]
    exact hdigits _ (by omega)
  · rw [overlap_eq_zero_of_outside A B L hA hB k (by omega)]
    exact Nat.zero_le _

end OMA

namespace OMA

open scoped BigOperators

lemma integer_partition_of_nat_digits (PA PB : Finset ℕ) (m q F R U : ℕ)
    (hDisj : Disjoint PA PB) (hUnion : PA ∪ PB = Finset.range (2 * m))
    (hCard : PA.card = m) (hF : ∑ i ∈ PA, q ^ i = F)
    (hR : ∑ i ∈ PB, q ^ (2 * m - 1 - i) = R)
    (hq : 2 ≤ q) (hcard : m * m < q)
    (hdigits : ∀ j < 2 * (2 * m), (F * R / q ^ j) % q ≤ U) :
    ∃ ones zeros : Finset ℤ, Disjoint ones zeros ∧
      ones ∪ zeros = Finset.Ico 0 (2 * (m : ℤ)) ∧
      ones.card = zeros.card ∧ ∀ k, Erdos36.Overlap ones zeros k ≤ U := by
  let castInt : ℕ ↪ ℤ := Nat.castEmbedding
  let ones := PA.map castInt
  let zeros := PB.map castInt
  have hCardB : PB.card = m := by
    have h := Finset.card_union_of_disjoint hDisj
    rw [hUnion, Finset.card_range, hCard] at h
    omega
  have hIco : ones ∪ zeros = Finset.Ico 0 (2 * (m : ℤ)) := by
    change PA.map castInt ∪ PB.map castInt = _
    rw [← Finset.map_union, hUnion]
    ext z
    rw [Finset.mem_map, Finset.mem_Ico]
    constructor
    · rintro ⟨n, hn, rfl⟩
      have hn' := Finset.mem_range.mp hn
      change 0 ≤ (n : ℤ) ∧ (n : ℤ) < 2 * (m : ℤ)
      omega
    · intro hz
      refine ⟨z.toNat, Finset.mem_range.mpr (by omega), ?_⟩
      change (z.toNat : ℤ) = z
      exact Int.toNat_of_nonneg hz.1
  have hbounds (z : ℤ) (hz : z ∈ ones ∪ zeros) : 0 ≤ z ∧ z < (2 * m : ℕ) := by
    rw [hIco, Finset.mem_Ico] at hz
    exact ⟨hz.1, by exact_mod_cast hz.2⟩
  have hA (a : ℤ) (ha : a ∈ ones) : 0 ≤ a ∧ a < (2 * m : ℕ) :=
    hbounds a (Finset.mem_union_left _ ha)
  have hB (b : ℤ) (hb : b ∈ zeros) : 0 ≤ b ∧ b < (2 * m : ℕ) :=
    hbounds b (Finset.mem_union_right _ hb)
  have hF' : ∑ a ∈ ones, q ^ a.toNat = F := by
    simpa only [ones, Finset.sum_map, castInt, Nat.castEmbedding_apply, Int.toNat_natCast] using hF
  have hR' : ∑ b ∈ zeros, q ^ (2 * m - 1 - b.toNat) = R := by
    simpa only [zeros, Finset.sum_map, castInt, Nat.castEmbedding_apply, Int.toNat_natCast] using hR
  have hCardA' : ones.card = m := by simpa only [ones, Finset.card_map] using hCard
  have hCardB' : zeros.card = m := by simpa only [zeros, Finset.card_map] using hCardB
  refine ⟨ones, zeros, (Finset.disjoint_map castInt).mpr hDisj, hIco,
    hCardA'.trans hCardB'.symm, ?_⟩
  apply overlap_le_of_digits_le ones zeros (2 * m) q U hA hB hq
  · simpa only [hCardA', hCardB'] using hcard
  · simpa only [hF', hR'] using hdigits

end OMA

namespace OverlapWord
open Finset

private structure Data where
  count : ℕ
  forward : ℕ
  reverseZeros : ℕ

private def pack (q : ℕ) : ℕ → ℕ → Data
  | 0, w => if w % 2 = 1 then ⟨1, 1, 0⟩ else ⟨0, 0, 1⟩
  | d + 1, w =>
    let size := 2 ^ d
    let low := pack q d (w % (2 ^ size))
    let high := pack q d (w / (2 ^ size))
    ⟨low.count + high.count, low.forward + q ^ size * high.forward,
      q ^ size * low.reverseZeros + high.reverseZeros⟩

private def shift (k : ℕ) (s : Finset ℕ) := s.image (k + ·)

private def join (k : ℕ) (s t : Finset ℕ) := s ∪ shift k t

private lemma join_sum {k : ℕ} {s t : Finset ℕ} (hs : s ⊆ range k) (f : ℕ → ℕ) :
    ∑ z ∈ join k s t, f z = (∑ z ∈ s, f z) + ∑ z ∈ t, f (k + z) := by
  have dis : Disjoint s (shift k t) := by
    refine disjoint_left.mpr ?_
    intro x hx h
    obtain ⟨z, _, rfl⟩ := mem_image.mp h
    have := mem_range.mp (hs hx)
    omega
  rw [join, sum_union dis, shift, sum_image]
  intro x _ y _ h
  exact Nat.add_left_cancel h

private lemma join_card {k : ℕ} {s t : Finset ℕ} (hs : s ⊆ range k) :
    (join k s t).card = s.card + t.card := by
  simpa using join_sum (t := t) hs (fun _ => 1)

private lemma join_partition {k : ℕ} {A B C D : Finset ℕ}
    (hAB : Disjoint A B) (hCD : Disjoint C D) (hAB' : A ∪ B = range k)
    (hCD' : C ∪ D = range k) :
    Disjoint (join k A C) (join k B D) ∧ join k A C ∪ join k B D = range (2*k) := by
  have ab (x : ℕ) : (x ∈ A ∨ x ∈ B) ↔ x < k := by rw [← mem_union, hAB', mem_range]
  have cd (x : ℕ) : (x ∈ C ∨ x ∈ D) ↔ x < k := by rw [← mem_union, hCD', mem_range]
  have test (u : Finset ℕ) (x : ℕ) : x ∈ shift k u ↔ k ≤ x ∧ x-k ∈ u := by
    constructor
    · intro hx
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hx
      simp [hz]
    · rintro ⟨hx, hm⟩
      exact mem_image.mpr ⟨x-k, hm, by omega⟩
  constructor
  · refine disjoint_left.mpr ?_
    intro x hx hy
    simp only [join, mem_union, test] at hx hy
    rcases hx with hA | ⟨ha, hC⟩ <;> rcases hy with hB | ⟨hb, hD⟩
    · exact disjoint_left.mp hAB hA hB
    · have := (ab x).1 (.inl hA)
      omega
    · have := (ab x).1 (.inr hB)
      omega
    · exact disjoint_left.mp hCD hC hD
  · ext x
    simp only [join, mem_union, test, mem_range]
    by_cases h : x < k
    · have hn : ¬ k ≤ x := by omega
      have hx : x < 2 * k := by omega
      simpa [hn, hx] using (ab x).2 h
    · have hk : k ≤ x := by omega
      have hh := (ab x).not.mpr h
      push Not at hh
      simp only [hh.1, hh.2, false_or, hk, true_and, cd]
      omega

private theorem realize (q : ℕ) (d w : ℕ) :
    ∃ A B : Finset ℕ, Disjoint A B ∧ A ∪ B = range (2^d) ∧
      A.card = (pack q d w).count ∧
      (∑ i ∈ A, q ^ i) = (pack q d w).forward ∧
      (∑ i ∈ B, q ^ (2^d-1-i)) = (pack q d w).reverseZeros := by
  induction d generalizing w with
  | zero =>
    by_cases h : w%2=1
    · exact ⟨{0}, ∅, by simp, by decide, by simp [pack, h], by simp [pack, h], by simp [pack, h]⟩
    · exact ⟨∅, {0}, by simp, by decide, by simp [pack, h], by simp [pack, h], by simp [pack, h]⟩
  | succ d ih =>
    let k := 2 ^ d
    obtain ⟨A, B, hd, hcov, hcard, hforward, hreverse⟩ := ih (w % 2^k)
    obtain ⟨C, D, hd', hcov', hcard', hforward', hreverse'⟩ := ih (w / 2^k)
    have hA : A ⊆ range k := hcov ▸ subset_union_left
    have hB : B ⊆ range k := hcov ▸ subset_union_right
    have hD : D ⊆ range k := hcov' ▸ subset_union_right
    have hpart := join_partition hd hd' hcov hcov'
    refine ⟨join k A C, join k B D, hpart.1, ?_, ?_, ?_, ?_⟩
    · simpa [k, pow_succ, Nat.mul_comm] using hpart.2
    · exact (join_card hA).trans (congrArg₂ (·+·) hcard hcard')
    · rw [join_sum hA, hforward]
      change _ + _ = _ + q^k * _
      rw [← hforward', mul_sum]
      simp only [pow_add]
      rfl
    · rw [join_sum hB]
      have hbig : 2 ^ (d+1) = k + k := by simp [k, pow_succ, Nat.mul_two]
      rw [hbig]
      change _ = q^k * _ + _
      rw [← hreverse, ← hreverse', mul_sum]
      congr 1
      · apply sum_congr rfl
        intro i hi
        have hi' := mem_range.mp (hB hi)
        change q^(k+k-1-i) = q^k * q^(k-1-i)
        rw [← pow_add]
        congr 1
        omega
      · apply sum_congr rfl
        intro i hi
        change q^(k+k-1-(k+i)) = q^(k-1-i)
        congr 1
        omega

private def checkDigits (q bound : ℕ) : ℕ → ℕ → Bool
  | 0, x => decide (x % q ≤ bound)
  | depth+1, x =>
    let scale := q ^ (2 ^ depth)
    checkDigits q bound depth (x % scale) && checkDigits q bound depth (x / scale)

private lemma checkDigits_sound {q bound d x : ℕ} (_hq : 2 ≤ q)
    (hc : checkDigits q bound d x = true) (j : ℕ) (hj : j < 2^d) :
    x / q^j % q ≤ bound := by
  induction d generalizing x j with
  | zero =>
    have : j = 0 := by simpa using hj
    simpa [this, checkDigits] using hc
  | succ d ih =>
    have hparts := Bool.and_eq_true_iff.mp hc
    by_cases h : j < 2 ^ d
    · have hh := ih hparts.1 j h
      have hsplit : x / q^j % q = (x % q^(2^d)) / q^j % q := by
        conv_rhs => rw [show 2^d = j + (2^d - j) by omega, pow_add]
        rw [Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd]
        obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : 2^d - j ≠ 0)
        rw [hr, pow_succ]
        exact Nat.dvd_mul_left _ _
      exact hsplit ▸ hh
    · have hj' : j - 2^d < 2^d := by rw [pow_succ] at hj; omega
      have hh := ih hparts.2 (j-2^d) hj'
      rw [Nat.div_div_eq_div_mul, ← pow_add, Nat.add_sub_of_le (by omega : 2^d ≤ j)] at hh
      exact hh

private def word : ℕ := 0x00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000010000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000040000000000000040000000000000000000000004000200000000000002000000000800000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000020000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000020000000000000000000000000000000000000000000000000000000000000000000200000000000000000200000000000000800040000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000040000000000200000000000000000000000000010000000080000000000000000000000000000200000000000000020000000000000000000000000100000000000000000000000000000000000000000000000000000004008000000000800000000000000000000000000000200020000010000000008000000000000040000010000000210000000000000000000000000000000000000000220000020000000000000000010000000000000000000000000000800000400001000000000000000000000000000000800100000000000000000400400000000000880000000000000000000000000000000080004002600000000000040000000020218000010000022e5f0b16d39e2c62fb7bd39f3340313c162f1e175fe0d19e2da72bbfa86b48ba2ede43a7f95cf19e8fdac1bc7bfda097e735513182a87e91e9ef7971a878efbf34b511e3f545fa0e7dd4b6d3bbdbad27ab266f550f69e881372ae2f9fb7b8347ec6deff59c9dfab977eff19c0b83dd28297784c288fbcdcd39d847fe6bca54c717b39bffb2dbbdd8957e4a2d8ddf7dd5da53c3f757dd79cefd69f229ec4144b0ab758a677de317bec7737bafbbc57d3ab03bf577ea2059b1ffb4e6d9e9f1449853fdb73b5f6b2db7de912342072c47bb5f4b2fd969b5e75b64f823fff59e5cf7e6637cacd8bce7b9fb1a3b7db6e1f3a155faa050c876facf7f9a71b586226adff9ddd3fabba4cf35f0cfb4bdbc7ff9d554dbefec759ebf65afc73d99dfe594c4baf927f4958699aed84ffc5e7f4bea93fc783ddf13310f5ebabfd4b06b76f9f397bffff7e5f79f477f5eb7ba3d7bffaa8df393d93f5bfefddbf76a7ddffbf66cde5d7ff3f97f6df7f32d6fd9fffb7e79ec97dfff7ef97fbfbcfefbbff87fabdaddfefeefbf3fd7c9ffdedfeefeff2f3fefddbdffb7f5afaefbf77fd7d7fff2ebddefdb4edff6e8fcfdd57b4ffeb77f7f977b7dfdb3f7cffff7d737d68ebfdaffab7defbfb8fdfff74dff3f6ff7dd6fb7ff7bdbffffefcad7f7fbedcfffbe1fdfe9aaf7fff717ab77eb85fddfff7feb9717efdedae73ffdbf7f9fecf6effdbcf8d7f6db1fffdedbffdf9cfa7ed7de73f3fbafde9ff6affdfff7bf6ff16abffdffe177abbffe7efbaffffd6fdffffff6dfcffe9fb55efdf85797d76efdfffdf6ff7b7f6fb3dddbff7377ddfffd7fffff5dfda7efdf7bdd6f7bffedbd779f0f7ff1fa29ff7be7effdddfc77fbedeb65fffbf9febfefcefedff9ef3d9faf7ff6efd9fff5ffff7fdffef5fdfabffffdbff7bfffffdffbdf7fdf77ffbf7ef7ff7fbefdff9d9ffdcf7ffefdefffefeeefffe7ffffff5f27f7d5ffffdffff7ffffcfddfffffbefffbff7fddbdcdfffbfb7ffbfff7fcdff9fffffbfd7fe77fbefffdeef3af7fdff7ffefffffbf7f7d77fffbdbf7ffff5ffff757bdfffddfffbffffffffff7ffffd7df7fdf7ffff9fb7ffffffdff7fedff5fddff7fffdbff4ffffdffbfff9aaffffffff6fdcbff3fffffeffebd6e7ffe7f5ffb3f7ffebff9efef57f5fffffbfbfbed7ff3fdf5f7fffdffffff7ffcfffff7fffffffeabfff7ffcffffefff2bfffffdddffff9f9ffffdffdde77ff4ff1fdffff3dff7ffffafffbfdddffb7fffeffdffdffbff72ff7eedfffbff3bfde77f6fef7fffdfffffff7efef7fffefbef7ffddfff3dfffdfdfffd5d7fffffffb9f3ff37efedfeebfbbffbff9fdfffffdb7df7e7c000110008890608b11002100a000100028000010000000000000000002020000000000900080000004100624200000002a10000228000100008080400400001a0240000100000000884000812208220400004080a000800000000000200000012000400024040800008000000100004400040100000000050400002000001022040020011001008010400000002100018000000000000001002000000000c001810002100000000000000001000010000200000100040a02000000100080006000040001000004201000004080800001802001000000020041800000108400010000000000009000400040000000200000400010401002000000010000000000000002000040080000002000080000300000000000208000000000611000000000000800010000000001208a0000120000001000000800011800201040900800400000000008000000000000000000000000000000000040040000000000000000400000010000080000000000000008000104000020000000008000004000000000000000000000000000000000000020084000010000000008040000000000000000000000000080000000000000004000000114400002000000000028000000000000400000200000000000000001000608000040000000000004000000000000010000800000000000400000000000000004000000000000000008000000020000000000000000000000000000000000000100000200000000200000000000001000000000000000000340000100002000040000000040000000200000004000402000000000010000010000000000a000000280000000000808000800000000000002000004000010000000200010000000400202001002000400800008000021f36fdf0fb6ba6d7ffb4ebbaf3fcffdfb367bffefcf7bfff729dccdf6e7ecfed5ebfada72fd63dfdfeeb499c3fefdff67ba7eb39bbb77fbeffed95f12bf7fffa12effdcffb77fedf7f25bfeecfbefefbfbcd5feddf4ddf08adf75d8f3a76fc67cbdeeffdfafb73f9bff15d9f96effbf997b9b3db73cf736ef79becb6efb77ffa7fb1fff96ef2cdffbdadf3fdf7fefedbbdfcfef7f1f5f4f5beaa7be9d6e7b76effa9dffbbfffb73edeeeb65797b8bfaffc54dfa6bff3b7bff6f7fd7f7f7b2f7fcffdfebb3efff3bd56d5df9b589f3f7d35ec537fff7eeffb977c9f9a529fef6bdff7eff8ccfeff6cd5f6febfd737b7fafeefbc7cffb573abbfbfbf9fe9e92f6967c77d737ffe96fe9ffeff17efefdafeb76fa7f7bcf2fecad3ffe63ef3b738de7cf67dd73efbdb3fbf3f6f9575fd9d7ffb52df7af7ffffb7fedbf9df9dbffbfe9fef3db3733db329f8f69fdc8960cac58e8a1e50f6f93fdffbd7d5e31bedc499f34bfb7bb0952efcf76f5b39f533fb9ac19d573f738c5deef36626faf5771b3c70bdfffe9f7f7d6a9652dff7d0197d3f257bfbffbe5fc82be3f5fc0f4eefb6781fecdaf4f6b8ddddb8058c838f7a556c6de67dedb7dbe79cf1f9c727b738f9b7fb3f7ab5cff17bfbda1ff5ddf6a0efbe3a4fd2acdfc7e9fd36df5df26d9ccf59fa585ee3f68fbdacffb7d1e6a3fafb6d7fff6ce25f74df8ee827c776cb29f5fd5f46abe57fffb3e755bc3da19bfddbffe934befff2fdbfda7fdedff8f39b4ad0f77ac3d88ba3771d9ab9195d3a66b93ab3e0fd3cc53ee2fdebd657a3eebc4dffdf7a5ed7dd7ad9e307df3fb6cf7fee75ddc96f5fef793fb8df7d3ffa7fff52f3f3d7a7ccf6ece3f728c6e75fefd2d7ce7c7b51f7c7e9f2ae59ecef8cedf695fdedc53640d6723802448e08000399420640c24171a81284094535d12054a411c1000a52900ac0194a064a41fac32602cf9ad4ccb0019c901cb808a14208c226904268a9af29080840903a5385c3910080850b04a23c28007a190242a5c872191b70980100a41a06033924983028565008c15d16504a161ca2241e52d01304c5486b2a0a3a04c611dc5834e276bb13cc10401652784013c455bd08a0c385a92285d2fd80e09094385567a540f2909061339404a0016095607629441b0f845388c902e550730d89103900a528202d580643c2154445c1199a56c5079929211040052c083078025d1e2888204295978513cc2e71a23bb0a009c89010ab4a9972c7850427ab0034f12aa23724142002310c8d0a3e219601a36d3a427d4480f6a934114805905014f428cc652008e02625d648a026915850dc28001410a01d11928073ae904691fffff6ffbefef7ffffdffbfbdff7b55ffffbbbffe79fffffffdfef7fdfffe9eff2edfeffffddbefffff96fffffff6fffffffffffbffefffffffdeffaff9fffefffbfdeefffcef7fe3fd7ff7fdfbefffffffbcfdfcff3ff77f777dfbbffdf7f6fffe6e6fdfffff77fffafffdfffeefffffb6ffffaffffffbf7ffff7ff3b7effefef9af7ed5fb71dffeffff7bfdfb5ffedd8ffd7fdfefffe63dfb9bffffefbffd7f3f74ef7ff3fdffcffffffffdfedf977fffc96fffffeffffcffdfffffdefdbfeffffffff3fffb9ffbbffbbffdffaff7fffff6feefebefff7bfffff5ffe73effffbff7fffffaffffeffff7dffdddeffffffffffbffffff575efddb5bddf3fe1fb7fffbfbebfffffffbffebef7eff3ffffbf7f7fbff7b7d7bffebfedf7ff7effffdbb7bffffef5ff7d74f7fec7ffcffbff7f9fffebffffffb7fdf7fd7fdfffbf3fe2a7532ad43627e08ee5a9d571b9b5e8f33decdfc5c42843f221a65f8b198cef3fadf4bd876f330e5713bcb463c235213b73f2d41de5e2dfc9af3ab6afb67c37bb049336c5fe7263a2ded50dc799d90cc73a4dff1203e804d02a8aef182b8fafc0f15b47f6a55939c99f795d5805c1d48f65497130a76d953b78395d688fa0f146c8a97fd36faf3742abbf6c493529ddeeaa3fcc135aa8ae0b15fad987ceccd9fc2a1dec2768cdeb87f97b5e9ed51bf6bb22ebd6bfbf50b6ae7e311b51381d63b4af9d33380815f22f65f9624c65e42034af08f7e0f8a4ebb8da3f537bc37044310eeeefaead5226ff6897dc7a01307426ff6d6165ea57af59b34f3715c497dcc8614dfca6e341d9a5258f6df2b37869f46e66ffa0f0d904a7d87f654a275616df9253be7b12da7e70be9bcb66ba7cb9dcbd473bc8eb4ad44e7cc6acc0323a478faf8402404000420055beb643f642511c102802044484288b081084200e829802981c84023800a0e0498542d914583c90140011405a002a180622d061808a0081021a884001a016122b0880484a600820c628051420b510a22438ac8c0903018a0301e008a005032aa56020d00045180a06002002c292600c00628091018c04c8432a580c8823621ce3005204409274e62611027a30412100310122e4010ce4c0006348c2110f4b11a004200c8435002a11204cc12680260a1220404e04000490222a201cc10015512e0103086c013cc260158024042182405f13c09a1025811801018062a012020618c48c30364c094a2504202956601089811d0020811a600d425105a830a8013c1001b730483c80402a04509811fd004004020443608040500d09008580498580000324c3098242208f09444816525100a13030412108566100301bfeb7bcffffffefadbf7defffffffa7efbdbffffef9ffffdcefffdff7f3ffbbefffcffffa7effbbf7e7ffedffedbfee7fabe71fbf4fffaf7df6bcefffff7ff7fffffeedefafbf5fffffbdef7ffdfffbfdfffcffeaffffdb7f6ffdfdfffffdd3ffeeeec7b3bff57ffffffaed2c7bffef6fb7fbfddfffceff3ffefffaeebffbeeffbf9dafffbf7cdfd7bddda7bf7fbfefffbbf57fffffddf3ebeffffffffefffffffbffd4fbffff7d4f34feffff977f8fb4fefdebfe6ffcdaff7fe7bff7aff5ff7ff76ff7dff9fffe7bfe7ffffffd7f1dfbebb3feffd9fff7ef5fbdfffffbff3dfd5ffffdf99b1ffbb7fdfbdee2fbfeffff8fdff3fbf7fbbfbfcfff7eaffbff7fbfbfffeffbfdf6b7fb7fdbeffffabfbffffffb7ffff6efffe7fabfefbdefff7d7fdff7faffe7ffdbddffbfbffffbf5dffe65ffebdf5fef97f9e7babdfffffbff5f95efb53a5e7f37903e9da46afcdcb7bc85044d20232b35143924f9eaa59e024f372ee0508b3759561c9fa2a915c8a874174e7652e66fab3b3edfca586464bb7b221bef4d9e7e13fdee95b1c74cd8e5f68744f19da357995bf8b86a5d42f7497c51fadb55f134262207125bd9e1ec7c21e55c3ca4c9bdfd2848b3348d52395b3844c315de6747bbb7d3df55bd0e37090ef7b8521fb9c1fc726c9aba9db62f25faff83a899274ce235afb03a33230b2ec8b1a70656e25c688c2a8253b55ebd13dd206b073dff89d29e5dff2c5e4f897db0e72d3838b6e5353ac76f640d6a7787034fd9fd13f67e7070efcfe5a6d5f2122a4433519d6f7e689241ea7e801a2f50fba6699ee246f9765e59061a93a57f79a2fdbf907e18e73e093e526294784577f9a935e84ddbd4f306bc35d58bac9d6852976befd6d0bf90e7acf5aaa7b6d9fd6b3815efffefffbffefffffffffffffffffffffffffffffffffefffffffffffffff7ffffffffffffefffff7fffffffffffffffffbfffef7ffffffffffffffffffffffffffffffffff7fffffdffffeffffffffffffffffeffffffffffffffff7fdfffffffffffffffffbffffffffffffff7ffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7feffffffffffffffffffffffffffffffffffffffdfffffffffffffffffffffff7ffffffffeeffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffffffffffffffffffffffffff7ffffffffffffffffffdffffffffffffffffffffffffffffbfaffffffffffffffff3302bef70e37bbf695cae72ea68dfe191b09a97b1b85423387df513d1ed4f4fbbcbe24ac08de74e820b86fdd79616f5b6a4edbd0fe49ff39d77037418b6b7aebdd6fc2b4aa279f7f8bc7668c5faa31de6e7a25f9f43280f2072018ffb25daaaee524ac62edddd1942f285a777b7e6ec8edbab7ee560fc7103264d761a3caff5bf8a19dba87f27ab6dd2629e6c9c3b5469f3c99efcd29f0a53009ada7f1f563297ed118e8ffc0aeaebb2f1efba9cd5d7d445bf94e0bcb22e2eab18bf929e386be2fca39de787acf6876ed8b7eeec98228e9b2aa19459a6b61bfdd287fafbf7665b1b81f4ac5755ff3651e33b63e3e5b21c426d3d0e55ecd4de1eeb3aa1f636f13ed6bdac38e8d6a45ba3a6d101c5523dfa8ecf787b14fdcbcdd12ed355b9caa1d5d3eb58e01d81b9c671ab56d62e9a5bfcb772aa2c71f3be4f555e6f3f652e36d7e3d77ff3dffffef9ffffdfffff3bfd77b71fffdffffffcfffff3defa7f7fffffbefefbfffddfffffffffe7feefefdbfffbff7fefbffffffffffffffaffbfffe7be3effbbff77fcfdfffdfffffff7fdbbfffff71ffdf7ea6efffffd7fff7fffffbffffffe76effffbfffffffff7f7ffbff77dfefedbfffff7dbbffe777fffffffffbffbfffffffdff973fff7fffd57fffffffbefffffffffffbffffffffc79dffbefeff8fff3cbfffbb8ffffffdf7ef7ffef5bffffbfffffbfff7fe7fffdfb7ffefffffdeefbf7fbdf77edbffebfbffefffffff7fffffdfdffddffdefffb7ff7edfffffffc7fbfbf7febbfadfff7ddfbbdffffffdff5efffeddbefffbfebffdfdfffefff37ffffdffffffdffbdfbbfffefffffffffffefdfffffffd7fdffffbfdfff1ffebdbfffffffbbfe7daffffbfbfeffffcdfff7dffff7feffffffffcdf7ffffdf7fafbbffffbf3edfdff7ffffd67fbeb2bbfdfff3ffff6fecefaffd79faefef3f7dfffffef6bfcfb5fbdb7ff7efbc7fbf7bf73ad7ffe77afee9bfbfd977fff7ff7ff97d7faffdfebdbf4f7fdfb6fffeffdefdebfeff7effbf6e6ff6bfefdfbffffbdbf587fefff7fbefdeffffffbfffaf3fda7fdf7fff39ff6d5faffcfbffd6dfedabf5fffb5e59f5f1ffb7ffcf7fffb7ffbfffff7ffafcf7fefdffbf9feeff2f7fbffffbcf7ffdff6bff7f7ffbbb7ffbffefeddc7feb9dff3bbdffcf6edfef73dfdffffdffaffef5ccffffffcf7ff9fef5efbf6f7b9bfffbfdff3fdffe7deffffeffeffbd2edff3ffdebdefadef97dabde7ffeb9fddfebf7fbedb7faadaff7ffdfbfffdeffeffdfefeebbffffebfaf3ffdeff75ffdeef7ff5f7faf5ddbebdffff76ffb3fbcffd7ffffbdeddf377d7bffffffffe7be9f4ffffffe5fdefeffdfe29efbfdfae7fffefa7efdbeffffffedfdfebffbff7dffffeffbfebfbfbff7ffedf77ff7ffbffbdeffbf97dffe1fde79ffffffff5dff7feffd7ffffdfdfffe77eff6bff7ffb97ffeeffdd7dfbffffff7fff7fefdffffcfeffff6fd7f79f9fbdfeff7fff7fefff76bff8efff7fff7fb7ffffdfeffbffffe69f7ff77efffdf7faf9fbfff3ff777ffffdf7e3ffebff6ffeeffffeaff7ffefeefdfdffffffff7dfff7fdfffe7f7fefffffdf7efffffffbfb7ff6bffefdfbbeff6fffaffff6fbbb7ffdffffeaf72bfffffbbbfbbefaf7fffffffbdf7fdfffffacfffffe7ffffefffffbfefffd7ff7fefffffffbdfffdfff7ff7d75fffdffdfd5effebffffffffffffffcfefedfffffffdfff7f7fefffffffff5f7fffffdfefefe6ffffffebb7f9fdbf7fffffedfffdc7fbafffffdfefefefbfffe3afdbffdffdf7dfffdbfefefffff7afffffffdeffbffffffeefffffffffffbef7fefff7fffffffffdfffc7fdfffffdfdbfffefff7f7feffffffeffbf5dffffff37ffff7ffefffffffffd7fffe7f7ffffffeff7fff7dffdfffffffbfbfffffeff7fdffbbfe7ffffefffffeffbfffffbfbfff9ffffffefdffffffffce7ff7fedffeffffbffdfbfffffeddffddfffbffffffffffffffff7fbfffe7fbffff7efbeffffffffedfff7e3ffff7fffffbffffffffea7ffffeffffbfffffffffdffffbbd7fbff7fffffff7cfdfffbfeffffffff7ffffffeffffffbffffff7fdefffff7fffffffbcffffffbffffffffffbef7defffffffbff9f7fbfffdfffffff7fffebfeffffeeffdfff7bffbeffffffffbffbfffcfffffbfffffffffb7fffeffffffeefffff7ffeffffffdeefffffbfffdffff2ffffffffffffffffffffffbff7ffffffeffffffffffd7fffffefffffffffebfffbffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffdfffff7fffffffffff7fffff7fffffffffdd5ffffffff7ffeffff7fffffffff7bf7ffffff7ffffffff7f7f7efd7ffffff9fffffffffffffffdfffffffbbfdfb7ffeefeffff7ffffffffffffff5fffdffffeefff7fffffffbfed6dd7fffeffffeefbfffdfff7f7fff5cffffffffffffffefffffffdbffefd7fffefffff7ffefffe7fefffffffff7fffefffffafbfff7f5ffefff7effffffffbffffffbfbffdffffffffbffffffdffff7ffbdfffbeeff7f7fefffffdeffffffffefffdfffffbffdfffff7fffffffffffdfffff7ffbf9fffefffffe7fecfeffffffffffffdfde7ff7dffffffffdfffff7fdffbdffffffffffdfbfffbfdf7fffffffffef7fff7fffffffffdefffffff7fefffffffffffffffefff7fffffb7ff7ff7ffdfff7fffffffffe7dfdffffefefffffffff7fbffffdf7dff7ff7ffffedfff7bdfebfffffffffbffff5ff7fffffffff2ffffdbf7ffffffbffff7ff7ffffffffafff5ffffffffff77efff7b7ffbf7fffebfffdefffeffa9fffafeffffffffdffbf7effbefebfbff7ff7fbdfeff7ffddf9db0fff77eff7ff7ddfffdfccffdbfff77defffffbffffffeb7f7faefddef7ffbdffffffdfffbfefeff7f92dffdfeffef7dffffffffa7bffff7bbfbeffbfefffffff7eff7dbf3fff7fffefbfdff7fdffffbffffffff7b3fbffdff7fffedbffdfdffb7ffffff7ffd6ffffffff7dffebfff5fbffbffbffd7f7f5fe7fffbfffcfffffffe7afff5fff7feefff4ffffffefffebfdffbdffffcffcffefffffffffff6affdfff7a7fbfffebbefff7fffe7ffffbf67fffffbbfeffbfffffffdffff7fbedffffefdfffffff7f9ffeefedfd7fffeffff7fdff77fffff766ff7fffbfffff665fffffdf7ffffffffff7fdd7ffdffff99fbfbfebbfffff7bdfffffff7bf9fea5ffeffff7eeffefddeff6fd7eff9fff7bd77f3ffef8fffff7ff5fbef9ff7af7fdf3ffde3fad1e97ffddeffefefbeafffbfddff526fef7ffaffa9ffceeefffd77bbbfff8777eddf7fffefff7fffb2fdfbcdfff67ffdffbbfff16fcdb7eff6d7ffbffb7efffbf5f2db3fff1ffdbdf517fff6ffff7fffffffedfdff4fffbd7ff5ffabcfffbadf3d7dff7eff7bdbe2b75dfe6ffbfcfefbefdfffe77ebbfffadfef5fbdefe7fd97dfeffeaf4d7fffdfeff97fff57ffe7afffff7e7ffcffefdbfff0bdebb7eff57dcdefc7bbd7b9fbf5fbefde5bd92cfbf7ff7ffffe7f7ffdbc6efffffffff7ef7fefe9bfffdd7fa9ee3ffb6ffff7dfeffffff7bfbdf7ffef77ffd7b9efeeffef8fbbdfb7befffefff7affffeffcdffcdbfdbeff77ffff57f3f7ef5ff5ffdfff5fdffefffaaeb7fff5ffebb7fff7ffecfe5ffff5ffffbfdeffff7fffff7fbf5fbbf7fefdfdfdebffbd7fbfdf7fffffdfdfbfff5f39fcfefeefff9ffe7b7ffbf7ff797fdfbfffffe3ffffffffeffdff67fffbfff7ff5ffeffafff7efffff37ffeffffffdf5f7feffff7ffdffbfffffef75f7ffffff3e7dbbffffffffffbffbffef7efffe7f7ffffdf7ffffffefeedeeff7b7fffffbfffd6f7ffefd77fdfffdfffe7f7ff77fff7fdfffffffbffffffdffffefffffe7b7ffdff6f7ffffffdffb1fffffffa37fa7fffffffbe7f7f3fffbfdfef7f7bffffdfffb3ffffe7daf7fffffbfddffa7b7fdfffaffffbf0f7ff7dfefffffbeffffdfe6ffffff9ffbfff7fffaebddefffff1ffbdffffdfffefffffffffff3b7c3fffffffd7ff3beeff6feffbfffefffffdf5dfefdfffffbdfff4ffffffdfffabffffebffbfffeffd7e9fff7fbddfffdfe7fcffffffffbffffe7ffe6acd7792efdc0b205d4381f59cf5b4af7f8dab90cf9fe7ceb54531a9335845ac3d74d1b41e19333df7f3e979c12f66e0deef82ecfc9f49ffe149fde909fb6a2bacd27a8c106496f35dcef86ededa6a8df87aded9f4b10140fed55e9e546a930f8e573122c634f1553eb29da1e6f323b7031553df3b3eacdfa5d3bd7cdced76719f3b33ab88c86eee936360fec556c18fe1af28417c43cc93f6bee7e2f67f30fc32d87732c9c65a74b79bfc199dbbeea1647f916b69948e261d7c9f359264d2b57db5a1a33fbcbf94b9ba18c71a16102af37fd8b7bcc0a59f76b86fcdb41f8c766af99e54dfb5d2c979fc3840a6f9daac90ae05b49f4fff20eababc1fa5e3bce4533e403055c98722fd5d7bad5ecb5844a977164c394f63597dffd6edd3b5bb94dba9eae63f167f5e7358ffd207a030c1b93da6bffbdc15bd7f33d849d17e797517effffffffffffffffff7fffffffffffffffffffffffffffffffffffbfffffffbffffffffffffffffffffffffffffffffffffefffffffffffffffffffffffffffffefffffffffffffffffffffffffffffffbfffffffffeffffffffffffffffffffffffffffffffffffffffffdfdfbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffb7ffffffffffffffffffffffffffffff7fffffffffffffffffdfffffbfffffffffffffffffffffffffff7fffffffffffffffffffbffffffffffffffffdffffffffffffffffffffffffffffffffffffffffffffffffffffffd7fffbffffffffffffffdfffbffffffffffffffffffffffffffffffffffffffffffdfffffffffbfffffffffffffdffffefbffffffffffffffff7ffffffffffffbfffffbfff7ffbdfeffffffffffffffffffffffffffffffffffff95bf2c3fec662efc2130ae33e01da363b97ffbb6deba56c5eaf2462c49e3f18bff50631fc98b798ec6481607f0c3436397505bec207f93def1dadaeb2dc87be65a48c306f7dad76dbff38f5192fc38e5bd66419d099e972c4e758b29559f402e102af59ba3a1a8f418fae2dc7b7e95cca93cb7854a368859092a757e798afbfcc6ced615f52d96dec345ce38fae67cb5547af7857e8ee682864f9e5a52538736e53bac7fb03ab28841ed13e9f5bef2d8d1164e670f10be3fa0aad886ce581cfcc3966a50fdd66d9bc5b7f1d26a9c5823ff5725c1c368fb270e7b12dfed3eec6d45cd74c72f668f4f1019f4888beb95ba233bbd19b348594820ebb9bd6c8d02662bcd20dbe309da7f032ffb04d041fa18e8137b8f63e51ce28cbac3b9cf5fc1ffc8fa81cea52e65e62032c9c5fff9a8a3eeecf8d95b26c56a7d770defad48b91fdc7ff5ffb5fff7ffefd3ebfffdaffffd7f9ffbfb766fef9bef7eb7ffff6dfd9b7f7fbffdffce7fdcf6f1ffdfffb7f6cfd6dfd6bfefeedfd7feeffefffdf7ebdfbeefe2ff7dcaf3effd9fdbdfe7fbf7afffeeffff7fefbfafedfffffff7f7f79fefff7f9ffdfbf4ffffffffafffb778f77affcfbffafbfefe7efff7ffff3cfefb7ffff3fffedf97cff9bbf3defdffefe7fffefffefb7f9fdffff69fffff7fffbbeefed7577fffeffedff7dfffdfffab7befffdf176f7fffffffdf97fdefdfe2ffffaa7ffcbfbeff4fdbefff3fffe6f9ff5bfff6bfeebbfb7beefed7ffffe7ffffeff7ff87ed6d7fd9f77ecbff9ef7eededeff5fdffffffbff7fffeffb7fbebffd357fbfbf3effceefef75faffffdf9ddf77fffc7a5fbf0ffdafffb7fdfb6bcffadef7fffffcf7bfff97ffffdd676ffbeffafdffe7d6ffffe7feffffefffffeeeff6cfb80529d2904008285402612080d3c588dc0044e429411d19a6a002011060210a663c4ae0ca1539429c0868004006c41001089820898a050030620a519140828481110ad40202790708014b00c0e00a0080ca412012200e0206310289e8045402220815421d11041050094222050194209e1265708200450006243214a0c84280a080804ac820001a390508504a00fa0884160a2a488802d05049d04260480059a24350106101040ab81d12f40aaa44284a311c1a040400505009122892932c0478a4004050520170c00a4220a180050a8109404129606a031484009a90402010a4601895600854292bca03a0e1289871406200d1809e0005000228040309a52181d601029401283101708029b94082311a804055b02c400c080124a2a44848413705a000002d000c02809a3d9084882581561c0269971921a200040690011420b0e210326763af7978a94f2a633115c0ebbc95f3f8aca309c9fdff310437ee6ebfce57f8f15791545917a55998bfc7fd73e20a82e8b29def4e6013e7dda0f74bfe7c13de9fde1c489bdb8a6686fe05766108b8871e522b3e6377944f7878befc6f5c85ceaafc18fe646965d45b787583ec7fc5f35090c6b2b38e7d02268fa758f68773c6d25579dd3f7430772bcd7af54732734b754d6eed9e7c4f0c8711ffa29cfd50887042a43aa1b42cb7c9d03f3b5faf2b64f0e2160d5d131a4b5f02f8ecf3f2beb08bd2f5177c8bc4a14ef32bd69af7d5d03fef7b83707dbb31db5b8e1344cfaf477a2e297520f24aab357d9638ddff5556c6b4dbafd65a7a120b14483ff74ad36713463a9a55c132aa4dde8865740c7ae0e8f965d35cdb105a6fd537f5164c92586380fef97d9679b944d5055f24be397b378e99161ebfc1e5ba474feaf7ebaf5f7fdf7ebdff9fffdf5d7efffff7ffbd7ef7bfffffff7ef7f7fbdeffbfffff9fff7fffffffbffcbff7eff739f7ff9ffffef3f7bffffffdbffafdfc77fffffaf7fddfffbcffffff7fffdfffff7fffefbbf7ffdf96e67eff7efe7fbef77fef2ffeffff7de7ffe3dfffddfddbb7ddffb3defebffffffdfddffb6ff7fffdff73ffffbd5e6eff7dbfdfbfe1ff7ffff6dff7f67fffeffd7f7dffffe7fffdffefb76ebdfeffedffffb9ffbdff5aebfbefffffffbbe6f7bfbffffffffffbfeebfeff5fd5ebadfdefffffefe7f7b5fff7fbfefbff9beffffffffef7b9dffb7fdfbfddfffdffffdbdff79f7becffdffdefcff7f7fffffefeffdefffdeeff5fefddeff3f3fbffaeff7bfff5fffffffefff7affd7f7fbfffffdfbfff7bfffddff7bfefffaedfddf1bff7fdffff7fffffbdf7efdfbf7bfdfaeffcf7bffff7bfffffdfffdfffbfbfe971421b646801308fe12005d24400a19548f347f296500144eda5fe4c2e06581b860f81008d580207e3022204eec2348b803342a10a60b1c516d02b92a04a11d28185d8e6015d9c8d418073807a50518b8d10100891a4080d0828598911201384541d03d5200086c024753000bf2815ec2a543a033081c86422c4265f80090ac0b63e8b00503010a175901b526465401ad4214e0c3298421d738494a070620354041ee05142301c4a432a16061604084121c4e742649d08c040849129ab10ce83231598cd20400a23d4466463f1cc06142029410126c4847200c49abf848230a82c44e58ab26c2ac10486420b84c1c85c5ec994cac440a72801f18c5d0189384555a060a6ceb12a232d5c05220484150409c30504ca0b9b12241661d32009e2a62400560d3078c5067fb58841694a6bac2e401294c244a021aa8c82141613a1c887c5672067d897e7bafe7ce9f6af4f63b793bf79f4fee5d4779ddbd9fe7efc14ed9ed4277e9f5fbceadbbfbefbfd8737758770f7baf4c43f6edb9a5bbf9be6bed96fa27ed5df4cfe3d7f7dfc3fdff6bcafb9e737b507cbff7eb3d9bcd37db4edcfb79351a3eeb6df29be4b8ff4f7db7e7d5df3523ff7afdf4842bfa44d4334bbbe655c5b3586e176f79cc0f8c3dfbfbbfea92f79c7ff7857bf2fe27e5aab2a9937c586e57febf7bae79ef9e33e7b9ffec3fe663578dfeec34d0df58aef7fec397be9dd86f76e4f77cffa99cf5cbc76fd9f95b5774cb3b63edf7bddfe1fa33e09f7b7ff795c466c7ef13ab78ebe5dbfa5498f6fbfd69ae156dc75ddf19b79b5fdb6a97f79447f5a79b5fd7618982fe72f74a5c6cbcc5dbfebbf9b27ebf3cdebff7d995a1ead7a26abf9ff6ffda6c7550f5a3dbff9fdffb397373bb0d2eeba7d51b7787edb7b93ff7b1fa7f7b7abf3ab7fdbc75eabedcff77fbf3e7ff5dddf756e7b7afabf0ffff3e7c7d7ee6bdbc773fffefbe6fffdaa88f7fe3fb5c3ed7fff4dfffd0cf6f7f9ff67ffddae8eeeeb7b3dbc13779f3f5cbfd5fdc6ebedbccfd7bafdfe3fd33bb76ffb1fbecffcfb7dfdeaf75bfdca8e5dcf0de1ffebddddf5ffb7e6bfeff3f6d5fcffff9effd0d9fe1bbb6f57ff9f6ed7fbf35321e9ff57bfeea7da6ff95df6dfd9fbdffd3feefdad7eff1db5ffacaf57f8d9d6ffffebcfe7f7fceafeefe9b8bce5f1beffabff7ef1f0ecbff3ffdfcfffd4f3fd363bb9beffb3e5fdffaee93d6fa1d7bafbe49b7ef32b7afadff6fecbf7ebebfdb7d5e69b75cf4bfd3babfb5f5fff7dd7be7eff7935fb77bdbddfa777dff6df9f7dee7b8ddbf3ad7b7b7efc7dfdbf7a7cfe4f7cffbfdd9f3fffff8eb7fb7959ebfbb8b7ad6be5d477df67900002000000010000008000000000000200000000000200000000000400000000000002000000082000800000000000100000000008404051400000000080000000008000000000000000080080100040040800000000000000000000000000002000000000000080000000000000000200000100000020000000000000880000000000000000000000000000000010004000200000000100001000020000000000002000000000000000000200000000002004000000080000000000000080000000080000380004000000000000004100000000000040000000000000000000000000000000040000000000000000008000000000001000400000000000000004000000000010000000400200000400800000200000000000000220000040000000000000000080000000200000002000000800200000800100000000000000000000000804000000000000000080040200000080000520200008005000c0020000000080000000082008100800080000000000800000020400008088004100000200000002080080000000240080000000000001000000405000000810000000204020000082840080120000000101000400050090000000000080021000000010000000000010400000c0100020400000420000000004422000001000004000000014000000800a200010008200081000080000001020000000000020800040010000200000000802800080400010500024020000000000008000000000300000501000000000000a00000000800004c422004004000010800000000840000400010948008140400008000410000090000000100402801a00400100004400002080000028000800d00004244000080000000204401002201001a022000020236377bff59fddf7eff9777dfffe7ff7bebdd777cfbbf7fdfff7ffdfdf7bfaffef7ffffddfffdffcfffff7df7ffbfff37fffffd7fbffffef6effffbfd77f97eafffefffb9ffffffb7ffbbffff7efbffbff3ffeefffffffddfbfffdbfbb7a6fffffefff3edffdfff4fffffffaebfbfffffff7ffbdbff33ffe9f3ffffeffffffffffffcff7fffffbf7bfccfefdfffbfefbfec4fbbfb7ffffffd5fbfffff7da7ffdfefbefffffb7c7ff7bfff7d3fffbffdeffdfffff6f3fffff7ff6dfc7d9fffff7e7fbfddfffffc5fffffdf4f6bfffffffefffd5bf7fffbefbfffbfffd6ffbdf39ffcdfffff7effffdfffff7efdbf7edfff77f2fffdfd9f9ffffef67fd7fefffffffeff5ffbdfffdfef7ffeffffbdff3beffcdff6ff7fff7ffbfffffeffff6cdfbfbbffff7ff7fdfffe7dbaffd7ffdf7fe9fffbff3fbf3fabfdfffbfdfff3eeffebf5ff7eaffdef9dbeffcdfdd07ebffff7effde0bff7f8fffffddff9ffbfb7d5ffef5ffcf26b66feddecef3fff96d7ff7fffebfca3fdd9d3fffeffe5779febfe5cffffffbdb6ffbdf9fff7fda4ffefdffbffb7ebf753e7fffdd87bece9defccfe777ffbbedcf7fdfffd3ddb7ff5e7be7d7ffefefdaf1d7c2dffdfb5fefdf7fbafcf5fbde5ffffafbffffe0daf3cf5ee3c7fbffaffbfa77fdbf76fbef7e5fdfdcdfc5ffefbf92fb7fe6bfafdf973ef9bf7dfbff5d5e673d7fbaffebbeb7db7f8fd7ddbefeebdb763fdfff5bedfde6eeffbbdfeffbcfbe7fffffde7feecdff3cbef9ffbb267bfe877fff5bbfd33cefbedff3f73ff17ef3f5c7cb7eeebb7fdddfdf7baefeffdabdd8d6fbe7fffe7b5b9ee7ddff5fdfd7f0fdecf7fd7b6fdbefa7fbff2ff9f67b73f74fe7decef2ffff8eeff7ddf561df9ffd7fd7ff25bc2bfebf1b4971fffdfefed0dfdf37ecc9fa3b30a5fbefa697db4bff593c2c6f52e8a85c3bddf497495658f561ad5bdf6d39d8ad7a88eb4ca33feb7a29ff2e4bd16dc32c3dbfc7dd542e82dc147e7305ff69aeb4fefdb2fa2769b6f7feb7fd8d85dcefdb7fd8f53f8b0adfc7a8fbfd07a38b379fbfafde8c4c036d7c5c3e4d2dad2ddcbe96cddccdbc032eb4f1e5dfe75cb99239913eab6b79a5e15aa75fe1d0d66cad2d03de7e72db17f735fddb4de7b78e5b5abc41e6f7ffb796b76d225fa72471d7b3b14ca2b8dd97cfb055d3f9775ae7bffaeac1ed7c6efe9d5bd47ddbe05bc3dfb72ae0b6d4e7b8dd496a1b298a5596d31f9666e94d82ef272c7b8ee827b72e523ad857aadb3cf8a68c4dc4d2db3fa56fdd855ffc3fe47f09bf7e4fb4f9aa7a572246fc81bddede58b3a2b7b65528797cb2e4aa6f5afe5a322d03eb2ab2f62f221595e86298bd508a0100900a001000001401010040008100010000000000010000020000000000000004000000000000000000000800000000000010000000000000000000000040000000000c000000000000000000000230000000000000000100000000200000000000000000000000000200000000000000000000020000000000000000000000804000000000000080000000000000000000009000000000000004000000000000000000000000000000000000001000000000000000000000020400000000000000000000000000000000000000200000000000000080000000040000000800080000000000000000000000000000000100000000000000000000000000000000000000000000001000000008000000000000000010000000000000000000008000002200000000000400000000000000002000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000404000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000200000000000000000002000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000040000000000000000000000000000000000080400000000000000000000000000000000000000000000000000000000000000001000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

set_option maxHeartbeats 30000000 in
private theorem wordCount : (pack (2^33) 17 word).count = 65536 := by decide +kernel

set_option maxHeartbeats 120000000 in
private theorem wordDigits : checkDigits (2^33) 25034 18
    ((pack (2^33) 17 word).forward * (pack (2^33) 17 word).reverseZeros) = true := by decide +kernel

private theorem certified_partition :
    ∃ A B : Finset ℤ, Disjoint A B ∧ A ∪ B = Finset.Ico 0 (2 * 65536 : ℤ) ∧
      A.card = B.card ∧ ∀ k : ℤ, Erdos36.Overlap A B k ≤ 25034 := by
  obtain ⟨A, B, hd, hu, ha, hf, hr⟩ := realize (2^33) 17 word
  apply OMA.integer_partition_of_nat_digits A B 65536 (2^33)
    (pack (2^33) 17 word).forward (pack (2^33) 17 word).reverseZeros 25034 hd hu
    (ha.trans wordCount) hf hr (by decide) (by decide)
  intro j hj
  exact checkDigits_sound (by decide) wordDigits j hj

end OverlapWord

theorem OMA.solution : type_of% @Erdos36.minimum_overlap.variants.upper.haugland_1996 := by
  obtain ⟨A, B, hd, hu, hc, ho⟩ := OverlapWord.certified_partition
  rw [OverlapLimit.tendsto_limit.limsup_eq]
  exact (OverlapLimit.limit_le_word_bound (m := 65536) (by decide) hd hu hc ho).trans
    (by norm_num)
