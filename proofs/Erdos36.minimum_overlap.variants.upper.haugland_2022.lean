import FormalConjectures.ErdosProblems.«36»
import Mathlib.Probability.Moments.SubGaussian

/-! The rational step profile is Haugland's 51-step construction
(https://www.neutreeko.net/mop/051.htm). Repeating its cells preserves the
weighted overlap bound. Independent sampling approximates every nonzero shift
at once: each shift splits into two matchings, so Hoeffding's inequality and
a union bound apply. Moving the small imbalance gives a balanced partition. -/

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

open Finset

namespace OverlapProfile

def pairStarts (L k : ℤ) : Finset ℤ := (Ico 0 L).filter fun x ↦ x - k ∈ Ico 0 L


/-- The 102 numerators in increasing cell order, packed in 54-bit fields. -/
private def packed : ℕ := 0xab0dc47f4c4002ac3711fd315498759962e0655261d6658b8196f7a3ca5216065bde8f294858197f300905c78a49fcc024171e292087f61715af57021fd85c56bd5c02b1c567576f600ac7159d5dbd86973a0ae68ead1a5ce82b9a3ab45b952bd40696e56e54af501a5b9326f55d4f6c870c9bd5753db21c7c859466e89519f216519ba25464d46fdd70333b5351bf75c0cced26147944fc4ec09851e513f13b0790fc6beef76bde43f1afbbddaf4a0e2156afcae12838855abf2b88e1bc9bf040002386f26fc100004e3f3ece01f50d38fcfb3807d438001e0b06cd2fe000782c1b34bf74f0ee1c65fb79d3c3b87197ede7e2f95a5ad1abdf8be5696b46af8461517b3759d6118545ecdd6758e1bc9bf040002386f26fc100008461517b3759d6118545ecdd6757e2f95a5ad1abdf8be5696b46af74f0ee1c65fb79d3c3b87197ede8001e0b06cd2fe000782c1b34bf4e3f3ece01f50d38fcfb3807d438e1bc9bf040002386f26fc100004a0e2156afcae12838855abf2b8790fc6beef76bde43f1afbbddaf26147944fc4ec09851e513f13b04d46fdd70333b5351bf75c0cced7c859466e89519f216519ba2546326f55d4f6c870c9bd5753db21c5b952bd40696e56e54af501a5b96973a0ae68ead1a5ce82b9a3ab402b1c567576f600ac7159d5dbd8087f61715af57021fd85c56bd5c7f300905c78a49fcc024171e2926f7a3ca5216065bde8f294858195498759962e0655261d6658b819000ab0dc47f4c4002ac3711fd31000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

private def den : ℕ := 10000000000000000
private def weightN (i : ℤ) : ℕ := (packed >>> (54*i.toNat)) % 2^54
noncomputable def weight (i : ℤ) : ℝ := weightN i / (den : ℝ)

private theorem weightCapFin : ∀ i : Fin 102, weightN i ≤ den := by decide +kernel

lemma weightCap {i : ℤ} (hi : i ∈ Ico (0 : ℤ) 102) : weight i ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨h0,h1⟩ := Finset.mem_Ico.mp hi
  have hh := weightCapFin ⟨i.toNat, by omega⟩
  have he : ((i.toNat : ℕ) : ℤ) = i := Int.toNat_of_nonneg h0
  change weightN (↑i.toNat : ℤ) ≤ den at hh
  rw [he] at hh
  unfold weight
  refine ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), (div_le_iff₀ (by norm_num [den])).mpr ?_⟩
  simpa using (show (weightN i : ℝ) ≤ (den : ℝ) by exact_mod_cast hh)

private theorem weightMassNat : ∑ i ∈ Ico (0 : ℤ) 102, weightN i = 51 * den := by
  decide +kernel

lemma weightMass : ∑ i ∈ Ico (0 : ℤ) 102, weight i = 51 := by
  rw [show (∑ i ∈ Ico (0 : ℤ) 102, weight i) =
    ((∑ i ∈ Ico (0 : ℤ) 102, weightN i : ℕ) : ℝ) / den by simp only [weight, Nat.cast_sum, Finset.sum_div]]
  rw [weightMassNat]
  norm_num [den]

private def numerator (k : ℤ) : ℕ :=
  ∑ i ∈ pairStarts 102 k, weightN i * (den - weightN (i - k))


private def partialNum (k : ℤ) : ℕ → ℕ
  | 0 => 0
  | n+1 => partialNum k n +
      if 0 ≤ (n : ℤ)-k ∧ (n : ℤ)-k < 102 then weightN n * (den-weightN ((n : ℤ)-k)) else 0

private lemma partialNum_eq (k : ℤ) (n : ℕ) :
    partialNum k n = ∑ i ∈ Ico (0 : ℤ) n,
      if 0 ≤ i-k ∧ i-k < 102 then weightN i * (den-weightN (i-k)) else 0 := by
  induction n with
  | zero => simp [partialNum]
  | succ n ih =>
    have hs : Ico (0 : ℤ) ((n : ℤ)+1) = insert (n : ℤ) (Ico 0 (n : ℤ)) := by
      ext z
      simp only [mem_Ico, mem_insert]
      omega
    rw [Nat.cast_succ, hs, sum_insert (by simp), partialNum, ih, add_comm]

private lemma partialNum102 (k : ℤ) : partialNum k 102 = numerator k := by
  rw [partialNum_eq]
  unfold numerator pairStarts
  simp only [Finset.sum_filter, Finset.mem_Ico, Nat.cast_ofNat]

private def allBounds (n : ℕ) : Bool :=
  match n with
  | 0 => true
  | t+1 => decide (partialNum ((t : ℤ)-101) 102 ≤ 1942726952508743600000000000000000) && allBounds t

private lemma allBounds_sound {n : ℕ} (h : allBounds n = true) {t : ℕ} (ht : t < n) :
    partialNum ((t : ℤ)-101) 102 ≤ 1942726952508743600000000000000000 := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [allBounds, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp ht with hlt | rfl
    · exact ih h.2 hlt
    · exact h.1

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem checkedBounds : allBounds 203 = true := by decide +kernel

private theorem profileCert (k : Fin 203) :
    numerator ((k : ℤ) - 101) ≤ 1942726952508743600000000000000000 := by
  rw [← partialNum102]
  exact allBounds_sound checkedBounds k.isLt
lemma profileBound (k : ℤ) :
    ∑ i ∈ pairStarts 102 k, weight i * (1 - weight (i - k)) ≤
      51 * (0.380926853433087 : ℝ) - 1 / 10^17 := by
  by_cases hk : -101 ≤ k ∧ k ≤ 101
  · have h := profileCert ⟨(k+101).toNat, by omega⟩
    have he : (↑(k+101).toNat : ℤ) - 101 = k := by omega
    change numerator ((↑(k+101).toNat : ℤ) - 101) ≤ _ at h
    rw [he] at h
    have hn : (numerator k : ℝ) ≤ 1942726952508743600000000000000000 := by exact_mod_cast h
    have hw (i : ℤ) (hi : i ∈ pairStarts 102 k) :
        weight i * (1 - weight (i-k)) =
          ((weightN i * (den - weightN (i-k)) : ℕ) : ℝ) / (den : ℝ)^2 := by
      have ha := Finset.mem_Ico.mp (Finset.mem_filter.mp hi).2
      have hd := weightCapFin ⟨(i-k).toNat, by omega⟩
      have he' : (↑(i-k).toNat : ℤ) = i-k := Int.toNat_of_nonneg ha.1
      change weightN (↑(i-k).toNat : ℤ) ≤ den at hd
      rw [he'] at hd
      simp only [weight, Nat.cast_mul, Nat.cast_sub hd]
      have hp : (den : ℝ) ≠ 0 := by norm_num [den]
      field_simp
    rw [Finset.sum_congr rfl hw, ← Finset.sum_div, ← Nat.cast_sum]
    change (numerator k : ℝ) / _ ≤ _
    exact (div_le_div_of_nonneg_right hn (sq_nonneg (den : ℝ))).trans (by norm_num [den])
  · have hs : pairStarts 102 k = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x h
      obtain ⟨h1,h2⟩ := Finset.mem_filter.mp h
      have h1' := Finset.mem_Ico.mp h1
      have h2' := Finset.mem_Ico.mp h2
      omega
    rw [hs, Finset.sum_empty]
    norm_num

private lemma div_mem_block {b x : ℤ} (hb : 0 < b) :
    x / b ∈ Ico (0 : ℤ) 102 ↔ x ∈ Ico 0 (102*b) := by
  rw [Finset.mem_Ico, Finset.mem_Ico, Int.le_ediv_iff_mul_le hb,
    Int.ediv_lt_iff_lt_mul hb, zero_mul]

lemma weighted_residue {b : ℤ} (hb : 0 < b) (k r : ℤ) (hr : r ∈ Ico 0 b)
    (F : ℤ → ℤ → ℝ) :
    ∑ x ∈ (pairStarts (102*b) k).filter (fun x ↦ x % b = r), F (x/b) ((x-k)/b) =
      ∑ i ∈ pairStarts 102 (-((r-k)/b)), F i (i-(-((r-k)/b))) := by
  obtain ⟨hr0,hrb⟩ := Finset.mem_Ico.mp hr
  have divRight (x : ℤ) (hx : x % b = r) :
      (x-k)/b = x/b - (-((r-k)/b)) := by
    have h := Int.emod_add_mul_ediv x b
    have hxk : x-k = r-k + b*(x/b) := by omega
    conv_lhs => rw [hxk]
    rw [Int.add_mul_ediv_left _ _ hb.ne']
    omega
  refine Finset.sum_bij (fun x hx ↦ x/b) ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨hx,hres⟩ := Finset.mem_filter.mp hx
    obtain ⟨hx₁,hx₂⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr
      ⟨(div_mem_block hb).mpr hx₁, divRight x hres ▸ (div_mem_block hb).mpr hx₂⟩
  · intro x hx y hy h
    have hxr := (Finset.mem_filter.mp hx).2
    have hyr := (Finset.mem_filter.mp hy).2
    have hxd := Int.emod_add_mul_ediv x b
    have hyd := Int.emod_add_mul_ediv y b
    change x/b = y/b at h
    rw [h] at hxd
    omega
  · intro i hi
    obtain ⟨hi₁,hi₂⟩ := Finset.mem_filter.mp hi
    let x := r + b*i
    have hdiv : x/b = i := by
      simp [x, Int.add_mul_ediv_left _ _ hb.ne', Int.ediv_eq_zero_of_lt hr0 hrb]
    have hmod : x%b = r := by
      simp [x, Int.add_mul_emod_self_left, Int.emod_eq_of_lt hr0 hrb]
    refine ⟨x, Finset.mem_filter.mpr ⟨?_,hmod⟩, hdiv⟩
    apply Finset.mem_filter.mpr
    exact ⟨(div_mem_block hb).mp (hdiv.symm ▸ hi₁),
      (div_mem_block hb).mp ((divRight x hmod).symm ▸ (hdiv.symm ▸ hi₂))⟩
  · intro x hx
    rw [divRight x (Finset.mem_filter.mp hx).2]

lemma weighted_sum {b : ℤ} (hb : 0 < b) (k : ℤ) (F : ℤ → ℤ → ℝ) :
    ∑ x ∈ pairStarts (102*b) k, F (x/b) ((x-k)/b) =
      ∑ r ∈ Ico 0 b, ∑ i ∈ pairStarts 102 (-((r-k)/b)), F i (i-(-((r-k)/b))) := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun x : ℤ ↦ x%b)
    (t := Ico 0 b) (fun x _ ↦ Finset.mem_Ico.mpr ⟨Int.emod_nonneg x hb.ne',
      Int.emod_lt_of_pos x hb⟩) (fun x ↦ F (x/b) ((x-k)/b))]
  exact Finset.sum_congr rfl fun r hr ↦ weighted_residue hb k r hr F

lemma scaledMass {b : ℤ} (hb : 0 < b) :
    ∑ x ∈ Ico 0 (102*b), weight (x/b) = 51 * b := by
  have h := weighted_sum hb 0 (fun x _ ↦ weight x)
  rw [show pairStarts (102*b) 0 = Ico 0 (102*b) by simp [pairStarts]] at h
  rw [h]
  have h' : ∑ r ∈ Ico (0 : ℤ) b, ∑ i ∈ pairStarts 102 (-((r-0)/b)), weight i =
      ∑ _r ∈ Ico (0 : ℤ) b, (51 : ℝ) := by
    apply Finset.sum_congr rfl
    intro r hr
    obtain ⟨h0,h1⟩ := Finset.mem_Ico.mp hr
    rw [sub_zero, Int.ediv_eq_zero_of_lt h0 h1, neg_zero,
      show pairStarts 102 0 = Ico (0 : ℤ) 102 by unfold pairStarts; simp only [sub_zero, filter_mem_eq_inter, inter_self]]
    exact weightMass
  rw [h']
  simp only [Finset.sum_const, Int.card_Ico, sub_zero, nsmul_eq_mul]
  have hc : (b.toNat : ℝ) = b := by exact_mod_cast Int.toNat_of_nonneg hb.le
  rw [hc, mul_comm]

lemma scaledBound {b : ℤ} (hb : 0 < b) (k : ℤ) :
    ∑ x ∈ pairStarts (102*b) k, weight (x/b) * (1 - weight ((x-k)/b)) ≤
      b * (51 * (0.380926853433087 : ℝ) - 1 / 10^17) := by
  rw [weighted_sum hb k (fun x y ↦ weight x * (1 - weight y))]
  calc
    _ ≤ ∑ _r ∈ Ico (0 : ℤ) b, (51 * (0.380926853433087 : ℝ) - 1 / 10^17) :=
      Finset.sum_le_sum fun r _ ↦ profileBound _
    _ = _ := by
      simp only [Finset.sum_const, Int.card_Ico, sub_zero, nsmul_eq_mul]
      have hc : (b.toNat : ℝ) = b := by exact_mod_cast Int.toNat_of_nonneg hb.le
      rw [hc]

end OverlapProfile

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal
noncomputable section

namespace OverlapSample

def unitProb : Measure ℝ := volume.restrict (Set.Ico 0 1)

instance : IsProbabilityMeasure unitProb := by
  constructor
  simp [unitProb, Real.volume_Ico]

def sampleProb (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi fun _ ↦ unitProb

instance (ι : Type*) [Fintype ι] : IsProbabilityMeasure (sampleProb ι) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : ι ↦ unitProb))

private lemma indepCoord {ι : Type*} [Fintype ι] :
    iIndepFun (fun i (ω : ι → ℝ) ↦ ω i) (sampleProb ι) :=
  iIndepFun_pi (X := fun _ ↦ id) fun _ ↦ aemeasurable_id

def rectangle {ι : Type*} (s : Finset ι) (T : ι → Set ℝ) : Set (ι → ℝ) :=
  ⋂ i ∈ s, (fun ω : ι → ℝ ↦ ω i) ⁻¹' T i

lemma measurable_rectangle {ι : Type*} (s : Finset ι) {T : ι → Set ℝ}
    (hT : ∀ i, MeasurableSet (T i)) : MeasurableSet (rectangle s T) :=
  s.measurableSet_biInter fun i _ ↦ (measurable_pi_apply i) (hT i)

lemma measure_rectangle {ι : Type*} [Fintype ι] (s : Finset ι) {T : ι → Set ℝ}
    (hT : ∀ i, MeasurableSet (T i)) :
    sampleProb ι (rectangle s T) = ∏ i ∈ s, unitProb (T i) := by
  rw [rectangle, indepCoord.measure_inter_preimage_eq_mul s fun i _ ↦ hT i]
  apply Finset.prod_congr rfl
  intro i hi
  exact ((measurePreserving_eval (fun _ : ι ↦ unitProb) i).measure_preimage (hT i).nullMeasurableSet)

lemma indepRectangle {ι κ : Type*} [Fintype ι] (D : κ → Finset ι)
    (hD : Pairwise fun i j ↦ Disjoint (D i) (D j)) {T : ι → Set ℝ}
    (hT : ∀ i, MeasurableSet (T i)) :
    iIndepSet (fun i ↦ rectangle (D i) T) (sampleProb ι) := by
  classical
  rw [iIndepSet_iff_meas_biInter fun i ↦ measurable_rectangle _ hT]
  intro s
  have hset : (⋂ i ∈ s, rectangle (D i) T) = rectangle (s.biUnion D) T := by
    ext x
    simp [rectangle]
  rw [hset, measure_rectangle _ hT, Finset.prod_biUnion (fun i _ j _ hij ↦ hD hij)]
  simp only [measure_rectangle _ hT]

def eventVal {Ω : Type*} (s : Set Ω) : Ω → ℝ := s.indicator fun _ ↦ 1

lemma integral_eventVal {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (s : Set Ω)
    (hs : MeasurableSet s) : (∫ ω, eventVal s ω ∂μ) = μ.real s := by
  rw [eventVal, integral_indicator_const _ hs, smul_eq_mul, mul_one]

lemma subGaussian_events {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {E : ι → Set Ω} (hE : ∀ i, MeasurableSet (E i))
    (hind : iIndepSet E μ) (s : Finset ι) :
    HasSubgaussianMGF
      (fun ω ↦ ∑ i ∈ s, eventVal (E i) ω - ∑ i ∈ s, μ.real (E i))
      ((s.card : ℝ≥0) / 4) μ := by
  have hind' : iIndepFun (fun i ω ↦ eventVal (E i) ω - μ.real (E i)) μ :=
    (hind.iIndepFun_indicator).comp (fun (i : ι) (x : ℝ) ↦ x - μ.real (E i))
      (fun _ ↦ measurable_id.sub_const _)
  have hi (i : ι) : HasSubgaussianMGF
      (fun ω ↦ eventVal (E i) ω - μ.real (E i)) ((1 : ℝ≥0) / 4) μ := by
    have hm : Measurable (eventVal (E i)) := measurable_const.indicator (hE i)
    have hI : ∀ ω, eventVal (E i) ω ∈ Set.Icc (0 : ℝ) 1 := by
      intro ω
      by_cases h : ω ∈ E i <;> simp [eventVal, h]
    convert hasSubgaussianMGF_of_mem_Icc (μ := μ) hm.aemeasurable (Filter.Eventually.of_forall hI) using 2
    · simp [integral_eventVal _ _ (hE i)]
    · norm_num
  convert HasSubgaussianMGF.sum_of_iIndepFun hind' (s := s) (fun i _ ↦ hi i) using 1
  · ext ω
    exact (Finset.sum_sub_distrib _ _).symm
  · simp [nsmul_eq_mul, div_eq_mul_inv]

abbrev positions (L : ℤ) := ↥(Ico 0 L)


def validStarts (L k : ℤ) : Finset ℤ := (Ico 0 L).filter fun x ↦ x - k ∈ Ico 0 L

def stepClass (k x : ℤ) : ℤ := (x / k) % 2

private lemma stepClass_next (x : ℤ) {k : ℤ} (hk : k ≠ 0) :
    stepClass k (x-k) ≠ stepClass k x := by
  unfold stepClass
  rw [show x-k = x+k*(-1) by ring, Int.add_mul_ediv_left _ _ hk]
  omega

private lemma unitProb_iio {p : ℝ} (hp : p ∈ Set.Icc 0 1) :
    unitProb (Set.Iio p) = ENNReal.ofReal p := by
  rw [unitProb, Measure.restrict_apply measurableSet_Iio]
  rw [show Set.Iio p ∩ Set.Ico 0 1 = Set.Ico 0 p by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ico]
    constructor
    · tauto
    · exact fun ⟨hx₀,hxp⟩ ↦ ⟨hxp,hx₀,hxp.trans_le hp.2⟩]
  simp [Real.volume_Ico]

private lemma unitProb_ici {p : ℝ} (hp : p ∈ Set.Icc 0 1) :
    unitProb (Set.Ici p) = ENNReal.ofReal (1-p) := by
  rw [unitProb, Measure.restrict_apply measurableSet_Ici]
  rw [show Set.Ici p ∩ Set.Ico 0 1 = Set.Ico p 1 by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ico]
    constructor
    · tauto
    · exact fun ⟨hpx,hx₁⟩ ↦ ⟨hpx,hp.1.trans hpx,hx₁⟩]
  exact Real.volume_Ico

def chosen {L : ℤ} (w : positions L → ℝ) (i : positions L) : Set (positions L → ℝ) :=
  (fun ω ↦ ω i) ⁻¹' Set.Iio (w i)

lemma chosen_meas {L : ℤ} (w : positions L → ℝ) (i : positions L) :
    MeasurableSet (chosen w i) := (measurable_pi_apply i) measurableSet_Iio

lemma chosen_mean {L : ℤ} {w : positions L → ℝ} (hw : ∀ i, w i ∈ Set.Icc (0 : ℝ) 1)
    (i : positions L) : (sampleProb (positions L)).real (chosen w i) = w i := by
  rw [measureReal_def, chosen, sampleProb, (measurePreserving_eval (fun _ : positions L ↦ unitProb)
    i).measure_preimage measurableSet_Iio.nullMeasurableSet, unitProb_iio (hw i),
    ENNReal.toReal_ofReal (hw i).1]

def leftEnd {L k : ℤ} (x : ↥(validStarts L k)) : positions L :=
  ⟨x.1, (Finset.mem_filter.mp x.2).1⟩

def rightEnd {L k : ℤ} (x : ↥(validStarts L k)) : positions L :=
  ⟨x.1-k, (Finset.mem_filter.mp x.2).2⟩

def edgeEvent {L k : ℤ} (w : positions L → ℝ) (x : ↥(validStarts L k)) :
    Set (positions L → ℝ) := chosen w (leftEnd x) ∩ (chosen w (rightEnd x))ᶜ

lemma edge_mean {L k : ℤ} (hk : k ≠ 0) {w : positions L → ℝ}
    (hw : ∀ i, w i ∈ Set.Icc (0 : ℝ) 1) (x : ↥(validStarts L k)) :
    (sampleProb (positions L)).real (edgeEvent w x) =
      w (leftEnd x) * (1-w (rightEnd x)) := by
  classical
  let i := leftEnd x
  let j := rightEnd x
  have hij : i ≠ j := by
    intro h
    have h' := congrArg Subtype.val h
    change x.1 = x.1-k at h'
    omega
  let T := fun y : positions L ↦ if y = i then Set.Iio (w y) else Set.Ici (w y)
  have hT (y : positions L) : MeasurableSet (T y) := by
    simp only [T]
    split_ifs <;> first | exact measurableSet_Iio | exact measurableSet_Ici
  have he : edgeEvent w x = rectangle {i,j} T := by
    ext ω
    change (ω ∈ chosen w i ∩ (chosen w j)ᶜ) ↔ ω ∈ rectangle {i,j} T
    simp [chosen, rectangle, T, Finset.mem_insert, Finset.mem_singleton, hij.symm]
  rw [measureReal_def, he, measure_rectangle _ hT, Finset.prod_insert (by simp [hij]),
    Finset.prod_singleton]
  simp only [T, if_pos rfl, if_neg hij.symm]
  rw [unitProb_iio (hw _), unitProb_ici (hw _), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (hw _).1, ENNReal.toReal_ofReal (sub_nonneg.mpr (hw _).2)]

lemma chosen_indep {L : ℤ} (w : positions L → ℝ) :
    iIndepSet (chosen w) (sampleProb (positions L)) := by
  classical
  have h := indepRectangle (fun i : positions L ↦ {i}) (by
    intro i j hij
    simpa using hij) (T := fun i ↦ Set.Iio (w i)) fun _ ↦ measurableSet_Iio
  convert h using 1
  funext i
  ext ω
  simp [chosen, rectangle]

def matching (L k c : ℤ) : Finset ↥(validStarts L k) :=
  (validStarts L k).attach.filter fun x ↦ stepClass k x.1 = c

lemma matching_indep {L k c : ℤ} (hk : k ≠ 0) (w : positions L → ℝ) :
    iIndepSet (fun x : ↥(matching L k c) ↦ edgeEvent w x.1)
      (sampleProb (positions L)) := by
  classical
  let D (x : ↥(matching L k c)) : Finset (positions L) := {leftEnd x.1,rightEnd x.1}
  let T (i : positions L) := if stepClass k i.1 = c then Set.Iio (w i) else Set.Ici (w i)
  have hT (i : positions L) : MeasurableSet (T i) := by
    simp only [T]
    split_ifs <;> first | exact measurableSet_Iio | exact measurableSet_Ici
  have hleft (x : ↥(matching L k c)) : stepClass k (leftEnd x.1).1 = c :=
    (Finset.mem_filter.mp x.2).2
  have hright (x : ↥(matching L k c)) : stepClass k (rightEnd x.1).1 ≠ c := by
    intro h
    exact stepClass_next x.1.1 hk (h.trans (hleft x).symm)
  have hD : Pairwise fun x y ↦ Disjoint (D x) (D y) := by
    intro x y hxy
    have h₁ : leftEnd x.1 ≠ leftEnd y.1 := by
      intro h
      apply hxy
      apply Subtype.ext
      exact Subtype.ext (congrArg (fun v : positions L ↦ (v : ℤ)) h)
    have h₂ : leftEnd x.1 ≠ rightEnd y.1 := by
      intro h
      exact hright y (h ▸ hleft x)
    have h₃ : rightEnd x.1 ≠ leftEnd y.1 := by
      intro h
      exact hright x (h.symm ▸ hleft y)
    have h₄ : rightEnd x.1 ≠ rightEnd y.1 := by
      intro h
      apply hxy
      have he := congrArg Subtype.val h
      change x.1.1-k = y.1.1-k at he
      exact Subtype.ext (Subtype.ext (by omega))
    simp [D, h₁.symm, h₂.symm, h₃.symm, h₄.symm]
  have he : (fun x : ↥(matching L k c) ↦ edgeEvent w x.1) =
      fun x ↦ rectangle (D x) T := by
    funext x
    ext ω
    simp [edgeEvent, chosen, rectangle, D, T, hleft, hright, Finset.mem_insert, Finset.mem_singleton]
  rw [he]
  exact indepRectangle D hD hT

private lemma subG_mono {Ω : Type*} [MeasurableSpace Ω] {X : Ω → ℝ}
    {μ : Measure Ω} {c d : ℝ≥0} (h : HasSubgaussianMGF X c μ)
    (hcd : c ≤ d) : HasSubgaussianMGF X d μ where
  integrable_exp_mul := h.integrable_exp_mul
  mgf_le t := (h.mgf_le t).trans (Real.exp_le_exp.mpr (by gcongr))

def countCentered {L : ℤ} (w : positions L → ℝ) (ω : positions L → ℝ) : ℝ :=
  (∑ i, eventVal (chosen w i) ω) - ∑ i, w i

def edgeCentered {L : ℤ} (w : positions L → ℝ) (k : ℤ) (ω : positions L → ℝ) : ℝ :=
  (∑ x : ↥(validStarts L k), eventVal (edgeEvent w x) ω) -
    ∑ x : ↥(validStarts L k), w (leftEnd x) * (1-w (rightEnd x))

lemma count_concentration {L : ℤ} {w : positions L → ℝ}
    (hw : ∀ i, w i ∈ Set.Icc (0 : ℝ) 1) :
    HasSubgaussianMGF (countCentered w) (L.toNat : ℝ≥0) (sampleProb (positions L)) := by
  have h := subGaussian_events (chosen_meas w) (chosen_indep w) univ
  simp_rw [chosen_mean hw] at h
  have hc : (univ : Finset (positions L)).card = L.toNat := by
    simp [positions, Int.card_Ico]
  rw [hc] at h
  exact subG_mono h (div_le_self zero_le (by norm_num))

lemma edge_concentration {L k : ℤ} {w : positions L → ℝ} (hk : k ≠ 0)
    (hw : ∀ i, w i ∈ Set.Icc (0 : ℝ) 1) :
    HasSubgaussianMGF (edgeCentered w k) (L.toNat : ℝ≥0) (sampleProb (positions L)) := by
  classical
  let μ := sampleProb (positions L)
  let S (c : ℤ) := matching L k c
  let E (x : ↥(validStarts L k)) := edgeEvent w x
  let X (c : ℤ) (ω : positions L → ℝ) :=
    (∑ x ∈ S c, eventVal (E x) ω) - ∑ x ∈ S c, μ.real (E x)
  have hG (c : ℤ) : HasSubgaussianMGF (X c) (((S c).card : ℝ≥0) / 4) μ := by
    have hm (x : ↥(S c)) : MeasurableSet (E x.1) :=
      (chosen_meas w (leftEnd x.1)).inter (chosen_meas w (rightEnd x.1)).compl
    have h := subGaussian_events hm (matching_indep hk w) univ
    unfold X
    have h₁ (ω : positions L → ℝ) := Finset.sum_attach (S c) (fun x ↦ eventVal (E x) ω)
    have h₂ := Finset.sum_attach (S c) (fun x ↦ μ.real (E x))
    simp_rw [← h₁, ← h₂]
    simpa only [Fintype.card_coe, Finset.card_univ, Finset.univ_eq_attach, Finset.card_attach, μ] using h
  have hc (c : ℤ) : (S c).card ≤ L.toNat := by
    calc
      _ ≤ (validStarts L k).attach.card := Finset.card_filter_le _ _
      _ ≤ (Ico 0 L).card := by
        rw [Finset.card_attach]
        exact Finset.card_filter_le _ _
      _ = _ := by simp [Int.card_Ico]
  let C : ℝ≥0 := (L.toNat : ℝ≥0) / 4
  have hd (c : ℤ) : (((S c).card : ℝ≥0) / 4) ≤ C := by
    dsimp [C]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hc c) (by norm_num)
  have h := (subG_mono (hG 0) (hd 0)).add (subG_mono (hG 1) (hd 1))
  have hC : (C.sqrt + C.sqrt)^2 = (L.toNat : ℝ≥0) := by
    calc
      _ = 4 * C.sqrt^2 := by ring
      _ = _ := by rw [NNReal.sq_sqrt]; dsimp [C]; ring
  rw [hC] at h
  have hg (f : ↥(validStarts L k) → ℝ) :
      ∑ x ∈ S 0, f x + ∑ x ∈ S 1, f x = ∑ x, f x := by
    rw [← Finset.sum_union (by
      rw [Finset.disjoint_left]
      intro x hx hy
      have h0 := (Finset.mem_filter.mp hx).2
      have h1 := (Finset.mem_filter.mp hy).2
      omega)]
    congr 1
    ext x
    simp only [S, matching, Finset.mem_union, Finset.mem_filter, Finset.mem_attach, true_and,
      Finset.mem_univ, iff_true]
    unfold stepClass
    omega
  convert h using 1
  ext ω
  change (∑ x, eventVal (E x) ω) - ∑ x, w (leftEnd x) * (1-w (rightEnd x)) = _
  unfold X
  simp_rw [show ∀ x, μ.real (E x) = w (leftEnd x) * (1-w (rightEnd x)) from edge_mean hk hw]
  rw [← hg fun x ↦ eventVal (E x) ω, ← hg fun x ↦ w (leftEnd x) * (1-w (rightEnd x))]
  dsimp [E]
  ring

end OverlapSample

namespace OverlapSample

lemma exists_good_sample {L : ℤ} {ε : ℝ} (hL : 0 < L) (hε : 0 ≤ ε)
    (hεL : (2 * (L : ℝ) + 3) * Real.exp (-ε^2/(2*(L : ℝ))) < 1)
    {w : positions L → ℝ} (hw : ∀ i, w i ∈ Set.Icc (0 : ℝ) 1) :
    ∃ ω, abs (countCentered w ω) < ε ∧
      ∀ k : ℤ, -L ≤ k → k ≤ L → k ≠ 0 → edgeCentered w k ω < ε := by
  classical
  let μ := sampleProb (positions L)
  let c := Real.exp (-ε^2/(2*(L : ℝ)))
  let E₀ : Set (positions L → ℝ) := {ω | ε ≤ countCentered w ω}
  let E₁ : Set (positions L → ℝ) := {ω | ε ≤ -countCentered w ω}
  let E (k : ℤ) : Set (positions L → ℝ) := {ω | ε ≤ edgeCentered w k ω}
  let S := (Icc (-L) L).filter (· ≠ 0)
  have hcast : (L.toNat : ℝ) = L := by exact_mod_cast (Int.toNat_of_nonneg hL.le)
  have h₀ : μ.real E₀ ≤ c := by
    simpa [μ, E₀, c, hcast] using (count_concentration hw).measure_ge_le hε
  have h₁ : μ.real E₁ ≤ c := by
    simpa [μ, E₁, c, hcast] using (count_concentration hw).neg.measure_ge_le hε
  have hE (k : ℤ) (hk : k ∈ S) : μ.real (E k) ≤ c := by
    have hk' := (Finset.mem_filter.mp hk).2
    simpa [μ, E, c, hcast] using (edge_concentration hk' hw).measure_ge_le hε
  have hS : (S.card : ℝ) ≤ 2 * (L : ℝ) + 1 := by
    have hc : ((Icc (-L) L).card : ℤ) = 2*L+1 := by
      rw [Int.card_Icc, Int.toNat_of_nonneg (by omega)]
      omega
    have ht : (S.card : ℤ) ≤ 2*L+1 := by
      rw [← hc]
      exact_mod_cast Finset.card_filter_le (Icc (-L) L) (· ≠ (0:ℤ))
    exact_mod_cast ht
  let B := E₀ ∪ E₁ ∪ (⋃ k ∈ S, E k)
  have hb : μ.real B < 1 := by
    calc
      _ ≤ μ.real E₀ + μ.real E₁ + ∑ k ∈ S, μ.real (E k) := by
        exact (measureReal_union_le _ _).trans (add_le_add
          (measureReal_union_le _ _) (measureReal_biUnion_finset_le _ _))
      _ ≤ c + c + ∑ _k ∈ S, c := by
        exact add_le_add (add_le_add h₀ h₁) (Finset.sum_le_sum hE)
      _ ≤ (2 * (L : ℝ) + 3) * c := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        have hm := mul_le_mul_of_nonneg_right hS (show 0 ≤ c from (Real.exp_pos _).le)
        linarith
      _ < 1 := hεL
  have hb' : B ≠ Set.univ := by
    intro h
    rw [h] at hb
    simp [μ,measureReal_def] at hb
  obtain ⟨ω,hω⟩ := (Set.ne_univ_iff_exists_notMem B).mp hb'
  refine ⟨ω, ?_, ?_⟩
  · apply abs_lt.mpr
    have hω₀ : ω ∉ E₀ := fun h ↦ hω (Or.inl (Or.inl h))
    have hω₁ : ω ∉ E₁ := fun h ↦ hω (Or.inl (Or.inr h))
    change ¬ ε ≤ countCentered w ω at hω₀
    change ¬ ε ≤ -countCentered w ω at hω₁
    exact ⟨by linarith, lt_of_not_ge hω₀⟩
  · intro k hk₀ hk₁ hk₂
    apply lt_of_not_ge
    intro h
    exact hω (Or.inr (Set.mem_iUnion₂.mpr
      ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hk₀,hk₁⟩,hk₂⟩, h⟩))

def chosenFinset {L : ℤ} (w : positions L → ℝ) (ω : positions L → ℝ) : Finset ℤ :=
  (univ.filter fun i : positions L ↦ ω i < w i).image Subtype.val

lemma chosen_subset {L : ℤ} (w : positions L → ℝ) (ω : positions L → ℝ) :
    chosenFinset w ω ⊆ Ico 0 L := by
  intro i hi
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
  exact j.2

lemma end_in_chosen {L : ℤ} (w : positions L → ℝ) (ω : positions L → ℝ)
    (i : positions L) : (i : ℤ) ∈ chosenFinset w ω ↔ ω ∈ chosen w i := by
  simp only [chosenFinset, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    chosen, Set.mem_preimage, Set.mem_Iio]
  constructor
  · rintro ⟨j,hj,hji⟩
    exact Subtype.ext hji ▸ hj
  · exact fun h ↦ ⟨i,h,rfl⟩

lemma count_eq {L : ℤ} (w : positions L → ℝ) (ω : positions L → ℝ) :
    (∑ i, eventVal (chosen w i) ω) = ((chosenFinset w ω).card : ℝ) := by
  classical
  rw [chosenFinset, Finset.card_image_of_injective _ Subtype.val_injective]
  simp only [eventVal, chosen, Set.indicator_apply, Set.mem_preimage, Set.mem_Iio, Finset.sum_boole]

lemma edge_count_eq {L k : ℤ} (w : positions L → ℝ) (ω : positions L → ℝ) :
    (∑ x : ↥(validStarts L k), eventVal (edgeEvent w x) ω) =
      (Erdos36.Overlap (chosenFinset w ω) (Ico 0 L \ chosenFinset w ω) k : ℝ) := by
  classical
  let S := (univ : Finset ↥(validStarts L k)).filter fun x ↦ ω ∈ edgeEvent w x
  have hs : (∑ x : ↥(validStarts L k), eventVal (edgeEvent w x) ω) = (S.card : ℝ) := by
    simp only [S, eventVal, Set.indicator_apply, Finset.sum_boole]
  rw [hs]
  congr 1
  refine Finset.card_bij (fun x _ ↦ (x.1,x.1-k)) ?_ ?_ ?_
  · intro x hx
    have h := (Finset.mem_filter.mp hx).2
    change ω ∈ chosen w (leftEnd x) ∧ ω ∉ chosen w (rightEnd x) at h
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨(end_in_chosen w ω _).mpr h.1,
      Finset.mem_sdiff.mpr ⟨(rightEnd x).2,fun hz ↦ h.2 ((end_in_chosen w ω _).mp hz)⟩⟩, ?_⟩
    change x.1-(x.1-k)=k
    omega
  · intro x hx y hy h
    exact Subtype.ext (congrArg Prod.fst h)
  · intro p hp
    obtain ⟨hp,hk⟩ := Finset.mem_filter.mp hp
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hp
    obtain ⟨hb₁,hb₂⟩ := Finset.mem_sdiff.mp hb
    have hEq : p.1-k = p.2 := by omega
    let x : ↥(validStarts L k) := ⟨p.1, Finset.mem_filter.mpr ⟨chosen_subset w ω ha,hEq.symm ▸ hb₁⟩⟩
    refine ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩, Prod.ext rfl hEq⟩
    change ω ∈ chosen w (leftEnd x) ∧ ω ∉ chosen w (rightEnd x)
    exact ⟨(end_in_chosen w ω _).mp ha,
      fun h ↦ hb₂ (hEq ▸ (end_in_chosen w ω _).mpr h)⟩

end OverlapSample

open Erdos36 Finset

namespace OverlapLimit

private lemma overlap_mono {A B A' B' : Finset ℤ}
    (ha : A ⊆ A') (hb : B ⊆ B') (k : ℤ) :
    Overlap A B k ≤ Overlap A' B' k := by
  apply Finset.card_le_card
  intro p hp
  obtain ⟨hm,hk⟩ := Finset.mem_filter.mp hp
  obtain ⟨hx,hy⟩ := Finset.mem_product.mp hm
  exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha hx,hb hy⟩,hk⟩

lemma balance {S A : Finset ℤ} {m : ℕ} (hS : S.card = 2*m) (hA : A ⊆ S) :
    ∃ A' B' : Finset ℤ, Disjoint A' B' ∧ A' ∪ B' = S ∧ A'.card = B'.card ∧
      ∀ k : ℤ, (Overlap A' B' k : ℝ) ≤
        Overlap A (S \ A) k + |(A.card : ℝ)-m| := by
  classical
  have hCard : (S \ A).card = 2*m - A.card := by
    rw [Finset.card_sdiff_of_subset hA, hS]
  have hAa : A.card ≤ 2*m := by simpa [hS] using Finset.card_le_card hA
  by_cases hm : m ≤ A.card
  · obtain ⟨A',hA',hA'c⟩ := Finset.exists_subset_card_eq hm
    let B' := S \ A'
    have hb : B' = (S \ A) ∪ (A \ A') := by
      ext x
      simp only [B',Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨hxs,hxa'⟩
        by_cases hxa : x ∈ A
        · exact Or.inr ⟨hxa,hxa'⟩
        · exact Or.inl ⟨hxs,hxa⟩
      · rintro (⟨hxs,hxa⟩ | ⟨hxa,hxa'⟩)
        · exact ⟨hxs, fun h ↦ hxa (hA' h)⟩
        · exact ⟨hA hxa,hxa'⟩
    have hs : A' ⊆ S := hA'.trans hA
    refine ⟨A',B',Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hs, ?_, ?_⟩
    · dsimp [B']
      rw [Finset.card_sdiff_of_subset hs, hS, hA'c]
      omega
    · intro k
      rw [hb]
      have h := extended_overlap A (S \ A) ∅ (A \ A') k
      simp only [Finset.union_empty,Finset.card_empty,add_zero] at h
      rw [Finset.card_sdiff_of_subset hA', hA'c] at h
      have hh := (overlap_mono hA' rfl.subset k).trans h
      rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hm))]
      have hhR : (Overlap A' ((S \ A) ∪ (A \ A')) k : ℝ) ≤
          (Overlap A (S \ A) k : ℝ) + ((A.card-m : ℕ) : ℝ) := by exact_mod_cast hh
      simpa [Nat.cast_sub hm] using hhR
  · have hBlarge : m ≤ (S \ A).card := by omega
    obtain ⟨B',hB',hB'c⟩ := Finset.exists_subset_card_eq hBlarge
    let A' := S \ B'
    have ha : A' = A ∪ ((S \ A) \ B') := by
      ext x
      simp only [A',Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨hxs,hxb'⟩
        by_cases hxa : x ∈ A
        · exact Or.inl hxa
        · exact Or.inr ⟨⟨hxs,hxa⟩,hxb'⟩
      · rintro (hxa | ⟨⟨hxs,hxa⟩,hxb'⟩)
        · exact ⟨hA hxa,fun h ↦ (Finset.mem_sdiff.mp (hB' h)).2 hxa⟩
        · exact ⟨hxs,hxb'⟩
    have hs : B' ⊆ S := hB'.trans Finset.sdiff_subset
    refine ⟨A',B',Finset.sdiff_disjoint, ?_, ?_, ?_⟩
    · rw [union_comm]
      exact Finset.union_sdiff_of_subset hs
    · dsimp [A']
      rw [Finset.card_sdiff_of_subset hs, hS, hB'c]
      omega
    · intro k
      rw [ha]
      have h := extended_overlap A (S \ A) ((S \ A) \ B') ∅ k
      simp only [Finset.union_empty,Finset.card_empty,add_zero] at h
      rw [Finset.card_sdiff_of_subset hB', hB'c] at h
      have hh := (overlap_mono rfl.subset hB' k).trans h
      have hf : ((S \ A).card - m : ℕ) = m-A.card := by omega
      rw [hf] at hh
      have hhR : (Overlap (A ∪ ((S \ A) \ B')) B' k : ℝ) ≤
          (Overlap A (S \ A) k : ℝ) + ((m-A.card : ℕ) : ℝ) := by exact_mod_cast hh
      rw [Nat.cast_sub (by omega : A.card ≤ m)] at hhR
      rwa [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast (show A.card ≤ m by omega))),
        neg_sub]

end OverlapLimit

open OverlapSample OverlapProfile Erdos36 Finset

private theorem hauglandUpperAtScale {b : ℕ} (hbNat : 0 < b)
    (hsmall : (2 * ((102*(b : ℤ) : ℤ) : ℝ) + 3) *
      Real.exp (-((b : ℝ)/10^18)^2 / (2*((102*(b : ℤ) : ℤ) : ℝ))) < 1) :
    Filter.atTop.limsup Erdos36.MinOverlapQuotient ≤ 0.3809268534330870 := by
  classical
  let m : ℕ := 51*b
  let L : ℤ := 102*(b : ℤ)
  let ε : ℝ := (b : ℝ) / 10^18
  let α : ℝ := 0.380926853433087
  have hb : 0 < (b : ℤ) := by exact_mod_cast hbNat
  have hL : 0 < L := by positivity
  have hε : 0 ≤ ε := by positivity
  have hm : 0 < m := by dsimp [m]; positivity
  have hL' : L = 2*(m : ℤ) := by simp [L,m]; ring
  let w (i : positions L) := weight ((i : ℤ)/(b : ℤ))
  have hw (i : positions L) : w i ∈ Set.Icc (0 : ℝ) 1 :=
    weightCap ((div_mem_block hb).mpr i.2)
  have hwm : (∑ i : positions L, w i) = (m : ℝ) := by
    calc
      _ = ∑ x ∈ Ico 0 L, weight (x/(b : ℤ)) :=
        Finset.sum_coe_sort (Ico 0 L) (fun x : ℤ ↦ weight (x/(b : ℤ)))
      _ = _ := by rw [show L = 102*(b : ℤ) by rfl, scaledMass hb]; simp [m]
  obtain ⟨ω,hcount,hedge⟩ := exists_good_sample hL hε hsmall hw
  rw [countCentered, count_eq, hwm] at hcount
  have hScard : (Ico 0 L).card = 2*m := by
    have he : ((2*m : ℕ) : ℤ) = 2*(m : ℤ) := by push_cast; rfl
    rw [Int.card_Ico, sub_zero, hL', ← he, Int.toNat_natCast]
  obtain ⟨A,B,hd,hunion,hcard,hbalanced⟩ :=
    OverlapLimit.balance hScard (chosen_subset w ω)
  have hA : A ⊆ Ico 0 L := hunion ▸ Finset.subset_union_left
  have hB : B ⊆ Ico 0 L := hunion ▸ Finset.subset_union_right
  have hAB (k : ℤ) : (Overlap A B k : ℝ) ≤ α * (m : ℝ) := by
    by_cases hk : -L ≤ k ∧ k ≤ L ∧ k ≠ 0
    · have h := hedge k hk.1 hk.2.1 hk.2.2
      rw [edgeCentered, edge_count_eq] at h
      have hsum : (∑ x : ↥(validStarts L k), w (leftEnd x) * (1-w (rightEnd x))) =
          ∑ x ∈ pairStarts (102*(b : ℤ)) k, weight (x/(b : ℤ)) *
            (1-weight ((x-k)/(b : ℤ))) := by
        change (∑ x : ↥(validStarts L k), weight ((x : ℤ)/(b : ℤ)) *
            (1-weight (((x : ℤ)-k)/(b : ℤ)))) = _
        exact Finset.sum_coe_sort (validStarts L k) (fun x : ℤ ↦
          weight (x/(b : ℤ)) * (1-weight ((x-k)/(b : ℤ))))
      rw [hsum] at h
      have hwBound := scaledBound hb k
      have hmargin : 2*ε ≤ (b : ℝ)*(1/10^17) := by
        have hbR : (0 : ℝ) ≤ b := by positivity
        dsimp [ε]
        norm_num1
        linarith only [hbR]
      have hbal := hbalanced k
      change (Overlap A B k : ℝ) ≤
        (Overlap (chosenFinset w ω) (Ico 0 L \ chosenFinset w ω) k : ℝ) +
          abs (((chosenFinset w ω).card : ℝ) - m) at hbal
      have heq : α*(m : ℝ) = (b : ℝ)*(51*α) := by simp [m]; ring
      rw [heq]
      rw [mul_sub, show ((b : ℤ) : ℝ) = (b : ℝ) by norm_cast] at hwBound
      change _ ≤ (b : ℝ)*(51*α) - (b : ℝ)*(1/10^17) at hwBound
      let W := ∑ x ∈ pairStarts (102*(b : ℤ)) k, weight (x/(b : ℤ)) *
        (1-weight ((x-k)/(b : ℤ)))
      let C := (b : ℝ)*(51*α)
      let D := (b : ℝ)*(1/10^17)
      have hfirst : (Overlap A B k : ℝ) ≤ (W + ε) + ε :=
        hbal.trans (add_le_add
          (by simpa only [add_comm ε] using (sub_lt_iff_lt_add.mp h).le) hcount.le)
      have hmiddle : W + (ε + ε) ≤ (C - D) + D :=
        add_le_add hwBound (by rw [← two_mul]; exact hmargin)
      calc
        _ ≤ (W + ε) + ε := hfirst
        _ = W + (ε + ε) := add_assoc _ _ _
        _ ≤ (C - D) + D := hmiddle
        _ = C := sub_add_cancel _ _
    · have hzero : Overlap A B k = 0 := by
        unfold Overlap
        apply Finset.card_eq_zero.mpr
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro p hp
        obtain ⟨hmemb,hk'⟩ := Finset.mem_filter.mp hp
        obtain ⟨ha,hbb⟩ := Finset.mem_product.mp hmemb
        have ha' := Finset.mem_Ico.mp (hA ha)
        have hb' := Finset.mem_Ico.mp (hB hbb)
        apply hk
        refine ⟨by omega, by omega, ?_⟩
        intro hz
        have he : p.1 = p.2 := by omega
        exact Finset.disjoint_left.mp hd ha (he.symm ▸ hbb)
      simpa [hzero] using (show 0 ≤ α * (m : ℝ) by positivity)
  let c : ℕ := ⌊α * (m : ℝ)⌋₊
  have hc (k : ℤ) : Overlap A B k ≤ c := Nat.le_floor (hAB k)
  have hcl : (c : ℝ) ≤ α * (m : ℝ) := Nat.floor_le (by positivity)
  have hα : α = 0.3809268534330870 := by norm_num [α]
  rw [OverlapLimit.tendsto_limit.limsup_eq, ← hα]
  exact (OverlapLimit.limit_le_word_bound hm hd (hunion.trans (congrArg (Ico 0) hL'))
    hcard hc).trans ((div_le_iff₀ (by exact_mod_cast hm : (0 : ℝ) < m)).mpr hcl)

theorem OMA.solution : type_of% @Erdos36.minimum_overlap.variants.upper.haugland_2022 := by
  let b : ℕ := 10^100
  apply hauglandUpperAtScale (b := b) (by norm_num [b])
  let L : ℝ := ((102 * (b : ℤ) : ℤ) : ℝ)
  let ε : ℝ := (b : ℝ) / 10^18
  let t := ε^2/(2*L)
  have ht : 0 ≤ t := by positivity
  have hlt : 2*L+3 < t^2/2 := by norm_num [t,ε,L,b]
  have he : t^2/2 ≤ Real.exp t := by
    have h := Real.quadratic_le_exp_of_nonneg ht
    linarith
  change (2*L+3) * Real.exp (-ε^2/(2*L)) < 1
  have heq : -ε^2/(2*L) = -t := by dsimp [t]; ring
  rw [heq, Real.exp_neg, ← div_eq_mul_inv]
  exact (div_lt_one (Real.exp_pos _)).mpr (hlt.trans_le he)