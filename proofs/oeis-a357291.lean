import OMAStatements.S_oeis_a357291
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace A357291Proof

open OMA.S_oeis_a357291

def triples (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range (n + 1) ×ˢ (Finset.range (n + 1) ×ˢ Finset.range (n + 1))).filter
    fun p => 0 < p.2.1 ∧ p.2.1 < p.2.2 ∧ p.2.1 + 2 * p.2.2 < p.1

def fiber (z u v : ℕ) : Finset (Finset ℕ) :=
  (Finset.Ioo v (z - u - v)).powerset.image fun t => insert u (insert v (insert z t))

def goodFinset (n : ℕ) : Finset (Finset ℕ) :=
  (triples n).biUnion fun p => fiber p.1 p.2.1 p.2.2

lemma mem_fiber_iff {z u v : ℕ} (hu : 0 < u) (huv : u < v) (huz : u + 2 * v < z)
    (s : Finset ℕ) : s ∈ fiber z u v ↔ Frame s u v z := by
  unfold fiber Frame
  simp only [Finset.mem_image, Finset.mem_powerset]
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨hu, huv, huz, by simp, by simp, by simp, ?_⟩
    intro w hw
    simp only [Finset.mem_insert] at hw
    rcases hw with rfl | rfl | rfl | hwt
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · have hioo := ht hwt
      simp only [Finset.mem_Ioo] at hioo
      exact Or.inr (Or.inr (Or.inr ⟨hioo.1, by omega⟩))
  · rintro ⟨_, _, _, hus, hvs, hzs, hall⟩
    refine ⟨s.filter (fun w => v < w ∧ w < z), ?_, ?_⟩
    · intro w hw
      simp only [Finset.mem_filter] at hw
      simp only [Finset.mem_Ioo]
      rcases hall w hw.1 with rfl | rfl | rfl | ⟨hvw, hwz⟩
      · omega
      · omega
      · omega
      · exact ⟨hvw, by omega⟩
    · ext w
      simp only [Finset.mem_insert, Finset.mem_filter]
      constructor
      · rintro (rfl | rfl | rfl | ⟨hws, _⟩)
        · exact hus
        · exact hvs
        · exact hzs
        · exact hws
      · intro hws
        rcases hall w hws with rfl | rfl | rfl | ⟨hvw, hwz⟩
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr ⟨hws, hvw, by omega⟩))

lemma frame_bounds {s : Finset ℕ} {u v z : ℕ} (hf : Frame s u v z) {w : ℕ} (hw : w ∈ s) :
    u ≤ w ∧ w ≤ z ∧ (w ≠ u → v ≤ w) := by
  rcases hf with ⟨hu, huv, huz, _, _, _, hall⟩
  rcases hall w hw with rfl | rfl | rfl | ⟨hvw, hwz⟩
  · exact ⟨le_refl _, by omega, fun h => False.elim (h rfl)⟩
  · exact ⟨by omega, by omega, fun _ => le_refl _⟩
  · exact ⟨by omega, le_refl _, fun _ => by omega⟩
  · exact ⟨by omega, by omega, fun _ => by omega⟩

lemma frame_unique {s : Finset ℕ} {u1 v1 z1 u2 v2 z2 : ℕ}
    (h1 : Frame s u1 v1 z1) (h2 : Frame s u2 v2 z2) :
    (z1, u1, v1) = (z2, u2, v2) := by
  have hu1_in : u1 ∈ s := h1.2.2.2.1
  have hv1_in : v1 ∈ s := h1.2.2.2.2.1
  have hz1_in : z1 ∈ s := h1.2.2.2.2.2.1
  have hu2_in : u2 ∈ s := h2.2.2.2.1
  have hv2_in : v2 ∈ s := h2.2.2.2.2.1
  have hz2_in : z2 ∈ s := h2.2.2.2.2.2.1
  have hu_eq : u1 = u2 := le_antisymm (frame_bounds h1 hu2_in).1 (frame_bounds h2 hu1_in).1
  have hz_eq : z1 = z2 := le_antisymm (frame_bounds h2 hz1_in).2.1 (frame_bounds h1 hz2_in).2.1
  have hv_eq : v1 = v2 := by
    have h12 : v1 ≤ v2 := (frame_bounds h1 hv2_in).2.2 (by have := h2.2.1; omega)
    have h21 : v2 ≤ v1 := (frame_bounds h2 hv1_in).2.2 (by have := h1.2.1; omega)
    omega
  simp [hz_eq, hu_eq, hv_eq]

lemma card_fiber {z u v : ℕ} (hu : 0 < u) (huv : u < v) (huz : u + 2 * v < z) :
    (fiber z u v).card = 2 ^ (z - u - 2 * v - 1) := by
  unfold fiber
  rw [Finset.card_image_of_injOn]
  · rw [Finset.card_powerset, Nat.card_Ioo]
    congr 1
    omega
  · intro t1 ht1 t2 ht2 heq
    dsimp only at heq
    simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, Finset.coe_subset] at ht1 ht2
    ext w
    constructor
    · intro hw1
      have hioo := Finset.mem_Ioo.mp (ht1 hw1)
      have hmem : w ∈ insert u (insert v (insert z t1)) := by simp [hw1]
      rw [heq] at hmem
      simp only [Finset.mem_insert] at hmem
      rcases hmem with rfl | rfl | rfl | hw2
      · omega
      · omega
      · omega
      · exact hw2
    · intro hw2
      have hioo := Finset.mem_Ioo.mp (ht2 hw2)
      have hmem : w ∈ insert u (insert v (insert z t2)) := by simp [hw2]
      rw [← heq] at hmem
      simp only [Finset.mem_insert] at hmem
      rcases hmem with rfl | rfl | rfl | hw1
      · omega
      · omega
      · omega
      · exact hw1

lemma mem_goodFinset_iff (n : ℕ) (s : Finset ℕ) : s ∈ goodFinset n ↔ Good n s := by
  unfold goodFinset Good triples
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Prod.exists]
  constructor
  · rintro ⟨z, u, v, ⟨⟨hz, hu_lt, hv_lt⟩, hu0, huv, huz⟩, hmem⟩
    exact ⟨u, v, z, by omega, (mem_fiber_iff hu0 huv huz s).mp hmem⟩
  · rintro ⟨u, v, z, hzn, hf⟩
    have hu0 := hf.1
    have huv := hf.2.1
    have huz := hf.2.2.1
    exact ⟨z, u, v, ⟨⟨by omega, by omega, by omega⟩, hu0, huv, huz⟩,
      (mem_fiber_iff hu0 huv huz s).mpr hf⟩

lemma literalCount_eq_card (n : ℕ) : literalCount n = (goodFinset n).card := by
  unfold literalCount
  have hequiv : {s : Finset ℕ // Good n s} ≃ {s : Finset ℕ // s ∈ goodFinset n} :=
    Equiv.subtypeEquivRight (fun s => (mem_goodFinset_iff n s).symm)
  rw [Nat.card_congr hequiv, Nat.card_eq_fintype_card, Fintype.card_coe]

def Dsum (n : ℕ) : ℕ :=
  ∑ u ∈ Finset.range (n + 1), ∑ v ∈ Finset.range (n + 1),
    if 0 < u ∧ u < v ∧ u + 2 * v ≤ n then 2 ^ (n - u - 2 * v) else 0

lemma literalCount_succ (n : ℕ) : literalCount (n + 1) = literalCount n + Dsum n := by
  have hcard : ∀ m : ℕ, (goodFinset m).card =
      ∑ z ∈ Finset.range (m + 1), ∑ u ∈ Finset.range (m + 1), ∑ v ∈ Finset.range (m + 1),
        if 0 < u ∧ u < v ∧ u + 2 * v < z then 2 ^ (z - u - 2 * v - 1) else 0 := by
    intro m
    unfold goodFinset
    rw [Finset.card_biUnion]
    · unfold triples
      rw [Finset.sum_filter]
      simp only [Finset.sum_product]
      refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
      split_ifs with h
      · exact card_fiber h.1 h.2.1 h.2.2
      · rfl
    · intro p1 hp1 p2 hp2 hne
      simp only [Finset.mem_coe, triples, Finset.mem_filter] at hp1 hp2
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro s hs1 hs2
      have hf1 := (mem_fiber_iff hp1.2.1 hp1.2.2.1 hp1.2.2.2 s).mp hs1
      have hf2 := (mem_fiber_iff hp2.2.1 hp2.2.2.1 hp2.2.2.2 s).mp hs2
      have heq := frame_unique hf1 hf2
      rcases p1 with ⟨z1, u1, v1⟩
      rcases p2 with ⟨z2, u2, v2⟩
      exact hne heq
  rw [literalCount_eq_card, literalCount_eq_card, hcard (n + 1), hcard n, Finset.sum_range_succ]
  congr 1
  · refine Finset.sum_congr rfl fun z hz => ?_
    have hzn : z < n + 1 := Finset.mem_range.mp hz
    rw [Finset.sum_range_succ]
    have hu_end : (∑ v ∈ Finset.range (n + 2),
        if 0 < n + 1 ∧ n + 1 < v ∧ n + 1 + 2 * v < z then 2 ^ (z - (n + 1) - 2 * v - 1) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro v _
      rw [if_neg (by omega)]
    rw [hu_end, add_zero]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_range_succ, if_neg (by omega), add_zero]
  · unfold Dsum
    rw [Finset.sum_range_succ]
    have hu_end : (∑ v ∈ Finset.range (n + 2),
        if 0 < n + 1 ∧ n + 1 < v ∧ n + 1 + 2 * v < n + 1 then 2 ^ (n + 1 - (n + 1) - 2 * v - 1) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro v _
      rw [if_neg (by omega)]
    rw [hu_end, add_zero]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_range_succ, if_neg (by omega), add_zero]
    refine Finset.sum_congr rfl fun v _ => ?_
    have hiff : (0 < u ∧ u < v ∧ u + 2 * v < n + 1) ↔ (0 < u ∧ u < v ∧ u + 2 * v ≤ n) := by omega
    by_cases hc : 0 < u ∧ u < v ∧ u + 2 * v ≤ n
    · rw [if_pos (hiff.mpr hc), if_pos hc]
      congr 1
      omega
    · rw [if_neg (fun h => hc (hiff.mp h)), if_neg hc]

def S : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | n + 2 => 2 ^ n + S n

lemma S_eq_sum (n : ℕ) :
    ∑ v ∈ Finset.range (n + 4),
      (if 1 < v ∧ 1 + 2 * v ≤ n + 3 then 2 ^ (n + 3 - 1 - 2 * v) else 0) = S n := by
  induction n using S.induct with
  | case1 => decide
  | case2 => decide
  | case3 n ih =>
    unfold S
    rw [← ih]
    rw [Finset.sum_range_succ' _ (n + 5), Finset.sum_range_succ' _ (n + 4),
      Finset.sum_range_succ' _ (n + 3)]
    have h0 : (if 1 < 0 ∧ 1 + 2 * 0 ≤ n + 5 then 2 ^ (n + 5 - 1 - 2 * 0) else 0) = 0 := by simp
    have h1 : (if 1 < 1 ∧ 1 + 2 * 1 ≤ n + 5 then 2 ^ (n + 5 - 1 - 2 * 1) else 0) = 0 := by simp
    have h2 : (if 1 < 2 ∧ 1 + 2 * 2 ≤ n + 5 then 2 ^ (n + 5 - 1 - 2 * 2) else 0) = 2 ^ n := by
      have hexp : n + 5 - 1 - 2 * 2 = n := by omega
      rw [if_pos (by omega), hexp]
    rw [h0, h1, h2, add_zero, add_zero]
    have hsum : (∑ x ∈ Finset.range (n + 3),
        if 1 < x + 3 ∧ 1 + 2 * (x + 3) ≤ n + 5 then 2 ^ (n + 5 - 1 - 2 * (x + 3)) else 0) =
        ∑ v ∈ Finset.range (n + 4),
          if 1 < v ∧ 1 + 2 * v ≤ n + 3 then 2 ^ (n + 3 - 1 - 2 * v) else 0 := by
      rw [Finset.sum_range_succ _ (n + 2)]
      have hend : (if 1 < n + 2 + 3 ∧ 1 + 2 * (n + 2 + 3) ≤ n + 5 then
          2 ^ (n + 5 - 1 - 2 * (n + 2 + 3)) else 0) = 0 := by rw [if_neg (by omega)]
      rw [hend, add_zero]
      rw [Finset.sum_range_succ' _ (n + 3)]
      have hv0 : (if 1 < 0 ∧ 1 + 2 * 0 ≤ n + 3 then 2 ^ (n + 3 - 1 - 2 * 0) else 0) = 0 := by simp
      rw [hv0, add_zero]
      rw [Finset.sum_range_succ' _ (n + 2)]
      have hv1 : (if 1 < 0 + 1 ∧ 1 + 2 * (0 + 1) ≤ n + 3 then
          2 ^ (n + 3 - 1 - 2 * (0 + 1)) else 0) = 0 := by simp
      rw [hv1, add_zero]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hiff : (1 < k + 3 ∧ 1 + 2 * (k + 3) ≤ n + 5) ↔
          (1 < k + 1 + 1 ∧ 1 + 2 * (k + 1 + 1) ≤ n + 3) := by omega
      by_cases hk : 1 < k + 1 + 1 ∧ 1 + 2 * (k + 1 + 1) ≤ n + 3
      · have hexp : n + 5 - 1 - 2 * (k + 3) = n + 3 - 1 - 2 * (k + 1 + 1) := by omega
        rw [if_pos (hiff.mpr hk), if_pos hk, hexp]
      · rw [if_neg (fun h => hk (hiff.mp h)), if_neg hk]
    rw [hsum, add_comm]

lemma Dsum_step3 (n : ℕ) : Dsum (n + 3) = Dsum n + S n := by
  unfold Dsum
  rw [Finset.sum_range_succ' _ (n + 3), Finset.sum_range_succ' _ (n + 2)]
  have hu0 : (∑ v ∈ Finset.range (n + 4),
      if 0 < 0 ∧ 0 < v ∧ 0 + 2 * v ≤ n + 3 then 2 ^ (n + 3 - 0 - 2 * v) else 0) = 0 := by
    simp
  have hu1 : (∑ v ∈ Finset.range (n + 4),
      if 0 < 1 ∧ 1 < v ∧ 1 + 2 * v ≤ n + 3 then 2 ^ (n + 3 - 1 - 2 * v) else 0) = S n := by
    simpa using S_eq_sum n
  rw [hu0, hu1, add_zero]
  congr 1
  have hshift : (∑ x ∈ Finset.range (n + 2), ∑ v ∈ Finset.range (n + 4),
      if 0 < x + 2 ∧ x + 2 < v ∧ x + 2 + 2 * v ≤ n + 3 then 2 ^ (n + 3 - (x + 2) - 2 * v) else 0) =
      ∑ u ∈ Finset.range (n + 1), ∑ v ∈ Finset.range (n + 1),
        if 0 < u ∧ u < v ∧ u + 2 * v ≤ n then 2 ^ (n - u - 2 * v) else 0 := by
    rw [Finset.sum_range_succ' _ (n + 0)]
    have h0' : (∑ v ∈ Finset.range (n + 1),
        if 0 < 0 ∧ 0 < v ∧ 0 + 2 * v ≤ n then 2 ^ (n - 0 - 2 * v) else 0) = 0 := by simp
    rw [h0', add_zero]
    rw [Finset.sum_range_succ _ (n + 1), Finset.sum_range_succ _ n]
    have he1 : (∑ v ∈ Finset.range (n + 4),
        if 0 < n + 1 + 2 ∧ n + 1 + 2 < v ∧ n + 1 + 2 + 2 * v ≤ n + 3 then
          2 ^ (n + 3 - (n + 1 + 2) - 2 * v) else 0) = 0 := by
      apply Finset.sum_eq_zero; intro v _; rw [if_neg (by omega)]
    have he2 : (∑ v ∈ Finset.range (n + 4),
        if 0 < n + 2 ∧ n + 2 < v ∧ n + 2 + 2 * v ≤ n + 3 then
          2 ^ (n + 3 - (n + 2) - 2 * v) else 0) = 0 := by
      apply Finset.sum_eq_zero; intro v _; rw [if_neg (by omega)]
    rw [he1, he2, add_zero, add_zero]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_range_succ' _ (n + 3)]
    have hv0 : (if 0 < x + 2 ∧ x + 2 < 0 ∧ x + 2 + 2 * 0 ≤ n + 3 then
        2 ^ (n + 3 - (x + 2) - 2 * 0) else 0) = 0 := by simp
    rw [hv0, add_zero]
    rw [Finset.sum_range_succ _ (n + 2), Finset.sum_range_succ _ (n + 1)]
    have hve1 : (if 0 < x + 2 ∧ x + 2 < n + 2 + 1 ∧ x + 2 + 2 * (n + 2 + 1) ≤ n + 3 then
        2 ^ (n + 3 - (x + 2) - 2 * (n + 2 + 1)) else 0) = 0 := by rw [if_neg (by omega)]
    have hve2 : (if 0 < x + 2 ∧ x + 2 < n + 1 + 1 ∧ x + 2 + 2 * (n + 1 + 1) ≤ n + 3 then
        2 ^ (n + 3 - (x + 2) - 2 * (n + 1 + 1)) else 0) = 0 := by rw [if_neg (by omega)]
    rw [hve1, hve2, add_zero, add_zero]
    refine Finset.sum_congr rfl fun v _ => ?_
    have hiff : (0 < x + 2 ∧ x + 2 < v + 1 ∧ x + 2 + 2 * (v + 1) ≤ n + 3) ↔
        (0 < x + 1 ∧ x + 1 < v ∧ x + 1 + 2 * v ≤ n) := by omega
    by_cases hv : 0 < x + 1 ∧ x + 1 < v ∧ x + 1 + 2 * v ≤ n
    · rw [if_pos (hiff.mpr hv), if_pos hv]
      congr 1
      omega
    · rw [if_neg (fun h => hv (hiff.mp h)), if_neg hv]
  exact hshift

lemma three_mul_S (n : ℕ) :
    3 * (S n : ℤ) = (2 : ℤ) ^ n - if n % 2 = 0 then 1 else 2 := by
  induction n using S.induct with
  | case1 => decide
  | case2 => decide
  | case3 n ih =>
    unfold S
    push_cast
    have hm : (n + 2) % 2 = n % 2 := by omega
    rw [hm]
    have hp : (2 : ℤ) ^ (n + 2) = 4 * (2 : ℤ) ^ n := by ring
    rw [hp]
    linarith

def rem3 (r : ℕ) : ℤ :=
  match r % 6 with
  | 0 => 4
  | 1 => 15
  | 2 => 16
  | 3 => 11
  | 4 => 8
  | _ => 23

lemma rem3_mod (n : ℕ) : rem3 n = rem3 (n % 6) := by
  unfold rem3
  rw [Nat.mod_mod]

lemma rem3_add_mod (m k : ℕ) : rem3 (m + k) = rem3 (m % 6 + k) := by
  unfold rem3
  have h : (m + k) % 6 = (m % 6 + k) % 6 := by omega
  rw [h]

lemma Dsum_closed (n : ℕ) :
    84 * (Dsum n : ℤ) = 4 * (2 : ℤ) ^ n - 14 * (n : ℤ) + 7 - rem3 (n + 1) + rem3 n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 3
    · interval_cases n <;> decide
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
      have hm := ih m (by omega)
      rw [Dsum_step3 m]
      push_cast
      have hS := three_mul_S m
      have hrem : -42 - rem3 (m + 4) + rem3 (m + 3) + rem3 (m + 1) - rem3 m =
          -28 * (if m % 2 = 0 then (1 : ℤ) else 2) := by
        have hcheck : ∀ r : Fin 6,
            -42 - rem3 (r.val + 4) + rem3 (r.val + 3) + rem3 (r.val + 1) - rem3 r.val =
              -28 * (if r.val % 2 = 0 then (1 : ℤ) else 2) := by decide
        have hr := hcheck ⟨m % 6, Nat.mod_lt _ (by decide)⟩
        have e0 : rem3 m = rem3 (m % 6) := rem3_mod m
        have e1 : rem3 (m + 1) = rem3 (m % 6 + 1) := rem3_add_mod m 1
        have e3 : rem3 (m + 3) = rem3 (m % 6 + 3) := rem3_add_mod m 3
        have e4 : rem3 (m + 4) = rem3 (m % 6 + 4) := rem3_add_mod m 4
        have em2 : m % 2 = (m % 6) % 2 := by omega
        rw [e0, e1, e3, e4, em2]
        exact hr
      have hp : (2 : ℤ) ^ (m + 3) = 8 * (2 : ℤ) ^ m := by ring
      have h1 : m + 3 + 1 = m + 4 := by omega
      rw [h1, hp]
      linarith

lemma literalCount_closed (n : ℕ) :
    252 * (literalCount n : ℤ) =
      12 * (2 : ℤ) ^ n - 21 * (n : ℤ) ^ 2 + 42 * (n : ℤ) - 3 * rem3 n := by
  induction n with
  | zero =>
    have h0 : literalCount 0 = 0 := by
      rw [literalCount_eq_card]
      decide
    rw [h0]
    decide
  | succ n ih =>
    rw [literalCount_succ n]
    push_cast
    have hD := Dsum_closed n
    have hp : (2 : ℤ) ^ (n + 1) = 2 * (2 : ℤ) ^ n := by ring
    rw [hp]
    linarith

lemma main_proof (n : ℕ) :
    (literalCount n : ℤ) = round ((2 : ℚ) ^ n / 21 - (n : ℚ) ^ 2 / 12 + (n : ℚ) / 6) := by
  have hclosed : (252 : ℚ) * ((literalCount n : ℤ) : ℚ) =
      12 * (2 : ℚ) ^ n - 21 * (n : ℚ) ^ 2 + 42 * (n : ℚ) - 3 * (rem3 n : ℚ) := by
    exact_mod_cast literalCount_closed n
  have hrat : (2 : ℚ) ^ n / 21 - (n : ℚ) ^ 2 / 12 + (n : ℚ) / 6 =
      ((literalCount n : ℤ) : ℚ) + 3 * (rem3 n : ℚ) / 252 := by
    linarith
  rw [hrat, round_intCast_add]
  have hb : (0 : ℤ) ≤ rem3 n ∧ rem3 n ≤ 23 := by
    unfold rem3
    have hm : n % 6 < 6 := Nat.mod_lt _ (by decide)
    interval_cases (n % 6) <;> decide
  have hb0 : (0 : ℚ) ≤ (rem3 n : ℚ) := by exact_mod_cast hb.1
  have hb1 : (rem3 n : ℚ) ≤ 23 := by exact_mod_cast hb.2
  have hround0 : round (3 * (rem3 n : ℚ) / 252) = 0 := by
    rw [round_eq, Int.floor_eq_iff]
    push_cast
    constructor <;> linarith
  rw [hround0, add_zero]

end A357291Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a357291.main :=
  A357291Proof.main_proof
