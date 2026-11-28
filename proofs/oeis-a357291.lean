import OMAStatements.S_oeis_a357291
import Mathlib

namespace A357291Aux
open OMA.S_oeis_a357291

def K (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range (n+1) ×ˢ Finset.range (n+1) ×ˢ Finset.range (n+1)).filter
    (fun x => 0 < x.2.2 ∧ x.2.2 < x.2.1 ∧ x.2.2 + 2 * x.2.1 < x.1)

def mk (x : ℕ × ℕ × ℕ) (T : Finset ℕ) : Finset ℕ := insert x.2.2 (insert x.2.1 (insert x.1 T))

def fam (x : ℕ × ℕ × ℕ) : Finset (Finset ℕ) :=
  ((Finset.Ioo x.2.1 (x.1 - x.2.2 - x.2.1)).powerset).image (mk x)

def S (n : ℕ) : Finset (Finset ℕ) := (K n).biUnion fam

lemma frame_unique {s : Finset ℕ} {u v z u' v' z' : ℕ} (h : Frame s u v z)
    (h' : Frame s u' v' z') : u = u' ∧ v = v' ∧ z = z' := by
  obtain ⟨hu0, huv, hz, hu, hv, hzs, hall⟩ := h
  obtain ⟨hu0', huv', hz', hu', hv', hzs', hall'⟩ := h'
  have a1 := hall' u hu
  have a2 := hall u' hu'
  have e1 : u = u' := by omega
  subst e1
  have b1 := hall' v hv
  have b2 := hall v' hv'
  have e2 : v = v' := by omega
  subst e2
  have c1 := hall' z hzs
  have c2 := hall z' hzs'
  omega

lemma frame_mk {x : ℕ × ℕ × ℕ} {T : Finset ℕ} (hx : 0 < x.2.2 ∧ x.2.2 < x.2.1 ∧ x.2.2 + 2 * x.2.1 < x.1)
    (hT : T ⊆ Finset.Ioo x.2.1 (x.1 - x.2.2 - x.2.1)) : Frame (mk x T) x.2.2 x.2.1 x.1 := by
  refine ⟨hx.1, hx.2.1, hx.2.2, by simp [mk], by simp [mk], by simp [mk], ?_⟩
  intro w hw
  simp only [mk, Finset.mem_insert] at hw
  rcases hw with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · have := hT h
    rw [Finset.mem_Ioo] at this
    right; right; right; omega

lemma good_iff (n : ℕ) (s : Finset ℕ) : Good n s ↔ s ∈ S n := by
  constructor
  · rintro ⟨u, v, z, hzn, hF⟩
    obtain ⟨hu0, huv, hz, hu, hv, hzs, hall⟩ := hF
    simp only [S, Finset.mem_biUnion, fam, Finset.mem_image, Finset.mem_powerset]
    refine ⟨(z, v, u), ?_, s.filter (fun w => v < w ∧ w < z - u - v), ?_, ?_⟩
    · simp only [K, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      omega
    · intro w hw
      simp only [Finset.mem_filter] at hw
      simp only [Finset.mem_Ioo]
      exact hw.2
    · ext w
      simp only [mk, Finset.mem_insert, Finset.mem_filter]
      constructor
      · rintro (h | h | h | h)
        · subst h; exact hu
        · subst h; exact hv
        · subst h; exact hzs
        · exact h.1
      · intro hw
        rcases hall w hw with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · right; right; right; exact ⟨hw, h.1, by omega⟩
  · intro hs
    simp only [S, Finset.mem_biUnion, fam, Finset.mem_image, Finset.mem_powerset] at hs
    obtain ⟨x, hx, T, hT, rfl⟩ := hs
    simp only [K, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hx
    exact ⟨x.2.2, x.2.1, x.1, by omega, frame_mk hx.2 hT⟩

lemma card_fam (x : ℕ × ℕ × ℕ) (hx : 0 < x.2.2 ∧ x.2.2 < x.2.1 ∧ x.2.2 + 2 * x.2.1 < x.1) :
    (fam x).card = 2 ^ (x.1 - x.2.2 - 2 * x.2.1 - 1) := by
  unfold fam
  rw [Finset.card_image_of_injOn, Finset.card_powerset, Nat.card_Ioo]
  · congr 1; omega
  · intro T1 h1 T2 h2 he
    simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, Finset.coe_subset] at h1 h2
    have key : ∀ A B : Finset ℕ, A ⊆ Finset.Ioo x.2.1 (x.1 - x.2.2 - x.2.1) → mk x A = mk x B →
        A ⊆ B := by
      intro A B hA hAB w hw
      have hw' := hA hw
      rw [Finset.mem_Ioo] at hw'
      have : w ∈ mk x B := hAB ▸ (by simp [mk, hw])
      simp only [mk, Finset.mem_insert] at this
      rcases this with h | h | h | h
      · omega
      · omega
      · omega
      · exact h
    exact Finset.Subset.antisymm (key T1 T2 h1 he) (key T2 T1 h2 he.symm)

lemma card_S (n : ℕ) : (S n).card = ∑ x ∈ K n, 2 ^ (x.1 - x.2.2 - 2 * x.2.1 - 1) := by
  unfold S
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro x hx
    simp only [K, Finset.mem_filter] at hx
    exact card_fam x hx.2
  · intro x hx y hy hxy
    rw [Function.onFun, Finset.disjoint_left]
    intro s hsx hsy
    simp only [K, Finset.coe_filter, Set.mem_ofPred_eq] at hx hy
    simp only [fam, Finset.mem_image, Finset.mem_powerset] at hsx hsy
    obtain ⟨T, hT, rfl⟩ := hsx
    obtain ⟨T', hT', he⟩ := hsy
    have f1 := frame_mk hx.2 hT
    have f2 := frame_mk hy.2 hT'
    rw [he] at f2
    obtain ⟨e1, e2, e3⟩ := frame_unique f1 f2
    apply hxy
    ext <;> simp [e1, e2, e3]

lemma count_eq (n : ℕ) : literalCount n = (S n).card := by
  unfold literalCount
  rw [Nat.card_congr (Equiv.subtypeEquivRight (good_iff n))]
  simp

open Finset

def g (z : ℕ) : ℕ := ∑ v ∈ range (z+1), ∑ u ∈ range (z+1),
  if 0 < u ∧ u < v ∧ u + 2*v < z then 2^(z-u-2*v-1) else 0

def h (z : ℕ) : ℕ := ∑ v ∈ range (z+1), ∑ u ∈ range (z+1),
  if 0 < u ∧ u < v ∧ u + 2*v = z then 1 else 0

lemma sumK (n : ℕ) : ∑ x ∈ K n, 2^(x.1 - x.2.2 - 2*x.2.1 - 1) = ∑ z ∈ range (n+1), g z := by
  rw [K, Finset.sum_filter, Finset.sum_product]
  apply sum_congr rfl
  intro z hz
  rw [Finset.sum_product]
  simp only [mem_range] at hz
  have sub : range (z+1) ⊆ range (n+1) := range_subset_range.2 (by omega)
  unfold g
  calc (∑ v ∈ range (n+1), ∑ u ∈ range (n+1),
        if 0 < (z, v, u).2.2 ∧ (z, v, u).2.2 < (z, v, u).2.1 ∧ (z, v, u).2.2 + 2 * (z, v, u).2.1 < (z, v, u).1
        then 2 ^ ((z, v, u).1 - (z, v, u).2.2 - 2 * (z, v, u).2.1 - 1) else 0)
      = ∑ v ∈ range (n+1), ∑ u ∈ range (z+1),
        if 0 < u ∧ u < v ∧ u + 2*v < z then 2^(z-u-2*v-1) else 0 := by
        apply sum_congr rfl
        intro v _
        symm
        apply sum_subset sub
        intro u _ hu
        simp only [mem_range] at hu
        rw [if_neg (by omega)]
    _ = _ := by
        symm
        apply sum_subset sub
        intro v _ hv
        simp only [mem_range] at hv
        apply sum_eq_zero
        intro u _
        rw [if_neg (by omega)]

lemma g_succ (z : ℕ) : g (z+1) = 2 * g z + h z := by
  unfold g h
  rw [sum_range_succ (n := z+1)]
  have h0 : (∑ u ∈ range (z+1+1), if 0 < u ∧ u < z+1 ∧ u + 2*(z+1) < z+1 then 2^(z+1-u-2*(z+1)-1) else 0) = 0 :=
    sum_eq_zero (fun u _ => if_neg (by omega))
  rw [h0, add_zero, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro v hv
  rw [sum_range_succ, if_neg (by omega), add_zero, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro u hu
  by_cases c2 : 0 < u ∧ u < v ∧ u + 2*v < z
  · have c1 : 0 < u ∧ u < v ∧ u + 2*v < z + 1 := by omega
    have c3 : ¬ (0 < u ∧ u < v ∧ u + 2*v = z) := by omega
    rw [if_pos c1, if_pos c2, if_neg c3, add_zero, ← pow_succ']
    congr 1
    omega
  · by_cases c3 : 0 < u ∧ u < v ∧ u + 2*v = z
    · have c1 : 0 < u ∧ u < v ∧ u + 2*v < z + 1 := by omega
      rw [if_pos c1, if_neg c2, if_pos c3]
      have : z + 1 - u - 2*v - 1 = 0 := by omega
      rw [this]
      rfl
    · have c1 : ¬ (0 < u ∧ u < v ∧ u + 2*v < z + 1) := by omega
      rw [if_neg c1, if_neg c2, if_neg c3]
      rfl

lemma h_eq (z : ℕ) : h z = (z-1)/2 - z/3 := by
  unfold h
  have inner : ∀ v ∈ range (z+1), (∑ u ∈ range (z+1), if 0 < u ∧ u < v ∧ u + 2*v = z then 1 else 0)
      = if 2*v < z ∧ z < 3*v then 1 else 0 := by
    intro v hv
    rw [Finset.sum_eq_single (z - 2*v)]
    · split_ifs <;> omega
    · intro u _ hu
      rw [if_neg]
      omega
    · intro hn
      simp only [mem_range] at hn
      omega
  rw [sum_congr rfl inner, sum_boole]
  have : (range (z+1)).filter (fun v => 2*v < z ∧ z < 3*v) = Ioc (z/3) ((z-1)/2) := by
    ext v
    simp only [mem_filter, mem_range, mem_Ioc]
    omega
  rw [this, Nat.card_Ioc]
  rfl

def dd : ℕ → ℕ
  | 0 => 40
  | 1 => 10
  | 2 => 20
  | 3 => 26
  | 4 => 24
  | _ => 6

def ee : ℕ → ℕ
  | 0 => 4
  | 1 => 15
  | 2 => 16
  | 3 => 11
  | 4 => 8
  | _ => 23

lemma g_closed (z : ℕ) (hz : 1 ≤ z) : 84 * g z + 14 * z = 2 * 2^z + dd (z % 6) := by
  induction z, hz using Nat.le_induction with
  | base => decide
  | succ z hz ih =>
    rw [g_succ, h_eq, pow_succ]
    have e : (z+1) % 6 = (z % 6 + 1) % 6 := by omega
    rw [e]
    generalize 2^z = X at *
    generalize g z = G at *
    have hr : z % 6 < 6 := Nat.mod_lt _ (by norm_num)
    generalize hr' : z % 6 = r at *
    interval_cases r <;> simp only [dd, Nat.reduceAdd, Nat.reduceMod] at * <;> omega

lemma F_closed (n : ℕ) : 84 * (∑ z ∈ range (n+1), g z) + 7*n^2 + ee (n % 6) = 4*2^n + 14*n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [sum_range_succ]
    have hg := g_closed (n+1) (by omega)
    have hsq : (n+1)^2 = n^2 + 2*n + 1 := by ring
    have hp : 2^(n+1) = 2 * 2^n := by ring
    rw [hsq, hp]
    rw [hp] at hg
    have e : (n+1) % 6 = (n % 6 + 1) % 6 := by omega
    rw [e] at hg ⊢
    clear hp hsq e
    generalize 2^n = X at *
    generalize n^2 = Q at *
    generalize (∑ z ∈ range (n+1), g z) = F at *
    generalize g (n+1) = G at *
    have hr : n % 6 < 6 := Nat.mod_lt _ (by norm_num)
    generalize hr' : n % 6 = r at *
    interval_cases r <;> simp only [dd, ee, Nat.reduceAdd, Nat.reduceMod] at * <;> omega

lemma ee_bound (r : ℕ) : 4 ≤ ee r ∧ ee r ≤ 23 := by
  unfold ee
  split <;> omega

end A357291Aux

open A357291Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a357291.main := by
  intro n
  rw [count_eq, card_S, sumK]
  have hF := F_closed n
  generalize (∑ z ∈ Finset.range (n+1), g z) = F at *
  have hEb := ee_bound (n % 6)
  generalize ee (n % 6) = E at *
  have hE1 : 4 ≤ E := hEb.1
  have hE2 : E ≤ 23 := hEb.2
  have hq : (84 * (F:ℚ) + 7 * (n:ℚ)^2 + E) = 4 * 2^n + 14 * n := by
    have : 84 * F + 7*n^2 + E = 4*2^n + 14*n := by omega
    exact_mod_cast this
  have hE1' : (4:ℚ) ≤ E := by exact_mod_cast hE1
  have hE2' : (E:ℚ) ≤ 23 := by exact_mod_cast hE2
  rw [eq_comm, round_eq, Int.floor_eq_iff]
  push_cast
  constructor <;> linarith
