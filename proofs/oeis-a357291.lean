import OMAStatements.S_oeis_a357291
import Mathlib

/-!
# OEIS A357291: the nearest-integer formula

A good set is determined by its frame (u, v, z) together with an arbitrary subset of the
open interval (v, z - u - v). Writing u = a + 1, v = a + b + 2, z = 3a + 2b + c + 6 the
count becomes the sum of 2^c over 3a + 2b + c + 6 ≤ n, which is evaluated in closed form
modulo 6 and compared with the rounding formula.
-/

namespace OMA.A357291

open Finset OMA.S_oeis_a357291

/-- The family of sets with a given frame. -/
def fib (u v z : ℕ) : Finset (Finset ℕ) :=
  (Ioo v (z - u - v)).powerset.image (fun T => insert u (insert v (insert z T)))

theorem mem_fib (u v z : ℕ) (hu : 0 < u) (huv : u < v) (hz : u + 2 * v < z) (s : Finset ℕ) :
    s ∈ fib u v z ↔ Frame s u v z := by
  unfold fib Frame
  constructor
  · intro h
    rw [mem_image] at h
    obtain ⟨T, hT, rfl⟩ := h
    rw [mem_powerset] at hT
    refine ⟨hu, huv, hz, by simp, by simp, by simp, ?_⟩
    intro w hw
    simp only [mem_insert] at hw
    rcases hw with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · have := hT h
      rw [mem_Ioo] at this
      right; right; right
      omega
  · rintro ⟨-, -, -, h1, h2, h3, h4⟩
    rw [mem_image]
    refine ⟨s.filter (fun w => v < w ∧ u + v + w < z), ?_, ?_⟩
    · rw [mem_powerset]
      intro w hw
      rw [mem_filter] at hw
      rw [mem_Ioo]
      omega
    · ext w
      simp only [mem_insert, mem_filter]
      constructor
      · rintro (h | h | h | h)
        · rw [h]; exact h1
        · rw [h]; exact h2
        · rw [h]; exact h3
        · exact h.1
      · intro hw
        rcases h4 w hw with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr ⟨hw, h⟩))

theorem card_fib (u v z : ℕ) (hu : 0 < u) (huv : u < v) (hz : u + 2 * v < z) :
    (fib u v z).card = 2 ^ (z - u - 2 * v - 1) := by
  unfold fib
  have key : ∀ T : Finset ℕ, T ⊆ Ioo v (z - u - v) →
      (insert u (insert v (insert z T))).filter (fun w => v < w ∧ u + v + w < z) = T := by
    intro T hT
    ext w
    simp only [mem_insert, mem_filter]
    constructor
    · rintro ⟨h | h | h | h, h5⟩
      · omega
      · omega
      · omega
      · exact h
    · intro hw
      have := hT hw
      rw [mem_Ioo] at this
      exact ⟨Or.inr (Or.inr (Or.inr hw)), by omega⟩
  rw [card_image_of_injOn, card_powerset, Nat.card_Ioo]
  · congr 1
    omega
  · intro T1 h1 T2 h2 heq
    have h1' := key T1 (mem_powerset.mp h1)
    have h2' := key T2 (mem_powerset.mp h2)
    simp only at heq
    rw [← h1', ← h2', heq]

theorem frame_unique (s : Finset ℕ) (u v z u' v' z' : ℕ)
    (h : Frame s u v z) (h' : Frame s u' v' z') : u = u' ∧ v = v' ∧ z = z' := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := h'
  have c1 := a7 u' b4
  have c2 := a7 v' b5
  have c3 := a7 z' b6
  have d1 := b7 u a4
  have d2 := b7 v a5
  have d3 := b7 z a6
  omega

/-- Index set: triples (a, b, c) with 3a + 2b + c ≤ m. -/
def Tset (m : ℕ) : Finset (Σ _ : ℕ, Σ _ : ℕ, ℕ) :=
  (range (m / 3 + 1)).sigma fun a =>
    (range ((m - 3 * a) / 2 + 1)).sigma fun b => range (m - 3 * a - 2 * b + 1)

theorem mem_Tset (m : ℕ) (t : Σ _ : ℕ, Σ _ : ℕ, ℕ) :
    t ∈ Tset m ↔ 3 * t.1 + 2 * t.2.1 + t.2.2 ≤ m := by
  unfold Tset
  simp only [mem_sigma, mem_range]
  omega

def E1 (k : ℕ) : ℕ := ∑ c ∈ range (k + 1), 2 ^ c
def E2 (k : ℕ) : ℕ := ∑ b ∈ range (k / 2 + 1), E1 (k - 2 * b)
def E3 (m : ℕ) : ℕ := ∑ a ∈ range (m / 3 + 1), E2 (m - 3 * a)

def fibT (t : Σ _ : ℕ, Σ _ : ℕ, ℕ) : Finset (Finset ℕ) :=
  fib (t.1 + 1) (t.1 + t.2.1 + 2) (3 * t.1 + 2 * t.2.1 + t.2.2 + 6)

def goodSet (m : ℕ) : Finset (Finset ℕ) := (Tset m).biUnion fibT

theorem mem_fibT (t : Σ _ : ℕ, Σ _ : ℕ, ℕ) (s : Finset ℕ) :
    s ∈ fibT t ↔ Frame s (t.1 + 1) (t.1 + t.2.1 + 2) (3 * t.1 + 2 * t.2.1 + t.2.2 + 6) := by
  unfold fibT
  exact mem_fib _ _ _ (by omega) (by omega) (by omega) s

theorem mem_goodSet (m : ℕ) (s : Finset ℕ) : s ∈ goodSet m ↔ Good (m + 6) s := by
  unfold goodSet Good
  rw [mem_biUnion]
  constructor
  · rintro ⟨t, ht, hs⟩
    rw [mem_Tset] at ht
    rw [mem_fibT] at hs
    exact ⟨_, _, _, by omega, hs⟩
  · rintro ⟨u, v, z, hz, hF⟩
    have hF' := hF
    obtain ⟨a1, a2, a3, -⟩ := hF'
    obtain ⟨a, rfl⟩ : ∃ a, u = a + 1 := ⟨u - 1, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, v = a + b + 2 := ⟨v - a - 2, by omega⟩
    obtain ⟨c, rfl⟩ : ∃ c, z = 3 * a + 2 * b + c + 6 := ⟨z - 3 * a - 2 * b - 6, by omega⟩
    refine ⟨⟨a, b, c⟩, ?_, ?_⟩
    · rw [mem_Tset]
      simp only
      omega
    · rw [mem_fibT]
      exact hF

theorem card_goodSet (m : ℕ) : (goodSet m).card = E3 m := by
  unfold goodSet
  rw [card_biUnion]
  · have h : ∀ t ∈ Tset m, (fibT t).card = 2 ^ t.2.2 := by
      intro t _
      unfold fibT
      rw [card_fib _ _ _ (by omega) (by omega) (by omega)]
      congr 1
      omega
    rw [sum_congr rfl h]
    unfold Tset E3 E2 E1
    rw [sum_sigma]
    refine sum_congr rfl ?_
    intro a _
    rw [sum_sigma]
  · intro x _ y _ hxy
    show Disjoint (fibT x) (fibT y)
    rw [Finset.disjoint_left]
    intro s hx hy
    rw [mem_fibT] at hx hy
    have := frame_unique s _ _ _ _ _ _ hx hy
    apply hxy
    obtain ⟨a, b, c⟩ := x
    obtain ⟨a', b', c'⟩ := y
    simp only at this
    obtain ⟨rfl, rfl, rfl⟩ : a = a' ∧ b = b' ∧ c = c' := by omega
    rfl

theorem count_ge (m : ℕ) : literalCount (m + 6) = E3 m := by
  unfold literalCount
  rw [Nat.subtype_card (goodSet m) (mem_goodSet m), card_goodSet]

theorem count_lt (n : ℕ) (hn : n < 6) : literalCount n = 0 := by
  unfold literalCount
  have : IsEmpty {s : Finset ℕ // Good n s} := by
    constructor
    rintro ⟨s, u, v, z, hz, h1, h2, h3, -⟩
    omega
  exact Nat.card_of_isEmpty

theorem E1_eq (k : ℕ) : (E1 k : ℤ) = 2 ^ (k + 1) - 1 := by
  unfold E1
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ]
    push_cast at ih ⊢
    rw [ih]
    ring

theorem E2_step (k : ℕ) : E2 (k + 2) = E1 (k + 2) + E2 k := by
  unfold E2
  have h : (k + 2) / 2 + 1 = (k / 2 + 1) + 1 := by omega
  rw [h, sum_range_succ']
  simp only [Nat.mul_zero, Nat.sub_zero]
  rw [add_comm]
  congr 1
  refine sum_congr rfl ?_
  intro b _
  congr 1
  omega

theorem E3_step (m : ℕ) : E3 (m + 3) = E2 (m + 3) + E3 m := by
  unfold E3
  have h : (m + 3) / 3 + 1 = (m / 3 + 1) + 1 := by omega
  rw [h, sum_range_succ']
  simp only [Nat.mul_zero, Nat.sub_zero]
  rw [add_comm]
  congr 1
  refine sum_congr rfl ?_
  intro a _
  congr 1
  omega

theorem E2_eq (m : ℕ) : 6 * (E2 m : ℤ) = 2 ^ (m + 4) - 3 * m - 10 - ((m % 2 : ℕ) : ℤ) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases m with _ | _ | m
    · simp [E2, E1]
    · simp [E2, E1, sum_range_succ]
    · rw [E2_step]
      have h := ih m (by omega)
      have h1 := E1_eq (m + 2)
      have h2 : (m + 1 + 1) % 2 = m % 2 := by omega
      rw [h2]
      generalize ((m % 2 : ℕ) : ℤ) = r at h ⊢
      push_cast
      rw [h1]
      have e1 : (2 : ℤ) ^ (m + 2 + 1) = 8 * 2 ^ m := by ring
      have e2 : (2 : ℤ) ^ (m + 1 + 1 + 4) = 64 * 2 ^ m := by ring
      have e3 : (2 : ℤ) ^ (m + 4) = 16 * 2 ^ m := by ring
      rw [e3] at h
      rw [e1, e2]
      linarith

/-- The residue correction. -/
def ee : ℕ → ℤ
  | 0 => 4
  | 1 => 15
  | 2 => 16
  | 3 => 11
  | 4 => 8
  | 5 => 23
  | _ => 0

theorem ee_bound (r : ℕ) : 0 ≤ ee r ∧ ee r ≤ 23 := by
  rcases r with _ | _ | _ | _ | _ | _ | r <;> simp [ee]

theorem E3_eq (m : ℕ) : 84 * (E3 m : ℤ) =
    4 * 2 ^ (m + 6) - 7 * ((m : ℤ) + 6) ^ 2 + 14 * ((m : ℤ) + 6) - ee (m % 6) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases hm : m < 6
    · interval_cases m <;> simp [E3, E2, E1, sum_range_succ, ee]
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 6 := ⟨m - 6, by omega⟩
      have h := ih k (by omega)
      have s1 : E3 (k + 6) = E2 (k + 6) + (E2 (k + 3) + E3 k) := by
        rw [show k + 6 = (k + 3) + 3 from rfl, E3_step, E3_step]
      have a1 := E2_eq (k + 6)
      have a2 := E2_eq (k + 3)
      have par : (((k + 6) % 2 : ℕ) : ℤ) + (((k + 3) % 2 : ℕ) : ℤ) = 1 := by
        have : (k + 6) % 2 + (k + 3) % 2 = 1 := by omega
        exact_mod_cast this
      have h6 : (k + 6) % 6 = k % 6 := by omega
      rw [s1, h6]
      push_cast at a1 a2 par ⊢
      have e1 : (2 : ℤ) ^ (k + 6 + 4) = 1024 * 2 ^ k := by ring
      have e2 : (2 : ℤ) ^ (k + 3 + 4) = 128 * 2 ^ k := by ring
      have e3 : (2 : ℤ) ^ (k + 6 + 6) = 4096 * 2 ^ k := by ring
      have e4 : (2 : ℤ) ^ (k + 6) = 64 * 2 ^ k := by ring
      rw [e1] at a1
      rw [e2] at a2
      rw [e4] at h
      rw [e3]
      linear_combination 14 * a1 + 14 * a2 + h - 14 * par

theorem round_close (x : ℚ) (k : ℤ) (h1 : (k : ℚ) - 1 / 2 ≤ x) (h2 : x < k + 1 / 2) :
    round x = k := by
  rw [round_eq, Int.floor_eq_iff]
  constructor <;> linarith

end OMA.A357291

open OMA.A357291 OMA.S_oeis_a357291 in
theorem OMA.solution : type_of% @OMA.S_oeis_a357291.main := by
  intro n
  symm
  by_cases hn : n < 6
  · rw [count_lt n hn]
    apply round_close
    · interval_cases n <;> norm_num
    · interval_cases n <;> norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    rw [count_ge]
    have h := E3_eq m
    have hb := ee_bound (m % 6)
    have hq := congrArg (Int.cast : ℤ → ℚ) h
    push_cast at hq
    have hb1 : (0 : ℚ) ≤ ((ee (m % 6) : ℤ) : ℚ) := by exact_mod_cast hb.1
    have hb2 : ((ee (m % 6) : ℤ) : ℚ) ≤ 23 := by exact_mod_cast hb.2
    apply round_close
    · push_cast
      linarith
    · push_cast
      linarith
