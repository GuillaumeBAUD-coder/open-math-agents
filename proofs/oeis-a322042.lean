import OMAStatements.S_oeis_a322042
import Mathlib

open OMA.S_oeis_a322042

namespace OMA.A322042Proof

/-- Potential: hexagonal norm of the shortest lift, computed on reduced representatives. -/
def g (n : ℕ) (v : ZMod n × ZMod n) : ℕ :=
  min (min (max v.1.val v.2.val) (max (n - v.1.val) (n - v.2.val)))
    (min (n - v.1.val + v.2.val) (n + v.1.val - v.2.val))

theorem val_add_one (n : ℕ) [NeZero n] (x : ZMod n) :
    ((x + 1).val = x.val + 1 ∧ x.val + 1 < n) ∨ ((x + 1).val = 0 ∧ x.val + 1 = n) := by
  have hx := ZMod.val_lt x
  rcases Nat.lt_or_ge (x.val + 1) n with h | h
  · left
    refine ⟨?_, h⟩
    rw [ZMod.val_add, ZMod.val_one_eq_one_mod]
    have h1 : 1 % n = 1 := Nat.mod_eq_of_lt (by omega)
    rw [h1, Nat.mod_eq_of_lt h]
  · right
    have he : x.val + 1 = n := by omega
    refine ⟨?_, he⟩
    rw [ZMod.val_add, ZMod.val_one_eq_one_mod]
    rcases Nat.lt_or_ge 1 n with h1 | h1
    · rw [Nat.mod_eq_of_lt h1, he, Nat.mod_self]
    · have : n = 1 := by have := NeZero.ne n; omega
      subst this
      simp [Nat.mod_one]

theorem val_sub_one (n : ℕ) [NeZero n] (x : ZMod n) :
    ((x - 1).val + 1 = x.val) ∨ (x.val = 0 ∧ (x - 1).val + 1 = n) := by
  rcases val_add_one n (x - 1) with ⟨h1, _⟩ | ⟨h1, h2⟩
  · left; rw [sub_add_cancel] at h1; omega
  · right; rw [sub_add_cancel] at h1; omega

set_option maxHeartbeats 4000000 in
theorem step (n : ℕ) [NeZero n] (u e : ZMod n × ZMod n) (he : e ∈ units n) :
    g n (u + e) ≤ g n u + 1 := by
  have h1 := ZMod.val_lt u.1
  have h2 := ZMod.val_lt u.2
  simp only [units, Set.mem_insert_iff, Set.mem_singleton_iff] at he
  rcases he with he | he | he | he | he | he <;> subst he
  · rw [show u + ((1 : ZMod n), (0 : ZMod n)) = (u.1 + 1, u.2) from by ext <;> simp [sub_eq_add_neg]]
    have hv0 := ZMod.val_lt (u.1 + 1)
    unfold g
    dsimp only
    rcases val_add_one n u.1 with k0 | k0 <;>
    · generalize (u.1 + 1).val = t0 at *; generalize u.1.val = r at *; generalize u.2.val = q at *; omega
  · rw [show u + ((-1 : ZMod n), (0 : ZMod n)) = (u.1 - 1, u.2) from by ext <;> simp [sub_eq_add_neg]]
    have hv0 := ZMod.val_lt (u.1 - 1)
    unfold g
    dsimp only
    rcases val_sub_one n u.1 with k0 | k0 <;>
    · generalize (u.1 - 1).val = t0 at *; generalize u.1.val = r at *; generalize u.2.val = q at *; omega
  · rw [show u + ((0 : ZMod n), (1 : ZMod n)) = (u.1, u.2 + 1) from by ext <;> simp [sub_eq_add_neg]]
    have hv0 := ZMod.val_lt (u.2 + 1)
    unfold g
    dsimp only
    rcases val_add_one n u.2 with k0 | k0 <;>
    · generalize (u.2 + 1).val = t0 at *; generalize u.1.val = r at *; generalize u.2.val = q at *; omega
  · rw [show u + ((0 : ZMod n), (-1 : ZMod n)) = (u.1, u.2 - 1) from by ext <;> simp [sub_eq_add_neg]]
    have hv0 := ZMod.val_lt (u.2 - 1)
    unfold g
    dsimp only
    rcases val_sub_one n u.2 with k0 | k0 <;>
    · generalize (u.2 - 1).val = t0 at *; generalize u.1.val = r at *; generalize u.2.val = q at *; omega
  · rw [show u + ((1 : ZMod n), (1 : ZMod n)) = (u.1 + 1, u.2 + 1) from by ext <;> simp [sub_eq_add_neg]]
    have hv0 := ZMod.val_lt (u.1 + 1)
    have hv1 := ZMod.val_lt (u.2 + 1)
    unfold g
    dsimp only
    rcases val_add_one n u.1 with k0 | k0 <;> rcases val_add_one n u.2 with k1 | k1 <;>
    · generalize (u.1 + 1).val = t0 at *; generalize (u.2 + 1).val = t1 at *; generalize u.1.val = r at *; generalize u.2.val = q at *; omega
  · rw [show u + ((-1 : ZMod n), (-1 : ZMod n)) = (u.1 - 1, u.2 - 1) from by ext <;> simp [sub_eq_add_neg]]
    have hv0 := ZMod.val_lt (u.1 - 1)
    have hv1 := ZMod.val_lt (u.2 - 1)
    unfold g
    dsimp only
    rcases val_sub_one n u.1 with k0 | k0 <;> rcases val_sub_one n u.2 with k1 | k1 <;>
    · generalize (u.1 - 1).val = t0 at *; generalize (u.2 - 1).val = t1 at *; generalize u.1.val = r at *; generalize u.2.val = q at *; omega

theorem neg_mem (n : ℕ) (e : ZMod n × ZMod n) (he : e ∈ units n) : -e ∈ units n := by
  simp only [units, Set.mem_insert_iff, Set.mem_singleton_iff] at he ⊢
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem walk_lb (n : ℕ) [NeZero n] {u w : ZMod n × ZMod n} (p : (graph n).Walk u w) :
    g n w ≤ g n u + p.length := by
  induction p with
  | nil => simp
  | @cons x y z h p ih =>
    rw [graph, SimpleGraph.fromRel_adj] at h
    have hm : y - x ∈ units n := by
      rcases h.2 with h' | h'
      · exact h'
      · rw [← neg_sub]; exact neg_mem n _ h'
    have hs := step n x (y - x) hm
    rw [show x + (y - x) = y by abel] at hs
    rw [SimpleGraph.Walk.length_cons]
    omega

def W (n k : ℕ) (x : ZMod n × ZMod n) : Prop := ∃ p : (graph n).Walk 0 x, p.length ≤ k

theorem W_step (n : ℕ) {k : ℕ} {x e : ZMod n × ZMod n} (h : W n k x) (he : e ∈ units n) :
    W n (k + 1) (x + e) := by
  obtain ⟨p, hp⟩ := h
  by_cases hx : x = x + e
  · rw [← hx]; exact ⟨p, by omega⟩
  · have hadj : (graph n).Adj x (x + e) := by
      rw [graph, SimpleGraph.fromRel_adj]
      refine ⟨hx, Or.inl ?_⟩
      rwa [add_sub_cancel_left]
    exact ⟨p.concat hadj, by rw [SimpleGraph.Walk.length_concat]; omega⟩

theorem W_iter (n : ℕ) {k : ℕ} {x e : ZMod n × ZMod n} (h : W n k x) (he : e ∈ units n)
    (j : ℕ) : W n (k + j) (x + j • e) := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
    have := W_step n ih he
    rw [succ_nsmul, ← add_assoc x]
    exact this

theorem W_mono (n : ℕ) {k k' : ℕ} {x : ZMod n × ZMod n} (h : W n k x) (hk : k ≤ k') :
    W n k' x := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, by omega⟩

theorem W_two (n : ℕ) {e1 e2 : ZMod n × ZMod n} (h1 : e1 ∈ units n) (h2 : e2 ∈ units n)
    (a b : ℕ) : W n (a + b) (a • e1 + b • e2) := by
  have h0 : W n 0 0 := ⟨SimpleGraph.Walk.nil, le_refl _⟩
  have := W_iter n (W_iter n h0 h1 a) h2 b
  simpa using this

theorem mem1 (n : ℕ) : ((1 : ZMod n), (0 : ZMod n)) ∈ units n := by simp [units]
theorem mem2 (n : ℕ) : ((-1 : ZMod n), (0 : ZMod n)) ∈ units n := by simp [units]
theorem mem3 (n : ℕ) : ((0 : ZMod n), (1 : ZMod n)) ∈ units n := by simp [units]
theorem mem4 (n : ℕ) : ((0 : ZMod n), (-1 : ZMod n)) ∈ units n := by simp [units]
theorem mem5 (n : ℕ) : ((1 : ZMod n), (1 : ZMod n)) ∈ units n := by simp [units]
theorem mem6 (n : ℕ) : ((-1 : ZMod n), (-1 : ZMod n)) ∈ units n := by simp [units]

theorem ub (n : ℕ) [NeZero n] (v : ZMod n × ZMod n) : W n (n - (n + 2) / 3) v := by
  have hr := ZMod.val_lt v.1
  have hs := ZMod.val_lt v.2
  have hv : v = ((v.1.val : ZMod n), (v.2.val : ZMod n)) := by
    ext <;> simp [ZMod.natCast_zmod_val]
  generalize v.1.val = r at hr hv
  generalize v.2.val = s at hs hv
  subst hv
  have hn0 : ((n : ℕ) : ZMod n) = 0 := ZMod.natCast_self n
  rcases (show (s ≤ r ∧ r ≤ n - (n + 2) / 3) ∨ (r ≤ s ∧ s ≤ n - (n + 2) / 3) ∨
      (r ≤ s ∧ n - r ≤ n - (n + 2) / 3) ∨ (s ≤ r ∧ n - s ≤ n - (n + 2) / 3) ∨
      (n - r + s ≤ n - (n + 2) / 3) ∨ (r + n - s ≤ n - (n + 2) / 3) by omega)
    with h | h | h | h | h | h
  · have he : ((r : ZMod n), (s : ZMod n)) = (s) • ((1 : ZMod n), (1 : ZMod n)) + (r - s) • ((1 : ZMod n), (0 : ZMod n)) := by
      have h1 : r ≤ n := hr.le
      have h2 : s ≤ n := hs.le
      ext <;> simp [Nat.cast_sub, h1, h2, h.1, hn0] <;> ring_nf <;> simp [hn0]
    rw [he]
    exact W_mono n (W_two n (mem5 n) (mem1 n) _ _) (by omega)
  · have he : ((r : ZMod n), (s : ZMod n)) = (r) • ((1 : ZMod n), (1 : ZMod n)) + (s - r) • ((0 : ZMod n), (1 : ZMod n)) := by
      have h1 : r ≤ n := hr.le
      have h2 : s ≤ n := hs.le
      ext <;> simp [Nat.cast_sub, h1, h2, h.1, hn0] <;> ring_nf <;> simp [hn0]
    rw [he]
    exact W_mono n (W_two n (mem5 n) (mem3 n) _ _) (by omega)
  · have he : ((r : ZMod n), (s : ZMod n)) = (n - s) • ((-1 : ZMod n), (-1 : ZMod n)) + (s - r) • ((-1 : ZMod n), (0 : ZMod n)) := by
      have h1 : r ≤ n := hr.le
      have h2 : s ≤ n := hs.le
      ext <;> simp [Nat.cast_sub, h1, h2, h.1, hn0] <;> ring_nf <;> simp [hn0]
    rw [he]
    exact W_mono n (W_two n (mem6 n) (mem2 n) _ _) (by omega)
  · have he : ((r : ZMod n), (s : ZMod n)) = (n - r) • ((-1 : ZMod n), (-1 : ZMod n)) + (r - s) • ((0 : ZMod n), (-1 : ZMod n)) := by
      have h1 : r ≤ n := hr.le
      have h2 : s ≤ n := hs.le
      ext <;> simp [Nat.cast_sub, h1, h2, h.1, hn0] <;> ring_nf <;> simp [hn0]
    rw [he]
    exact W_mono n (W_two n (mem6 n) (mem4 n) _ _) (by omega)
  · have he : ((r : ZMod n), (s : ZMod n)) = (n - r) • ((-1 : ZMod n), (0 : ZMod n)) + (s) • ((0 : ZMod n), (1 : ZMod n)) := by
      have h1 : r ≤ n := hr.le
      have h2 : s ≤ n := hs.le
      ext <;> simp [Nat.cast_sub, h1, h2, hn0] <;> ring_nf <;> simp [hn0]
    rw [he]
    exact W_mono n (W_two n (mem2 n) (mem3 n) _ _) (by omega)
  · have he : ((r : ZMod n), (s : ZMod n)) = (r) • ((1 : ZMod n), (0 : ZMod n)) + (n - s) • ((0 : ZMod n), (-1 : ZMod n)) := by
      have h1 : r ≤ n := hr.le
      have h2 : s ≤ n := hs.le
      ext <;> simp [Nat.cast_sub, h1, h2, hn0] <;> ring_nf <;> simp [hn0]
    rw [he]
    exact W_mono n (W_two n (mem1 n) (mem4 n) _ _) (by omega)

theorem a_eq (n : ℕ) (hn : 1 ≤ n) : a n = n - (n + 2) / 3 := by
  haveI : NeZero n := ⟨by omega⟩
  apply le_antisymm
  · apply ciSup_le
    intro v
    obtain ⟨p, hp⟩ := ub n v
    exact (SimpleGraph.dist_le p).trans hp
  · rcases (show n = 1 ∨ 2 ≤ n by omega) with h1 | h2
    · subst h1; norm_num
    · set w : ZMod n × ZMod n := (((n - (n + 2) / 3 : ℕ) : ZMod n), (((n + 2) / 3 : ℕ) : ZMod n))
        with hw
      obtain ⟨p, _⟩ := ub n w
      have hr : (graph n).Reachable 0 w := ⟨p⟩
      obtain ⟨q, hq⟩ := hr.exists_walk_length_eq_dist
      have hlb := walk_lb n q
      have g0 : g n 0 = 0 := by simp [g]
      have gw : n - (n + 2) / 3 ≤ g n w := by
        have v1 : w.1.val = n - (n + 2) / 3 := by
          rw [hw, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
        have v2 : w.2.val = (n + 2) / 3 := by
          rw [hw, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
        unfold g
        rw [v1, v2]
        omega
      refine le_trans ?_ (le_ciSup (Finite.bddAbove_range _) w)
      omega

theorem ceil_eq (n : ℕ) : ⌈(n : ℚ) / 3⌉ = (((n + 2) / 3 : ℕ) : ℤ) := by
  rw [Int.ceil_eq_iff]
  have h1 : 3 * ((n + 2) / 3) ≤ n + 2 := Nat.mul_div_le (n + 2) 3
  have h2 : n ≤ 3 * ((n + 2) / 3) := by omega
  have h1' : (3 * ((n + 2) / 3 : ℕ) : ℚ) ≤ (n : ℚ) + 2 := by exact_mod_cast h1
  have h2' : (n : ℚ) ≤ 3 * ((n + 2) / 3 : ℕ) := by exact_mod_cast h2
  rw [Int.cast_natCast]
  constructor
  · rw [lt_div_iff₀ (by norm_num)]
    linarith
  · rw [div_le_iff₀ (by norm_num)]
    linarith

theorem closedZ (n : ℕ) (hn : 1 ≤ n) : (a n : ℤ) = n - ⌈(n : ℚ) / 3⌉ := by
  rw [ceil_eq, a_eq n hn]
  omega

theorem recZ (n : ℕ) (hn : 4 < n) : (a n : ℤ) = a (n - 1) + a (n - 3) - a (n - 4) := by
  rw [a_eq n (by omega), a_eq (n - 1) (by omega), a_eq (n - 3) (by omega),
    a_eq (n - 4) (by omega)]
  omega

theorem b_eq (n : ℕ) : (if n = 0 then (0 : ℚ) else (a n : ℚ)) = ((n - (n + 2) / 3 : ℕ) : ℚ) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · rw [if_neg (by omega), a_eq n h]

end OMA.A322042Proof

open OMA.A322042Proof PowerSeries

theorem OMA.solution : type_of% @OMA.S_oeis_a322042.main := by
  refine ⟨?_, recZ, closedZ⟩
  have hf : (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) =
      fun n => ((n - (n + 2) / 3 : ℕ) : ℚ) := funext b_eq
  rw [hf]
  ext d
  have e1 : ∀ A : PowerSeries ℚ, A * (1 - X - X ^ 3 + X ^ 4) =
      A - A * X ^ 1 - A * X ^ 3 + A * X ^ 4 := by
    intro A; ring
  have e2 : (X ^ 2 * (1 + X) : PowerSeries ℚ) = X ^ 2 + X ^ 3 := by ring
  rw [e1, e2]
  simp only [map_add, map_sub, coeff_mul_X_pow', coeff_mk, coeff_X_pow]
  rcases (show d ≤ 3 ∨ 4 ≤ d by omega) with hd | hd
  · interval_cases d <;> norm_num
  · obtain ⟨j, rfl⟩ : ∃ j, d = j + 4 := ⟨d - 4, by omega⟩
    simp only [if_pos (show 1 ≤ j + 4 by omega), if_pos (show 3 ≤ j + 4 by omega),
      if_pos (show 4 ≤ j + 4 by omega), if_neg (show j + 4 ≠ 1 by omega),
      if_neg (show j + 4 ≠ 2 by omega), show j + 4 - 1 = j + 3 by omega,
      show j + 4 - 3 = j + 1 by omega, show j + 4 - 4 = j by omega]
    have key : (j + 4 - (j + 4 + 2) / 3) + (j - (j + 2) / 3) =
        (j + 3 - (j + 3 + 2) / 3) + (j + 1 - (j + 1 + 2) / 3) := by omega
    have keyQ : (((j + 4 - (j + 4 + 2) / 3 : ℕ) : ℚ) + ((j - (j + 2) / 3 : ℕ) : ℚ)) =
        ((j + 3 - (j + 3 + 2) / 3 : ℕ) : ℚ) + ((j + 1 - (j + 1 + 2) / 3 : ℕ) : ℚ) := by
      exact_mod_cast key
    split_ifs <;> first | omega | linarith
