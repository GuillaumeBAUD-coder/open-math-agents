import OMAStatements.S_oeis_a360925
import Mathlib

/-!
# OEIS A360925: integer lunar lander from velocity n and altitude zero

Lower bound: every flight of length t from velocity u to velocity v has
altitude change at least the sum of max (u - i) (v - (t - i)) for i = 1..t.
Upper bound: descend n, n-1, ..., 0 and then fly a nonpositive bump of length s
whose area is n(n-1)/2, which exists as soon as 4 * area is at most s^2.
-/

namespace OMA.A360925

open OMA.S_oeis_a360925 Finset

theorem mv {t : ℕ} {u v d w d' : ℤ} (h : Flight t u v d) (h1 : v - 1 ≤ w)
    (h2 : w ≤ v + 1) (hd : d' = d + w) : Flight (t + 1) u w d' := by
  subst hd; exact Flight.move w h h1 h2

theorem castF {t t' : ℕ} {u v d u' v' d' : ℤ} (h : Flight t u v d) (ht : t = t')
    (hu : u = u') (hv : v = v') (hd : d = d') : Flight t' u' v' d' := by
  subst ht; subst hu; subst hv; subst hd; exact h

theorem comp {t : ℕ} {u v d : ℤ} (h : Flight t u v d) {t' : ℕ} {w d' : ℤ}
    (h' : Flight t' v w d') : Flight (t + t') u w (d + d') := by
  induction h' with
  | rest => simpa using h
  | move w' hf h1 h2 ih => exact mv (ih h) h1 h2 (by ring)

theorem shift {t : ℕ} {u v d : ℤ} (h : Flight t u v d) :
    Flight t (u + 1) (v + 1) (d + t) := by
  induction h with
  | rest u => exact castF (Flight.rest (u + 1)) rfl rfl rfl (by simp)
  | move w hf h1 h2 ih =>
    exact mv ih (by linarith) (by linarith) (by push_cast; ring)

theorem negF {t : ℕ} {u v d : ℤ} (h : Flight t u v d) :
    Flight t (-u) (-v) (-d) := by
  induction h with
  | rest u => exact castF (Flight.rest (-u)) rfl rfl rfl (by simp)
  | move w hf h1 h2 ih =>
    exact mv ih (by linarith) (by linarith) (by ring)

theorem bump (s : ℕ) : (∀ T : ℤ, 0 ≤ T → 4 * T ≤ (s : ℤ) ^ 2 → Flight s 0 0 T) ∧
    (∀ T : ℤ, 0 ≤ T → 4 * T ≤ ((s : ℤ) + 1) ^ 2 → Flight (s + 1) 0 0 T) := by
  induction s with
  | zero =>
    constructor
    · intro T h0 h1
      have : T = 0 := by norm_num at h1; omega
      subst this; exact Flight.rest 0
    · intro T h0 h1
      have : T = 0 := by norm_num at h1; omega
      subst this
      exact mv (Flight.rest 0) (by norm_num) (by norm_num) (by norm_num)
  | succ s ih =>
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨fun T h0 h1 => ih2 T h0 (by push_cast at h1; exact h1), ?_⟩
    intro T h0 h1
    push_cast at h1
    by_cases hc : 4 * T ≤ ((s : ℤ) + 1) ^ 2
    · exact mv (ih2 T h0 hc) (by norm_num) (by norm_num) (by ring)
    · push_neg at hc
      have hT : (s : ℤ) + 1 ≤ T := by
        by_contra hlt
        push_neg at hlt
        nlinarith [sq_nonneg ((s : ℤ) - 1)]
      have h3 := ih1 (T - s - 1) (by linarith) (by nlinarith)
      have h4 := shift h3
      have h5 : Flight 1 0 1 1 :=
        mv (Flight.rest 0) (by norm_num) (by norm_num) (by norm_num)
      have h4' : Flight s 1 1 (T - s - 1 + s) := castF h4 rfl (by norm_num) (by norm_num) rfl
      have h6 := comp h5 h4'
      have h7 : Flight (1 + s + 1) 0 0 (1 + (T - s - 1 + s) + 0) :=
        mv h6 (by norm_num) (by norm_num) rfl
      exact castF h7 (by omega) rfl rfl (by ring)

theorem descent (u : ℤ) (k : ℕ) :
    ∃ d : ℤ, Flight k u (u - k) d ∧ 2 * d = 2 * k * u - k * (k + 1) := by
  induction k with
  | zero => exact ⟨0, castF (Flight.rest u) rfl rfl (by simp) rfl, by simp⟩
  | succ k ih =>
    obtain ⟨d, hf, hd⟩ := ih
    refine ⟨d + (u - ((k + 1 : ℕ) : ℤ)),
      mv hf (by push_cast; linarith) (by push_cast; linarith) rfl, ?_⟩
    push_cast
    linear_combination hd

theorem exists_flight (n s : ℕ) (h : 2 * (n : ℤ) * (n - 1) ≤ (s : ℤ) ^ 2) :
    Flight (n + s) n 0 0 := by
  obtain ⟨d, hf, hd⟩ := descent (n : ℤ) n
  have hd' : 2 * d = (n : ℤ) * (n - 1) := by linear_combination hd
  have hnn : 0 ≤ (n : ℤ) * (n - 1) := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp
    · have : (1 : ℤ) ≤ n := by exact_mod_cast h0
      exact mul_nonneg (by linarith) (by linarith)
  have hb := negF ((bump s).1 d (by linarith) (by linarith))
  have hf' : Flight n (n : ℤ) 0 d := castF hf rfl rfl (by simp) rfl
  have hb' : Flight s 0 0 (-d) := castF hb rfl (by simp) (by simp) rfl
  have hc := comp hf' hb'
  exact castF hc rfl rfl rfl (by ring)

theorem lower {t : ℕ} {u v d : ℤ} (h : Flight t u v d) :
    u - t ≤ v ∧
    ∑ i ∈ range t, max (u - ((i : ℤ) + 1)) (v - ((t : ℤ) - ((i : ℤ) + 1))) ≤ d := by
  induction h with
  | rest u => simp
  | @move t u v d w hf h1 h2 ih =>
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨by push_cast; linarith, ?_⟩
    rw [Finset.sum_range_succ]
    have e : max (u - ((t : ℤ) + 1)) (w - (((t + 1 : ℕ) : ℤ) - ((t : ℤ) + 1))) = w := by
      push_cast
      rw [max_eq_right (by linarith)]
      ring
    rw [e]
    have hs : ∑ i ∈ range t,
        max (u - ((i : ℤ) + 1)) (w - (((t + 1 : ℕ) : ℤ) - ((i : ℤ) + 1))) ≤
        ∑ i ∈ range t, max (u - ((i : ℤ) + 1)) (v - ((t : ℤ) - ((i : ℤ) + 1))) := by
      apply Finset.sum_le_sum
      intro i _
      apply max_le_max le_rfl
      push_cast
      linarith
    linarith

theorem tri (c : ℤ) (n : ℕ) :
    2 * ∑ i ∈ range n, (c - ((i : ℤ) + 1)) = 2 * c * n - n * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    push_cast
    ring

def K (s : ℕ) : ℤ := ∑ j ∈ range s, max (-((j : ℤ) + 1)) ((j : ℤ) + 1 - s)

theorem K_step (s : ℕ) : K (s + 2) = K s - s - 1 := by
  unfold K
  rw [Finset.sum_range_succ, Finset.sum_range_succ']
  have e : ∀ i : ℕ, max (-(((i + 1 : ℕ) : ℤ) + 1)) (((i + 1 : ℕ) : ℤ) + 1 - ((s + 2 : ℕ) : ℤ))
      = max (-((i : ℤ) + 1)) ((i : ℤ) + 1 - s) - 1 := by
    intro i
    push_cast
    simp only [max_def]
    split_ifs <;> omega
  have e1 : max (-(((0 : ℕ) : ℤ) + 1)) (((0 : ℕ) : ℤ) + 1 - ((s + 2 : ℕ) : ℤ)) = -1 := by
    push_cast
    simp only [max_def]
    split_ifs <;> omega
  have e2 : max (-(((s + 1 : ℕ) : ℤ) + 1)) (((s + 1 : ℕ) : ℤ) + 1 - ((s + 2 : ℕ) : ℤ)) = 0 := by
    push_cast
    simp only [max_def]
    split_ifs <;> omega
  rw [e1, e2]
  simp only [e]
  rw [Finset.sum_sub_distrib]
  simp
  ring

theorem K_bound (s : ℕ) : -(s : ℤ) ^ 2 ≤ 4 * K s ∧ -((s : ℤ) + 1) ^ 2 ≤ 4 * K (s + 1) := by
  induction s with
  | zero =>
    constructor
    · simp [K]
    · simp [K]
  | succ s ih =>
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨by push_cast; exact ih2, ?_⟩
    rw [K_step]
    push_cast
    nlinarith

theorem lowerN {t n : ℕ} (h : Flight t (n : ℤ) 0 0) :
    ∃ s : ℕ, t = n + s ∧ 2 * (n : ℤ) * (n - 1) ≤ (s : ℤ) ^ 2 := by
  obtain ⟨h1, h2⟩ := lower h
  have hnt : n ≤ t := by
    have : (n : ℤ) ≤ t := by linarith
    exact_mod_cast this
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hnt
  refine ⟨s, rfl, ?_⟩
  rw [Finset.sum_range_add] at h2
  have a1 : ∑ x ∈ range n, ((n : ℤ) - ((x : ℤ) + 1)) ≤
      ∑ x ∈ range n, max ((n : ℤ) - ((x : ℤ) + 1))
        (0 - (((n + s : ℕ) : ℤ) - ((x : ℤ) + 1))) :=
    Finset.sum_le_sum (fun i _ => le_max_left _ _)
  have a2 : ∑ x ∈ range s, max ((n : ℤ) - (((n + x : ℕ) : ℤ) + 1))
        (0 - (((n + s : ℕ) : ℤ) - (((n + x : ℕ) : ℤ) + 1))) = K s := by
    unfold K
    apply Finset.sum_congr rfl
    intro x _
    push_cast
    congr 1 <;> ring
  rw [a2] at h2
  have a3 := tri (n : ℤ) n
  have a4 := (K_bound s).1
  nlinarith

open Classical in
theorem time_eq (n s : ℕ) (h1 : 2 * (n : ℤ) * (n - 1) ≤ (s : ℤ) ^ 2)
    (h2 : ∀ r : ℕ, r < s → (r : ℤ) ^ 2 < 2 * (n : ℤ) * (n - 1)) : time n = n + s := by
  have hf := exists_flight n s h1
  unfold time
  rw [dif_pos ⟨_, hf⟩]
  refine (Nat.find_eq_iff _).2 ⟨hf, fun m hm hfm => ?_⟩
  obtain ⟨r, rfl, hr⟩ := lowerN hfm
  have := h2 r (by omega)
  linarith

theorem sq_mod_four (x : ℕ) : x * x % 4 = 0 ∨ x * x % 4 = 1 := by
  rw [Nat.mul_mod]
  have := Nat.mod_lt x (by norm_num : 4 > 0)
  interval_cases (x % 4) <;> simp

theorem sub_fact (n : ℕ) (hn : 2 ≤ n) : 2 * n ^ 2 - 2 * n - 3 + 2 * n + 3 = 2 * (n * n) := by
  have h1 : 2 * n + 3 ≤ 2 * (n * n) := by nlinarith
  have h2 : n ^ 2 = n * n := sq n
  omega

theorem formula (n : ℕ) (hn : 2 ≤ n) : time n = n + 1 + Nat.sqrt (2 * n ^ 2 - 2 * n - 3) := by
  have hA := sub_fact n hn
  generalize 2 * n ^ 2 - 2 * n - 3 = A at hA ⊢
  have ha1 := Nat.sqrt_le A
  have ha2 := Nat.lt_succ_sqrt A
  generalize Nat.sqrt A = m at ha1 ha2
  have hP := sq_mod_four (m + 1)
  obtain ⟨q, hq⟩ := Nat.even_mul_succ_self n
  have hq' : n * n + n = q + q := by rw [← hq]; ring
  have hmm : (m + 1) * (m + 1) = m * m + 2 * m + 1 := by ring
  have key : 2 * (n * n) ≤ (m + 1) * (m + 1) + 2 * n := by
    simp only [Nat.succ_eq_add_one] at ha2
    omega
  have e : time n = n + (m + 1) := by
    apply time_eq
    · have : (2 * ((n : ℤ) * n)) ≤ ((m : ℤ) + 1) * ((m : ℤ) + 1) + 2 * n := by
        exact_mod_cast key
      push_cast
      linarith
    · intro r hr
      have hr1 : r * r ≤ m * m := Nat.mul_le_mul (by omega) (by omega)
      have hr2 : r * r + 2 * n < 2 * (n * n) := by omega
      have : ((r : ℤ) * r + 2 * n) < 2 * ((n : ℤ) * n) := by exact_mod_cast hr2
      linarith
  rw [e]; ring

theorem sqrt_step (n : ℕ) (hn : 2 ≤ n) :
    Nat.sqrt (2 * (n + 1) ^ 2 - 2 * (n + 1) - 3) = Nat.sqrt (2 * n ^ 2 - 2 * n - 3) + 1 ∨
    Nat.sqrt (2 * (n + 1) ^ 2 - 2 * (n + 1) - 3) = Nat.sqrt (2 * n ^ 2 - 2 * n - 3) + 2 := by
  have hA := sub_fact n hn
  have hB := sub_fact (n + 1) (by omega)
  generalize 2 * n ^ 2 - 2 * n - 3 = A at hA ⊢
  generalize 2 * (n + 1) ^ 2 - 2 * (n + 1) - 3 = B at hB ⊢
  have ha1 := Nat.sqrt_le A
  have ha2 := Nat.lt_succ_sqrt A
  have hb1 := Nat.sqrt_le B
  have hb2 := Nat.lt_succ_sqrt B
  generalize Nat.sqrt A = a at ha1 ha2 ⊢
  generalize Nat.sqrt B = b at hb1 hb2 ⊢
  simp only [Nat.succ_eq_add_one] at ha2 hb2
  have hAB : B = A + 4 * n := by
    have : (n + 1) * (n + 1) = n * n + 2 * n + 1 := by ring
    omega
  subst hAB
  have hab : a + 1 ≤ b := by
    by_contra hlt
    have h1 : b + 1 ≤ a + 1 := by omega
    have h2 := Nat.mul_le_mul h1 h1
    have h3 : (a + 1) * (a + 1) = a * a + 2 * a + 1 := by ring
    have h4 : 2 * n ≤ a := by omega
    have h5 := Nat.mul_le_mul h4 h4
    have h6 : 2 * n * (2 * n) = 4 * (n * n) := by ring
    omega
  have hba : b ≤ a + 2 := by
    by_contra hlt
    have h1 : a + 3 ≤ b := by omega
    have h2 := Nat.mul_le_mul h1 h1
    have h3 : (a + 3) * (a + 3) = a * a + 6 * a + 9 := by ring
    have h3' : (a + 1) * (a + 1) = a * a + 2 * a + 1 := by ring
    have h4 : a + 3 ≤ n := by omega
    have h5 := Nat.mul_le_mul h4 h4
    nlinarith
  omega

end OMA.A360925

open OMA.S_oeis_a360925 in
theorem OMA.solution : type_of% @OMA.S_oeis_a360925.main := by
  have t0 : time 0 = 0 := by
    have := OMA.A360925.time_eq 0 0 (by norm_num) (by intro r hr; omega)
    simpa using this
  have t1 : time 1 = 1 := by
    have := OMA.A360925.time_eq 1 0 (by norm_num) (by intro r hr; omega)
    simpa using this
  have t2 : time 2 = 4 := by
    have := OMA.A360925.time_eq 2 2 (by norm_num)
      (by intro r hr; interval_cases r <;> norm_num)
    simpa using this
  refine ⟨?_, t0, t1, OMA.A360925.formula, ?_⟩
  · intro n
    exact ⟨n + (2 * n), OMA.A360925.exists_flight n (2 * n) (by push_cast; nlinarith)⟩
  · intro n hn
    rcases Nat.lt_or_ge n 2 with h | h
    · have : n = 1 := by omega
      subst this
      right
      rw [t1, t2]
    · rw [OMA.A360925.formula n h, OMA.A360925.formula (n + 1) (by omega)]
      rcases OMA.A360925.sqrt_step n h with h' | h' <;> rw [h'] <;> omega
