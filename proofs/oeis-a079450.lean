import OMAStatements.S_oeis_a079450
import Mathlib

namespace OMA.S_oeis_a079450

/-- remainder after processing exponents up to n -/
def rr : ℕ → ℚ
  | 0 => 1
  | n + 1 => if (2 / 3 : ℚ) ^ (n + 1) ≤ rr n then rr n - (2 / 3) ^ (n + 1) else rr n

theorem rr_bounds : ∀ n, 0 ≤ rr n ∧ (rr n ≤ (2/3:ℚ)^n) ∧ (1 ≤ n → rr n < (2/3:ℚ)^n) := by
  intro n
  induction n with
  | zero => simp [rr]
  | succ n ih =>
    obtain ⟨h0, h1, _⟩ := ih
    have hp : (0:ℚ) < (2/3)^n := by positivity
    have e : (2/3:ℚ)^(n+1) = (2/3)^n * (2/3) := pow_succ _ _
    by_cases h : (2/3:ℚ)^(n+1) ≤ rr n
    · simp only [rr, if_pos h]
      refine ⟨by linarith, by linarith, fun _ => by linarith⟩
    · simp only [rr, if_neg h]
      push_neg at h
      exact ⟨h0, h.le, fun _ => h⟩

theorem rr_sp (n : ℕ) (h : (2/3:ℚ)^(n+1) ≤ rr n) : rr (n+1) = rr n - (2/3)^(n+1) := by
  simp only [rr, if_pos h]

theorem rr_sn (n : ℕ) (h : ¬ (2/3:ℚ)^(n+1) ≤ rr n) : rr (n+1) = rr n := by
  simp only [rr, if_neg h]

theorem rr_succ_le (n : ℕ) : rr (n+1) ≤ rr n := by
  by_cases h : (2/3:ℚ)^(n+1) ≤ rr n
  · have : (0:ℚ) < (2/3)^(n+1) := by positivity
    rw [rr_sp n h]; linarith
  · rw [rr_sn n h]

theorem rr_anti {m n : ℕ} (h : m ≤ n) : rr n ≤ rr m := antitone_nat_of_succ_le rr_succ_le h

theorem rr_odd : ∀ n, ∃ k : ℤ, Odd k ∧ (3:ℚ)^n * rr n = k := by
  intro n
  induction n with
  | zero => exact ⟨1, by decide, by simp [rr]⟩
  | succ n ih =>
    obtain ⟨k, hk, e⟩ := ih
    have h3 : (3:ℚ)^(n+1)*(2/3)^(n+1) = 2^(n+1) := by rw [← mul_pow]; norm_num
    have h4 : (3:ℚ)^(n+1) * rr n = 3 * k := by rw [← e]; ring
    by_cases h : (2/3:ℚ)^(n+1) ≤ rr n
    · refine ⟨3 * k - 2^(n+1), ?_, ?_⟩
      · refine Odd.sub_even (Odd.mul (by decide) hk) ⟨2^n, by ring⟩
      · simp only [rr, if_pos h]
        push_cast
        rw [mul_sub, h3, h4]
    · refine ⟨3 * k, Odd.mul (by decide) hk, ?_⟩
      simp only [rr, if_neg h]
      push_cast
      exact h4

def Yf (n : ℕ) : ℚ := (3/2:ℚ)^n * rr n

theorem hp1 (n : ℕ) : (3/2:ℚ)^n * (2/3)^n = 1 := by rw [← mul_pow]; norm_num

theorem Y_le (n : ℕ) : Yf n ≤ 1 := by
  unfold Yf
  have := (rr_bounds n).2.1
  have hq : (0:ℚ) ≤ (3/2)^n := by positivity
  calc (3/2:ℚ)^n * rr n ≤ (3/2)^n * (2/3)^n := mul_le_mul_of_nonneg_left this hq
    _ = 1 := hp1 n

theorem Y_pos (n : ℕ) : 0 < Yf n := by
  unfold Yf
  obtain ⟨k, hk, e⟩ := rr_odd n
  have h0 := (rr_bounds n).1
  rcases h0.lt_or_eq with h | h
  · positivity
  · exfalso
    rw [← h] at e
    simp at e
    have : k = 0 := by exact_mod_cast e.symm
    rw [this] at hk
    exact absurd hk (by decide)

theorem Y_ne (n : ℕ) : Yf n ≠ 2/3 := by
  intro hY
  obtain ⟨k, hk, e⟩ := rr_odd n
  have h1 : (3:ℚ)^n * rr n = 2^n * Yf n := by
    unfold Yf
    rw [← mul_assoc, show (2:ℚ)^n * (3/2)^n = 3^n by rw [← mul_pow]; norm_num]
  rw [hY] at h1
  have h2 : (3 * k : ℚ) = 2^(n+1) := by
    rw [← e, h1]; ring
  have h3 : (3 * k : ℤ) = 2^(n+1) := by exact_mod_cast h2
  have h4 : Odd (3 * k) := Odd.mul (by decide) hk
  rw [h3] at h4
  obtain ⟨t, ht⟩ := h4
  have h5 : (2:ℤ)^(n+1) = 2 * 2^n := by ring
  rw [h5] at ht
  generalize (2:ℤ)^n = w at ht
  omega

theorem G_iff (n : ℕ) : (2/3:ℚ)^(n+1) ≤ rr n ↔ 2/3 ≤ Yf n := by
  unfold Yf
  have hq : (0:ℚ) ≤ (3/2)^n := by positivity
  have hq' : (0:ℚ) ≤ (2/3)^n := by positivity
  have hp : (2/3:ℚ)^n * (3/2)^n = 1 := by rw [mul_comm]; exact hp1 n
  constructor
  · intro h
    have := mul_le_mul_of_nonneg_left h hq
    rw [pow_succ] at this
    have e2 : (3/2:ℚ)^n * ((2/3)^n * (2/3)) = 2/3 := by
      rw [← mul_assoc, hp1]; ring
    linarith
  · intro h
    have := mul_le_mul_of_nonneg_left h hq'
    have e2 : (2/3:ℚ)^n * ((3/2)^n * rr n) = rr n := by
      rw [← mul_assoc, hp]; ring
    rw [pow_succ]
    linarith

theorem Y_succ_pos (n : ℕ) (h : (2/3:ℚ)^(n+1) ≤ rr n) : Yf (n+1) = 3/2 * Yf n - 1 := by
  unfold Yf
  simp only [rr, if_pos h]
  rw [mul_sub, hp1 (n+1), pow_succ]; ring

theorem Y_succ_neg (n : ℕ) (h : ¬ (2/3:ℚ)^(n+1) ≤ rr n) : Yf (n+1) = 3/2 * Yf n := by
  unfold Yf
  simp only [rr, if_neg h]
  rw [pow_succ]; ring

theorem u_eq : ∀ n, u (n+1) = 2 - Yf n := by
  intro n
  induction n with
  | zero => norm_num [u, Yf, rr]
  | succ n ih =>
    have e : u (n+1+1) = Int.fract ((3/2 : ℚ) * u (n+1)) + 1 := rfl
    rw [e, ih]
    have hle := Y_le n
    have hpos := Y_pos n
    have hne := Y_ne n
    by_cases h : (2/3:ℚ)^(n+1) ≤ rr n
    · have hY := (G_iff n).1 h
      have hY2 : 2/3 < Yf n := lt_of_le_of_ne hY (Ne.symm hne)
      rw [Y_succ_pos n h]
      have : Int.fract ((3/2:ℚ) * (2 - Yf n)) = 2 - 3/2 * Yf n := by
        rw [Int.fract_eq_iff]
        refine ⟨by linarith, by linarith, 1, by push_cast; linarith⟩
      rw [this]; ring
    · have hY : ¬ (2/3 ≤ Yf n) := fun hh => h ((G_iff n).2 hh)
      push_neg at hY
      rw [Y_succ_neg n h]
      have : Int.fract ((3/2:ℚ) * (2 - Yf n)) = 1 - 3/2 * Yf n := by
        rw [Int.fract_eq_iff]
        refine ⟨by linarith, by linarith, 2, by push_cast; linarith⟩
      rw [this]; ring

def Inv (l : List ℕ) (N : ℕ) : Prop :=
  (l.map fun j => (2 / 3 : ℚ) ^ j).sum = 1 - rr N ∧
  ∀ k, k ∈ l ↔ (1 ≤ k ∧ k ≤ N ∧ (2/3:ℚ)^k ≤ rr (k-1))

theorem inv_A : ∀ N, ∃ l, Greedy l ∧ Inv l N := by
  intro N
  induction N with
  | zero => exact ⟨[], Greedy.nil, by simp [rr], fun k => by simp only [List.not_mem_nil, false_iff]; rintro ⟨a, b, _⟩; omega⟩
  | succ N ih =>
    obtain ⟨l, hg, hs, hm⟩ := ih
    by_cases h : (2/3:ℚ)^(N+1) ≤ rr N
    · refine ⟨l ++ [N+1], ?_, ?_, ?_⟩
      · refine Greedy.snoc l (N+1) hg ⟨⟨by omega, ?_⟩, ?_⟩
        · rw [hs]; linarith
        · rintro k ⟨hk1, hk2⟩
          rw [hs] at hk2
          by_contra hlt
          push_neg at hlt
          have hb := (rr_bounds N)
          have hNk : (2/3:ℚ)^N ≤ (2/3)^k := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
          rcases Nat.eq_zero_or_pos N with h0 | h0
          · omega
          · have := hb.2.2 h0
            linarith
      · simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hs]
        rw [rr_sp N h]
        ring
      · intro k
        simp only [List.mem_append, List.mem_singleton, hm]
        constructor
        · rintro (⟨a, b, c⟩ | rfl)
          · exact ⟨a, by omega, c⟩
          · exact ⟨by omega, le_rfl, by simpa using h⟩
        · rintro ⟨a, b, c⟩
          by_cases hk : k ≤ N
          · exact Or.inl ⟨a, hk, c⟩
          · exact Or.inr (by omega)
    · refine ⟨l, hg, ?_, ?_⟩
      · rw [hs, rr_sn N h]
      · intro k
        rw [hm]
        constructor
        · rintro ⟨a, b, c⟩; exact ⟨a, by omega, c⟩
        · rintro ⟨a, b, c⟩
          by_cases hk : k ≤ N
          · exact ⟨a, hk, c⟩
          · exfalso
            have : k = N + 1 := by omega
            subst this
            exact h (by simpa using c)

theorem inv_B (l : List ℕ) (hl : Greedy l) : ∃ N, Inv l N := by
  induction hl with
  | nil => exact ⟨0, by simp [rr], fun k => by simp only [List.not_mem_nil, false_iff]; rintro ⟨a, b, _⟩; omega⟩
  | snoc l e hg he ih =>
    obtain ⟨N, hs, hm⟩ := ih
    obtain ⟨⟨he1, he2⟩, hmin⟩ := he
    rw [hs] at he2
    have he2' : (2/3:ℚ)^e ≤ rr N := by linarith
    have hmin' : ∀ k, 1 ≤ k → (2/3:ℚ)^k ≤ rr N → e ≤ k := by
      intro k hk1 hk2
      exact hmin ⟨hk1, by rw [hs]; linarith⟩
    have heN : N < e := by
      by_contra hle
      push_neg at hle
      have h1 := rr_anti hle
      have h2 := (rr_bounds e).2.2 he1
      linarith
    have hr : ∀ j, N ≤ j → j < e → rr j = rr N := by
      intro j hj
      induction j, hj using Nat.le_induction with
      | base => intro _; rfl
      | succ j hj ih =>
        intro hje
        have ih' := ih (by omega)
        have hlt : ¬ (2/3:ℚ)^(j+1) ≤ rr j := by
          rw [ih']
          intro hh
          have := hmin' (j+1) (by omega) hh
          omega
        rw [rr_sn j hlt]
        exact ih'
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    have hre : rr e' = rr N := hr e' (by omega) (by omega)
    have hG : (2/3:ℚ)^(e'+1) ≤ rr e' := by rw [hre]; exact he2'
    refine ⟨e'+1, ?_, ?_⟩
    · simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hs]
      rw [rr_sp e' hG, hre]
      ring
    · intro k
      simp only [List.mem_append, List.mem_singleton, hm]
      constructor
      · rintro (⟨a, b, c⟩ | rfl)
        · exact ⟨a, by omega, c⟩
        · exact ⟨by omega, le_rfl, by simpa using hG⟩
      · rintro ⟨a, b, c⟩
        by_cases hk : k ≤ N
        · exact Or.inl ⟨a, hk, c⟩
        · by_cases hke : k = e' + 1
          · exact Or.inr hke
          · exfalso
            have hk2 : k - 1 < e'+1 := by omega
            have hk3 := hr (k-1) (by omega) hk2
            rw [hk3] at c
            have := hmin' k a c
            omega

end OMA.S_oeis_a079450

open OMA.S_oeis_a079450 in
theorem OMA.solution : type_of% @OMA.S_oeis_a079450.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h1 : a (m+1) = 2^m * (2 - Yf m) := by
    unfold a
    simp only [Nat.add_sub_cancel]
    rw [u_eq]
  have h2 : a (m+1+1) = 2^(m+1) * (2 - Yf (m+1)) := by
    unfold a
    simp only [Nat.add_sub_cancel]
    rw [u_eq]
  have hgreedy : IsGreedyPower (m+1) ↔ (2/3:ℚ)^(m+1) ≤ rr m := by
    constructor
    · rintro ⟨l, hl, hmem⟩
      obtain ⟨N, hs, hm⟩ := inv_B l hl
      have := (hm _).1 hmem
      simpa using this.2.2
    · intro h
      obtain ⟨l, hl, hs, hm⟩ := inv_A (m+1)
      exact ⟨l, hl, (hm _).2 ⟨by omega, le_rfl, by simpa using h⟩⟩
  rw [hgreedy, h1, h2]
  have hp2 : (0:ℚ) < 2^m := by positivity
  by_cases hG : (2/3:ℚ)^(m+1) ≤ rr m
  · rw [Y_succ_pos m hG]
    simp only [hG, iff_true]
    rw [pow_succ]; ring
  · rw [Y_succ_neg m hG]
    simp only [hG, iff_false]
    intro hh
    rw [pow_succ] at hh
    nlinarith [Y_pos m]
