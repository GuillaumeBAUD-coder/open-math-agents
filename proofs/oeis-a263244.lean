import OMAStatements.S_oeis_a263244

-- Problem: A263244: Binary representation of the n-th iteration of the "Rule 155" elementary cellular automaton starting with a single ON (black) cell
-- Upstream: formal-conjectures statements/oeis-a263244.lean:0 (declaration OMA.S_oeis_a263244.main)
-- Credit: @caa1982 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.


namespace R155
open OMA.S_oeis_a263244

def g (p : ℕ) (d : ℤ) : Bool := !(decide (d = 0) || (decide (p = 1) && decide (d = 1)))

theorem step (p : ℕ) (hp : p < 2) (d : ℤ) :
    ruleOut 155 (g p (d - 1)) (g p d) (g p (d + 1)) = g ((p + 1) % 2) (d + 1) := by
  interval_cases p
  all_goals
    by_cases h : d = -1 ∨ d = 0 ∨ d = 1 ∨ d = 2
    · rcases h with h | h | h | h <;> subst h <;> decide
    · have h1 : d - 1 ≠ 0 := by omega
      have h2 : d - 1 ≠ 1 := by omega
      have h3 : d ≠ 0 := by omega
      have h4 : d ≠ 1 := by omega
      have h5 : d + 1 ≠ 0 := by omega
      have h6 : d + 1 ≠ 1 := by omega
      simp [g, h1, h2, h3, h4, h5, h6]
      decide

theorem cell_succ (t : ℕ) (i : ℤ) : cell 155 (t + 1) i = g (t % 2) (i + t) := by
  induction t generalizing i with
  | zero =>
    show ruleOut 155 (decide (i - 1 = 0)) (decide (i = 0)) (decide (i + 1 = 0)) = _
    by_cases h : i = -1 ∨ i = 0 ∨ i = 1
    · rcases h with h | h | h <;> subst h <;> decide
    · have h1 : i - 1 ≠ 0 := by omega
      have h3 : i ≠ 0 := by omega
      have h5 : i + 1 ≠ 0 := by omega
      simp [g, h1, h3, h5]
      decide
  | succ t ih =>
    show ruleOut 155 (cell 155 (t + 1) (i - 1)) (cell 155 (t + 1) i) (cell 155 (t + 1) (i + 1)) = _
    rw [ih, ih, ih]
    have e1 : i - 1 + (t : ℤ) = (i + t) - 1 := by ring
    have e2 : i + 1 + (t : ℤ) = (i + t) + 1 := by ring
    have e3 : i + ((t + 1 : ℕ) : ℤ) = (i + t) + 1 := by push_cast; ring
    rw [e1, e2, e3, step _ (Nat.mod_lt _ (by norm_num))]
    congr 1
    omega


def S (b : ℤ) (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (2 * n + 1), if cell 155 n ((j : ℤ) - n) then b ^ (2 * n - j) else 0

theorem S_zero (b : ℤ) : S b 0 = 1 := by
  simp [S, cell]

theorem geom (b : ℤ) (m : ℕ) : (b - 1) * ∑ j ∈ Finset.range (m + 1), b ^ (m - j) = b ^ (m + 1) - 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ']
    simp only [Nat.add_sub_add_right, Nat.sub_zero]
    rw [mul_add, ih]
    ring

theorem S_succ (b : ℤ) (t : ℕ) : (b - 1) * S b (t + 1) =
    b ^ (2 * t + 3) - 1 - (b - 1) * b ^ (2 * t + 1) - (if t % 2 = 1 then (b - 1) * b ^ (2 * t) else 0) := by
  unfold S
  have hterm : ∀ j ∈ Finset.range (2 * (t + 1) + 1),
      (if cell 155 (t + 1) ((j : ℤ) - ((t + 1 : ℕ) : ℤ)) then b ^ (2 * (t + 1) - j) else 0) =
      b ^ (2 * (t + 1) - j) - (if j = 1 then b ^ (2 * t + 1) else 0)
        - (if t % 2 = 1 then (if j = 2 then b ^ (2 * t) else 0) else 0) := by
    intro j _
    rw [cell_succ]
    have e : (j : ℤ) - ((t + 1 : ℕ) : ℤ) + t = j - 1 := by push_cast; ring
    rw [e]
    rcases Nat.mod_two_eq_zero_or_one t with ht | ht
    · by_cases h1 : j = 1
      · subst h1
        have : 2 * (t + 1) - 1 = 2 * t + 1 := by omega
        simp [g, ht, this]
      · have : (j : ℤ) - 1 ≠ 0 := by omega
        simp [g, ht, h1, this]
    · by_cases h1 : j = 1
      · subst h1
        have : 2 * (t + 1) - 1 = 2 * t + 1 := by omega
        simp [g, ht, this]
      · by_cases h2 : j = 2
        · subst h2
          have : 2 * (t + 1) - 2 = 2 * t := by omega
          simp [g, ht, this]
        · have : (j : ℤ) - 1 ≠ 0 := by omega
          have : (j : ℤ) - 1 ≠ 1 := by omega
          simp [g, *]
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_sub_distrib, mul_sub, mul_sub,
    show 2 * (t + 1) = 2 * t + 2 by ring, geom]
  rw [Finset.sum_ite_eq' _ 1, if_pos (by simp)]
  split_ifs with ht
  · rw [Finset.sum_ite_eq' _ 2, if_pos (by simp)]
  · simp

theorem ha_odd (k : ℕ) : 9 * a (2 * k + 1) = 91 * 10 ^ (4 * k + 1) - 1 := by
  have h := S_succ 10 (2 * k)
  rw [if_neg (by omega)] at h
  show 9 * S 10 (2 * k + 1) = _
  rw [show 2 * (2 * k) + 3 = 4 * k + 1 + 2 by ring, show 2 * (2 * k) + 1 = 4 * k + 1 by ring] at h
  linear_combination h

theorem ha_even (k : ℕ) : 9 * a (2 * k + 2) = 901 * 10 ^ (4 * k + 2) - 1 := by
  have h := S_succ 10 (2 * k + 1)
  rw [if_pos (by omega)] at h
  show 9 * S 10 (2 * k + 1 + 1) = _
  rw [show 2 * (2 * k + 1) + 3 = 4 * k + 2 + 3 by ring, show 2 * (2 * k + 1) + 1 = 4 * k + 2 + 1 by ring,
    show 2 * (2 * k + 1) = 4 * k + 2 by ring] at h
  linear_combination h

theorem ha_zero : a 0 = 1 := S_zero 10

theorem recur (m : ℕ) : a (m + 4) = a (m + 3) + 10000 * a (m + 2) - 10000 * a (m + 1) := by
  have key : 9 * (a (m + 4) - (a (m + 3) + 10000 * a (m + 2) - 10000 * a (m + 1))) = 0 := by
    rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
    · rw [show 2 * k + 4 = 2 * (k + 1) + 2 by ring, show 2 * k + 3 = 2 * (k + 1) + 1 by ring]
      linear_combination ha_even (k + 1) - ha_odd (k + 1) - 10000 * ha_even k + 10000 * ha_odd k
    · rw [show 2 * k + 1 + 4 = 2 * (k + 2) + 1 by ring, show 2 * k + 1 + 3 = 2 * (k + 1) + 2 by ring,
        show 2 * k + 1 + 2 = 2 * (k + 1) + 1 by ring, show 2 * k + 1 + 1 = 2 * k + 2 by ring]
      linear_combination ha_odd (k + 2) - ha_even (k + 1) - 10000 * ha_odd (k + 1) + 10000 * ha_even k
  have := (mul_eq_zero.mp key).resolve_left (by norm_num)
  linarith

end R155

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a263244.main := by
  open OMA.S_oeis_a263244 R155 in
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
      show m + 4 - 3 = m + 1 by omega]
    exact recur m
  · have h1 : a 1 = 101 := by have := ha_odd 0; norm_num at this; omega
    have h2 : a 2 = 10011 := by have := ha_even 0; norm_num at this; omega
    have h3 : a 3 = 1011111 := by have := ha_odd 1; norm_num at this; omega
    rw [show ((1 - X) * (1 - 100 * X) * (1 + 100 * X) : PowerSeries ℚ)
        = 1 - X ^ 1 - C 10000 * X ^ 2 + C 10000 * X ^ 3 by simp only [map_ofNat]; ring,
      show (1 + 100 * X - 90 * X ^ 2 + 1100 * X ^ 3 : PowerSeries ℚ)
        = 1 + C 100 * X ^ 1 - C 90 * X ^ 2 + C 1100 * X ^ 3 by simp only [map_ofNat]; ring]
    rw [show ∀ p : PowerSeries ℚ, p * (1 - X ^ 1 - C 10000 * X ^ 2 + C 10000 * X ^ 3)
        = p - p * X ^ 1 - C 10000 * (p * X ^ 2) + C 10000 * (p * X ^ 3) from fun p => by ring]
    ext n
    simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_one, coeff_mk]
    rcases n with _ | _ | _ | _ | n
    · simp [ha_zero]
    · simp [ha_zero, h1]; norm_num
    · simp [ha_zero, h1, h2]; norm_num
    · simp [ha_zero, h1, h2, h3]; norm_num
    · have := recur n
      simp only [show n + 1 + 1 + 1 + 1 = n + 4 by ring]
      simp
      rw [this]
      push_cast
      ring
  · rintro n ⟨k, rfl⟩
    have h9 : (9 * a (2 * k + 1) : ℚ) = 91 * 10 ^ (4 * k + 1) - 1 := by exact_mod_cast ha_odd k
    have e : (((2 * k + 1 : ℕ) : ℤ) - 1) / 2 = (k : ℤ) := by omega
    rw [e, zpow_natCast, zpow_natCast, show (100 : ℚ) = 10 ^ 2 by norm_num, ← pow_mul]
    have hx : (91 : ℚ) * 10 ^ (2 * k) * 10 ^ (2 * k + 1) / 9 = (a (2 * k + 1) : ℚ) + 1 / 9 := by
      linear_combination (-1 / 9 : ℚ) * h9
    have key : ⌊(a (2 * k + 1) : ℚ) + 1 / 9⌋ = a (2 * k + 1) :=
      Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩
    rw [hx, key]
  · rintro n ⟨r, rfl⟩
    rcases r with _ | s
    · rw [ha_zero]
      norm_num [Int.floor_eq_iff]
    · rw [show s + 1 + (s + 1) = 2 * s + 2 by ring]
      have h9 : (9 * a (2 * s + 2) : ℚ) = 901 * 10 ^ (4 * s + 2) - 1 := by exact_mod_cast ha_even s
      have e : ((2 * s + 2 : ℕ) : ℤ) / 2 - 1 = (s : ℤ) := by omega
      rw [e, zpow_natCast, zpow_natCast, show (100 : ℚ) = 10 ^ 2 by norm_num, ← pow_mul]
      have hx : (901 : ℚ) * 10 ^ (2 * s) * 10 ^ (2 * s + 2) / 9 = (a (2 * s + 2) : ℚ) + 1 / 9 := by
        linear_combination (-1 / 9 : ℚ) * h9
      have key : ⌊(a (2 * s + 2) : ℚ) + 1 / 9⌋ = a (2 * s + 2) :=
        Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩
      rw [hx, key]
