import OMAStatements.S_oeis_a152491

/-- Digit sum with fuel: agrees with `(Nat.digits 10 m).sum` when `m < 10 ^ k`. -/
def OMA.A152491.ds : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, m => m % 10 + OMA.A152491.ds k (m / 10)

theorem OMA.A152491.ds_eq : ∀ k m : ℕ, m < 10 ^ k → OMA.A152491.ds k m = (Nat.digits 10 m).sum := by
  intro k
  induction k with
  | zero =>
    intro m hm
    have : m = 0 := by simpa using hm
    subst this
    simp [OMA.A152491.ds]
  | succ k ih =>
    intro m hm
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0
      simp only [OMA.A152491.ds, Nat.zero_mod, Nat.zero_div, zero_add]
      rw [ih 0 (by positivity)]
    · rw [Nat.digits_def' (by norm_num) hpos, List.sum_cons]
      simp only [OMA.A152491.ds]
      rw [ih (m / 10) (by rw [pow_succ] at hm; omega)]

theorem OMA.A152491.pow_big : ∀ L : ℕ, 4 ≤ L → 81 * (L + 1) ^ 2 ≤ 10 ^ L := by
  intro L hL
  induction L, hL using Nat.le_induction with
  | base => norm_num
  | succ L hL ih =>
    have h := pow_succ 10 L
    nlinarith [ih, h, sq_nonneg L]

theorem OMA.solution : type_of% @OMA.S_oeis_a152491.main := by
  have key : ∀ n : ℕ, n < 1296 → 0 < n →
      (n + OMA.A152491.ds 4 n) ∣ n * OMA.A152491.ds 4 n → n = 2 ∨ n = 4 ∨ n = 6 ∨ n = 8 ∨ n = 18 ∨ n = 72 := by
    decide +kernel
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hn, c, hc, h⟩
    set s := (Nat.digits 10 n).sum with hsdef
    have hne : Nat.digits 10 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.2 (by omega)
    have hs0 : 0 < s := by
      have hlast := Nat.getLast_digit_ne_zero 10 (show n ≠ 0 by omega)
      have hle := List.le_sum_of_mem (List.getLast_mem hne)
      rw [← hsdef] at hle
      omega
    have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
    have hs' : (s : ℚ) ≠ 0 := by exact_mod_cast hs0.ne'
    have hc' : (c : ℚ) ≠ 0 := by exact_mod_cast hc.ne'
    rw [div_add_div _ _ hn' hs', div_eq_div_iff hc' (mul_ne_zero hn' hs')] at h
    have hq : ((c * (n + s) : ℕ) : ℚ) = ((n * s : ℕ) : ℚ) := by
      push_cast
      linear_combination (-1 : ℚ) * h
    have hnat : c * (n + s) = n * s := by exact_mod_cast hq
    -- `c < s` and `n * (s - c) = c * s`, so `n < s ^ 2`.
    have hcs : c < s := by
      by_contra hcon
      push_neg at hcon
      have : s * (n + s) ≤ c * (n + s) := Nat.mul_le_mul_right _ hcon
      nlinarith
    have hns : n < s * s := by
      have h1 : n * (s - c) = c * s := by
        have : n * s = n * (s - c) + n * c := by
          rw [← Nat.mul_add, Nat.sub_add_cancel hcs.le]
        nlinarith
      have h2 : 1 ≤ s - c := by omega
      have h3 : n ≤ c * s := by nlinarith
      nlinarith
    -- digit sum versus length
    have hlen : s ≤ 9 * (Nat.digits 10 n).length := by
      have := List.sum_le_card_nsmul (Nat.digits 10 n) 9
        (fun x hx => by have := Nat.digits_lt_base (by norm_num) hx; omega)
      simpa [hsdef, mul_comm] using this
    have hpow : 10 ^ (Nat.digits 10 n).length ≤ 10 * n := Nat.base_pow_length_digits_le 10 n (by norm_num) (by omega)
    have hL : (Nat.digits 10 n).length ≤ 4 := by
      by_contra hcon
      push_neg at hcon
      have hb := OMA.A152491.pow_big ((Nat.digits 10 n).length - 1) (by omega)
      rw [Nat.sub_add_cancel (by omega)] at hb
      have h10 : 10 ^ (Nat.digits 10 n).length = 10 * 10 ^ ((Nat.digits 10 n).length - 1) := by
        rw [← pow_succ']; congr 1; omega
      nlinarith
    have hn4 : n < 10 ^ 4 := by
      have : n < 10 ^ (Nat.digits 10 n).length := Nat.lt_base_pow_length_digits (by norm_num)
      calc n < 10 ^ (Nat.digits 10 n).length := this
        _ ≤ 10 ^ 4 := Nat.pow_le_pow_right (by norm_num) hL
    have hds : OMA.A152491.ds 4 n = s := OMA.A152491.ds_eq 4 n hn4
    have hlt : n < 1296 := by nlinarith
    apply key n hlt hn
    rw [hds]
    exact ⟨c, by rw [mul_comm (n + s) c, hnat]⟩
  · intro h
    refine ⟨by rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num, ?_⟩
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨1, by norm_num, ?_⟩
      rw [← OMA.A152491.ds_eq 4 _ (by norm_num)]
      norm_num [OMA.A152491.ds]
    · refine ⟨2, by norm_num, ?_⟩
      rw [← OMA.A152491.ds_eq 4 _ (by norm_num)]
      norm_num [OMA.A152491.ds]
    · refine ⟨3, by norm_num, ?_⟩
      rw [← OMA.A152491.ds_eq 4 _ (by norm_num)]
      norm_num [OMA.A152491.ds]
    · refine ⟨4, by norm_num, ?_⟩
      rw [← OMA.A152491.ds_eq 4 _ (by norm_num)]
      norm_num [OMA.A152491.ds]
    · refine ⟨6, by norm_num, ?_⟩
      rw [← OMA.A152491.ds_eq 4 _ (by norm_num)]
      norm_num [OMA.A152491.ds]
    · refine ⟨8, by norm_num, ?_⟩
      rw [← OMA.A152491.ds_eq 4 _ (by norm_num)]
      norm_num [OMA.A152491.ds]
