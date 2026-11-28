import OMAStatements.S_oeis_a297556

-- Problem: A297556, least positive integer with base-4 up-variation n (Kimberling's conjecture).
-- b(n+3) = 16 b(n) + 3 (append digits 0,3); two appended digits add at most 3 to the up-variation.
-- Credit: @bnb9001

namespace OMA_A297556_Proof

open OMA.S_oeis_a297556

def b : ℕ → ℕ
  | 0 => 1
  | 1 => 6
  | 2 => 7
  | (n + 3) => 16 * b n + 3

theorem b_pos (n : ℕ) : 0 < b n := by
  match n with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | (n + 3) => show 0 < 16 * b n + 3; omega

theorem b_mod (n : ℕ) : 1 ≤ b n % 4 := by
  match n with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | (n + 3) => show 1 ≤ (16 * b n + 3) % 4; omega

theorem digits_two (y c d : ℕ) (hy : 0 < y) (hc : c < 4) (hd : d < 4) :
    Nat.digits 4 (16 * y + (4 * c + d)) = d :: c :: Nat.digits 4 y := by
  rw [Nat.digits_def' (by norm_num) (by omega)]
  have h1 : (16 * y + (4 * c + d)) % 4 = d := by omega
  have h2 : (16 * y + (4 * c + d)) / 4 = 4 * y + c := by omega
  rw [h1, h2, Nat.digits_def' (by norm_num) (by omega)]
  have h3 : (4 * y + c) % 4 = c := by omega
  have h4 : (4 * y + c) / 4 = y := by omega
  rw [h3, h4]

theorem uv_step (y c d : ℕ) (hy : 0 < y) (hc : c < 4) (hd : d < 4) :
    uv (16 * y + (4 * c + d)) = (d - c) + ((c - y % 4) + uv y) := by
  unfold uv
  rw [digits_two y c d hy hc hd, Nat.digits_def' (by norm_num) hy, uvList, uvList]

theorem uv_lt16 (x : ℕ) (h0 : 0 < x) (h16 : x < 16) :
    uv x = if x < 4 then 0 else x % 4 - x / 4 := by
  unfold uv
  rcases Nat.lt_or_ge x 4 with h4 | h4
  · rw [if_pos h4, Nat.digits_def' (by norm_num) h0, show x / 4 = 0 by omega, Nat.digits_zero, uvList]
  · rw [if_neg (by omega), Nat.digits_def' (by norm_num) h0,
      Nat.digits_def' (by norm_num) (by omega : 0 < x / 4),
      show x / 4 / 4 = 0 by omega, Nat.digits_zero, uvList, uvList]
    rw [Nat.mod_eq_of_lt (show x / 4 < 4 by omega)]; omega

theorem uv_b (n : ℕ) : uv (b n) = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => rw [show b 0 = 1 from rfl, uv_lt16 1 (by norm_num) (by norm_num)]; rfl
    | 1, _ => rw [show b 1 = 6 from rfl, uv_lt16 6 (by norm_num) (by norm_num)]; rfl
    | 2, _ => rw [show b 2 = 7 from rfl, uv_lt16 7 (by norm_num) (by norm_num)]; rfl
    | (n + 3), ih =>
      rw [show b (n + 3) = 16 * b n + (4 * 0 + 3) from rfl,
        uv_step _ 0 3 (b_pos _) (by norm_num) (by norm_num), ih n (by omega)]
      omega

theorem b_min : ∀ n x, 0 < x → n ≤ uv x → b n ≤ x := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x hx hn
    have b0 : b 0 = 1 := rfl
    have b1 : b 1 = 6 := rfl
    have b2 : b 2 = 7 := rfl
    rcases Nat.lt_or_ge x 16 with hx16 | hx16
    · rw [uv_lt16 x hx hx16] at hn
      split_ifs at hn with hx4
      · have : n = 0 := by omega
        subst this; omega
      · have : n ≤ 2 := by omega
        interval_cases n <;> omega
    · set y := x / 16 with hy
      set c := x % 16 / 4 with hc
      set d := x % 4 with hd
      have hxyd : x = 16 * y + (4 * c + d) := by omega
      have hy0 : 0 < y := by omega
      have hc4 : c < 4 := by omega
      have hd4 : d < 4 := by omega
      rcases Nat.lt_or_ge n 3 with hn3 | hn3
      · interval_cases n <;> omega
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
        have hstep := uv_step y c d hy0 hc4 hd4
        rw [← hxyd] at hstep
        have hy4 := Nat.mod_lt y (show 4 > 0 by norm_num)
        have hy_ge : m ≤ uv y := by omega
        have hb := ih m (by omega) y hy0 hy_ge
        show 16 * b m + 3 ≤ x
        rcases Nat.lt_or_ge (b m) y with hlt | hge
        · omega
        · have hyeq : y = b m := le_antisymm hge hb
          have hmod : 1 ≤ y % 4 := by rw [hyeq]; exact b_mod _
          have huvy : uv y = m := by rw [hyeq]; exact uv_b _
          rw [huvy] at hstep
          omega

theorem a_eq_b : ∀ n, a n = (b n : ℤ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | 3, _ => decide
    | (n + 4), ih =>
      show a (n + 3) + 16 * a (n + 1) - 16 * a n = (b (n + 4) : ℤ)
      rw [ih (n + 3) (by omega), ih (n + 1) (by omega), ih n (by omega)]
      have h4 : b (n + 4) = 16 * b (n + 1) + 3 := rfl
      have h3 : b (n + 3) = 16 * b n + 3 := rfl
      rw [h4, h3]; push_cast; ring

end OMA_A297556_Proof

open OMA.S_oeis_a297556 OMA_A297556_Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a297556.main := by
  intro n
  rw [a_eq_b, Int.toNat_natCast]
  exact ⟨⟨b_pos n, uv_b n⟩, fun x ⟨hx, huv⟩ => b_min n x hx huv.ge⟩
