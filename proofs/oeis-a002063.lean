import OMAStatements.S_oeis_a002063

namespace A002063

private lemma four_dvd_large_two_power {y j : ℕ} (hy : 2 < y) (hd : y ∣ 2^j) : 4 ∣ y := by
  obtain ⟨k, _, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  cases k with
  | zero => norm_num at hy
  | succ k =>
    cases k with
    | zero => norm_num at hy
    | succ k => exact ⟨2^k, by simp only [pow_succ]; omega⟩

private lemma odd_base {x j : ℕ} (hj : 0 < j) (h : x^2 = 1 + 2^j) : x = 3 := by
  have hf : (x-1)*(x+1) = 2^j := by
    cases x with
    | zero =>
      exfalso
      exact (Nat.ne_of_lt (show 0 < 1+(2:ℕ)^j by positivity)) (by simpa using h)
    | succ x => simp only [Nat.succ_sub_one]; nlinarith
  have hu : x ≤ 3 := by
    by_contra! hlarge
    have hl := four_dvd_large_two_power (y := x-1) (by omega) (hf ▸ dvd_mul_right _ _)
    have hr := four_dvd_large_two_power (y := x+1) (by omega) (hf ▸ dvd_mul_left _ _)
    omega
  cases j with
  | zero => omega
  | succ j =>
    rw [pow_succ] at h
    have hp : 0 < (2:ℕ)^j := by positivity
    interval_cases x <;> norm_num at * <;> omega

private lemma classify (i x j : ℕ) (hij : i < j) (h : x^2 = 2^i + 2^j) :
    ∃ n : ℕ, x^2 = 9 * 4^n := by
  match i, j with
  | 0, j =>
    have hx := odd_base hij (by simpa using h)
    exact ⟨0, by rw [hx]; decide⟩
  | i+1, 0 => omega
  | i+1, j+1 =>
    have hx : 2 ∣ x := Nat.prime_two.dvd_of_dvd_pow (n := 2) (by
      rw [h, pow_succ, pow_succ]; exact ⟨2^i + 2^j, by omega⟩)
    obtain ⟨y, rfl⟩ := hx
    cases i with
    | zero =>
      cases j with
      | zero => omega
      | succ j =>
        simp only [pow_succ, pow_zero] at h
        have hm : 4 * (y*y) = 2 + 4 * 2^j := by nlinarith only [h]
        omega
    | succ i =>
      cases j with
      | zero => omega
      | succ j =>
        simp only [pow_succ] at h
        have hy : y^2 = 2^i + 2^j := by nlinarith only [h]
        obtain ⟨n, hn⟩ := classify i y j (by omega) hy
        exact ⟨n+1, by rw [pow_succ 4 n]; nlinarith only [hn]⟩
termination_by i

theorem solution : ∀ x : ℕ,
    (∃ i j : ℕ, i < j ∧ x ^ 2 = 2 ^ i + 2 ^ j) ↔
      ∃ n : ℕ, x ^ 2 = 9 * 4 ^ n := by
  intro x
  constructor
  · rintro ⟨i,j,hij,h⟩
    exact classify i x j hij h
  · rintro ⟨n,h⟩
    refine ⟨2*n, 2*n+3, by omega, ?_⟩
    rw [h, pow_add, pow_mul]
    norm_num
    ring


end A002063
theorem OMA.solution : type_of% @OMA.S_oeis_a002063.main := A002063.solution




