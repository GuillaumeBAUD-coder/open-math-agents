import OMAStatements.S_oeis_a267051

/-!
# A267051: Rule 92 binary representation

The rows of rule 92 satisfy: for `t >= 3`, cell `i` is ON iff `i` is even with
`0 <= i <= t-2`, or `i = t-1`, or `i = t`.  Hence `a n = 10^n + a (n-2)` for
`n >= 3`, which gives Barker's closed form and the generating function.
-/

namespace OMA

open OMA.S_oeis_a267051



lemma rule92 (l c r : Bool) :
    ruleOut 92 l c r = true ↔
      (c = true ∧ (l = false ∨ r = false)) ∨ (c = false ∧ l = true ∧ r = false) := by
  cases l <;> cases c <;> cases r <;> decide

lemma cell_succ (t : ℕ) (i : ℤ) :
    cell 92 (t + 1) i = ruleOut 92 (cell 92 t (i - 1)) (cell 92 t i) (cell 92 t (i + 1)) := rfl

lemma support (t : ℕ) (i : ℤ) (h : i < 0 ∨ (t : ℤ) < i) : cell 92 t i = false := by
  induction t generalizing i with
  | zero =>
    rw [cell]
    rcases h with h | h
    · simp [show i ≠ 0 by omega]
    · simp [show i ≠ 0 by omega]
  | succ t ih =>
    rw [cell_succ]
    rcases h with h | h
    · rcases lt_or_eq_of_le (show i ≤ -1 by omega) with hlt | heq
      · have hl : cell 92 t (i - 1) = false := ih _ (Or.inl (by omega))
        have hc : cell 92 t i = false := ih _ (Or.inl (by omega))
        have hr : cell 92 t (i + 1) = false := ih _ (Or.inl (by omega))
        rw [hl, hc, hr]; decide
      · subst heq
        have hl : cell 92 t ((-1 : ℤ) - 1) = false := ih _ (Or.inl (by norm_num))
        have hc : cell 92 t ((-1 : ℤ)) = false := ih _ (Or.inl (by norm_num))
        rw [hl, hc]
        cases hr : cell 92 t ((-1 : ℤ) + 1) <;> decide
    · push_cast at h
      have hl : cell 92 t (i - 1) = false := ih _ (Or.inr (by omega))
      have hc : cell 92 t i = false := ih _ (Or.inr (by omega))
      have hr : cell 92 t (i + 1) = false := ih _ (Or.inr (by omega))
      rw [hl, hc, hr]; decide

lemma even_sub_one' {x : ℤ} : Even (x - 1) ↔ ¬ Even x := by
  rw [even_sub_one, Int.not_even_iff_odd]

lemma even_add_one' {x : ℤ} : Even (x + 1) ↔ ¬ Even x := by
  rw [Int.even_iff, Int.even_iff]
  omega

set_option maxHeartbeats 1600000 in
lemma spec_step (t : ℕ) (ht : 3 ≤ t)
    (ih : ∀ i : ℤ, cell 92 t i = true ↔
      (Even i ∧ 0 ≤ i ∧ i ≤ (t : ℤ) - 2) ∨ i = (t : ℤ) - 1 ∨ i = (t : ℤ))
    (i : ℤ) :
    cell 92 (t + 1) i = true ↔
      (Even i ∧ 0 ≤ i ∧ i ≤ ((t : ℤ) + 1) - 2) ∨ i = ((t : ℤ) + 1) - 1 ∨ i = ((t : ℤ) + 1) := by
  have hT : ((t : ℤ) + 1) - 2 = (t : ℤ) - 1 := by ring
  have hT' : ((t : ℤ) + 1) - 1 = (t : ℤ) := by ring
  rw [hT, hT']
  by_cases hneg : i < 0
  · have hf : cell 92 (t + 1) i = false := support (t + 1) i (Or.inl hneg)
    have hnot : ¬ ((Even i ∧ 0 ≤ i ∧ i ≤ (t : ℤ) - 1) ∨ i = (t : ℤ) ∨ i = (t : ℤ) + 1) := by
      rintro (⟨_, h0, _⟩ | h | h) <;> omega
    rw [hf]; simp only [Bool.false_eq_true]
    exact ⟨False.elim, fun h => absurd h hnot⟩
  · by_cases hbig : (t : ℤ) + 1 < i
    · have hf : cell 92 (t + 1) i = false := support (t + 1) i (Or.inr (by push_cast; omega))
      have hnot : ¬ ((Even i ∧ 0 ≤ i ∧ i ≤ (t : ℤ) - 1) ∨ i = (t : ℤ) ∨ i = (t : ℤ) + 1) := by
        rintro (⟨_, h0, _⟩ | h | h) <;> omega
      rw [hf]; simp only [Bool.false_eq_true]
      exact ⟨False.elim, fun h => absurd h hnot⟩
    · have hge : (0 : ℤ) ≤ i := by omega
      have hle : i ≤ (t : ℤ) + 1 := by omega
      have ON : ∀ x : ℤ, ((Even x ∧ 0 ≤ x ∧ x ≤ (t : ℤ) - 2) ∨ x = (t : ℤ) - 1 ∨ x = (t : ℤ)) →
          cell 92 t x = true := fun x h => (ih x).mpr h
      have OFF : ∀ x : ℤ, ¬ ((Even x ∧ 0 ≤ x ∧ x ≤ (t : ℤ) - 2) ∨ x = (t : ℤ) - 1 ∨ x = (t : ℤ)) →
          cell 92 t x = false := fun x h => Bool.eq_false_of_not_eq_true (fun hc => h ((ih x).mp hc))
      rw [cell_succ, rule92]
      by_cases h1 : i = (t : ℤ) + 1
      · rw [h1]
        have hl : cell 92 t ((t : ℤ) + 1 - 1) = true := by apply ON; right; right; ring
        have hc : cell 92 t ((t : ℤ) + 1) = false := by
          apply OFF; rintro (⟨_, h, _⟩ | h | h) <;> omega
        have hr : cell 92 t ((t : ℤ) + 1 + 1) = false := by
          apply OFF; rintro (⟨_, h, _⟩ | h | h) <;> omega
        rw [hl, hc, hr]; simp
      · by_cases h2 : i = (t : ℤ)
        · rw [h2]
          have hl : cell 92 t ((t : ℤ) - 1) = true := by apply ON; right; left; ring
          have hc : cell 92 t ((t : ℤ)) = true := by apply ON; right; right; ring
          have hr : cell 92 t ((t : ℤ) + 1) = false := by
            apply OFF; rintro (⟨_, h, _⟩ | h | h) <;> omega
          rw [hl, hc, hr]; simp
        · by_cases h3 : i = (t : ℤ) - 1
          · rw [h3]
            by_cases hE : Even ((t : ℤ) - 1)
            · have hl : cell 92 t ((t : ℤ) - 1 - 1) = false := by
                apply OFF
                rintro (⟨hEv, _, _⟩ | h | h)
                · exact (even_sub_one' (x := (t : ℤ) - 1)).mp hEv hE
                · omega
                · omega
              have hc : cell 92 t ((t : ℤ) - 1) = true := by apply ON; right; left; ring
              have hr : cell 92 t ((t : ℤ) - 1 + 1) = true := by apply ON; right; right; ring
              rw [hl, hc, hr]; simp [hE]; omega
            · have hl : cell 92 t ((t : ℤ) - 1 - 1) = true := by
                apply ON; left
                exact ⟨(even_sub_one' (x := (t : ℤ) - 1)).mpr hE, by omega, by omega⟩
              have hc : cell 92 t ((t : ℤ) - 1) = true := by apply ON; right; left; ring
              have hr : cell 92 t ((t : ℤ) - 1 + 1) = true := by apply ON; right; right; ring
              rw [hl, hc, hr]; simp [hE]; omega
          · by_cases h4 : i = (t : ℤ) - 2
            · rw [h4]
              by_cases hE : Even ((t : ℤ) - 2)
              · have hl : cell 92 t ((t : ℤ) - 2 - 1) = false := by
                  apply OFF
                  rintro (⟨hEv, _, _⟩ | h | h)
                  · exact (even_sub_one' (x := (t : ℤ) - 2)).mp hEv hE
                  · omega
                  · omega
                have hc : cell 92 t ((t : ℤ) - 2) = true := by
                  apply ON; left; exact ⟨hE, by omega, by omega⟩
                have hr : cell 92 t ((t : ℤ) - 2 + 1) = true := by apply ON; right; left; ring
                rw [hl, hc, hr]; simp [hE]; omega
              · have hl : cell 92 t ((t : ℤ) - 2 - 1) = true := by
                  apply ON; left
                  exact ⟨(even_sub_one' (x := (t : ℤ) - 2)).mpr hE, by omega, by omega⟩
                have hc : cell 92 t ((t : ℤ) - 2) = false := by
                  apply OFF; rintro (⟨hEv, _, _⟩ | h | h)
                  · exact hE hEv
                  · omega
                  · omega
                have hr : cell 92 t ((t : ℤ) - 2 + 1) = true := by apply ON; right; left; ring
                rw [hl, hc, hr]; simp [hE]; omega
            · have hle3 : i ≤ (t : ℤ) - 3 := by omega
              by_cases hE : Even i
              · have hl : cell 92 t (i - 1) = false := by
                  apply OFF
                  rintro (⟨hEv, _, _⟩ | h | h)
                  · exact (even_sub_one' (x := i)).mp hEv hE
                  · omega
                  · omega
                have hc : cell 92 t i = true := by
                  apply ON; left; exact ⟨hE, by omega, by omega⟩
                have hr : cell 92 t (i + 1) = false := by
                  apply OFF
                  rintro (⟨hEv, _, _⟩ | h | h)
                  · exact (even_add_one' (x := i)).mp hEv hE
                  · omega
                  · omega
                rw [hl, hc, hr]; simp [hE]
                left; exact ⟨by omega, by omega⟩
              · have hi1 : (1 : ℤ) ≤ i := by
                  rcases lt_or_eq_of_le hge with h | h
                  · omega
                  · rw [← h] at hE; exact absurd ⟨0, by ring⟩ hE
                have hl : cell 92 t (i - 1) = true := by
                  apply ON; left
                  exact ⟨(even_sub_one' (x := i)).mpr hE, by omega, by omega⟩
                have hc : cell 92 t i = false := by
                  apply OFF; rintro (⟨hEv, _, _⟩ | h | h)
                  · exact hE hEv
                  · omega
                  · omega
                have hr : cell 92 t (i + 1) = true := by
                  apply ON; left
                  exact ⟨(even_add_one' (x := i)).mpr hE, by omega, by omega⟩
                rw [hl, hc, hr]; simp [hE]; omega

lemma spec : ∀ (t : ℕ), 3 ≤ t → ∀ i : ℤ,
    cell 92 t i = true ↔ (Even i ∧ 0 ≤ i ∧ i ≤ (t : ℤ) - 2) ∨ i = (t : ℤ) - 1 ∨ i = (t : ℤ) := by
  intro t
  induction t with
  | zero => intro ht; omega
  | succ t ih =>
    intro ht i
    rcases Nat.lt_or_ge t 3 with hlt | hge
    · interval_cases t
      · omega
      · omega
      · by_cases hneg : i < 0
        · have hf : cell 92 3 i = false := support 3 i (Or.inl hneg)
          rw [show (2 + 1 : ℕ) = 3 from rfl, hf]; simp only [Bool.false_eq_true]
          exact ⟨False.elim, fun h => by rcases h with ⟨_, h0, _⟩ | h | h <;> omega⟩
        · by_cases hbig : (3 : ℤ) < i
          · have hf : cell 92 3 i = false := support 3 i (Or.inr hbig)
            rw [show (2 + 1 : ℕ) = 3 from rfl, hf]; simp only [Bool.false_eq_true]
            exact ⟨False.elim, fun h => by rcases h with ⟨_, h0, _⟩ | h | h <;> omega⟩
          · interval_cases i <;> decide
    · exact spec_step t hge (ih hge) i

set_option maxHeartbeats 800000 in
lemma sum_biject (m : ℕ) (hm : 3 ≤ m) :
    (∑ j ∈ Finset.range (2*m-1),
        (if cell 92 m ((j:ℤ) - (m:ℤ)) then (10:ℤ)^(2*m-j) else 0))
      = ∑ k ∈ Finset.range (m/2), (10:ℤ)^(m-2*k) := by
  have key := Finset.sum_bij
    (s := Finset.range (m/2))
    (t := (Finset.range (2*m-1)).filter (fun (j : ℕ) => cell 92 m ((j:ℤ) - (m:ℤ))))
    (f := fun (k : ℕ) => (10:ℤ)^(m-2*k))
    (g := fun (j : ℕ) => (10:ℤ)^(2*m-j))
    (i := fun (k : ℕ) (_ : k ∈ Finset.range (m/2)) => m+2*k)
    (fun k hk => by
      rw [Finset.mem_range] at hk
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      have hcell : ((m + 2*k : ℕ) : ℤ) - (m:ℤ) = 2*(k:ℤ) := by push_cast; ring
      rw [hcell]
      exact (spec m hm (2*(k:ℤ))).mpr (Or.inl ⟨⟨(k:ℤ), by ring⟩, by positivity, by omega⟩))
    (fun k1 hk1 k2 hk2 heq => by
      rw [Finset.mem_range] at hk1 hk2
      omega)
    (fun j hj => by
      rw [Finset.mem_filter, Finset.mem_range] at hj
      obtain ⟨hjlt, hjc⟩ := hj
      have hspec := (spec m hm ((j:ℤ) - (m:ℤ))).mp hjc
      rcases hspec with ⟨hEv, h0, hle⟩ | heq | heq
      · obtain ⟨c, hc⟩ := hEv
        have hc0 : 0 ≤ c := by omega
        have hck : ((c.toNat : ℕ) : ℤ) = c := Int.toNat_of_nonneg hc0
        refine ⟨c.toNat, ?_, ?_⟩
        · rw [Finset.mem_range]; omega
        · omega
      · omega
      · omega)
    (fun k hk => by
      rw [Finset.mem_range] at hk
      show (10:ℤ)^(m-2*k) = (10:ℤ)^(2*m-(m+2*k))
      congr 1
      omega)
  rw [show (∑ j ∈ Finset.range (2*m-1),
        (if cell 92 m ((j:ℤ) - (m:ℤ)) then (10:ℤ)^(2*m-j) else 0))
      = ∑ j ∈ (Finset.range (2*m-1)).filter (fun (j : ℕ) => cell 92 m ((j:ℤ) - (m:ℤ))),
          (10:ℤ)^(2*m-j) from (Finset.sum_filter _ _).symm]
  exact key.symm

set_option maxHeartbeats 800000 in
lemma sum_form (m : ℕ) (hm : 3 ≤ m) :
    (∑ j ∈ Finset.range (2*m+1),
        (if cell 92 m ((j:ℤ)-(m:ℤ)) then (10:ℤ)^(2*m-j) else 0))
      = (∑ k ∈ Finset.range (m/2), (10:ℤ)^(m-2*k)) + 11 := by
  set f : ℕ → ℤ := fun j => if cell 92 m ((j:ℤ)-(m:ℤ)) then (10:ℤ)^(2*m-j) else 0 with hf
  have h1 : (∑ j ∈ Finset.range (2*m+1), f j) = (∑ j ∈ Finset.range (2*m), f j) + f (2*m) := by
    rw [Finset.sum_range_succ]
  have h2 : (∑ j ∈ Finset.range (2*m), f j) = (∑ j ∈ Finset.range (2*m-1), f j) + f (2*m-1) := by
    have h := Finset.sum_range_succ f (2*m-1)
    rwa [show (2*m-1)+1 = 2*m by omega] at h
  have h3 : f (2*m) = 1 := by
    simp only [hf]
    have harg : ((2*m : ℕ) : ℤ) - (m:ℤ) = (m:ℤ) := by push_cast; ring
    rw [harg]
    have hc : cell 92 m (m:ℤ) = true := (spec m hm (m:ℤ)).mpr (Or.inr (Or.inr rfl))
    rw [hc]
    have hw : 2*m - 2*m = (0:ℕ) := by omega
    rw [hw]; norm_num
  have h4 : f (2*m-1) = 10 := by
    simp only [hf]
    have h1m : 1 ≤ 2*m := by omega
    have harg : ((2*m-1 : ℕ) : ℤ) - (m:ℤ) = (m:ℤ) - 1 := by
      push_cast [Nat.cast_sub h1m]; ring
    rw [harg]
    have hc : cell 92 m ((m:ℤ)-1) = true := (spec m hm ((m:ℤ)-1)).mpr (Or.inr (Or.inl rfl))
    rw [hc]
    have hw : 2*m - (2*m-1) = (1:ℕ) := by omega
    rw [hw]; norm_num
  have h5 : (∑ j ∈ Finset.range (2*m-1), f j) = ∑ k ∈ Finset.range (m/2), (10:ℤ)^(m-2*k) := by
    simp only [hf]
    exact sum_biject m hm
  rw [h1, h2, h3, h4, h5]
  ring

lemma a_shift (m : ℕ) (hm : 3 ≤ m) :
    a m = (∑ k ∈ Finset.range (m/2), (10:ℤ)^(m-2*k)) + 11 := sum_form m hm

lemma a_rec (m : ℕ) (hm : 3 ≤ m) : a m = 10^m + a (m-2) := by
  rcases Nat.lt_or_ge m 5 with h | h
  · interval_cases m <;> decide
  · rw [a_shift m hm, a_shift (m-2) (by omega)]
    have hK : m/2 = (m-2)/2 + 1 := by omega
    rw [hK, Finset.sum_range_succ']
    have hsum : (∑ k ∈ Finset.range ((m-2)/2), (10:ℤ)^(m-2*(k+1)))
        = (∑ k ∈ Finset.range ((m-2)/2), (10:ℤ)^((m-2)-2*k)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range] at hk
      congr 1
      omega
    rw [hsum]
    have h0 : m - 2*0 = m := by omega
    rw [h0]
    ring

lemma a_one : a 1 = 11 := by decide
lemma a_two : a 2 = 111 := by decide
lemma a_zero : a 0 = 1 := by decide
lemma a_three : a 3 = 1011 := by decide
lemma a_four : a 4 = 10111 := by decide
lemma a_five : a 5 = 101011 := by decide

lemma a_closed (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℚ) = ((10:ℚ)^(n+2) + 450 * (-1:ℚ)^n + 539) / 99 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 3 with h | h
    · interval_cases n
      · rw [a_one]; norm_num
      · rw [a_two]; norm_num
    · have hrec := a_rec n h
      have ih' := ih (n-2) (by omega) (by omega)
      rw [hrec]
      push_cast
      rw [ih']
      have hp : (n-2)+2 = n := by omega
      rw [hp]
      have hsign : (-1:ℚ)^n = (-1:ℚ)^(n-2) := by
        rw [show n = (n-2)+2 by omega, pow_add]
        norm_num
      rw [← hsign]
      have hpow : (10:ℚ)^(n+2) = 100 * (10:ℚ)^n := by
        rw [pow_add]; ring
      rw [hpow]
      field_simp
      ring

lemma a_rec3 (n : ℕ) (hn : 4 ≤ n) : a n = 10 * a (n-1) + a (n-2) - 10 * a (n-3) := by
  have h1 := a_rec n (by omega)
  have h2 := a_rec (n-1) (by omega)
  rw [show n - 1 - 2 = n - 3 by omega] at h2
  rw [h1, h2]
  have hp : (10:ℤ)^n = 10 * 10^(n-1) := by
    rw [mul_comm, ← pow_succ, show n-1+1 = n by omega]
  rw [hp]
  ring

set_option maxHeartbeats 1600000 in
lemma gf_main :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - PowerSeries.X) * (1 + PowerSeries.X) * (1 - 10 * PowerSeries.X)) = 1 + PowerSeries.X - 100 * PowerSeries.X^3 := by
  set A : PowerSeries ℚ := PowerSeries.mk (fun n => (a n : ℚ)) with hA
  have hcoeff : ∀ m, PowerSeries.coeff m A = (a m : ℚ) := fun m => PowerSeries.coeff_mk m _
  have hD : A * ((1 - PowerSeries.X) * (1 + PowerSeries.X) * (1 - 10 * PowerSeries.X))
      = A - (A * PowerSeries.X) * 10 - A * PowerSeries.X^2 + (A * PowerSeries.X^3) * 10 := by ring
  have ten : (10 : PowerSeries ℚ) = PowerSeries.C 10 := (map_ofNat PowerSeries.C 10).symm
  have c1 : ∀ n, PowerSeries.coeff n (A * PowerSeries.X) = if 1 ≤ n then (a (n-1) : ℚ) else 0 := by
    intro n
    have h := PowerSeries.coeff_mul_X_pow' A 1 n
    rw [pow_one] at h
    rw [h]
    by_cases h1 : 1 ≤ n <;> simp [h1, hcoeff]
  have c2 : ∀ n, PowerSeries.coeff n (A * PowerSeries.X^2) = if 2 ≤ n then (a (n-2) : ℚ) else 0 := by
    intro n
    rw [PowerSeries.coeff_mul_X_pow']
    by_cases h1 : 2 ≤ n <;> simp [h1, hcoeff]
  have c3 : ∀ n, PowerSeries.coeff n (A * PowerSeries.X^3) = if 3 ≤ n then (a (n-3) : ℚ) else 0 := by
    intro n
    rw [PowerSeries.coeff_mul_X_pow']
    by_cases h1 : 3 ≤ n <;> simp [h1, hcoeff]
  apply PowerSeries.ext
  intro n
  rw [hD]
  have lhs : PowerSeries.coeff n (A - (A * PowerSeries.X) * 10 - A * PowerSeries.X^2 + (A * PowerSeries.X^3) * 10)
      = (a n : ℚ) - (if 1 ≤ n then (a (n-1) : ℚ) else 0) * 10
        - (if 2 ≤ n then (a (n-2) : ℚ) else 0) + (if 3 ≤ n then (a (n-3) : ℚ) else 0) * 10 := by
    rw [ten]
    simp only [map_sub, map_add, PowerSeries.coeff_mul_C, hcoeff, c1, c2, c3]
  have rhs : PowerSeries.coeff n (1 + PowerSeries.X - 100 * PowerSeries.X^3)
      = (if n = 0 then (1:ℚ) else 0) + (if n = 1 then (1:ℚ) else 0) - 100 * (if n = 3 then (1:ℚ) else 0) := by
    rw [show (100 : PowerSeries ℚ) = PowerSeries.C 100 from (map_ofNat PowerSeries.C 100).symm]
    simp [map_sub, map_add, PowerSeries.coeff_X_pow, PowerSeries.coeff_X, PowerSeries.coeff_one]
  rw [lhs, rhs]
  rcases Nat.lt_or_ge n 6 with h | h
  · interval_cases n <;> norm_num [a_zero, a_one, a_two, a_three, a_four, a_five]
  · have hn0 : ¬ n = 0 := by omega
    have hn1 : 1 ≤ n := by omega
    have hn2 : 2 ≤ n := by omega
    have hn3 : 3 ≤ n := by omega
    have hn3' : ¬ n = 3 := by omega
    have hn1' : ¬ n = 1 := by omega
    rw [if_neg hn0, if_neg hn1', if_pos hn1, if_pos hn2, if_pos hn3, if_neg hn3']
    have h3 := a_rec3 n (by omega)
    have hcast : (a n : ℚ) = 10 * (a (n-1) : ℚ) + (a (n-2) : ℚ) - 10 * (a (n-3) : ℚ) := by
      rw [h3]; push_cast; ring
    rw [hcast]
    ring

end OMA

open OMA.S_oeis_a267051

theorem OMA.solution : type_of% @OMA.S_oeis_a267051.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    rw [OMA.a_closed n hn]
    rw [show 2 + n = n + 2 by omega]
    ring
  · intro n hn
    have h := OMA.a_rec3 n hn
    rw [h]
    push_cast
    ring
  · exact OMA.gf_main
