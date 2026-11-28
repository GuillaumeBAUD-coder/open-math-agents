import OMAStatements.S_oeis_a212495
import Mathlib

-- Problem: A212495 versus A033036 (base-11 numbers with only odd digits versus only even digits).
-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Proof sketch: counting. Writing n = d + 11m, the even-digit numbers below 11^k number at least 6^k
-- (injection from pairs (even digit, even-digit m)), while the odd-digit numbers below 11^k number
-- at most (5^(k+1) - 5)/4. Since 5^(k+2) <= 4*6^k for k >= 11, count odd x <= count even x for all
-- x >= 11^11. For i >= 11^11 the i-th odd-digit number o is at least i, and count odd (o+1) = i+1,
-- so i < count even (o+1), giving nth even i <= o by Nat.nth_lt_of_lt_count. Hence the set is finite.

open OMA.S_oeis_a212495 Finset

theorem a212495_digits_cons (d m : ℕ) (hd : d < 11) (h : d + 11 * m ≠ 0) :
    Nat.digits 11 (d + 11 * m) = d :: Nat.digits 11 m := by
  apply Nat.digits_add 11 (by norm_num) d m hd
  by_contra hc
  push_neg at hc
  apply h; rw [hc.1, hc.2]

theorem a212495_even_step (d m : ℕ) (hd : d < 11) (hde : Even d) (hm : evenDigits m) :
    evenDigits (d + 11 * m) := by
  intro x hx
  by_cases h : d + 11 * m = 0
  · rw [h] at hx; simp at hx
  · rw [a212495_digits_cons d m hd h] at hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hde
    · exact hm x hx

theorem a212495_odd_step (d m : ℕ) (hd : d < 11) (hdo : Odd d) (hm : m = 0 ∨ oddDigits m) :
    oddDigits (d + 11 * m) := by
  have h : d + 11 * m ≠ 0 := by
    intro h; have : d = 0 := by omega
    subst this; exact (Nat.not_odd_zero hdo)
  refine ⟨Nat.pos_of_ne_zero h, ?_⟩
  intro x hx
  rw [a212495_digits_cons d m hd h] at hx
  rcases List.mem_cons.1 hx with rfl | hx
  · exact hdo
  · rcases hm with rfl | hm
    · simp at hx
    · exact hm.2 x hx

open Classical in
theorem a212495_even_card (k : ℕ) : 6 ^ k ≤ #{x ∈ range (11 ^ k) | evenDigits x} := by
  induction k with
  | zero =>
    simp only [pow_zero]
    apply Finset.card_pos.2
    exact ⟨0, Finset.mem_filter.2 ⟨by simp, fun d hd => by simp at hd⟩⟩
  | succ k ih =>
    set E := ({x ∈ range (11 ^ k) | evenDigits x} : Finset ℕ)
    let D : Finset ℕ := {0, 2, 4, 6, 8, 10}
    have hD : #D = 6 := by decide
    have hinj : Set.InjOn (fun p : ℕ × ℕ => p.1 + 11 * p.2) (D ×ˢ E : Finset (ℕ × ℕ)) := by
      rintro ⟨a, b⟩ ha ⟨c, e⟩ hc hEq
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at ha hc
      have ha1 : a < 11 := by
        have := ha.1; simp only [D, Finset.mem_insert, Finset.mem_singleton] at this; omega
      have hc1 : c < 11 := by
        have := hc.1; simp only [D, Finset.mem_insert, Finset.mem_singleton] at this; omega
      simp only at hEq
      have h1 : a = c := by omega
      have h2 : b = e := by omega
      rw [h1, h2]
    have hmaps : ∀ p ∈ D ×ˢ E, (fun p : ℕ × ℕ => p.1 + 11 * p.2) p ∈
        ({x ∈ range (11 ^ (k + 1)) | evenDigits x} : Finset ℕ) := by
      rintro ⟨a, b⟩ hp
      rw [Finset.mem_product] at hp
      obtain ⟨ha, hb⟩ := hp
      simp only [E, Finset.mem_filter, Finset.mem_range] at hb
      have ha' : a < 11 ∧ Even a := by
        simp only [D, Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨?_, a212495_even_step a b ha'.1 ha'.2 hb.2⟩
      rw [pow_succ]; nlinarith [ha'.1, hb.1]
    have := Finset.card_le_card_of_injOn _ hmaps hinj
    rw [Finset.card_product, hD] at this
    rw [pow_succ]; nlinarith [ih, this]

open Classical in
theorem a212495_odd_card (k : ℕ) : 4 * #{x ∈ range (11 ^ k) | oddDigits x} + 5 ≤ 5 ^ (k + 1) := by
  induction k with
  | zero =>
    have : ({x ∈ range (11 ^ 0) | oddDigits x} : Finset ℕ) = ∅ := by
      ext x; simp [oddDigits]; omega
    rw [this]; simp
  | succ k ih =>
    set O := ({x ∈ range (11 ^ k) | oddDigits x} : Finset ℕ)
    let D : Finset ℕ := {1, 3, 5, 7, 9}
    have hD : #D = 5 := by decide
    have hsub : ({x ∈ range (11 ^ (k + 1)) | oddDigits x} : Finset ℕ) ⊆
        (D ×ˢ (insert 0 O)).image (fun p : ℕ × ℕ => p.1 + 11 * p.2) := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_range] at hn
      obtain ⟨hlt, hpos, hod⟩ := hn
      rw [Finset.mem_image]
      refine ⟨(n % 11, n / 11), ?_, by simp only; omega⟩
      rw [Finset.mem_product]
      have hdig := Nat.digits_def' (b := 11) (by norm_num) hpos
      have hodd : Odd (n % 11) := hod _ (by rw [hdig]; exact List.mem_cons_self)
      constructor
      · simp only [D, Finset.mem_insert, Finset.mem_singleton]
        have : n % 11 < 11 := Nat.mod_lt _ (by norm_num)
        obtain ⟨j, hj⟩ := hodd
        omega
      · rw [Finset.mem_insert]
        by_cases h0 : n / 11 = 0
        · left; exact h0
        · right
          simp only [O, Finset.mem_filter, Finset.mem_range]
          refine ⟨?_, Nat.pos_of_ne_zero h0, fun d hd => hod d ?_⟩
          · rw [pow_succ] at hlt; exact (Nat.div_lt_iff_lt_mul (by norm_num)).2 hlt
          · rw [hdig]; exact List.mem_cons_of_mem (n % 11) hd
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_image_le (s := D ×ˢ (insert 0 O)) (f := fun p : ℕ × ℕ => p.1 + 11 * p.2)
    rw [Finset.card_product, hD] at h2
    have h3 := Finset.card_insert_le 0 O
    rw [pow_succ 5 (k + 1)]
    nlinarith [h1, h2, h3, ih]

theorem a212495_ineq (k : ℕ) (hk : 11 ≤ k) : 5 ^ (k + 2) ≤ 4 * 6 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ, pow_succ 6]
    calc 5 ^ (k + 2) * 5 ≤ 4 * 6 ^ k * 5 := Nat.mul_le_mul_right 5 ih
      _ ≤ 4 * (6 ^ k * 6) := by rw [← mul_assoc]; exact Nat.mul_le_mul_left _ (by norm_num)

open Classical in
theorem a212495_count (x : ℕ) (hx : 11 ^ 11 ≤ x) :
    Nat.count oddDigits x ≤ Nat.count evenDigits x := by
  set k := Nat.log 11 x with hk
  have hx0 : x ≠ 0 := by positivity
  have h1 : 11 ^ k ≤ x := Nat.pow_log_le_self 11 hx0
  have h2 : x < 11 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) x
  have hk11 : 11 ≤ k := by
    rw [hk]; exact Nat.le_log_of_pow_le (by norm_num) hx
  have hE : Nat.count evenDigits (11 ^ k) ≤ Nat.count evenDigits x := Nat.count_monotone _ h1
  have hO : Nat.count oddDigits x ≤ Nat.count oddDigits (11 ^ (k + 1)) :=
    Nat.count_monotone _ h2.le
  rw [Nat.count_eq_card_filter_range] at hE hO
  rw [Nat.count_eq_card_filter_range] at hO
  have a := a212495_even_card k
  have b := a212495_odd_card (k + 1)
  have c := a212495_ineq k hk11
  rw [Nat.count_eq_card_filter_range] at hE ⊢
  rw [Nat.count_eq_card_filter_range]
  have : 5 ^ (k + 1 + 1) = 5 ^ (k + 2) := rfl
  omega

theorem a212495_odd_infinite : (Set.ofPred oddDigits).Infinite := by
  let r : ℕ → ℕ := fun m => Nat.rec 1 (fun _ x => 1 + 11 * x) m
  have hr : ∀ m, oddDigits (r m) ∧ m < r m := by
    intro m
    induction m with
    | zero => exact ⟨by
        show oddDigits 1
        have := a212495_odd_step 1 0 (by norm_num) (by decide) (Or.inl rfl)
        simpa using this, by simp [r]⟩
    | succ m ih =>
      have e : r (m + 1) = 1 + 11 * r m := rfl
      rw [e]
      exact ⟨a212495_odd_step 1 (r m) (by norm_num) (by decide) (Or.inr ih.1), by omega⟩
  apply Set.infinite_of_forall_exists_gt
  intro a
  exact ⟨r a, (hr a).1, (hr a).2⟩

theorem OMA.solution : type_of% @OMA.S_oeis_a212495.main := by
  classical
  apply (Set.finite_lt_nat (11 ^ 11)).subset
  intro i hi
  simp only [Set.mem_setOf_eq] at hi ⊢
  by_contra hge
  push_neg at hge
  have hinf := a212495_odd_infinite
  have hle : i ≤ Nat.nth oddDigits i := Nat.le_nth (fun hf => absurd hf hinf)
  have hc : Nat.count oddDigits (Nat.nth oddDigits i + 1) = i + 1 := by
    rw [Nat.count_succ, Nat.count_nth_of_infinite hinf, if_pos (Nat.nth_mem_of_infinite hinf i)]
  have hcnt := a212495_count (Nat.nth oddDigits i + 1) (by omega)
  have hlt : Nat.nth evenDigits i < Nat.nth oddDigits i + 1 :=
    Nat.nth_lt_of_lt_count (by omega)
  omega
