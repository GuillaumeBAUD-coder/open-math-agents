import OMAStatements.S_oeis_a344598

/- Peter Bala's identity follows by pairing the alternating gcd sum and using
Daniel Weber's divisor-sum expression for the finite difference. -/
open Finset

private theorem sum_from_one (n : ℕ) (f : ℕ → ℤ) :
    ∑ k ∈ Icc 1 n, f k = ∑ k ∈ range n, f (k + 1) := by
  symm
  refine sum_bij (fun k _ => k + 1) ?_ ?_ ?_ ?_
  · intro k hk
    simp only [mem_range] at hk
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  · intro a _ b _ h
    omega
  · intro k hk
    obtain ⟨h₁, h₂⟩ := mem_Icc.mp hk
    exact ⟨k - 1, mem_range.mpr (by omega), by omega⟩
  · intros
    rfl

private theorem count_multiples (n d : ℕ) (hd : 0 < d) :
    (∑ k ∈ Icc 1 n, if d ∣ k then (1 : ℤ) else 0) = (n / d : ℕ) := by
  rw [← sum_filter]
  calc
    (∑ _k ∈ (Icc 1 n).filter (d ∣ ·), (1 : ℤ)) = ∑ _k ∈ Icc 1 (n / d), (1 : ℤ) := by
      symm
      refine sum_bij (fun k _ => k * d) ?_ ?_ ?_ ?_
      · intro k hk
        obtain ⟨h₁, h₂⟩ := mem_Icc.mp hk
        exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos (by omega) hd,
          (Nat.le_div_iff_mul_le hd).mp h₂⟩, dvd_mul_left d k⟩
      · intro a _ b _ h
        exact Nat.eq_of_mul_eq_mul_right hd h
      · intro k hk
        obtain ⟨hk, hdk⟩ := mem_filter.mp hk
        obtain ⟨h₁, h₂⟩ := mem_Icc.mp hk
        obtain ⟨q, rfl⟩ := hdk
        have hq : q ≠ 0 := by
          rintro rfl
          simp at h₁
        rw [mul_comm d q] at h₂ ⊢
        exact ⟨q, mem_Icc.mpr ⟨by omega, (Nat.le_div_iff_mul_le hd).mpr h₂⟩, rfl⟩
      · intros
        rfl
    _ = (n / d : ℕ) := by simp

private theorem gcd_totients {n k : ℕ} (hn : 0 < n) :
    (Nat.gcd k n : ℤ) = ∑ d ∈ Icc 1 n, if d ∣ n ∧ d ∣ k then (d.totient : ℤ) else 0 := by
  rw [← sum_filter]
  have hg : Nat.gcd k n ≠ 0 := by
    intro h
    have hd := Nat.gcd_dvd_right k n
    rw [h] at hd
    simp_all
  have hs : (Icc 1 n).filter (fun d => d ∣ n ∧ d ∣ k) = (k.gcd n).divisors := by
    ext d
    simp only [mem_filter, mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨_, hdn, hdk⟩
      exact ⟨Nat.dvd_gcd hdk hdn, hg⟩
    · rintro ⟨hd, _⟩
      have hdn := hd.trans (Nat.gcd_dvd_right k n)
      have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
      exact ⟨⟨hd0, Nat.le_of_dvd hn hdn⟩, hdn, hd.trans (Nat.gcd_dvd_left k n)⟩
  rw [hs, ← Nat.cast_sum, Nat.sum_totient]

private theorem sum_gcd (n : ℕ) (hn : 0 < n) :
    (∑ k ∈ Icc 1 n, (Nat.gcd k n : ℤ)) =
      ∑ d ∈ Icc 1 n, if d ∣ n then (d.totient : ℤ) * (n / d : ℕ) else 0 := by
  simp_rw [gcd_totients hn]
  rw [sum_comm]
  refine sum_congr rfl fun d hd => ?_
  by_cases h : d ∣ n
  · simp only [h, true_and, if_true]
    rw [← count_multiples n d (by have := (mem_Icc.mp hd).1; omega), mul_sum]
    exact sum_congr rfl fun k _ => by split <;> simp_all
  · simp [h]

private theorem div_step {n d : ℕ} (hn : 0 < n) (hd : 0 < d) :
    if d ∣ n then n / d = (n - 1) / d + 1 else n / d = (n - 1) / d := by
  have hn' : n - 1 + 1 = n := by omega
  have h₁ := Nat.mod_add_div n d
  have h₂ := Nat.mod_add_div (n - 1) d
  have hl₁ := Nat.mod_lt n hd
  have hl₂ := Nat.mod_lt (n - 1) hd
  by_cases h : d ∣ n
  · rw [if_pos h]
    have hz := Nat.dvd_iff_mod_eq_zero.mp h
    have he : n % d + d * (n / d) = (n - 1) % d + d * ((n - 1) / d) + 1 := by omega
    rw [hz, zero_add] at he
    have hmono : (n - 1) / d ≤ n / d := Nat.div_le_div_right (Nat.sub_le _ _)
    by_contra hbad
    rcases Nat.eq_or_lt_of_le hmono with heq | hlt
    · rw [heq] at he
      omega
    · have hm : d * (((n - 1) / d) + 2) ≤ d * (n / d) := Nat.mul_le_mul_left d (by omega)
      rw [Nat.mul_add] at hm
      omega
  · rw [if_neg h]
    have hpos : 0 < n % d := Nat.pos_of_ne_zero fun h0 => h (Nat.dvd_iff_mod_eq_zero.mpr h0)
    symm
    apply (Nat.div_eq_iff hd).2
    rw [Nat.mul_comm (n / d) d]
    omega

private theorem sum_difference (n : ℕ) (hn : 0 < n) :
    (∑ d ∈ Icc 1 n, (d.totient : ℤ) * (((n / d : ℕ) : ℤ) ^ 2 -
      (((n - 1) / d : ℕ) : ℤ) ^ 2)) = 2 * (∑ k ∈ Icc 1 n, (Nat.gcd k n : ℤ)) - n := by
  rw [sum_gcd n hn]
  have ht : (∑ d ∈ Icc 1 n, if d ∣ n then (d.totient : ℤ) else 0) = n := by
    simpa only [Nat.gcd_self, and_self] using (gcd_totients (k := n) hn).symm
  rw [← ht, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun d hd => ?_
  have hs := div_step hn (d := d) (by have := (mem_Icc.mp hd).1; omega)
  by_cases h : d ∣ n
  · rw [if_pos h] at hs
    simp only [if_pos h, hs, Nat.cast_add, Nat.cast_one]
    ring
  · rw [if_neg h] at hs
    simp [h, hs]

private theorem sum_pairs (n : ℕ) (f : ℕ → ℤ) :
    ∑ k ∈ range (2 * n), f (k + 1) =
      ∑ j ∈ range n, (f (2 * j + 1) + f (2 * j + 2)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
    rw [sum_range_succ, sum_range_succ, ih, sum_range_succ]
    simp only [add_assoc]

private theorem gcd_odd_double (j n : ℕ) :
    Nat.gcd (2 * j + 1) (2 * n) = Nat.gcd (2 * j + 1) n := by
  apply Nat.dvd_antisymm
  · have hd := Nat.gcd_dvd_left (2 * j + 1) (2 * n)
    have hodd : (2 * j + 1).Coprime 2 := by
      rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec]
      simp [show (2 * j + 1) % 2 = 1 by omega]
    apply Nat.dvd_gcd hd
    exact (hodd.coprime_dvd_left hd).dvd_of_dvd_mul_left (Nat.gcd_dvd_right _ _)
  · exact Nat.gcd_dvd_gcd_mul_left_right _ _ _

private theorem sum_gcd_double (n : ℕ) :
    (∑ k ∈ range (2 * n), (Nat.gcd (k + 1) (2 * n) : ℤ)) =
      2 * (∑ j ∈ range n, (Nat.gcd (j + 1) (2 * n) : ℤ)) + n := by
  let f : ℕ → ℤ := fun k => Nat.gcd k (2 * n)
  change (∑ k ∈ range (2 * n), f (k + 1)) = 2 * (∑ k ∈ range n, f (k + 1)) + n
  rw [two_mul n, sum_range_add]
  have h : (∑ k ∈ range n, f (n + k + 1)) = ∑ k ∈ range n, f k := by
    rw [← sum_range_reflect (fun k => f (n + k + 1)) n]
    refine sum_congr rfl fun k hk => ?_
    have hk' := mem_range.mp hk
    change (Nat.gcd (n + (n - 1 - k) + 1) (2 * n) : ℤ) = Nat.gcd k (2 * n)
    rw [show n + (n - 1 - k) + 1 = 2 * n - k by omega,
      Nat.gcd_sub_left_left_of_dvd _ (by omega) (dvd_refl (2 * n))]
  rw [h]
  have hshift : (∑ k ∈ range n, f k) = (∑ k ∈ range n, f (k + 1)) + n := by
    have h₁ : (∑ k ∈ range (n + 1), f k) = (∑ k ∈ range n, f k) + f n := sum_range_succ _ _
    have h₂ : (∑ k ∈ range (n + 1), f k) = (∑ k ∈ range n, f (k + 1)) + f 0 :=
      sum_range_succ' _ _
    have hfn : f n = n := by simp [f]
    have hf0 : f 0 = 2 * (n : ℤ) := by simp [f]
    rw [hfn] at h₁
    rw [hf0] at h₂
    omega
  rw [hshift]
  ring

private theorem sum_alternating_gcd (n : ℕ) :
    (∑ k ∈ Icc 1 (2 * n), (-1 : ℤ) ^ k * (Nat.gcd k (4 * n) : ℤ)) =
      2 * (∑ k ∈ Icc 1 n, (Nat.gcd k n : ℤ)) - n := by
  rw [sum_from_one, sum_from_one n,
    sum_pairs n (fun k => (-1 : ℤ) ^ k * (Nat.gcd k (4 * n) : ℤ))]
  have hplain := sum_gcd_double n
  rw [sum_pairs n (fun k => (Nat.gcd k (2 * n) : ℤ))] at hplain
  have heven (j : ℕ) :
      (Nat.gcd (2 * j + 2) (2 * n) : ℤ) = 2 * (Nat.gcd (j + 1) n : ℤ) := by
    rw [show 2 * j + 2 = 2 * (j + 1) by omega, Nat.gcd_mul_left, Nat.cast_mul]
    rfl
  have hodd (j : ℕ) :
      Nat.gcd (2 * j + 1) (4 * n) = Nat.gcd (2 * j + 1) (2 * n) := by
    rw [show 4 * n = 2 * (2 * n) by omega, gcd_odd_double]
  have heven' (j : ℕ) :
      (Nat.gcd (2 * j + 2) (4 * n) : ℤ) = 2 * (Nat.gcd (j + 1) (2 * n) : ℤ) := by
    rw [show 2 * j + 2 = 2 * (j + 1) by omega, show 4 * n = 2 * (2 * n) by omega,
      Nat.gcd_mul_left, Nat.cast_mul]
    rfl
  have hsign (j : ℕ) : (-1 : ℤ) ^ (2 * j + 1) = -1 ∧ (-1 : ℤ) ^ (2 * j + 2) = 1 := by
    rw [pow_add, pow_add, pow_mul]
    norm_num
  simp_rw [sum_add_distrib, heven, ← mul_sum] at hplain
  simp_rw [(hsign _).1, (hsign _).2, hodd, heven', neg_one_mul, one_mul,
    sum_add_distrib, sum_neg_distrib, ← mul_sum]
  omega

theorem OMA.solution : type_of% @OMA.S_oeis_a344598.main := by
  intro n hn
  rw [sum_difference n (by omega), sum_alternating_gcd]
