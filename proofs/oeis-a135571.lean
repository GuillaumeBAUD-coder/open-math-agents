import OMAStatements.S_oeis_a135571

-- Problem: A135571: Positive integers that are the difference of two positive triangular numbers in an odd number of ways.
-- Upstream: formal-conjectures statements/oeis-a135571.lean:0 (declaration OMA.S_oeis_a135571.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: T(b+u) = T(b) + n iff u(u+2b+1) = 2n. The solutions (u, b) with b >= 0 match the
-- pairs (o, f) with o odd and o f = n (o is the odd one of u and u+2b+1); the solution with b = 0
-- exists iff n is triangular. The number of pairs (o, f) is unchanged by n -> 2n, and for odd n it
-- is the number of divisor pairs, odd iff n is a square (swap involution). A triangular number is
-- never twice a square, since k(k+1) is not a square for k >= 1.

open OMA.S_oeis_a135571 in
theorem OMA.solution : type_of% @OMA.S_oeis_a135571.main := by
  have hT2 : ∀ k : ℕ, 2 * T k = k * (k + 1) := by
    intro k
    exact Nat.mul_div_cancel' (Nat.even_mul_succ_self k).two_dvd
  have hkey : ∀ b u n : ℕ, (T (b + u) = T b + n ↔ u * (u + 2 * b + 1) = 2 * n) := by
    intro b u n
    have h1 := hT2 (b + u)
    have h2 := hT2 b
    constructor
    · intro h
      linarith
    · intro h
      linarith
  -- ways n counts the solutions with b >= 1
  have hA : ∀ n : ℕ, 0 < n → ways n =
      (((Finset.range (2 * n + 1) ×ˢ Finset.range (2 * n + 1)).filter
        (fun q => q.1 * (q.1 + 2 * q.2 + 1) = 2 * n)).filter (fun q => 1 ≤ q.2)).card := by
    intro n hn
    unfold ways
    apply Finset.card_nbij' (fun p : ℕ × ℕ => (p.1 - p.2, p.2)) (fun q : ℕ × ℕ => (q.2 + q.1, q.2))
    · rintro ⟨a, b⟩ hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
        Finset.mem_range] at hp ⊢
      obtain ⟨⟨⟨ha1, ha2⟩, hb1, hb2⟩, hba, hT⟩ := hp
      obtain ⟨u, rfl⟩ : ∃ u, a = b + u := ⟨a - b, by omega⟩
      rw [show b + u - b = u by omega]
      have hE := (hkey b u n).mp hT
      exact ⟨⟨⟨by omega, by omega⟩, hE⟩, hb1⟩
    · rintro ⟨u, b⟩ hq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
        Finset.mem_range] at hq ⊢
      obtain ⟨⟨⟨hu1, hb2⟩, hE⟩, hb1⟩ := hq
      have hT := (hkey b u n).mpr hE
      have hu : 1 ≤ u := by
        rcases Nat.eq_zero_or_pos u with h0 | h0
        · rw [h0] at hE
          omega
        · exact h0
      have hbu : b + u ≤ n := by
        obtain ⟨v, rfl⟩ : ∃ v, u = v + 1 := ⟨u - 1, by omega⟩
        nlinarith [Nat.zero_le (b * v), Nat.zero_le (v * v)]
      exact ⟨⟨⟨by omega, hbu⟩, hb1, by omega⟩, by omega, hT⟩
    · rintro ⟨a, b⟩ hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
      show (b + (a - b), b) = (a, b)
      rw [Prod.mk.injEq]
      omega
    · rintro ⟨u, b⟩ -
      show (b + u - b, b) = (u, b)
      rw [Prod.mk.injEq]
      omega
  -- the solution with b = 0 exists iff n is triangular
  have hB1 : ∀ n : ℕ, (∃ k : ℕ, n = T k) →
      (((Finset.range (2 * n + 1) ×ˢ Finset.range (2 * n + 1)).filter
        (fun q => q.1 * (q.1 + 2 * q.2 + 1) = 2 * n)).filter (fun q => ¬ 1 ≤ q.2)).card = 1 := by
    intro n htri
    obtain ⟨k, hk⟩ := htri
    have hk2 := hT2 k
    rw [Finset.card_eq_one]
    refine ⟨(k, 0), ?_⟩
    ext ⟨u, b⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_singleton,
      Prod.mk.injEq]
    constructor
    · rintro ⟨⟨⟨hu, hb⟩, hE⟩, hb0⟩
      have hb0' : b = 0 := by omega
      rw [hb0'] at hE
      refine ⟨?_, hb0'⟩
      have e : u * (u + 1) = k * (k + 1) := by linarith
      rcases lt_trichotomy u k with h | h | h
      · exfalso
        have := Nat.mul_le_mul (show u + 1 ≤ k by omega) (show u + 2 ≤ k + 1 by omega)
        linarith
      · exact h
      · exfalso
        have := Nat.mul_le_mul (show k + 1 ≤ u by omega) (show k + 2 ≤ u + 1 by omega)
        linarith
    · rintro ⟨hu, hb⟩
      rw [hu, hb]
      exact ⟨⟨⟨by nlinarith [Nat.zero_le (k * k)], by omega⟩, by linarith⟩, by omega⟩
  have hB0 : ∀ n : ℕ, ¬ (∃ k : ℕ, n = T k) →
      (((Finset.range (2 * n + 1) ×ˢ Finset.range (2 * n + 1)).filter
        (fun q => q.1 * (q.1 + 2 * q.2 + 1) = 2 * n)).filter (fun q => ¬ 1 ≤ q.2)).card = 0 := by
    intro n htri
    rw [Finset.card_eq_zero]
    apply Finset.filter_false_of_mem
    rintro ⟨u, b⟩ hq hb
    change ¬ 1 ≤ b at hb
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hq
    obtain ⟨-, hE⟩ := hq
    rw [show b = 0 by omega] at hE
    apply htri
    refine ⟨u, ?_⟩
    have hu2 := hT2 u
    linarith
  -- the solutions match the pairs (o, f) with o odd and o * f = n
  have hC : ∀ n : ℕ, 0 < n →
      ((Finset.range (2 * n + 1) ×ˢ Finset.range (2 * n + 1)).filter
        (fun q => q.1 * (q.1 + 2 * q.2 + 1) = 2 * n)).card =
      ((Nat.divisorsAntidiagonal n).filter (fun p => p.1 % 2 = 1)).card := by
    intro n hn
    apply Finset.card_nbij'
      (fun q : ℕ × ℕ => if q.1 % 2 = 1 then (q.1, (q.1 + 2 * q.2 + 1) / 2)
        else (q.1 + 2 * q.2 + 1, q.1 / 2))
      (fun p : ℕ × ℕ => if p.1 < 2 * p.2 then (p.1, (2 * p.2 - p.1 - 1) / 2)
        else (2 * p.2, (p.1 - 2 * p.2 - 1) / 2))
    · rintro ⟨u, b⟩ hq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hq
      obtain ⟨-, hE⟩ := hq
      dsimp only
      split_ifs with hu
      · simp only [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisorsAntidiagonal]
        obtain ⟨f, hf⟩ : ∃ f, u + 2 * b + 1 = 2 * f := ⟨(u + 2 * b + 1) / 2, by omega⟩
        rw [hf] at hE ⊢
        rw [show 2 * f / 2 = f by omega]
        exact ⟨⟨by linarith, by omega⟩, hu⟩
      · simp only [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisorsAntidiagonal]
        obtain ⟨f, rfl⟩ : ∃ f, u = 2 * f := ⟨u / 2, by omega⟩
        rw [show 2 * f / 2 = f by omega]
        exact ⟨⟨by linarith, by omega⟩, by omega⟩
    · rintro ⟨o, f⟩ hp
      simp only [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hp
      obtain ⟨⟨hof, -⟩, ho⟩ := hp
      have hon : o ≤ n := Nat.le_of_dvd hn ⟨f, hof.symm⟩
      have hfn : f ≤ n := Nat.le_of_dvd hn ⟨o, by rw [← hof, Nat.mul_comm]⟩
      dsimp only
      split_ifs with h
      · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
        obtain ⟨c, hc⟩ : ∃ c, 2 * f = o + 2 * c + 1 := ⟨(2 * f - o - 1) / 2, by omega⟩
        rw [show (2 * f - o - 1) / 2 = c by omega]
        refine ⟨⟨by omega, by omega⟩, ?_⟩
        rw [show o + 2 * c + 1 = 2 * f by omega]
        linarith
      · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
        obtain ⟨c, hc⟩ : ∃ c, o = 2 * f + 2 * c + 1 := ⟨(o - 2 * f - 1) / 2, by omega⟩
        rw [show (o - 2 * f - 1) / 2 = c by omega]
        refine ⟨⟨by omega, by omega⟩, ?_⟩
        rw [show 2 * f + 2 * c + 1 = o by omega]
        linarith
    · rintro ⟨u, b⟩ -
      dsimp only
      by_cases hu : u % 2 = 1
      · rw [if_pos hu]
        dsimp only
        rw [if_pos (by omega : u < 2 * ((u + 2 * b + 1) / 2)), Prod.mk.injEq]
        omega
      · rw [if_neg hu]
        dsimp only
        rw [if_neg (by omega : ¬ (u + 2 * b + 1 < 2 * (u / 2))), Prod.mk.injEq]
        omega
    · rintro ⟨o, f⟩ hp
      simp only [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hp
      obtain ⟨-, ho⟩ := hp
      dsimp only
      by_cases h : o < 2 * f
      · rw [if_pos h]
        dsimp only
        rw [if_pos ho, Prod.mk.injEq]
        omega
      · rw [if_neg h]
        dsimp only
        rw [if_neg (by omega : ¬ (2 * f % 2 = 1)), Prod.mk.injEq]
        omega
  -- the number of pairs (o, f) is unchanged by doubling n
  have hodd2 : ∀ o g n : ℕ, o * g = 2 * n → o % 2 = 1 → g % 2 = 0 := by
    intro o g n hog ho
    by_contra hg
    have h1 : Odd (o * g) := Nat.odd_mul.mpr ⟨Nat.odd_iff.mpr ho, Nat.odd_iff.mpr (by omega)⟩
    rw [hog] at h1
    obtain ⟨t, ht⟩ := h1
    omega
  have hD : ∀ n : ℕ, 0 < n →
      ((Nat.divisorsAntidiagonal (2 * n)).filter (fun p => p.1 % 2 = 1)).card =
      ((Nat.divisorsAntidiagonal n).filter (fun p => p.1 % 2 = 1)).card := by
    intro n hn
    apply Finset.card_nbij' (fun p : ℕ × ℕ => (p.1, p.2 / 2)) (fun p : ℕ × ℕ => (p.1, 2 * p.2))
    · rintro ⟨o, g⟩ hp
      simp only [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hp ⊢
      obtain ⟨⟨hog, -⟩, ho⟩ := hp
      have hg := hodd2 o g n hog ho
      obtain ⟨f, rfl⟩ : ∃ f, g = 2 * f := ⟨g / 2, by omega⟩
      rw [show 2 * f / 2 = f by omega]
      exact ⟨⟨by linarith, by omega⟩, ho⟩
    · rintro ⟨o, f⟩ hp
      simp only [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hp ⊢
      obtain ⟨⟨hof, -⟩, ho⟩ := hp
      exact ⟨⟨by linarith, by omega⟩, ho⟩
    · rintro ⟨o, g⟩ hp
      simp only [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hp
      obtain ⟨⟨hog, -⟩, ho⟩ := hp
      have hg := hodd2 o g n hog ho
      show (o, 2 * (g / 2)) = (o, g)
      rw [Prod.mk.injEq]
      omega
    · rintro ⟨o, f⟩ -
      show (o, 2 * f / 2) = (o, f)
      rw [Prod.mk.injEq]
      omega
  -- for odd n every divisor pair has an odd first entry
  have hE : ∀ n : ℕ, n % 2 = 1 →
      (Nat.divisorsAntidiagonal n).filter (fun p => p.1 % 2 = 1) = Nat.divisorsAntidiagonal n := by
    intro n hn
    apply Finset.filter_true_of_mem
    rintro ⟨o, f⟩ hp
    simp only [Nat.mem_divisorsAntidiagonal] at hp
    have h1 : Odd (o * f) := by
      rw [hp.1]
      exact Nat.odd_iff.mpr hn
    exact Nat.odd_iff.mp (Nat.odd_mul.mp h1).1
  -- the number of divisor pairs of n is odd iff n is a square (swap involution)
  have hF : ∀ n : ℕ, 0 < n → (Odd (Nat.divisorsAntidiagonal n).card ↔ IsSquare n) := by
    intro n hn
    have hsplit : ((Nat.divisorsAntidiagonal n).filter (fun p : ℕ × ℕ => p.1 = p.2)).card +
        ((Nat.divisorsAntidiagonal n).filter (fun p : ℕ × ℕ => ¬ p.1 = p.2)).card =
        (Nat.divisorsAntidiagonal n).card :=
      Finset.card_filter_add_card_filter_not _
    rw [← hsplit]
    have hz : Even ((Nat.divisorsAntidiagonal n).filter (fun p : ℕ × ℕ => ¬ p.1 = p.2)).card := by
      rw [← ZMod.natCast_eq_zero_iff_even, Finset.card_eq_sum_ones, Nat.cast_sum]
      refine Finset.sum_involution (fun p _ => p.swap) ?_ ?_ ?_ ?_
      · intro p _
        show ((1 : ℕ) : ZMod 2) + ((1 : ℕ) : ZMod 2) = 0
        rw [← Nat.cast_add, ZMod.natCast_eq_zero_iff_even]
        exact ⟨1, rfl⟩
      · intro p hp _
        rw [Finset.mem_filter] at hp
        show p.swap ≠ p
        intro h
        apply hp.2
        have h' := congrArg Prod.fst h
        rw [Prod.fst_swap] at h'
        exact h'.symm
      · rintro ⟨x, y⟩ hp
        simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hp
        show (y, x) ∈ _
        simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal]
        obtain ⟨⟨hxy, h0⟩, hne⟩ := hp
        refine ⟨⟨?_, h0⟩, fun h => hne h.symm⟩
        rw [Nat.mul_comm]
        exact hxy
      · intro p _
        exact Prod.swap_swap p
    by_cases hsq : IsSquare n
    · obtain ⟨r, hr⟩ := hsq
      have hd : (Nat.divisorsAntidiagonal n).filter (fun p : ℕ × ℕ => p.1 = p.2) = {(r, r)} := by
        ext ⟨x, y⟩
        simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal, Finset.mem_singleton,
          Prod.mk.injEq]
        constructor
        · rintro ⟨⟨hxy, -⟩, hx⟩
          rw [hx] at hxy
          have hy : y = r := Nat.mul_self_inj.mp (hxy.trans hr)
          exact ⟨hx.trans hy, hy⟩
        · rintro ⟨hx, hy⟩
          rw [hx, hy]
          exact ⟨⟨hr.symm, by omega⟩, rfl⟩
      rw [hd, Finset.card_singleton]
      obtain ⟨t, ht⟩ := hz
      constructor
      · intro _
        exact ⟨r, hr⟩
      · intro _
        exact ⟨t, by omega⟩
    · have hd : (Nat.divisorsAntidiagonal n).filter (fun p : ℕ × ℕ => p.1 = p.2) = ∅ := by
        apply Finset.filter_false_of_mem
        rintro ⟨x, y⟩ hp hxy
        change x = y at hxy
        simp only [Nat.mem_divisorsAntidiagonal] at hp
        apply hsq
        refine ⟨x, ?_⟩
        rw [← hp.1, ← hxy]
      rw [hd, Finset.card_empty, Nat.zero_add]
      constructor
      · intro h
        exact absurd h (Nat.not_odd_iff_even.mpr hz)
      · intro h
        exact absurd h hsq
  -- square and twice-square under doubling
  have hG : ∀ k : ℕ, ((IsSquare k ∨ ∃ m : ℕ, k = 2 * m ^ 2) ↔
      (IsSquare (2 * k) ∨ ∃ m : ℕ, 2 * k = 2 * m ^ 2)) := by
    intro k
    constructor
    · rintro (⟨r, hr⟩ | ⟨m, hm⟩)
      · exact Or.inr ⟨r, by rw [hr]; ring⟩
      · exact Or.inl ⟨2 * m, by rw [hm]; ring⟩
    · rintro (⟨r, hr⟩ | ⟨m, hm⟩)
      · right
        have h2 : 2 ∣ r * r := ⟨k, by omega⟩
        obtain ⟨t, rfl⟩ := (Nat.prime_two.dvd_mul.mp h2).elim id id
        exact ⟨t, by linarith⟩
      · left
        exact ⟨m, by linarith⟩
  -- the number of pairs (o, f) is odd iff n is a square or twice a square
  have hod : ∀ n : ℕ, 0 < n →
      (Odd ((Nat.divisorsAntidiagonal n).filter (fun p => p.1 % 2 = 1)).card ↔
        (IsSquare n ∨ ∃ m : ℕ, n = 2 * m ^ 2)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      rcases Nat.even_or_odd' n with ⟨k, hk | hk⟩
      · have hk0 : 0 < k := by omega
        rw [hk, hD k hk0, ih k (by omega) hk0]
        exact hG k
      · rw [hE n (by omega), hF n hn]
        constructor
        · intro h
          exact Or.inl h
        · rintro (h | ⟨m, hm⟩)
          · exact h
          · omega
  -- a triangular number is never twice a square
  have hH : ∀ n : ℕ, 0 < n → (∃ k : ℕ, n = T k) → ¬ ∃ m : ℕ, n = 2 * m ^ 2 := by
    rintro n hn ⟨k, hk⟩ ⟨m, hm⟩
    have hk2 := hT2 k
    have e : k * (k + 1) = (2 * m) * (2 * m) := by linarith
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · rw [h0] at hm
        linarith
      · exact h0
    rcases Nat.lt_or_ge k (2 * m) with h | h
    · have := Nat.mul_le_mul (show k + 1 ≤ 2 * m by omega) (show k + 1 ≤ 2 * m by omega)
      linarith
    · have := Nat.mul_le_mul h h
      linarith
  intro n hn
  have h1 : ((Finset.range (2 * n + 1) ×ˢ Finset.range (2 * n + 1)).filter
        (fun q => q.1 * (q.1 + 2 * q.2 + 1) = 2 * n)).card =
      ways n + (((Finset.range (2 * n + 1) ×ˢ Finset.range (2 * n + 1)).filter
        (fun q => q.1 * (q.1 + 2 * q.2 + 1) = 2 * n)).filter (fun q => ¬ 1 ≤ q.2)).card := by
    rw [hA n hn]
    exact (Finset.card_filter_add_card_filter_not (fun q : ℕ × ℕ => 1 ≤ q.2)).symm
  rw [hC n hn] at h1
  have h2 := hod n hn
  rw [h1] at h2
  by_cases htri : ∃ k : ℕ, n = T k
  · rw [hB1 n htri, Nat.odd_add_one] at h2
    have hn2 : ¬ ∃ m : ℕ, n = 2 * m ^ 2 := hH n hn htri
    constructor
    · intro hw
      refine ⟨Or.inr (Or.inr htri), ?_⟩
      rintro ⟨hsq, -⟩
      exact (h2.mpr (Or.inl hsq)) hw
    · rintro ⟨-, hns⟩
      by_contra hw
      rcases h2.mp hw with hsq | h2sq
      · exact hns ⟨hsq, htri⟩
      · exact hn2 h2sq
  · rw [hB0 n htri, Nat.add_zero] at h2
    rw [h2]
    constructor
    · rintro (hsq | h2sq)
      · exact ⟨Or.inl hsq, fun h => htri h.2⟩
      · exact ⟨Or.inr (Or.inl h2sq), fun h => htri h.2⟩
    · rintro ⟨hsq | h2sq | htri', -⟩
      · exact Or.inl hsq
      · exact Or.inr h2sq
      · exact absurd htri' htri
