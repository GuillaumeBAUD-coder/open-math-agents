import OMAReductions.R_Andrica_andrica_conjecture_ferreira_large_n_R1

/-! Let p be the n-th prime, q the next one and x the integer square root of p, so that
x^2 ≤ p < (x + 1)^2 and x ≥ X. If p < x (x + 1), Oppermann at x + 1 gives a prime between
x (x + 1) and (x + 1)^2, so q ≤ x^2 + 2 x < (1 + sqrt p)^2. Otherwise it gives a prime
between (x + 1)^2 and (x + 1) (x + 2), so q ≤ x^2 + 3 x + 1 < (1 + sqrt p)^2 because
p ≥ x^2 + x. -/

namespace OMAAndrica

lemma next_le {n r : ℕ} (hr : r.Prime) (h : n.nth Nat.Prime < r) :
    (n + 1).nth Nat.Prime ≤ r := by
  have hc : n < Nat.count Nat.Prime r :=
    (Nat.lt_nth_iff_count_lt Nat.infinite_setOfPred_prime).2 h
  calc (n + 1).nth Nat.Prime ≤ (Nat.count Nat.Prime r).nth Nat.Prime :=
        (Nat.nth_le_nth Nat.infinite_setOfPred_prime).2 hc
    _ = r := Nat.nth_count hr

lemma sqrt_sub_lt (p q : ℕ) (s : ℝ) (hs0 : 0 ≤ s) (hs : s ^ 2 = (p : ℝ))
    (h : (q : ℝ) < (1 + s) ^ 2) : Real.sqrt q - Real.sqrt p < 1 := by
  have h1 : Real.sqrt p = s := by rw [← hs, Real.sqrt_sq hs0]
  have h2 : Real.sqrt q < 1 + s := (Real.sqrt_lt' (by linarith)).2 h
  linarith

end OMAAndrica

theorem OMA.solution : OMA.R_Andrica_andrica_conjecture_ferreira_large_n_R1.H2 := by
  intro X hX n hn
  obtain ⟨p, hp⟩ : ∃ p, p = n.nth Nat.Prime := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = (n + 1).nth Nat.Prime := ⟨_, rfl⟩
  rw [← hp] at hn ⊢
  rw [← hq]
  obtain ⟨x, hx⟩ : ∃ x, x = Nat.sqrt p := ⟨_, rfl⟩
  have hx1 : x ^ 2 ≤ p := hx ▸ Nat.sqrt_le' p
  have hx2 : p < (x + 1) ^ 2 := hx ▸ Nat.lt_succ_sqrt' p
  have hXx : X ≤ x := hx ▸ Nat.le_sqrt'.2 hn
  obtain ⟨⟨r1, hr1, hr1p⟩, ⟨r2, hr2, hr2p⟩⟩ := hX (x + 1) (by omega)
  rw [Finset.mem_Ioo] at hr1 hr2
  have e1 : x + 1 - 1 = x := by omega
  rw [e1] at hr1
  have hs0 : (0 : ℝ) ≤ Real.sqrt p := Real.sqrt_nonneg _
  have hs : Real.sqrt p ^ 2 = (p : ℝ) := Real.sq_sqrt (Nat.cast_nonneg p)
  have hsx : (x : ℝ) ≤ Real.sqrt p := by
    apply Real.le_sqrt_of_sq_le
    exact_mod_cast hx1
  have hpR : ((x : ℝ)) ^ 2 ≤ (p : ℝ) := by exact_mod_cast hx1
  apply OMAAndrica.sqrt_sub_lt p q _ hs0 hs
  by_cases hc : p < x * (x + 1)
  · have hqr : q ≤ r1 := hq ▸ OMAAndrica.next_le hr1p (by rw [← hp]; nlinarith [hr1.1])
    have hq2 : q + 1 ≤ (x + 1) ^ 2 := by omega
    have hq3 : (q : ℝ) + 1 ≤ ((x : ℝ) + 1) ^ 2 := by exact_mod_cast hq2
    nlinarith
  · have hc' : x * (x + 1) ≤ p := not_lt.1 hc
    have hqr : q ≤ r2 := hq ▸ OMAAndrica.next_le hr2p (by rw [← hp]; omega)
    have hq2 : q + 1 ≤ (x + 1) * (x + 1 + 1) := by omega
    have hq3 : (q : ℝ) + 1 ≤ ((x : ℝ) + 1) * ((x : ℝ) + 1 + 1) := by exact_mod_cast hq2
    have hc3 : (x : ℝ) * ((x : ℝ) + 1) ≤ (p : ℝ) := by exact_mod_cast hc'
    by_cases hx0 : x = 0
    · subst hx0
      have hp1 : 1 ≤ p := by
        rw [hp]; exact (Nat.prime_nth_prime n).one_lt.le
      have hp1' : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp1
      have : (1 : ℝ) ≤ Real.sqrt p := by
        rw [show (1 : ℝ) = Real.sqrt 1 by simp]
        exact Real.sqrt_le_sqrt hp1'
      simp at hq3
      nlinarith
    · have hxpos : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hx0
      have hlt : (x : ℝ) < Real.sqrt p := by
        apply Real.lt_sqrt_of_sq_lt
        nlinarith
      nlinarith
