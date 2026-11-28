import OMAStatements.S_oeis_a272101

namespace OMA.S_oeis_a272101






lemma inf : (Set.ofPred Nat.Prime).Infinite := Nat.infinite_setOfPred_prime

lemma p_prime (n : ℕ) : (p n).Prime := Nat.nth_mem_of_infinite inf _

lemma p_one : p 1 = 2 := Nat.nth_prime_zero_eq_two

lemma p_two : p 2 = 3 := Nat.nth_prime_one_eq_three

lemma p_lt {n : ℕ} (hn : 1 ≤ n) : p n < p (n + 1) := by
  unfold p
  exact Nat.nth_strictMono inf (by omega)

lemma p_ge_three {n : ℕ} (hn : 2 ≤ n) : 3 ≤ p n := by
  have h : p 2 ≤ p n := by
    unfold p
    exact (Nat.nth_strictMono inf).monotone (by omega)
  rw [p_two] at h
  exact h

/-- No prime lies strictly between `p n` and `p (n + 1)`. -/
lemma no_prime_between {n q : ℕ} (hn : 1 ≤ n) (hq : q.Prime) (h : q < p (n + 1)) : q ≤ p n := by
  unfold p at *
  have e : n + 1 - 1 = n - 1 + 1 := by omega
  rw [e] at h
  exact Nat.le_nth_of_lt_nth_succ h hq

/-- Bertrand: `p (n + 1) < 2 * p n`. -/
lemma bertrand {n : ℕ} (hn : 1 ≤ n) : p (n + 1) < 2 * p n := by
  have h2 := (p_prime n).two_le
  obtain ⟨q, hq, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (p n) (by omega)
  have hq2 : q ≠ 2 * p n := by
    rintro rfl
    exact Nat.not_prime_mul (by norm_num) (by omega) hq
  by_contra hc
  have : q < p (n + 1) := by omega
  have := no_prime_between hn hq this
  omega

lemma odd_p {n : ℕ} (hn : 2 ≤ n) : Odd (p n) := by
  rcases (p_prime n).eq_two_or_odd' with h | h
  · have := p_ge_three hn
    omega
  · exact h

lemma A069482_eq {n : ℕ} (hn : 1 ≤ n) : A069482 n = g n * (2 * p n + g n) := by
  have hlt := p_lt hn
  unfold A069482 g
  rw [Nat.sq_sub_sq]
  have : p (n + 1) + p n = 2 * p n + (p (n + 1) - p n) := by omega
  rw [this, mul_comm]

lemma le_two_of_sq_dvd {s k : ℕ} (hs : Squarefree s) (h : k ^ 2 ∣ 4 * s) : k ≤ 2 := by
  rcases Nat.even_or_odd k with ⟨j, rfl⟩ | hk
  · have e : (j + j) ^ 2 = 4 * (j * j) := by ring
    rw [e] at h
    have hj : j * j ∣ s := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h
    have := Nat.isUnit_iff.mp (hs j hj)
    omega
  · have hc : Nat.Coprime (k ^ 2) 4 := by
      have : Nat.Coprime k 2 := Nat.coprime_two_right.mpr hk
      simpa using Nat.Coprime.pow 2 2 this
    have hks : k ^ 2 ∣ s := hc.dvd_of_dvd_mul_left h
    have := Nat.isUnit_iff.mp (hs k (by rw [← pow_two]; exact hks))
    omega

/-- For `n ≥ 2`: if every number strictly between `p n` and `p (n+1)` is squarefree, the gap is 2. -/
lemma gap_two {n : ℕ} (hn : 2 ≤ n) (hall : ∀ x, p n < x → x < p (n + 1) → Squarefree x) :
    p (n + 1) = p n + 2 := by
  have h3 := p_ge_three hn
  have hlt := p_lt (show 1 ≤ n by omega)
  obtain ⟨u, hu⟩ := odd_p hn
  obtain ⟨v, hv⟩ := odd_p (show 2 ≤ n + 1 by omega)
  by_contra hne
  have h4 : p n + 4 ≤ p (n + 1) := by omega
  rcases Nat.even_or_odd u with ⟨w, hw⟩ | ⟨w, hw⟩
  · -- p n = 4w + 1, so 4 divides p n + 3
    have hsq := hall (p n + 3) (by omega) (by omega)
    have := Nat.isUnit_iff.mp (hsq 2 ⟨w + 1, by omega⟩)
    omega
  · -- p n = 4w + 3, so 4 divides p n + 1
    have hsq := hall (p n + 1) (by omega) (by omega)
    have := Nat.isUnit_iff.mp (hsq 2 ⟨w + 1, by omega⟩)
    omega

lemma all_sqfree {n : ℕ} (h : InA068361 n) : ∀ x, p n < x → x < p (n + 1) → Squarefree x := by
  intro x h1 h2
  unfold InA068361 at h
  rw [← Nat.card_Ioo] at h
  exact Finset.filter_card_eq h x (Finset.mem_Ioo.mpr ⟨h1, h2⟩)

/-- For `n ≥ 2` in A068361, `a n = 2`. -/
lemma a_eq_two {n : ℕ} (hn : 2 ≤ n) (h : InA068361 n) : a n = 2 ∧ g n = 2 := by
  have hall := all_sqfree h
  have hgap := gap_two hn hall
  have hg : g n = 2 := by unfold g; omega
  have hs : Squarefree (p n + 1) := hall _ (by omega) (by omega)
  refine ⟨?_, hg⟩
  have hM : A069482 n = 4 * (p n + 1) := by
    rw [A069482_eq (by omega), hg]
    ring
  unfold a
  rw [hM, Nat.findGreatest_eq_iff]
  refine ⟨by omega, fun _ => ⟨p n + 1, by ring⟩, ?_⟩
  intro j hj _ hdvd
  have := le_two_of_sq_dvd hs hdvd
  omega

theorem c1 : ∀ n : ℕ, 1 ≤ n → InA068361 n → a n = g n := by
  intro n hn h
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · obtain rfl : n = 1 := by omega
    have hM : A069482 1 = 5 := by
      unfold A069482
      rw [p_one, show (1 + 1 : ℕ) = 2 from rfl, p_two]
      norm_num
    have hg : g 1 = 1 := by
      unfold g
      rw [p_one, show (1 + 1 : ℕ) = 2 from rfl, p_two]
    unfold a
    rw [hM, hg]
    decide
  · obtain ⟨ha, hg⟩ := a_eq_two h2 h
    rw [ha, hg]

theorem c2 : ∀ n : ℕ, 2 ≤ n → InA068361 n → a n = 2 := fun _ hn h => (a_eq_two hn h).1

theorem c3 : ∀ n : ℕ, 1 ≤ n → a n = g n → InA068361 n := by
  intro n hn ha
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · obtain rfl : n = 1 := by omega
    unfold InA068361
    rw [p_one, show (1 + 1 : ℕ) = 2 from rfl, p_two]
    decide
  · have h3 := p_ge_three h2
    have hlt := p_lt hn
    have hb := bertrand hn
    have hgpos : 1 ≤ g n := by unfold g; omega
    have hglt : g n < p n := by unfold g; omega
    have hM := A069482_eq hn
    -- g n squared divides A069482 n
    have hsq : g n ^ 2 ∣ A069482 n := by
      unfold a at ha
      exact (Nat.findGreatest_eq_iff.mp ha).2.1 (by omega)
    -- so g n divides 2 * p n
    have hdvd : g n ∣ 2 * p n := by
      rw [hM, pow_two] at hsq
      have h1 : g n ∣ 2 * p n + g n := Nat.dvd_of_mul_dvd_mul_left (by omega) hsq
      exact (Nat.dvd_add_left (dvd_refl _)).mp h1
    -- and is coprime to p n, so it divides 2
    have hcop : Nat.Coprime (g n) (p n) := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (p_prime n)]
      intro hd
      have := Nat.le_of_dvd (by omega) hd
      omega
    have h2' : g n ∣ 2 := hcop.dvd_of_dvd_mul_right hdvd
    have hle : g n ≤ 2 := Nat.le_of_dvd (by norm_num) h2'
    obtain ⟨u, hu⟩ := odd_p h2
    obtain ⟨v, hv⟩ := odd_p (show 2 ≤ n + 1 by omega)
    have hg2 : g n = 2 := by unfold g at *; omega
    have hgap : p (n + 1) = p n + 2 := by unfold g at hg2; omega
    -- a n = 2 forces p n + 1 squarefree
    have hs : Squarefree (p n + 1) := by
      intro x hx
      rw [Nat.isUnit_iff]
      by_contra hx1
      have hx0 : x ≠ 0 := by
        rintro rfl
        simp at hx
      have hM4 : A069482 n = 4 * (p n + 1) := by rw [hM, hg2]; ring
      unfold a at ha
      rw [hg2, hM4] at ha
      have h' : ∀ j, 2 < j → j ≤ 4 * (p n + 1) → ¬ j ^ 2 ∣ 4 * (p n + 1) :=
        (Nat.findGreatest_eq_iff.mp ha).2.2
      have hxle : x ≤ p n + 1 := Nat.le_of_dvd (by omega) (Dvd.dvd.trans (Dvd.intro x rfl) hx)
      have hx2 : 2 ≤ x := by omega
      obtain ⟨c, hc⟩ := hx
      exact h' (2 * x) (by omega) (by omega) ⟨c, by rw [hc]; ring⟩
    unfold InA068361
    rw [hgap, show p n + 2 - p n - 1 = 1 by omega]
    have hI : Finset.Ioo (p n) (p n + 2) = {p n + 1} := by
      ext x
      simp only [Finset.mem_Ioo, Finset.mem_singleton]
      omega
    rw [hI, Finset.filter_singleton, if_pos hs, Finset.card_singleton]

theorem solution :
    (∀ n : ℕ, 1 ≤ n → InA068361 n → a n = g n) ∧
      (∀ n : ℕ, 2 ≤ n → InA068361 n → a n = 2) ∧
      (∀ n : ℕ, 1 ≤ n → a n = g n → InA068361 n) :=
  ⟨c1, c2, c3⟩

lemma p3 : p 3 = 5 := by
  have h : Nat.count Nat.Prime 5 = 2 := by decide
  show Nat.nth Nat.Prime 2 = 5
  rw [← h]
  exact Nat.nth_count (by norm_num)

lemma p4 : p 4 = 7 := by
  have h : Nat.count Nat.Prime 7 = 3 := by decide
  show Nat.nth Nat.Prime 3 = 7
  rw [← h]
  exact Nat.nth_count (by norm_num)

/-- Controls: 3 is in A068361 (5, 6, 7) with `a 3 = g 3 = 2`; 2 is not (3, 4, 5), and `a 2 ≠ g 2`. -/
lemma control : InA068361 3 ∧ a 3 = 2 ∧ ¬ InA068361 2 ∧ a 2 ≠ g 2 := by
  have s6 : Squarefree 6 := by
    rw [Nat.squarefree_iff_prime_squarefree]
    intro x hx hd
    have hx2 := hx.two_le
    have hle : x * x ≤ 6 := Nat.le_of_dvd (by norm_num) hd
    have hx3 : x ≤ 2 := by nlinarith
    obtain rfl : x = 2 := by omega
    norm_num at hd
  have h3 : InA068361 3 := by
    unfold InA068361
    rw [p3, show (3 + 1 : ℕ) = 4 from rfl, p4]
    have e : (Finset.Ioo 5 7).filter Squarefree = {6} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_Ioo, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨h1, h2⟩, -⟩
        omega
      · rintro rfl
        exact ⟨by norm_num, s6⟩
    rw [e]
    rfl
  have h2 : ¬ InA068361 2 := by
    unfold InA068361
    rw [p_two, show (2 + 1 : ℕ) = 3 from rfl, p3]
    have e : (Finset.Ioo 3 5).filter Squarefree = ∅ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_Ioo, Finset.notMem_empty, iff_false, not_and]
      intro ⟨h1, h2⟩ hs
      obtain rfl : x = 4 := by omega
      exact absurd (Nat.isUnit_iff.mp (hs 2 ⟨1, rfl⟩)) (by norm_num)
    rw [e]
    decide
  exact ⟨h3, c2 3 (by norm_num) h3, h2, fun h => h2 (c3 2 (by norm_num) h)⟩

end OMA.S_oeis_a272101

theorem OMA.solution : type_of% @OMA.S_oeis_a272101.main :=
  OMA.S_oeis_a272101.solution
