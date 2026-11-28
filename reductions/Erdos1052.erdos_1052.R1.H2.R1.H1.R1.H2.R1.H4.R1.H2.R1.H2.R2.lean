import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H2_R1

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H4.R1.H2.R1.H2.R2 of step Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H4.R1.H2.R1.H2
-- Credit: @CBaquero

-- The Graham-weight argument in the parent reduction (sanchan, building on
-- aroth01) is sharpened at the 11-leaves. If 43 is missing their total
-- weight is small enough to contradict the unitary divisor balance.
-- Both 7 and 43 must then have simple donors because neither divides a
-- square plus one. The two remaining bounds concern shared or distinct donors.
namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H2_R1_H2_R2

def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 11) →
    6 ≤ n.factorization 11 →
    n.factorization 11 % 4 = 2 →
    padicValNat 2 n % 4 = 2 →
    padicValNat 2 n % 20 ≠ 10 →
    padicValNat 2 n % 28 ≠ 14 →
    7 ∣ n → ¬ 13 ∣ n →
    43 ∣ n →
    (∃ p ∈ n.primeFactors, n.factorization p = 1 ∧ 601 ≤ p ∧ 602 ∣ p+1) →
    padicValNat 2 n ≤ A

def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 11) →
    6 ≤ n.factorization 11 →
    n.factorization 11 % 4 = 2 →
    padicValNat 2 n % 4 = 2 →
    padicValNat 2 n % 20 ≠ 10 →
    padicValNat 2 n % 28 ≠ 14 →
    7 ∣ n → ¬ 13 ∣ n →
    43 ∣ n →
    (∃ p ∈ n.primeFactors, ∃ t ∈ n.primeFactors, p ≠ t ∧
      n.factorization p = 1 ∧ n.factorization t = 1 ∧
      223 ≤ p ∧ 3181 ≤ t ∧ 7 ∣ p+1 ∧ 43 ∣ t+1 ∧ ¬ 7 ∣ t+1) →
    padicValNat 2 n ≤ A



open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H2_R1

theorem split_estimate {L : Finset ℕ} {β : ℕ → ℚ} {a b : ℚ} (p : ℕ → Prop)
    (ha : 0 ≤ a) (hβ : ∀ q ∈ L, 0 ≤ β q)
    (hl : ∀ T ⊆ L, (∀ q ∈ T, p q) → ∏ q ∈ T, β q ≤ a)
    (hr : ∀ T ⊆ L, (∀ q ∈ T, ¬ p q) → ∏ q ∈ T, β q ≤ b) :
    ∏ q ∈ L, β q ≤ a*b := by
  classical
  rw [← Finset.prod_filter_mul_prod_filter_not L p]
  exact mul_le_mul
    (hl _ (Finset.filter_subset _ _) (fun q hq => (Finset.mem_filter.mp hq).2))
    (hr _ (Finset.filter_subset _ _) (fun q hq => (Finset.mem_filter.mp hq).2))
    (Finset.prod_nonneg (fun q hq => hβ q (Finset.mem_filter.mp hq).1)) ha

theorem sharp_leaf11 {L : Finset ℕ} {β : ℕ → ℚ} (h43 : β 43 = 1)
    (hLp : ∀ q ∈ L, q.Prime ∧ q ≠ 2)
    (hL11 : ∀ q ∈ L, 11 ∣ q+1 ∧ ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q+1 → c=11)
    (hLβ : ∀ q ∈ L, 0 < β q ∧ β q ≤ ((q : ℚ)+1)/((q : ℚ)-1)) :
    ∏ q ∈ L, β q ≤ (1 * (11264/11262)) *
      (((242/240)*(968/966) * (61952/61950)) * (1331/1328)) := by
  classical
  have hkj : ∀ q ∈ L, ∃ k j, 1 ≤ k ∧ 1 ≤ j ∧ q + 1 = 2 ^ k * 11 ^ j := fun q hq => by
    obtain ⟨k, j, heq⟩ := two_pow_mul_pow_of_odd_primes_eq (by omega) (hL11 q hq).2
    have hodd := Nat.odd_iff.mp ((hLp q hq).1.odd_of_ne_two (hLp q hq).2)
    have hk1 : 1 ≤ k := by
      by_contra h0
      have hk0 : k = 0 := by omega
      rw [hk0, pow_zero, one_mul] at heq
      have : ∀ t : ℕ, (11 ^ t) % 2 = 1 := fun t => by
        induction t with
        | zero => norm_num
        | succ t ih => rw [pow_succ, Nat.mul_mod, ih]
      have := this j
      omega
    have hj1 : 1 ≤ j := by
      by_contra h0
      have hj0 : j = 0 := by omega
      rw [hj0, pow_zero, mul_one] at heq
      have h11d : 11 ∣ 2 ^ k := heq ▸ (hL11 q hq).1
      have := (Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).mp
        (Nat.Prime.dvd_of_dvd_pow (by norm_num) h11d)
      norm_num at this
    exact ⟨k, j, hk1, hj1, heq⟩

  choose! k j hk hj he using hkj
  have liftB (T : Finset ℕ) (hT : T ⊆ L) :
      ∏ q ∈ T, β q ≤ ∏ q ∈ T, (((q : ℚ)+1)/((q : ℚ)-1)) :=
    Finset.prod_le_prod (fun q hq => (hLβ q (hT hq)).1.le) (fun q hq => (hLβ q (hT hq)).2)
  refine split_estimate (fun q => j q = 1) (by norm_num)
    (fun q hq => (hLβ q hq).1.le) ?_ ?_
  · intro T hT hj1
    refine split_estimate (fun q => q=43) (by norm_num)
      (fun q hq => (hLβ q (hT hq)).1.le) ?_ ?_
    · intro U hU h43U
      exact le_of_eq (Finset.prod_eq_one (fun q hq => (h43U q hq) ▸ h43))
    · intro U hU hx
      refine (liftB U (hU.trans hT)).trans ((fiber_bound (u := 11264) (by norm_num) U ?_).trans (by norm_num))
      intro q hq
      have hqt := hU hq
      have hql := hT hqt
      have hqk := hk q hql
      have hqe := he q hql
      rw [hj1 q hqt, pow_one] at hqe
      have big : 11 ≤ k q := by
        by_contra! hsmall
        have hprime := (hLp q hql).1
        have hne := hx q hq
        have hval : q = 2 ^ k q * 11 - 1 := by omega
        generalize hkk : k q = v at hval hsmall hqk
        interval_cases v <;> norm_num at hval <;> subst q <;> first | exact hne rfl | exact absurd hprime (by norm_num)
      refine ⟨k q-10, by omega, ?_⟩
      rw [hqe, show k q = k q-10+10 by omega] <;> simp [pow_add] <;> ring
  · intro T hT hjnot
    refine split_estimate (fun q => j q = 2) (by norm_num)
      (fun q hq => (hLβ q (hT hq)).1.le) ?_ ?_
    · intro U hU hj2
      refine split_estimate (fun q => q ∈ ({241,967} : Finset ℕ)) (by norm_num)
        (fun q hq => (hLβ q (hT (hU hq))).1.le) ?_ ?_
      · intro V hV hsmall
        have A := Finset.prod_le_prod_of_subset_of_one_le
          (f := fun q : ℕ => ((q : ℚ)+1)/((q : ℚ)-1)) (show V ⊆ {241,967} from fun q hq => hsmall q hq)
          (fun q hq => B_nonneg (hLp q (hT (hU (hV hq)))).1.one_le)
          (fun q hq _ => by simp only [Finset.mem_insert,Finset.mem_singleton] at hq; rcases hq with rfl|rfl <;> norm_num)
        exact (liftB V (hV.trans (hU.trans hT))).trans (A.trans (by norm_num))
      · intro V hV hx
        refine (liftB V (hV.trans (hU.trans hT))).trans ((fiber_bound (u := 61952) (by norm_num) V ?_).trans (by norm_num))
        intro q hq
        have hqu := hV hq
        have hql := hT (hU hqu)
        have hqk := hk q hql
        have hqe := he q hql
        rw [hj2 q hqu] at hqe
        have big : 10 ≤ k q := by
          by_contra! hsmall
          have hprime := (hLp q hql).1
          have hne := hx q hq
          have hval : q = 2 ^ k q * 11^2 - 1 := by omega
          generalize hkk : k q = v at hval hsmall hqk
          interval_cases v <;> norm_num at hval <;> subst q <;> first | exact hne (by decide) | exact absurd hprime (by norm_num)
        refine ⟨k q-9, by omega, ?_⟩
        rw [hqe, show k q = k q-9+9 by omega] <;> simp [pow_add] <;> ring
    · intro U hU hjnot2
      refine (liftB U (hU.trans hT)).trans ((zleaf_bound (z := 11) (by norm_num) 3 (by norm_num) U ?_).trans (by norm_num))
      intro q hq
      have hql := hT (hU hq)
      exact ⟨k q,j q,hk q hql,by have := hj q hql; have := hjnot q (hU hq); have := hjnot2 q hq; omega, he q hql⟩
theorem graham_contra_six {m e z : ℕ} {P : Finset ℕ} {zB : ℚ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (hz : z.Prime) (hm : 20 ≤ m) (he : 6 ≤ e)
    (E : (2 ^ m + 1) * (1 + z ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * z ^ e * ∏ p ∈ P, p)
    (β : ℕ → ℚ)
    (hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1))
    (h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
        (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ ({z} : Finset ℕ) → c' ∣ p + 1 → c ≤ c') →
        β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c)
    (h1 : 1 ≤ β 3 ∧ 1 ≤ β 7 ∧ 1 ≤ β 31 ∧ 1 ≤ β 127)
    (hzL : ∀ L : Finset ℕ, (∀ q ∈ L, q.Prime ∧ q ≠ 2) →
        (∀ q ∈ L, z ∣ q + 1 ∧ ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c = z) →
        (∀ q ∈ L, 0 < β q ∧ β q ≤ ((q : ℚ) + 1) / ((q : ℚ) - 1)) → ∏ q ∈ L, β q ≤ zB)
    (hnum : (1 + 1 / (2 : ℚ) ^ 20) * (1 + 1 / (z : ℚ) ^ 6) *
        ((β 3 * β 7 * β 31 * β 127) * (2048 / 2047) * zB) < 2) :
    False := by
  have hK := prime_dvd_prime_pow (e := e) hz
  have hK0 : 0 < z ^ e := pow_pos hz.pos e
  obtain ⟨L, hLP, hLleaf, hmain⟩ := master_gen hP hK hK0 E β hB h4
  have hLpos : ∀ q ∈ L, 0 < β q ∧ β q ≤ ((q : ℚ) + 1) / ((q : ℚ) - 1) := fun q hq => by
    have hb := hB q (hLP hq)
    have h0 : (0 : ℚ) ≤ 1 / (q : ℚ) := by positivity
    exact ⟨by linarith [hb.1], hb.2⟩
  rw [← Finset.prod_filter_mul_prod_filter_not L (fun q => ¬ z ∣ q + 1)] at hmain
  have hM : ∏ q ∈ L.filter (fun q => ¬ z ∣ q + 1), β q ≤
      (β 3 * β 7 * β 31 * β 127) * (2048 / 2047) := by
    refine mersenne_bound β _ (fun q hq => (hP q (hLP (Finset.mem_filter.mp hq).1)).1)
      (fun q hq => two_pow_of_no_odd_prime (fun c hc hc2 hcd => by
        obtain ⟨hqL, hnd⟩ := Finset.mem_filter.mp hq
        have hcz : c = z := Finset.mem_singleton.mp (hLleaf q hqL c hc hc2 hcd)
        exact hnd (hcz ▸ hcd)))
      (fun q hq => hLpos q (Finset.mem_filter.mp hq).1) h1
  have hZ : ∏ q ∈ L.filter (fun q => ¬ ¬ z ∣ q + 1), β q ≤ zB := by
    refine hzL _ (fun q hq => hP q (hLP (Finset.mem_filter.mp hq).1))
      (fun q hq => by
        obtain ⟨hqL, hd⟩ := Finset.mem_filter.mp hq
        push Not at hd
        exact ⟨hd, fun c hc hc2 hcd => Finset.mem_singleton.mp (hLleaf q hqL c hc hc2 hcd)⟩)
      (fun q hq => hLpos q (Finset.mem_filter.mp hq).1)
  have hprod : (∏ q ∈ L.filter (fun q => ¬ z ∣ q + 1), β q) *
      (∏ q ∈ L.filter (fun q => ¬ ¬ z ∣ q + 1), β q) ≤
      (β 3 * β 7 * β 31 * β 127) * (2048 / 2047) * zB :=
    mul_le_mul hM hZ (Finset.prod_nonneg fun q hq => (hLpos q (Finset.mem_filter.mp hq).1).1.le)
      (by have := h1.1; have := h1.2.1; have := h1.2.2.1; have := h1.2.2.2; positivity)
  have h2m : (1 + 1 / (2 : ℚ) ^ m) ≤ 1 + 1 / (2 : ℚ) ^ 20 := by
    have hpow : (2 : ℚ) ^ 20 ≤ (2 : ℚ) ^ m := pow_le_pow_right₀ (by norm_num) hm
    have := one_div_le_one_div_of_le (by positivity : (0 : ℚ) < (2 : ℚ) ^ 20) hpow
    linarith
  have hze : ((1 + z ^ e : ℕ) : ℚ) / ((z ^ e : ℕ) : ℚ) ≤ 1 + 1 / (z : ℚ) ^ 6 := by
    have hz1 : (1 : ℚ) ≤ z := by exact_mod_cast hz.one_le
    have hpow : (z : ℚ) ^ 6 ≤ (z : ℚ) ^ e := pow_le_pow_right₀ hz1 he
    have hpos : (0 : ℚ) < (z : ℚ) ^ 6 := by positivity
    have hpos2 : (0 : ℚ) < (z : ℚ) ^ e := by positivity
    have hdiv := one_div_le_one_div_of_le hpos hpow
    push_cast
    rw [add_div, div_self hpos2.ne']
    linarith
  have hfac : (1 + 1 / (2 : ℚ) ^ m) * (((1 + z ^ e : ℕ) : ℚ) / ((z ^ e : ℕ) : ℚ)) ≤
      (1 + 1 / (2 : ℚ) ^ 20) * (1 + 1 / (z : ℚ) ^ 6) :=
    mul_le_mul h2m hze (by positivity) (by positivity)
  have htot := mul_le_mul hfac hprod
    (mul_nonneg (Finset.prod_nonneg fun q hq => (hLpos q (Finset.mem_filter.mp hq).1).1.le)
      (Finset.prod_nonneg fun q hq => (hLpos q (Finset.mem_filter.mp hq).1).1.le))
    (by positivity)
  linarith


theorem force43 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (h11 : 11 ∉ P) (h13 : 13 ∉ P) (he6 : 6 ≤ e) (hm : 20 ≤ m) (he : e % 4 = 2) (hm2 : m % 4 = 2)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 11 ^ e * ∏ p ∈ P, p) :
    43 ∈ P := by
  have he2 : 2 ≤ e := by omega
  have hK := prime_dvd_prime_pow (e := e) (z := 11) (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 11 → c ∉ ({11} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, -, S6, -, S8⟩ := facts hP hK E
  obtain ⟨h61d, h61P, h31P⟩ := z11_61_31 hP he E
  have h5m : 5 ∣ 2 ^ m + 1 := five_dvd_two_pow_add_one hm2
  have h5P : 5 ∈ P := S2 5 (by norm_num) (by norm_num) (hnz (by norm_num)) h5m
  have h3P : 3 ∈ P := S1 3 Nat.prime_three (by norm_num) (hnz (by norm_num)) 5 h5P (by norm_num)

  by_contra h43
  let β : ℕ → ℚ := fun p =>
    if p = 3 then 8 / 5
    else if p = 5 then 6 / 5
    else if p = 61 then 62 / 61
    else if p = 31 then 64 / 61
    else if p = 7 then (8/7)*(182/180)
    else if p = 43 then 1
    else ((p : ℚ)+1)/((p : ℚ)-1)
  have HB : ∀ p ∈ P, 1 + 1/(p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ)+1)/((p : ℚ)-1) := by
    intro p hp
    dsimp only [β]
    split_ifs with h3 h5 h61 h31 h7 h43'
    · subst p; norm_num
    · subst p; norm_num
    · subst p; norm_num
    · subst p; norm_num
    · subst p; norm_num
    · exact absurd (h43' ▸ hp) h43
    · exact ⟨one_add_le_B (hP p hp).1.two_le,le_rfl⟩
  apply graham_contra_six (z := 11) hP (by norm_num) hm he6 E β HB _
    (by dsimp [β]; norm_num) (fun L hL hs hB => sharp_leaf11 (by dsimp [β]) hL hs hB)
    (by dsimp [β]; norm_num)
  intro p hp c hcP hcd hmin hne
  dsimp only [β] at hne
  split_ifs at hne with hc3 hc5 hc61 hc31 hc7 hc43
  · subst hc3
    have hpeq := S3 3 Nat.prime_three (by norm_num) (hnz (by norm_num)) p hp 5 h5P hcd (by norm_num)
    rw [hpeq]; dsimp only [β]; norm_num
  · subst hc5
    exact absurd hcd (S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) h5m p hp)
  · subst hc61
    exact absurd hcd (S8 61 (by norm_num) (by norm_num) (hnz (by norm_num)) h61d p hp)
  · subst hc31
    have hpeq := S3 31 (by norm_num) (by norm_num) (hnz (by norm_num)) p hp 61 h61P hcd (by norm_num)
    rw [hpeq]; dsimp only [β]; norm_num
  · subst hc7
    have hsq := S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) p hp
    have hp181 := (parent_ge_of_c7 (z := 11) (hP p hp).1 (hP p hp).2
      (fun h => h11 (h ▸ hp)) (fun h => h13 (h ▸ hp)) (by decide) (by decide) (by decide)
      hcd hmin hsq).2 rfl
    have hle := (HB p hp).2.trans (B_anti (by norm_num : 2 ≤ 181) hp181)
    have hle' : β p ≤ 182 / 180 := hle.trans (by norm_num)
    change (1 + 1 / (7 : ℚ)) * β p ≤ (8/7)*(182/180)
    linarith
  · exact absurd (hc43 ▸ hcP) h43
  · exact absurd rfl hne


theorem simple_donor {m e c : ℕ} {P : Finset ℕ} (hc : c.Prime) (hc4 : c % 4 = 3)
    (hcP : c ∈ P) (hm : m % 4 = 2) (he : e % 4 = 2)
    (E : (2 ^ m + 1) * (1 + 11 ^ e) * ∏ p ∈ P, (p+1) =
      2 ^ (m+1) * 11 ^ e * ∏ p ∈ P, p) : ∃ p ∈ P, c ∣ p+1 := by
  have square (x b : ℕ) (hb : b % 4 = 2) : ¬ c ∣ x^b+1 := by
    intro h
    have hs : c ∣ (x^(b/2))^(2^1)+1 := by
      rwa [← pow_mul, show b/2 * 2^1 = b by omega]
    obtain ⟨j,hj⟩ := Nat.pow_pow_add_primeFactors_one_lt hc (by omega) hs
    omega
  have hdiv : c ∣ 2 ^ (m+1) * 11 ^ e * ∏ p ∈ P, p :=
    dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem (fun p => p) hcP) _
  rw [← E] at hdiv
  rcases hc.dvd_mul.mp hdiv with h | h
  · rcases hc.dvd_mul.mp h with h | h
    · exact False.elim (square 2 m hm h)
    · exact False.elim (square 11 e he (by simpa [Nat.add_comm] using h))
  · exact (Prime.dvd_finsetProd_iff hc.prime _).mp h

set_option maxRecDepth 8000 in
theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H2_R1.H2 := by
  rintro ⟨A,hA⟩ ⟨B,hB⟩
  refine ⟨max 20 (max A B), ?_⟩
  intro n hn hu he6 he hm h20 h28 hn7 hn13
  by_cases hlarge : 20 ≤ padicValNat 2 n
  swap
  · omega
  have hn0 := hn.2.ne'
  have h11pf : 11 ∈ n.primeFactors := Nat.mem_primeFactors.mpr
    ⟨by norm_num, Nat.dvd_of_factorization_pos (by omega), hn0⟩
  have hs {p : ℕ} (hp : p ∈ n.primeFactors) (hp2 : p ≠ 2) (hp11 : p ≠ 11) :
      n.factorization p = 1 := by
    have hpr := (Nat.mem_primeFactors.mp hp).1
    have hpos := hpr.factorization_pos_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hp)
    by_contra hne
    exact hp11 ((hu p).mp ⟨hpr,hp2,(hpr.pow_dvd_iff_le_factorization hn0).mpr (by omega)⟩)
  let P := (n.primeFactors.erase 2).filter (fun p => ¬ p ∈ ({11} : Finset ℕ))
  obtain ⟨hP,E⟩ := kernel_balance_one hn h11pf (by decide) (fun p hp h2 h11 => hs hp h2 h11)
  change ∀ p ∈ P, p.Prime ∧ p ≠ 2 at hP
  change (2^n.factorization 2+1)*(1+11^n.factorization 11)*(∏ p ∈ P, (p+1)) =
    2^(n.factorization 2+1)*11^n.factorization 11*(∏ p ∈ P, p) at E
  rw [Nat.factorization_def n Nat.prime_two] at E
  have pf {p : ℕ} (h : p ∈ P) : p ∈ n.primeFactors :=
    Finset.mem_of_mem_erase (Finset.mem_filter.mp h).1
  have ne11 {p : ℕ} (h : p ∈ P) : p ≠ 11 := fun e =>
    (Finset.mem_filter.mp h).2 (Finset.mem_singleton.mpr e)
  have h11 : 11 ∉ P := fun h => ne11 h rfl
  have h13 : 13 ∉ P := fun h => hn13 (Nat.dvd_of_mem_primeFactors (pf h))
  have h7 : 7 ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨by decide,
    Nat.mem_primeFactors.mpr ⟨by decide,hn7,hn0⟩⟩,by decide⟩
  have h43 := force43 hP h11 h13 he6 hlarge he hm E
  have hn43 := Nat.dvd_of_mem_primeFactors (pf h43)
  obtain ⟨p,hp,hp7⟩ := simple_donor (by decide : Nat.Prime 7) (by decide) h7 hm he E
  obtain ⟨t,ht,ht43⟩ := simple_donor (by decide : Nat.Prime 43) (by decide) h43 hm he E
  have hd7 := two_mul_dvd_of_odd (hP p hp).1 (hP p hp).2 (by decide : 7 % 2 = 1) hp7
  have hd43 := two_mul_dvd_of_odd (hP t ht).1 (hP t ht).2 (by decide : 43 % 2 = 1) ht43
  have ep := hs (pf hp) (hP p hp).2 (ne11 hp)
  have et := hs (pf ht) (hP t ht).2 (ne11 ht)
  by_cases hsame : p=t
  · subst t
    have hd : 602 ∣ p+1 := (show Nat.Coprime 14 43 by decide).mul_dvd_of_dvd_of_dvd hd7 ht43
    have hh := Nat.le_of_dvd (by omega : 0 < p+1) hd
    exact (hA n hn hu he6 he hm h20 h28 hn7 hn13 hn43 ⟨p,pf hp,ep,by omega,hd⟩).trans
      ((le_max_left A B).trans (le_max_right 20 _))
  · have hK := prime_dvd_prime_pow (e := n.factorization 11) (z := 11) (by decide)
    obtain ⟨s1,s2,s3,s4,_,s6,_,_⟩ := facts hP hK E
    have h5seed := five_dvd_two_pow_add_one hm
    have h5 := s2 5 (by decide) (by decide) (by decide) h5seed
    have nod3 {x : ℕ} (hx : x ∈ P) (hx5 : x ≠ 5) : ¬ 3 ∣ x+1 :=
      fun hd => hx5 (s3 3 (by decide) (by decide) (by decide) x hx 5 h5 hd (by decide))
    have nod5 {x : ℕ} (hx : x ∈ P) : ¬ 5 ∣ x+1 :=
      s4 5 (by decide) (by decide) (by decide) h5seed x hx
    have nod13 {x : ℕ} (hx : x ∈ P) : ¬ 13 ∣ x+1 :=
      fun hd => h13 (s1 13 (by decide) (by decide) (by decide) x hx hd)
    have ht7 : ¬ 7 ∣ t+1 := fun hd => hsame
      (s3 7 (by decide) (by decide) (by decide) p hp t ht hp7 hd)
    have hpl : 223 ≤ p := by
      obtain ⟨k,hk⟩ := hd7
      by_contra! hlt
      have small : k < 16 := by omega
      have cert : ∀ i : Fin 16, let v := 14*(i:ℕ)-1; v.Prime → v ≠ 13 →
          ¬ 3 ∣ v+1 → ¬ 5 ∣ v+1 → ¬ 13 ∣ v+1 → ¬ 49 ∣ v+1 → False := by decide
      have hpk : 14*k-1=p := by omega
      have hbad := cert ⟨k,small⟩
      change Nat.Prime (14*k-1) → _ at hbad
      simp only [hpk] at hbad
      exact hbad (hP p hp).1 (fun heq => h13 (heq ▸ hp))
        (nod3 hp (by omega)) (nod5 hp) (nod13 hp) (s6 7 (by decide) (by decide) (by decide) p hp)
    have htl : 3181 ≤ t := by
      obtain ⟨k,hk⟩ := hd43
      by_contra! hlt
      have small : k < 37 := by omega
      have cert : ∀ i : Fin 37, let v := 86*(i:ℕ)-1; v.Prime →
          ¬ 3 ∣ v+1 → ¬ 5 ∣ v+1 → ¬ 7 ∣ v+1 → ¬ 13 ∣ v+1 → False := by
        intro i
        fin_cases i <;> norm_num
      have htk : 86*k-1=t := by omega
      have hbad := cert ⟨k,small⟩
      change Nat.Prime (86*k-1) → _ at hbad
      simp only [htk] at hbad
      exact hbad (hP t ht).1 (nod3 ht (by omega)) (nod5 ht) ht7 (nod13 ht)
    exact (hB n hn hu he6 he hm h20 h28 hn7 hn13 hn43
      ⟨p,pf hp,t,pf ht,hsame,ep,et,hpl,htl,hp7,ht43,ht7⟩).trans
      ((le_max_right A B).trans (le_max_right 20 _))

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H2_R1_H2_R2
