import FormalConjectures.ErdosProblems.«373»

-- Problem: Erdős Problem 373 — of lower bound
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/373.lean:71 (declaration Erdos373.erdos_373.variants.of_lower_bound)
-- Credit: @OrangeHeadz (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
Sketch.  Let `n ! = a₁ ! * ∏ a ∈ r, a !` with `a₁ + 2 ≤ n`, all `a ∈ r` between `2` and `a₁`, and
`L = log₂ n` large.  Write `v a` for the 2-adic valuation of `a !`, `t = n - a₁`, `D = a₁ + 1`,
`N = ∏ a ∈ r, a !` and `E = ∑ a ∈ r, v a`.

* Legendre: `v a + (binary digit sum of a) = a`, hence `E = v n - v a₁ ≤ t + L`.
* Bertrand: a prime in `(n/2, n]` must be at most `a₁`, so `2 ^ L ≤ 2 * D`.
* Size: `D ^ t ≤ N`.
* The largest prime factor `P` of `n (n - 1)` divides `N`, so `P ≤ A` for some `A ∈ r`.

If some `a ∈ r` is at least `2 (L + 1) ^ 2`, then `a ! * D ^ (L + 1) ≤ D ^ v a` while every other
`b ∈ r` has `b ! ≤ D ^ v b`; so `N * D ^ (L + 1) ≤ D ^ E ≤ D ^ (t + L)`, contradicting `D ^ t ≤ N`.
Otherwise all `a ∈ r` are below `Q = 2 (L + 1) ^ 2`, so `N ≤ Q ^ (2 E)`; as `Q ^ 4 ≤ D` this gives
`t ≤ L`, hence `A ≤ v A + log₂ A + 1 ≤ 2 L + log₂ A + 1 < 11 L / 4`, contradicting
`4 log n < P ≤ A`.
-/

namespace OMA373

open Nat

/-- The 2-adic valuation of `a !`. -/
def v (a : ℕ) : ℕ := padicValNat 2 a.factorial

lemma v_add_digits (a : ℕ) : v a + (Nat.digits 2 a).sum = a := by
  have h : (2 - 1) * padicValNat 2 a.factorial = a - (Nat.digits 2 a).sum :=
    sub_one_mul_padicValNat_factorial a
  have h2 := Nat.digit_sum_le 2 a
  rw [show 2 - 1 = 1 from rfl, one_mul] at h
  unfold v
  omega

lemma digits_sum_le_log (a : ℕ) : (Nat.digits 2 a).sum ≤ Nat.log 2 a + 1 := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  · rw [← Nat.length_digits 2 a (by norm_num) ha.ne']
    have h := List.sum_le_card_nsmul (Nat.digits 2 a) 1 (fun d hd => by
      have := Nat.digits_lt_base (by norm_num : 1 < 2) hd
      omega)
    simpa using h

lemma le_v_add_log (a : ℕ) : a ≤ v a + Nat.log 2 a + 1 := by
  have h1 := v_add_digits a
  have h2 := digits_sum_le_log a
  omega

lemma v_lt {a : ℕ} (ha : a ≠ 0) : v a < a := by
  have h : (2 - 1) * padicValNat 2 a.factorial < a :=
    sub_one_mul_padicValNat_factorial_lt_of_ne_zero (p := 2) (n := a) ha
  rw [show 2 - 1 = 1 from rfl, one_mul] at h
  exact h

lemma half_le_v (a : ℕ) : a / 2 ≤ v a := by
  unfold v
  rw [padicValNat_factorial (p := 2) (b := Nat.log 2 a + 2) (by omega)]
  have h1 : (1 : ℕ) ∈ Finset.Ico 1 (Nat.log 2 a + 2) := by
    rw [Finset.mem_Ico]; omega
  have h2 := Finset.single_le_sum (f := fun i => a / 2 ^ i) (fun _ _ => Nat.zero_le _) h1
  simpa using h2

lemma le_two_v (a : ℕ) : a ≤ 2 * v a + 1 := by
  have := half_le_v a
  omega

/- Size bounds for factorials. -/

lemma succ_factorial_le_pow (a : ℕ) : (a + 1).factorial ≤ (a + 1) ^ a := by
  induction a with
  | zero => simp
  | succ a ih =>
    calc (a + 1 + 1).factorial = (a + 2) * (a + 1).factorial := Nat.factorial_succ (a + 1)
      _ ≤ (a + 2) * (a + 1) ^ a := Nat.mul_le_mul_left _ ih
      _ ≤ (a + 2) * (a + 2) ^ a := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) a)
      _ = (a + 1 + 1) ^ (a + 1) := by ring

lemma factorial_le_pow_two_v {a : ℕ} (ha : 1 ≤ a) : a.factorial ≤ a ^ (2 * v a) := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  have h := le_two_v (b + 1)
  exact (succ_factorial_le_pow b).trans (Nat.pow_le_pow_right (by omega) (by omega))

lemma bern (m : ℕ) : ∀ k : ℕ, m ^ k * (m + k) ≤ (m + 1) ^ k * m := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    calc m ^ (k + 1) * (m + (k + 1)) ≤ (m + 1) * (m ^ k * (m + k)) := by
          have e1 : m ^ (k + 1) * (m + (k + 1)) = m ^ k * (m * m + m * k + m) := by ring
          have e2 : (m + 1) * (m ^ k * (m + k)) = m ^ k * (m * m + m * k + m + k) := by ring
          rw [e1, e2]
          exact Nat.mul_le_mul_left _ (by omega)
      _ ≤ (m + 1) * ((m + 1) ^ k * m) := Nat.mul_le_mul_left _ ih
      _ = (m + 1) ^ (k + 1) * m := by ring

lemma two_mul_pow_le (m : ℕ) (hm : 0 < m) : 2 * m ^ m ≤ (m + 1) ^ m := by
  have h := bern m m
  have h' : m * (2 * m ^ m) ≤ m * (m + 1) ^ m := by
    calc m * (2 * m ^ m) = m ^ m * (m + m) := by ring
      _ ≤ (m + 1) ^ m * m := h
      _ = m * (m + 1) ^ m := by ring
  exact Nat.le_of_mul_le_mul_left h' hm

lemma two_pow_mul_factorial_le (a : ℕ) : 2 ^ a * a.factorial ≤ (a + 1) ^ a := by
  induction a with
  | zero => simp
  | succ a ih =>
    calc 2 ^ (a + 1) * (a + 1).factorial = 2 * (a + 1) * (2 ^ a * a.factorial) := by
          rw [Nat.factorial_succ]; ring
      _ ≤ 2 * (a + 1) * (a + 1) ^ a := Nat.mul_le_mul_left _ ih
      _ = 2 * (a + 1) ^ (a + 1) := by ring
      _ ≤ (a + 1 + 1) ^ (a + 1) := two_mul_pow_le (a + 1) (by omega)

lemma two_sq_le_two_pow : ∀ j : ℕ, 7 ≤ j → 2 * (j + 1) ^ 2 ≤ 2 ^ j := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ j hj ih =>
    have h1 : 2 * (j + 1 + 1) ^ 2 ≤ 2 * (2 * (j + 1) ^ 2) := by nlinarith
    calc 2 * (j + 1 + 1) ^ 2 ≤ 2 * (2 * (j + 1) ^ 2) := h1
      _ ≤ 2 * 2 ^ j := Nat.mul_le_mul_left _ ih
      _ = 2 ^ (j + 1) := by ring

lemma two_log_sq_le {a : ℕ} (ha : 128 ≤ a) : 2 * (Nat.log 2 a + 1) ^ 2 ≤ a := by
  have h7 : 7 ≤ Nat.log 2 a := Nat.le_log_of_pow_le (by norm_num) (by norm_num; exact ha)
  exact (two_sq_le_two_pow _ h7).trans (Nat.pow_log_le_self 2 (by omega))

/-- Every factorial up to `D - 1` is at most `D ^ v a`, once `D` is large. -/
lemma fine_bound {D a : ℕ} (hD : 2 ^ 14 ≤ D) (ha : 1 ≤ a) (haD : a + 1 ≤ D) :
    a.factorial ≤ D ^ v a := by
  by_cases h : a * a ≤ D
  · calc a.factorial ≤ a ^ (2 * v a) := factorial_le_pow_two_v ha
      _ = (a * a) ^ v a := by rw [pow_mul, sq]
      _ ≤ D ^ v a := Nat.pow_le_pow_left h _
  · have hDlt : D < a * a := Nat.lt_of_not_le h
    have ha128 : 128 ≤ a := by
      by_contra hlt
      have h127 : a ≤ 127 := by omega
      have : a * a ≤ 127 * 127 := Nat.mul_le_mul h127 h127
      norm_num at hD
      omega
    have hDpos : 0 < D := by
      have : 0 < 2 ^ 14 := by norm_num
      omega
    obtain ⟨s, hs⟩ : ∃ s, s = (Nat.digits 2 a).sum := ⟨_, rfl⟩
    have hvs : v a + s = a := by rw [hs]; exact v_add_digits a
    have hsk : s ≤ Nat.log 2 a + 1 := by rw [hs]; exact digits_sum_le_log a
    have halt : a < 2 ^ (Nat.log 2 a + 1) := Nat.lt_pow_succ_log_self (by norm_num) a
    have hkk : (Nat.log 2 a + 1) * (2 * s) ≤ a := by
      calc (Nat.log 2 a + 1) * (2 * s) ≤ (Nat.log 2 a + 1) * (2 * (Nat.log 2 a + 1)) :=
            Nat.mul_le_mul_left _ (by omega)
        _ = 2 * (Nat.log 2 a + 1) ^ 2 := by ring
        _ ≤ a := two_log_sq_le ha128
    have h1 : D ^ s ≤ 2 ^ a := by
      calc D ^ s ≤ (a * a) ^ s := Nat.pow_le_pow_left hDlt.le _
        _ = a ^ (2 * s) := by rw [pow_mul, sq]
        _ ≤ (2 ^ (Nat.log 2 a + 1)) ^ (2 * s) := Nat.pow_le_pow_left halt.le _
        _ = 2 ^ ((Nat.log 2 a + 1) * (2 * s)) := by rw [← pow_mul]
        _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) hkk
    have h2 : D ^ s * a.factorial ≤ D ^ s * D ^ v a := by
      calc D ^ s * a.factorial ≤ 2 ^ a * a.factorial := Nat.mul_le_mul_right _ h1
        _ ≤ (a + 1) ^ a := two_pow_mul_factorial_le a
        _ ≤ D ^ a := Nat.pow_le_pow_left haD _
        _ = D ^ s * D ^ v a := by rw [← pow_add]; congr 1; omega
    exact Nat.le_of_mul_le_mul_left h2 (Nat.pow_pos hDpos)

/-- A factorial of size at least `2 (L + 1) ^ 2` has room to spare. -/
lemma fine_special {D a L : ℕ} (hDpos : 0 < D) (hDu : D ≤ 2 ^ (L + 1)) (haD : a + 1 ≤ D)
    (ha : 2 * (L + 1) ^ 2 ≤ a) (hlog : Nat.log 2 a ≤ L) :
    a.factorial * D ^ (L + 1) ≤ D ^ v a := by
  obtain ⟨s, hs⟩ : ∃ s, s = (Nat.digits 2 a).sum := ⟨_, rfl⟩
  have hvs : v a + s = a := by rw [hs]; exact v_add_digits a
  have hsk : s ≤ Nat.log 2 a + 1 := by rw [hs]; exact digits_sum_le_log a
  have hexp : (L + 1) * (s + (L + 1)) ≤ a := by
    calc (L + 1) * (s + (L + 1)) ≤ (L + 1) * ((L + 1) + (L + 1)) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = 2 * (L + 1) ^ 2 := by ring
      _ ≤ a := ha
  have h1 : D ^ (s + (L + 1)) ≤ 2 ^ a := by
    calc D ^ (s + (L + 1)) ≤ (2 ^ (L + 1)) ^ (s + (L + 1)) := Nat.pow_le_pow_left hDu _
      _ = 2 ^ ((L + 1) * (s + (L + 1))) := by rw [← pow_mul]
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) hexp
  have h2 : D ^ s * (a.factorial * D ^ (L + 1)) ≤ D ^ s * D ^ v a := by
    calc D ^ s * (a.factorial * D ^ (L + 1)) = D ^ (s + (L + 1)) * a.factorial := by
          rw [pow_add]; ring
      _ ≤ 2 ^ a * a.factorial := Nat.mul_le_mul_right _ h1
      _ ≤ (a + 1) ^ a := two_pow_mul_factorial_le a
      _ ≤ D ^ a := Nat.pow_le_pow_left haD _
      _ = D ^ s * D ^ v a := by rw [← pow_add]; congr 1; omega
  exact Nat.le_of_mul_le_mul_left h2 (Nat.pow_pos hDpos)

/- Lists of factorials. -/

lemma prod_factorial_pos (r : List ℕ) : 0 < (r.map Nat.factorial).prod := by
  induction r with
  | nil => simp
  | cons a r ih =>
    simp only [List.map_cons, List.prod_cons]
    exact Nat.mul_pos (Nat.factorial_pos a) ih

lemma padic_prod (r : List ℕ) :
    padicValNat 2 (r.map Nat.factorial).prod = (r.map v).sum := by
  induction r with
  | nil => simp
  | cons a r ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    rw [padicValNat.mul (Nat.factorial_ne_zero a) (prod_factorial_pos r).ne', ih]
    rfl

lemma v_le_sum {r : List ℕ} {a : ℕ} (ha : a ∈ r) : v a ≤ (r.map v).sum := by
  induction r with
  | nil => simp at ha
  | cons b r ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 ha with rfl | h
    · omega
    · have := ih h
      omega

lemma coarse_prod {Q : ℕ} (r : List ℕ) (h : ∀ a ∈ r, 1 ≤ a ∧ a ≤ Q) :
    (r.map Nat.factorial).prod ≤ Q ^ (2 * (r.map v).sum) := by
  induction r with
  | nil => simp
  | cons a r ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    have ha := h a (List.mem_cons_self ..)
    have h1 : a.factorial ≤ Q ^ (2 * v a) :=
      (factorial_le_pow_two_v ha.1).trans (Nat.pow_le_pow_left ha.2 _)
    have h2 := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    calc a.factorial * (r.map Nat.factorial).prod
        ≤ Q ^ (2 * v a) * Q ^ (2 * (r.map v).sum) := Nat.mul_le_mul h1 h2
      _ = Q ^ (2 * (v a + (r.map v).sum)) := by rw [← pow_add]; congr 1; ring

lemma fine_prod {D : ℕ} (r : List ℕ) (h : ∀ a ∈ r, a.factorial ≤ D ^ v a) :
    (r.map Nat.factorial).prod ≤ D ^ (r.map v).sum := by
  induction r with
  | nil => simp
  | cons a r ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    have h1 := h a (List.mem_cons_self ..)
    have h2 := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    calc a.factorial * (r.map Nat.factorial).prod ≤ D ^ v a * D ^ (r.map v).sum :=
          Nat.mul_le_mul h1 h2
      _ = D ^ (v a + (r.map v).sum) := by rw [← pow_add]

lemma fine_prod_special {D K : ℕ} (r : List ℕ) (h : ∀ a ∈ r, a.factorial ≤ D ^ v a)
    {b : ℕ} (hb : b ∈ r) (hbK : b.factorial * K ≤ D ^ v b) :
    (r.map Nat.factorial).prod * K ≤ D ^ (r.map v).sum := by
  induction r with
  | nil => simp at hb
  | cons a r ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    have hrest : ∀ c ∈ r, c.factorial ≤ D ^ v c := fun c hc => h c (List.mem_cons_of_mem _ hc)
    rcases List.mem_cons.1 hb with rfl | hbr
    · calc b.factorial * (r.map Nat.factorial).prod * K
          = b.factorial * K * (r.map Nat.factorial).prod := by ring
        _ ≤ D ^ v b * D ^ (r.map v).sum := Nat.mul_le_mul hbK (fine_prod r hrest)
        _ = D ^ (v b + (r.map v).sum) := by rw [← pow_add]
    · calc a.factorial * (r.map Nat.factorial).prod * K
          = a.factorial * ((r.map Nat.factorial).prod * K) := by ring
        _ ≤ D ^ v a * D ^ (r.map v).sum :=
            Nat.mul_le_mul (h a (List.mem_cons_self ..)) (ih hrest hbr)
        _ = D ^ (v a + (r.map v).sum) := by rw [← pow_add]

lemma prime_le_of_dvd_prod {p : ℕ} (hp : p.Prime) {r : List ℕ}
    (h : p ∣ (r.map Nat.factorial).prod) : ∃ a ∈ r, p ≤ a := by
  obtain ⟨x, hx, hpx⟩ := (Prime.dvd_prod_iff hp.prime).1 h
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
  exact ⟨a, ha, (Nat.Prime.dvd_factorial hp).1 hpx⟩

/- A polynomial versus an exponential. -/

lemma poly_le_exp {L : ℕ} (hL : 100 ≤ L) : (2 * (L + 1) ^ 2) ^ 4 ≤ 2 ^ (L - 1) := by
  obtain ⟨m, hm⟩ : ∃ m, m = (L + 1) / 16 + 1 := ⟨_, rfl⟩
  have h1 : L + 1 ≤ 16 * m := by omega
  have h2 : m < 2 ^ m := Nat.lt_two_pow_self
  have h3 : 36 + 8 * m ≤ L - 1 := by omega
  calc (2 * (L + 1) ^ 2) ^ 4 = 16 * (L + 1) ^ 8 := by ring
    _ ≤ 16 * (16 * m) ^ 8 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 _)
    _ = 2 ^ 36 * m ^ 8 := by ring
    _ ≤ 2 ^ 36 * (2 ^ m) ^ 8 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2.le _)
    _ = 2 ^ (36 + 8 * m) := by rw [← pow_mul, ← pow_add]; congr 1; ring
    _ ≤ 2 ^ (L - 1) := Nat.pow_le_pow_right (by norm_num) h3

/- The main step: no solution with `n` large. -/

lemma no_solution {n : ℕ} (hL : 100 ≤ Nat.log 2 n)
    (hP : 11 * Nat.log 2 n < 4 * (n * (n - 1)).maxPrimeFac)
    {a₁ : ℕ} {r : List ℕ} (ha₁ : a₁ + 2 ≤ n) (hr : ∀ a ∈ r, 2 ≤ a ∧ a ≤ a₁)
    (heq : n.factorial = a₁.factorial * (r.map Nat.factorial).prod) : False := by
  obtain ⟨L, hLdef⟩ : ∃ L, L = Nat.log 2 n := ⟨_, rfl⟩
  rw [← hLdef] at hL hP
  have hn0 : n ≠ 0 := by omega
  have hnlow : 2 ^ L ≤ n := by rw [hLdef]; exact Nat.pow_log_le_self 2 hn0
  have hnup : n < 2 ^ (L + 1) := by rw [hLdef]; exact Nat.lt_pow_succ_log_self (by norm_num) n
  obtain ⟨N, hN⟩ : ∃ N, N = (r.map Nat.factorial).prod := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E, E = (r.map v).sum := ⟨_, rfl⟩
  rw [← hN] at heq
  have hNpos : 0 < N := by rw [hN]; exact prod_factorial_pos r
  -- Bertrand: `n ≤ 2 * a₁`
  have hbert : n ≤ 2 * a₁ := by
    obtain ⟨p, hp, hp1, hp2⟩ := Nat.exists_prime_lt_and_le_two_mul (n / 2) (by omega)
    have hpn : p ∣ n.factorial := (Nat.Prime.dvd_factorial hp).2 (by omega)
    rw [heq] at hpn
    rcases (Nat.Prime.dvd_mul hp).1 hpn with h | h
    · have := (Nat.Prime.dvd_factorial hp).1 h
      omega
    · rw [hN] at h
      obtain ⟨a, ha, hpa⟩ := prime_le_of_dvd_prod hp h
      have := (hr a ha).2
      omega
  -- the 2-adic count
  have hEle : E + a₁ ≤ n + L := by
    have h1 : v n = v a₁ + E := by
      unfold v
      rw [heq, padicValNat.mul (Nat.factorial_ne_zero a₁) hNpos.ne', hN, padic_prod, hE]
    have h2 := v_lt hn0
    have h3 := le_v_add_log a₁
    have h4 : Nat.log 2 a₁ ≤ L := by rw [hLdef]; exact Nat.log_mono_right (by omega)
    omega
  -- the size bound
  have hsize : (a₁ + 1) ^ (n - a₁) ≤ N := by
    have h1 : a₁.factorial * (a₁ + 1) ^ (n - a₁) ≤ (a₁ + (n - a₁)).factorial :=
      Nat.factorial_mul_pow_le_factorial
    rw [show a₁ + (n - a₁) = n by omega, heq] at h1
    exact Nat.le_of_mul_le_mul_left h1 (Nat.factorial_pos a₁)
  -- the large prime
  obtain ⟨A, hAr, hPA⟩ : ∃ A ∈ r, (n * (n - 1)).maxPrimeFac ≤ A := by
    have h1 : 1 < n * (n - 1) := by
      have : 2 * 1 ≤ n * (n - 1) := Nat.mul_le_mul (by omega) (by omega)
      omega
    have hprime : Nat.Prime (n * (n - 1)).maxPrimeFac :=
      Nat.prime_maxPrimeFac_of_one_lt _ h1
    have hdvd1 : (n * (n - 1)).maxPrimeFac ∣ n * (n - 1) := Nat.maxPrimeFac_dvd
    have hdvd2 : n * (n - 1) ∣ N := by
      obtain ⟨c, hc⟩ := Nat.factorial_dvd_factorial (show a₁ ≤ n - 2 by omega)
      have h3 : n.factorial = n * (n - 1) * (n - 2).factorial := by
        obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
        rw [Nat.factorial_succ, Nat.factorial_succ]
        simp
        ring
      have h4 : a₁.factorial * N = a₁.factorial * (n * (n - 1) * c) := by
        rw [← heq, h3, hc]; ring
      exact ⟨c, Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos a₁) h4⟩
    rw [hN] at hdvd2
    exact prime_le_of_dvd_prod hprime (hdvd1.trans hdvd2)
  have hDlow : 2 ^ (L - 1) ≤ a₁ + 1 := by
    have h1 : 2 ^ L = 2 * 2 ^ (L - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega
  by_cases hbig : ∃ a ∈ r, 2 * (L + 1) ^ 2 ≤ a
  · -- a very large factorial among the `a ∈ r`
    obtain ⟨b, hbr, hb⟩ := hbig
    have hD14 : 2 ^ 14 ≤ a₁ + 1 := by
      have : 2 ^ 14 ≤ 2 ^ (L - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hfine : ∀ a ∈ r, a.factorial ≤ (a₁ + 1) ^ v a := fun a ha =>
      fine_bound hD14 (by have := (hr a ha).1; omega) (by have := (hr a ha).2; omega)
    have hblog : Nat.log 2 b ≤ L := by
      rw [hLdef]
      exact Nat.log_mono_right (by have := (hr b hbr).2; omega)
    have hspecial : b.factorial * (a₁ + 1) ^ (L + 1) ≤ (a₁ + 1) ^ v b :=
      fine_special (by omega) (by omega) (by have := (hr b hbr).2; omega) hb hblog
    have h1 := fine_prod_special r hfine hbr hspecial
    rw [← hN, ← hE] at h1
    have h2 : (a₁ + 1) ^ (n - a₁) * (a₁ + 1) ^ (L + 1) ≤ (a₁ + 1) ^ E :=
      (Nat.mul_le_mul_right _ hsize).trans h1
    rw [← pow_add] at h2
    have h3 : n - a₁ + (L + 1) ≤ E := (Nat.pow_le_pow_iff_right (by omega)).1 h2
    omega
  · -- all `a ∈ r` are small
    have hsmall : ∀ a ∈ r, a < 2 * (L + 1) ^ 2 := by
      intro a ha
      by_contra hcon
      exact hbig ⟨a, ha, Nat.le_of_not_lt hcon⟩
    obtain ⟨Q, hQ⟩ : ∃ Q, Q = 2 * (L + 1) ^ 2 := ⟨_, rfl⟩
    rw [← hQ] at hsmall
    have hQ4 : Q ^ 4 ≤ 2 ^ (L - 1) := by rw [hQ]; exact poly_le_exp hL
    have hQ2 : 1 < Q := by
      rw [hQ]
      have : 1 ≤ (L + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      omega
    have hcoarse : N ≤ Q ^ (2 * E) := by
      rw [hN, hE]
      exact coarse_prod r fun a ha =>
        ⟨by have := (hr a ha).1; omega, (hsmall a ha).le⟩
    have h1 : (Q ^ 4) ^ (n - a₁) ≤ Q ^ (2 * E) :=
      (Nat.pow_le_pow_left (hQ4.trans hDlow) _).trans (hsize.trans hcoarse)
    rw [← pow_mul] at h1
    have h2 : 4 * (n - a₁) ≤ 2 * E := (Nat.pow_le_pow_iff_right hQ2).1 h1
    -- `A` is small as well
    have hAQ := hsmall A hAr
    have hAlog : 4 * Nat.log 2 A < L := by
      have hA0 : A ≠ 0 := by have := (hr A hAr).1; omega
      have h3 : 2 ^ Nat.log 2 A ≤ A := Nat.pow_log_le_self 2 hA0
      have h4 : (2 ^ Nat.log 2 A) ^ 4 < 2 ^ (L - 1) :=
        lt_of_lt_of_le (Nat.pow_lt_pow_left (lt_of_le_of_lt h3 hAQ) (by norm_num)) hQ4
      rw [← pow_mul] at h4
      have h5 : Nat.log 2 A * 4 < L - 1 := (Nat.pow_lt_pow_iff_right (by norm_num)).1 h4
      omega
    have hA1 := le_v_add_log A
    have hA2 : v A ≤ E := by rw [hE]; exact v_le_sum hAr
    omega

/- Finiteness. -/

lemma finite_lists (b : ℕ) : ∀ m : ℕ, {l : List ℕ | l.length ≤ m ∧ ∀ a ∈ l, a < b}.Finite := by
  intro m
  induction m with
  | zero =>
    refine (Set.finite_singleton ([] : List ℕ)).subset ?_
    rintro l ⟨hl, -⟩
    simpa using hl
  | succ m ih =>
    refine ((Set.finite_singleton ([] : List ℕ)).union
        ((Set.finite_lt_nat b).image2 List.cons ih)).subset ?_
    rintro l ⟨hl, hlb⟩
    cases l with
    | nil => exact Or.inl rfl
    | cons a l =>
      refine Or.inr ⟨a, hlb a (List.mem_cons_self ..), l, ⟨?_, ?_⟩, rfl⟩
      · simp only [List.length_cons] at hl
        omega
      · exact fun c hc => hlb c (List.mem_cons_of_mem _ hc)

end OMA373

theorem OMA.solution : type_of% @Erdos373.erdos_373.variants.of_lower_bound := by
  intro H
  obtain ⟨n₁, hn₁⟩ := Filter.eventually_atTop.1 H
  obtain ⟨n₀, hn₀⟩ : ∃ n₀, n₀ = max n₁ (2 ^ 100) := ⟨_, rfl⟩
  have key : ∀ n : ℕ, ∀ l : List ℕ, (n, l) ∈ Erdos373.S → n < n₀ := by
    intro n l hS
    by_contra hge
    have hn : n₀ ≤ n := Nat.le_of_not_lt hge
    have hn1 : n₁ ≤ n := le_trans (le_max_left _ _) (hn₀ ▸ hn)
    have hn2 : 2 ^ 100 ≤ n := le_trans (le_max_right _ _) (hn₀ ▸ hn)
    obtain ⟨hfac, hpair, hhead, hall⟩ := hS
    have hL : 100 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) hn2
    have hP : 11 * Nat.log 2 n < 4 * (n * (n - 1)).maxPrimeFac := by
      have h1 := hn₁ n hn1
      have hn0 : n ≠ 0 := by
        have : 0 < 2 ^ 100 := by norm_num
        omega
      have h2 : (2 : ℝ) ^ Nat.log 2 n ≤ n := by
        exact_mod_cast Nat.pow_log_le_self 2 hn0
      have h3 : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log n := by
        have h4 := Real.log_le_log (by positivity) h2
        rwa [Real.log_pow] at h4
      have h5 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
      have h6 : (0 : ℝ) ≤ (Nat.log 2 n : ℝ) := Nat.cast_nonneg _
      have h7 : (11 : ℝ) * (Nat.log 2 n : ℝ) < 4 * ((n * (n - 1)).maxPrimeFac : ℝ) := by
        nlinarith
      exact_mod_cast h7
    cases l with
    | nil =>
      simp only [List.map_nil, List.prod_nil] at hfac
      have hle : n ≤ 1 := Nat.factorial_eq_one.1 hfac
      have : 2 ≤ 2 ^ 100 := by norm_num
      omega
    | cons a₁ r =>
      simp only [List.map_cons, List.prod_cons] at hfac
      rw [List.pairwise_cons] at hpair
      simp only [List.headI_cons] at hhead
      refine OMA373.no_solution hL hP (a₁ := a₁) (r := r) (by omega) ?_ hfac
      intro a ha
      exact ⟨hall a (List.mem_cons_of_mem _ ha), hpair.1 a ha⟩
  refine ((Set.finite_lt_nat n₀).prod (OMA373.finite_lists n₀ n₀.factorial)).subset ?_
  rintro ⟨n, l⟩ hS
  have hlt := key n l hS
  obtain ⟨hfac, hpair, hhead, hall⟩ := hS
  refine ⟨hlt, ?_, ?_⟩
  · have h1 : 2 ^ (l.map Nat.factorial).length ≤ (l.map Nat.factorial).prod := by
      apply List.pow_card_le_prod
      intro x hx
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
      exact Nat.self_le_factorial a |>.trans' (hall a ha)
    rw [List.length_map, ← hfac] at h1
    have h2 : l.length < 2 ^ l.length := Nat.lt_two_pow_self
    have h3 : n.factorial ≤ n₀.factorial := Nat.factorial_le hlt.le
    show l.length ≤ n₀.factorial
    omega
  · intro a ha
    cases l with
    | nil => simp at ha
    | cons a₁ r =>
      rw [List.pairwise_cons] at hpair
      simp only [List.headI_cons] at hhead
      have : a ≤ a₁ := by
        rcases List.mem_cons.1 ha with rfl | h
        · exact le_rfl
        · exact hpair.1 a h
      show a < n₀
      omega
