import FormalConjectures.OEIS.«60841»

/-!
# OEIS A060841, conjecture 1: proof

Problem: Numerator of 1/det(M) for M[i,j] = 1/lcm(i,j)
Upstream: formal-conjectures FormalConjectures/OEIS/60841.lean (declaration OeisA60841.conjecture1)
Credit: @implicitall (agent: Grok Bot)

Proof outline.
* Smith-type determinant: 1/lcm(i,j) = gcd(i,j)/(i j), and gcd(i,j) = sum of phi(d) over common
  divisors d, so M = D (E diag(phi) E^T) D with E unitriangular. Hence det M = (prod phi(k)) / (n!)^2
  and 1/det M is an integer iff prod_{k<=n} phi(k) divides prod_{k<=n} k^2.
* For n < 160 the divisibility is checked by kernel computation.
* For n >= 160 it fails 2-adically: with S = {4} and the odd primes up to 151 (pairwise coprime),
  prod_{m in S} phi(m)^(n/m) divides prod phi(k), and the 2-adic weights give at least
  sum w_m (n/m) >= 2n - 1 > 2 v_2(n!) factors of 2, while (n!)^2 has exactly 2 v_2(n!).
-/

open Finset

namespace OMA60841

def A (n : ℕ) : ℕ := ∏ i ∈ range n, (i + 1) ^ 2
def B (n : ℕ) : ℕ := ∏ i ∈ range n, Nat.totient (i + 1)

theorem B_ne_zero (n : ℕ) : B n ≠ 0 := by
  unfold B
  rw [Finset.prod_ne_zero_iff]
  intro i _
  exact (Nat.totient_pos.2 (Nat.succ_pos i)).ne'

theorem A_eq (n : ℕ) : A n = (n.factorial) ^ 2 := by
  induction n with
  | zero => simp [A]
  | succ k ih =>
    rw [A, Finset.prod_range_succ, ← A, ih, Nat.factorial_succ]
    ring

-- The gcd sum

theorem gcd_sum (n a b : ℕ) (ha : 0 < a) (han : a ≤ n) (_hb : 0 < b) :
    (∑ x ∈ range n, if x + 1 ∣ a ∧ x + 1 ∣ b then Nat.totient (x + 1) else 0) = Nat.gcd a b := by
  set g := Nat.gcd a b with hg
  have gpos : 0 < g := Nat.gcd_pos_of_pos_left b ha
  have gle : g ≤ n := le_trans (Nat.le_of_dvd ha (Nat.gcd_dvd_left a b)) han
  let f : ℕ → ℕ := fun m => if m ∣ g then Nat.totient m else 0
  have h1 : (∑ x ∈ range n, if x + 1 ∣ a ∧ x + 1 ∣ b then Nat.totient (x + 1) else 0)
      = ∑ x ∈ range n, f (x + 1) := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    simp only [f, hg, Nat.dvd_gcd_iff]
  have h2 : ∑ x ∈ range (n + 1), f x = ∑ x ∈ range n, f (x + 1) := by
    rw [Finset.sum_range_succ']
    have : f 0 = 0 := by
      simp only [f, zero_dvd_iff]
      rw [if_neg gpos.ne']
    rw [this, add_zero]
  have h3 : ∑ x ∈ range (g + 1), f x = ∑ x ∈ range (n + 1), f x := by
    apply Finset.sum_subset
    · intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega
    · intro x hx hx'
      simp only [Finset.mem_range] at hx hx'
      simp only [f]
      rw [if_neg]
      intro hd
      have := Nat.le_of_dvd gpos hd
      omega
  have h4 : ∑ x ∈ range (g + 1), f x = g := by
    rw [← Finset.sum_filter]
    exact Nat.sum_totient' g
  rw [h1, ← h2, ← h3, h4]

-- The determinant

theorem det_eq (n : ℕ) : (OeisA60841.lcmMatrix n).det = (B n : ℚ) / (A n : ℚ) := by
  let D : Matrix (Fin n) (Fin n) ℚ := Matrix.diagonal (fun i => 1 / ((i : ℕ) + 1 : ℚ))
  let E : Matrix (Fin n) (Fin n) ℚ :=
    Matrix.of fun i d => if (d : ℕ) + 1 ∣ (i : ℕ) + 1 then (1 : ℚ) else 0
  let Φ : Fin n → ℚ := fun d => (Nat.totient ((d : ℕ) + 1) : ℚ)
  have hM : OeisA60841.lcmMatrix n = D * (E * Matrix.diagonal Φ * E.transpose) * D := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply, E, Φ,
      Matrix.of_apply, OeisA60841.lcmMatrix]
    have key : (∑ x : Fin n, (if (x : ℕ) + 1 ∣ (i : ℕ) + 1 then (1 : ℚ) else 0)
        * (Nat.totient ((x : ℕ) + 1) : ℚ) * (if (x : ℕ) + 1 ∣ (j : ℕ) + 1 then (1 : ℚ) else 0))
        = (Nat.gcd ((i : ℕ) + 1) ((j : ℕ) + 1) : ℚ) := by
      rw [← gcd_sum n ((i : ℕ) + 1) ((j : ℕ) + 1) (Nat.succ_pos _) i.isLt (Nat.succ_pos _)]
      rw [Nat.cast_sum, ← Fin.sum_univ_eq_sum_range
        (fun x => ((if x + 1 ∣ (i : ℕ) + 1 ∧ x + 1 ∣ (j : ℕ) + 1 then Nat.totient (x + 1) else 0 : ℕ) : ℚ))]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      by_cases h1 : (x : ℕ) + 1 ∣ (i : ℕ) + 1 <;> by_cases h2 : (x : ℕ) + 1 ∣ (j : ℕ) + 1 <;>
        simp [h1, h2]
    rw [key]
    have hgl : (Nat.gcd ((i : ℕ) + 1) ((j : ℕ) + 1) : ℚ) * (Nat.lcm ((i : ℕ) + 1) ((j : ℕ) + 1) : ℚ)
        = ((i : ℕ) + 1 : ℚ) * ((j : ℕ) + 1 : ℚ) := by
      exact_mod_cast Nat.gcd_mul_lcm ((i : ℕ) + 1) ((j : ℕ) + 1)
    have hl : (Nat.lcm ((i : ℕ) + 1) ((j : ℕ) + 1) : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.lcm_pos (Nat.succ_pos _) (Nat.succ_pos _)).ne'
    have hi : ((i : ℕ) + 1 : ℚ) ≠ 0 := by positivity
    have hj : ((j : ℕ) + 1 : ℚ) ≠ 0 := by positivity
    field_simp
    linarith [hgl]
  have hE : E.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular]
    · simp [E]
    · intro i j hij
      simp only [E, Matrix.of_apply]
      rw [if_neg]
      intro hd
      have := Nat.le_of_dvd (Nat.succ_pos _) hd
      have hij' : (i : ℕ) < (j : ℕ) := hij
      omega
  rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    hE, Matrix.det_diagonal, Matrix.det_diagonal]
  simp only [Φ, A, B, Nat.cast_prod, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
  rw [Fin.prod_univ_eq_prod_range (fun i => 1 / ((i : ℚ) + 1)),
    Fin.prod_univ_eq_prod_range (fun i => ((Nat.totient (i + 1) : ℕ) : ℚ))]
  have hp : ∏ i ∈ range n, (1 : ℚ) / ((i : ℚ) + 1) = 1 / ∏ i ∈ range n, ((i : ℚ) + 1) := by
    rw [Finset.prod_div_distrib, Finset.prod_const_one]
  have hnz : ∏ i ∈ range n, ((i : ℚ) + 1) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i _
    positivity
  rw [hp, Finset.prod_pow]
  field_simp

theorem den_iff (n : ℕ) : ((OeisA60841.lcmMatrix n).det)⁻¹.den = 1 ↔ B n ∣ A n := by
  rw [det_eq, inv_div]
  exact Rat.den_div_natCast_eq_one_iff (A n) (B n) (B_ne_zero n)


-- Totient and divisibility over pairwise coprime finite sets

theorem totient_prod_coprime (T : Finset ℕ)
    (h : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → Nat.Coprime a b) :
    Nat.totient (∏ m ∈ T, m) = ∏ m ∈ T, Nat.totient m := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hc : Nat.Coprime a (∏ m ∈ s, m) := by
      apply Nat.Coprime.prod_right
      intro b hb
      exact h a (Finset.mem_insert_self a s) b (Finset.mem_insert_of_mem hb)
        (fun hab => ha (hab ▸ hb))
    rw [Nat.totient_mul hc, ih (fun x hx y hy hxy =>
      h x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hxy)]

theorem prod_dvd_coprime (T : Finset ℕ) (k : ℕ)
    (h : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → Nat.Coprime a b) (hk : ∀ m ∈ T, m ∣ k) :
    ∏ m ∈ T, m ∣ k := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hc : Nat.Coprime a (∏ m ∈ s, m) := by
      apply Nat.Coprime.prod_right
      intro b hb
      exact h a (Finset.mem_insert_self a s) b (Finset.mem_insert_of_mem hb)
        (fun hab => ha (hab ▸ hb))
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hc (hk a (Finset.mem_insert_self a s))
      (ih (fun x hx y hy hxy =>
        h x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hxy)
        (fun m hm => hk m (Finset.mem_insert_of_mem hm)))

theorem prod_totient_dvd (S : Finset ℕ)
    (hS : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Nat.Coprime a b) (n : ℕ) :
    ∏ m ∈ S, Nat.totient m ^ (n / m) ∣ B n := by
  have step1 : ∏ m ∈ S, Nat.totient m ^ (n / m)
      = ∏ m ∈ S, ∏ i ∈ range n, (if m ∣ i + 1 then Nat.totient m else 1) := by
    refine Finset.prod_congr rfl (fun m _ => ?_)
    rw [← Finset.prod_filter, Finset.prod_const, Nat.card_multiples]
  have step2 : ∀ i ∈ range n, ∏ m ∈ S, (if m ∣ i + 1 then Nat.totient m else 1)
      ∣ Nat.totient (i + 1) := by
    intro i _
    rw [← Finset.prod_filter]
    rw [← totient_prod_coprime _ (fun a ha b hb hab =>
      hS a (Finset.mem_of_mem_filter a ha) b (Finset.mem_of_mem_filter b hb) hab)]
    apply Nat.totient_dvd_of_dvd
    apply prod_dvd_coprime _ _ (fun a ha b hb hab =>
      hS a (Finset.mem_of_mem_filter a ha) b (Finset.mem_of_mem_filter b hb) hab)
    intro m hm
    exact (Finset.mem_filter.1 hm).2
  rw [step1, Finset.prod_comm]
  exact Finset.prod_dvd_prod_of_dvd _ _ step2

-- The modulus set: 4 and the odd primes up to 151, with 2-adic weights of their totients

def S : Finset ℕ := {4, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
  73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151}

def wt (m : ℕ) : ℕ :=
  if m = 5 ∨ m = 13 ∨ m = 29 ∨ m = 37 ∨ m = 53 ∨ m = 61 ∨ m = 101 ∨ m = 109 ∨ m = 149 then 2
  else if m = 41 ∨ m = 73 ∨ m = 89 ∨ m = 137 then 3
  else if m = 17 ∨ m = 113 then 4
  else if m = 97 then 5
  else 1

theorem S_coprime : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Nat.Coprime a b := by
  decide +kernel

theorem S_wt : ∀ m ∈ S, 2 ^ wt m ∣ Nat.totient m := by
  decide +kernel

theorem S_pos : ∀ m ∈ S, 0 < m := by
  decide +kernel

theorem S_wsum : ∑ m ∈ S, (wt m : ℚ) = 63 := by
  decide +kernel

theorem S_c : (12 : ℚ) / 5 ≤ ∑ m ∈ S, (wt m : ℚ) / m := by
  decide +kernel

theorem two_pow_dvd_B (n : ℕ) : 2 ^ (∑ m ∈ S, wt m * (n / m)) ∣ B n := by
  refine dvd_trans ?_ (prod_totient_dvd S S_coprime n)
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_dvd_prod_of_dvd
  intro m hm
  rw [pow_mul]
  exact pow_dvd_pow_of_dvd (S_wt m hm) _

theorem big_sum (n : ℕ) (hn : 160 ≤ n) : 2 * n ≤ 1 + ∑ m ∈ S, wt m * (n / m) := by
  have key : ∀ m ∈ S, (wt m : ℚ) * (((n : ℚ) + 1) / m - 1) ≤ ((wt m * (n / m) : ℕ) : ℚ) := by
    intro m hm
    have hm0 : (0 : ℚ) < m := by exact_mod_cast S_pos m hm
    have hlt : n < m * (n / m + 1) := Nat.lt_mul_div_succ n (S_pos m hm)
    have hle : ((n : ℚ) + 1) ≤ (m : ℚ) * (((n / m : ℕ) : ℚ) + 1) := by exact_mod_cast hlt
    push_cast
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    rw [div_sub_one hm0.ne', div_le_iff₀ hm0]
    linarith
  have hsum := Finset.sum_le_sum key
  rw [← Nat.cast_sum] at hsum
  have e1 : ∑ m ∈ S, (wt m : ℚ) * (((n : ℚ) + 1) / m - 1)
      = ((n : ℚ) + 1) * ∑ m ∈ S, (wt m : ℚ) / m - ∑ m ∈ S, (wt m : ℚ) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    ring
  rw [e1, S_wsum] at hsum
  have hc := S_c
  have hn' : (160 : ℚ) ≤ n := by exact_mod_cast hn
  have h3 : ((n : ℚ) + 1) * (12 / 5) ≤ ((n : ℚ) + 1) * ∑ m ∈ S, (wt m : ℚ) / m :=
    mul_le_mul_of_nonneg_left hc (by positivity)
  have : (2 * n : ℚ) ≤ 1 + ((∑ m ∈ S, wt m * (n / m) : ℕ) : ℚ) := by linarith
  exact_mod_cast this

theorem large_not_dvd (n : ℕ) (hn : 160 ≤ n) : ¬ B n ∣ A n := by
  intro h
  have h2 := dvd_trans (two_pow_dvd_B n) h
  rw [A_eq] at h2
  have hv : padicValNat 2 n.factorial < n := by
    have hp2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := sub_one_mul_padicValNat_factorial_lt_of_ne_zero 2 (n := n) (by omega)
    simpa using this
  have hf : (n.factorial) ^ 2 ≠ 0 := pow_ne_zero _ (Nat.factorial_ne_zero n)
  have := (@padicValNat_dvd_iff_le 2 ⟨Nat.prime_two⟩ _ _ hf).1 h2
  rw [@padicValNat.pow 2 ⟨Nat.prime_two⟩] at this
  have hb := big_sum n hn
  omega

theorem small_iff : ∀ n < 160, 1 ≤ n → (B n ∣ A n ↔ (n ≤ 34 ∨ n = 36 ∨ n = 38)) := by
  decide +kernel

end OMA60841

theorem OMA.solution : type_of% @OeisA60841.conjecture1 := by
  intro n hn
  rw [OMA60841.den_iff]
  have hmem : n ∈ OeisA60841.integerDetN ↔ (n ≤ 34 ∨ n = 36 ∨ n = 38) := by
    simp only [OeisA60841.integerDetN, Set.mem_union, Set.mem_Icc, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    omega
  rw [hmem]
  by_cases h : n < 160
  · exact OMA60841.small_iff n h hn
  · constructor
    · intro hd
      exact absurd hd (OMA60841.large_not_dvd n (by omega))
    · intro hc
      omega
