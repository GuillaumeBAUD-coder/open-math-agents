import OMAReductions.R_OeisA105751_conjecture_variants_moll_p_mod_4_eq_1_R1

/-!
# Proof of `OeisA105751.conjecture.variants.moll_p_mod_4_eq_1.R1.H1`

For every prime `p ≡ 1 (mod 4)` and every `n : ℕ`, `p ^ ν_p(n!) ∣ OeisA105751.a n`.

Proof outline:
1. Identify `OeisA105751.a n` with the exact integer imaginary part `(seqPair n).2` of
   `∏_{k=0}^n (1 + k * i)`.
2. For `M = padicValNat p n.factorial`, lift a root of `r^2 ≡ -1 (mod p)` via Hensel's lemma
   to an integer `r` with `p^M ∣ r^2 + 1`.
3. Show modulo `p^M` that `(seqPair n).1 ± r * (seqPair n).2 ≡ ∏_{k=0}^n (1 ± k * r)` and
   that `∏_{k=0}^n (1 ± k * r) ≡ (±r)^n * ∏_{k=0}^{n-1} ((k + 1) ∓ r)`.
4. Since `∏_{k=0}^{n-1} (a + k)` is a product of `n` consecutive integers, `n!` (and hence `p^M`)
   divides both products. Subtracting yields `p^M ∣ 2 * r * (seqPair n).2`, and since `p` is an
   odd prime not dividing `r`, `p^M ∣ OeisA105751.a n`.
-/

namespace OMA105751R1H1

open Finset

def seqPair : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 =>
    let p := seqPair n
    (p.1 - ((n + 1 : ℕ) : ℤ) * p.2, p.2 + ((n + 1 : ℕ) : ℤ) * p.1)

lemma prod_complex_eq_seqPair (n : ℕ) :
    ∏ k ∈ range (n + 1), ((1 : ℂ) + (k : ℂ) * Complex.I) =
      ((seqPair n).1 : ℂ) + ((seqPair n).2 : ℂ) * Complex.I := by
  induction n with
  | zero =>
    simp [seqPair]
  | succ n ih =>
    rw [prod_range_succ, ih]
    simp only [seqPair, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
    have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
    linear_combination ((seqPair n).2 : ℂ) * ((n + 1 : ℕ) : ℂ) * hI2

lemma a_eq_seqPair_snd (n : ℕ) : OeisA105751.a n = (seqPair n).2 := by
  unfold OeisA105751.a
  dsimp only
  rw [prod_complex_eq_seqPair]
  simp only [Complex.add_im, Complex.intCast_im, Complex.mul_im, Complex.intCast_re,
    Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add]
  exact Int.floor_intCast _

lemma hensel_sq_add_one {p : ℕ} (hp : p.Prime) (hmod : p % 4 = 1) :
    ∀ M : ℕ, ∃ r : ℤ, ((p : ℤ) ^ M) ∣ (r ^ 2 + 1) := by
  have : Fact p.Prime := ⟨hp⟩
  intro M
  induction M with
  | zero =>
    exact ⟨0, one_dvd _⟩
  | succ M ih =>
    cases M with
    | zero =>
      have hne3 : p % 4 ≠ 3 := by omega
      rcases (ZMod.exists_sq_eq_neg_one_iff (p := p)).2 hne3 with ⟨x, hx⟩
      refine ⟨(x.val : ℤ), ?_⟩
      rw [pow_one, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [ZMod.natCast_zmod_val, sq, ← hx]
      ring
    | succ M =>
      rcases ih with ⟨r, hr⟩
      rcases hr with ⟨t, ht⟩
      have hp_two : 2 ≤ p := hp.two_le
      have hp_dvd_sq : (p : ℤ) ∣ r ^ 2 + 1 := by
        rw [ht, pow_succ']
        exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
      have hr0 : (r : ZMod p) ≠ 0 := by
        intro h0
        have hpr : (p : ℤ) ∣ r := (ZMod.intCast_zmod_eq_zero_iff_dvd r p).1 h0
        have hp1 : (p : ℤ) ∣ 1 := by
          have h1 : (p : ℤ) ∣ (r ^ 2 + 1) - r * r :=
            dvd_sub hp_dvd_sq (dvd_mul_of_dvd_left hpr r)
          simpa [sq] using h1
        have hp1n : p ∣ 1 := Int.ofNat_dvd.1 hp1
        have := Nat.le_of_dvd Nat.zero_lt_one hp1n
        omega
      have h20 : (2 : ZMod p) ≠ 0 := by
        intro h0
        have h0' : ((2 : ℤ) : ZMod p) = 0 := by simpa using h0
        have hp2 : (p : ℤ) ∣ 2 := (ZMod.intCast_zmod_eq_zero_iff_dvd 2 p).1 h0'
        have hp2n : p ∣ 2 := Int.ofNat_dvd.1 hp2
        have := Nat.le_of_dvd (by decide) hp2n
        omega
      have h2r0 : (2 : ZMod p) * (r : ZMod p) ≠ 0 := mul_ne_zero h20 hr0
      let uZ : ZMod p := -((t : ZMod p) * ((2 : ZMod p) * (r : ZMod p))⁻¹)
      let u : ℤ := (uZ.val : ℤ)
      have hu_dvd : (p : ℤ) ∣ t + 2 * r * u := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        dsimp only [u]
        push_cast
        rw [ZMod.natCast_zmod_val]
        dsimp only [uZ]
        have hmul : (2 : ZMod p) * (r : ZMod p) * -((t : ZMod p) * ((2 : ZMod p) * (r : ZMod p))⁻¹) =
            -(t : ZMod p) := by
          rw [mul_neg, mul_comm (t : ZMod p), ← mul_assoc, mul_inv_cancel₀ h2r0, one_mul]
        rw [hmul, add_neg_cancel]
      rcases hu_dvd with ⟨w, hw⟩
      refine ⟨r + u * (p : ℤ) ^ (M + 1), ?_⟩
      refine ⟨w + u ^ 2 * (p : ℤ) ^ M, ?_⟩
      have hcalc : (r + u * (p : ℤ) ^ (M + 1)) ^ 2 + 1 =
          (r ^ 2 + 1) + 2 * r * u * (p : ℤ) ^ (M + 1) +
            u ^ 2 * ((p : ℤ) ^ (M + 1) * (p : ℤ) ^ (M + 1)) := by ring
      rw [hcalc, ht]
      have h1 : (p : ℤ) ^ (M + 1) * t + 2 * r * u * (p : ℤ) ^ (M + 1) =
          (p : ℤ) ^ (M + 1) * (t + 2 * r * u) := by ring
      rw [h1, hw]
      have hp_pow : (p : ℤ) ^ (M + 1 + 1) = (p : ℤ) ^ (M + 1) * (p : ℤ) := pow_succ _ _
      have hp_sq : (p : ℤ) ^ (M + 1) * (p : ℤ) ^ (M + 1) =
          (p : ℤ) ^ (M + 1 + 1) * (p : ℤ) ^ M := by
        rw [hp_pow, pow_succ (p : ℤ) M]
        ring
      rw [hp_sq, hp_pow]
      ring

lemma seqPair_split_mod (n : ℕ) (m r : ℤ) (hr : m ∣ r ^ 2 + 1) :
    m ∣ ((seqPair n).1 + r * (seqPair n).2) - ∏ k ∈ range (n + 1), (1 + (k : ℤ) * r) ∧
    m ∣ ((seqPair n).1 - r * (seqPair n).2) - ∏ k ∈ range (n + 1), (1 - (k : ℤ) * r) := by
  induction n with
  | zero =>
    simp [seqPair]
  | succ n ih =>
    rcases ih with ⟨ih1, ih2⟩
    rw [prod_range_succ (n := n + 1), prod_range_succ (n := n + 1)]
    simp only [seqPair]
    constructor
    · have hident :
          ((seqPair n).1 - ((n + 1 : ℕ) : ℤ) * (seqPair n).2 +
            r * ((seqPair n).2 + ((n + 1 : ℕ) : ℤ) * (seqPair n).1)) -
            (∏ k ∈ range (n + 1), (1 + (k : ℤ) * r)) * (1 + ((n + 1 : ℕ) : ℤ) * r) =
          (((seqPair n).1 + r * (seqPair n).2) - ∏ k ∈ range (n + 1), (1 + (k : ℤ) * r)) *
            (1 + ((n + 1 : ℕ) : ℤ) * r) -
          ((n + 1 : ℕ) : ℤ) * (seqPair n).2 * (r ^ 2 + 1) := by ring
      rw [hident]
      exact dvd_sub (dvd_mul_of_dvd_left ih1 _) (dvd_mul_of_dvd_right hr _)
    · have hident :
          ((seqPair n).1 - ((n + 1 : ℕ) : ℤ) * (seqPair n).2 -
            r * ((seqPair n).2 + ((n + 1 : ℕ) : ℤ) * (seqPair n).1)) -
            (∏ k ∈ range (n + 1), (1 - (k : ℤ) * r)) * (1 - ((n + 1 : ℕ) : ℤ) * r) =
          (((seqPair n).1 - r * (seqPair n).2) - ∏ k ∈ range (n + 1), (1 - (k : ℤ) * r)) *
            (1 - ((n + 1 : ℕ) : ℤ) * r) -
          ((n + 1 : ℕ) : ℤ) * (seqPair n).2 * (r ^ 2 + 1) := by ring
      rw [hident]
      exact dvd_sub (dvd_mul_of_dvd_left ih2 _) (dvd_mul_of_dvd_right hr _)

lemma prod_one_add_mul_mod (n : ℕ) (m r : ℤ) (hr : m ∣ r ^ 2 + 1) :
    m ∣ (∏ k ∈ range (n + 1), (1 + (k : ℤ) * r)) -
      r ^ n * ∏ k ∈ range n, ((k + 1 : ℤ) - r) := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [prod_range_succ (n := n + 1), prod_range_succ (f := fun k => ((k + 1 : ℤ) - r)), pow_succ]
    have hstep :
        (∏ k ∈ range (n + 1), (1 + (k : ℤ) * r)) * (1 + ((n + 1 : ℕ) : ℤ) * r) -
          r ^ n * r * ((∏ k ∈ range n, ((k + 1 : ℤ) - r)) * (((n : ℤ) + 1) - r)) =
        ((∏ k ∈ range (n + 1), (1 + (k : ℤ) * r)) - r ^ n * ∏ k ∈ range n, ((k + 1 : ℤ) - r)) *
          (1 + ((n + 1 : ℕ) : ℤ) * r) +
        (r ^ n * ∏ k ∈ range n, ((k + 1 : ℤ) - r)) * (r ^ 2 + 1) := by
      push_cast
      ring
    rw [hstep]
    exact dvd_add (dvd_mul_of_dvd_left ih _) (dvd_mul_of_dvd_right hr _)

lemma prod_one_sub_mul_mod (n : ℕ) (m r : ℤ) (hr : m ∣ r ^ 2 + 1) :
    m ∣ (∏ k ∈ range (n + 1), (1 - (k : ℤ) * r)) -
      (-r) ^ n * ∏ k ∈ range n, ((k + 1 : ℤ) + r) := by
  have hr' : m ∣ (-r) ^ 2 + 1 := by simpa using hr
  have h := prod_one_add_mul_mod n m (-r) hr'
  simpa [sub_eq_add_neg, mul_neg, neg_neg] using h

lemma nat_factorial_dvd_prod_consec (n a : ℕ) :
    n.factorial ∣ ∏ k ∈ range n, (a + k) := by
  have hprod : ∏ k ∈ range n, (a + k) = (a + n - 1).descFactorial n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [prod_range_succ, ih]
      cases n with
      | zero => simp
      | succ n =>
        have h1 : a + (n + 1) - 1 = a + n := by omega
        have h2 : a + (n + 1 + 1) - 1 = a + n + 1 := by omega
        rw [h1, h2, Nat.succ_descFactorial_succ]
        ring
  rw [hprod, Nat.descFactorial_eq_factorial_mul_choose]
  exact dvd_mul_right _ _

lemma int_factorial_dvd_prod_consec (n : ℕ) (a : ℤ) :
    (n.factorial : ℤ) ∣ ∏ k ∈ range n, (a + (k : ℤ)) := by
  by_cases ha : 0 ≤ a
  · lift a to ℕ using ha
    have hnat : (n.factorial : ℤ) ∣ ((∏ k ∈ range n, (a + k) : ℕ) : ℤ) :=
      Int.ofNat_dvd.2 (nat_factorial_dvd_prod_consec n a)
    simpa [Nat.cast_prod] using hnat
  · have hneg : 0 ≤ -a := by omega
    lift (-a) to ℕ using hneg with b hb
    have ha_eq : a = -(b : ℤ) := by omega
    rw [ha_eq]
    by_cases hbn : b < n
    · have hzero : ∏ k ∈ range n, (-(b : ℤ) + (k : ℤ)) = 0 :=
        prod_eq_zero (mem_range.2 hbn) (by ring)
      rw [hzero]
      exact dvd_zero _
    · have hle : n ≤ b := by omega
      have hshift : ∏ k ∈ range n, (-(b : ℤ) + (k : ℤ)) =
          (-1 : ℤ) ^ n * ∏ k ∈ range n, (((b + 1 - n : ℕ) : ℤ) + (k : ℤ)) := by
        have hneg_prod : ∏ k ∈ range n, (-(b : ℤ) + (k : ℤ)) =
            (-1 : ℤ) ^ n * ∏ k ∈ range n, ((b : ℤ) - (k : ℤ)) := by
          have hcard : (-1 : ℤ) ^ n = ∏ _k ∈ range n, (-1 : ℤ) := by simp
          rw [hcard, ← prod_mul_distrib]
          refine prod_congr rfl fun k _ => ?_
          ring
        rw [hneg_prod]
        congr 1
        rw [← prod_range_reflect (fun k => ((b + 1 - n : ℕ) : ℤ) + (k : ℤ)) n]
        refine prod_congr rfl fun k hk => ?_
        have hklt : k < n := mem_range.1 hk
        omega
      rw [hshift]
      have hnat : (n.factorial : ℤ) ∣ ((∏ k ∈ range n, (b + 1 - n + k) : ℕ) : ℤ) :=
        Int.ofNat_dvd.2 (nat_factorial_dvd_prod_consec n (b + 1 - n))
      refine dvd_mul_of_dvd_right ?_ _
      simpa [Nat.cast_prod] using hnat

lemma prime_pow_dvd_of_dvd_mul_coprime {p : ℕ} (hp : p.Prime) {c y : ℤ}
    (hc : ¬ (p : ℤ) ∣ c) : ∀ M : ℕ, (p : ℤ) ^ M ∣ c * y → (p : ℤ) ^ M ∣ y := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  intro M
  induction M generalizing y with
  | zero =>
    intro _
    exact one_dvd y
  | succ M ih =>
    intro h
    have hpy : (p : ℤ) ∣ y := by
      have hpc : (p : ℤ) ∣ c * y := dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero M)) h
      rcases hpZ.dvd_or_dvd hpc with h1 | h2
      · exact absurd h1 hc
      · exact h2
    rcases hpy with ⟨y', rfl⟩
    rw [pow_succ'] at h
    have h' : (p : ℤ) ^ M ∣ c * y' := by
      have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have hmul : (p : ℤ) * (p : ℤ) ^ M ∣ (p : ℤ) * (c * y') := by
        have heq : c * ((p : ℤ) * y') = (p : ℤ) * (c * y') := by ring
        rwa [heq] at h
      exact (mul_dvd_mul_iff_left hp0).1 hmul
    rw [pow_succ']
    exact mul_dvd_mul_left (p : ℤ) (ih h')

end OMA105751R1H1

open OMA105751R1H1 Finset in
theorem OMA.solution :
    OMA.R_OeisA105751_conjecture_variants_moll_p_mod_4_eq_1_R1.H1 := by
  intro p hp hmod n
  rw [a_eq_seqPair_snd]
  have hp_two : 2 ≤ p := hp.two_le
  set M := padicValNat p n.factorial with hM_def
  rcases hensel_sq_add_one hp hmod M with ⟨r, hr⟩
  have hM_dvd_fact : (p : ℤ) ^ M ∣ (n.factorial : ℤ) := by
    exact_mod_cast (pow_padicValNat_dvd (p := p) (n := n.factorial))
  have hprod_add : (p : ℤ) ^ M ∣ ∏ k ∈ range (n + 1), (1 + (k : ℤ) * r) := by
    have h1 := prod_one_add_mul_mod n ((p : ℤ) ^ M) r hr
    have h2 : (p : ℤ) ^ M ∣ r ^ n * ∏ k ∈ range n, ((k + 1 : ℤ) - r) := by
      have hcon : (n.factorial : ℤ) ∣ ∏ k ∈ range n, ((1 - r) + (k : ℤ)) :=
        int_factorial_dvd_prod_consec n (1 - r)
      have heq : ∏ k ∈ range n, ((k + 1 : ℤ) - r) = ∏ k ∈ range n, ((1 - r) + (k : ℤ)) :=
        prod_congr rfl fun k _ => by ring
      rw [heq]
      exact dvd_mul_of_dvd_right (dvd_trans hM_dvd_fact hcon) _
    have hsum := dvd_add h1 h2
    simpa using hsum
  have hprod_sub : (p : ℤ) ^ M ∣ ∏ k ∈ range (n + 1), (1 - (k : ℤ) * r) := by
    have h1 := prod_one_sub_mul_mod n ((p : ℤ) ^ M) r hr
    have h2 : (p : ℤ) ^ M ∣ (-r) ^ n * ∏ k ∈ range n, ((k + 1 : ℤ) + r) := by
      have hcon : (n.factorial : ℤ) ∣ ∏ k ∈ range n, ((1 + r) + (k : ℤ)) :=
        int_factorial_dvd_prod_consec n (1 + r)
      have heq : ∏ k ∈ range n, ((k + 1 : ℤ) + r) = ∏ k ∈ range n, ((1 + r) + (k : ℤ)) :=
        prod_congr rfl fun k _ => by ring
      rw [heq]
      exact dvd_mul_of_dvd_right (dvd_trans hM_dvd_fact hcon) _
    have hsum := dvd_add h1 h2
    simpa using hsum
  rcases seqPair_split_mod n ((p : ℤ) ^ M) r hr with ⟨hsp1, hsp2⟩
  have hplus : (p : ℤ) ^ M ∣ (seqPair n).1 + r * (seqPair n).2 := by
    simpa using dvd_add hsp1 hprod_add
  have hminus : (p : ℤ) ^ M ∣ (seqPair n).1 - r * (seqPair n).2 := by
    simpa using dvd_add hsp2 hprod_sub
  have h2ry : (p : ℤ) ^ M ∣ (2 * r) * (seqPair n).2 := by
    have hdiff := dvd_sub hplus hminus
    have hident : ((seqPair n).1 + r * (seqPair n).2) - ((seqPair n).1 - r * (seqPair n).2) =
        (2 * r) * (seqPair n).2 := by ring
    rwa [hident] at hdiff
  cases hM : M with
  | zero =>
    simp
  | succ M' =>
    rw [hM] at hr h2ry
    have hp_dvd_sq : (p : ℤ) ∣ r ^ 2 + 1 :=
      dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero M')) hr
    have hnot2r : ¬ (p : ℤ) ∣ 2 * r := by
      intro h
      have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
      rcases hpZ.dvd_or_dvd h with hp2 | hpr
      · have hp2n : p ∣ 2 := Int.ofNat_dvd.1 hp2
        have := Nat.le_of_dvd (by decide) hp2n
        omega
      · have hp1 : (p : ℤ) ∣ 1 := by
          have h1 : (p : ℤ) ∣ (r ^ 2 + 1) - r * r :=
            dvd_sub hp_dvd_sq (dvd_mul_of_dvd_left hpr r)
          simpa [sq] using h1
        have hp1n : p ∣ 1 := Int.ofNat_dvd.1 hp1
        have := Nat.le_of_dvd Nat.zero_lt_one hp1n
        omega
    exact prime_pow_dvd_of_dvd_mul_coprime hp hnot2r (M' + 1) h2ry
