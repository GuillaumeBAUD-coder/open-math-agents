import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1

/-!
# Counting small prime-power components of a unitary perfect number

Write m for the 2-adic valuation. Split the odd prime-power components
p^e exactly dividing n at (m+2)^2. The reciprocal of the abundancy product
over the large components, including the 2-component, is at least 1-1/(m+2):
there are at most m+2 factors and each loses at most 1/(m+2)^2.

The abundancy product over the small components is strictly below 2.
A product of at most k factors of the form (y+1)/y lying below 2 stays
a positive distance below 2, uniformly in the integer denominators y.
The induction below proves this separation by removing a bounded component
or estimating every factor together if all components are large.
Thus bounding the two counts below suffices to bound m. The simple-prime
count omits the eight odd primes allowed below 5057. The repeated-prime
count tests the full prime power, so large exponents fall into the tail.
-/

-- Credit: @Pixelstorm44
namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1_H2_R3


-- U and V are the numerator and denominator of the partial product.
private theorem tail_loss (s : Finset ℕ) (f : ℕ → ℕ) (x : ℕ)
    (hx : ∀ p ∈ s, x ≤ f p) :
    x * (∏ p ∈ s, (f p+1)) ≤ x * (∏ p ∈ s, f p) + s.card * (∏ p ∈ s, (f p+1)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert y s hy ih =>
    have hi := ih (fun z hz => hx z (Finset.mem_insert_of_mem hz))
    have hxy := hx y (Finset.mem_insert_self ..)
    simp only [Finset.prod_insert hy, Finset.card_insert_of_notMem hy]
    nlinarith only [Nat.mul_le_mul_right (f y) hi,
      Nat.mul_le_mul_right (∏ z ∈ s, (f z+1)) (show x ≤ f y+1 by omega),
      Nat.zero_le (s.card * ∏ z ∈ s, (f z+1))]

/-- Products of bounded length lying strictly below a fixed positive rational
have a uniform gap from it, even if the components are unbounded. -/
private theorem separation (k M : ℕ) : ∃ C : ℕ, ∀ (s : Finset ℕ) (f : ℕ → ℕ) (a b : ℕ),
    s.card ≤ k → a ≤ M → b ≤ M →
    let U := ∏ p ∈ s, (f p+1)
    let V := ∏ p ∈ s, f p
    a*U < b*V → U ≤ C*(b*V-a*U) := by
  induction k generalizing M with
  | zero =>
    refine ⟨1, fun s f a b hk _ _ => ?_⟩
    have : s = ∅ := Finset.card_eq_zero.mp (by omega)
    subst s
    simp only [Finset.prod_empty, mul_one, one_mul]
    omega
  | succ k ih =>
    let T := 2*(k+1)*M
    obtain ⟨C,hC⟩ := ih (M*(T+1))
    refine ⟨max 2 ((T+1)*C), fun s f a b hk ha hb => ?_⟩
    dsimp only
    intro h
    by_cases hex : ∃ p ∈ s, f p ≤ T
    · obtain ⟨p,hp,hpT⟩ := hex
      rw [← Finset.mul_prod_erase s (fun i => f i+1) hp,
          ← Finset.mul_prod_erase s f hp] at h ⊢
      have hrem := hC (s.erase p) f (a*(f p+1)) (b*f p)
        (by rw [Finset.card_erase_of_mem hp]; omega)
        (Nat.mul_le_mul ha (by omega)) (Nat.mul_le_mul hb (by omega))
        (by simpa only [mul_assoc] using h)
      have hmul := Nat.mul_le_mul (show f p+1 ≤ T+1 by omega) hrem
      simp only [mul_assoc] at *
      exact hmul.trans (by rw [← mul_assoc]; exact Nat.mul_le_mul_right _ (le_max_right ..))
    · let U := ∏ p ∈ s, (f p+1)
      let V := ∏ p ∈ s, f p
      change a*U < b*V at h
      change U ≤ _*(b*V-a*U)
      have hVU : V ≤ U := Finset.prod_le_prod' (fun p _ => Nat.le_succ (f p))
      have hab : a < b := by
        by_contra! hba
        exact (not_lt_of_ge (Nat.mul_le_mul hba hVU)) h
      have hcut := Nat.mul_le_mul_left (2*(k+1)) hb
      have hg := tail_loss s f (2*b*(k+1)) (fun p hp => by
        have hn : ¬ f p ≤ T := fun h => hex ⟨p,hp,h⟩
        dsimp [T] at hn
        nlinarith only [hn,hcut])
      change 2*b*(k+1)*U ≤ 2*b*(k+1)*V+s.card*U at hg
      have hcancel : (k+1)*(2*b*U) ≤ (k+1)*(2*b*V+U) := by
        nlinarith only [hg,Nat.mul_le_mul_right U hk]
      have h2 := Nat.le_of_mul_le_mul_left hcancel (Nat.succ_pos k)
      have h3 := Nat.mul_le_mul_right U (show a+1 ≤ b from hab)
      have hd := Nat.sub_add_cancel (Nat.le_of_lt h)
      apply le_trans _ (Nat.mul_le_mul_right _ (le_max_left 2 ((T+1)*C)))
      nlinarith only [h2,h3,hd]

private theorem two_growth {m : ℕ} (h : 6 ≤ m) : (m+2)^2 ≤ 2^m := by
  induction m, h using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    rw [pow_succ 2]
    nlinarith [Nat.mul_le_mul hm hm, Nat.mul_le_mul_right 2 ih]


open OMA.R_Erdos1052_erdos_1052_R1 (prod_eq_two_mul prod_primeFactors_pow_self card_primeFactors_le)

/-- A count of the small odd components suffices because the large components
together change the reciprocal of the product by at most 1/(m+2). -/
private theorem bound_of_small_count (k : ℕ) : ∃ B : ℕ, ∀ n : ℕ,
    Erdos1052.IsUnitaryPerfect n → 6 ≤ padicValNat 2 n →
    (n.primeFactors.filter (fun p => p ≠ 2 ∧ p ^ n.factorization p < (padicValNat 2 n+2)^2)).card ≤ k →
    padicValNat 2 n ≤ B := by
  obtain ⟨C,hC⟩ := separation k 2
  refine ⟨2*C, fun n h hm hk => ?_⟩
  let m := padicValNat 2 n
  let f := fun p : ℕ => p ^ n.factorization p
  let s := n.primeFactors.filter (fun p => p ≠ 2 ∧ f p < (m+2)^2)
  let t := n.primeFactors \ s
  let U := ∏ p ∈ s, (f p+1)
  let V := ∏ p ∈ s, f p
  let W := ∏ p ∈ t, (f p+1)
  let X := ∏ p ∈ t, f p
  have hn0 := h.2.ne'
  have hsub : s ⊆ n.primeFactors := Finset.filter_subset _ _
  have hf : ∀ p ∈ n.primeFactors, 0 < f p := fun p hp =>
    pow_pos (Nat.prime_of_mem_primeFactors hp).pos _
  have h2 : 2 ∣ n := by
    have ha : 1 ≤ n.factorization 2 := by rw [Nat.factorization_def n Nat.prime_two]; omega
    simpa using (Nat.prime_two.pow_dvd_iff_le_factorization hn0).mpr ha
  have ht : t.Nonempty := ⟨2, Finset.mem_sdiff.mpr
    ⟨Nat.mem_primeFactors.mpr ⟨Nat.prime_two,h2,hn0⟩, by simp [s]⟩⟩
  have hXW : X < W := Finset.prod_lt_prod_of_nonempty
    (fun p hp => hf p (Finset.mem_sdiff.mp hp).1) (fun p _ => Nat.lt_succ_self (f p)) ht
  have hV : 0 < V := Finset.prod_pos (fun p hp => hf p (hsub hp))
  have hVU : V ≤ U := Finset.prod_le_prod' (fun p _ => Nat.le_succ (f p))
  have E : W*U = 2*(X*V) := by
    dsimp only [W,U,X,V,t]
    rw [Finset.prod_sdiff hsub, Finset.prod_sdiff hsub]
    simpa only [f, Nat.add_comm 1, prod_primeFactors_pow_self hn0] using prod_eq_two_mul h
  have hd : 1*U < 2*V := by
    by_contra! hl
    have h1 := Nat.mul_le_mul_left W hl
    have h2' := Nat.mul_lt_mul_of_pos_left hXW (show 0 < 2*V by omega)
    nlinarith only [h1,h2',E]
  have hsep := hC s f 1 2 hk (by decide) (by decide) hd
  change U ≤ C*(2*V-1*U) at hsep
  simp only [one_mul] at hd hsep
  have hcut : ∀ p ∈ t, (m+2)^2 ≤ f p := by
    intro p hp
    obtain ⟨hpn,hps⟩ := Finset.mem_sdiff.mp hp
    by_cases heq : p = 2
    · subst p
      simpa only [f, Nat.factorization_def n Nat.prime_two, m] using two_growth hm
    · exact le_of_not_gt (fun hl => hps (Finset.mem_filter.mpr ⟨hpn, heq, hl⟩))
  have hg := tail_loss t f ((m+2)^2) hcut
  change (m+2)^2*W ≤ (m+2)^2*X+t.card*W at hg
  have hcard : t.card ≤ m+2 := (Finset.card_le_card Finset.sdiff_subset).trans (card_primeFactors_le h)
  have htail : (m+2)*W ≤ (m+2)*X+W := by
    apply Nat.le_of_mul_le_mul_left _ (show 0 < m+2 by omega)
    nlinarith only [hg,Nat.mul_le_mul_right W hcard]
  have hmul := Nat.mul_le_mul_left (2*V) htail
  have hweighted : ((m+2)*(2*V))*W ≤ ((m+2)*U+2*V)*W := by
    calc
      _ ≤ (m+2)*(2*(X*V))+2*V*W := by nlinarith only [hmul]
      _ = _ := by rw [← E]; ring
  have hsmall := Nat.le_of_mul_le_mul_right hweighted (show 0 < W by omega)
  have hfinal : (m+2)*(2*V-U) ≤ (2*C)*(2*V-U) := by
    calc
      _ ≤ 2*V := by rw [Nat.mul_sub]; omega
      _ ≤ 2*U := Nat.mul_le_mul_left 2 hVU
      _ ≤ _ := by simpa only [mul_assoc] using Nat.mul_le_mul_left 2 hsep
  have hresult := Nat.le_of_mul_le_mul_right hfinal (show 0 < 2*V-U by omega)
  change m ≤ 2*C
  omega

def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ¬ Squarefree (n / 2 ^ padicValNat 2 n) →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) →
    (∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) →
    ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097 →
    4 ∣ padicValNat 2 n → 3 ∣ n → 5 ∣ n → 7 ∣ n → 19 ∣ n →
    (∀ N : Finset ℕ, S ⊆ N → (∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z) →
      ∏ z ∈ N, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097 →
      (∃ z ∈ N, z ∣ 2 ^ padicValNat 2 n + 1 ∧ z % 3 = 2) ∧
      ∀ z ∈ N, z % 3 = 2 → Even (n.factorization z)) →
    16 ∣ padicValNat 2 n → padicValNat 2 n % 64 ≠ 32 →
    31 ∣ n →
    (∀ q : ℕ, q.Prime → q ∣ n → q < 5057 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607 ∨ q = 3967) →
    223 ∣ n → 607 ∣ n → 3967 ∣ n → 48 ≤ padicValNat 2 n →
    ∏ z ∈ S, (1 + 5 / (z : ℚ)) ≤ 5001 / 5000 →
    (n.primeFactors.filter (fun p => 5057 ≤ p ∧ n.factorization p = 1 ∧
      p < (padicValNat 2 n + 2)^2)).card ≤ A

def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ¬ Squarefree (n / 2 ^ padicValNat 2 n) →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) →
    (∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) →
    ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097 →
    4 ∣ padicValNat 2 n → 3 ∣ n → 5 ∣ n → 7 ∣ n → 19 ∣ n →
    (∀ N : Finset ℕ, S ⊆ N → (∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z) →
      ∏ z ∈ N, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097 →
      (∃ z ∈ N, z ∣ 2 ^ padicValNat 2 n + 1 ∧ z % 3 = 2) ∧
      ∀ z ∈ N, z % 3 = 2 → Even (n.factorization z)) →
    16 ∣ padicValNat 2 n → padicValNat 2 n % 64 ≠ 32 →
    31 ∣ n →
    (∀ q : ℕ, q.Prime → q ∣ n → q < 5057 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607 ∨ q = 3967) →
    223 ∣ n → 607 ∣ n → 3967 ∣ n → 48 ≤ padicValNat 2 n →
    ∏ z ∈ S, (1 + 5 / (z : ℚ)) ≤ 5001 / 5000 →
    (S.filter (fun p => p ^ n.factorization p < (padicValNat 2 n + 2)^2)).card ≤ A

set_option maxHeartbeats 650000 in
theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1.H2 := by
  rintro ⟨A,hA⟩ ⟨B,hB⟩
  obtain ⟨D,hD⟩ := bound_of_small_count (8+A+B)
  refine ⟨D, ?_⟩
  intro n h hns S hS hlarge hprod h4 h3 h5 h7 h19 hext h16 hmod h31 hsieve h223 h607 h3967 hm hthin
  specialize hA n h hns S hS hlarge hprod h4 h3 h5 h7 h19 hext h16 hmod h31 hsieve h223 h607 h3967 hm hthin
  specialize hB n h hns S hS hlarge hprod h4 h3 h5 h7 h19 hext h16 hmod h31 hsieve h223 h607 h3967 hm hthin
  clear hns hlarge hprod h4 h3 h5 h7 h19 hext h16 hmod h31 h223 h607 h3967 hthin
  apply hD n h (le_trans (by decide : 6 ≤ 48) hm)
  let cutoff := (padicValNat 2 n + 2)^2
  let core : Finset ℕ := {3,5,7,19,31,223,607,3967}
  let simple := n.primeFactors.filter (fun p => 5057 ≤ p ∧ n.factorization p = 1 ∧ p < cutoff)
  let repeated := S.filter (fun p => p ^ n.factorization p < cutoff)
  have cover : n.primeFactors.filter (fun p => p ≠ 2 ∧ p ^ n.factorization p < cutoff) ⊆
      (core ∪ simple) ∪ repeated := by
    intro p hp
    obtain ⟨hpn,hp2,hcut⟩ := Finset.mem_filter.mp hp
    obtain ⟨hprime,hd,hn0⟩ := Nat.mem_primeFactors.mp hpn
    by_cases he : n.factorization p = 1
    · apply Finset.mem_union_left
      by_cases hlo : p < 5057
      · apply Finset.mem_union_left
        have hz := hsieve p hprime hd hlo
        simpa only [core, Finset.mem_insert, Finset.mem_singleton] using hz.resolve_left hp2
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
          ⟨hpn,Nat.le_of_not_gt hlo,he,by simpa only [he,pow_one] using hcut⟩)
    · apply Finset.mem_union_right
      have hepos := hprime.factorization_pos_of_dvd hn0 hd
      have he2 : 2 ≤ n.factorization p := by clear * - hepos he; omega
      have hs := (hS p).mpr ⟨hprime,hp2,(hprime.pow_dvd_iff_le_factorization hn0).mpr he2⟩
      exact Finset.mem_filter.mpr ⟨hs,hcut⟩
  have hcard : core.card = 8 := by unfold core; decide
  have hu := Finset.card_union_le core simple
  have hv := Finset.card_union_le (core ∪ simple) repeated
  change simple.card ≤ A at hA
  change repeated.card ≤ B at hB
  exact (Finset.card_le_card cover).trans (hv.trans (Nat.add_le_add (hu.trans (Nat.add_le_add (le_of_eq hcard) hA)) hB))

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1_H2_R3
