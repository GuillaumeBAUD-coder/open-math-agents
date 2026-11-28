import OMAStatements.S_oeis_a000089

-- Problem: A000089: Number of solutions to x^2 + 1 == 0 (mod n).
-- Upstream: formal-conjectures statements/oeis-a000089.lean:0 (declaration OMA.S_oeis_a000089.main)
-- Credit: @Dolcruz (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.OeisA000089

open ArithmeticFunction OMA.S_oeis_a000089

private def solCount (n : ℕ) : ℕ :=
  ((Finset.range n).filter fun x => (x ^ 2 + 1) % n = 0).card

private lemma a_apply_pos {n : ℕ} (hn : n ≠ 0) : a n = (solCount n : ℤ) := by
  simp [a, solCount, hn]

private lemma solCount_eq_zmod_card (n : ℕ) [NeZero n] :
    solCount n = (Finset.univ.filter fun x : ZMod n => x ^ 2 + 1 = 0).card := by
  unfold solCount
  refine Finset.card_bij (fun x _ => (x : ZMod n)) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_univ, true_and] at hx ⊢
    have hdvd : n ∣ x ^ 2 + 1 := Nat.dvd_of_mod_eq_zero hx.2
    have hcast : ((x ^ 2 + 1 : ℕ) : ZMod n) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hdvd
    push_cast at hcast
    exact hcast
  · intro x₁ hx₁ x₂ hx₂ heq
    simp only [Finset.mem_filter, Finset.mem_range] at hx₁ hx₂
    have h1 : ((x₁ : ZMod n)).val = x₁ := ZMod.val_natCast_of_lt hx₁.1
    have h2 : ((x₂ : ZMod n)).val = x₂ := ZMod.val_natCast_of_lt hx₂.1
    rw [← h1, ← h2, heq]
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    refine ⟨z.val, ?_, ZMod.natCast_zmod_val z⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨ZMod.val_lt z, ?_⟩
    apply Nat.mod_eq_zero_of_dvd
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [ZMod.natCast_zmod_val]
    exact hz

private lemma solCount_mul {m n : ℕ} (hcop : Nat.Coprime m n) (hm : m ≠ 0) (hn : n ≠ 0) :
    solCount (m * n) = solCount m * solCount n := by
  have : NeZero m := ⟨hm⟩
  have : NeZero n := ⟨hn⟩
  have : NeZero (m * n) := ⟨mul_ne_zero hm hn⟩
  rw [solCount_eq_zmod_card (m * n), solCount_eq_zmod_card m, solCount_eq_zmod_card n,
    ← Finset.card_product]
  let e := ZMod.chineseRemainder hcop
  refine Finset.card_bij (fun x _ => e x) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product] at hx ⊢
    have h0 : e (x ^ 2 + 1) = 0 := by rw [hx, _root_.map_zero]
    rw [map_add, map_pow, map_one] at h0
    exact ⟨congrArg Prod.fst h0, congrArg Prod.snd h0⟩
  · intro x₁ _ x₂ _ heq
    exact e.injective heq
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    refine ⟨e.symm p, ?_, e.apply_symm_apply p⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    apply e.injective
    rw [map_add, map_pow, map_one, _root_.map_zero, e.apply_symm_apply]
    exact Prod.ext hp.1 hp.2

private lemma a_isMultiplicative : a.IsMultiplicative := by
  constructor
  · have h1 : solCount 1 = 1 := by decide
    rw [a_apply_pos one_ne_zero, h1]
    rfl
  · intro m n hcop
    by_cases hm : m = 0
    · simp [a, hm]
    by_cases hn : n = 0
    · simp [a, hn]
    rw [a_apply_pos (mul_ne_zero hm hn), a_apply_pos hm, a_apply_pos hn, solCount_mul hcop hm hn]
    push_cast
    rfl

private lemma a_two : a 2 = 1 := by
  have h2 : solCount 2 = 1 := by decide
  rw [a_apply_pos (by decide : (2 : ℕ) ≠ 0), h2]
  rfl

private lemma a_two_pow {k : ℕ} (hk : 2 ≤ k) : a (2 ^ k) = 0 := by
  have hne : 2 ^ k ≠ 0 := by positivity
  rw [a_apply_pos hne]
  suffices h : solCount (2 ^ k) = 0 by simp [h]
  unfold solCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x _ hmod
  have hdvd1 : 2 ^ k ∣ x ^ 2 + 1 := Nat.dvd_of_mod_eq_zero hmod
  have hdvd2 : 4 ∣ 2 ^ k := by
    change 2 ^ 2 ∣ 2 ^ k
    exact Nat.pow_dvd_pow 2 hk
  have hdvd4 : 4 ∣ x ^ 2 + 1 := hdvd2.trans hdvd1
  have hm4 : (x ^ 2 + 1) % 4 = 0 := Nat.mod_eq_zero_of_dvd hdvd4
  have hsq : (x ^ 2 + 1) % 4 = ((x % 4) ^ 2 + 1) % 4 := by
    rw [Nat.add_mod, Nat.pow_mod, ← Nat.add_mod]
  rw [hsq] at hm4
  have hr : x % 4 < 4 := Nat.mod_lt x (by decide)
  interval_cases (x % 4) <;> simp at hm4

private lemma a_prime_pow_mod4_eq_3 {p k : ℕ} (hp : p.Prime) (hp3 : p % 4 = 3) (hk : 1 ≤ k) :
    a (p ^ k) = 0 := by
  have hne : p ^ k ≠ 0 := pow_ne_zero k hp.ne_zero
  rw [a_apply_pos hne]
  suffices h : solCount (p ^ k) = 0 by simp [h]
  unfold solCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x _ hmod
  have hdvd : p ∣ x ^ 2 + 1 := (dvd_pow_self p (by omega : k ≠ 0)).trans (Nat.dvd_of_mod_eq_zero hmod)
  have : Fact p.Prime := ⟨hp⟩
  have hz : ((x : ZMod p) ^ 2) = -1 := by
    have h0 : ((x ^ 2 + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hdvd
    push_cast at h0
    exact eq_neg_of_add_eq_zero_left h0
  have hiff := (ZMod.exists_sq_eq_neg_one_iff (p := p)).1 ⟨(x : ZMod p), by rw [← sq]; exact hz.symm⟩
  exact hiff hp3

private lemma solCount_prime_mod4_eq_1 {p : ℕ} (hp : p.Prime) (hp1 : p % 4 = 1) :
    solCount p = 2 := by
  have : Fact p.Prime := ⟨hp⟩
  rw [solCount_eq_zmod_card p]
  have hne3 : p % 4 ≠ 3 := by omega
  obtain ⟨r, hr'⟩ := (ZMod.exists_sq_eq_neg_one_iff (p := p)).2 hne3
  have hr : r ^ 2 = -1 := by rw [sq]; exact hr'.symm
  have hne : r ≠ -r := by
    intro heq
    have h2r : (2 : ZMod p) * r = 0 := by
      have : r + r = 0 := by
        calc r + r = r + (-r) := by nth_rw 2 [heq]
          _ = 0 := add_neg_cancel r
      rwa [two_mul]
    have h2ne : (2 : ZMod p) ≠ 0 := by
      intro h20
      have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 (by simpa using h20)
      have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hdvd
      omega
    have hr0 : r = 0 := (mul_eq_zero.1 h2r).resolve_left h2ne
    rw [hr0] at hr
    simp at hr
  have hset : Finset.univ.filter (fun x : ZMod p => x ^ 2 + 1 = 0) = ({r, -r} : Finset (ZMod p)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hx
      have hmul : (x - r) * (x + r) = 0 := by
        calc (x - r) * (x + r) = x ^ 2 - r ^ 2 := by ring
          _ = x ^ 2 + 1 := by rw [hr]; ring
          _ = 0 := hx
      rcases mul_eq_zero.1 hmul with h1 | h2
      · exact Or.inl (sub_eq_zero.1 h1)
      · exact Or.inr (eq_neg_of_add_eq_zero_left h2)
    · rintro (rfl | rfl)
      · rw [hr]; ring
      · rw [neg_sq, hr]; ring
  rw [hset, Finset.card_pair hne]

private lemma solCount_prime_pow_step {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk : 1 ≤ k) :
    solCount (p ^ (k + 1)) = solCount (p ^ k) := by
  have : Fact p.Prime := ⟨hp⟩
  have hpk_pos : 0 < p ^ k := pow_pos hp.pos k
  have hpk_ne : p ^ k ≠ 0 := hpk_pos.ne'
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h20
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 (by simpa using h20)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hdvd)
  have hnotdvd_x : ∀ x : ℕ, p ∣ x ^ 2 + 1 → ¬ (p ∣ x) := by
    intro x hx hpx
    have hpx2 : p ∣ x ^ 2 := dvd_pow hpx (by decide : 2 ≠ 0)
    have hp1 : p ∣ 1 := (Nat.dvd_add_right hpx2).1 hx
    exact hp.not_dvd_one hp1
  unfold solCount
  refine Finset.card_bij (fun y _ => y % p ^ k) ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_range] at hy ⊢
    refine ⟨Nat.mod_lt y hpk_pos, ?_⟩
    have hdvd_y : p ^ k ∣ y ^ 2 + 1 :=
      (Nat.pow_dvd_pow p (Nat.le_succ k)).trans (Nat.dvd_of_mod_eq_zero hy.2)
    have hmod : (y % p ^ k) ^ 2 + 1 ≡ y ^ 2 + 1 [MOD p ^ k] :=
      ((Nat.mod_modEq y (p ^ k)).pow 2).add_right 1
    rw [Nat.ModEq] at hmod
    rw [hmod]
    exact Nat.mod_eq_zero_of_dvd hdvd_y
  · intro y₁ hy₁ y₂ hy₂ hmod_eq
    simp only [Finset.mem_filter, Finset.mem_range] at hy₁ hy₂
    set x := y₁ % p ^ k
    set t₁ := y₁ / p ^ k
    set t₂ := y₂ / p ^ k
    have hy₁_eq : y₁ = x + p ^ k * t₁ := by
      rw [add_comm]
      exact (Nat.div_add_mod y₁ (p ^ k)).symm
    have hy₂_eq : y₂ = x + p ^ k * t₂ := by
      rw [hmod_eq, add_comm]
      exact (Nat.div_add_mod y₂ (p ^ k)).symm
    have ht₁_lt : t₁ < p :=
      Nat.div_lt_of_lt_mul (by simpa [pow_succ] using hy₁.1)
    have ht₂_lt : t₂ < p :=
      Nat.div_lt_of_lt_mul (by simpa [pow_succ] using hy₂.1)
    have hd1 : ((p ^ (k + 1) : ℕ) : ℤ) ∣ ((y₁ : ℤ) ^ 2 + 1) := by
      exact_mod_cast Nat.dvd_of_mod_eq_zero hy₁.2
    have hd2 : ((p ^ (k + 1) : ℕ) : ℤ) ∣ ((y₂ : ℤ) ^ 2 + 1) := by
      exact_mod_cast Nat.dvd_of_mod_eq_zero hy₂.2
    have hdiff : ((p ^ (k + 1) : ℕ) : ℤ) ∣ ((y₁ : ℤ) ^ 2 + 1) - ((y₂ : ℤ) ^ 2 + 1) :=
      dvd_sub hd1 hd2
    have hfactor : ((y₁ : ℤ) ^ 2 + 1) - ((y₂ : ℤ) ^ 2 + 1) =
        ((p ^ k : ℕ) : ℤ) * (((t₁ : ℤ) - t₂) * (2 * x + ((t₁ : ℤ) + t₂) * ((p ^ k : ℕ) : ℤ))) := by
      rw [hy₁_eq, hy₂_eq]
      push_cast
      ring
    rw [hfactor, pow_succ, Nat.cast_mul] at hdiff
    have hpk_z_ne : ((p ^ k : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hpk_ne
    have hpdvd : (p : ℤ) ∣ ((t₁ : ℤ) - t₂) * (2 * x + ((t₁ : ℤ) + t₂) * ((p ^ k : ℕ) : ℤ)) :=
      (mul_dvd_mul_iff_left hpk_z_ne).1 hdiff
    have hp_dvd_pk : p ∣ p ^ k := dvd_pow_self p (by omega : k ≠ 0)
    have hpdvd_x : p ∣ x ^ 2 + 1 := by
      have hdvd_y1 : p ∣ y₁ ^ 2 + 1 :=
        (dvd_pow_self p (by omega : k + 1 ≠ 0)).trans (Nat.dvd_of_mod_eq_zero hy₁.2)
      have hcong : x ^ 2 + 1 ≡ y₁ ^ 2 + 1 [MOD p] := by
        have hxy : x ≡ y₁ [MOD p] := (Nat.mod_modEq y₁ (p ^ k)).of_dvd hp_dvd_pk
        exact (hxy.pow 2).add_right 1
      exact (Nat.ModEq.dvd_iff hcong (dvd_refl p)).2 hdvd_y1
    have hnot_second : ¬ ((p : ℤ) ∣ (2 * (x : ℤ) + ((t₁ : ℤ) + t₂) * ((p ^ k : ℕ) : ℤ))) := by
      intro hsec
      have hterm : (p : ℤ) ∣ ((t₁ : ℤ) + t₂) * ((p ^ k : ℕ) : ℤ) :=
        dvd_mul_of_dvd_right (by exact_mod_cast hp_dvd_pk) _
      have h2x_z : (p : ℤ) ∣ 2 * (x : ℤ) := (dvd_add_left hterm).1 hsec
      have h2x : p ∣ 2 * x := by exact_mod_cast h2x_z
      rcases hp.dvd_mul.1 h2x with h2 | hx
      · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
      · exact hnotdvd_x x hpdvd_x hx
    have hpdvd_t : (p : ℤ) ∣ (t₁ : ℤ) - t₂ := by
      rcases (Nat.prime_iff_prime_int.1 hp).dvd_or_dvd hpdvd with h1 | h2
      · exact h1
      · exact absurd h2 hnot_second
    have ht_eq : t₁ = t₂ := by
      obtain ⟨c, hc⟩ := hpdvd_t
      have ht₁_z : (t₁ : ℤ) < p := by exact_mod_cast ht₁_lt
      have ht₂_z : (t₂ : ℤ) < p := by exact_mod_cast ht₂_lt
      have hbound1 : -((p : ℤ)) < (t₁ : ℤ) - t₂ := by linarith [Int.natCast_nonneg t₁]
      have hbound2 : (t₁ : ℤ) - t₂ < (p : ℤ) := by linarith [Int.natCast_nonneg t₂]
      have hc0 : c = 0 := by nlinarith
      rw [hc0, mul_zero] at hc
      have hz_eq : (t₁ : ℤ) = t₂ := by linarith
      exact_mod_cast hz_eq
    rw [hy₁_eq, hy₂_eq, ht_eq]
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx
    have hdvd_x : p ^ k ∣ x ^ 2 + 1 := Nat.dvd_of_mod_eq_zero hx.2
    set q := (x ^ 2 + 1) / p ^ k
    have hq_eq : x ^ 2 + 1 = p ^ k * q := (Nat.mul_div_cancel' hdvd_x).symm
    have hp_dvd_pk : p ∣ p ^ k := dvd_pow_self p (by omega : k ≠ 0)
    have hpx_ne : (x : ZMod p) ≠ 0 := by
      intro hx0
      have hpx : p ∣ x := (ZMod.natCast_eq_zero_iff x p).1 hx0
      exact hnotdvd_x x (hp_dvd_pk.trans hdvd_x) hpx
    have h2x_ne : (2 : ZMod p) * (x : ZMod p) ≠ 0 := mul_ne_zero h2ne hpx_ne
    let tz : ZMod p := -(q : ZMod p) * ((2 : ZMod p) * (x : ZMod p))⁻¹
    let t : ℕ := tz.val
    have ht_lt : t < p := ZMod.val_lt tz
    refine ⟨x + p ^ k * t, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨?_, ?_⟩
      · have : x + p ^ k * t < p ^ k + p ^ k * (p - 1) := by
          have ht_le : t ≤ p - 1 := Nat.le_sub_one_of_lt ht_lt
          have hmul : p ^ k * t ≤ p ^ k * (p - 1) := Nat.mul_le_mul_left (p ^ k) ht_le
          omega
        have hpow : p ^ k + p ^ k * (p - 1) = p ^ (k + 1) := by
          rw [pow_succ]
          have hp_pos : 1 ≤ p := hp.one_le
          zify [hp_pos]
          ring
        omega
      · apply Nat.mod_eq_zero_of_dvd
        have hexpand : (x + p ^ k * t) ^ 2 + 1 = p ^ k * (q + 2 * x * t + t ^ 2 * p ^ k) := by
          calc (x + p ^ k * t) ^ 2 + 1 = (x ^ 2 + 1) + 2 * x * (p ^ k * t) + (p ^ k * t) ^ 2 := by ring
            _ = p ^ k * q + 2 * x * (p ^ k * t) + (p ^ k * t) ^ 2 := by rw [hq_eq]
            _ = p ^ k * (q + 2 * x * t + t ^ 2 * p ^ k) := by ring
        rw [hexpand, pow_succ]
        apply Nat.mul_dvd_mul_left
        rw [← ZMod.natCast_eq_zero_iff]
        push_cast
        have hp0 : (p : ZMod p) = 0 := ZMod.natCast_self p
        rw [hp0, zero_pow (by omega : k ≠ 0)]
        have ht_cast : (t : ZMod p) = tz := ZMod.natCast_zmod_val tz
        rw [ht_cast]
        simp only [tz, mul_zero, add_zero]
        calc (q : ZMod p) + 2 * (x : ZMod p) * (-(q : ZMod p) * (2 * (x : ZMod p))⁻¹)
            = (q : ZMod p) - (q : ZMod p) * ((2 * (x : ZMod p)) * (2 * (x : ZMod p))⁻¹) := by ring
          _ = (q : ZMod p) - (q : ZMod p) * 1 := by rw [mul_inv_cancel₀ h2x_ne]
          _ = 0 := by ring
    · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx.1]

private lemma solCount_prime_pow_mod4_eq_1 {p k : ℕ} (hp : p.Prime) (hp1 : p % 4 = 1) (hk : 1 ≤ k) :
    solCount (p ^ k) = 2 := by
  have hp2 : p ≠ 2 := by omega
  induction k, hk using Nat.le_induction with
  | base =>
    simpa using solCount_prime_mod4_eq_1 hp hp1
  | succ m hm ih =>
    rw [solCount_prime_pow_step hp hp2 hm, ih]

private lemma a_prime_pow_mod4_eq_1 {p k : ℕ} (hp : p.Prime) (hp1 : p % 4 = 1) (hk : 1 ≤ k) :
    a (p ^ k) = 2 := by
  rw [a_apply_pos (pow_ne_zero k hp.ne_zero), solCount_prime_pow_mod4_eq_1 hp hp1 hk]
  rfl

private def omegaCount (n : ℕ) : ℕ :=
  n.factorization.sum fun _ k => k

private lemma omegaCount_one : omegaCount 1 = 0 := by
  simp [omegaCount]

private lemma omegaCount_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    omegaCount (m * n) = omegaCount m + omegaCount n := by
  unfold omegaCount
  rw [Nat.factorization_mul hm hn]
  exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

private lemma omegaCount_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    omegaCount (p ^ k) = k := by
  unfold omegaCount
  rw [hp.factorization_pow, Finsupp.sum_single_index rfl]

private lemma A091400_one : A091400 1 = 1 := by
  simp [A091400]

private lemma A091400_mul {m n : ℕ} (hcop : Nat.Coprime m n) (hm : m ≠ 0) (hn : n ≠ 0) :
    A091400 (m * n) = A091400 m * A091400 n := by
  unfold A091400
  rw [Nat.primeFactors_mul hm hn, Finset.filter_union]
  apply Finset.prod_union
  exact (hcop.disjoint_primeFactors).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)

private lemma A091400_nonneg (n : ℕ) : 0 ≤ A091400 n := by
  unfold A091400
  apply Finset.prod_nonneg
  intro p _
  unfold chi
  split_ifs <;> omega

private lemma A091400_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    A091400 (p ^ k) = if p = 2 then 1 else 1 + chi p := by
  unfold A091400
  rw [Nat.primeFactors_pow p (by omega : k ≠ 0), hp.primeFactors]
  by_cases h2 : p = 2
  · subst h2
    simp [Finset.filter_singleton]
  · simp [Finset.filter_singleton, h2]

private def g0 : ArithmeticFunction ℤ :=
  ⟨fun n => if n = 0 then 0 else (-1 : ℤ) ^ (omegaCount n) * A091400 n, by simp⟩

private lemma g0_apply_pos {n : ℕ} (hn : n ≠ 0) :
    g0 n = (-1 : ℤ) ^ (omegaCount n) * A091400 n := by
  simp [g0, hn]

private lemma g0_isMultiplicative : g0.IsMultiplicative := by
  constructor
  · rw [g0_apply_pos one_ne_zero, omegaCount_one, A091400_one]
    simp
  · intro m n hcop
    by_cases hm : m = 0
    · simp [g0, hm]
    by_cases hn : n = 0
    · simp [g0, hn]
    rw [g0_apply_pos (mul_ne_zero hm hn), g0_apply_pos hm, g0_apply_pos hn,
      omegaCount_mul hm hn, A091400_mul hcop hm hn, pow_add]
    ring

private lemma g0_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    g0 (p ^ k) = (-1 : ℤ) ^ k * (if p = 2 then 1 else 1 + chi p) := by
  rw [g0_apply_pos (pow_ne_zero k hp.ne_zero), omegaCount_prime_pow hp k, A091400_prime_pow hp hk]

private lemma mul_prime_pow_sum (f h : ArithmeticFunction ℤ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (f * h) (p ^ k) = ∑ i ∈ Finset.range (k + 1), f (p ^ i) * h (p ^ (k - i)) := by
  rw [ArithmeticFunction.mul_apply]
  symm
  refine Finset.sum_bij (fun i _ => (p ^ i, p ^ (k - i))) ?_ ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_range] at hi
    rw [Nat.mem_divisorsAntidiagonal]
    refine ⟨?_, pow_ne_zero k hp.ne_zero⟩
    rw [← pow_add, Nat.add_sub_of_le (by omega)]
  · intro i₁ _ i₂ _ heq
    have h1 : p ^ i₁ = p ^ i₂ := congrArg Prod.fst heq
    exact Nat.pow_right_injective hp.two_le h1
  · intro x hx
    rw [Nat.mem_divisorsAntidiagonal] at hx
    have hdvd : x.1 ∣ p ^ k := ⟨x.2, hx.1.symm⟩
    obtain ⟨i, hi, hx1⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    refine ⟨i, Finset.mem_range.2 (by omega), ?_⟩
    apply Prod.ext
    · exact hx1.symm
    · have hmul : p ^ i * x.2 = p ^ i * p ^ (k - i) := by
        calc p ^ i * x.2 = x.1 * x.2 := by rw [hx1]
          _ = p ^ k := hx.1
          _ = p ^ (i + (k - i)) := by rw [Nat.add_sub_of_le hi]
          _ = p ^ i * p ^ (k - i) := pow_add p i (k - i)
      exact (Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos i) hmul).symm
  · intro _ _
    rfl

private lemma a_mul_g0_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    (a * g0) (p ^ k) = 0 := by
  rw [mul_prime_pow_sum a g0 hp k]
  by_cases hp2 : p = 2
  · subst hp2
    have hsplit : ∑ i ∈ Finset.range (k + 1), a (2 ^ i) * g0 (2 ^ (k - i)) =
        a (2 ^ 0) * g0 (2 ^ k) + a (2 ^ 1) * g0 (2 ^ (k - 1)) +
        ∑ i ∈ (Finset.range (k + 1)).filter (fun i => 2 ≤ i), a (2 ^ i) * g0 (2 ^ (k - i)) := by
      have h01 : ∑ i ∈ Finset.range (k + 1), a (2 ^ i) * g0 (2 ^ (k - i)) =
          ∑ i ∈ (Finset.range (k + 1)).filter (fun i => i < 2), a (2 ^ i) * g0 (2 ^ (k - i)) +
          ∑ i ∈ (Finset.range (k + 1)).filter (fun i => ¬ i < 2), a (2 ^ i) * g0 (2 ^ (k - i)) := by
        rw [Finset.sum_filter_add_sum_filter_not]
      rw [h01]
      have hlt : (Finset.range (k + 1)).filter (fun i => i < 2) = {0, 1} := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
        omega
      have hge : (Finset.range (k + 1)).filter (fun i => ¬ i < 2) =
          (Finset.range (k + 1)).filter (fun i => 2 ≤ i) := by
        ext i; simp only [Finset.mem_filter, not_lt]
      rw [hlt, hge, Finset.sum_pair (by decide : (0 : ℕ) ≠ 1)]
      simp
    rw [hsplit]
    have hrest : ∑ i ∈ (Finset.range (k + 1)).filter (fun i => 2 ≤ i), a (2 ^ i) * g0 (2 ^ (k - i)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp only [Finset.mem_filter] at hi
      rw [a_two_pow hi.2, zero_mul]
    rw [hrest, add_zero, pow_zero, pow_one, a_isMultiplicative.map_one, a_two, one_mul, one_mul]
    rw [g0_prime_pow Nat.prime_two hk]
    simp only [↓reduceIte, mul_one]
    by_cases hk1 : k = 1
    · subst hk1
      simp [g0_isMultiplicative.map_one]
    · have hk2 : 1 ≤ k - 1 := by omega
      rw [g0_prime_pow Nat.prime_two hk2]
      simp only [↓reduceIte, mul_one]
      have hpow : (-1 : ℤ) ^ k = -((-1 : ℤ) ^ (k - 1)) := by
        conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
        ring
      linarith
  · have hmod := hp.eq_two_or_odd
    have hodd : p % 2 = 1 := hmod.resolve_left hp2
    have h4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
    rcases h4 with hp1 | hp3
    · have hg0_val : ∀ m : ℕ, 1 ≤ m → g0 (p ^ m) = 2 * (-1 : ℤ) ^ m := by
        intro m hm
        rw [g0_prime_pow hp hm]
        simp [hp2, chi, hp1]
        ring
      have hS : ∀ m : ℕ, 1 ≤ m → ∑ i ∈ Finset.range (m + 1), a (p ^ i) * g0 (p ^ (m - i)) = 0 := by
        intro m hm
        induction m, hm using Nat.le_induction with
        | base =>
          rw [Finset.sum_range_succ, Finset.sum_range_one]
          simp only [Nat.sub_zero, Nat.sub_self, pow_zero, pow_one,
            a_isMultiplicative.map_one, g0_isMultiplicative.map_one, one_mul, mul_one]
          have hg1 : g0 p = 2 * (-1 : ℤ) ^ 1 := by simpa using hg0_val 1 le_rfl
          have ha1 : a p = 2 := by simpa using a_prime_pow_mod4_eq_1 hp hp1 le_rfl
          rw [hg1, ha1]
          norm_num
        | succ m hm ih =>
          have hadd : ∑ i ∈ Finset.range (m + 2), a (p ^ i) * g0 (p ^ (m + 1 - i)) +
              ∑ i ∈ Finset.range (m + 1), a (p ^ i) * g0 (p ^ (m - i)) = 0 := by
            rw [Finset.sum_range_succ (fun i => a (p ^ i) * g0 (p ^ (m + 1 - i))) (m + 1)]
            rw [add_assoc, add_comm (a (p ^ (m + 1)) * g0 (p ^ (m + 1 - (m + 1)))), ← add_assoc]
            rw [← Finset.sum_add_distrib]
            rw [Finset.sum_range_succ (fun i => a (p ^ i) * g0 (p ^ (m + 1 - i)) +
                a (p ^ i) * g0 (p ^ (m - i))) m]
            have hprefix : ∑ i ∈ Finset.range m,
                (a (p ^ i) * g0 (p ^ (m + 1 - i)) + a (p ^ i) * g0 (p ^ (m - i))) = 0 := by
              apply Finset.sum_eq_zero
              intro i hi
              rw [Finset.mem_range] at hi
              rw [hg0_val (m + 1 - i) (by omega), hg0_val (m - i) (by omega)]
              have hexp : m + 1 - i = (m - i) + 1 := by omega
              rw [hexp, pow_succ]
              ring
            rw [hprefix, zero_add]
            simp only [Nat.sub_self, pow_zero, g0_isMultiplicative.map_one, mul_one]
            rw [show m + 1 - m = 1 by omega, hg0_val 1 le_rfl,
              a_prime_pow_mod4_eq_1 hp hp1 hm, a_prime_pow_mod4_eq_1 hp hp1 (by omega)]
            norm_num
          linarith
      exact hS k hk
    · apply Finset.sum_eq_zero
      intro i hi
      rw [Finset.mem_range] at hi
      by_cases hi0 : i = 0
      · subst hi0
        simp only [Nat.sub_zero]
        rw [g0_prime_pow hp hk]
        simp [hp2, chi, hp3]
      · rw [a_prime_pow_mod4_eq_3 hp hp3 (by omega : 1 ≤ i), zero_mul]

private lemma a_mul_g0_eq_one : a * g0 = 1 := by
  have hmul : (a * g0).IsMultiplicative := a_isMultiplicative.mul g0_isMultiplicative
  ext n
  induction n using Nat.recOnPrimeCoprime with
  | zero => simp
  | prime_pow p k hp =>
    by_cases hk : k = 0
    · subst hk
      simp [hmul.map_one]
    · rw [a_mul_g0_prime_pow hp (by omega : 1 ≤ k)]
      simp [hp.ne_one, hk]
  | coprime m n _ _ hcop ihm ihn =>
    rw [hmul.map_mul_of_coprime hcop, ihm, ihn,
      ArithmeticFunction.isMultiplicative_one.map_mul_of_coprime hcop]

theorem main_proof : ∀ g : ArithmeticFunction ℤ, a * g = 1 → ∀ n : ℕ, 1 ≤ n → |g n| = A091400 n := by
  intro g hg n hn
  have hgg0 : g = g0 := by
    calc g = 1 * g := (one_mul g).symm
      _ = (a * g0) * g := by rw [a_mul_g0_eq_one]
      _ = g0 * (a * g) := by ring
      _ = g0 := by rw [hg, mul_one]
  rw [hgg0, g0_apply_pos (by omega : n ≠ 0), abs_mul, abs_pow]
  simp only [abs_neg, abs_one, one_pow, one_mul]
  exact abs_of_nonneg (A091400_nonneg n)

end OMA.OeisA000089

theorem OMA.solution : type_of% @OMA.S_oeis_a000089.main :=
  OMA.OeisA000089.main_proof
