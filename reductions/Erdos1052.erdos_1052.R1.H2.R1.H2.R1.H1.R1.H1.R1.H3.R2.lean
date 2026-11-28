import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H2.R1.H1.R1.H1.R1.H3.R2 of step Erdos1052.erdos_1052.R1.H2.R1.H2.R1.H1.R1.H1.R1.H3
/-!
For each fixed r below 250100 the two remaining problems bound the exponent.
Both use S.card ≤ 20. A base-two supplier forces r = 1 mod 32. In the other
case r² divides one different odd prime-power unitary factor, or r divides two
different such factors. Finiteness of the range makes the per-r bounds uniform.

The unitary product formula comes from the merged R1.H2.R1 reduction by
adammcarter. The mod-32 order argument adapts the mod-128 argument in PR 8848.
The cardinality estimate is the UnitaryThickKernel result of this project.
-/

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1_H3_R2

private theorem product_bounds (s : Finset ℕ) (t : ℕ → ℚ)
    (ht : ∀ i, 0 ≤ t i) :
    1 + ∑ i ∈ s, t i ≤ ∏ i ∈ s, (1 + t i) ∧
    (∏ i ∈ s, (1 + t i)) - 1 ≤ (∏ i ∈ s, (1 + t i)) * ∑ i ∈ s, t i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have hs : 0 ≤ ∑ i ∈ s, t i := Finset.sum_nonneg fun i _ => ht i
    have hp : 1 ≤ ∏ i ∈ s, (1 + t i) := by linarith [ih.1]
    have h₁ := mul_nonneg (ht a) (sub_nonneg.mpr hp)
    have h₂ := mul_nonneg (mul_nonneg (ht a) (by linarith : 0 ≤ ∏ i ∈ s, (1 + t i)))
      (add_nonneg (ht a) hs)
    constructor <;> nlinarith [ih.1, ih.2]

theorem card_le_twenty (S : Finset ℕ)
    (hadm : ∀ z ∈ S, S.card + 3 ≤ z)
    (hupper : ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097)
    (hthick : 2501 / 2500 < ∏ z ∈ S, (1 + 5 / (z : ℚ))) : S.card ≤ 20 := by
  by_contra! hc
  have hcard : (21 : ℚ) ≤ (S.card : ℚ) := by exact_mod_cast hc
  have hsmall := (product_bounds S (fun z => 24 / (z : ℚ)) (by intros; positivity)).1
  have hlarge := (product_bounds S (fun z => 5 / (z : ℚ)) (by intros; positivity)).2
  have hcompare : ∏ z ∈ S, (1 + 24 / (z : ℚ)) ≤
      ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) := by
    apply Finset.prod_le_prod (fun z _ => by positivity)
    intro z hz
    have hz' : (S.card : ℚ) + 3 ≤ (z : ℚ) := by exact_mod_cast hadm z hz
    have hpos : 0 < (z : ℚ) := by linarith
    have hd : 0 < (z : ℚ) - 2 - (S.card : ℚ) := by linarith
    apply (le_div_iff₀ hd).mpr
    field_simp
    nlinarith [mul_nonneg (sub_nonneg.mpr hcard) hpos.le]
  have hsum : (∑ z ∈ S, 24 / (z : ℚ)) = (24 / 5) * ∑ z ∈ S, 5 / (z : ℚ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    ring
  rw [hsum] at hsmall
  have hb : (∑ z ∈ S, 5 / (z : ℚ)) ≤ 5 / 12582 := by
    linarith [hsmall.trans (hcompare.trans hupper)]
  have hp : 0 ≤ ∏ z ∈ S, (1 + 5 / (z : ℚ)) := by linarith
  nlinarith [mul_nonneg hp (sub_nonneg.mpr hb)]

theorem small_kernel_member (S : Finset ℕ) (hc : S.card ≤ 20)
    (hthick : 2501 / 2500 < ∏ z ∈ S, (1 + 5 / (z : ℚ))) :
    ∃ r ∈ S, r < 250100 := by
  by_contra! hn
  have hc' : (S.card : ℚ) ≤ 20 := by exact_mod_cast hc
  have hs : (∑ z ∈ S, 5 / (z : ℚ)) ≤ 1 / 2501 := calc
    _ ≤ ∑ _z ∈ S, (5 / 250100 : ℚ) := by
      apply Finset.sum_le_sum
      intro z hz
      have hz' : (250100 : ℚ) ≤ z := by exact_mod_cast hn z hz
      exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hz'
    _ ≤ _ := by rw [Finset.sum_const, nsmul_eq_mul]; linarith
  have hlarge := (product_bounds S (fun z => 5 / (z : ℚ)) (by intros; positivity)).2
  have hpos : 0 ≤ ∏ z ∈ S, (1 + 5 / (z : ℚ)) := by linarith
  nlinarith [mul_nonneg hpos (sub_nonneg.mpr hs)]


theorem two_units_of_square {r : ℕ} (hr : r.Prime) (s : Finset ℕ) (f : ℕ → ℕ)
    (h : r ^ 2 ∣ ∏ p ∈ s, f p) :
    (∃ p ∈ s, r ^ 2 ∣ f p) ∨
      ∃ p ∈ s, ∃ q ∈ s, p ≠ q ∧ r ∣ f p ∧ r ∣ f q := by
  by_cases hs : ∃ p ∈ s, r ^ 2 ∣ f p
  · exact Or.inl hs
  right
  have h1 : r ∣ ∏ p ∈ s, f p := (dvd_pow_self r (by decide : 2 ≠ 0)).trans h
  obtain ⟨p, hp, hd⟩ := (Prime.dvd_finsetProd_iff hr.prime _).mp h1
  obtain ⟨j, hj⟩ := hd
  have hn : ¬ r ∣ j := by
    intro hh
    exact hs ⟨p, hp, by rw [hj, pow_two]; exact mul_dvd_mul_left r hh⟩
  rw [← Finset.mul_prod_erase s f hp, hj, pow_two, mul_assoc] at h
  have hrest := (Nat.mul_dvd_mul_iff_left hr.pos).mp h
  obtain ⟨q, hq, hqd⟩ := (Prime.dvd_finsetProd_iff hr.prime _).mp
    ((hr.dvd_mul.mp hrest).resolve_left hn)
  exact ⟨p, hp, q, Finset.mem_of_mem_erase hq, (Finset.ne_of_mem_erase hq).symm,
    ⟨j, hj⟩, hqd⟩

theorem supplier_ne {n r p : ℕ} (hr : r.Prime) (hp : p ∈ n.primeFactors)
    (hno : ¬ r ∣ 2 ^ padicValNat 2 n + 1)
    (hpr : r ∣ 1 + p ^ n.factorization p) : p ≠ 2 ∧ p ≠ r := by
  rw [add_comm] at hpr
  constructor
  · rintro rfl
    rw [Nat.factorization_def n Nat.prime_two] at hpr
    exact hno hpr
  · rintro rfl
    have he : n.factorization p ≠ 0 := Finsupp.mem_support_iff.mp
      (show p ∈ n.factorization.support by simpa using hp)
    exact hr.not_dvd_one ((Nat.dvd_add_right (dvd_pow_self p he)).mp hpr)

theorem odd_square_suppliers {n r : ℕ} (hr : r.Prime) (hrn : r ^ 2 ∣ n)
    (hprod : ∏ p ∈ n.primeFactors, (1 + p ^ n.factorization p) = 2 * n)
    (hno : ¬ r ∣ 2 ^ padicValNat 2 n + 1) :
    (∃ p ∈ n.primeFactors, p ≠ 2 ∧ p ≠ r ∧ r ^ 2 ∣ p ^ n.factorization p + 1) ∨
    (∃ p ∈ n.primeFactors, ∃ q ∈ n.primeFactors, p ≠ q ∧ p ≠ 2 ∧ p ≠ r ∧ q ≠ 2 ∧ q ≠ r ∧
      r ∣ p ^ n.factorization p + 1 ∧ r ∣ q ^ n.factorization q + 1) := by
  have hd : r ^ 2 ∣ ∏ p ∈ n.primeFactors, (1 + p ^ n.factorization p) := by
    rw [hprod]
    exact dvd_mul_of_dvd_right hrn _
  rcases two_units_of_square hr _ _ hd with ⟨p, hp, hd⟩ | ⟨p, hp, q, hq, hn, h1, h2⟩
  · have hne := supplier_ne hr hp hno ((dvd_pow_self r (by decide : 2 ≠ 0)).trans hd)
    exact Or.inl ⟨p, hp, hne.1, hne.2, by rwa [add_comm]⟩
  · have hpne := supplier_ne hr hp hno h1
    have hqne := supplier_ne hr hq hno h2
    exact Or.inr ⟨p, hp, q, hq, hn, hpne.1, hpne.2, hqne.1, hqne.2, by rwa [add_comm],
      by rwa [add_comm]⟩

private theorem uniform_bound (m : ℕ) (b₁ b₂ : ℕ → ℕ) :
    ∃ A : ℕ, ∀ r < m, b₁ r ≤ A ∧ b₂ r ≤ A := by
  refine ⟨(Finset.range m).sup (fun r => max (b₁ r) (b₂ r)), ?_⟩
  intro r hr
  have h := Finset.le_sup (s := Finset.range m) (f := fun t => max (b₁ t) (b₂ t))
    (Finset.mem_range.mpr hr)
  exact ⟨(le_max_left _ _).trans h, (le_max_right _ _).trans h⟩

-- Generalizes the modular-order argument of adammcarter in PR 8848.
private theorem neg_one_of_dvd {z a : ℕ} (hd : z ∣ 2 ^ a + 1) : (2 : ZMod z) ^ a = -1 := by
  have h0 : ((2 ^ a + 1 : ℕ) : ZMod z) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
  push_cast at h0
  exact eq_neg_of_add_eq_zero_left h0

private theorem neg_one_ne_one {z : ℕ} (hz : 2 < z) : (-1 : ZMod z) ≠ 1 := by
  intro h
  have e5 : (2 : ZMod z) = 0 := by linear_combination -h
  have h2 : ((2 : ℕ) : ZMod z) = 0 := by exact_mod_cast e5
  have h3 := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff 2 z).mp h2)
  omega

-- If 2^(c t) = 1 mod z with t odd, then z does not divide 2^a + 1 for any multiple a of c.
private theorem no_div {z a c t : ℕ} (hz : 2 < z) (ht : Odd t) (h1 : (2 ^ c) ^ t % z = 1) (hc : c ∣ a)
    (hd : z ∣ 2 ^ a + 1) : False := by
  obtain ⟨k, rfl⟩ := hc
  have e1 := neg_one_of_dvd hd
  have e2 : ((2 : ZMod z) ^ c) ^ t = 1 := by
    have h0 : (((2 ^ c) ^ t : ℕ) : ZMod z) = ((1 : ℕ) : ZMod z) := by
      rw [ZMod.natCast_eq_natCast_iff']
      rw [h1, Nat.mod_eq_of_lt (by omega)]
    push_cast at h0
    exact h0
  have e3 : ((2 : ZMod z) ^ (c * k)) ^ t = -1 := by rw [e1, ht.neg_one_pow]
  have e4 : ((2 : ZMod z) ^ (c * k)) ^ t = 1 := by
    rw [← pow_mul, mul_right_comm, pow_mul, pow_mul, e2, one_pow]
  exact neg_one_ne_one hz (e3.symm.trans e4)


theorem direct_order_dvd {z a k : ℕ} (hzp : z.Prime) (hz : 2 < z)
    (hk : 2^k ∣ a) (hd : z ∣ 2^a + 1) : 2^(k+1) ∣ z-1 := by
  let _ : Fact z.Prime := ⟨hzp⟩
  obtain ⟨m, rfl⟩ := hk
  have hx : ((2 : ZMod z)^m)^(2^k) = -1 := by
    rw [← pow_mul, mul_comm]; exact neg_one_of_dvd hd
  have hord : orderOf ((2 : ZMod z)^m) = 2^(k+1) :=
    orderOf_eq_prime_pow (p := 2) (n := k)
      (by rw [hx]; exact neg_one_ne_one hz)
      (by rw [pow_succ, pow_mul, hx]; norm_num)
  have hxn : (2 : ZMod z)^m ≠ 0 := fun h0 => by
    rw [h0, zero_pow (by positivity)] at hx
    exact one_ne_zero (neg_eq_zero.mp hx.symm)
  exact hord ▸ ZMod.orderOf_dvd_card_sub_one hxn

private theorem square_residue {a b r z j : ℕ} (h : 2^j ≡ a [MOD z])
    (hj : j+j = b) (hr : a*a ≡ r [MOD z]) : 2^b ≡ r [MOD z] := by
  subst b
  rw [pow_add]
  exact (h.mul h).trans hr

private theorem residue_163841 : (2^16384)^5 % 163841 = 1 := by
  have h128 : 2^128 ≡ 160720 [MOD 163841] := by decide
  have h256 : 2^256 ≡ 74022 [MOD 163841] := square_residue h128 (by decide) (by decide)
  have h512 : 2^512 ≡ 85762 [MOD 163841] := square_residue h256 (by decide) (by decide)
  have h1024 : 2^1024 ≡ 134313 [MOD 163841] := square_residue h512 (by decide) (by decide)
  have h2048 : 2^2048 ≡ 104823 [MOD 163841] := square_residue h1024 (by decide) (by decide)
  have h4096 : 2^4096 ≡ 28505 [MOD 163841] := square_residue h2048 (by decide) (by decide)
  have h8192 : 2^8192 ≡ 47506 [MOD 163841] := square_residue h4096 (by decide) (by decide)
  have h16384 : 2^16384 ≡ 74102 [MOD 163841] := square_residue h8192 (by decide) (by decide)
  exact (h16384.pow 5).trans (by decide : _ ≡ 1 [MOD 163841])

theorem direct_upper {z a : ℕ} (hzp : z.Prime) (hz : 2 < z) (hlim : z < 250100)
    (hd : z ∣ 2^a + 1) : ¬ 16384 ∣ a := by
  intro h
  have ht : 2^14 ∣ a := h
  obtain ⟨j, hj⟩ := direct_order_dvd hzp hz ht hd
  norm_num at hj
  have hzj : z = 32768*j+1 := by omega
  have hjlo : 1 ≤ j := by omega
  have hjhi : j ≤ 7 := by omega
  subst z
  interval_cases j <;> norm_num at hzp
  · exact no_div (z := 65537) (c := 32) (t := 1) (by norm_num) (by decide) (by norm_num) (dvd_trans (by decide : 32 ∣ 16384) h) hd
  · exact no_div (z := 163841) (c := 16384) (t := 5) (by norm_num) (by decide) residue_163841 h hd


private theorem direct_mod_32 {r a : ℕ} (hr : r.Prime) (hgt : 2 < r) (h16 : 16 ∣ a)
    (hbase : r ∣ 2 ^ a + 1) : r % 32 = 1 := by
  have hord := direct_order_dvd (k := 4) hr hgt h16 hbase
  norm_num at hord
  omega


def H1 : Prop :=
  ∀ r : ℕ, r < 250100 → ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ¬ Squarefree (n / 2 ^ padicValNat 2 n) →
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
    (∀ q : ℕ, q.Prime → q ∣ n → q < 1899 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 991 ∨ q = 1783) →
    223 ∣ n → 991 ∣ n → 1783 ∣ n → 48 ≤ padicValNat 2 n →
    2501 / 2500 < ∏ z ∈ S, (1 + 5 / (z : ℚ)) →
    S.card ≤ 20 → r ∈ S →
    r ∣ 2 ^ padicValNat 2 n + 1 → r % 32 = 1 → ¬ 16384 ∣ padicValNat 2 n → padicValNat 2 n ≤ A

def H2 : Prop :=
  ∀ r : ℕ, r < 250100 → ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ¬ Squarefree (n / 2 ^ padicValNat 2 n) →
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
    (∀ q : ℕ, q.Prime → q ∣ n → q < 1899 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 991 ∨ q = 1783) →
    223 ∣ n → 991 ∣ n → 1783 ∣ n → 48 ≤ padicValNat 2 n →
    2501 / 2500 < ∏ z ∈ S, (1 + 5 / (z : ℚ)) →
    S.card ≤ 20 → r ∈ S →
    (¬ r ∣ 2 ^ padicValNat 2 n + 1) →
    ((∃ p ∈ n.primeFactors, p ≠ 2 ∧ p ≠ r ∧ r ^ 2 ∣ p ^ n.factorization p + 1) ∨
      (∃ p ∈ n.primeFactors, ∃ q ∈ n.primeFactors, p ≠ q ∧ p ≠ 2 ∧ p ≠ r ∧ q ≠ 2 ∧ q ≠ r ∧
        r ∣ p ^ n.factorization p + 1 ∧ r ∣ q ^ n.factorization q + 1)) → padicValNat 2 n ≤ A

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1.H3 := by
  classical
  intro h₁ h₂
  let b₁ (r : ℕ) := if h : r < 250100 then (h₁ r h).choose else 0
  let b₂ (r : ℕ) := if h : r < 250100 then (h₂ r h).choose else 0
  obtain ⟨A, hA⟩ := uniform_bound 250100 b₁ b₂
  refine ⟨A, ?_⟩
  intro n hn hs S hS hadm hu h4 h3 h5 h7 h19 hN h16 h64 h31 hq h223 h991 h1783 h48 ht
  have hc := card_le_twenty S (fun z hz => (hadm z hz).2) hu ht
  obtain ⟨r, hr, hlt⟩ := small_kernel_member S hc ht
  obtain ⟨hrp, _, hrsq⟩ := (hS r).mp hr
  by_cases hbase : r ∣ 2 ^ padicValNat 2 n + 1
  · have hrgt : 2 < r := lt_of_lt_of_le (by decide : 2 < 128) (hadm r hr).1
    have h32 := direct_mod_32 hrp hrgt h16 hbase
    apply le_trans _ (hA r hlt).1
    simpa only [b₁, dif_pos hlt] using
      (h₁ r hlt).choose_spec n hn hs S hS hadm hu h4 h3 h5 h7 h19 hN h16 h64 h31 hq h223
        h991 h1783 h48 ht hc hr hbase h32 (direct_upper hrp hrgt hlt hbase)
  · have hsup := odd_square_suppliers hrp hrsq
      (OMA.R_Erdos1052_erdos_1052_R1_H2_R1.prod_eq_two_mul hn) hbase
    apply le_trans _ (hA r hlt).2
    simpa only [b₂, dif_pos hlt] using
      (h₂ r hlt).choose_spec n hn hs S hS hadm hu h4 h3 h5 h7 h19 hN h16 h64 h31 hq h223
        h991 h1783 h48 ht hc hr hbase hsup

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1_H3_R2
