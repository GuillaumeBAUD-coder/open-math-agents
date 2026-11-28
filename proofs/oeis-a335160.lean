import OMAStatements.S_oeis_a335160

-- Problem: A335160: a(n) = nim-product of 2^3 and 2^n.
-- Credit: @ceejcake
-- Proof:
-- 1. Define the explicit GF(16) nim-multiplication formula `nm16` on Fin 16 and verify its
--    closure, distributivity, no-zero-divisors, surjectivity, and mex properties on Fin 16.
-- 2. By strong induction on a + b, `nimMul a b = nm16 a b` for all a, b < 16.
-- 3. By strong induction on a + b, prove Conway's Fermat 2-power scaling theorem for F = 16:
--      ∀ a < 16, ∀ b : ℕ, nimMul a b = 16 * nimMul a (b / 16) ^^^ nimMul a (b % 16).
-- 4. Specializing to a = 8 and b = 2^n (n > 3) gives a(n) = 16 * a(n - 4), and base cases
--    a(0..3) = 8, 12, 11, 13 yield the rational generating function.

namespace ProofA335160

open OMA.S_oeis_a335160 PowerSeries

-- Part 1: Computable GF(16) nim-multiplication and its finite properties (before Classical)
private def nm4 (a b : ℕ) : ℕ :=
  let a1 := a / 2; let a0 := a % 2
  let b1 := b / 2; let b0 := b % 2
  let c1 := (a1 * b0) ^^^ (a0 * b1) ^^^ (a1 * b1)
  let c0 := (a0 * b0) ^^^ (a1 * b1)
  2 * c1 + c0

private def nm16 (a b : ℕ) : ℕ :=
  let a1 := a / 4; let a0 := a % 4
  let b1 := b / 4; let b0 := b % 4
  let c1 := nm4 a1 b0 ^^^ nm4 a0 b1 ^^^ nm4 a1 b1
  let c0 := nm4 a0 b0 ^^^ nm4 2 (nm4 a1 b1)
  4 * c1 + c0

private lemma nm16_lt : ∀ a b : Fin 16, nm16 a.1 b.1 < 16 := by decide

private lemma nm16_comm : ∀ a b : Fin 16, nm16 a.1 b.1 = nm16 b.1 a.1 := by decide

private lemma nm16_distrib_left : ∀ a b c : Fin 16,
    nm16 (a.1 ^^^ b.1) c.1 = nm16 a.1 c.1 ^^^ nm16 b.1 c.1 := by decide

private lemma nm16_no_zero_div : ∀ a b : Fin 16, nm16 a.1 b.1 = 0 → a.1 = 0 ∨ b.1 = 0 := by decide

private lemma nm16_surj : ∀ d : Fin 16, d.1 ≠ 0 → ∀ v : Fin 16, ∃ r : Fin 16, nm16 d.1 r.1 = v.1 := by decide

private lemma nm16_mex_lt : ∀ a b m : Fin 16, m.1 < nm16 a.1 b.1 →
    ∃ a' : Fin 16, a'.1 < a.1 ∧ ∃ b' : Fin 16, b'.1 < b.1 ∧
      m.1 = nm16 a'.1 b.1 ^^^ nm16 a.1 b'.1 ^^^ nm16 a'.1 b'.1 := by decide +kernel

private lemma nm16_base :
    nm16 8 1 = 8 ∧ nm16 8 2 = 12 ∧ nm16 8 4 = 11 ∧ nm16 8 8 = 13 := by decide

private lemma xor_lt_16 : ∀ a b : Fin 16, (a.1 ^^^ b.1) < 16 := by decide

section
open scoped Classical

-- Bitwise XOR helpers for F = 16 = 2^4
private lemma xor_div16 (x y : ℕ) : (x ^^^ y) / 16 = x / 16 ^^^ y / 16 := by
  have h : (16 : ℕ) = 2 ^ 4 := rfl
  rw [h, ← Nat.shiftRight_eq_div_pow, ← Nat.shiftRight_eq_div_pow, ← Nat.shiftRight_eq_div_pow,
    Nat.shiftRight_xor_distrib]

private lemma xor_mod16 (x y : ℕ) : (x ^^^ y) % 16 = x % 16 ^^^ y % 16 := by
  have h : (16 : ℕ) = 2 ^ 4 := rfl
  rw [h, Nat.xor_mod_two_pow]

private lemma mul16_xor_add (q r : ℕ) (hr : r < 16) : 16 * q ^^^ r = 16 * q + r := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_xor]
  by_cases hk : k < 4
  · have hq : (16 * q).testBit k = false := by
      have : 16 * q = q <<< 4 := by rw [Nat.shiftLeft_eq]; ring
      rw [this, Nat.testBit_shiftLeft]; simp [show ¬ (4 ≤ k) by omega]
    have hadd : (16 * q + r).testBit k = r.testBit k := by
      have h1 := Nat.testBit_mod_two_pow (16 * q + r) 4 k
      simp [hk, Nat.mod_eq_of_lt hr] at h1
      exact h1.symm
    rw [hq, Bool.false_xor, hadd]
  · have h16le : 16 ≤ 2 ^ k := by
      have : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have hr0 : r.testBit k = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le hr h16le)
    have hadd : (16 * q + r).testBit k = (16 * q).testBit k := by
      rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
      have hdiv : (16 * q + r) / 2 ^ k = (16 * q) / 2 ^ k := by
        have hpow : 16 ∣ 2 ^ k := by
          have : 2 ^ k = 16 * 2 ^ (k - 4) := by
            have hk4 : k = 4 + (k - 4) := by omega
            conv_lhs => rw [hk4]
            rw [pow_add]; norm_num
          exact ⟨2 ^ (k - 4), this⟩
        rcases hpow with ⟨t, ht⟩
        rw [ht, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
        congr 1; omega
      rw [hdiv]
    rw [hr0, Bool.xor_false, hadd]

private lemma div16_mul16_xor (q r : ℕ) (hr : r < 16) : (16 * q ^^^ r) / 16 = q := by
  rw [mul16_xor_add q r hr]; omega

private lemma mod16_mul16_xor (q r : ℕ) (hr : r < 16) : (16 * q ^^^ r) % 16 = r := by
  rw [mul16_xor_add q r hr]; omega

private lemma nimMul_eq_sInf (a b : ℕ) :
    nimMul a b = sInf {m : ℕ | ∀ a' < a, ∀ b' < b, m ≠ nimMul a' b ^^^ nimMul a b' ^^^ nimMul a' b'} := by
  rw [nimMul]

private lemma nimMul_mem_set (a b : ℕ) :
    ∀ a' < a, ∀ b' < b, nimMul a b ≠ nimMul a' b ^^^ nimMul a b' ^^^ nimMul a' b' := by
  let S := {m : ℕ | ∀ a' < a, ∀ b' < b, m ≠ nimMul a' b ^^^ nimMul a b' ^^^ nimMul a' b'}
  have hne : S.Nonempty := by
    let bad := (Finset.range a ×ˢ Finset.range b).image (fun p => nimMul p.1 b ^^^ nimMul a p.2 ^^^ nimMul p.1 p.2)
    obtain ⟨m, hm⟩ := Infinite.exists_notMem_finset bad
    refine ⟨m, fun a' ha' b' hb' heq => hm ?_⟩
    exact Finset.mem_image.mpr ⟨(a', b'), Finset.mem_product.mpr ⟨Finset.mem_range.mpr ha', Finset.mem_range.mpr hb'⟩, heq.symm⟩
  have hmem : sInf S ∈ S := Nat.sInf_mem hne
  rw [← nimMul_eq_sInf] at hmem
  exact hmem

private lemma nimMul_lt_witness {a b m : ℕ} (hm : m < nimMul a b) :
    ∃ a' < a, ∃ b' < b, m = nimMul a' b ^^^ nimMul a b' ^^^ nimMul a' b' := by
  by_contra h
  push_neg at h
  have hmem : m ∈ {m : ℕ | ∀ a' < a, ∀ b' < b, m ≠ nimMul a' b ^^^ nimMul a b' ^^^ nimMul a' b'} := h
  have hle : nimMul a b ≤ m := by rw [nimMul_eq_sInf]; exact Nat.sInf_le hmem
  omega

private lemma nimMul_eq_of_mex {a b M : ℕ}
    (h1 : ∀ a' < a, ∀ b' < b, M ≠ nimMul a' b ^^^ nimMul a b' ^^^ nimMul a' b')
    (h2 : ∀ m < M, ∃ a' < a, ∃ b' < b, m = nimMul a' b ^^^ nimMul a b' ^^^ nimMul a' b') :
    nimMul a b = M := by
  apply le_antisymm
  · rw [nimMul_eq_sInf]; exact Nat.sInf_le h1
  · by_contra hlt; push_neg at hlt
    rcases h2 (nimMul a b) hlt with ⟨a', ha', b', hb', heq⟩
    exact nimMul_mem_set a b a' ha' b' hb' heq

private lemma nimMul_zero_right (a : ℕ) : nimMul a 0 = 0 := by
  apply nimMul_eq_of_mex
  · intro _ _ _ hb; omega
  · intro _ hm; omega

private lemma xor_eq_zero_imp {a b : ℕ} (h : a ^^^ b = 0) : a = b := by
  apply Nat.eq_of_testBit_eq; intro k
  have hk := congr_arg (fun x => x.testBit k) h
  simp only [Nat.testBit_xor, Nat.zero_testBit] at hk
  cases ha : a.testBit k <;> cases hb : b.testBit k <;> simp [ha, hb] at hk ⊢

-- Part 2: nimMul agrees with nm16 on [0, 16) x [0, 16)
private lemma nm16_mex_ne {a b a' b' : ℕ} (ha : a < 16) (hb : b < 16) (ha' : a' < a) (hb' : b' < b) :
    nm16 a b ≠ nm16 a' b ^^^ nm16 a b' ^^^ nm16 a' b' := by
  intro heq
  have hx : (a ^^^ a') < 16 := xor_lt_16 ⟨a, ha⟩ ⟨a', by omega⟩
  have hy : (b ^^^ b') < 16 := xor_lt_16 ⟨b, hb⟩ ⟨b', by omega⟩
  have hdist1 : nm16 (a ^^^ a') b = nm16 a b ^^^ nm16 a' b := nm16_distrib_left ⟨a, ha⟩ ⟨a', by omega⟩ ⟨b, hb⟩
  have hdist2 : nm16 (a ^^^ a') b' = nm16 a b' ^^^ nm16 a' b' := nm16_distrib_left ⟨a, ha⟩ ⟨a', by omega⟩ ⟨b', by omega⟩
  have hdist3 : nm16 (a ^^^ a') (b ^^^ b') = nm16 (a ^^^ a') b ^^^ nm16 (a ^^^ a') b' := by
    rw [nm16_comm ⟨a ^^^ a', hx⟩ ⟨b ^^^ b', hy⟩, nm16_distrib_left ⟨b, hb⟩ ⟨b', by omega⟩ ⟨a ^^^ a', hx⟩,
      nm16_comm ⟨b, hb⟩ ⟨a ^^^ a', hx⟩, nm16_comm ⟨b', by omega⟩ ⟨a ^^^ a', hx⟩]
  have hzero : nm16 (a ^^^ a') (b ^^^ b') = 0 := by
    rw [hdist3, hdist1, hdist2, heq]
    simp [Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm]
  rcases nm16_no_zero_div ⟨a ^^^ a', hx⟩ ⟨b ^^^ b', hy⟩ hzero with h0 | h0
  · dsimp only at h0
    have : a = a' := xor_eq_zero_imp h0
    omega
  · dsimp only at h0
    have : b = b' := xor_eq_zero_imp h0
    omega

private lemma nimMul_eq_nm16 : ∀ s a b : ℕ, a + b = s → a < 16 → b < 16 → nimMul a b = nm16 a b := by
  intro s
  induction s using Nat.strong_induction_on with
  | h s ih =>
    intro a b hsum ha hb
    apply nimMul_eq_of_mex
    · intro a' ha' b' hb'
      rw [ih (a' + b) (by omega) a' b rfl (by omega) hb,
          ih (a + b') (by omega) a b' rfl ha (by omega),
          ih (a' + b') (by omega) a' b' rfl (by omega) (by omega)]
      exact nm16_mex_ne ha hb ha' hb'
    · intro m hm
      have hm16 : m < 16 := lt_trans hm (nm16_lt ⟨a, ha⟩ ⟨b, hb⟩)
      rcases nm16_mex_lt ⟨a, ha⟩ ⟨b, hb⟩ ⟨m, hm16⟩ hm with ⟨a', ha', b', hb', heq⟩
      dsimp only at ha' hb'
      refine ⟨a'.1, ha', b'.1, hb', ?_⟩
      rw [ih (a'.1 + b) (by omega) a'.1 b rfl a'.2 hb,
          ih (a + b'.1) (by omega) a b'.1 rfl ha b'.2,
          ih (a'.1 + b'.1) (by omega) a'.1 b'.1 rfl a'.2 b'.2]
      exact heq

-- Part 3: Conway's Fermat 2-power scaling theorem for F = 16
private lemma nimMul_scale16 : ∀ s a b : ℕ, a + b = s → a < 16 →
    nimMul a b = 16 * nimMul a (b / 16) ^^^ nimMul a (b % 16) := by
  intro s
  induction s using Nat.strong_induction_on with
  | h s ih =>
    intro a b hsum ha
    let q := b / 16
    let r := b % 16
    have hr16 : r < 16 := Nat.mod_lt b (by omega)
    have hnr16 : nimMul a r < 16 := by
      rw [nimMul_eq_nm16 (a + r) a r rfl ha hr16]; exact nm16_lt ⟨a, ha⟩ ⟨r, hr16⟩
    apply nimMul_eq_of_mex
    · intro a' ha' b' hb' heq
      let q' := b' / 16
      let r' := b' % 16
      have hr'16 : r' < 16 := Nat.mod_lt b' (by omega)
      have ha'16 : a' < 16 := by omega
      rw [ih (a' + b) (by omega) a' b rfl ha'16,
          ih (a + b') (by omega) a b' rfl ha,
          ih (a' + b') (by omega) a' b' rfl ha'16] at heq
      have hdiv := congr_arg (· / 16) heq
      have hmod := congr_arg (· % 16) heq
      have hna'r : nimMul a' r < 16 := by rw [nimMul_eq_nm16 (a' + r) a' r rfl ha'16 hr16]; exact nm16_lt ⟨a', ha'16⟩ ⟨r, hr16⟩
      have hnar' : nimMul a r' < 16 := by rw [nimMul_eq_nm16 (a + r') a r' rfl ha hr'16]; exact nm16_lt ⟨a, ha⟩ ⟨r', hr'16⟩
      have hna'r' : nimMul a' r' < 16 := by rw [nimMul_eq_nm16 (a' + r') a' r' rfl ha'16 hr'16]; exact nm16_lt ⟨a', ha'16⟩ ⟨r', hr'16⟩
      rw [div16_mul16_xor _ _ hnr16, xor_div16, xor_div16,
          div16_mul16_xor _ _ hna'r, div16_mul16_xor _ _ hnar', div16_mul16_xor _ _ hna'r'] at hdiv
      rw [mod16_mul16_xor _ _ hnr16, xor_mod16, xor_mod16,
          mod16_mul16_xor _ _ hna'r, mod16_mul16_xor _ _ hnar', mod16_mul16_xor _ _ hna'r'] at hmod
      by_cases hq : q' < q
      · exact nimMul_mem_set a q a' ha' q' hq hdiv
      · have hqeq : q' = q := by omega
        have hrlt : r' < r := by omega
        exact nimMul_mem_set a r a' ha' r' hrlt hmod
    · intro m hm
      rw [mul16_xor_add _ _ hnr16] at hm
      have hdiv_mod : ∀ x y : ℕ, x / 16 = y / 16 → x % 16 = y % 16 → x = y := fun x y h1 h2 => by omega
      have hv16 : m % 16 < 16 := Nat.mod_lt m (by omega)
      by_cases hu : m / 16 < nimMul a (b / 16)
      · -- Case A: m / 16 < nimMul a q
        rcases nimMul_lt_witness hu with ⟨a', ha', q', hq', hu_eq⟩
        have ha'16 : a' < 16 := by omega
        have hdiff_lt : (a ^^^ a') < 16 := xor_lt_16 ⟨a, ha⟩ ⟨a', ha'16⟩
        have hdiff_ne : (a ^^^ a') ≠ 0 := fun h => by have := xor_eq_zero_imp h; omega
        have hna'r : nimMul a' (b % 16) < 16 := by rw [nimMul_eq_nm16 (a' + b % 16) a' (b % 16) rfl ha'16 hr16]; exact nm16_lt ⟨a', ha'16⟩ ⟨b % 16, hr16⟩
        have htarget_lt : (m % 16 ^^^ nm16 a' (b % 16)) < 16 :=
          xor_lt_16 ⟨m % 16, hv16⟩ ⟨nm16 a' (b % 16), nm16_lt ⟨a', ha'16⟩ ⟨b % 16, hr16⟩⟩
        rcases nm16_surj ⟨a ^^^ a', hdiff_lt⟩ hdiff_ne ⟨m % 16 ^^^ nm16 a' (b % 16), htarget_lt⟩ with ⟨r', hr'_eq⟩
        let b' := 16 * q' + r'.1
        have hb' : b' < b := by have := r'.2; omega
        refine ⟨a', ha', b', hb', ?_⟩
        rw [ih (a' + b) (by omega) a' b rfl ha'16,
            ih (a + b') (by omega) a b' rfl ha,
            ih (a' + b') (by omega) a' b' rfl ha'16]
        have hb'd : b' / 16 = q' := by have := r'.2; omega
        have hb'm : b' % 16 = r'.1 := by have := r'.2; omega
        rw [hb'd, hb'm]
        have hlow : nimMul a' (b % 16) ^^^ nimMul a r'.1 ^^^ nimMul a' r'.1 = m % 16 := by
          rw [nimMul_eq_nm16 (a' + b % 16) a' (b % 16) rfl ha'16 hr16,
              nimMul_eq_nm16 (a + r'.1) a r'.1 rfl ha r'.2,
              nimMul_eq_nm16 (a' + r'.1) a' r'.1 rfl ha'16 r'.2]
          have hdist := nm16_distrib_left ⟨a, ha⟩ ⟨a', ha'16⟩ r'
          rw [Nat.xor_assoc, ← hdist, hr'_eq]
          simp [Nat.xor_left_comm]
        have hnar' : nimMul a r'.1 < 16 := by rw [nimMul_eq_nm16 (a + r'.1) a r'.1 rfl ha r'.2]; exact nm16_lt ⟨a, ha⟩ r'
        have hna'r' : nimMul a' r'.1 < 16 := by rw [nimMul_eq_nm16 (a' + r'.1) a' r'.1 rfl ha'16 r'.2]; exact nm16_lt ⟨a', ha'16⟩ r'
        apply hdiv_mod
        · rw [xor_div16, xor_div16, div16_mul16_xor _ _ hna'r, div16_mul16_xor _ _ hnar', div16_mul16_xor _ _ hna'r']
          exact hu_eq
        · rw [xor_mod16, xor_mod16, mod16_mul16_xor _ _ hna'r, mod16_mul16_xor _ _ hnar', mod16_mul16_xor _ _ hna'r']
          exact hlow.symm
      · -- Case B: m / 16 = nimMul a (b / 16) and m % 16 < nimMul a (b % 16)
        have hu_eq : m / 16 = nimMul a (b / 16) := by omega
        have hv_lt : m % 16 < nimMul a (b % 16) := by dsimp only [r] at hm; omega
        rcases nimMul_lt_witness hv_lt with ⟨a', ha', r', hr', hv_eq⟩
        have ha'16 : a' < 16 := by omega
        have hr'16 : r' < 16 := by omega
        let b' := 16 * (b / 16) + r'
        have hb' : b' < b := by omega
        refine ⟨a', ha', b', hb', ?_⟩
        rw [ih (a' + b) (by omega) a' b rfl ha'16,
            ih (a + b') (by omega) a b' rfl ha,
            ih (a' + b') (by omega) a' b' rfl ha'16]
        have hb'd : b' / 16 = b / 16 := by omega
        have hb'm : b' % 16 = r' := by omega
        rw [hb'd, hb'm]
        have hna'r : nimMul a' (b % 16) < 16 := by rw [nimMul_eq_nm16 (a' + b % 16) a' (b % 16) rfl ha'16 hr16]; exact nm16_lt ⟨a', ha'16⟩ ⟨b % 16, hr16⟩
        have hnar' : nimMul a r' < 16 := by rw [nimMul_eq_nm16 (a + r') a r' rfl ha hr'16]; exact nm16_lt ⟨a, ha⟩ ⟨r', hr'16⟩
        have hna'r' : nimMul a' r' < 16 := by rw [nimMul_eq_nm16 (a' + r') a' r' rfl ha'16 hr'16]; exact nm16_lt ⟨a', ha'16⟩ ⟨r', hr'16⟩
        apply hdiv_mod
        · rw [xor_div16, xor_div16, div16_mul16_xor _ _ hna'r, div16_mul16_xor _ _ hnar', div16_mul16_xor _ _ hna'r']
          rw [hu_eq]; simp [Nat.xor_left_comm]
        · rw [xor_mod16, xor_mod16, mod16_mul16_xor _ _ hna'r, mod16_mul16_xor _ _ hnar', mod16_mul16_xor _ _ hna'r']
          exact hv_eq

-- Part 4: Main theorem for A335160
theorem main :
    (∀ n : ℕ, 3 < n → a n = 16 * a (n - 4)) ∧
    ((1 - 2 * X) * (1 + 2 * X) * (1 + 4 * X ^ 2) * PowerSeries.mk (fun n => (a n : ℤ)) =
      (8 + 12 * X + 11 * X ^ 2 + 13 * X ^ 3 : PowerSeries ℤ)) := by
  have hrec : ∀ n : ℕ, 3 < n → a n = 16 * a (n - 4) := by
    intro n hn
    unfold a
    have hpow : 2 ^ n = 16 * 2 ^ (n - 4) := by
      have : n = 4 + (n - 4) := by omega
      conv_lhs => rw [this]
      rw [pow_add]; norm_num
    rw [nimMul_scale16 (2 ^ 3 + 2 ^ n) (2 ^ 3) (2 ^ n) rfl (by norm_num), hpow]
    have hd : 16 * 2 ^ (n - 4) / 16 = 2 ^ (n - 4) := by omega
    have hm : 16 * 2 ^ (n - 4) % 16 = 0 := by omega
    rw [hd, hm, nimMul_zero_right, Nat.xor_zero]
  refine ⟨hrec, ?_⟩
  have ha0 : a 0 = 8 := by unfold a; rw [nimMul_eq_nm16 _ _ _ rfl (by norm_num) (by norm_num)]; exact nm16_base.1
  have ha1 : a 1 = 12 := by unfold a; rw [nimMul_eq_nm16 _ _ _ rfl (by norm_num) (by norm_num)]; exact nm16_base.2.1
  have ha2 : a 2 = 11 := by unfold a; rw [nimMul_eq_nm16 _ _ _ rfl (by norm_num) (by norm_num)]; exact nm16_base.2.2.1
  have ha3 : a 3 = 13 := by unfold a; rw [nimMul_eq_nm16 _ _ _ rfl (by norm_num) (by norm_num)]; exact nm16_base.2.2.2
  let f : PowerSeries ℤ := PowerSeries.mk (fun n => (a n : ℤ))
  have hlhs : (1 - 2 * X) * (1 + 2 * X) * (1 + 4 * X ^ 2) * f = f - PowerSeries.C 16 * (X ^ 4 * f) := by
    simp only [map_ofNat]; ring
  have hrhs : (8 + 12 * X + 11 * X ^ 2 + 13 * X ^ 3 : PowerSeries ℤ) =
      PowerSeries.C 8 + PowerSeries.C 12 * X ^ 1 + PowerSeries.C 11 * X ^ 2 + PowerSeries.C 13 * X ^ 3 := by
    simp only [map_ofNat]; ring
  rw [hlhs, hrhs]
  ext k
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_C, PowerSeries.coeff_X_pow, f, PowerSeries.coeff_mk]
  match k with
  | 0 => simp [ha0]
  | 1 => simp [ha1]
  | 2 => simp [ha2]
  | 3 => simp [ha3]
  | m + 4 =>
    have hr := hrec (m + 4) (by omega)
    simp only [show m + 4 ≠ 0 by omega, show m + 4 ≠ 1 by omega, show m + 4 ≠ 2 by omega,
      show m + 4 ≠ 3 by omega, show 4 ≤ m + 4 by omega, ↓reduceIte, mul_zero, add_zero]
    have hsub : m + 4 - 4 = m := by omega
    rw [hsub] at hr ⊢
    exact_mod_cast (by omega : (a (m + 4) : ℤ) - 16 * (a m : ℤ) = 0)

end
end ProofA335160

theorem OMA.solution : type_of% @OMA.S_oeis_a335160.main :=
  ProofA335160.main
