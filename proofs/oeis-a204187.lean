import OMAStatements.S_oeis_a204187
import Mathlib

-- Problem: OEIS A204187, conjecture of Neretin: for a(n) = Sum_{m=1..n-1} m^(n-1) mod n,
-- a(n) = n/2 if and only if n = 4k + 2.
-- Statement: statements/oeis-a204187.lean (declaration OMA.S_oeis_a204187.main)
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Proof. For odd n the equation 2 a(n) = n is false. Let n = 2h, so the exponent k = n - 1 is
-- odd. In Z/n the terms x^k and (-x)^k cancel, so the sum of x^k over Z/n is the sum over the
-- fixed points of the negation, which are 0 and h. Thus the sum is h^k modulo n. If h is even,
-- then n divides h^k (k >= 2), so a(n) = 0. If h is odd, then h^(k-1) is odd and
-- h^k = h (mod 2h), so a(n) = h = n/2.

namespace OMA.A204187

open OMA.S_oeis_a204187

/-- The sum over 1 <= m < n, as a sum over ZMod n. -/
lemma sum_cast (n k : ℕ) [NeZero n] (hk : 1 ≤ k) :
    (((∑ m ∈ Finset.Ico 1 n, m ^ k : ℕ)) : ZMod n) = ∑ x : ZMod n, x ^ k := by
  have h0 : ∑ m ∈ Finset.range n, ((m : ZMod n)) ^ k = ∑ m ∈ Finset.Ico 1 n, ((m : ZMod n)) ^ k := by
    have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hn]
    simp [zero_pow (by omega : k ≠ 0)]
  push_cast
  rw [← h0]
  refine Finset.sum_nbij' (fun m => (m : ZMod n)) (fun x => x.val) ?_ ?_ ?_ ?_ ?_
  · intro m _; exact Finset.mem_univ _
  · intro x _; exact Finset.mem_range.mpr (ZMod.val_lt x)
  · intro m hm; exact ZMod.val_cast_of_lt (Finset.mem_range.mp hm)
  · intro x _; exact ZMod.natCast_zmod_val x
  · intro m _; rfl

/-- For even n = 2h and odd k, the sum of the k-th powers over ZMod n is h^k. -/
lemma sum_pow (h k : ℕ) [NeZero (2 * h)] (hh : 1 ≤ h) (hk : Odd k) :
    ∑ x : ZMod (2 * h), x ^ k = ((h : ZMod (2 * h))) ^ k := by
  have hk0 : k ≠ 0 := by obtain ⟨t, rfl⟩ := hk; omega
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (ZMod (2 * h)))
    (fun x => x = -x) (fun x => x ^ k)
  have hzero : ∑ x ∈ Finset.univ.filter (fun x : ZMod (2 * h) => ¬ x = -x), x ^ k = 0 := by
    refine Finset.sum_involution (fun x _ => -x) ?_ ?_ ?_ ?_
    · intro x _
      rw [Odd.neg_pow hk, add_neg_cancel]
    · intro x hx _ hcon
      exact (Finset.mem_filter.mp hx).2 hcon.symm
    · intro x hx
      rw [Finset.mem_filter] at hx ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [neg_neg]
      exact fun hcon => hx.2 hcon.symm
    · intro x _; exact neg_neg x
  rw [← hsplit, hzero, add_zero]
  -- the fixed points of the negation are 0 and h
  have hfix : Finset.univ.filter (fun x : ZMod (2 * h) => x = -x) = {0, (h : ZMod (2 * h))} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hx
      have h2 : ((2 * x.val : ℕ) : ZMod (2 * h)) = 0 := by
        push_cast
        rw [ZMod.natCast_zmod_val]
        linear_combination hx
      rw [ZMod.natCast_eq_zero_iff] at h2
      have hlt := ZMod.val_lt x
      have hd : h ∣ x.val := (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).mp h2
      obtain ⟨t, ht⟩ := hd
      have ht01 : t = 0 ∨ t = 1 := by
        rcases Nat.lt_or_ge t 2 with h' | h'
        · omega
        · exfalso
          have : h * 2 ≤ h * t := Nat.mul_le_mul_left h h'
          omega
      rcases ht01 with rfl | rfl
      · left
        have : x.val = 0 := by rw [ht]; ring
        exact (ZMod.val_eq_zero x).mp this
      · right
        rw [← ZMod.natCast_zmod_val x, ht, mul_one]
    · rintro (rfl | rfl)
      · simp
      · have : ((2 * h : ℕ) : ZMod (2 * h)) = 0 := ZMod.natCast_self _
        push_cast at this
        linear_combination this
  rw [hfix]
  by_cases h0 : (0 : ZMod (2 * h)) = (h : ZMod (2 * h))
  · rw [← h0]; simp [hk0]
  · rw [Finset.sum_pair h0, zero_pow hk0, zero_add]

theorem main' : ∀ n : ℕ, 1 ≤ n → (2 * a n = n ↔ n % 4 = 2) := by
  intro n hn
  rcases Nat.even_or_odd' n with ⟨h, rfl | rfl⟩
  · -- n = 2 h
    have hh : 1 ≤ h := by omega
    have hne : NeZero (2 * h) := ⟨by omega⟩
    have hkodd : Odd (2 * h - 1) := ⟨h - 1, by omega⟩
    have hcast := sum_cast (2 * h) (2 * h - 1) (by omega)
    rw [sum_pow h (2 * h - 1) hh hkodd] at hcast
    have hmod : (∑ m ∈ Finset.Ico 1 (2 * h), m ^ (2 * h - 1)) % (2 * h)
        = h ^ (2 * h - 1) % (2 * h) := by
      have : (((∑ m ∈ Finset.Ico 1 (2 * h), m ^ (2 * h - 1) : ℕ)) : ZMod (2 * h))
          = ((h ^ (2 * h - 1) : ℕ) : ZMod (2 * h)) := by rw [hcast]; push_cast; rfl
      exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp this
    unfold a
    rw [hmod]
    rcases Nat.even_or_odd' h with ⟨j, rfl | rfl⟩
    · -- h even: the power is a multiple of 2 h
      have hj : 1 ≤ j := by omega
      have hd : 2 * (2 * j) ∣ (2 * j) ^ (2 * (2 * j) - 1) := by
        obtain ⟨e, he⟩ : ∃ e, 2 * (2 * j) - 1 = e + 2 := ⟨2 * (2 * j) - 3, by omega⟩
        rw [he, pow_add, pow_two]
        exact Dvd.dvd.mul_left ⟨j, by ring⟩ _
      rw [Nat.mod_eq_zero_of_dvd hd]
      omega
    · -- h odd: the power is h modulo 2 h
      have hoddpow : Odd ((2 * j + 1) ^ (2 * (2 * j + 1) - 1 - 1)) := Odd.pow ⟨j, rfl⟩
      obtain ⟨u, hu⟩ := hoddpow
      have hpow : (2 * j + 1) ^ (2 * (2 * j + 1) - 1)
          = 2 * (2 * j + 1) * u + (2 * j + 1) := by
        have : 2 * (2 * j + 1) - 1 = (2 * (2 * j + 1) - 1 - 1) + 1 := by omega
        rw [this, pow_succ, hu]; ring
      rw [hpow, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
      omega
  · -- n odd
    constructor
    · intro hcon; omega
    · intro hcon; omega

end OMA.A204187

theorem OMA.solution : type_of% @OMA.S_oeis_a204187.main :=
  OMA.A204187.main'
