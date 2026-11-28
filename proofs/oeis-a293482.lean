import OMAStatements.S_oeis_a293482
import Mathlib

open OMA.S_oeis_a293482


theorem range_eq (n k : ℕ) :
    (Set.range fun x : (ZMod n)ˣ => x ^ k) = ((powMonoidHom k : (ZMod n)ˣ →* (ZMod n)ˣ).range : Set (ZMod n)ˣ) := by
  rw [MonoidHom.coe_range]; rfl

theorem card_cyc (n k : ℕ) [NeZero n] (hc : IsCyclic (ZMod n)ˣ) :
    Nat.card (Set.range fun x : (ZMod n)ˣ => x ^ k) = Nat.totient n / (Nat.totient n).gcd k := by
  rw [range_eq]
  have := IsCyclic.card_powMonoidHom_range (ZMod n)ˣ k
  rw [Nat.card_eq_fintype_card (α := (ZMod n)ˣ), ZMod.card_units_eq_totient] at this
  exact this

theorem card_cop (n k : ℕ) [NeZero n] (h : (Nat.totient n).Coprime k) :
    Nat.card (Set.range fun x : (ZMod n)ˣ => x ^ k) = Nat.totient n := by
  have h' : (Nat.card (ZMod n)ˣ).Coprime k := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]; exact h
  have : (Set.range fun x : (ZMod n)ˣ => x ^ k) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    exact ⟨(powCoprime h').symm y, (powCoprime h').apply_symm_apply y⟩
  rw [this, Nat.card_univ, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]

theorem odd_pp (k p e : ℕ) (hk : k.Prime) (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e) :
    Nat.card (Set.range fun x : (ZMod (p ^ e))ˣ => x ^ k) =
      p ^ (e - 1) * (p - 1) / (p ^ (e - 1) * (p - 1)).gcd k := by
  have : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [card_cyc _ _ (ZMod.isCyclic_units_of_prime_pow p hp hp2 e), Nat.totient_prime_pow hp he]

theorem gcd_one (k p e : ℕ) (hk : k.Prime) (hp : p.Prime) (h0 : p % k ≠ 0) (h1 : p % k ≠ 1) :
    (p ^ (e - 1) * (p - 1)).gcd k = 1 := by
  rw [Nat.gcd_comm]
  apply (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hk).2 _)).symm
  intro hd
  rcases (Nat.Prime.dvd_mul hk).1 hd with h | h
  · have := hk.dvd_of_dvd_pow h
    exact h0 (Nat.mod_eq_zero_of_dvd this)
  · have h2 := hp.two_le
    have hmod : (p - 1) % k = 0 := Nat.mod_eq_zero_of_dvd h
    have hk2 := hk.two_le
    have e : p = (p - 1) + 1 := by omega
    apply h1
    rw [e, Nat.add_mod, hmod, zero_add, Nat.mod_mod, Nat.one_mod_eq_one.2 (by omega)]

theorem gcd_k (k p e : ℕ) (hp : p.Prime) (h1 : p % k = 1) :
    (p ^ (e - 1) * (p - 1)).gcd k = k := by
  apply Nat.gcd_eq_right
  apply Dvd.dvd.mul_left
  have := Nat.dvd_sub_mod (n := k) p
  rwa [h1] at this

theorem two_pow (k e : ℕ) (hk : k.Prime) (hk2 : k ≠ 2) :
    Nat.card (Set.range fun x : (ZMod (2 ^ e))ˣ => x ^ k) = Nat.totient (2 ^ e) := by
  have : NeZero (2 ^ e) := ⟨by positivity⟩
  apply card_cop
  rcases Nat.eq_zero_or_pos e with rfl | he
  · simp
  · rw [Nat.totient_prime_pow Nat.prime_two he]
    simp only [Nat.add_one_sub_one, mul_one]
    apply Nat.Coprime.pow_left
    exact (Nat.coprime_primes Nat.prime_two hk).2 (Ne.symm hk2)

theorem OMA.solution : type_of% @OMA.S_oeis_a293482.main := by
  have k5 : Nat.Prime 5 := by norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    unfold a
    rw [two_pow 5 e k5 (by norm_num)]
    interval_cases e <;> simp
  · intro e he
    unfold a
    rw [two_pow 5 e k5 (by norm_num), Nat.totient_prime_pow Nat.prime_two he]
    norm_num
  · have := odd_pp 5 5 1 k5 k5 (by norm_num) le_rfl
    show Nat.card (Set.range fun x : (ZMod (5 ^ 1))ˣ => x ^ 5) = 4
    rw [this]; norm_num
  · intro e he
    unfold a
    rw [odd_pp 5 5 e k5 k5 (by norm_num) (by omega)]
    obtain ⟨f, rfl⟩ : ∃ f, e = f + 2 := ⟨e - 2, by omega⟩
    rw [show f + 2 - 1 = f + 1 by omega, show f + 2 - 2 = f by omega]
    have hg : (5 ^ (f + 1) * (5 - 1)).gcd 5 = 5 := by
      apply Nat.gcd_eq_right
      exact Dvd.dvd.mul_right (dvd_pow_self 5 (by omega)) _
    rw [hg, pow_succ]
    rw [show 5 ^ f * 5 * (5 - 1) = (4 * 5 ^ f) * 5 by ring, Nat.mul_div_cancel _ (by norm_num)]
  · intro p e hp hmod he
    unfold a
    by_cases hp2 : p = 2
    · subst hp2
      rw [two_pow 5 e k5 (by norm_num), Nat.totient_prime_pow Nat.prime_two he]
      simp
    · rw [odd_pp 5 p e k5 hp hp2 he, gcd_one 5 p e k5 hp (by omega) (by omega), Nat.div_one, mul_comm]
  · intro p e hp hmod he
    unfold a
    have hp2 : p ≠ 2 := by rintro rfl; norm_num at hmod
    rw [odd_pp 5 p e k5 hp hp2 he, gcd_k 5 p e hp hmod, mul_comm]
