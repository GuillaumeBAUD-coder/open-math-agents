import OMAReductions.R_OeisA108129_conjecture_R1

namespace OMA.RieselCertificate

def divisor (r : Fin 24) : Nat :=
  if r.val % 2 = 0 then 3 else
  if r.val % 4 = 1 then 5 else
  if r.val % 3 = 2 then 7 else
  if r.val % 12 = 7 then 13 else
  if r.val % 8 = 7 then 17 else 241

theorem residues : ∀ r : Fin 24, 1 < divisor r ∧ divisor r ≤ 241 ∧
    2 ^ (24 : Nat) % divisor r = 1 ∧ 509203 * 2 ^ r.val % divisor r = 1 := by
  decide

theorem period (m q : Nat) (hq : 1 < q) (h : 2 ^ (24 : Nat) % q = 1) :
    2 ^ m % q = 2 ^ (m % 24) % q := by
  have hpart : (2 ^ (24 : Nat)) ^ (m / 24) % q = 1 := by
    rw [Nat.pow_mod, h, Nat.one_pow, Nat.mod_eq_of_lt hq]
  calc
    2 ^ m % q = (2 ^ (m % 24) * (2 ^ (24 : Nat)) ^ (m / 24)) % q := by
      rw [← Nat.pow_mul, ← Nat.pow_add, Nat.mod_add_div]
    _ = 2 ^ (m % 24) % q := by
      rw [Nat.mul_mod, hpart, Nat.mul_one, Nat.mod_mod]

theorem properDivisor (m : Nat) : ∃ q : Nat, 1 < q ∧
    q < 509203 * 2 ^ m - 1 ∧ q ∣ 509203 * 2 ^ m - 1 := by
  let r : Fin 24 := ⟨m % 24, Nat.mod_lt _ (by decide)⟩
  let q := divisor r
  obtain ⟨hq, hb, hp, hr⟩ := residues r
  have hmod : 509203 * 2 ^ m % q = 1 := by
    rw [Nat.mul_mod 509203 (2 ^ m), period m q hq hp, ← Nat.mul_mod]
    exact hr
  have ht := Nat.two_pow_pos m
  refine ⟨q, hq, by omega, Nat.dvd_of_mod_eq_zero ?_⟩
  exact Nat.sub_mod_eq_zero_of_mod_eq (hmod.trans (Nat.mod_eq_of_lt hq).symm)

end OMA.RieselCertificate

theorem OMA.solution : OMA.R_OeisA108129_conjecture_R1.H1 := by
  change OeisA108129.a 254602 = -1
  unfold OeisA108129.a
  rw [if_neg (by decide : (254602 : ℕ) ≠ 0), dif_neg]
  rintro ⟨m, _, hp⟩
  change (509203 * 2 ^ m - 1).Prime at hp
  obtain ⟨q, hq, hlt, hd⟩ := OMA.RieselCertificate.properDivisor m
  rcases (Nat.dvd_prime hp).mp hd with h | h <;> omega
