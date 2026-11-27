import FormalConjectures.ErdosProblems.«436»

/-! Each interval of length four contains a number twice an odd integer. To
exclude such a number choose a prime modulo which 2 is a nonpower but the
small odd primes are powers. It suffices to use a prime divisor of the exponent.
The quadratic prescription follows from Dirichlet and quadratic reciprocity:
for the product P of the prescribed odd primes, use primes 1+4P modulo 8P.
The odd prime prescription is a special case of Kummer theory and Chebotarev. -/

namespace OMA.R_Erdos436_erdos_436_variants_ge_four_R1
open Erdos436 Filter

def H1 : Prop := ∀ M B : ℕ, ∃ p > B, p.Prime ∧
  (¬ ∃ x : ZMod p, x^2 = 2) ∧
  ∀ q : ℕ, q.Prime → Odd q → q ≤ M → ∃ x : ZMod p, x^2 = q

def H2 : Prop := ∀ d : ℕ, d.Prime → Odd d → ∀ M B : ℕ, ∃ p > B, p.Prime ∧
  (¬ ∃ x : ZMod p, x^d = 2) ∧
  ∀ q : ℕ, q.Prime → Odd q → q ≤ M → ∃ x : ZMod p, x^d = q

private lemma odd_power {d M p : ℕ}
    (hq : ∀ q : ℕ, q.Prime → Odd q → q ≤ M → ∃ x : ZMod p, x^d = q)
    {a : ℕ} (ha : Odd a) (hM : a ≤ M) : ∃ x : ZMod p, x^d = a := by
  induction a using induction_on_primes with
  | zero => simp at ha
  | one => exact ⟨1, by simp⟩
  | prime_mul q a hp ih =>
    obtain ⟨ho,ha⟩ := Nat.odd_mul.mp ha
    have ap : 0 < a := by obtain ⟨k,hk⟩ := ha; omega
    obtain ⟨x,hx⟩ := hq q hp ho ((Nat.le_mul_of_pos_right q ap).trans hM)
    obtain ⟨y,hy⟩ := ih ha ((Nat.le_mul_of_pos_left a hp.pos).trans hM)
    exact ⟨x*y, by rw [mul_pow,hx,hy,Nat.cast_mul]⟩

private lemma obstruction {k d l M p : ℕ} (hp : p.Prime) (hd : d ∣ k)
    (hl : 4 ≤ l) (hpM : M+4 < p) (hnon : ¬ ∃ x : ZMod p, x^d = 2)
    (hq : ∀ q : ℕ, q.Prime → Odd q → q ≤ M+4 → ∃ x : ZMod p, x^d = q) :
    (M : ℕ∞) ≤ r k l p := by
  letI : Fact p.Prime := ⟨hp⟩
  apply le_iInf₂
  rintro n ⟨one,allpow⟩
  suffices M ≤ n by exact_mod_cast this
  by_contra! small
  let i := (6 - n % 4) % 4
  have hi : i < 4 := Nat.mod_lt _ (by decide)
  let a := (n+i)/2
  have ha : Odd a := by rw [Nat.odd_iff]; dsimp [a,i]; omega
  have eq : n+i = 2*a := by dsimp [a,i]; omega
  have ap : 0 < a := by obtain ⟨j,hj⟩ := ha; omega
  obtain ⟨y,hy⟩ := odd_power hq ha (by omega)
  obtain ⟨_,x,hx⟩ := allpow i (hi.trans_le hl)
  have anz : (a : ZMod p) ≠ 0 := by
    rw [Ne,ZMod.natCast_eq_zero_iff]
    exact fun h => (by omega : ¬p ≤ a) (Nat.le_of_dvd ap h)
  obtain ⟨e,he⟩ := hd
  apply hnon
  refine ⟨x^e / y,?_⟩
  rw [div_pow, ← pow_mul, Nat.mul_comm e d, ← he, hx,hy,eq,Nat.cast_mul,Nat.cast_ofNat]
  exact mul_div_cancel_right₀ _ anz

theorem main : H1 → H2 → type_of% @Erdos436.erdos_436.variants.ge_four := by
  intro two odd k hk l hl
  obtain ⟨d,hd,hdk⟩ := Nat.exists_prime_and_dvd (by omega : k ≠ 1)
  have prescribe : ∀ M B : ℕ, ∃ p > B, p.Prime ∧
      (¬ ∃ x : ZMod p, x^d = 2) ∧
      ∀ q : ℕ, q.Prime → Odd q → q ≤ M → ∃ x : ZMod p, x^d = q := by
    rcases hd.eq_two_or_odd with e | h
    · subst d; exact two
    · exact odd d hd (Nat.odd_iff.mpr h)
  by_contra htop
  obtain ⟨N,hN⟩ := ENat.ne_top_iff_exists.mp htop
  have freq : ∃ᶠ p in atTop ⊓ 𝓟 {p : ℕ | p.Prime}, ((N+1 : ℕ) : ℕ∞) ≤ r k l p := by
    rw [Filter.frequently_inf_principal,Filter.frequently_atTop]
    intro B
    obtain ⟨p,hpB,hp,hn,hq⟩ := prescribe (N+1+4) (max B (N+1+4))
    exact ⟨p,by omega,hp,obstruction hp hdk hl (by omega) hn hq⟩
  have h : ((N+1 : ℕ) : ℕ∞) ≤ runLimsup k l := Filter.le_limsup_of_frequently_le' freq
  rw [← hN] at h
  have : N+1 ≤ N := by exact_mod_cast h
  omega
end OMA.R_Erdos436_erdos_436_variants_ge_four_R1
