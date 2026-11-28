import OMAReductions.R_mse_1838931_R1
import Mathlib

private theorem reflectFac {p : ℕ} [Fact p.Prime] (k : ℕ) (hk : k < p) :
    (k.factorial : ZMod p) * ((p-k-1).factorial : ZMod p) = (-1)^(k+1) := by
  induction k with
  | zero => simpa using ZMod.wilsons_lemma p
  | succ k ih =>
    have hi := ih (by omega)
    have he : p-k-1 = (p-(k+1)-1)+1 := by omega
    rw [he, Nat.factorial_succ, Nat.cast_mul] at hi
    have hc : (((p-(k+1)-1)+1 : ℕ) : ZMod p) = -((k+1 : ℕ) : ZMod p) := by
      apply eq_neg_of_add_eq_zero_left
      rw [← Nat.cast_add, show (p-(k+1)-1+1)+(k+1) = p by omega, ZMod.natCast_self]
    rw [hc] at hi
    rw [Nat.factorial_succ, Nat.cast_mul, pow_succ (-1 : ZMod p) (k+1)]
    linear_combination -hi

theorem OMA.solution : OMA.R_mse_1838931_R1.H1 := by
  constructor
  · intro N
    obtain ⟨q,hqN,hq⟩ := Nat.exists_infinite_primes (N+1)
    obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd (n := q.factorial+1) (by have := Nat.factorial_pos q; omega)
    refine ⟨p,q,by omega,?_,hp,hq,hd⟩
    by_contra! h
    exact hp.not_dvd_one ((Nat.dvd_add_right (Nat.dvd_factorial hp.pos h)).mp hd)
  intro p q hp hq hq2 hd
  let : Fact p.Prime := ⟨hp⟩
  have hlt : q < p := by
    by_contra! h
    have hu := (Nat.dvd_add_right (Nat.dvd_factorial hp.pos h)).mp hd
    exact hp.not_dvd_one hu
  have hf := (ZMod.natCast_eq_zero_iff _ _).2 hd
  push_cast at hf
  have hr := reflectFac (p := p) (q-1) (by omega)
  have hpred : q-1+1 = q := by omega
  rw [hpred, show p-(q-1)-1 = p-q by omega, (hq.odd_of_ne_two (by omega)).neg_one_pow] at hr
  have hfac : (q.factorial : ZMod p) = (q : ZMod p) * ((q-1).factorial : ZMod p) := by
    conv_lhs => rw [← hpred, Nat.factorial_succ, Nat.cast_mul, hpred]
  rw [hfac] at hf
  have hc : (q : ZMod p) = ((p-q).factorial : ZMod p) := by
    linear_combination (q : ZMod p) * hr - ((p-q).factorial : ZMod p) * hf
  have hm := (ZMod.natCast_eq_natCast_iff _ _ _).1 hc
  refine ⟨hlt, ?_, hm⟩
  by_contra! h
  have hsmall : (p-q).factorial ≤ 2 := by
    generalize p-q = d at h ⊢
    interval_cases d <;> decide
  have := hm.eq_of_lt_of_lt hlt (by omega)
  omega
