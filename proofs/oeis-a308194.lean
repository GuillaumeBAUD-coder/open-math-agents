import OMAStatements.S_oeis_a308194
import Mathlib

/-
A308194: iterating f(n) = min over divisors b of n of (b + n / b) from any n >= 5 reaches 5.

For every n, f(n) = b + n / b for some divisor b, and f(n) <= b + n / b for all divisors b. If n >= 6
then f(n) >= 5, since b + c <= 4 forces b c <= 4. Strong induction on n: if n >= 6 is composite with
least prime factor p, then f(n) <= p + n / p < n; if n >= 6 is prime, then f(n) = n + 1 and
f(n + 1) <= 2 + (n + 1) / 2 < n. In both cases a value in [5, n) is reached.
-/

namespace OMA.P308194

lemma main' (f : ℕ → ℕ) (hf : ∀ n, f n = sInf ((fun b => b + n / b) '' {b | b ∣ n})) :
    ∀ n : ℕ, 5 ≤ n → ∃ k : ℕ, f^[k] n = 5 := by
  have hle : ∀ n b, b ∣ n → f n ≤ b + n / b := by
    intro n b hb
    rw [hf]
    exact Nat.sInf_le ⟨b, hb, rfl⟩
  have hmem : ∀ n, ∃ b, b ∣ n ∧ f n = b + n / b := by
    intro n
    have hne : ((fun b => b + n / b) '' {b | b ∣ n}).Nonempty := ⟨_, ⟨1, one_dvd n, rfl⟩⟩
    have h := Nat.sInf_mem hne
    rw [← hf] at h
    obtain ⟨b, hb, hb'⟩ := h
    exact ⟨b, hb, hb'.symm⟩
  have hge : ∀ n, 6 ≤ n → 5 ≤ f n := by
    intro n hn
    obtain ⟨b, hb, hfb⟩ := hmem n
    obtain ⟨c, rfl⟩ := hb
    have hb0 : 0 < b := by
      rcases Nat.eq_zero_or_pos b with h | h
      · subst h
        simp at hn
      · exact h
    rw [Nat.mul_div_cancel_left c hb0] at hfb
    rw [hfb]
    by_contra hlt
    have hb4 : b ≤ 4 := by omega
    have hc4 : c ≤ 4 := by omega
    interval_cases b <;> interval_cases c <;> omega
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.eq_or_lt_of_le hn with h5 | h6
    · exact ⟨0, h5.symm⟩
    · by_cases hp : n.Prime
      · have hodd : n % 2 = 1 := by
          rcases hp.eq_two_or_odd with h | h <;> omega
        have h1 : f n = n + 1 := by
          obtain ⟨b, hb, hfb⟩ := hmem n
          rcases (Nat.dvd_prime hp).mp hb with h | h
          · subst h
            rw [hfb, Nat.div_one]
            omega
          · subst h
            rw [hfb, Nat.div_self (by omega)]
        have h2 : f (n + 1) ≤ 2 + (n + 1) / 2 := hle (n + 1) 2 (by omega)
        have h3 : 5 ≤ f (n + 1) := hge (n + 1) (by omega)
        obtain ⟨k, hk⟩ := ih (f (n + 1)) (by omega) h3
        refine ⟨k + 1 + 1, ?_⟩
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply, h1]
        exact hk
      · have hmf : 2 ≤ n.minFac := (Nat.minFac_prime (by omega)).two_le
        have hle' : n.minFac ≤ n / n.minFac := Nat.minFac_le_div (by omega) hp
        have hcp : n / n.minFac * n.minFac = n := Nat.div_mul_cancel (Nat.minFac_dvd n)
        have hfn : f n ≤ n.minFac + n / n.minFac := hle n n.minFac (Nat.minFac_dvd n)
        have h3 : 5 ≤ f n := hge n (by omega)
        generalize n.minFac = p at hmf hle' hcp hfn
        generalize n / p = c at hle' hcp hfn
        have hc3 : 3 ≤ c := by
          by_contra hlt
          have hc2 : c ≤ 2 := by omega
          have hp2 : p ≤ 2 := by omega
          have := Nat.mul_le_mul hc2 hp2
          omega
        obtain ⟨c', rfl⟩ : ∃ c', c = c' + 3 := ⟨c - 3, by omega⟩
        obtain ⟨p', rfl⟩ : ∃ p', p = p' + 2 := ⟨p - 2, by omega⟩
        have hlt : f n < n := by
          have : p' + 2 + (c' + 3) < n := by
            rw [← hcp]
            nlinarith [Nat.zero_le (c' * p')]
          omega
        obtain ⟨k, hk⟩ := ih (f n) hlt h3
        refine ⟨k + 1, ?_⟩
        rw [Function.iterate_succ_apply]
        exact hk

end OMA.P308194

theorem OMA.solution : type_of% @OMA.S_oeis_a308194.main :=
  OMA.P308194.main' OMA.S_oeis_a308194.f (fun _ => rfl)
