import OMAStatements.S_oeis_a308194

-- f n ≥ 5 for n ≥ 5; for composite n ≥ 6, f n ≤ minFac n + n / minFac n < n; for prime n,
-- f n = n + 1 is even and f (n + 1) ≤ 2 + (n + 1) / 2 < n. Strong induction ends at 5.

namespace OMA.A308194
open OMA.S_oeis_a308194

lemma f_le (n b : ℕ) (hb : b ∣ n) : f n ≤ b + n / b :=
  Nat.sInf_le ⟨b, hb, rfl⟩

lemma f_mem (n : ℕ) : ∃ b, b ∣ n ∧ f n = b + n / b := by
  have hne : ((fun b => b + n / b) '' {b | b ∣ n}).Nonempty := ⟨_, ⟨1, one_dvd n, rfl⟩⟩
  obtain ⟨b, hb, h⟩ := Nat.sInf_mem hne
  exact ⟨b, hb, by rw [f, ← h]⟩

lemma f_ge (n : ℕ) (hn : 5 ≤ n) : 5 ≤ f n := by
  obtain ⟨b, hb, h⟩ := f_mem n
  obtain ⟨d, rfl⟩ := hb
  have hb0 : 0 < b := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  rw [h, Nat.mul_div_cancel_left _ hb0]
  by_contra hc
  have : b ≤ 4 := by omega
  have : d ≤ 4 := by omega
  interval_cases b <;> interval_cases d <;> omega

lemma f_prime (n : ℕ) (hp : n.Prime) : f n = n + 1 := by
  obtain ⟨b, hb, h⟩ := f_mem n
  rcases (Nat.dvd_prime hp).mp hb with rfl | rfl
  · simpa [add_comm] using h
  · rw [h, Nat.div_self hp.pos]

lemma f_comp (n : ℕ) (hn : 6 ≤ n) (hp : ¬ n.Prime) : f n < n := by
  have h2 : 2 ≤ n.minFac := (Nat.minFac_prime (by omega)).two_le
  have hlt : n.minFac < n := (Nat.not_prime_iff_minFac_lt (by omega)).mp hp
  have hle := f_le n n.minFac (Nat.minFac_dvd n)
  obtain ⟨d, hd⟩ := Nat.minFac_dvd n
  generalize n.minFac = m at h2 hlt hle hd
  subst hd
  rw [Nat.mul_div_cancel_left _ (by omega)] at hle
  have hd2 : 2 ≤ d := by
    by_contra hc
    interval_cases d <;> omega
  nlinarith

lemma reach (n : ℕ) : 5 ≤ n → ∃ k : ℕ, f^[k] n = 5 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.eq_or_lt_of_le hn with rfl | hn6
    · exact ⟨0, rfl⟩
    by_cases hp : n.Prime
    · have hodd : n % 2 = 1 := by
        rcases hp.eq_two_or_odd with h | h
        · omega
        · exact h
      have hf := f_prime n hp
      have hle := f_le (n + 1) 2 (by omega)
      have hlt : f (n + 1) < n := by omega
      obtain ⟨k, hk⟩ := ih _ hlt (f_ge _ (by omega))
      refine ⟨k + 2, ?_⟩
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hf, hk]
    · obtain ⟨k, hk⟩ := ih _ (f_comp n hn6 hp) (f_ge _ hn)
      exact ⟨k + 1, by rw [Function.iterate_succ_apply, hk]⟩

end OMA.A308194

theorem OMA.solution : type_of% @OMA.S_oeis_a308194.main := fun n hn => OMA.A308194.reach n hn

