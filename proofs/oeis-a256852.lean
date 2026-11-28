import OMAStatements.S_oeis_a256852

-- Problem: A256852: Number of ways to write prime(n) = a^2 + b^4.
-- Upstream: formal-conjectures statements/oeis-a256852.lean:0 (declaration OMA.S_oeis_a256852.main)
-- Credit: @ryanwitzman (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.A256852Proof

/-- One half of the uniqueness argument: if `p ∣ a*c + b*d` then `(a, b) = (c, d)`. -/
lemma half {p a b c d : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h1 : a ^ 2 + b ^ 2 = p) (h2 : c ^ 2 + d ^ 2 = p) (hdvd : p ∣ a * c + b * d) :
    a = c ∧ b = d := by
  have hpos : 0 < a * c + b * d := by positivity
  have hle : p ≤ a * c + b * d := Nat.le_of_dvd hpos hdvd
  have hid : ((a * c + b * d : ℕ) : ℤ) ^ 2 + ((a : ℤ) * d - b * c) ^ 2 = (p : ℤ) ^ 2 := by
    have e1 : ((a : ℤ) ^ 2 + b ^ 2) = p := by exact_mod_cast h1
    have e2 : ((c : ℤ) ^ 2 + d ^ 2) = p := by exact_mod_cast h2
    push_cast
    rw [← e1, ← e2] at *
    nlinarith [e1, e2]
  have hle' : (p : ℤ) ≤ ((a * c + b * d : ℕ) : ℤ) := by exact_mod_cast hle
  have hp0 : (0 : ℤ) ≤ p := by positivity
  have hsq : ((a : ℤ) * d - b * c) ^ 2 = 0 := by
    nlinarith [sq_nonneg ((a : ℤ) * d - b * c), mul_le_mul hle' hle' hp0 (by positivity)]
  have had : (a : ℤ) * d = b * c := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
    linarith
  have e1 : ((a : ℤ) ^ 2 + b ^ 2) = p := by exact_mod_cast h1
  have e2 : ((c : ℤ) ^ 2 + d ^ 2) = p := by exact_mod_cast h2
  -- p * d^2 = b^2 * p
  have hpd : (p : ℤ) * d ^ 2 = b ^ 2 * p := by
    calc (p : ℤ) * d ^ 2 = (a ^ 2 + b ^ 2) * d ^ 2 := by rw [e1]
      _ = ((a : ℤ) * d) ^ 2 + b ^ 2 * d ^ 2 := by ring
      _ = ((b : ℤ) * c) ^ 2 + b ^ 2 * d ^ 2 := by rw [had]
      _ = b ^ 2 * (c ^ 2 + d ^ 2) := by ring
      _ = b ^ 2 * p := by rw [e2]
  have hp_ne : (p : ℤ) ≠ 0 := by
    have : 0 < p := by rw [← h1]; positivity
    exact_mod_cast this.ne'
  have hdb2 : (d : ℤ) ^ 2 = b ^ 2 := by
    have := hpd
    rw [mul_comm ((b : ℤ) ^ 2)] at this
    exact mul_left_cancel₀ hp_ne this
  have hdb : d = b := by
    have := (sq_eq_sq₀ (by positivity) (by positivity)).mp hdb2
    exact_mod_cast this
  subst hdb
  have hac2 : (a : ℤ) ^ 2 = c ^ 2 := by linarith
  have hac : a = c := by
    have := (sq_eq_sq₀ (by positivity) (by positivity)).mp hac2
    exact_mod_cast this
  exact ⟨hac, rfl⟩

/-- Uniqueness of the representation of a prime as a sum of two positive squares. -/
lemma uniq {p a b c d : ℕ} (hp : p.Prime) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (h1 : a ^ 2 + b ^ 2 = p) (h2 : c ^ 2 + d ^ 2 = p) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have key : (a * c + b * d) * (a * d + b * c) = p * (c * d + a * b) := by
    calc (a * c + b * d) * (a * d + b * c)
        = c * d * (a ^ 2 + b ^ 2) + a * b * (c ^ 2 + d ^ 2) := by ring
      _ = p * (c * d + a * b) := by rw [h1, h2]; ring
  have hdvd : p ∣ (a * c + b * d) * (a * d + b * c) := ⟨_, key⟩
  rcases hp.dvd_mul.mp hdvd with h | h
  · exact Or.inl (half ha hb hc hd h1 h2 h)
  · have h2' : d ^ 2 + c ^ 2 = p := by rw [← h2]; ring
    have h' : p ∣ a * d + b * c := h
    exact Or.inr (half ha hb hd hc h1 h2' h')

lemma count_le_two {p : ℕ} (hp : p.Prime) : OMA.S_oeis_a256852.count p ≤ 2 := by
  unfold OMA.S_oeis_a256852.count
  set S := (Finset.Icc 1 p ×ˢ Finset.Icc 1 p).filter (fun ab => ab.1 ^ 2 + ab.2 ^ 4 = p)
  by_cases hS : S.Nonempty
  · obtain ⟨⟨a0, b0⟩, h0⟩ := hS
    have mem : ∀ {x : ℕ × ℕ}, x ∈ S → 1 ≤ x.1 ∧ 1 ≤ x.2 ∧ x.1 ^ 2 + x.2 ^ 4 = p := by
      intro x hx
      simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hx
      exact ⟨hx.1.1.1, hx.1.2.1, hx.2⟩
    obtain ⟨ha0, hb0, he0⟩ : 1 ≤ a0 ∧ 1 ≤ b0 ∧ a0 ^ 2 + b0 ^ 4 = p := mem h0
    have sub : S ⊆ {(a0, b0), (b0 ^ 2, Nat.sqrt a0)} := by
      intro x hx
      obtain ⟨ha, hb, he⟩ := mem hx
      have e1 : x.1 ^ 2 + (x.2 ^ 2) ^ 2 = p := by rw [← he]; ring
      have e2 : a0 ^ 2 + (b0 ^ 2) ^ 2 = p := by rw [← he0]; ring
      rcases uniq hp ha (by positivity) ha0 (by positivity) e1 e2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have : x.2 = b0 := by
          have := (Nat.pow_left_injective (n := 2) (by norm_num)) h2
          exact this
        simp [Prod.ext_iff, h1, this]
      · have hs : Nat.sqrt a0 = x.2 := by
          rw [← h2]; exact Nat.sqrt_eq' x.2
        simp [Prod.ext_iff, h1, hs]
    calc S.card ≤ ({(a0, b0), (b0 ^ 2, Nat.sqrt a0)} : Finset (ℕ × ℕ)).card :=
          Finset.card_le_card sub
      _ ≤ 2 := Finset.card_le_two
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS]; simp

end OMA.A256852Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a256852.main := by
  intro n _
  exact OMA.A256852Proof.count_le_two (Nat.prime_nth_prime (n - 1))
