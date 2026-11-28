import OMAStatements.S_oeis_a117971
import Mathlib

/-!
# A117971: powers of two with no ternary digit `2` — a verified prefix and the open tail

The conjecture (Erdős, 1979; the comment in A117971) says that `2 ^ n` has a ternary digit `2`
unless `n` is `0`, `2` or `8`. The ternary digit of `2 ^ n` at position `j` depends only on `n`
modulo `2 * 3 ^ j`, because `2 ^ (2 * 3 ^ j) ≡ 1` modulo `3 ^ (j + 1)`. So the exponents whose
lowest digits avoid `2` can be lifted one digit at a time, as in Robert I. Saye, On Two
Conjectures Concerning the Ternary Digits of Powers of Two, J. Integer Sequences 25 (2022).
The lemma `checkedPrefix` runs this lift in the Lean kernel for all `n < 2 * 3 ^ 15`
(about 28.7 million exponents): the only such `n` with no ternary digit `2` are `0`, `2`, `8`.

The shape of the kernel computation follows the merged reduction of
`OeisA259667.conjecture_2` by @marcusbuffett, which treats the even exponents.

* `H1` is the conjecture on the finite range `2 * 3 ^ 15 ≤ n ≤ 2 * 3 ^ 45`. The upper end is the
  bound of Saye's published computation.
* `H2` is the open tail `n > 2 * 3 ^ 45`.
-/

namespace TernaryTwo

/-- With no digit `2`, no position of `x` holds a `2`. -/
private lemma n2 (j : ℕ) : ∀ x : ℕ, 2 ∉ Nat.digits 3 x → x / 3 ^ j % 3 ≠ 2 := by
  induction j with
  | zero =>
    intro x h
    rcases Nat.eq_zero_or_pos x with rfl | hx0
    · simp
    · rw [Nat.digits_def' (by decide) hx0, List.mem_cons, not_or] at h
      rw [pow_zero, Nat.div_one]
      exact fun h2 => h.1 h2.symm
  | succ j ih =>
    intro x h
    rcases Nat.eq_zero_or_pos x with rfl | hx0
    · simp
    · rw [Nat.digits_def' (by decide) hx0, List.mem_cons, not_or] at h
      have := ih (x / 3) h.2
      rwa [Nat.div_div_eq_div_mul, ← pow_succ'] at this

/-- The digit at position `p` is unchanged by reduction modulo a higher power of `3`. -/
private lemma digMod (x p K : ℕ) (hp : p < K) : x % 3 ^ K / 3 ^ p % 3 = x / 3 ^ p % 3 := by
  obtain ⟨d, rfl⟩ : ∃ d, K = p + (d + 1) := ⟨K - p - 1, by omega⟩
  rw [pow_add, Nat.mod_mul_right_div_self, pow_succ,
    Nat.mod_mod_of_dvd _ (dvd_mul_left 3 (3 ^ d))]

/-- `2 ^ (2 * 3 ^ l) ≡ 1` modulo `3 ^ (l + 1)`. -/
private lemma per (l : ℕ) : 2 ^ (2 * 3 ^ l) ≡ 1 [MOD 3 ^ (l + 1)] := by
  induction l with
  | zero => decide
  | succ l ih =>
    have h1 : 1 ≤ 2 ^ (2 * 3 ^ l) := Nat.one_le_two_pow
    obtain ⟨c, hc⟩ := (Nat.modEq_iff_dvd' h1).mp ih.symm
    have ha : 2 ^ (2 * 3 ^ l) = 1 + 3 ^ (l + 1) * c := by omega
    have e : 2 ^ (2 * 3 ^ (l + 1)) =
        1 + 3 ^ (l + 1 + 1) * (c + 3 * 3 ^ l * c ^ 2 + 3 * (3 ^ l) ^ 2 * c ^ 3) := by
      rw [show 2 * 3 ^ (l + 1) = 2 * 3 ^ l * 3 by ring, pow_mul, ha]
      ring
    rw [e]
    exact (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right (3 ^ (l + 1 + 1)) _)).add_left 1

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
/-- The verified prefix: the exponents below `2 * 3 ^ 15` with no ternary digit `2`. -/
private lemma checkedPrefix (n : ℕ) (hn : n < 2 * 3 ^ 15) (h : 2 ∉ Nat.digits 3 (2 ^ n)) :
    n = 0 ∨ n = 2 ∨ n = 8 := by
  let M : ℕ := 3 ^ 80
  let rz : ℕ → ℕ → Bool := Nat.rec (fun _ => false)
    (fun _ next x => decide (x % 3 = 2) || next (x / 3))
  have rzs (s x : ℕ) (hr : rz s x = true) : ∃ j, j < s ∧ x / 3 ^ j % 3 = 2 := by
    induction s generalizing x with
    | zero =>
      change false = true at hr
      cases hr
    | succ s ih =>
      change (decide (x % 3 = 2) || rz s (x / 3)) = true at hr
      rcases Bool.or_eq_true_iff.mp hr with h1 | h2
      · exact ⟨0, by omega, by simpa using of_decide_eq_true h1⟩
      · obtain ⟨j, hj, a⟩ := ih _ h2
        refine ⟨j + 1, by omega, ?_⟩
        rwa [pow_succ', ← Nat.div_div_eq_div_mul]
  let exc : ℕ → Bool := fun i => decide (i = 0 ∨ i = 2 ∨ i = 8)
  let scan : ℕ → ℕ → ℕ → ℕ → ℕ → Bool := Nat.rec
    (fun q idx v _ => exc idx || rz 48 (v / q))
    (fun _ next q idx v u =>
      if (v / q) % 3 = 2 then true
      else [0, 1, 2].all (fun i =>
        next (q * 3) (idx + 2 * q * i) ((v * u ^ i) % M) (u ^ 3 % M)))
  have sound (dep lev idx v u t : ℕ) (bound : lev + dep ≤ 30)
      (hv : v = 2 ^ idx % M) (hu : u = 2 ^ (2 * 3 ^ lev) % M)
      (ht : t < 3 ^ dep) (good : 2 ∉ Nat.digits 3 (2 ^ (idx + 2 * 3 ^ lev * t)))
      (ok : scan dep (3 ^ lev) idx v u = true) :
      exc (idx + 2 * 3 ^ lev * t) = true := by
    induction dep generalizing lev idx v u t with
    | zero =>
      have t0 : t = 0 := by simpa using ht
      subst t0
      simp only [Nat.mul_zero, Nat.add_zero] at good ⊢
      change (exc idx || rz 48 (v / 3 ^ lev)) = true at ok
      rcases Bool.or_eq_true_iff.mp ok with h1 | h2
      · exact h1
      · exfalso
        obtain ⟨j, hj, hz⟩ := rzs 48 _ h2
        rw [Nat.div_div_eq_div_mul, ← pow_add] at hz
        have hd := digMod (2 ^ idx) (lev + j) 80 (by omega)
        rw [← hv, hz] at hd
        exact n2 _ _ good hd.symm
    | succ dep ih =>
      have hpow : 2 ^ (idx + 2 * 3 ^ lev * t) ≡ 2 ^ idx [MOD 3 ^ (lev + 1)] := by
        have := ((per lev).pow t).mul_left (2 ^ idx)
        simpa [pow_add, pow_mul] using this
      change (if (v / 3 ^ lev) % 3 = 2 then true
        else [0, 1, 2].all (fun i =>
          scan dep (3 ^ lev * 3) (idx + 2 * 3 ^ lev * i) ((v * u ^ i) % M) (u ^ 3 % M))) = true
        at ok
      by_cases hd : (v / 3 ^ lev) % 3 = 2
      · exfalso
        have hdig : 2 ^ (idx + 2 * 3 ^ lev * t) / 3 ^ lev % 3 = 2 := by
          have e1 : 2 ^ (idx + 2 * 3 ^ lev * t) / 3 ^ lev % 3
              = 2 ^ (idx + 2 * 3 ^ lev * t) % 3 ^ (lev + 1) / 3 ^ lev := by
            rw [pow_succ, Nat.mod_mul_right_div_self]
          have e2 : 2 ^ idx / 3 ^ lev % 3 = 2 ^ idx % 3 ^ (lev + 1) / 3 ^ lev := by
            rw [pow_succ, Nat.mod_mul_right_div_self]
          have e3 := digMod (2 ^ idx) lev 80 (by omega)
          rw [← hv, hd] at e3
          rw [e1, hpow, ← e2, ← e3]
        exact n2 _ _ good hdig
      · rw [if_neg hd] at ok
        simp only [List.all_eq_true] at ok
        have imem : t % 3 ∈ ([0, 1, 2] : List ℕ) := by
          have : t % 3 < 3 := Nat.mod_lt _ (by norm_num)
          simp
          omega
        have next := ok (t % 3) imem
        have idxEq : idx + 2 * 3 ^ lev * t
            = (idx + 2 * 3 ^ lev * (t % 3)) + 2 * 3 ^ (lev + 1) * (t / 3) := by
          rw [pow_succ]
          linear_combination (2 * 3 ^ lev) * (Nat.mod_add_div t 3).symm
        have vi : (v * u ^ (t % 3)) % M = 2 ^ (idx + 2 * 3 ^ lev * (t % 3)) % M := by
          rw [hv, hu, pow_add, pow_mul 2 (2 * 3 ^ lev) (t % 3)]
          exact (Nat.mod_modEq _ _).mul ((Nat.mod_modEq _ _).pow _)
        have ui : u ^ 3 % M = 2 ^ (2 * 3 ^ (lev + 1)) % M := by
          rw [hu, show 2 * 3 ^ (lev + 1) = 2 * 3 ^ lev * 3 by ring, pow_mul 2 (2 * 3 ^ lev) 3]
          exact (Nat.mod_modEq _ _).pow 3
        have ht1 : t / 3 < 3 ^ dep := by
          rw [pow_succ] at ht
          omega
        rw [idxEq] at good ⊢
        exact ih (lev + 1) _ _ _ (t / 3) (by omega) vi ui ht1 good
          (by rw [pow_succ 3 lev]; exact next)
  have all : scan 15 1 0 1 4 = true ∧ scan 15 1 1 2 4 = true := by
    dsimp only [scan, rz, exc, M]
    decide +kernel
  have hmod : n % 2 = 0 ∨ n % 2 = 1 := by omega
  have hsplit : n = n % 2 + 2 * 3 ^ 0 * (n / 2) := by omega
  have ht : n / 2 < 3 ^ 15 := by omega
  rw [hsplit] at h
  have res : exc (n % 2 + 2 * 3 ^ 0 * (n / 2)) = true := by
    rcases hmod with h0 | h1
    · rw [h0] at h ⊢
      exact sound 15 0 0 1 4 (n / 2) (by decide) (by decide) (by decide) ht h all.1
    · rw [h1] at h ⊢
      exact sound 15 0 1 2 4 (n / 2) (by decide) (by decide) (by decide) ht h all.2
  rw [← hsplit] at res
  exact of_decide_eq_true res

end TernaryTwo

namespace OMA.R_oeis_a117971_R1

/-- The conjecture on the finite range `2 * 3 ^ 15 ≤ n ≤ 2 * 3 ^ 45`. -/
def H1 : Prop := ∀ n : ℕ, 2 * 3 ^ 15 ≤ n → n ≤ 2 * 3 ^ 45 → 2 ∈ Nat.digits 3 (2 ^ n)

/-- The open tail: `2 ^ n` has a ternary digit `2` for every `n > 2 * 3 ^ 45`. -/
def H2 : Prop := ∀ n : ℕ, 2 * 3 ^ 45 < n → 2 ∈ Nat.digits 3 (2 ^ n)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a117971.main := by
  intro h1 h2
  ext n
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hn
    by_cases hlt : n < 2 * 3 ^ 15
    · exact TernaryTwo.checkedPrefix n hlt hn
    · by_cases hle : n ≤ 2 * 3 ^ 45
      · exact absurd (h1 n (by omega) hle) hn
      · exact absurd (h2 n (by omega)) hn
  · rintro (rfl | rfl | rfl) <;> decide

end OMA.R_oeis_a117971_R1
