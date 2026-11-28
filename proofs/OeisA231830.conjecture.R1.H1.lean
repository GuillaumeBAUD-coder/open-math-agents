import OMAReductions.R_OeisA231830_conjecture_R1

/-!
# Step H1 of OeisA231830.conjecture.R1: the modular check for primes up to 1000

For every `p ≤ 1000` with `p % 4 = 1` (prime or not, `p > 1`) we run the recurrence
`x ↦ x (x + 1)^2 mod p^2` from `4 mod p^2` for `p` steps in a single pass and test that no
visited value is `-1 mod p^2`. A Boolean checker does this; the kernel evaluates it once
(`decide +kernel`, no `native_decide`), and a short induction turns the checker's output
into the statement about the `Nat.rec` orbit.
-/

namespace OMA.P16A231830

/-- One step of the recurrence modulo `m`. -/
def stp (m x : ℕ) : ℕ := (x * (x + 1) ^ 2) % m

/-- `run m x k`: the first `k` points of the orbit of `x` under `stp m` avoid `-1 mod m`. -/
def run (m : ℕ) : ℕ → ℕ → Bool
  | _, 0 => true
  | x, k + 1 => ((x + 1) % m != 0) && run m (stp m x) k

theorem run_spec (m : ℕ) :
    ∀ k x : ℕ, run m x k = true → ∀ n < k, ((stp m)^[n] x + 1) % m ≠ 0 := by
  intro k
  induction k with
  | zero => intro x _ n hn; omega
  | succ k ih =>
    intro x h n hn
    simp only [run, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    cases n with
    | zero => simpa using h.1
    | succ n =>
      rw [Function.iterate_succ_apply]
      exact ih _ h.2 n (by omega)

theorem orbit_eq (m n : ℕ) :
    Nat.rec (motive := fun _ => ℕ) (4 % m) (fun _ x => (x * (x + 1) ^ 2) % m) n =
      (stp m)^[n] (4 % m) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ← ih]; rfl

/-- The finite check: every modulus `p ^ 2` with `1 < p ≤ 1000` and `p % 4 = 1`. -/
theorem table : ∀ p < 1001, p % 4 = 1 → 1 < p → run (p ^ 2) (4 % p ^ 2) p = true := by
  decide +kernel

end OMA.P16A231830

open OMA.P16A231830 in
theorem OMA.solution : OMA.R_OeisA231830_conjecture_R1.H1 := by
  intro p hp h4 hle n hn
  have key := run_spec (p ^ 2) p (4 % p ^ 2) (table p (by omega) h4 hp.one_lt) n hn
  rw [← orbit_eq] at key
  exact key
