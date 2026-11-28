import OMAReductions.R_OeisA219023_conjecture_2_R1
import Mathlib

namespace OMA.W

def prAux (n : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, d => if n < d * d then true else if n % d = 0 then false else prAux n f (d + 1)

def pr (n : ℕ) : Bool := decide (2 ≤ n) && prAux n n 2

theorem prAux_sound (n : ℕ) (hn : 2 ≤ n) : ∀ (f d : ℕ), prAux n f d = true →
    (∀ m, 2 ≤ m → m < d → ¬ m ∣ n) → n.Prime := by
  intro f
  induction f with
  | zero => intro d h; simp [prAux] at h
  | succ f ih =>
    intro d h hd
    unfold prAux at h
    split_ifs at h with h1 h2
    · by_contra hp
      have h3 := Nat.minFac_sq_le_self (by omega) hp
      have h4 : n.minFac < d := by
        by_contra hc
        have : d * d ≤ n.minFac * n.minFac := Nat.mul_le_mul (by omega) (by omega)
        nlinarith
      exact hd _ (Nat.minFac_prime (by omega)).two_le h4 (Nat.minFac_dvd n)
    · exact ih (d + 1) h (fun m hm hlt => by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h5 | h5
        · exact hd m hm h5
        · subst h5; exact fun hdv => h2 (Nat.mod_eq_zero_of_dvd hdv))

theorem pr_sound {n : ℕ} (h : pr n = true) : n.Prime := by
  unfold pr at h
  rw [Bool.and_eq_true, decide_eq_true_eq] at h
  exact prAux_sound n h.1 n 2 h.2 (fun m hm hlt => by omega)

def all (f : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | k + 1 => f k && all f k

theorem all_sound (f : ℕ → Bool) : ∀ k, all f k = true → ∀ i, i < k → f i = true := by
  intro k
  induction k with
  | zero => intro _ i hi; omega
  | succ k ih =>
    intro h i hi
    unfold all at h
    rw [Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h5 | h5
    · exact ih h.2 i h5
    · subst h5; exact h.1

def test (n d : ℕ) : Bool :=
  pr d && decide (n < d) && decide (d < 2 * n) && pr (n ^ 2 - n + d) && pr (n ^ 2 + n - d)

def T : ℕ := 28586603279468615998719551809155907244967336806331871514692221871473715950133596523577537645725570824940022168400101434618642276933428345993293015925330511036011302479139964822062420633100719511341474889151216807771913714554773465320957

theorem key : all (fun i => test (3513 + i) (T / 16384 ^ i % 16384)) 56 = true := by
  decide +kernel

end OMA.W

open OMA.W in
theorem OMA.solution : OMA.R_OeisA219023_conjecture_2_R1.H1 := by
  intro n h1 h2
  have h := all_sound _ _ key (n - 3513) (by omega)
  rw [show 3513 + (n - 3513) = n by omega] at h
  generalize T / _ ^ _ % _ = d at h
  unfold test at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨a, b⟩, c⟩, e⟩, f⟩ := h
  exact ⟨d, pr_sound a, b, c, pr_sound e, pr_sound f⟩
