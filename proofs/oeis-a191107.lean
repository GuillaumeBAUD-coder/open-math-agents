import OMAStatements.S_oeis_a191107
import Mathlib

/-!
Credit: @ivillar
Proof: let f(m) be the binary digits of m read in base 3, so f(2m) = 3 f(m) and
f(2m+1) = 3 f(m) + 1, and f is strictly increasing. Let g(m) = 3 f(m) + 1. Then g(0) = 1,
g(2m) = 3 g(m) - 2 and g(2m+1) = 3 g(m) + 1, so (by induction on the generation and by strong
induction on m) the generated set is exactly the range of g. Since g is strictly increasing,
the number of elements of the set below g(m) is m, so the (n-1)-st element is
g(n-1) = 3 f(n-1) + 1 = 3 A003278(n) - 2 = 1 + f(2n-2) = A003278(2n-1).
-/

namespace OMAA191107Helpers
open OMA.S_oeis_a191107

/-- The binary digits of m read in base 3. -/
def f (m : ℕ) : ℕ := Nat.ofDigits 3 (Nat.digits 2 m)

theorem f_even (m : ℕ) : f (2 * m) = 3 * f m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [f]
  · unfold f
    rw [Nat.digits_def' (by norm_num) (by omega), Nat.ofDigits_cons,
      show 2 * m % 2 = 0 by omega, show 2 * m / 2 = m by omega]
    ring

theorem f_odd (m : ℕ) : f (2 * m + 1) = 3 * f m + 1 := by
  unfold f
  rw [Nat.digits_def' (by norm_num) (by omega), Nat.ofDigits_cons,
    show (2 * m + 1) % 2 = 1 by omega, show (2 * m + 1) / 2 = m by omega]
  ring

theorem f_succ (m : ℕ) : f m < f (m + 1) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
  · rw [f_even, f_odd]
    omega
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp only [f]
      norm_num [Nat.ofDigits]
    · have := ih k (by omega)
      rw [f_odd, show 2 * k + 1 + 1 = 2 * (k + 1) by ring, f_even]
      omega

theorem f_mono : StrictMono f := strictMono_nat_of_lt_succ f_succ

def g (m : ℕ) : ℕ := 3 * f m + 1

theorem g_mono : StrictMono g := fun a b h => by
  have := f_mono h
  unfold g
  omega

theorem mem_iff (x : ℕ) : InA191107 x ↔ ∃ m, x = g m := by
  constructor
  · intro hx
    induction hx with
    | base => exact ⟨0, by simp [g, f]⟩
    | step1 _ ih =>
      obtain ⟨m, rfl⟩ := ih
      exact ⟨2 * m, by unfold g; rw [f_even]; omega⟩
    | step2 _ ih =>
      obtain ⟨m, rfl⟩ := ih
      exact ⟨2 * m + 1, by unfold g; rw [f_odd]⟩
  · rintro ⟨m, rfl⟩
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · have : g (2 * 0) = 1 := by simp [g, f]
        rw [this]
        exact InA191107.base
      · have h := InA191107.step1 (ih k (by omega))
        have e : 3 * g k - 2 = g (2 * k) := by unfold g; rw [f_even]; omega
        rwa [e] at h
    · have h := InA191107.step2 (ih k (by omega))
      have e : 3 * g k + 1 = g (2 * k + 1) := by unfold g; rw [f_odd]
      rwa [e] at h

theorem nth_eq (m : ℕ) : Nat.nth InA191107 m = g m := by
  classical
  have hc : Nat.count InA191107 (g m) = m := by
    rw [Nat.count_eq_card_filter_range]
    have hset : (Finset.range (g m)).filter InA191107 = (Finset.range m).image g := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, mem_iff]
      constructor
      · rintro ⟨hx, j, rfl⟩
        exact ⟨j, g_mono.lt_iff_lt.mp hx, rfl⟩
      · rintro ⟨j, hj, rfl⟩
        exact ⟨g_mono hj, j, rfl⟩
    rw [hset, Finset.card_image_of_injective _ g_mono.injective, Finset.card_range]
  have hm : InA191107 (g m) := (mem_iff _).mpr ⟨m, rfl⟩
  have h := Nat.nth_count hm
  rw [hc] at h
  exact h

end OMAA191107Helpers

open OMAA191107Helpers OMA.S_oeis_a191107 in
theorem OMA.solution : type_of% @OMA.S_oeis_a191107.main := by
  refine ⟨fun n hn => ?_, fun n hn => ?_⟩
  · rw [nth_eq]
    unfold g A003278
    rw [show f (n - 1) = Nat.ofDigits 3 (Nat.digits 2 (n - 1)) from rfl]
    omega
  · rw [nth_eq]
    unfold g A003278
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [show 2 * (k + 1) - 1 - 1 = 2 * k by omega, show k + 1 - 1 = k by omega]
    have := f_even k
    unfold f at this
    rw [show f k = Nat.ofDigits 3 (Nat.digits 2 k) from rfl, this]
    ring
