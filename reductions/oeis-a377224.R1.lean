import OMAStatements.S_oeis_a377224

-- Reduction oeis-a377224.R1 of A377224: Number of ways to write n as x*(5*x+1) + y*(5*y+1)/2 + z*(5*z+1)/2, where x,y,z are integers with y*(5*y+1) <= z*(5*z+1).
-- Credit: @jarrettbranch
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_oeis_a377224_R1

open OMA.S_oeis_a377224

/-- Every even `n ≥ 2` is representable. -/
def H1 : Prop := ∀ n : ℕ, 2 ≤ n → Even n → IsRepresentable n

/-- Every odd `n ≥ 3` is representable. -/
def H2 : Prop := ∀ n : ℕ, 3 ≤ n → Odd n → IsRepresentable n

/-- `t(5t + 1)` is `0` or at least `4` for every integer `t`. -/
theorem quad_cases (t : ℤ) : t * (5 * t + 1) = 0 ∨ 4 ≤ t * (5 * t + 1) := by
  rcases lt_trichotomy t 0 with h | rfl | h
  · right
    nlinarith
  · left
    ring
  · right
    nlinarith

/-- Each of the three terms is `0` or at least `2`, so they never sum to `1`; `0` is representable
with `x = y = z = 0`. All other `n` are split by parity. -/
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a377224.main := by
  intro h1 h2 n
  constructor
  · rintro ⟨x, y, z, h⟩ rfl
    have hx := quad_cases x
    have hy := quad_cases y
    have hz := quad_cases z
    generalize x * (5 * x + 1) = A at h hx
    generalize y * (5 * y + 1) = B at h hy
    generalize z * (5 * z + 1) = C at h hz
    push_cast at h
    omega
  · intro hn
    rcases (show n = 0 ∨ 2 ≤ n by omega) with rfl | h2n
    · exact ⟨0, 0, 0, by norm_num⟩
    · rcases Nat.even_or_odd n with he | ho
      · exact h1 n h2n he
      · exact h2 n (by obtain ⟨t, ht⟩ := ho; omega) ho

end OMA.R_oeis_a377224_R1
