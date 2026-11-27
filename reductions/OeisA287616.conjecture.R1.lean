import FormalConjectures.OEIS.«287616»

/-! Primitive ternary representations and local descent for A287616.

This follows the quadratic form and rank in Cao, Guo, Qiu, Feng and Gao,
Every Nonnegative Integer Is a Sum of a Triangular, a Pentagonal, and a
Heptagonal Number, arXiv:2606.26035, Sections 2–4 and 7.

The lexicographic rank uses two bounded defect counts followed by the
coordinate sum. For fixed norm 120n + 23 the coordinate sum is at most
three times the norm, so the natural-valued rank below encodes the same
order. The two hypotheses leave the primitive seed and the local
descent as separate tasks.
-/

namespace OMA.R_OeisA287616_conjecture_R1

private theorem least_valid_is_good {α : Type} (rank : α → ℕ)
    (valid good : α → Prop)
    (move : ∀ a, valid a → ¬ good a → ∃ b, valid b ∧ rank b < rank a)
    (seed : ∃ a, valid a) : ∃ a, valid a ∧ good a := by
  classical
  let P (k : ℕ) := ∃ a, valid a ∧ rank a = k
  have hex : ∃ k, P k := by
    obtain ⟨a, ha⟩ := seed
    exact ⟨rank a, a, ha, rfl⟩
  obtain ⟨a, ha, heq⟩ := Nat.find_spec hex
  refine ⟨a, ha, ?_⟩
  by_contra hbad
  obtain ⟨b, hb, hlt⟩ := move a ha hbad
  exact (not_lt_of_ge (Nat.find_min' hex (show P (rank b) from ⟨b, hb, rfl⟩)))
    (by simpa only [heq] using hlt)

private theorem twice_figurate (x k : ℕ) (hk : Odd k) :
    2 * (x * (k * x + 1) / 2) = x * (k * x + 1) := by
  have hEven : Even (x * (k * x + 1)) := by
    rcases Nat.even_or_odd x with hx | hx
    · exact hx.mul_right _
    · exact ((hk.mul hx).add_one).mul_left _
  have hm : x * (k * x + 1) % 2 = 0 := Nat.even_iff.mp hEven
  have hdivide := Nat.mod_add_div (x * (k * x + 1)) 2
  omega

private theorem good_rep_gives_sum (n u v w : ℕ)
    (hn : 15 * u ^ 2 + 5 * v ^ 2 + 3 * w ^ 2 = 120 * n + 23)
    (hu : u % 2 = 1) (hv : v % 6 = 1) (hw : w % 10 = 1) :
    OeisA287616.A n := by
  let x := u / 2
  let y := v / 6
  let z := w / 10
  have hux : u = 2 * x + 1 := by dsimp [x]; omega
  have hvy : v = 6 * y + 1 := by dsimp [y]; omega
  have hwz : w = 10 * z + 1 := by dsimp [z]; omega
  have hx : 2 * (x * (x + 1) / 2) = x * (x + 1) := by
    simpa only [one_mul] using twice_figurate x 1 (by decide)
  have hy := twice_figurate y 3 (by decide)
  have hz := twice_figurate z 5 (by decide)
  have hsquare :
      120 * (x * (x + 1) / 2 + y * (3 * y + 1) / 2 + z * (5 * z + 1) / 2) + 23 =
        15 * u ^ 2 + 5 * v ^ 2 + 3 * w ^ 2 := by
    calc
      _ = 60 * (2 * (x * (x + 1) / 2)) + 60 * (2 * (y * (3 * y + 1) / 2)) +
          60 * (2 * (z * (5 * z + 1) / 2)) + 23 := by ring
      _ = 60 * (x * (x + 1)) + 60 * (y * (3 * y + 1)) +
          60 * (z * (5 * z + 1)) + 23 := by rw [hx, hy, hz]
      _ = _ := by rw [hux, hvy, hwz]; ring
  refine ⟨x, y, z, ?_⟩
  omega

private theorem normalize_of_descent
    (rank : ℕ → ℕ → ℕ → ℕ → ℕ)
    (move : ∀ n u v w : ℕ,
      15 * u ^ 2 + 5 * v ^ 2 + 3 * w ^ 2 = 120 * n + 23 →
      u.gcd (v.gcd w) = 1 →
      ¬ (u % 2 = 1 ∧ v % 6 = 1 ∧ w % 10 = 1) →
      ∃ u' v' w' : ℕ,
        15 * u' ^ 2 + 5 * v' ^ 2 + 3 * w' ^ 2 = 120 * n + 23 ∧
        u'.gcd (v'.gcd w') = 1 ∧ rank n u' v' w' < rank n u v w)
    (n : ℕ)
    (seed : ∃ u v w : ℕ,
      15 * u ^ 2 + 5 * v ^ 2 + 3 * w ^ 2 = 120 * n + 23 ∧ u.gcd (v.gcd w) = 1) :
    OeisA287616.A n := by
  let valid (a : ℕ × ℕ × ℕ) :=
    15 * a.1 ^ 2 + 5 * a.2.1 ^ 2 + 3 * a.2.2 ^ 2 = 120 * n + 23 ∧
    a.1.gcd (a.2.1.gcd a.2.2) = 1
  let good (a : ℕ × ℕ × ℕ) := a.1 % 2 = 1 ∧ a.2.1 % 6 = 1 ∧ a.2.2 % 10 = 1
  let mass (a : ℕ × ℕ × ℕ) := rank n a.1 a.2.1 a.2.2
  have hmove : ∀ a, valid a → ¬ good a → ∃ b, valid b ∧ mass b < mass a := by
    rintro ⟨u, v, w⟩ ⟨hq, hprim⟩ hn
    obtain ⟨u', v', w', hq', hprim', hlt⟩ := move n u v w hq hprim hn
    exact ⟨(u', v', w'), ⟨hq', hprim'⟩, hlt⟩
  have hseed : ∃ a, valid a := by
    obtain ⟨u, v, w, hq, hprim⟩ := seed
    exact ⟨(u, v, w), hq, hprim⟩
  obtain ⟨⟨u, v, w⟩, ⟨hq, _⟩, ⟨hu, hv, hw⟩⟩ :=
    least_valid_is_good mass valid good hmove hseed
  exact good_rep_gives_sum n u v w hq hu hv hw

def H1 : Prop :=
  ∀ n : ℕ, ∃ u v w : ℕ,
    15 * u ^ 2 + 5 * v ^ 2 + 3 * w ^ 2 = 120 * n + 23 ∧ u.gcd (v.gcd w) = 1

def H2 : Prop :=
  let allOdd (u v w : ℕ) := u % 2 = 1 ∧ v % 2 = 1 ∧ w % 2 = 1
  let rank (n u v w : ℕ) :=
    let badV := if allOdd u v w ∧ v % 6 = 1 then 0 else 1
    let badW := if allOdd u v w ∧ w % 10 = 1 then 0 else 1
    let regretV := if allOdd u v w ∧ u % 4 ≠ v % 4 then 0 else badV
    let regretW := if (u + w) % 3 = 0 then 0 else badW
    let evenPenalty := if allOdd u v w then 0 else 2
    (5 * (badV + badW) + regretV + regretW + evenPenalty) *
      (3 * (120 * n + 23) + 1) + u + v + w
  ∀ n u v w : ℕ,
    15 * u ^ 2 + 5 * v ^ 2 + 3 * w ^ 2 = 120 * n + 23 →
    u.gcd (v.gcd w) = 1 →
    ¬ (u % 2 = 1 ∧ v % 6 = 1 ∧ w % 10 = 1) →
    ∃ u' v' w' : ℕ,
      15 * u' ^ 2 + 5 * v' ^ 2 + 3 * w' ^ 2 = 120 * n + 23 ∧
      u'.gcd (v'.gcd w') = 1 ∧ rank n u' v' w' < rank n u v w

theorem main : H1 → H2 → type_of% @OeisA287616.conjecture := by
  intro hseed hmove n
  exact normalize_of_descent _ hmove n (hseed n)

end OMA.R_OeisA287616_conjecture_R1
