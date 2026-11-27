import FormalConjectures.Mathoverflow.«486451»

-- Problem: MathOverflow 486451 — a semiring with a unique maximal left ideal but more than one
-- maximal right ideal.
-- Credit: @timlantin (the owner of the agent is credited as the solver)
-- Written with Claude Code (AI-assisted). No prior example was found in the MathOverflow thread
-- (whose only answer, by Firsching, settles the sibling question), in Gupta and Chaudhari,
-- Right Local Semirings (Asian-Eur. J. Math. 2013), or in the upstream file history.
--
-- Construction: R = {0} ∪ ℕ³. A triple (j, k, n) is the map f_{j,k} on ℕ ∪ {∞}
-- (m ↦ 0 for m ≤ j, m ↦ m - j + k otherwise) tagged with n ∈ ℕ. Addition is pointwise min on
-- the maps and + on tags; multiplication is composition on the maps and × on tags.
-- (j,k,n) has a left inverse iff j = 0 and n = 1, and a right inverse iff k = 0 and n = 1.
-- Left side: if a + b has a left inverse then one of a, b does, so the non-left-invertible
-- elements form the unique maximal left ideal. Right side: x = (0,1,1) and y = (0,0,0) have no
-- right inverse but x + y = 1, which gives two distinct maximal right ideals.

namespace OMA

def MR : Type := Option (ℕ × ℕ × ℕ)

def mrAdd : MR → MR → MR
  | none, none => none
  | none, some b => some b
  | some a, none => some a
  | some (j, k, n), some (j', k', n') =>
      some (max j j', min (max j j' - j + k) (max j j' - j' + k'), n + n')

def mrMul : MR → MR → MR
  | none, _ => none
  | some _, none => none
  | some (j, k, n), some (j', k', n') => some (j' + (j - k'), k + (k' - j), n * n')

theorem mk_eq {a b c d e f : ℕ} (h1 : a = d) (h2 : b = e) (h3 : c = f) :
    (some (a, b, c) : MR) = some (d, e, f) := by
  subst h1 h2 h3; rfl

theorem mrAdd_assoc (a b c : MR) : mrAdd (mrAdd a b) c = mrAdd a (mrAdd b c) := by
  rcases a with _ | ⟨a1, a2, a3⟩ <;> rcases b with _ | ⟨b1, b2, b3⟩ <;>
    rcases c with _ | ⟨c1, c2, c3⟩ <;>
    simp only [mrAdd] <;>
    first | rfl | (apply mk_eq <;> omega)

theorem mrAdd_comm (a b : MR) : mrAdd a b = mrAdd b a := by
  rcases a with _ | ⟨a1, a2, a3⟩ <;> rcases b with _ | ⟨b1, b2, b3⟩ <;>
    simp only [mrAdd] <;>
    first | rfl | (apply mk_eq <;> omega)

theorem mrMul_assoc (a b c : MR) : mrMul (mrMul a b) c = mrMul a (mrMul b c) := by
  rcases a with _ | ⟨a1, a2, a3⟩ <;> rcases b with _ | ⟨b1, b2, b3⟩ <;>
    rcases c with _ | ⟨c1, c2, c3⟩ <;>
    simp only [mrMul] <;>
    first | rfl | (apply mk_eq <;> first | omega | ring)

theorem mr_left_distrib (a b c : MR) : mrMul a (mrAdd b c) = mrAdd (mrMul a b) (mrMul a c) := by
  rcases a with _ | ⟨a1, a2, a3⟩ <;> rcases b with _ | ⟨b1, b2, b3⟩ <;>
    rcases c with _ | ⟨c1, c2, c3⟩ <;>
    simp only [mrMul, mrAdd] <;>
    first | rfl | (apply mk_eq <;> first | omega | ring)

theorem mr_right_distrib (a b c : MR) : mrMul (mrAdd a b) c = mrAdd (mrMul a c) (mrMul b c) := by
  rcases a with _ | ⟨a1, a2, a3⟩ <;> rcases b with _ | ⟨b1, b2, b3⟩ <;>
    rcases c with _ | ⟨c1, c2, c3⟩ <;>
    simp only [mrMul, mrAdd] <;>
    first | rfl | (apply mk_eq <;> first | omega | ring)

instance : Zero MR := ⟨none⟩
instance : One MR := ⟨some (0, 0, 1)⟩
instance : Add MR := ⟨mrAdd⟩
instance : Mul MR := ⟨mrMul⟩

instance : Semiring MR where
  add_assoc := mrAdd_assoc
  zero_add := by rintro (_ | ⟨a, b, c⟩) <;> rfl
  add_zero := by rintro (_ | ⟨a, b, c⟩) <;> rfl
  add_comm := mrAdd_comm
  nsmul := nsmulRec
  nsmul_zero := fun _ => rfl
  nsmul_succ := fun _ _ => rfl
  left_distrib := mr_left_distrib
  right_distrib := mr_right_distrib
  zero_mul := by rintro (_ | ⟨a, b, c⟩) <;> rfl
  mul_zero := by rintro (_ | ⟨a, b, c⟩) <;> rfl
  mul_assoc := mrMul_assoc
  one_mul := by
    rintro (_ | ⟨a, b, c⟩)
    · rfl
    · exact mk_eq (by omega) (by omega) (by omega)
  mul_one := by
    rintro (_ | ⟨a, b, c⟩)
    · rfl
    · exact mk_eq (by omega) (by omega) (by omega)



theorem two_maximal_right {R : Type*} [Semiring R] (x y : R) (hx : ∀ r, x * r ≠ 1) (hy : ∀ r, y * r ≠ 1)
    (hxy : ∃ r, (x + y) * r = 1) :
    ∃ I J : Ideal Rᵐᵒᵖ, I.IsMaximal ∧ J.IsMaximal ∧ I ≠ J := by
  obtain ⟨r, hr⟩ := hxy
  have hIx : Ideal.span ({MulOpposite.op x} : Set Rᵐᵒᵖ) ≠ ⊤ := by
    rw [Ne, Ideal.eq_top_iff_one, Ideal.mem_span_singleton']
    rintro ⟨s, hs⟩
    exact hx s.unop (by simpa using congrArg MulOpposite.unop hs)
  have hIy : Ideal.span ({MulOpposite.op y} : Set Rᵐᵒᵖ) ≠ ⊤ := by
    rw [Ne, Ideal.eq_top_iff_one, Ideal.mem_span_singleton']
    rintro ⟨s, hs⟩
    exact hy s.unop (by simpa using congrArg MulOpposite.unop hs)
  obtain ⟨I, hI, hxI⟩ := Ideal.exists_le_maximal _ hIx
  obtain ⟨J, hJ, hyJ⟩ := Ideal.exists_le_maximal _ hIy
  refine ⟨I, J, hI, hJ, ?_⟩
  rintro rfl
  have h1 : MulOpposite.op x ∈ I := hxI (Ideal.subset_span rfl)
  have h2 : MulOpposite.op y ∈ I := hyJ (Ideal.subset_span rfl)
  have h3 : MulOpposite.op r * MulOpposite.op (x + y) ∈ I :=
    I.mul_mem_left _ (by simpa using I.add_mem h1 h2)
  have e : MulOpposite.op r * MulOpposite.op (x + y) = 1 := by
    rw [← MulOpposite.op_mul, hr, MulOpposite.op_one]
  rw [e] at h3
  exact hI.ne_top ((Ideal.eq_top_iff_one _).2 h3)

theorem unique_maximal_left {R : Type*} [Semiring R] (h10 : (1 : R) ≠ 0)
    (hL : ∀ a b : R, (∃ w, w * (a + b) = 1) → (∃ w, w * a = 1) ∨ (∃ w, w * b = 1)) :
    ∃! I : Ideal R, I.IsMaximal := by
  let N : Ideal R :=
    { carrier := {x | ∀ w, w * x ≠ 1}
      add_mem' := by
        intro a b ha hb w hw
        rcases hL a b ⟨w, hw⟩ with ⟨u, hu⟩ | ⟨u, hu⟩
        · exact ha u hu
        · exact hb u hu
      zero_mem' := by intro w hw; simp at hw; exact h10 hw.symm
      smul_mem' := by
        intro c x hx w hw
        exact hx (w * c) (by simpa [smul_eq_mul, mul_assoc] using hw) }
  have hNtop : N ≠ ⊤ := by
    intro h
    have : (1 : R) ∈ N := h ▸ Submodule.mem_top
    exact this 1 (one_mul 1)
  have hle : ∀ I : Ideal R, I ≠ ⊤ → I ≤ N := by
    intro I hI x hx w hw
    apply hI
    rw [Ideal.eq_top_iff_one, ← hw]
    exact I.mul_mem_left w hx
  have hNmax : N.IsMaximal := by
    refine ⟨⟨hNtop, fun J hJ => ?_⟩⟩
    by_contra hJt
    exact (not_le_of_gt hJ) (hle J hJt)
  refine ⟨N, hNmax, fun I hI => ?_⟩
  exact hI.eq_of_le hNtop (hle I hI.ne_top)


def mk (j k n : ℕ) : MR := some (j, k, n)

theorem mk_mul (j k n j' k' n' : ℕ) :
    mk j k n * mk j' k' n' = mk (j' + (j - k')) (k + (k' - j)) (n * n') := rfl

theorem mk_add (j k n j' k' n' : ℕ) :
    mk j k n + mk j' k' n' =
      mk (max j j') (min (max j j' - j + k) (max j j' - j' + k')) (n + n') := rfl

theorem mk_one : (1 : MR) = mk 0 0 1 := rfl

theorem mk_inj {a b c d e f : ℕ} (h : mk a b c = mk d e f) : a = d ∧ b = e ∧ c = f := by
  have h' : (some (a, b, c) : Option (ℕ × ℕ × ℕ)) = some (d, e, f) := h
  simp only [Option.some.injEq, Prod.mk.injEq] at h'
  exact h'

theorem mr_left_inv (j k n : ℕ) (h : ∃ w : MR, w * mk j k n = 1) : j = 0 ∧ n = 1 := by
  obtain ⟨w, hw⟩ := h
  rcases w with _ | ⟨a, b, c⟩
  · cases hw
  · have hw' := mk_inj ((mk_mul a b c j k n).symm.trans hw)
    exact ⟨by omega, Nat.eq_one_of_mul_eq_one_left hw'.2.2⟩

theorem mr_left_inv_of (k : ℕ) : ∃ w : MR, w * mk 0 k 1 = 1 :=
  ⟨mk k 0 1, by rw [mk_mul, mk_one]; congr 1 <;> omega⟩

theorem mr_hL (a b : MR) (h : ∃ w, w * (a + b) = 1) : (∃ w, w * a = 1) ∨ (∃ w, w * b = 1) := by
  rcases a with _ | ⟨j, k, n⟩
  · right; obtain ⟨w, hw⟩ := h
    have e : w * (0 + b) = 1 := hw
    rw [zero_add] at e; exact ⟨w, e⟩
  rcases b with _ | ⟨j', k', n'⟩
  · left; obtain ⟨w, hw⟩ := h
    have e : w * (mk j k n + 0) = 1 := hw
    rw [add_zero] at e; exact ⟨w, e⟩
  have h0 : ∃ w, w * (mk j k n + mk j' k' n') = 1 := h
  rw [mk_add] at h0
  obtain ⟨h1, h2⟩ := mr_left_inv _ _ _ h0
  have hj : j = 0 := by omega
  have hj' : j' = 0 := by omega
  subst hj hj'
  rcases Nat.add_eq_one_iff.mp h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · right; exact mr_left_inv_of k'
  · left; exact mr_left_inv_of k

theorem mr_one_ne_zero : (1 : MR) ≠ 0 := by intro h; cases h

end OMA

open OMA in
theorem OMA.solution : type_of% @Mathoverflow486451.exists_semiring_unique_left_maximal_not_unique_right_maximal := by
  refine ⟨MR, inferInstance, unique_maximal_left mr_one_ne_zero mr_hL, ?_⟩
  refine two_maximal_right (mk 0 1 1) (mk 0 0 0) ?_ ?_ ⟨1, rfl⟩
  · rintro (_ | ⟨a, b, c⟩) h
    · cases h
    · have h' := mk_inj ((mk_mul 0 1 1 a b c).symm.trans h)
      omega
  · rintro (_ | ⟨a, b, c⟩) h
    · cases h
    · have h' := mk_inj ((mk_mul 0 0 0 a b c).symm.trans h)
      omega
