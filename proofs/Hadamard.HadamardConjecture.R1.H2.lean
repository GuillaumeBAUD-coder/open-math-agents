import OMAReductions.R_Hadamard_HadamardConjecture_R1

/-!
# Paley II construction for Hadamard's conjecture (`H2`)

Proves `Hadamard.HadamardConjecture.R1.H2`: for every prime power `q ≡ 1 (mod 4)`,
there exists a Hadamard matrix of order `2 * (q + 1)`.
-/

-- Step Hadamard.HadamardConjecture.R1.H2: hypothesis H2 of reduction Hadamard.HadamardConjecture.R1
-- Credit: @nnkostov
-- H2 := ∀ q : ℕ, IsPrimePow q → q % 4 = 1 → ∃ M, IsHadamard' (n := 2 * (q + 1)) M

open Matrix

namespace OMAPaleyII

section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem jac (hF : ringChar F ≠ 2) :
    ∑ x : F, quadraticChar F x * quadraticChar F (1 - x) = -quadraticChar F (-1) := by
  have h := jacobiSum_nontrivial_inv (quadraticChar_ne_one hF)
  rw [(quadraticChar_isQuadratic F).inv] at h
  exact h

theorem shift (hF : ringChar F ≠ 2) (hpos : quadraticChar F (-1) = 1) {a b : F} (hab : a ≠ b) :
    ∑ c : F, quadraticChar F (c - a) * quadraticChar F (c - b) = -1 := by
  have hd : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  let e : F ≃ F := (Equiv.mulLeft₀ (b - a) hd).trans (Equiv.addLeft a)
  have hsum : ∑ c : F, quadraticChar F (c - a) * quadraticChar F (c - b) =
      ∑ x : F, quadraticChar F x * quadraticChar F (1 - x) := by
    symm
    apply Fintype.sum_equiv e
    intro x
    have hm : e x = a + (b - a) * x := rfl
    rw [hm]
    have h1 : a + (b - a) * x - a = (b - a) * x := by ring
    have h2 : a + (b - a) * x - b = (-1) * ((b - a) * (1 - x)) := by ring
    rw [h1, h2, map_mul, map_mul, map_mul, hpos, one_mul]
    have hsq := quadraticChar_sq_one hd
    linear_combination -(quadraticChar F x * quadraticChar F (1 - x)) * hsq
  rw [hsum, jac hF, hpos]

theorem diag (a : F) :
    ∑ c : F, quadraticChar F (c - a) * quadraticChar F (c - a) = (Fintype.card F : ℤ) - 1 := by
  have : ∀ c : F, quadraticChar F (c - a) * quadraticChar F (c - a) = 1 - if c = a then 1 else 0 := by
    intro c
    split_ifs with h
    · simp [h]
    · rw [← pow_two, sub_zero]; exact quadraticChar_sq_one (sub_ne_zero.mpr h)
  rw [Finset.sum_congr rfl (fun c _ => this c), Finset.sum_sub_distrib, Finset.sum_ite_eq']
  simp

noncomputable def chi (x : F) : ℝ := ((quadraticChar F x : ℤ) : ℝ)

theorem sumchi (hF : ringChar F ≠ 2) (b : F) : ∑ c : F, chi (c - b) = 0 := by
  have h : ∑ c : F, quadraticChar F (c - b) = ∑ c : F, quadraticChar F c :=
    Fintype.sum_equiv (Equiv.subRight b) _ _ (fun _ => rfl)
  rw [quadraticChar_sum_zero hF] at h
  have := congrArg (Int.cast : ℤ → ℝ) h
  push_cast at this
  simpa [chi] using this

theorem shiftR (hF : ringChar F ≠ 2) (hpos : quadraticChar F (-1) = 1) {a b : F} (hab : a ≠ b) :
    ∑ c : F, chi (c - a) * chi (c - b) = -1 := by
  have := congrArg (Int.cast : ℤ → ℝ) (shift hF hpos hab)
  push_cast at this
  simpa [chi] using this

theorem diagR (a : F) : ∑ c : F, chi (c - a) * chi (c - a) = (Fintype.card F : ℝ) - 1 := by
  have := congrArg (Int.cast : ℤ → ℝ) (diag a)
  push_cast at this
  simpa [chi] using this

theorem chi_zero : chi (0 : F) = 0 := by simp [chi]

theorem chi_symm (hpos : quadraticChar F (-1) = 1) (a b : F) : chi (b - a) = chi (a - b) := by
  have h : b - a = (-1) * (a - b) := by ring
  simp only [chi, h, map_mul, hpos, one_mul]

noncomputable def Q : Matrix (Option F) (Option F) ℝ := fun x y =>
  match x, y with
  | none, none => 0
  | none, some _ => 1
  | some _, none => 1
  | some a, some b => chi (a - b)

theorem Q_symm (hpos : quadraticChar F (-1) = 1) (x y : Option F) : Q x y = Q y x := by
  rcases x with _ | a <;> rcases y with _ | b <;> simp [Q, chi_symm hpos]

theorem Q_diag (x : Option F) : Q x x = 0 := by
  rcases x with _ | a <;> simp [Q, chi_zero]

theorem Q_off {x y : Option F} (hxy : x ≠ y) : Q x y = 1 ∨ Q x y = -1 := by
  rcases x with _ | a <;> rcases y with _ | b
  · exact (hxy rfl).elim
  · exact Or.inl rfl
  · exact Or.inl rfl
  · have hd : a - b ≠ 0 := sub_ne_zero.mpr (fun h => hxy (congrArg some h))
    rcases quadraticChar_dichotomy hd with h | h <;> simp [Q, chi, h]

theorem Q_col (hF : ringChar F ≠ 2) (hpos : quadraticChar F (-1) = 1) (x y : Option F) :
    ∑ z, Q z x * Q z y = if x = y then (Fintype.card F : ℝ) else 0 := by
  rw [Fintype.sum_option]
  rcases x with _ | a <;> rcases y with _ | b
  · simp [Q]
  · simp [Q, sumchi hF b]
  · simp [Q, sumchi hF a]
  · simp only [Q, one_mul, Option.some.injEq]
    by_cases hab : a = b
    · subst hab
      simp [diagR]
    · simp only [hab, if_false]
      rw [shiftR hF hpos hab]
      ring

def A : Bool → Bool → ℝ
  | false, false => 1
  | false, true => 1
  | true, false => 1
  | true, true => -1

def B : Bool → Bool → ℝ
  | false, false => 1
  | false, true => -1
  | true, false => -1
  | true, true => -1

theorem A_entries (w u : Bool) : A w u = 1 ∨ A w u = -1 := by
  cases w <;> cases u <;> simp [A]

theorem B_entries (w u : Bool) : B w u = 1 ∨ B w u = -1 := by
  cases w <;> cases u <;> simp [B]

theorem sum_AA (u v : Bool) : ∑ w : Bool, A w u * A w v = if u = v then 2 else 0 := by
  cases u <;> cases v <;> simp [A] <;> norm_num

theorem sum_BB (u v : Bool) : ∑ w : Bool, B w u * B w v = if u = v then 2 else 0 := by
  cases u <;> cases v <;> simp [B] <;> norm_num

theorem sum_AB_BA (u v : Bool) : ∑ w : Bool, (A w u * B w v + B w u * A w v) = 0 := by
  cases u <;> cases v <;> simp [A, B]

noncomputable def H : Matrix (Option F × Bool) (Option F × Bool) ℝ := fun p r =>
  Q p.1 r.1 * A p.2 r.2 + if p.1 = r.1 then B p.2 r.2 else 0

theorem H_entries (p r : Option F × Bool) : H p r ∈ ({1, -1} : Finset ℝ) := by
  by_cases h : p.1 = r.1
  · simp only [H, h, Q_diag, zero_mul, zero_add, if_true, Finset.mem_insert, Finset.mem_singleton]
    exact B_entries p.2 r.2
  · simp only [H, h, if_false, add_zero, Finset.mem_insert, Finset.mem_singleton]
    rcases Q_off h with hq | hq <;> rcases A_entries p.2 r.2 with ha | ha <;> rw [hq, ha] <;> norm_num

theorem H_col (hF : ringChar F ≠ 2) (hpos : quadraticChar F (-1) = 1) (x y : Option F) (u v : Bool) :
    ∑ p : Option F × Bool, H p (x, u) * H p (y, v) =
      if (x, u) = (y, v) then 2 * ((Fintype.card F : ℝ) + 1) else 0 := by
  rw [Fintype.sum_prod_type]
  have expand (z : Option F) (w : Bool) :
      H (z, w) (x, u) * H (z, w) (y, v) =
        (Q z x * Q z y) * (A w u * A w v) +
        (Q z x * (if z = y then B w v else 0) * A w u +
         Q z y * (if z = x then B w u else 0) * A w v) +
        (if z = x then B w u else 0) * (if z = y then B w v else 0) := by
    dsimp [H]
    ring
  simp_rw [expand, Finset.sum_add_distrib]
  have t1 : ∑ z : Option F, ∑ w : Bool, (Q z x * Q z y) * (A w u * A w v) =
      (if x = y then (Fintype.card F : ℝ) else 0) * (if u = v then 2 else 0) := by
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul, Q_col hF hpos x y, sum_AA u v]
  have t2a : ∑ z : Option F, ∑ w : Bool, Q z x * (if z = y then B w v else 0) * A w u =
      Q y x * ∑ w : Bool, A w u * B w v := by
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    have h' : ∀ z : Option F, Q z x * (if z = y then B w v else 0) * A w u =
        if z = y then Q y x * (A w u * B w v) else 0 := fun z => by
      by_cases hz : z = y
      · subst hz; simp only [if_true]; ring
      · simp [hz]
    rw [Finset.sum_congr rfl (fun z _ => h' z), Finset.sum_ite_eq']
    simp
  have t2b : ∑ z : Option F, ∑ w : Bool, Q z y * (if z = x then B w u else 0) * A w v =
      Q x y * ∑ w : Bool, B w u * A w v := by
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    have h' : ∀ z : Option F, Q z y * (if z = x then B w u else 0) * A w v =
        if z = x then Q x y * (B w u * A w v) else 0 := fun z => by
      by_cases hz : z = x
      · subst hz; simp [mul_assoc]
      · simp [hz]
    rw [Finset.sum_congr rfl (fun z _ => h' z), Finset.sum_ite_eq']
    simp
  have t3 : ∑ z : Option F, ∑ w : Bool,
      (if z = x then B w u else 0) * (if z = y then B w v else 0) =
      if x = y then (if u = v then 2 else 0) else 0 := by
    have h' : ∀ z : Option F, (∑ w : Bool, (if z = x then B w u else 0) * (if z = y then B w v else 0)) =
        if z = x then (if x = y then ∑ w : Bool, B w u * B w v else 0) else 0 := fun z => by
      by_cases hx : z = x
      · subst hx
        by_cases hy : z = y
        · simp [hy]
        · simp [hy]
      · simp [hx]
    rw [Finset.sum_congr rfl (fun z _ => h' z), Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true, sum_BB u v]
  rw [t1, t2a, t2b, t3, Q_symm hpos y x, ← mul_add, ← Finset.sum_add_distrib, sum_AB_BA u v,
    mul_zero]
  by_cases hxy : x = y <;> by_cases huv : u = v <;> simp [hxy, huv] <;> ring

end

theorem paleyII {F : Type*} [Field F] [Fintype F] [DecidableEq F] (q : ℕ)
    (hF : ringChar F ≠ 2) (hpos : quadraticChar F (-1) = 1) (hcard : Fintype.card F = q) :
    ∃ M, Hadamard.IsHadamard' (n := 2 * (q + 1)) M := by
  let e : Fin (2 * (q + 1)) ≃ Option F × Bool :=
    (Fintype.equivFinOfCardEq (by simp [hcard]; ring : Fintype.card (Option F × Bool) = 2 * (q + 1))).symm
  refine ⟨H.submatrix e e, fun i j => H_entries _ _, ?_⟩
  ext i j
  rw [Matrix.mul_apply]
  simp only [transpose_apply, submatrix_apply]
  rw [show ∑ k, H (e k) (e i) * H (e k) (e j) = ∑ p : Option F × Bool, H p (e i) * H p (e j) from
    Fintype.sum_equiv e _ _ (fun _ => rfl)]
  rw [H_col hF hpos (e i).1 (e j).1 (e i).2 (e j).2, Matrix.natCast_apply]
  have hij : ((e i).1, (e i).2) = ((e j).1, (e j).2) ↔ i = j := by
    rw [Prod.ext_iff]
    constructor
    · intro h
      exact e.injective (Prod.ext h.1 h.2)
    · intro h
      subst h
      exact ⟨rfl, rfl⟩
  simp only [hij, hcard]
  split_ifs <;> push_cast <;> ring

end OMAPaleyII

theorem OMA.solution : OMA.R_Hadamard_HadamardConjecture_R1.H2 := by
  intro q hq h1
  obtain ⟨p, k, hp, hk, rfl⟩ := hq
  have hp' : p.Prime := Nat.prime_iff.mpr hp
  have := Fact.mk hp'
  classical
  let _ : Fintype (GaloisField p k) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField p k) = p ^ k := by
    rw [← Nat.card_eq_fintype_card]; exact GaloisField.card p k hk.ne'
  have hp2 : p ≠ 2 := by
    rintro rfl
    have : 2 ∣ 2 ^ k := dvd_pow_self 2 hk.ne'
    omega
  have hF : ringChar (GaloisField p k) ≠ 2 := by
    rw [ringChar.eq (GaloisField p k) p]; exact hp2
  have hpos : quadraticChar (GaloisField p k) (-1) = 1 := by
    rw [quadraticChar_neg_one hF, hcard]
    exact ZMod.χ₄_nat_one_mod_four h1
  exact OMAPaleyII.paleyII (p ^ k) hF hpos hcard
