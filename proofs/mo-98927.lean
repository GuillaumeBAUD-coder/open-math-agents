import OMAStatements.S_mo_98927
import Mathlib

/-!
MathOverflow 98927: a counterexample in `G = S₃ × C₃`. Take `x = (c, 1)` with `c` a 3-cycle and
`y = (1, g)` with `g` a generator of `C₃`. Then `⟨x⟩` and `⟨y⟩` are normal, so `m = n = 1`, and
`⟨x⟩^G ∩ ⟨y⟩^G = 1`; but `⟨xy⟩` is not normal (conjugating `xy = (c, g)` by a transposition gives
`(c², g) ∉ ⟨xy⟩`), so `|⟨xy⟩^G : ⟨xy⟩| ≠ 1`.
-/

open Subgroup

namespace OMA.P98927

/-- `S₃ × C₃`. -/
abbrev G := Equiv.Perm (Fin 3) × Multiplicative (ZMod 3)

/-- A 3-cycle. -/
def c : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2

/-- A transposition. -/
def t : Equiv.Perm (Fin 3) := Equiv.swap 0 1

def g : Multiplicative (ZMod 3) := Multiplicative.ofAdd 1

def x : G := (c, 1)
def y : G := (1, g)

/-- If every conjugate of `a` is a power of `a`, then `⟨a⟩^G ≤ ⟨a⟩`. -/
lemma normalClosure_le_zpowers {H : Type*} [Group H] (a : H)
    (h : ∀ b : H, ∃ k : ℤ, b * a * b⁻¹ = a ^ k) : normalClosure {a} ≤ zpowers a := by
  rw [normalClosure, closure_le]
  intro z hz
  rw [Group.mem_conjugatesOfSet_iff] at hz
  obtain ⟨a', ha', hc⟩ := hz
  rw [Set.mem_singleton_iff] at ha'
  subst ha'
  obtain ⟨b, rfl⟩ := isConj_iff.mp hc
  obtain ⟨k, hk⟩ := h b
  rw [SetLike.mem_coe, hk]
  exact zpow_mem (mem_zpowers _) k

lemma conj_x : ∀ b : G, b * x * b⁻¹ = x ∨ b * x * b⁻¹ = x⁻¹ := by decide

lemma conj_y : ∀ b : G, b * y * b⁻¹ = y := by decide

lemma ncx : normalClosure {x} ≤ zpowers x := by
  apply normalClosure_le_zpowers
  intro b
  rcases conj_x b with h | h
  · exact ⟨1, by rw [h, zpow_one]⟩
  · exact ⟨-1, by rw [h, zpow_neg_one]⟩

lemma ncy : normalClosure {y} ≤ zpowers y := by
  apply normalClosure_le_zpowers
  intro b
  exact ⟨1, by rw [conj_y b, zpow_one]⟩

lemma inter : normalClosure {x} ⊓ normalClosure {y} = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨hx, hy⟩ := mem_inf.mp hz
  obtain ⟨a, rfl⟩ := mem_zpowers_iff.mp (ncx hx)
  obtain ⟨b, hb⟩ := mem_zpowers_iff.mp (ncy hy)
  rw [mem_bot]
  have h1 : (x ^ a).1 = 1 := by
    rw [← hb]
    show (MonoidHom.fst _ _) (y ^ b) = 1
    rw [map_zpow]; simp [y]
  have h2 : (x ^ a).2 = 1 := by
    show (MonoidHom.snd _ _) (x ^ a) = 1
    rw [map_zpow]; simp [x]
  exact Prod.ext h1 h2

lemma xy_order : orderOf (x * y) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by decide) (by decide)

lemma xy_pow (k : ℤ) : (x * y) ^ k = (x * y) ^ (k % 3) := by
  rw [← zpow_mod_orderOf, xy_order]; rfl

lemma pow0 : (x * y) ^ (0 : ℕ) = ((1 : Equiv.Perm (Fin 3)), (1 : Multiplicative (ZMod 3))) := rfl
lemma pow1 : (x * y) ^ (1 : ℕ) = (c, g) := by simp [x, y]
lemma pow2 : (x * y) ^ (2 : ℕ) = (c * c, g * g) := by simp [x, y, pow_two]

lemma not_mem : ((c * c, g) : G) ∉ zpowers (x * y) := by
  rw [mem_zpowers_iff]
  rintro ⟨k, hk⟩
  rw [xy_pow] at hk
  obtain ⟨j, hj, hjk⟩ : ∃ j : ℕ, j < 3 ∧ k % 3 = (j : ℤ) :=
    ⟨(k % 3).toNat, by omega, by omega⟩
  rw [hjk, zpow_natCast] at hk
  interval_cases j
  · rw [pow0] at hk
    have := congrArg Prod.fst hk
    revert this; decide
  · rw [pow1] at hk
    have := congrArg Prod.fst hk
    revert this; decide
  · rw [pow2] at hk
    have := congrArg Prod.snd hk
    revert this; decide

lemma mem_nc : ((c * c, g) : G) ∈ normalClosure {x * y} := by
  have h : ((c * c, g) : G) = (t, 1) * (x * y) * (t, 1)⁻¹ := by decide
  rw [h]
  exact (normalClosure_normal (s := ({x * y} : Set G))).conj_mem (x * y)
    (subset_normalClosure (Set.mem_singleton _)) ((t, 1) : G)

end OMA.P98927

open OMA.P98927 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_98927.main) := by
  intro h
  have e := h G x y inter
  rw [relIndex_eq_one.mpr ncx, relIndex_eq_one.mpr ncy, one_mul, eq_comm,
    relIndex_eq_one] at e
  exact not_mem (e mem_nc)
