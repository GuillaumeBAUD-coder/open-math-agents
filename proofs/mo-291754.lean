import OMAStatements.S_mo_291754
import Mathlib

-- Problem: What is the smallest sphere whose surface includes 100 integer points?
-- Credit: @xor2k
-- Idea: if the sphere of radius r has an integer point, r^2 = m is an integer. For m at most 80
-- every integer point lies in the box [-8,8]^3, so the point count equals the size of a finite
-- filter over that box, which the kernel evaluates: 120 points for m = 74, below 100 for m < 74.

open OMA.S_mo_291754

namespace OMA.P_mo_291754

def I : Finset ℤ := (Finset.range 17).image (fun n : ℕ => (n : ℤ) - 8)

def box : Finset (ℤ × ℤ × ℤ) := I ×ˢ I ×ˢ I

def cnt (m : ℤ) : ℕ := (box.filter (fun p => p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 = m)).card

lemma cnt74 : 100 ≤ cnt 74 := by decide +kernel

def rng (s : ℕ) : ℕ → Bool
  | 0 => true
  | n + 1 => decide (cnt ((s + n : ℕ) : ℤ) < 100) && rng s n

lemma rng_spec (s : ℕ) : ∀ n, rng s n = true → ∀ k, s ≤ k → k < s + n → cnt (k : ℤ) < 100 := by
  intro n
  induction n with
  | zero => intro _ k h1 h2; omega
  | succ n ih =>
    intro h k h1 h2
    simp only [rng, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases Nat.lt_or_ge k (s + n) with hk | hk
    · exact ih h.2 k h1 hk
    · have : k = s + n := by omega
      subst this; exact h.1

lemma r0 : rng 0 10 = true := by decide +kernel

lemma r10 : rng 10 10 = true := by decide +kernel

lemma r20 : rng 20 10 = true := by decide +kernel

lemma r30 : rng 30 10 = true := by decide +kernel

lemma r40 : rng 40 10 = true := by decide +kernel

lemma r50 : rng 50 10 = true := by decide +kernel

lemma r60 : rng 60 10 = true := by decide +kernel

lemma r70 : rng 70 4 = true := by decide +kernel

lemma cntSmall (k : ℕ) (hk : k < 74) : cnt (k : ℤ) < 100 := by
  rcases (show k < 10 ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30) ∨ (30 ≤ k ∧ k < 40) ∨ (40 ≤ k ∧ k < 50) ∨ (50 ≤ k ∧ k < 60) ∨ (60 ≤ k ∧ k < 70) ∨ 70 ≤ k by omega) with h | h | h | h | h | h | h | h
  · exact rng_spec 0 _ r0 k (by omega) (by omega)
  · exact rng_spec 10 _ r10 k (by omega) (by omega)
  · exact rng_spec 20 _ r20 k (by omega) (by omega)
  · exact rng_spec 30 _ r30 k (by omega) (by omega)
  · exact rng_spec 40 _ r40 k (by omega) (by omega)
  · exact rng_spec 50 _ r50 k (by omega) (by omega)
  · exact rng_spec 60 _ r60 k (by omega) (by omega)
  · exact rng_spec 70 _ r70 k (by omega) (by omega)

lemma mem_I {x : ℤ} (h1 : -8 ≤ x) (h2 : x ≤ 8) : x ∈ I := by
  simp only [I, Finset.mem_image, Finset.mem_range]
  refine ⟨(x + 8).toNat, by omega, by omega⟩

lemma bound {x y z m : ℤ} (hm : m ≤ 80) (h : x ^ 2 + y ^ 2 + z ^ 2 = m) :
    -8 ≤ x ∧ x ≤ 8 := by
  have hy := sq_nonneg y
  have hz := sq_nonneg z
  constructor <;> nlinarith

lemma key (m : ℤ) (hm : m ≤ 80) (r : ℝ) (hr : r ^ 2 = (m : ℝ)) :
    (spherePoints r).ncard = cnt m := by
  have hset : spherePoints r =
      ↑(box.filter (fun p => p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 = m)) := by
    ext ⟨x, y, z⟩
    simp only [spherePoints, Set.mem_ofPred_eq, Finset.coe_filter, hr]
    constructor
    · intro h
      have h' : x ^ 2 + y ^ 2 + z ^ 2 = m := by exact_mod_cast h
      have hx := bound hm h'
      have hy := bound hm (show y ^ 2 + x ^ 2 + z ^ 2 = m by linarith)
      have hz := bound hm (show z ^ 2 + y ^ 2 + x ^ 2 = m by linarith)
      refine ⟨?_, h'⟩
      simp only [box, Finset.mem_product]
      exact ⟨mem_I hx.1 hx.2, mem_I hy.1 hy.2, mem_I hz.1 hz.2⟩
    · rintro ⟨-, h⟩
      exact_mod_cast h
  rw [hset, Set.ncard_coe_finset]
  rfl

end OMA.P_mo_291754

open OMA.P_mo_291754 in
theorem OMA.solution : type_of% @OMA.S_mo_291754.main := by
  refine ⟨⟨Real.sqrt_nonneg _, ?_⟩, ?_⟩
  · rw [key 74 (by norm_num) _ (by rw [Real.sq_sqrt (by norm_num)]; norm_num)]
    exact cnt74
  · rintro r ⟨hr0, hr⟩
    by_contra hlt
    replace hlt := lt_of_not_ge hlt
    have hne : (spherePoints r).Nonempty :=
      Set.nonempty_of_ncard_ne_zero (by omega)
    obtain ⟨⟨x, y, z⟩, hp⟩ := hne
    simp only [spherePoints, Set.mem_ofPred_eq] at hp
    set m : ℤ := x ^ 2 + y ^ 2 + z ^ 2 with hmdef
    have hmr : r ^ 2 = (m : ℝ) := by rw [hmdef]; push_cast; linarith
    have h74 : r ^ 2 < 74 := by
      have := Real.sq_sqrt (show (0 : ℝ) ≤ 74 by norm_num)
      nlinarith [Real.sqrt_nonneg 74]
    have hm74 : m < 74 := by
      have : (m : ℝ) < 74 := by linarith
      exact_mod_cast this
    have hm0 : 0 ≤ m := by positivity
    have hc := key m (by omega) r hmr
    have := cntSmall m.toNat (by omega)
    rw [show ((m.toNat : ℕ) : ℤ) = m by omega] at this
    omega
