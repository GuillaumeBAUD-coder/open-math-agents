import FormalConjectures.ErdosProblems.«770»

-- Problem: Erdős Problem 770 — odd h unbounded
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/770.lean:51 (declaration Erdos770.erdos_770.variants.odd_h_unbounded)
-- Credit: @Genbox (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
namespace OMA770

theorem key (K : ℕ) : ∃ p, p.Prime ∧ K < p ∧ p % 4 = 3 ∧
    ∀ i : ℕ, 0 < i → i ≤ K → ((i : ZMod p)) ^ (p / 2) = 1 := by
  have hM : NeZero (8 * K.factorial) := ⟨by positivity⟩
  obtain ⟨p, hpK, hp, hpa⟩ := Nat.forall_exists_prime_gt_and_eq_mod
    (q := 8 * K.factorial) (a := -1) isUnit_one.neg K
  have hdvd : 8 * K.factorial ∣ p + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]; push_cast; rw [hpa]; ring
  have h8 : 8 ∣ p + 1 := Dvd.dvd.trans (Dvd.intro _ rfl) hdvd
  have hp4 : p % 4 = 3 := by omega
  have hp8 : p % 8 = 7 := by omega
  have := Fact.mk hp
  refine ⟨p, hp, hpK, hp4, ?_⟩
  have hprime : ∀ q : ℕ, q.Prime → q ≤ K → ((q : ZMod p)) ^ (p / 2) = 1 := by
    intro q hq hqK
    have := Fact.mk hq
    have hqd : q ∣ p + 1 :=
      (Nat.dvd_factorial hq.pos hqK).trans ((Dvd.intro_left _ rfl).trans hdvd)
    have hpq : (p : ZMod q) = -1 := by
      have : ((p + 1 : ℕ) : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hqd
      push_cast at this; exact eq_neg_of_add_eq_zero_left this
    have hne : (q : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro h; have := Nat.le_of_dvd hq.pos h; omega
    rw [← ZMod.euler_criterion p hne]
    rcases hq.eq_two_or_odd with h2 | hodd
    · subst h2
      exact_mod_cast (ZMod.exists_sq_eq_two_iff (p := p) (by omega)).mpr (Or.inr hp8)
    · have hq2 : q ≠ 2 := by omega
      rcases (show q % 4 = 1 ∨ q % 4 = 3 by omega) with h1 | h3
      · refine (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := q) (q := p) h1 (by omega)).mp ?_
        rw [hpq]; exact ZMod.exists_sq_eq_neg_one_iff.mpr (by omega)
      · refine (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three (p := p) (q := q) hp4 h3
          (by omega)).mpr ?_
        rw [hpq]; intro h; exact (ZMod.exists_sq_eq_neg_one_iff.mp h) h3
  intro i
  induction i using Nat.recOnMul with
  | zero => intro h; omega
  | one => intro _ _; simp
  | prime q hq => intro _ hqK; exact hprime q hq hqK
  | mul a b iha ihb =>
    intro hab habK
    have ha : 0 < a := Nat.pos_of_mul_pos_right hab
    have hb : 0 < b := Nat.pos_of_mul_pos_left hab
    push_cast
    rw [mul_pow, iha ha (le_trans (Nat.le_mul_of_pos_right a hb) habK),
      ihb hb (le_trans (Nat.le_mul_of_pos_left b ha) habK), one_mul]

end OMA770

open Erdos770 in
theorem OMA.solution : type_of% @Erdos770.erdos_770.variants.odd_h_unbounded := by
  intro a
  obtain ⟨p, hp, hpK, hp4, hres⟩ := OMA770.key (a + 2)
  set n := p / 2
  have hodd : Odd n := Nat.odd_iff.mpr (by omega)
  set S : Set ℕ∞ := {m | 2 < m ∧
    ((Finset.Icc 2 m.toNat).image fun i => (i ^ n - 1)).gcd id = 1}
  -- finiteness
  set g := Nat.gcd (2 ^ n - 1) (3 ^ n - 1)
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ (by
    have := Nat.one_lt_two_pow (n := n) (by omega); omega)
  have hmem : ((g + 3 : ℕ) : ℕ∞) ∈ S := by
    refine ⟨by exact_mod_cast (show 2 < g + 3 by omega), ?_⟩
    rw [ENat.toNat_natCast]
    set G := ((Finset.Icc 2 (g + 3)).image fun i => (i ^ n - 1)).gcd id
    have hd : ∀ i, 2 ≤ i → i ≤ g + 3 → G ∣ i ^ n - 1 := fun i h1 h2 =>
      Finset.gcd_dvd (Finset.mem_image_of_mem _ (Finset.mem_Icc.mpr ⟨h1, h2⟩))
    have hGg : G ∣ g := Nat.dvd_gcd (hd 2 le_rfl (by omega)) (hd 3 (by omega) (by omega))
    by_contra hG1
    have hGpos : 0 < G := Nat.pos_of_dvd_of_pos hGg hgpos
    have hGle := Nat.le_of_dvd hgpos hGg
    have h1 : G ∣ G ^ n - 1 := hd G (by omega) (by omega)
    have hpow : 1 ≤ G ^ n := Nat.one_le_pow n G hGpos
    have hsub : G ^ n - (G ^ n - 1) = 1 := by omega
    exact hG1 (Nat.dvd_one.mp (hsub ▸ Nat.dvd_sub (dvd_pow_self G (by omega)) h1))
  have hlow : ∀ x ∈ S, ((a + 3 : ℕ) : ℕ∞) ≤ x := by
    intro x hx
    rcases hx with ⟨h2x, hgcd⟩
    induction x using ENat.recTopCoe with
    | top => exact le_top
    | coe k =>
      rw [ENat.toNat_natCast] at hgcd
      by_contra hk
      have hk' : k ≤ a + 2 := by
        have : ¬ (a + 3 ≤ k) := fun h => hk (by exact_mod_cast h)
        omega
      have : p ∣ ((Finset.Icc 2 k).image fun i => (i ^ n - 1)).gcd id := by
        rw [Finset.dvd_gcd_iff]
        intro b hb
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
        rw [Finset.mem_Icc] at hi
        simp only [id]
        rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ (by omega))]
        push_cast
        rw [hres i (by omega) (by omega)]; simp
      rw [hgcd] at this
      exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  have hge : ((a + 3 : ℕ) : ℕ∞) ≤ h n := le_sInf hlow
  have hne : h n ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top _) (sInf_le hmem)
  refine ⟨(h n).toNat, ⟨h n, ⟨n, hodd, rfl⟩, rfl⟩, ?_⟩
  rw [← ENat.natCast_toNat hne] at hge
  have : a + 3 ≤ (h n).toNat := by exact_mod_cast hge
  omega
