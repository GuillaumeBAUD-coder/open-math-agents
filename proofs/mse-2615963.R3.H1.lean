import OMAReductions.R_mse_2615963_R3
import Mathlib.FieldTheory.Finite.GaloisField

-- Step mse-2615963.R3.H1: hypothesis H1 of reduction mse-2615963.R3
-- Credit: @nisbenz
-- Evaluates ∑_{k < p} C_m(k) mod p for odd primes p via the quadratic extension GaloisField p 2
-- and the two cyclic subgroups G₁ = {t^(p-1) = 1} and G₂ = {t^(p+1) = 1} of (GaloisField p 2)ˣ.

namespace OMA.Mse2615963H1

open Finset Polynomial

lemma chebyshev_C_eval_add_inv {K : Type*} [Field K] (m : ℕ) (t : Kˣ) :
    (Polynomial.Chebyshev.C K (m : ℤ)).eval ((t : K) + (t⁻¹ : Kˣ)) =
      (t : K) ^ m + ((t⁻¹ : Kˣ) : K) ^ m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    match m with
    | 0 =>
      simp [Polynomial.Chebyshev.C_zero]
      ring
    | 1 =>
      simp [Polynomial.Chebyshev.C_one]
    | m + 2 =>
      have hcast : ((m + 2 : ℕ) : ℤ) = (m : ℤ) + 2 := by push_cast; ring
      have hcast1 : ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
      rw [hcast, Polynomial.Chebyshev.C_add_two]
      simp only [eval_sub, eval_mul, eval_X, ← hcast1]
      rw [ih (m + 1) (by omega), ih m (by omega)]
      have hmul : (t : K) * ((t⁻¹ : Kˣ) : K) = 1 := by simp
      have hmul' : ((t⁻¹ : Kˣ) : K) * (t : K) = 1 := by simp
      calc
        ((t : K) + ((t⁻¹ : Kˣ) : K)) * ((t : K) ^ (m + 1) + ((t⁻¹ : Kˣ) : K) ^ (m + 1)) -
            ((t : K) ^ m + ((t⁻¹ : Kˣ) : K) ^ m)
          = (t : K) ^ (m + 2) + ((t⁻¹ : Kˣ) : K) ^ (m + 2) +
              ((t : K) * ((t⁻¹ : Kˣ) : K) - 1) * ((t⁻¹ : Kˣ) : K) ^ m +
              (((t⁻¹ : Kˣ) : K) * (t : K) - 1) * (t : K) ^ m := by ring
        _ = (t : K) ^ (m + 2) + ((t⁻¹ : Kˣ) : K) ^ (m + 2) := by rw [hmul, hmul']; ring

lemma chebyshev_C_map_int {K : Type*} [CommRing K] (m : ℤ) :
    (Polynomial.Chebyshev.C ℤ m).map (Int.castRingHom K) = Polynomial.Chebyshev.C K m := by
  exact Polynomial.Chebyshev.map_C (Int.castRingHom K) m

lemma eval_map_intCast {K : Type*} [CommRing K] (P : ℤ[X]) (x : ℤ) :
    ((P.eval x : ℤ) : K) = (P.map (Int.castRingHom K)).eval (x : K) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.eval_add, Int.cast_add, Polynomial.map_add, hp, hq]
  | monomial n a =>
    simp only [Polynomial.eval_monomial, Int.cast_mul, Int.cast_pow,
      Polynomial.map_monomial, Int.coe_castRingHom]

lemma sum_pow_eq_of_cyclic_subgroup {K : Type*} [Field K] [DecidableEq K]
    (G : Finset Kˣ) (d : ℕ) (hd : 0 < d) (hcard : G.card = d)
    (hpow : ∀ t ∈ G, t ^ d = 1)
    (hmul : ∀ a ∈ G, ∀ b ∈ G, a * b ∈ G)
    (hgen : ∃ g ∈ G, orderOf g = d) (m : ℕ) :
    (∑ t ∈ G, (t : K) ^ m) = if d ∣ m then (d : K) else 0 := by
  by_cases hdm : d ∣ m
  · rw [if_pos hdm]
    obtain ⟨q, rfl⟩ := hdm
    have hone : ∀ t ∈ G, (t : K) ^ (d * q) = 1 := by
      intro t ht
      rw [pow_mul]
      have h1 : (t : K) ^ d = 1 := by rw [← Units.val_pow_eq_pow_val, hpow t ht, Units.val_one]
      rw [h1, one_pow]
    rw [Finset.sum_congr rfl hone, Finset.sum_const, hcard, nsmul_eq_mul, mul_one]
  · rw [if_neg hdm]
    obtain ⟨g, hgG, hgord⟩ := hgen
    have hgm_ne : (g : K) ^ m ≠ 1 := by
      intro heq
      have hgu : g ^ m = 1 := by
        apply Units.ext
        simpa using heq
      have hdvd : orderOf g ∣ m := orderOf_dvd_of_pow_eq_one hgu
      rw [hgord] at hdvd
      exact hdm hdvd
    have hbij : ∑ t ∈ G, (t : K) ^ m = ∑ t ∈ G, ((g * t : Kˣ) : K) ^ m := by
      refine (Finset.sum_bij (fun t _ => g * t) (fun t ht => hmul g hgG t ht)
        (fun a _ b _ h => mul_left_cancel h) ?_ (fun _ _ => rfl)).symm
      intro y hy
      have hinv : g ^ (d - 1) ∈ G := by
        have hpowG : ∀ k : ℕ, 1 ≤ k → g ^ k ∈ G := by
          intro k hk
          induction k with
          | zero => omega
          | succ k ih =>
            rcases k with _ | k
            · simpa using hgG
            · rw [pow_succ]
              exact hmul _ (ih (by omega)) _ hgG
        rcases eq_or_lt_of_le (Nat.succ_le_of_lt hd) with h1 | hgt
        · rw [← h1]
          have hg1 : g = 1 := by
            have := hpow g hgG
            rwa [← h1, pow_one] at this
          simpa [hg1] using hgG
        · exact hpowG (d - 1) (by omega)
      refine ⟨g ^ (d - 1) * y, hmul _ hinv _ hy, ?_⟩
      rw [← mul_assoc, ← pow_succ', show d - 1 + 1 = d by omega, hpow g hgG, one_mul]
    have hmul_eq : (g : K) ^ m * (∑ t ∈ G, (t : K) ^ m) = ∑ t ∈ G, (t : K) ^ m := by
      rw [Finset.mul_sum]
      calc
        ∑ t ∈ G, (g : K) ^ m * (t : K) ^ m
          = ∑ t ∈ G, ((g * t : Kˣ) : K) ^ m := by
              refine Finset.sum_congr rfl fun t _ => ?_
              simp [mul_pow]
        _ = ∑ t ∈ G, (t : K) ^ m := hbij.symm
    have hsub : ((g : K) ^ m - 1) * (∑ t ∈ G, (t : K) ^ m) = 0 := by
      linear_combination hmul_eq
    exact (mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr hgm_ne)

lemma sum_inv_eq_self {K : Type*} [Field K] [DecidableEq K]
    (G : Finset Kˣ) (hinv : ∀ t ∈ G, t⁻¹ ∈ G) (m : ℕ) :
    (∑ t ∈ G, ((t⁻¹ : Kˣ) : K) ^ m) = ∑ t ∈ G, (t : K) ^ m := by
  refine Finset.sum_bij (fun t _ => t⁻¹) (fun t ht => hinv t ht)
    (fun a _ b _ h => inv_injective h) ?_ (fun _ _ => rfl)
  intro y hy
  exact ⟨y⁻¹, hinv y hy, inv_inv y⟩

lemma card_pow_eq_one_of_cyclic {A : Type*} [CommGroup A] [Fintype A] [DecidableEq A]
    [IsCyclic A] {d : ℕ} (hd : 0 < d) (hdvd : d ∣ Fintype.card A) :
    (Finset.univ.filter (fun t : A => t ^ d = 1)).card = d ∧
    ∃ g ∈ Finset.univ.filter (fun t : A => t ^ d = 1), orderOf g = d := by
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := A)
  have hu_ord : orderOf u = Fintype.card A := by
    rw [← Nat.card_eq_fintype_card]
    exact orderOf_eq_card_of_forall_mem_zpowers hu
  obtain ⟨q, hq⟩ := hdvd
  let g : A := u ^ q
  have hg_ord : orderOf g = d := by
    dsimp [g]
    rw [orderOf_pow, hu_ord, hq]
    have hgcd : Nat.gcd (d * q) q = q := Nat.gcd_eq_right (dvd_mul_left q d)
    rw [hgcd]
    have hqpos : 0 < q := by
      have hpos : 0 < Fintype.card A := Fintype.card_pos
      rw [hq] at hpos
      exact Nat.pos_of_mul_pos_left hpos
    exact Nat.mul_div_cancel d hqpos
  have hg_mem : g ∈ Finset.univ.filter (fun t : A => t ^ d = 1) := by
    simp [Finset.mem_filter, ← hg_ord, pow_orderOf_eq_one]
  have hbij : (Finset.range d).image (fun k => g ^ k) =
      Finset.univ.filter (fun t : A => t ^ d = 1) := by
    ext t
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨k, _, rfl⟩
      rw [← pow_mul, mul_comm, pow_mul, ← hg_ord, pow_orderOf_eq_one, one_pow]
    · intro ht
      have ht_mem : t ∈ Subgroup.zpowers u := hu t
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht_mem
      have hj_mod : (u ^ j) ^ d = 1 := ht
      rw [← zpow_natCast, ← zpow_mul] at hj_mod
      have hdiv : (Fintype.card A : ℤ) ∣ j * (d : ℤ) := by
        rw [← hu_ord]
        exact orderOf_dvd_iff_zpow_eq_one.mpr hj_mod
      rw [hq] at hdiv
      push_cast at hdiv
      have hqdvd : (q : ℤ) ∣ j := by
        obtain ⟨c, hc⟩ := hdiv
        refine ⟨c, ?_⟩
        have hd_ne : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
        have : j * (d : ℤ) = (q : ℤ) * c * (d : ℤ) := by linarith
        exact mul_right_cancel₀ hd_ne this
      obtain ⟨r, rfl⟩ := hqdvd
      refine ⟨(r % (d : ℤ)).toNat, ?_, ?_⟩
      · have hdpos : (0 : ℤ) < d := by exact_mod_cast hd
        have h1 : 0 ≤ r % (d : ℤ) := Int.emod_nonneg r hdpos.ne'
        have h2 : r % (d : ℤ) < d := Int.emod_lt_of_pos r hdpos
        omega
      · have hdpos : (0 : ℤ) < d := by exact_mod_cast hd
        have h1 : 0 ≤ r % (d : ℤ) := Int.emod_nonneg r hdpos.ne'
        have hcast : (((r % (d : ℤ)).toNat : ℕ) : ℤ) = r % (d : ℤ) := Int.toNat_of_nonneg h1
        have hgr : u ^ ((q : ℤ) * r) = g ^ r := by
          dsimp [g]
          rw [← zpow_natCast u q, ← zpow_mul]
        rw [hgr, ← zpow_natCast, hcast]
        have hdiv_r : (orderOf g : ℤ) ∣ r - r % (d : ℤ) := by
          rw [hg_ord, Int.dvd_iff_emod_eq_zero, Int.sub_emod, Int.emod_emod, sub_self, Int.zero_emod]
        have hdiff : g ^ (r - r % (d : ℤ)) = 1 := orderOf_dvd_iff_zpow_eq_one.mp hdiv_r
        rw [zpow_sub, mul_inv_eq_one] at hdiff
        exact hdiff.symm
  have hcard : (Finset.univ.filter (fun t : A => t ^ d = 1)).card = d := by
    rw [← hbij, Finset.card_image_of_injOn, Finset.card_range]
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    dsimp only at hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hsub : g ^ (b - a) = 1 := by
        have hmul : g ^ a * g ^ (b - a) = g ^ a * 1 := by
          rw [← pow_add, Nat.add_sub_of_le hlt.le, mul_one, hab]
        exact mul_left_cancel hmul
      have hdvd' : d ∣ b - a := by rw [← hg_ord]; exact orderOf_dvd_of_pow_eq_one hsub
      have hle := Nat.le_of_dvd (by omega) hdvd'
      omega
    · have hsub : g ^ (a - b) = 1 := by
        have hmul : g ^ b * g ^ (a - b) = g ^ b * 1 := by
          rw [← pow_add, Nat.add_sub_of_le hgt.le, mul_one, ← hab]
        exact mul_left_cancel hmul
      have hdvd' : d ∣ a - b := by rw [← hg_ord]; exact orderOf_dvd_of_pow_eq_one hsub
      have hle := Nat.le_of_dvd (by omega) hdvd'
      omega
  exact ⟨hcard, g, hg_mem, hg_ord⟩

theorem h1_proof : OMA.R_mse_2615963_R3.H1 := by
  intro p hp hp2 m
  have : Fact p.Prime := ⟨hp⟩
  classical
  let K := GaloisField p 2
  let _ : Fintype K := Fintype.ofFinite K
  have hKcard : Fintype.card K = p ^ 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card p 2 (by norm_num)
  have hUcard : Fintype.card Kˣ = (p - 1) * (p + 1) := by
    rw [Fintype.card_units, hKcard]
    have hp1 : 1 ≤ p := hp.one_le
    have hp2' : 1 ≤ p ^ 2 := by nlinarith
    zify [hp1, hp2']
    ring
  have hpm1_pos : 0 < p - 1 := by have := hp.two_le; omega
  have hpp1_pos : 0 < p + 1 := by omega
  let G₁ : Finset Kˣ := Finset.univ.filter (fun t : Kˣ => t ^ (p - 1) = 1)
  let G₂ : Finset Kˣ := Finset.univ.filter (fun t : Kˣ => t ^ (p + 1) = 1)
  obtain ⟨hcard₁, hgen₁⟩ :=
    card_pow_eq_one_of_cyclic (A := Kˣ) hpm1_pos (hUcard ▸ dvd_mul_right (p - 1) (p + 1))
  obtain ⟨hcard₂, hgen₂⟩ :=
    card_pow_eq_one_of_cyclic (A := Kˣ) hpp1_pos (hUcard ▸ dvd_mul_left (p + 1) (p - 1))
  let F : Finset K := Finset.univ.image (algebraMap (ZMod p) K)
  have hFcard : F.card = p := by
    rw [Finset.card_image_of_injective _ (RingHom.injective (algebraMap (ZMod p) K)),
      Finset.card_univ, ZMod.card]
  have hF_frob : ∀ y : K, y ∈ F ↔ y ^ p = y := by
    let S : Finset K := Finset.univ.filter (fun y : K => y ^ p = y)
    have hsub : F ⊆ S := by
      intro y hy
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← map_pow, ZMod.pow_card]
    have hScard_le : S.card ≤ p := by
      let P : K[X] := X ^ p - X
      have hPne : P ≠ 0 := by
        intro h0
        have hcoeff := congrArg (fun f : K[X] => f.coeff p) h0
        have hp1 : p ≠ 1 := hp.ne_one
        simp [P, Polynomial.coeff_X, hp1.symm] at hcoeff
      have hPdeg : P.natDegree ≤ p := by
        refine (Polynomial.natDegree_sub_le _ _).trans ?_
        simp only [Polynomial.natDegree_X_pow, Polynomial.natDegree_X]
        exact max_le le_rfl hp.one_le
      have hSsub : S.val ⊆ P.roots := by
        intro y hy
        have hy' : y ^ p = y := (Finset.mem_filter.mp hy).2
        rw [Polynomial.mem_roots hPne, Polynomial.IsRoot.def]
        simp [P, hy']
      have hle1 : S.card ≤ P.roots.card :=
        Multiset.card_le_card ((Multiset.le_iff_subset S.nodup).mpr hSsub)
      exact hle1.trans ((Polynomial.card_roots' P).trans hPdeg)
    have hFS : F = S := Finset.eq_of_subset_of_card_le hsub (hFcard ▸ hScard_le)
    intro y
    rw [hFS]
    simp [S]
  let φ : Kˣ → K := fun t => (t : K) + ((t⁻¹ : Kˣ) : K)
  have hφ_G₁ : ∀ t ∈ G₁, φ t ∈ F := by
    intro t ht
    have h1 : t ^ (p - 1) = 1 := (Finset.mem_filter.mp ht).2
    have htu : t ^ p = t := by
      calc t ^ p = t ^ (p - 1 + 1) := congrArg (t ^ ·) (by omega)
        _ = t ^ (p - 1) * t := pow_succ t (p - 1)
        _ = t := by rw [h1, one_mul]
    have htp : (t : K) ^ p = (t : K) := by
      exact_mod_cast congrArg Units.val htu
    have htip : ((t⁻¹ : Kˣ) : K) ^ p = ((t⁻¹ : Kˣ) : K) := by
      have h2 : (t⁻¹) ^ p = t⁻¹ := by rw [inv_pow, htu]
      exact_mod_cast congrArg Units.val h2
    rw [hF_frob]
    dsimp [φ]
    rw [add_pow_char, htp, htip]
  have hφ_G₂ : ∀ t ∈ G₂, φ t ∈ F := by
    intro t ht
    have htp : (t : K) ^ p = ((t⁻¹ : Kˣ) : K) := by
      have h1 : t ^ (p + 1) = 1 := (Finset.mem_filter.mp ht).2
      have h2 : t ^ p = t⁻¹ := by
        apply eq_inv_of_mul_eq_one_left
        rw [← pow_succ, h1]
      exact_mod_cast congrArg Units.val h2
    have htip : ((t⁻¹ : Kˣ) : K) ^ p = (t : K) := by
      have h1 : t ^ (p + 1) = 1 := (Finset.mem_filter.mp ht).2
      have h2 : (t⁻¹) ^ p = t := by
        rw [inv_pow]
        apply inv_eq_of_mul_eq_one_right
        rw [← pow_succ, h1]
      exact_mod_cast congrArg Units.val h2
    rw [hF_frob]
    dsimp [φ]
    rw [add_pow_char, htp, htip, add_comm]
  have hfib_le : ∀ x ∈ F,
      (G₁.filter (fun t => φ t = x)).card + (G₂.filter (fun t => φ t = x)).card ≤ 2 := by
    intro x _
    let F₁ := G₁.filter (fun t => φ t = x)
    let F₂ := G₂.filter (fun t => φ t = x)
    have hpair : ∀ t₁ ∈ F₁ ∪ F₂, ∀ t₂ ∈ F₁ ∪ F₂, t₂ = t₁ ∨ t₂ = t₁⁻¹ := by
      intro t₁ ht₁ t₂ ht₂
      have h1 : φ t₁ = x := by
        rcases Finset.mem_union.mp ht₁ with h | h <;> exact (Finset.mem_filter.mp h).2
      have h2 : φ t₂ = x := by
        rcases Finset.mem_union.mp ht₂ with h | h <;> exact (Finset.mem_filter.mp h).2
      have heq : (t₂ : K) + ((t₂⁻¹ : Kˣ) : K) = (t₁ : K) + ((t₁⁻¹ : Kˣ) : K) := h2.trans h1.symm
      have hprod : ((t₂ : K) - (t₁ : K)) * ((t₂ : K) * (t₁ : K) - 1) = 0 := by
        have hm1 : (t₁ : K) * ((t₁⁻¹ : Kˣ) : K) = 1 := by simp
        have hm2 : (t₂ : K) * ((t₂⁻¹ : Kˣ) : K) = 1 := by simp
        have : (t₁ : K) * (t₂ : K) * ((t₂ : K) + ((t₂⁻¹ : Kˣ) : K) -
            ((t₁ : K) + ((t₁⁻¹ : Kˣ) : K))) =
            ((t₂ : K) - (t₁ : K)) * ((t₂ : K) * (t₁ : K) - 1) := by
          calc
            (t₁ : K) * (t₂ : K) * ((t₂ : K) + ((t₂⁻¹ : Kˣ) : K) -
                ((t₁ : K) + ((t₁⁻¹ : Kˣ) : K)))
              = (t₁ : K) * (t₂ : K) ^ 2 + (t₁ : K) * ((t₂ : K) * ((t₂⁻¹ : Kˣ) : K)) -
                  (t₂ : K) * (t₁ : K) ^ 2 - (t₂ : K) * ((t₁ : K) * ((t₁⁻¹ : Kˣ) : K)) := by ring
            _ = (t₁ : K) * (t₂ : K) ^ 2 + (t₁ : K) * 1 -
                  (t₂ : K) * (t₁ : K) ^ 2 - (t₂ : K) * 1 := by rw [hm1, hm2]
            _ = ((t₂ : K) - (t₁ : K)) * ((t₂ : K) * (t₁ : K) - 1) := by ring
        rw [← this, sub_eq_zero.mpr heq, mul_zero]
      rcases mul_eq_zero.mp hprod with h | h
      · left; exact Units.ext (sub_eq_zero.mp h)
      · right
        apply Units.ext
        have : (t₂ : K) * (t₁ : K) = 1 := sub_eq_zero.mp h
        rw [Units.val_inv_eq_inv_val]
        exact eq_inv_of_mul_eq_one_left this
    by_cases hne : (F₁ ∩ F₂).Nonempty
    · obtain ⟨t₀, ht₀⟩ := hne
      have ht0_1 : t₀ ∈ G₁ := (Finset.mem_filter.mp (Finset.mem_inter.mp ht₀).1).1
      have ht0_2 : t₀ ∈ G₂ := (Finset.mem_filter.mp (Finset.mem_inter.mp ht₀).2).1
      have h1 : t₀ ^ (p - 1) = 1 := (Finset.mem_filter.mp ht0_1).2
      have h2 : t₀ ^ (p + 1) = 1 := (Finset.mem_filter.mp ht0_2).2
      have hsq : t₀ ^ 2 = 1 := by
        have hmul : t₀ ^ (p - 1) * t₀ ^ 2 = t₀ ^ (p + 1) := by
          rw [← pow_add, show p - 1 + 2 = p + 1 by omega]
        rw [h1, one_mul, h2] at hmul
        exact hmul
      have hinv_eq : t₀⁻¹ = t₀ := by
        apply inv_eq_of_mul_eq_one_right
        simpa [sq] using hsq
      have hsub : F₁ ∪ F₂ ⊆ {t₀} := by
        intro t ht
        have ht0_u : t₀ ∈ F₁ ∪ F₂ := Finset.mem_union_left _ (Finset.mem_inter.mp ht₀).1
        rcases hpair t₀ ht0_u t ht with rfl | rfl
        · simp
        · simp [hinv_eq]
      have hle1 : F₁.card ≤ 1 :=
        (Finset.card_le_card (Finset.subset_union_left.trans hsub)).trans (by simp)
      have hle2 : F₂.card ≤ 1 :=
        (Finset.card_le_card (Finset.subset_union_right.trans hsub)).trans (by simp)
      exact Nat.add_le_add hle1 hle2
    · have hdisj : Disjoint F₁ F₂ := Finset.disjoint_iff_inter_eq_empty.mpr
        (Finset.not_nonempty_iff_eq_empty.mp hne)
      rw [← Finset.card_union_of_disjoint hdisj]
      by_cases hu : (F₁ ∪ F₂).Nonempty
      · obtain ⟨t₀, ht₀⟩ := hu
        have hsub : F₁ ∪ F₂ ⊆ {t₀, t₀⁻¹} := by
          intro t ht
          rcases hpair t₀ ht₀ t ht with rfl | rfl <;> simp
        exact (Finset.card_le_card hsub).trans (Finset.card_le_two)
      · simp [Finset.not_nonempty_iff_eq_empty.mp hu]
  have hsum_fib :
      ∑ x ∈ F, ((G₁.filter (fun t => φ t = x)).card + (G₂.filter (fun t => φ t = x)).card) =
      ∑ _x ∈ F, 2 := by
    rw [Finset.sum_add_distrib]
    have h1 : ∑ x ∈ F, (G₁.filter (fun t => φ t = x)).card = G₁.card := by
      rw [← Finset.card_biUnion]
      · congr 1
        ext t
        simp only [Finset.mem_biUnion, Finset.mem_filter]
        exact ⟨fun ⟨_, _, ht, _⟩ => ht, fun ht => ⟨φ t, hφ_G₁ t ht, ht, rfl⟩⟩
      · intro x _ y _ hxy
        rw [Function.onFun, Finset.disjoint_left]
        intro t ht1 ht2
        exact hxy ((Finset.mem_filter.mp ht1).2.symm.trans (Finset.mem_filter.mp ht2).2)
    have h2 : ∑ x ∈ F, (G₂.filter (fun t => φ t = x)).card = G₂.card := by
      rw [← Finset.card_biUnion]
      · congr 1
        ext t
        simp only [Finset.mem_biUnion, Finset.mem_filter]
        exact ⟨fun ⟨_, _, ht, _⟩ => ht, fun ht => ⟨φ t, hφ_G₂ t ht, ht, rfl⟩⟩
      · intro x _ y _ hxy
        rw [Function.onFun, Finset.disjoint_left]
        intro t ht1 ht2
        exact hxy ((Finset.mem_filter.mp ht1).2.symm.trans (Finset.mem_filter.mp ht2).2)
    rw [h1, h2, hcard₁, hcard₂, Finset.sum_const, hFcard, smul_eq_mul]
    omega
  have hfib_eq : ∀ x ∈ F,
      (G₁.filter (fun t => φ t = x)).card + (G₂.filter (fun t => φ t = x)).card = 2 := by
    intro x hx
    exact (Finset.sum_eq_sum_iff_of_le hfib_le).mp hsum_fib x hx
  have hmain_K : (2 : K) * (∑ x ∈ F, (Polynomial.Chebyshev.C K (m : ℤ)).eval x) =
      (2 : K) * ((∑ t ∈ G₁, (t : K) ^ m) + (∑ t ∈ G₂, (t : K) ^ m)) := by
    have hlhs : (2 : K) * (∑ x ∈ F, (Polynomial.Chebyshev.C K (m : ℤ)).eval x) =
        (∑ t ∈ G₁, (Polynomial.Chebyshev.C K (m : ℤ)).eval (φ t)) +
        (∑ t ∈ G₂, (Polynomial.Chebyshev.C K (m : ℤ)).eval (φ t)) := by
      have hf1 : ∑ t ∈ G₁, (Polynomial.Chebyshev.C K (m : ℤ)).eval (φ t) =
          ∑ x ∈ F, ((G₁.filter (fun t => φ t = x)).card : K) *
            (Polynomial.Chebyshev.C K (m : ℤ)).eval x := by
        rw [← Finset.sum_fiberwise_of_maps_to hφ_G₁]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_congr rfl (fun t ht => by rw [(Finset.mem_filter.mp ht).2]),
          Finset.sum_const, nsmul_eq_mul]
      have hf2 : ∑ t ∈ G₂, (Polynomial.Chebyshev.C K (m : ℤ)).eval (φ t) =
          ∑ x ∈ F, ((G₂.filter (fun t => φ t = x)).card : K) *
            (Polynomial.Chebyshev.C K (m : ℤ)).eval x := by
        rw [← Finset.sum_fiberwise_of_maps_to hφ_G₂]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_congr rfl (fun t ht => by rw [(Finset.mem_filter.mp ht).2]),
          Finset.sum_const, nsmul_eq_mul]
      rw [hf1, hf2, ← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [← add_mul, ← Nat.cast_add, hfib_eq x hx]
      simp
    rw [hlhs]
    have hG1_inv : ∀ t ∈ G₁, t⁻¹ ∈ G₁ := by
      intro t ht
      simp only [G₁, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      rw [inv_pow, ht, inv_one]
    have hG2_inv : ∀ t ∈ G₂, t⁻¹ ∈ G₂ := by
      intro t ht
      simp only [G₂, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      rw [inv_pow, ht, inv_one]
    have hs1 : ∑ t ∈ G₁, (Polynomial.Chebyshev.C K (m : ℤ)).eval (φ t) =
        (2 : K) * (∑ t ∈ G₁, (t : K) ^ m) := by
      simp_rw [φ, chebyshev_C_eval_add_inv, Finset.sum_add_distrib, sum_inv_eq_self G₁ hG1_inv]
      ring
    have hs2 : ∑ t ∈ G₂, (Polynomial.Chebyshev.C K (m : ℤ)).eval (φ t) =
        (2 : K) * (∑ t ∈ G₂, (t : K) ^ m) := by
      simp_rw [φ, chebyshev_C_eval_add_inv, Finset.sum_add_distrib, sum_inv_eq_self G₂ hG2_inv]
      ring
    rw [hs1, hs2, mul_add]
  have h2ne : (2 : K) ≠ 0 := by
    intro h2z
    have h2z' : (algebraMap (ZMod p) K) (2 : ZMod p) = (algebraMap (ZMod p) K) 0 := by
      rw [map_ofNat, map_zero]
      exact h2z
    have h2mod : (2 : ZMod p) = 0 := RingHom.injective (algebraMap (ZMod p) K) h2z'
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h2mod)
    have hle := Nat.le_of_dvd (by decide) hdvd
    have := hp.two_le
    omega
  have hsum_K : ∑ x ∈ F, (Polynomial.Chebyshev.C K (m : ℤ)).eval x =
      (∑ t ∈ G₁, (t : K) ^ m) + (∑ t ∈ G₂, (t : K) ^ m) :=
    mul_left_cancel₀ h2ne hmain_K
  have hG1_mul : ∀ a ∈ G₁, ∀ b ∈ G₁, a * b ∈ G₁ := by
    intro a ha b hb
    simp only [G₁, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb ⊢
    rw [mul_pow, ha, hb, one_mul]
  have hG2_mul : ∀ a ∈ G₂, ∀ b ∈ G₂, a * b ∈ G₂ := by
    intro a ha b hb
    simp only [G₂, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb ⊢
    rw [mul_pow, ha, hb, one_mul]
  have hS1 := sum_pow_eq_of_cyclic_subgroup G₁ (p - 1) hpm1_pos hcard₁
    (fun t ht => (Finset.mem_filter.mp ht).2) hG1_mul hgen₁ m
  have hS2 := sum_pow_eq_of_cyclic_subgroup G₂ (p + 1) hpp1_pos hcard₂
    (fun t ht => (Finset.mem_filter.mp ht).2) hG2_mul hgen₂ m
  rw [hS1, hS2] at hsum_K
  have hp0 : (p : K) = 0 := by
    have h : (algebraMap (ZMod p) K) (p : ZMod p) = 0 := by simp
    rw [map_natCast] at h
    exact h
  have hpm1_K : ((p - 1 : ℕ) : K) = -1 := by
    have h : ((p - 1 : ℕ) : K) + ((1 : ℕ) : K) = (p : K) := by
      rw [← Nat.cast_add, show p - 1 + 1 = p by omega]
    rw [Nat.cast_one, hp0] at h
    linear_combination h
  have hpp1_K : ((p + 1 : ℕ) : K) = 1 := by
    rw [Nat.cast_add, Nat.cast_one, hp0, zero_add]
  rw [hpm1_K, hpp1_K] at hsum_K
  have hLHS_K : ((∑ k ∈ Finset.range p, (Polynomial.Chebyshev.C ℤ (m : ℤ)).eval (k : ℤ) : ℤ) : K) =
      ∑ x ∈ F, (Polynomial.Chebyshev.C K (m : ℤ)).eval x := by
    rw [Int.cast_sum]
    have hrange : (∑ k ∈ Finset.range p,
        (((Polynomial.Chebyshev.C ℤ (m : ℤ)).eval (k : ℤ) : ℤ) : K)) =
        ∑ x : ZMod p, (Polynomial.Chebyshev.C K (m : ℤ)).eval (algebraMap (ZMod p) K x) := by
      refine Finset.sum_bij (fun k _ => (k : ZMod p)) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
      · intro a ha b hb hab
        have ha' : a < p := Finset.mem_range.mp ha
        have hb' : b < p := Finset.mem_range.mp hb
        have hmod : a ≡ b [MOD p] := (ZMod.natCast_eq_natCast_iff a b p).mp hab
        rw [Nat.ModEq, Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at hmod
        exact hmod
      · intro x _
        exact ⟨x.val, Finset.mem_range.mpr (ZMod.val_lt x), ZMod.natCast_zmod_val x⟩
      · intro k _
        rw [eval_map_intCast, chebyshev_C_map_int]
        congr 1
        simp
    rw [hrange]
    dsimp [F]
    rw [Finset.sum_image]
    intro a _ b _ hab
    exact RingHom.injective (algebraMap (ZMod p) K) hab
  have hRHS_K : ((((if (p - 1) ∣ m then (-1 : ℤ) else 0) +
      (if (p + 1) ∣ m then (1 : ℤ) else 0)) : ℤ) : K) =
      (if (p - 1) ∣ m then (-1 : K) else 0) + (if (p + 1) ∣ m then (1 : K) else 0) := by
    split_ifs <;> simp
  rw [← ZMod.intCast_eq_intCast_iff]
  apply RingHom.injective (algebraMap (ZMod p) K)
  rw [map_intCast, map_intCast, hLHS_K, hRHS_K]
  exact hsum_K

end OMA.Mse2615963H1

theorem OMA.solution : OMA.R_mse_2615963_R3.H1 := OMA.Mse2615963H1.h1_proof
