import OMAStatements.S_oeis_a123164

-- Problem: A123164: a supercongruence for the coefficient of x^n in ((1+x)/(1-x))^n.
-- Upstream: statements/oeis-a123164.lean (declaration OMA.S_oeis_a123164.main)
-- Credit: Daniel Whorlow (@draonbioetl)
-- Proof of Peter Bala's Oct 07 2021 supercongruence conjecture (OEIS A123164):
--   For a(n) = Sum_{k=0..n} C(n,k) * C(n+k-1,k), prime p >= 5, n >= 1, r >= 1:
--     a(n * p^r) ≡ a(n * p^(r-1)) (mod p^(3*r))

namespace OMA_A123164

open Finset

/-! ### Part 1: Elementary ZMod, unit-sum, Jacobsthal/Kazandzidis, and p-adic valuation lemmas -/

private lemma succ_mul_choose_eq (n k : ℕ) :
    (n + 1) * Nat.choose n k = (k + 1) * Nat.choose (n + 1) (k + 1) := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => simp
    | succ k => simp [Nat.choose_eq_zero_of_lt (show 1 < k + 2 by omega)]
  | succ n ih =>
    cases k with
    | zero => simp [Nat.choose_one_right]
    | succ k =>
      have h1 := ih k
      have h2 := ih (k + 1)
      have hpas1 : Nat.choose (n + 1) (k + 1) = Nat.choose n k + Nat.choose n (k + 1) :=
        Nat.choose_succ_succ n k
      have hpas2 : Nat.choose (n + 1 + 1) (k + 1 + 1) =
          Nat.choose (n + 1) (k + 1) + Nat.choose (n + 1) (k + 1 + 1) :=
        Nat.choose_succ_succ (n + 1) (k + 1)
      calc (n + 1 + 1) * Nat.choose (n + 1) (k + 1)
          = (n + 1) * Nat.choose n k + (n + 1) * Nat.choose n (k + 1) +
            Nat.choose (n + 1) (k + 1) := by rw [hpas1]; ring
        _ = (k + 1) * Nat.choose (n + 1) (k + 1) +
            (k + 1 + 1) * Nat.choose (n + 1) (k + 1 + 1) +
            Nat.choose (n + 1) (k + 1) := by rw [h1, h2]
        _ = (k + 1 + 1) * Nat.choose (n + 1 + 1) (k + 1 + 1) := by rw [hpas2]; ring

private lemma coprime_prod_right {α : Type*} (s : Finset α) (n : ℕ) (f : α → ℕ)
    (h : ∀ x ∈ s, Nat.Coprime n (f x)) : Nat.Coprime n (∏ x ∈ s, f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul_right
      (ih fun x hx => h x (Finset.mem_insert_of_mem hx))

private lemma int_dvd_of_coprime_mul {p s : ℕ} {a b : ℤ} (hp : p.Prime)
    (ha : ¬ (p : ℤ) ∣ a) (hd : ((p ^ s : ℕ) : ℤ) ∣ a * b) :
    ((p ^ s : ℕ) : ℤ) ∣ b := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hd ⊢
  rw [Int.cast_mul] at hd
  have hua : IsUnit (a : ZMod (p ^ s)) := by
    have hcop : Nat.Coprime a.natAbs (p ^ s) := by
      refine (Nat.Coprime.pow_right s ?_)
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
      intro hdiv
      apply ha
      have h1 : ((p : ℕ) : ℤ) ∣ (a.natAbs : ℤ) := Int.natCast_dvd_natCast.mpr hdiv
      exact Int.dvd_natAbs.mp h1
    rcases Int.natAbs_eq a with hpos | hneg
    · have hc : (a : ZMod (p ^ s)) = (a.natAbs : ZMod (p ^ s)) := by
        conv_lhs => rw [hpos]
        simp
      rw [hc, ZMod.isUnit_iff_coprime]
      exact hcop
    · have hc : (a : ZMod (p ^ s)) = -(a.natAbs : ZMod (p ^ s)) := by
        conv_lhs => rw [hneg]
        simp
      rw [hc]
      exact ((ZMod.isUnit_iff_coprime _ _).mpr hcop).neg
  exact hua.mul_left_cancel (by rw [hd, mul_zero])

private lemma coprime_of_not_dvd_prime {p u : ℕ} (hp : p.Prime) (hu : ¬ p ∣ u) :
    Nat.Coprime u p :=
  (hp.coprime_iff_not_dvd.mpr hu).symm

private lemma isUnit_zmod_pow {p s u : ℕ} (hp : p.Prime) (hu : ¬ p ∣ u) :
    IsUnit (u : ZMod (p ^ s)) := by
  rw [ZMod.isUnit_iff_coprime]
  exact (coprime_of_not_dvd_prime hp hu).pow_right s

private lemma zmod_pow_mul_inv {p s u : ℕ} (hp : p.Prime) (hu : ¬ p ∣ u) :
    (u : ZMod (p ^ s)) * (u : ZMod (p ^ s))⁻¹ = 1 :=
  ZMod.mul_inv_of_unit _ (isUnit_zmod_pow hp hu)

private lemma isUnit_prod_of_mem {R : Type*} [CommMonoid R] {α : Type*}
    (s : Finset α) (f : α → R) (h : ∀ x ∈ s, IsUnit (f x)) :
    IsUnit (∏ x ∈ s, f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul
      (ih fun x hx => h x (Finset.mem_insert_of_mem hx))

private lemma sum_inv_sq_units {p s : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hs : 1 ≤ s) :
    ∑ u ∈ (Finset.range (p ^ s)).filter (fun u => ¬ p ∣ u),
      ((u : ZMod (p ^ s))⁻¹) ^ 2 = 0 := by
  set N := p ^ s
  set S := (Finset.range N).filter (fun u => ¬ p ∣ u)
  have hNpos : 0 < N := pow_pos hp.pos s
  have h2nd : ¬ p ∣ 2 := fun h => by have := Nat.le_of_dvd (by decide) h; omega
  have h3nd : ¬ p ∣ 3 := fun h => by have := Nat.le_of_dvd (by decide) h; omega
  have h2u : IsUnit (2 : ZMod N) := by
    change IsUnit ((2 : ℕ) : ZMod N); exact isUnit_zmod_pow hp h2nd
  have h3u : IsUnit (3 : ZMod N) := by
    change IsUnit ((3 : ℕ) : ZMod N); exact isUnit_zmod_pow hp h3nd
  have hbij : ∑ u ∈ S, (((2 * u % N : ℕ) : ZMod N)⁻¹) ^ 2 = ∑ u ∈ S, ((u : ZMod N)⁻¹) ^ 2 := by
    refine Finset.sum_bij (fun u _ => 2 * u % N) ?_ ?_ ?_ ?_
    · intro u hu
      simp only [S, Finset.mem_filter, Finset.mem_range] at hu ⊢
      refine ⟨Nat.mod_lt _ hNpos, ?_⟩
      intro hd
      have hpN : p ∣ N := dvd_pow_self p (by omega)
      have h2u_dvd : p ∣ 2 * u := by
        have hmod := Nat.div_add_mod (2 * u) N
        have : p ∣ N * (2 * u / N) + 2 * u % N := dvd_add (dvd_mul_of_dvd_left hpN _) hd
        rwa [hmod] at this
      rcases hp.dvd_mul.mp h2u_dvd with h2 | hu'
      · exact h2nd h2
      · exact hu.2 hu'
    · intro u1 hu1 u2 hu2 heq
      simp only [S, Finset.mem_filter, Finset.mem_range] at hu1 hu2
      have hcast : ((2 * u1 % N : ℕ) : ZMod N) = ((2 * u2 % N : ℕ) : ZMod N) := by rw [heq]
      simp only [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_ofNat] at hcast
      have hcancel := h2u.mul_left_cancel hcast
      have hval := congrArg ZMod.val hcancel
      rwa [ZMod.val_natCast_of_lt hu1.1, ZMod.val_natCast_of_lt hu2.1] at hval
    · intro v hv
      simp only [S, Finset.mem_filter, Finset.mem_range] at hv
      have : NeZero N := ⟨Nat.ne_of_gt hNpos⟩
      set u := ((2 : ZMod N)⁻¹ * (v : ZMod N)).val
      have hu_lt : u < N := ZMod.val_lt _
      have hu_cast : (u : ZMod N) = (2 : ZMod N)⁻¹ * (v : ZMod N) := ZMod.natCast_zmod_val _
      have h2u_eq : ((2 * u % N : ℕ) : ZMod N) = (v : ZMod N) := by
        rw [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_ofNat, hu_cast, ← mul_assoc,
          ZMod.mul_inv_of_unit _ h2u, one_mul]
      have h2u_nat : 2 * u % N = v := by
        have hval := congrArg ZMod.val h2u_eq
        rwa [ZMod.val_natCast_of_lt (Nat.mod_lt _ hNpos), ZMod.val_natCast_of_lt hv.1] at hval
      refine ⟨u, ?_, h2u_nat⟩
      simp only [S, Finset.mem_filter, Finset.mem_range]
      refine ⟨hu_lt, fun hdu => hv.2 ?_⟩
      have hpN : p ∣ N := dvd_pow_self p (by omega)
      have hmod := Nat.div_add_mod (2 * u) N
      have h1 : p ∣ 2 * u := dvd_mul_of_dvd_right hdu 2
      rw [← h2u_nat]
      exact (Nat.dvd_add_right (dvd_mul_of_dvd_left hpN _)).mp (hmod.symm ▸ h1)
    · intro _ _; rfl
  have h4 : ∑ u ∈ S, (((2 * u % N : ℕ) : ZMod N)⁻¹) ^ 2 =
      ((2 : ZMod N)⁻¹ ^ 2) * ∑ u ∈ S, ((u : ZMod N)⁻¹) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_ofNat]
    have hu_u : IsUnit (u : ZMod N) := isUnit_zmod_pow hp (Finset.mem_filter.mp hu).2
    have hmul_inv : ((2 : ZMod N) * (u : ZMod N))⁻¹ = (2 : ZMod N)⁻¹ * (u : ZMod N)⁻¹ := by
      have h1 : ((2 : ZMod N) * (u : ZMod N)) * ((2 : ZMod N)⁻¹ * (u : ZMod N)⁻¹) = 1 := by
        calc ((2 : ZMod N) * (u : ZMod N)) * ((2 : ZMod N)⁻¹ * (u : ZMod N)⁻¹)
            = ((2 : ZMod N) * (2 : ZMod N)⁻¹) * ((u : ZMod N) * (u : ZMod N)⁻¹) := by ring
          _ = 1 := by rw [ZMod.mul_inv_of_unit _ h2u, ZMod.mul_inv_of_unit _ hu_u, mul_one]
      exact (h2u.mul hu_u).mul_left_cancel (by rw [ZMod.mul_inv_of_unit _ (h2u.mul hu_u), h1])
    rw [hmul_inv, mul_pow]
  rw [h4] at hbij
  have h4_eq : (4 : ZMod N) * (∑ u ∈ S, ((u : ZMod N)⁻¹) ^ 2) =
      ∑ u ∈ S, ((u : ZMod N)⁻¹) ^ 2 := by
    have h2sq : (4 : ZMod N) * ((2 : ZMod N)⁻¹ ^ 2) = 1 := by
      calc (4 : ZMod N) * ((2 : ZMod N)⁻¹ ^ 2)
          = ((2 : ZMod N) * (2 : ZMod N)⁻¹) ^ 2 := by ring
        _ = 1 := by rw [ZMod.mul_inv_of_unit _ h2u, one_pow]
    calc (4 : ZMod N) * (∑ u ∈ S, ((u : ZMod N)⁻¹) ^ 2)
        = (4 : ZMod N) * (((2 : ZMod N)⁻¹ ^ 2) * (∑ u ∈ S, ((u : ZMod N)⁻¹) ^ 2)) := by rw [hbij]
      _ = ((4 : ZMod N) * ((2 : ZMod N)⁻¹ ^ 2)) * (∑ u ∈ S, ((u : ZMod N)⁻¹) ^ 2) := by ring
      _ = ∑ u ∈ S, ((u : ZMod N)⁻¹) ^ 2 := by rw [h2sq, one_mul]
  have h3_eq : (3 : ZMod N) * (∑ u ∈ S, ((u : ZMod N)⁻¹) ^ 2) = 0 := by
    linear_combination h4_eq
  exact h3u.mul_left_cancel (by rw [h3_eq, mul_zero])

private lemma sum_inv_sq_mul_block {p s c : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hs : 1 ≤ s) :
    ∑ u ∈ (Finset.range (c * p ^ s)).filter (fun u => ¬ p ∣ u),
      ((u : ZMod (p ^ s))⁻¹) ^ 2 = 0 := by
  induction c with
  | zero => simp
  | succ c ih =>
    have hsplit : (Finset.range ((c + 1) * p ^ s)).filter (fun u => ¬ p ∣ u) =
        (Finset.range (c * p ^ s)).filter (fun u => ¬ p ∣ u) ∪
        ((Finset.range (p ^ s)).filter (fun u => ¬ p ∣ u)).image (fun u => c * p ^ s + u) := by
      ext x
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨hx, hnd⟩
        by_cases hlt : x < c * p ^ s
        · exact Or.inl ⟨hlt, hnd⟩
        · right
          have hlt2 : x - c * p ^ s < p ^ s := by rw [add_mul, one_mul] at hx; omega
          refine ⟨x - c * p ^ s, ⟨hlt2, ?_⟩, by omega⟩
          intro hd
          apply hnd
          have hpN : p ∣ c * p ^ s := dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) c
          have := dvd_add hpN hd
          rwa [show c * p ^ s + (x - c * p ^ s) = x by omega] at this
      · rintro (⟨hlt, hnd⟩ | ⟨u, ⟨hu, hnd⟩, rfl⟩)
        · exact ⟨by nlinarith, hnd⟩
        · refine ⟨by nlinarith, fun hd => hnd ?_⟩
          have hpN : p ∣ c * p ^ s := dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) c
          exact (Nat.dvd_add_right hpN).mp hd
    have hdisj : Disjoint
        ((Finset.range (c * p ^ s)).filter (fun u => ¬ p ∣ u))
        (((Finset.range (p ^ s)).filter (fun u => ¬ p ∣ u)).image (fun u => c * p ^ s + u)) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image] at hx1 hx2
      rcases hx2 with ⟨u, _, rfl⟩; omega
    rw [hsplit, Finset.sum_union hdisj, ih, zero_add,
      Finset.sum_image (fun _ _ _ _ h => Nat.add_left_cancel h)]
    have hcongr : ∑ u ∈ (Finset.range (p ^ s)).filter (fun u => ¬ p ∣ u),
        (((c * p ^ s + u : ℕ) : ZMod (p ^ s))⁻¹) ^ 2 =
        ∑ u ∈ (Finset.range (p ^ s)).filter (fun u => ¬ p ∣ u), ((u : ZMod (p ^ s))⁻¹) ^ 2 := by
      refine Finset.sum_congr rfl fun u _ => ?_
      simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add]
    rw [hcongr]
    exact sum_inv_sq_units hp h5 hs

private lemma sum_inv_pair_block {p t B : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (ht : 1 ≤ t)
    (hB : p ^ t ∣ B) :
    ∑ u ∈ (Finset.range B).filter (fun u => ¬ p ∣ u),
      ((u : ZMod (p ^ t)) * ((B - u : ℕ) : ZMod (p ^ t)))⁻¹ = 0 := by
  rcases hB with ⟨c, rfl⟩
  rw [mul_comm]
  have hcongr : ∑ u ∈ (Finset.range (c * p ^ t)).filter (fun u => ¬ p ∣ u),
      ((u : ZMod (p ^ t)) * ((c * p ^ t - u : ℕ) : ZMod (p ^ t)))⁻¹ =
      - ∑ u ∈ (Finset.range (c * p ^ t)).filter (fun u => ¬ p ∣ u),
        ((u : ZMod (p ^ t))⁻¹) ^ 2 := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun u hu => ?_
    simp only [Finset.mem_filter, Finset.mem_range] at hu
    have hcast : ((c * p ^ t - u : ℕ) : ZMod (p ^ t)) = -(u : ZMod (p ^ t)) := by
      rw [Nat.cast_sub (by omega), Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_sub]
    rw [hcast, mul_neg, ← sq]
    have huu : IsUnit ((u : ZMod (p ^ t)) ^ 2) := (isUnit_zmod_pow hp hu.2).pow 2
    have hneg_inv : (-((u : ZMod (p ^ t)) ^ 2))⁻¹ = -((u : ZMod (p ^ t))⁻¹ ^ 2) := by
      have h1 : (-((u : ZMod (p ^ t)) ^ 2)) * (-((u : ZMod (p ^ t))⁻¹ ^ 2)) = 1 := by
        calc (-((u : ZMod (p ^ t)) ^ 2)) * (-((u : ZMod (p ^ t))⁻¹ ^ 2))
            = ((u : ZMod (p ^ t)) * (u : ZMod (p ^ t))⁻¹) ^ 2 := by ring
          _ = 1 := by rw [zmod_pow_mul_inv hp hu.2, one_pow]
      exact huu.neg.mul_left_cancel (by rw [ZMod.mul_inv_of_unit _ huu.neg, h1])
    exact hneg_inv
  rw [hcongr, sum_inv_sq_mul_block hp h5 ht, neg_zero]

private lemma prod_Icc_split_dvd (p m : ℕ) (hp : 1 ≤ p) (f : ℕ → ℕ) :
    ∏ u ∈ Finset.Icc 1 (p * m), f u =
      (∏ j ∈ Finset.Icc 1 m, f (p * j)) *
        (∏ u ∈ (Finset.range (p * m)).filter (fun u => ¬ p ∣ u), f u) := by
  have hpart : Finset.Icc 1 (p * m) =
      (Finset.Icc 1 m).image (fun j => p * j) ∪
      (Finset.range (p * m)).filter (fun u => ¬ p ∣ u) := by
    ext u
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
      Finset.mem_range]
    constructor
    · rintro ⟨hu1, hum⟩
      by_cases hd : p ∣ u
      · left
        rcases hd with ⟨j, rfl⟩
        exact ⟨j, ⟨by nlinarith, by nlinarith⟩, rfl⟩
      · right
        refine ⟨?_, hd⟩
        have hne : u ≠ p * m := fun h => hd (h ▸ dvd_mul_right p m)
        omega
    · rintro (⟨j, ⟨hj1, hjm⟩, rfl⟩ | ⟨hult, hnd⟩)
      · exact ⟨by nlinarith, by nlinarith⟩
      · refine ⟨?_, by omega⟩
        by_contra h0
        have hu0 : u = 0 := by omega
        exact hnd (hu0 ▸ dvd_zero p)
  have hdisj : Disjoint ((Finset.Icc 1 m).image (fun j => p * j))
      ((Finset.range (p * m)).filter (fun u => ¬ p ∣ u)) := by
    rw [Finset.disjoint_left]
    intro u hu1 hu2
    simp only [Finset.mem_image, Finset.mem_filter] at hu1 hu2
    rcases hu1 with ⟨j, _, rfl⟩
    exact hu2.2 (dvd_mul_right p j)
  rw [hpart, Finset.prod_union hdisj,
    Finset.prod_image (fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left (by omega) h)]

private lemma choose_mul_prod_Icc (d b : ℕ) :
    Nat.choose (d + b) b * (∏ j ∈ Finset.Icc 1 b, j) =
      ∏ j ∈ Finset.Icc 1 b, (d + j) := by
  induction b with
  | zero => simp
  | succ b ih =>
    have hIcc : Finset.Icc 1 (b + 1) = insert (b + 1) (Finset.Icc 1 b) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hIcc, Finset.prod_insert (by simp), Finset.prod_insert (by simp)]
    have hstep : (b + 1) * Nat.choose (d + (b + 1)) (b + 1) =
        (d + (b + 1)) * Nat.choose (d + b) b := by
      have h2 := succ_mul_choose_eq (d + b) b
      rw [show d + (b + 1) = d + b + 1 by omega]
      linarith
    calc Nat.choose (d + (b + 1)) (b + 1) * ((b + 1) * ∏ j ∈ Finset.Icc 1 b, j)
        = ((b + 1) * Nat.choose (d + (b + 1)) (b + 1)) * ∏ j ∈ Finset.Icc 1 b, j := by ring
      _ = (d + (b + 1)) * (Nat.choose (d + b) b * ∏ j ∈ Finset.Icc 1 b, j) := by rw [hstep]; ring
      _ = (d + (b + 1)) * ∏ j ∈ Finset.Icc 1 b, (d + j) := by rw [ih]

private lemma choose_mul_prod_nonmul (p a b : ℕ) (hp : 1 ≤ p) (hab : b ≤ a) :
    Nat.choose (p * a) (p * b) *
      (∏ u ∈ (Finset.range (p * b)).filter (fun u => ¬ p ∣ u), u) =
    Nat.choose a b *
      (∏ u ∈ (Finset.range (p * b)).filter (fun u => ¬ p ∣ u), (p * (a - b) + u)) := by
  set d := a - b
  have hdb : d + b = a := Nat.sub_add_cancel hab
  have hpdb : p * d + p * b = p * a := by rw [← mul_add, hdb]
  have h1 := choose_mul_prod_Icc (p * d) (p * b)
  rw [hpdb, prod_Icc_split_dvd p b hp (fun u => u),
    prod_Icc_split_dvd p b hp (fun u => p * d + u)] at h1
  have h2 := choose_mul_prod_Icc d b
  rw [hdb] at h2
  have hfac1 : ∏ j ∈ Finset.Icc 1 b, (p * j) = p ^ b * ∏ j ∈ Finset.Icc 1 b, j := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc]; simp
  have hfac2 : ∏ j ∈ Finset.Icc 1 b, (p * d + p * j) =
      p ^ b * ∏ j ∈ Finset.Icc 1 b, (d + j) := by
    have : ∀ j ∈ Finset.Icc 1 b, p * d + p * j = p * (d + j) := fun j _ => by ring
    rw [Finset.prod_congr rfl this, Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc]; simp
  rw [hfac1, hfac2] at h1
  have hpos : 0 < p ^ b * ∏ j ∈ Finset.Icc 1 b, j := by
    refine mul_pos (pow_pos (by omega) b) (Finset.prod_pos fun j hj => ?_)
    exact (Finset.mem_Icc.mp hj).1
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc (p ^ b * ∏ j ∈ Finset.Icc 1 b, j) *
        (Nat.choose (p * a) (p * b) * ∏ u ∈ (Finset.range (p * b)).filter (fun u => ¬ p ∣ u), u)
      = Nat.choose (p * a) (p * b) *
        ((p ^ b * ∏ j ∈ Finset.Icc 1 b, j) *
          ∏ u ∈ (Finset.range (p * b)).filter (fun u => ¬ p ∣ u), u) := by ring
    _ = (p ^ b * ∏ j ∈ Finset.Icc 1 b, (d + j)) *
        ∏ u ∈ (Finset.range (p * b)).filter (fun u => ¬ p ∣ u), (p * d + u) := h1
    _ = (p ^ b * (Nat.choose a b * ∏ j ∈ Finset.Icc 1 b, j)) *
        ∏ u ∈ (Finset.range (p * b)).filter (fun u => ¬ p ∣ u), (p * d + u) := by rw [← h2]
    _ = (p ^ b * ∏ j ∈ Finset.Icc 1 b, j) *
        (Nat.choose a b * ∏ u ∈ (Finset.range (p * b)).filter (fun u => ¬ p ∣ u), (p * d + u)) := by ring

private lemma prod_one_add_of_sq_zero {R : Type*} [CommRing R] {α : Type*}
    (s : Finset α) {c : R} (f : α → R) (hc : c ^ 2 = 0) :
    ∏ x ∈ s, (1 + c * f x) = 1 + c * ∑ x ∈ s, f x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih]
    have hsq : c * f a * (c * ∑ x ∈ s, f x) = 0 := by
      calc c * f a * (c * ∑ x ∈ s, f x) = c ^ 2 * (f a * ∑ x ∈ s, f x) := by ring
        _ = 0 := by rw [hc, zero_mul]
    calc (1 + c * f a) * (1 + c * ∑ x ∈ s, f x)
        = 1 + c * (f a + ∑ x ∈ s, f x) + c * f a * (c * ∑ x ∈ s, f x) := by ring
      _ = 1 + c * (f a + ∑ x ∈ s, f x) := by rw [hsq, add_zero]

private lemma jacobsthal_prod_cong {p a b t e : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hab : b ≤ a) (ht : 1 ≤ t) (hte : t ≤ e)
    (hB : p ^ t ∣ p * b) (hDA : p ^ e ∣ (p * (a - b)) * (p * a)) :
    (∏ u ∈ (Finset.range (p * b)).filter (fun u => ¬ p ∣ u),
        ((p * (a - b) + u : ℕ) : ZMod (p ^ (e + t)))) =
      (∏ u ∈ (Finset.range (p * b)).filter (fun u => ¬ p ∣ u),
        (u : ZMod (p ^ (e + t)))) := by
  set N := p ^ (e + t)
  set B := p * b
  set D := p * (a - b)
  set S := (Finset.range B).filter (fun u => ¬ p ∣ u)
  have hNpos : 0 < N := pow_pos hp.pos (e + t)
  set U : ZMod N := ∏ u ∈ S, (u : ZMod N)
  set P : ZMod N := ∏ u ∈ S, (1 + (D : ZMod N) * (u : ZMod N)⁻¹)
  have hprod_P : ∏ u ∈ S, ((D + u : ℕ) : ZMod N) = U * P := by
    simp only [U, P, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun u hu => ?_
    have hnd : ¬ p ∣ u := (Finset.mem_filter.mp hu).2
    have hinv := zmod_pow_mul_inv (s := e + t) hp hnd
    push_cast
    calc (D : ZMod N) + (u : ZMod N)
        = (u : ZMod N) + (D : ZMod N) * ((u : ZMod N) * (u : ZMod N)⁻¹) := by rw [hinv, mul_one]; ring
      _ = (u : ZMod N) * (1 + (D : ZMod N) * (u : ZMod N)⁻¹) := by ring
  have hP_eq_one : P = 1 := by
    have hP_rev : P = ∏ u ∈ S, (1 + (D : ZMod N) * ((B - u : ℕ) : ZMod N)⁻¹) := by
      refine Finset.prod_bij (fun u _ => B - u) ?_ ?_ ?_ ?_
      · intro u hu
        simp only [S, Finset.mem_filter, Finset.mem_range] at hu ⊢
        have hu1 : 1 ≤ u := Nat.pos_of_ne_zero (fun h => hu.2 (h ▸ dvd_zero p))
        refine ⟨by omega, fun hd => hu.2 ?_⟩
        have hpB : p ∣ B := dvd_mul_right p b
        exact (Nat.dvd_add_right hd).mp (by rwa [Nat.sub_add_cancel (by omega)])
      · intro u1 hu1 u2 hu2 heq
        simp only [S, Finset.mem_filter, Finset.mem_range] at hu1 hu2; omega
      · intro v hv
        simp only [S, Finset.mem_filter, Finset.mem_range] at hv
        have hv1 : 1 ≤ v := Nat.pos_of_ne_zero (fun h => hv.2 (h ▸ dvd_zero p))
        refine ⟨B - v, ?_, by omega⟩
        simp only [S, Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, fun hd => hv.2 ?_⟩
        have hpB : p ∣ B := dvd_mul_right p b
        exact (Nat.dvd_add_right hd).mp (by rwa [Nat.sub_add_cancel (by omega)])
      · intro u hu
        have hlt := Finset.mem_range.mp (Finset.mem_filter.mp hu).1
        rw [Nat.sub_sub_self (by omega)]
    have hDA_eq : (D : ZMod N) * ((D + B : ℕ) : ZMod N) = ((D * (p * a) : ℕ) : ZMod N) := by
      have : D + B = p * a := by
        simp only [D, B]; rw [← mul_add, Nat.sub_add_cancel hab]
      rw [this, ← Nat.cast_mul]
    have hP2 : P ^ 2 = ∏ u ∈ S, (1 + ((D * (p * a) : ℕ) : ZMod N) *
        ((u : ZMod N) * ((B - u : ℕ) : ZMod N))⁻¹) := by
      rw [sq]
      conv_lhs => rhs; rw [hP_rev]
      simp only [P, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun u hu => ?_
      have hnd1 : ¬ p ∣ u := (Finset.mem_filter.mp hu).2
      have hult : u < B := (Finset.mem_filter.mp hu).1 |> Finset.mem_range.mp
      have hnd2 : ¬ p ∣ (B - u) := fun hd => hnd1 <| by
        have hpB : p ∣ B := dvd_mul_right p b
        exact (Nat.dvd_add_right hd).mp (by rwa [Nat.sub_add_cancel (by omega)])
      have hu1 := isUnit_zmod_pow (s := e + t) hp hnd1
      have hu2 := isUnit_zmod_pow (s := e + t) hp hnd2
      have hmul_inv : ((u : ZMod N) * ((B - u : ℕ) : ZMod N))⁻¹ =
          (u : ZMod N)⁻¹ * ((B - u : ℕ) : ZMod N)⁻¹ := by
        have h1 : ((u : ZMod N) * ((B - u : ℕ) : ZMod N)) *
            ((u : ZMod N)⁻¹ * ((B - u : ℕ) : ZMod N)⁻¹) = 1 := by
          calc ((u : ZMod N) * ((B - u : ℕ) : ZMod N)) *
                ((u : ZMod N)⁻¹ * ((B - u : ℕ) : ZMod N)⁻¹)
              = ((u : ZMod N) * (u : ZMod N)⁻¹) *
                (((B - u : ℕ) : ZMod N) * ((B - u : ℕ) : ZMod N)⁻¹) := by ring
            _ = 1 := by rw [ZMod.mul_inv_of_unit _ hu1, ZMod.mul_inv_of_unit _ hu2, mul_one]
        exact (hu1.mul hu2).mul_left_cancel (by rw [ZMod.mul_inv_of_unit _ (hu1.mul hu2), h1])
      rw [hmul_inv, ← hDA_eq]
      have hBu : (B : ZMod N) = (u : ZMod N) + ((B - u : ℕ) : ZMod N) := by
        rw [← Nat.cast_add, Nat.add_sub_of_le (by omega)]
      have hinv1 := ZMod.mul_inv_of_unit _ hu1
      have hinv2 := ZMod.mul_inv_of_unit _ hu2
      have hsum_inv : (u : ZMod N)⁻¹ + ((B - u : ℕ) : ZMod N)⁻¹ =
          (B : ZMod N) * ((u : ZMod N)⁻¹ * ((B - u : ℕ) : ZMod N)⁻¹) := by
        rw [hBu]
        calc (u : ZMod N)⁻¹ + ((B - u : ℕ) : ZMod N)⁻¹
            = (u : ZMod N)⁻¹ * (((B - u : ℕ) : ZMod N) * ((B - u : ℕ) : ZMod N)⁻¹) +
              ((u : ZMod N) * (u : ZMod N)⁻¹) * ((B - u : ℕ) : ZMod N)⁻¹ := by rw [hinv1, hinv2]; ring
          _ = ((u : ZMod N) + ((B - u : ℕ) : ZMod N)) *
              ((u : ZMod N)⁻¹ * ((B - u : ℕ) : ZMod N)⁻¹) := by ring
      push_cast
      calc (1 + (D : ZMod N) * (u : ZMod N)⁻¹) * (1 + (D : ZMod N) * ((B - u : ℕ) : ZMod N)⁻¹)
          = 1 + (D : ZMod N) * ((u : ZMod N)⁻¹ + ((B - u : ℕ) : ZMod N)⁻¹) +
            (D : ZMod N) ^ 2 * ((u : ZMod N)⁻¹ * ((B - u : ℕ) : ZMod N)⁻¹) := by ring
        _ = 1 + (D : ZMod N) * ((D : ZMod N) + (B : ZMod N)) *
            ((u : ZMod N)⁻¹ * ((B - u : ℕ) : ZMod N)⁻¹) := by rw [hsum_inv]; ring
    have hc_sq : (((D * (p * a) : ℕ) : ZMod N)) ^ 2 = 0 := by
      rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
      have h1 : (p ^ e) ^ 2 ∣ (D * (p * a)) ^ 2 := pow_dvd_pow_of_dvd hDA 2
      have h2 : p ^ (e + t) ∣ (p ^ e) ^ 2 := by
        rw [← pow_mul]
        exact pow_dvd_pow p (by omega)
      exact dvd_trans h2 h1
    rw [prod_one_add_of_sq_zero S _ hc_sq] at hP2
    set sum_inv : ZMod N := ∑ u ∈ S, ((u : ZMod N) * ((B - u : ℕ) : ZMod N))⁻¹
    have hproj_sum : ZMod.castHom (pow_dvd_pow p (Nat.le_add_left t e)) (ZMod (p ^ t)) sum_inv = 0 := by
      set φ := ZMod.castHom (pow_dvd_pow p (Nat.le_add_left t e)) (ZMod (p ^ t))
      have hmap : φ sum_inv = ∑ u ∈ S, ((u : ZMod (p ^ t)) * ((B - u : ℕ) : ZMod (p ^ t)))⁻¹ := by
        simp only [sum_inv, map_sum]
        refine Finset.sum_congr rfl fun u hu => ?_
        have hnd1 : ¬ p ∣ u := (Finset.mem_filter.mp hu).2
        have hult : u < B := Finset.mem_range.mp (Finset.mem_filter.mp hu).1
        have hnd2 : ¬ p ∣ (B - u) := fun hd => hnd1 <| by
          have hpB : p ∣ B := dvd_mul_right p b
          exact (Nat.dvd_add_right hd).mp (by rwa [Nat.sub_add_cancel (by omega)])
        have huN : IsUnit ((u : ZMod N) * ((B - u : ℕ) : ZMod N)) :=
          (isUnit_zmod_pow hp hnd1).mul (isUnit_zmod_pow hp hnd2)
        have hut : IsUnit ((u : ZMod (p ^ t)) * ((B - u : ℕ) : ZMod (p ^ t))) :=
          (isUnit_zmod_pow hp hnd1).mul (isUnit_zmod_pow hp hnd2)
        have h1 := congrArg φ (ZMod.mul_inv_of_unit _ huN)
        simp only [map_mul, map_natCast, map_one] at h1
        exact hut.mul_left_cancel (by rw [h1, ZMod.mul_inv_of_unit _ hut])
      rw [hmap]
      exact sum_inv_pair_block hp h5 ht hB
    have hmul_zero : ((D * (p * a) : ℕ) : ZMod N) * sum_inv = 0 := by
      have : NeZero N := ⟨Nat.ne_of_gt hNpos⟩
      have hdvd_sum : p ^ t ∣ sum_inv.val := by
        rw [← ZMod.natCast_eq_zero_iff]
        have h1 : ZMod.castHom (pow_dvd_pow p (Nat.le_add_left t e)) (ZMod (p ^ t))
            (sum_inv.val : ZMod N) = (sum_inv.val : ZMod (p ^ t)) := map_natCast _ _
        rw [← h1, ZMod.natCast_zmod_val, hproj_sum]
      rcases hDA with ⟨q1, hq1⟩
      rcases hdvd_sum with ⟨q2, hq2⟩
      rw [← ZMod.natCast_zmod_val sum_inv, hq1, hq2, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
      dsimp only [N]
      rw [pow_add]
      exact ⟨q1 * q2, by ring⟩
    rw [hmul_zero, add_zero] at hP2
    have hP_mod_p : ZMod.castHom (dvd_pow_self p (by omega : e + t ≠ 0)) (ZMod p) P = 1 := by
      simp only [P, map_prod, map_add, map_one, map_mul, map_natCast]
      have hD0 : (D : ZMod p) = 0 := by
        rw [ZMod.natCast_eq_zero_iff]; exact dvd_mul_right p (a - b)
      simp [hD0]
    have hP1_unit : IsUnit (P + 1) := by
      have : NeZero N := ⟨Nat.ne_of_gt hNpos⟩
      rw [← ZMod.natCast_zmod_val (P + 1), ZMod.isUnit_iff_coprime]
      refine (coprime_of_not_dvd_prime hp ?_).pow_right (e + t)
      intro hd
      have h0 : ((P + 1).val : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).mpr hd
      have h1 : ZMod.castHom (dvd_pow_self p (by omega : e + t ≠ 0)) (ZMod p) (P + 1) = 0 := by
        rw [← ZMod.natCast_zmod_val (P + 1), map_natCast, h0]
      rw [map_add, map_one, hP_mod_p] at h1
      have h20 : ((2 : ℕ) : ZMod p) = 0 := by simpa only [Nat.cast_ofNat, one_add_one_eq_two] using h1
      have hd2 := (ZMod.natCast_eq_zero_iff 2 p).mp h20
      have := Nat.le_of_dvd (by decide) hd2; omega
    have hdiff : (P + 1) * (P - 1) = 0 := by linear_combination hP2
    have hPsub : P - 1 = 0 := hP1_unit.mul_left_cancel (by rw [hdiff, mul_zero])
    exact sub_eq_zero.mp hPsub
  rw [hprod_P, hP_eq_one, mul_one]

/-- Strong Jacobsthal/Kazandzidis divisibility in ℤ:
    for prime p ≥ 5 and 0 < v < u, p^(3 + v_p(u) + v_p(v) + v_p(u-v) + v_p(C(u,v))) | C(pu, pv) - C(u, v). -/
private lemma jacobsthal_strong {p u v : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hv : 0 < v) (hvu : v < u) :
    ((p ^ (3 + padicValNat p u + padicValNat p v + padicValNat p (u - v) +
        padicValNat p (Nat.choose u v)) : ℕ) : ℤ) ∣
      ((Nat.choose (p * u) (p * v) : ℤ) - (Nat.choose u v : ℤ)) := by
  have : Fact p.Prime := ⟨hp⟩
  -- Helper proving the claim whenever v_p(b) ≤ 1 + v_p(a) + v_p(a - b)
  have haux : ∀ a b : ℕ, 0 < b → b < a →
      padicValNat p b + 1 ≤ (padicValNat p a + 1) + (padicValNat p (a - b) + 1) →
      ((p ^ (3 + padicValNat p a + padicValNat p b + padicValNat p (a - b) +
          padicValNat p (Nat.choose a b)) : ℕ) : ℤ) ∣
        ((Nat.choose (p * a) (p * b) : ℤ) - (Nat.choose a b : ℤ)) := by
    intro a b hb hba hle
    set t := padicValNat p b + 1
    set e := (padicValNat p a + 1) + (padicValNat p (a - b) + 1)
    set k := padicValNat p (Nat.choose a b)
    have hB : p ^ t ∣ p * b := by
      rw [show t = padicValNat p b + 1 from rfl, pow_succ']
      exact mul_dvd_mul_left p pow_padicValNat_dvd
    have hDA : p ^ e ∣ (p * (a - b)) * (p * a) := by
      rw [show e = (padicValNat p a + 1) + (padicValNat p (a - b) + 1) from rfl, pow_add, mul_comm]
      refine mul_dvd_mul ?_ ?_
      · rw [pow_succ']; exact mul_dvd_mul_left p pow_padicValNat_dvd
      · rw [pow_succ']; exact mul_dvd_mul_left p pow_padicValNat_dvd
    have hcong := jacobsthal_prod_cong (p := p) (a := a) (b := b) (t := t) (e := e)
      hp h5 (by omega) (by omega) hle hB hDA
    set S := (Finset.range (p * b)).filter (fun w => ¬ p ∣ w)
    set U := ∏ w ∈ S, w
    set W := ∏ w ∈ S, (p * (a - b) + w)
    have hU_W : ((p ^ (e + t) : ℕ) : ℤ) ∣ ((W : ℤ) - (U : ℤ)) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_natCast, Int.cast_natCast,
        sub_eq_zero]
      simpa only [W, U, Nat.cast_prod] using hcong
    have hid_nat := choose_mul_prod_nonmul p a b hp.one_le (by omega)
    have hid_int : (U : ℤ) * ((Nat.choose (p * a) (p * b) : ℤ) - (Nat.choose a b : ℤ)) =
        (Nat.choose a b : ℤ) * ((W : ℤ) - (U : ℤ)) := by
      have h1 : (Nat.choose (p * a) (p * b) : ℤ) * (U : ℤ) = (Nat.choose a b : ℤ) * (W : ℤ) := by
        exact_mod_cast hid_nat
      linarith
    have hck : ((p ^ k : ℕ) : ℤ) ∣ (Nat.choose a b : ℤ) := by
      exact_mod_cast (pow_padicValNat_dvd : p ^ k ∣ Nat.choose a b)
    have hprod_dvd : ((p ^ (e + t + k) : ℕ) : ℤ) ∣
        (U : ℤ) * ((Nat.choose (p * a) (p * b) : ℤ) - (Nat.choose a b : ℤ)) := by
      rw [hid_int, pow_add, Nat.cast_mul, mul_comm ((p ^ (e + t) : ℕ) : ℤ)]
      exact mul_dvd_mul hck hU_W
    have hUnd : ¬ (p : ℤ) ∣ (U : ℤ) := by
      intro hd
      have hnat : p ∣ U := Int.natCast_dvd_natCast.mp hd
      have hcop : Nat.Coprime p U :=
        coprime_prod_right S p (fun w => w) fun w hw =>
          (coprime_of_not_dvd_prime hp (Finset.mem_filter.mp hw).2).symm
      have : p ∣ 1 := by
        have := Nat.dvd_gcd (dvd_refl p) hnat
        rwa [hcop.gcd_eq_one] at this
      have := Nat.le_of_dvd (by decide) this
      have := hp.two_le; omega
    have hfin := int_dvd_of_coprime_mul hp hUnd hprod_dvd
    have hexp : e + t + k = 3 + padicValNat p a + padicValNat p b + padicValNat p (a - b) + k := by
      omega
    rwa [hexp] at hfin
  by_cases hle : padicValNat p v + 1 ≤ (padicValNat p u + 1) + (padicValNat p (u - v) + 1)
  · exact haux u v hv hvu hle
  · -- Swap v and u - v; since u = v + (u - v) and v_p(v) > v_p(u), we have v_p(u - v) = v_p(u)
    have hswap_le : padicValNat p (u - v) + 1 ≤
        (padicValNat p u + 1) + (padicValNat p (u - (u - v)) + 1) := by
      have hsub : u - (u - v) = v := by omega
      rw [hsub]
      omega
    have hres := haux u (u - v) (by omega) (by omega) hswap_le
    have hsub : u - (u - v) = v := by omega
    have hsym1 : Nat.choose (p * u) (p * (u - v)) = Nat.choose (p * u) (p * v) := by
      rw [← Nat.choose_symm (by nlinarith : p * v ≤ p * u)]
      congr 1; rw [Nat.mul_sub_left_distrib]
    have hsym2 : Nat.choose u (u - v) = Nat.choose u v := Nat.choose_symm (by omega)
    rw [hsub, hsym1, hsym2] at hres
    have hexp : 3 + padicValNat p u + padicValNat p (u - v) + padicValNat p v +
        padicValNat p (Nat.choose u v) =
        3 + padicValNat p u + padicValNat p v + padicValNat p (u - v) +
        padicValNat p (Nat.choose u v) := by omega
    rwa [hexp] at hres

/-- Elementary valuation lower bounds on C(u, v) for 0 < v < u. -/
private lemma padicValNat_choose_ge_sub {p u v : ℕ} (hp : p.Prime) (hv : 0 < v) (hvu : v ≤ u) :
    padicValNat p u - padicValNat p v ≤ padicValNat p (Nat.choose u v) := by
  have : Fact p.Prime := ⟨hp⟩
  have hid : v * Nat.choose u v = u * Nat.choose (u - 1) (v - 1) := by
    have h := succ_mul_choose_eq (u - 1) (v - 1)
    rw [show u - 1 + 1 = u by omega, show v - 1 + 1 = v by omega] at h
    linarith
  have hpos : Nat.choose u v ≠ 0 := Nat.ne_of_gt (Nat.choose_pos hvu)
  have hpos2 : Nat.choose (u - 1) (v - 1) ≠ 0 := Nat.ne_of_gt (Nat.choose_pos (by omega))
  have hval := congrArg (padicValNat p) hid
  rw [padicValNat.mul (by omega) hpos, padicValNat.mul (by omega) hpos2] at hval
  omega

private lemma padicValNat_choose_ge_sub_symm {p u v : ℕ} (hp : p.Prime) (hvu : v < u) :
    padicValNat p u - padicValNat p (u - v) ≤ padicValNat p (Nat.choose u v) := by
  rw [← Nat.choose_symm (by omega : v ≤ u)]
  exact padicValNat_choose_ge_sub hp (by omega) (by omega)

/-- Ultrametric helper: if p^k | a and p^k | b then p^k | a - b (and a + b). -/
private lemma padicValNat_sub_ge_min {p a b : ℕ} (hp : p.Prime) (hba : b < a) :
    min (padicValNat p a) (padicValNat p b) ≤ padicValNat p (a - b) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← padicValNat_dvd_iff_le (by omega)]
  exact Nat.dvd_sub
    (dvd_trans (pow_dvd_pow p (min_le_left _ _)) pow_padicValNat_dvd)
    (dvd_trans (pow_dvd_pow p (min_le_right _ _)) pow_padicValNat_dvd)

private lemma padicValNat_add_ge_min {p a b : ℕ} (hp : p.Prime) (ha : 0 < a) (hb : 0 < b) :
    min (padicValNat p a) (padicValNat p b) ≤ padicValNat p (a + b) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← padicValNat_dvd_iff_le (by omega)]
  exact dvd_add
    (dvd_trans (pow_dvd_pow p (min_le_left _ _)) pow_padicValNat_dvd)
    (dvd_trans (pow_dvd_pow p (min_le_right _ _)) pow_padicValNat_dvd)

/-! ### Part 2: p-multiple terms via Jacobsthal/Kazandzidis -/

private abbrev a_seq := OMA.S_oeis_a123164.a

private lemma mul_pow_eq_mul_pred (p n r : ℕ) (hr : 0 < r) :
    n * p ^ r = p * (n * p ^ (r - 1)) := by
  conv_lhs => rw [show r = (r - 1) + 1 by omega, pow_succ]
  ring

private lemma le_padicValNat_mul_pow {p n r : ℕ} (hp : p.Prime) (hn : 0 < n) :
    r ≤ padicValNat p (n * p ^ r) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [padicValNat.mul hn.ne' (pow_ne_zero r hp.ne_zero), padicValNat.prime_pow]
  omega

private lemma choose_mul_prime_dvd {p u v : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    ((p ^ padicValNat p (u.choose v) : ℕ) : ℤ) ∣ ((p * u).choose (p * v) : ℤ) := by
  have h1 : ((p ^ padicValNat p (u.choose v) : ℕ) : ℤ) ∣ (u.choose v : ℤ) :=
    Int.natCast_dvd_natCast.mpr pow_padicValNat_dvd
  by_cases hv0 : v = 0
  · subst hv0; simp
  by_cases huv : v < u
  · have hj := jacobsthal_strong hp h5 (Nat.pos_of_ne_zero hv0) huv
    have hd : ((p ^ padicValNat p (u.choose v) : ℕ) : ℤ) ∣
        (((p * u).choose (p * v) : ℤ) - (u.choose v : ℤ)) :=
      dvd_trans (Int.natCast_dvd_natCast.mpr (pow_dvd_pow p (by omega))) hj
    have hadd := dvd_add hd h1
    simpa using hadd
  · by_cases heq : v = u
    · subst heq; simp
    · have hlt : u < v := by omega
      rw [Nat.choose_eq_zero_of_lt hlt, Nat.choose_eq_zero_of_lt (by nlinarith : p * u < p * v)]
      exact dvd_zero _

private lemma add_mul_choose_pred (u j : ℕ) (hu : 1 ≤ u) :
    (u + j) * (u + j - 1).choose j = u * (u + j).choose j := by
  have h1 : (u + j - 1).choose j = (u + j - 1).choose (u - 1) := by
    have := Nat.choose_symm (show j ≤ u + j - 1 by omega)
    rw [show u + j - 1 - j = u - 1 by omega] at this
    exact this.symm
  have h2 : (u + j).choose j = (u + j).choose u := by
    have := Nat.choose_symm (show j ≤ u + j by omega)
    rw [show u + j - j = u by omega] at this
    exact this.symm
  rw [h1, h2]
  have h3 := succ_mul_choose_eq (u + j - 1) (u - 1)
  rwa [show u + j - 1 + 1 = u + j by omega, show u - 1 + 1 = u by omega] at h3

/-- For every 0 ≤ j ≤ N = n*p^(r-1), p^(3*r) divides the difference of p-multiple terms. -/
private lemma mul_term_diff_dvd {p n r j : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hn : 0 < n) (hr : 0 < r) (hj : j ≤ n * p ^ (r - 1)) :
    ((p ^ (3 * r) : ℕ) : ℤ) ∣
      (((n * p ^ r).choose (p * j) * (n * p ^ r + p * j - 1).choose (p * j) : ℕ) : ℤ) -
      (((n * p ^ (r - 1)).choose j * (n * p ^ (r - 1) + j - 1).choose j : ℕ) : ℤ) := by
  have : Fact p.Prime := ⟨hp⟩
  set N := n * p ^ (r - 1)
  set M := n * p ^ r
  have hMp : M = p * N := mul_pow_eq_mul_pred p n r hr
  have hNpos : 0 < N := mul_pos hn (pow_pos hp.pos (r - 1))
  have hMpos : 0 < M := mul_pos hn (pow_pos hp.pos r)
  by_cases hj0 : j = 0
  · subst hj0; simp
  have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
  have hNjpos : 0 < N + j := by omega
  have hN_ge : r - 1 ≤ padicValNat p N := le_padicValNat_mul_pow hp hn
  set vN := padicValNat p N
  set vj := padicValNat p j
  set vNj := padicValNat p (N + j)
  set w1 := padicValNat p (N.choose j)
  set w2 := padicValNat p ((N + j).choose j)
  have hw1 : vN - vj ≤ w1 := padicValNat_choose_ge_sub hp hjpos hj
  have hw2 : vNj - vj ≤ w2 := padicValNat_choose_ge_sub hp hjpos (by omega)
  -- Identity: (N + j) * Δ = N * (A1 * A2 - B1 * B2)
  have hid_M : (N + j) * (M.choose (p * j) * (M + p * j - 1).choose (p * j)) =
      N * (M.choose (p * j) * (M + p * j).choose (p * j)) := by
    have h1 := add_mul_choose_pred M (p * j) hMpos
    have h2 : p * (N + j) = M + p * j := by rw [hMp]; ring
    have h3 : p * ((N + j) * (M + p * j - 1).choose (p * j)) =
        p * (N * (M + p * j).choose (p * j)) := by
      calc p * ((N + j) * (M + p * j - 1).choose (p * j))
          = (M + p * j) * (M + p * j - 1).choose (p * j) := by rw [← h2]; ring
        _ = M * (M + p * j).choose (p * j) := h1
        _ = p * (N * (M + p * j).choose (p * j)) := by rw [hMp]; ring
    have h4 := Nat.eq_of_mul_eq_mul_left hp.pos h3
    calc (N + j) * (M.choose (p * j) * (M + p * j - 1).choose (p * j))
        = M.choose (p * j) * ((N + j) * (M + p * j - 1).choose (p * j)) := by ring
      _ = M.choose (p * j) * (N * (M + p * j).choose (p * j)) := by rw [h4]
      _ = N * (M.choose (p * j) * (M + p * j).choose (p * j)) := by ring
  have hid_N : (N + j) * (N.choose j * (N + j - 1).choose j) =
      N * (N.choose j * (N + j).choose j) := by
    have h1 := add_mul_choose_pred N j hNpos
    calc (N + j) * (N.choose j * (N + j - 1).choose j)
        = N.choose j * ((N + j) * (N + j - 1).choose j) := by ring
      _ = N.choose j * (N * (N + j).choose j) := by rw [h1]
      _ = N * (N.choose j * (N + j).choose j) := by ring
  -- Show p^(3*r + vNj) ∣ (N + j) * Δ
  have hmul_dvd : ((p ^ (3 * r + vNj) : ℕ) : ℤ) ∣
      ((N + j : ℕ) : ℤ) *
        ((((M.choose (p * j) * (M + p * j - 1).choose (p * j) : ℕ) : ℤ)) -
         (((N.choose j * (N + j - 1).choose j : ℕ) : ℤ))) := by
    have hrw : ((N + j : ℕ) : ℤ) *
        ((((M.choose (p * j) * (M + p * j - 1).choose (p * j) : ℕ) : ℤ)) -
         (((N.choose j * (N + j - 1).choose j : ℕ) : ℤ))) =
      (N : ℤ) * (((M.choose (p * j) : ℤ) - (N.choose j : ℤ)) * ((M + p * j).choose (p * j) : ℤ)) +
      (N : ℤ) * ((N.choose j : ℤ) * (((M + p * j).choose (p * j) : ℤ) - ((N + j).choose j : ℤ))) := by
      rw [mul_sub, ← Nat.cast_mul, ← Nat.cast_mul, hid_M, hid_N]
      push_cast; ring
    rw [hrw]
    have hN_dvd : ((p ^ vN : ℕ) : ℤ) ∣ (N : ℤ) := Int.natCast_dvd_natCast.mpr pow_padicValNat_dvd
    have hB1_dvd : ((p ^ w1 : ℕ) : ℤ) ∣ (N.choose j : ℤ) :=
      Int.natCast_dvd_natCast.mpr pow_padicValNat_dvd
    have hMp_add : M + p * j = p * (N + j) := by rw [hMp]; ring
    refine dvd_add ?_ ?_
    · -- Term 1: N * (C(p*N, p*j) - C(N, j)) * C(p*(N+j), p*j)
      by_cases hjN : j = N
      · subst hjN; rw [hMp, Nat.choose_self, Nat.choose_self, sub_self, zero_mul, mul_zero]
        exact dvd_zero _
      have hjlt : j < N := lt_of_le_of_ne hj hjN
      have hJ1 : ((p ^ (3 + vN + vj + padicValNat p (N - j) + w1) : ℕ) : ℤ) ∣
          ((M.choose (p * j) : ℤ) - (N.choose j : ℤ)) := by
        rw [hMp]; exact jacobsthal_strong hp h5 hjpos hjlt
      have hA2_dvd : ((p ^ w2 : ℕ) : ℤ) ∣ ((M + p * j).choose (p * j) : ℤ) := by
        rw [hMp_add]; exact choose_mul_prime_dvd hp h5
      have hprod := mul_dvd_mul hN_dvd (mul_dvd_mul hJ1 hA2_dvd)
      rw [← Nat.cast_mul, ← Nat.cast_mul, ← pow_add, ← pow_add] at hprod
      refine dvd_trans (Int.natCast_dvd_natCast.mpr (pow_dvd_pow p ?_)) hprod
      have hsub := padicValNat_sub_ge_min hp hjlt
      have hult1 : min vNj vN ≤ vj := by
        have h := padicValNat_sub_ge_min hp (by omega : N < N + j)
        rwa [Nat.add_sub_cancel_left] at h
      have hult2 : min vNj vj ≤ vN := by
        have h := padicValNat_sub_ge_min hp (by omega : j < N + j)
        rwa [Nat.add_sub_cancel] at h
      omega
    · -- Term 2: N * C(N, j) * (C(p*(N+j), p*j) - C(N+j, j))
      have hJ2 : ((p ^ (3 + vNj + vj + vN + w2) : ℕ) : ℤ) ∣
          (((M + p * j).choose (p * j) : ℤ) - ((N + j).choose j : ℤ)) := by
        rw [hMp_add]
        have h := jacobsthal_strong hp h5 hjpos (by omega : j < N + j)
        rwa [Nat.add_sub_cancel] at h
      have hprod := mul_dvd_mul hN_dvd (mul_dvd_mul hB1_dvd hJ2)
      rw [← Nat.cast_mul, ← Nat.cast_mul, ← pow_add, ← pow_add] at hprod
      refine dvd_trans (Int.natCast_dvd_natCast.mpr (pow_dvd_pow p ?_)) hprod
      omega
  -- Cancel (N + j) = p^vNj * u with ¬ p ∣ u
  set u := (N + j) / p ^ vNj
  have hNj_eq : N + j = p ^ vNj * u := (Nat.mul_div_cancel' pow_padicValNat_dvd).symm
  have hnd_u : ¬ p ∣ u := by
    intro hpu
    have h1 : p ^ (vNj + 1) ∣ N + j := by
      rw [hNj_eq, pow_succ]; exact mul_dvd_mul_left (p ^ vNj) hpu
    have h2 : vNj + 1 ≤ vNj := (padicValNat_dvd_iff_le hNjpos.ne').mp h1
    omega
  have hNj_cast : ((N + j : ℕ) : ℤ) = ((p ^ vNj : ℕ) : ℤ) * (u : ℤ) := by exact_mod_cast hNj_eq
  rw [pow_add, Nat.cast_mul] at hmul_dvd
  have hcancel : ((p ^ (3 * r) : ℕ) : ℤ) ∣
      (u : ℤ) * ((((M.choose (p * j) * (M + p * j - 1).choose (p * j) : ℕ) : ℤ)) -
                 (((N.choose j * (N + j - 1).choose j : ℕ) : ℤ))) := by
    rcases hmul_dvd with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have hpne : ((p ^ vNj : ℕ) : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (pow_ne_zero _ hp.ne_zero)
    apply mul_left_cancel₀ hpne
    rw [← mul_assoc, ← hNj_cast, hc]
    ring
  have hnd_uz : ¬ (p : ℤ) ∣ (u : ℤ) := fun hd => hnd_u (Int.natCast_dvd_natCast.mp hd)
  exact int_dvd_of_coprime_mul hp hnd_uz hcancel

/-! ### Part 3: Non-multiple sum divisibility by p^(3*r) via alternating block telescoping -/

private def gFun (M q : ℕ) : ℤ :=
  (-1 : ℤ) ^ q * (((M - 1).choose q * (M + q).choose q : ℕ) : ℤ)

private lemma term_mul_sq_eq {M k : ℕ} (hk1 : 1 ≤ k) (hkM : k ≤ M) :
    ((k : ℤ) ^ 2) * ((M.choose k * (M + k - 1).choose k : ℕ) : ℤ) =
      (M : ℤ) ^ 2 * (-1 : ℤ) ^ (k - 1) * gFun M (k - 1) := by
  have h1 : k * M.choose k = M * (M - 1).choose (k - 1) := by
    have := (succ_mul_choose_eq (M - 1) (k - 1)).symm
    rwa [show M - 1 + 1 = M by omega, show k - 1 + 1 = k by omega] at this
  have h2 : k * (M + k - 1).choose k = M * (M + k - 1).choose (k - 1) := by
    have hsym1 : (M + k - 1).choose k = (M + k - 1).choose (M - 1) := by
      have := Nat.choose_symm (show k ≤ M + k - 1 by omega)
      rw [show M + k - 1 - k = M - 1 by omega] at this; exact this.symm
    have hsym2 : (M + k - 1).choose (k - 1) = (M + k - 1).choose M := by
      have := Nat.choose_symm (show k - 1 ≤ M + k - 1 by omega)
      rw [show M + k - 1 - (k - 1) = M by omega] at this; exact this.symm
    rw [hsym1, hsym2]
    have h3 : k * (M + k - 1).choose (M - 1) = M * (M + k - 1).choose M := by
      have ha := succ_mul_choose_eq (M + k - 1) (M - 1)
      have hb := succ_mul_choose_eq (M + k - 1) (k - 1)
      -- Wait: directly use Nat.choose_succ_right_eq!
      have hc := Nat.choose_succ_right_eq (M + k - 1) (M - 1)
      rw [show M - 1 + 1 = M by omega, show M + k - 1 - (M - 1) = k by omega] at hc
      linarith
    exact h3
  have hnat : k ^ 2 * (M.choose k * (M + k - 1).choose k) =
      M ^ 2 * ((M - 1).choose (k - 1) * (M + (k - 1)).choose (k - 1)) := by
    rw [show M + (k - 1) = M + k - 1 by omega]
    calc k ^ 2 * (M.choose k * (M + k - 1).choose k)
        = (k * M.choose k) * (k * (M + k - 1).choose k) := by ring
      _ = (M * (M - 1).choose (k - 1)) * (M * (M + k - 1).choose (k - 1)) := by rw [h1, h2]
      _ = M ^ 2 * ((M - 1).choose (k - 1) * (M + k - 1).choose (k - 1)) := by ring
  have hcast : ((k : ℤ) ^ 2) * ((M.choose k * (M + k - 1).choose k : ℕ) : ℤ) =
      (M : ℤ) ^ 2 * (((M - 1).choose (k - 1) * (M + (k - 1)).choose (k - 1) : ℕ) : ℤ) := by
    exact_mod_cast hnat
  have hsign : (-1 : ℤ) ^ (k - 1) * (-1 : ℤ) ^ (k - 1) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  rw [hcast, gFun]
  calc (M : ℤ) ^ 2 * (((M - 1).choose (k - 1) * (M + (k - 1)).choose (k - 1) : ℕ) : ℤ)
      = (M : ℤ) ^ 2 * ((-1 : ℤ) ^ (k - 1) * (-1 : ℤ) ^ (k - 1)) *
          (((M - 1).choose (k - 1) * (M + (k - 1)).choose (k - 1) : ℕ) : ℤ) := by rw [hsign, mul_one]
    _ = (M : ℤ) ^ 2 * (-1 : ℤ) ^ (k - 1) *
          ((-1 : ℤ) ^ (k - 1) * (((M - 1).choose (k - 1) * (M + (k - 1)).choose (k - 1) : ℕ) : ℤ)) := by ring

private lemma gFun_step_int {M q : ℕ} (hq : q + 1 ≤ M) :
    ((q + 1 : ℤ) ^ 2) * (gFun M (q + 1) - gFun M q) = -((M : ℤ) ^ 2) * gFun M q := by
  have h1 : (q + 1) * (M - 1).choose (q + 1) = (M - 1 - q) * (M - 1).choose q := by
    have := Nat.choose_succ_right_eq (M - 1) q
    linarith
  have h2 : (q + 1) * (M + (q + 1)).choose (q + 1) = (M + q + 1) * (M + q).choose q := by
    have := succ_mul_choose_eq (M + q) q
    rw [show M + q + 1 = M + (q + 1) by omega] at this ⊢
    linarith
  have hnat : (q + 1) ^ 2 * ((M - 1).choose (q + 1) * (M + (q + 1)).choose (q + 1)) =
      (M - 1 - q) * (M + q + 1) * ((M - 1).choose q * (M + q).choose q) := by
    calc (q + 1) ^ 2 * ((M - 1).choose (q + 1) * (M + (q + 1)).choose (q + 1))
        = ((q + 1) * (M - 1).choose (q + 1)) * ((q + 1) * (M + (q + 1)).choose (q + 1)) := by ring
      _ = ((M - 1 - q) * (M - 1).choose q) * ((M + q + 1) * (M + q).choose q) := by rw [h1, h2]
      _ = (M - 1 - q) * (M + q + 1) * ((M - 1).choose q * (M + q).choose q) := by ring
  have hsub_cast : ((M - 1 - q : ℕ) : ℤ) = (M : ℤ) - ((q : ℤ) + 1) := by omega
  have hcast : ((q + 1 : ℤ) ^ 2) * (((M - 1).choose (q + 1) * (M + (q + 1)).choose (q + 1) : ℕ) : ℤ) =
      ((M : ℤ) ^ 2 - (q + 1 : ℤ) ^ 2) * (((M - 1).choose q * (M + q).choose q : ℕ) : ℤ) := by
    have hz : (((q + 1) ^ 2 * ((M - 1).choose (q + 1) * (M + (q + 1)).choose (q + 1)) : ℕ) : ℤ) =
        (((M - 1 - q) * (M + q + 1) * ((M - 1).choose q * (M + q).choose q) : ℕ) : ℤ) :=
      congrArg Nat.cast hnat
    push_cast at hz ⊢
    rw [hsub_cast] at hz
    linear_combination hz
  simp only [gFun, pow_succ]
  linear_combination (-((-1 : ℤ) ^ q)) * hcast

private lemma gFun_step_dvd {p M r q s : ℕ} (hp : p.Prime)
    (hMr : p ^ r ∣ M) (hq : q + 1 ≤ M) (hs : s ≤ r) (hnd : ¬ p ^ (s + 1) ∣ (q + 1)) :
    ((p ^ (2 * r - 2 * s) : ℕ) : ℤ) ∣ gFun M (q + 1) - gFun M q := by
  have : Fact p.Prime := ⟨hp⟩
  set e := padicValNat p (q + 1)
  have he_le : e ≤ s := by
    by_contra hgt
    push Not at hgt
    have hd : p ^ (s + 1) ∣ q + 1 :=
      (padicValNat_dvd_iff_le (by omega : q + 1 ≠ 0)).mpr (by omega)
    exact hnd hd
  set u := (q + 1) / p ^ e
  have hq1_eq : q + 1 = p ^ e * u := (Nat.mul_div_cancel' pow_padicValNat_dvd).symm
  have hnd_u : ¬ p ∣ u := by
    intro hpu
    have h1 : p ^ (e + 1) ∣ q + 1 := by
      rw [hq1_eq, pow_succ]; exact mul_dvd_mul_left (p ^ e) hpu
    have h2 : e + 1 ≤ e := (padicValNat_dvd_iff_le (by omega : q + 1 ≠ 0)).mp h1
    omega
  have hstep := gFun_step_int hq
  have hM2_dvd : ((p ^ (2 * r) : ℕ) : ℤ) ∣ -((M : ℤ) ^ 2) * gFun M q := by
    have h1 : p ^ (2 * r) ∣ M ^ 2 := by
      rw [mul_comm, pow_mul]; exact pow_dvd_pow_of_dvd hMr 2
    exact dvd_mul_of_dvd_left (dvd_neg.mpr (Int.natCast_dvd_natCast.mpr h1)) _
  rw [← hstep] at hM2_dvd
  have hq1_sq : ((q + 1 : ℤ) ^ 2) = ((p ^ (2 * e) : ℕ) : ℤ) * ((u : ℤ) ^ 2) := by
    have hnat : (q + 1) ^ 2 = p ^ (2 * e) * u ^ 2 := by
      rw [hq1_eq, mul_pow, ← pow_mul, mul_comm e 2]
    exact_mod_cast hnat
  rw [hq1_sq, mul_assoc] at hM2_dvd
  have hsplit : 2 * r = 2 * e + (2 * r - 2 * e) := by omega
  rw [hsplit, pow_add, Nat.cast_mul] at hM2_dvd
  have hcancel : ((p ^ (2 * r - 2 * e) : ℕ) : ℤ) ∣ ((u : ℤ) ^ 2) * (gFun M (q + 1) - gFun M q) := by
    rcases hM2_dvd with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have hpne : ((p ^ (2 * e) : ℕ) : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (pow_ne_zero _ hp.ne_zero)
    apply mul_left_cancel₀ hpne
    linarith
  have hnd_u2 : ¬ (p : ℤ) ∣ ((u : ℤ) ^ 2) := by
    intro hd
    have hp_int : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hu_dvd : (p : ℤ) ∣ (u : ℤ) := hp_int.dvd_of_dvd_pow hd
    exact hnd_u (Int.natCast_dvd_natCast.mp hu_dvd)
  have hdvd := int_dvd_of_coprime_mul hp hnd_u2 hcancel
  exact dvd_trans (Int.natCast_dvd_natCast.mpr (pow_dvd_pow p (by omega))) hdvd

private lemma gFun_block_cong {p M r t v q1 q2 : ℕ} (hp : p.Prime)
    (hMr : p ^ r ∣ M) (ht1 : 1 ≤ t) (htr : t ≤ r)
    (hvq1 : v * p ^ t ≤ q1) (hq12 : q1 ≤ q2) (hq2v : q2 < (v + 1) * p ^ t)
    (hvM : (v + 1) * p ^ t ≤ M) :
    (gFun M q1 : ZMod (p ^ (r + 1 - t))) = (gFun M q2 : ZMod (p ^ (r + 1 - t))) := by
  induction q2 with
  | zero =>
    have h0 : q1 = 0 := by omega
    subst h0; rfl
  | succ q ih =>
    by_cases hle : q1 ≤ q
    · have hih := ih hle (by omega)
      rw [hih]
      have hnd : ¬ p ^ t ∣ (q + 1) := by
        intro ⟨k, hk⟩
        have hpt : 0 < p ^ t := pow_pos hp.pos t
        have hlt1 : v < k := by nlinarith
        have hlt2 : k < v + 1 := by nlinarith
        omega
      have hdvd := gFun_step_dvd (q := q) hp hMr (by omega) (s := t - 1) (by omega) (by
        rwa [show t - 1 + 1 = t by omega])
      have hdvd' : ((p ^ (r + 1 - t) : ℕ) : ℤ) ∣ gFun M (q + 1) - gFun M q :=
        dvd_trans (Int.natCast_dvd_natCast.mpr (pow_dvd_pow p (by omega))) hdvd
      have hzero : ((gFun M (q + 1) - gFun M q : ℤ) : ZMod (p ^ (r + 1 - t))) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd'
      push_cast at hzero
      exact (sub_eq_zero.mp hzero).symm
    · have heq : q1 = q + 1 := by omega
      subst heq; rfl

private lemma sum_alt_inv_sq_units {p t : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (ht : 1 ≤ t) :
    ∑ w ∈ (Finset.range (p ^ t)).filter (fun w => ¬ p ∣ w),
      (-1 : ZMod (p ^ t)) ^ (w - 1) * ((w : ZMod (p ^ t))⁻¹) ^ 2 = 0 := by
  set S := (Finset.range (p ^ t)).filter (fun w => ¬ p ∣ w)
  set f : ℕ → ZMod (p ^ t) := fun w => (-1 : ZMod (p ^ t)) ^ (w - 1) * ((w : ZMod (p ^ t))⁻¹) ^ 2
  have hodd_p : p % 2 = 1 := by
    have hne : p ≠ 2 := by omega
    exact (hp.eq_two_or_odd.resolve_left hne)
  have hodd_pow : ∀ m, p ^ m % 2 = 1 := fun m => by
    induction m with
    | zero => simp
    | succ k ih => rw [pow_succ, Nat.mul_mod, ih, hodd_p]
  have hodd_pt : p ^ t % 2 = 1 := hodd_pow t
  have hpt_pos : 0 < p ^ t := pow_pos hp.pos t
  have hpt2 : 2 ≤ p ^ t := le_trans (by omega : 2 ≤ p) (Nat.le_self_pow (by omega) p)
  have hneg : ∑ w ∈ S, f w = - ∑ w ∈ S, f w := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_bij (fun w _ => p ^ t - w) ?_ ?_ ?_ ?_
    · intro w hw
      simp only [S, Finset.mem_filter, Finset.mem_range] at hw ⊢
      have hw1 : 1 ≤ w := Nat.pos_of_ne_zero (fun h => hw.2 (h ▸ dvd_zero p))
      refine ⟨by omega, fun hd => hw.2 ?_⟩
      have hpt_dvd : p ∣ p ^ t := dvd_pow_self p (by omega)
      have := Nat.dvd_sub hpt_dvd hd
      rwa [Nat.sub_sub_self (by omega)] at this
    · intro w1 hw1 w2 hw2 heq
      simp only [S, Finset.mem_filter, Finset.mem_range] at hw1 hw2
      omega
    · intro w hw
      simp only [S, Finset.mem_filter, Finset.mem_range] at hw
      have hw1 : 1 ≤ w := Nat.pos_of_ne_zero (fun h => hw.2 (h ▸ dvd_zero p))
      refine ⟨p ^ t - w, ?_, by omega⟩
      simp only [S, Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, fun hd => hw.2 ?_⟩
      have hpt_dvd : p ∣ p ^ t := dvd_pow_self p (by omega)
      have := Nat.dvd_sub hpt_dvd hd
      rwa [Nat.sub_sub_self (by omega)] at this
    · intro w hw
      simp only [S, Finset.mem_filter, Finset.mem_range] at hw
      have hw1 : 1 ≤ w := Nat.pos_of_ne_zero (fun h => hw.2 (h ▸ dvd_zero p))
      have hnd2 : ¬ p ∣ (p ^ t - w) := fun hd => hw.2 <| by
        have hpt_dvd : p ∣ p ^ t := dvd_pow_self p (by omega)
        have := Nat.dvd_sub hpt_dvd hd
        rwa [Nat.sub_sub_self (by omega)] at this
      have hcast_neg : ((p ^ t - w : ℕ) : ZMod (p ^ t)) = -(w : ZMod (p ^ t)) := by
        rw [Nat.cast_sub (by omega), ZMod.natCast_self, zero_sub]
      have hu1 : IsUnit (w : ZMod (p ^ t)) := isUnit_zmod_pow hp hw.2
      have hu2 : IsUnit ((p ^ t - w : ℕ) : ZMod (p ^ t)) := isUnit_zmod_pow hp hnd2
      have hinv_neg : ((p ^ t - w : ℕ) : ZMod (p ^ t))⁻¹ = -((w : ZMod (p ^ t))⁻¹) := by
        apply hu1.mul_left_cancel
        have h1 := ZMod.mul_inv_of_unit _ hu2
        conv_lhs at h1 => arg 1; rw [hcast_neg]
        rw [neg_mul] at h1
        have h2 := ZMod.mul_inv_of_unit _ hu1
        rw [mul_neg, h2]
        linear_combination -h1
      have hsign : (-1 : ZMod (p ^ t)) ^ (p ^ t - w - 1) = -((-1 : ZMod (p ^ t)) ^ (w - 1)) := by
        have hmul_eq : (-1 : ZMod (p ^ t)) ^ (p ^ t - w - 1) * (-1 : ZMod (p ^ t)) ^ (w - 1) = -1 := by
          rw [← pow_add, show p ^ t - w - 1 + (w - 1) = 2 * ((p ^ t - 2) / 2) + 1 by omega,
            pow_succ, pow_mul]
          norm_num
        have hsq : (-1 : ZMod (p ^ t)) ^ (w - 1) * (-1 : ZMod (p ^ t)) ^ (w - 1) = 1 := by
          rw [← pow_add, ← two_mul, pow_mul]; norm_num
        calc (-1 : ZMod (p ^ t)) ^ (p ^ t - w - 1)
            = (-1 : ZMod (p ^ t)) ^ (p ^ t - w - 1) *
                ((-1 : ZMod (p ^ t)) ^ (w - 1) * (-1 : ZMod (p ^ t)) ^ (w - 1)) := by rw [hsq, mul_one]
          _ = ((-1 : ZMod (p ^ t)) ^ (p ^ t - w - 1) * (-1 : ZMod (p ^ t)) ^ (w - 1)) *
                (-1 : ZMod (p ^ t)) ^ (w - 1) := by ring
          _ = -((-1 : ZMod (p ^ t)) ^ (w - 1)) := by rw [hmul_eq]; ring
      dsimp only [f]
      rw [hinv_neg, neg_sq, hsign]; ring
  have h2sum : (2 : ZMod (p ^ t)) * ∑ w ∈ S, f w = 0 := by
    have : ∑ w ∈ S, f w + ∑ w ∈ S, f w = 0 := by linear_combination hneg
    linear_combination this
  have h2nd : ¬ p ∣ 2 := fun hd => by have := Nat.le_of_dvd (by decide) hd; omega
  have hu2 : IsUnit ((2 : ℕ) : ZMod (p ^ t)) := isUnit_zmod_pow hp h2nd
  have h2eq : ((2 : ℕ) : ZMod (p ^ t)) * ∑ w ∈ S, f w = ((2 : ℕ) : ZMod (p ^ t)) * 0 := by
    simpa using h2sum
  exact hu2.mul_left_cancel h2eq

private def I_alt (p r t v : ℕ) : ZMod (p ^ r) :=
  ∑ w ∈ (Finset.range (p ^ t)).filter (fun w => ¬ p ∣ w),
    (-1 : ZMod (p ^ r)) ^ (v * p ^ t + w - 1) * (((v * p ^ t + w : ℕ) : ZMod (p ^ r))⁻¹) ^ 2

private lemma proj_I_alt_eq_zero {p r t v : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (ht : 1 ≤ t) (htr : t ≤ r) :
    ZMod.castHom (pow_dvd_pow p htr) (ZMod (p ^ t)) (I_alt p r t v) = 0 := by
  set φ := ZMod.castHom (pow_dvd_pow p htr) (ZMod (p ^ t))
  have hmap : φ (I_alt p r t v) =
      (-1 : ZMod (p ^ t)) ^ (v * p ^ t) *
        ∑ w ∈ (Finset.range (p ^ t)).filter (fun w => ¬ p ∣ w),
          (-1 : ZMod (p ^ t)) ^ (w - 1) * ((w : ZMod (p ^ t))⁻¹) ^ 2 := by
    simp only [I_alt, map_sum, map_mul, map_pow, map_neg, map_one, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w hw => ?_
    have hnd : ¬ p ∣ w := (Finset.mem_filter.mp hw).2
    have hw1 : 1 ≤ w := Nat.pos_of_ne_zero (fun h => hnd (h ▸ dvd_zero p))
    have hnd2 : ¬ p ∣ (v * p ^ t + w) := fun hd => hnd <| by
      have hp1 : p ∣ v * p ^ t := dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) v
      exact (Nat.dvd_add_right hp1).mp hd
    have huR : IsUnit ((v * p ^ t + w : ℕ) : ZMod (p ^ r)) := isUnit_zmod_pow hp hnd2
    have huK : IsUnit (w : ZMod (p ^ t)) := isUnit_zmod_pow hp hnd
    have h1 := congrArg φ (ZMod.mul_inv_of_unit _ huR)
    rw [map_mul, map_natCast, map_one] at h1
    have hcast : ((v * p ^ t + w : ℕ) : ZMod (p ^ t)) = (w : ZMod (p ^ t)) := by
      simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add]
    rw [hcast] at h1
    have hinv : φ (((v * p ^ t + w : ℕ) : ZMod (p ^ r))⁻¹) = (w : ZMod (p ^ t))⁻¹ :=
      huK.mul_left_cancel (by rw [h1, ZMod.mul_inv_of_unit _ huK])
    rw [hinv, show v * p ^ t + w - 1 = v * p ^ t + (w - 1) by omega, pow_add]
    ring
  rw [hmap, sum_alt_inv_sq_units hp h5 ht, mul_zero]

private lemma mul_zero_of_proj_eq_zero {p r s t : ℕ} (hp : p.Prime) (hst : s + t = r)
    (x y : ZMod (p ^ r))
    (hx : ZMod.castHom (pow_dvd_pow p (by omega : s ≤ r)) (ZMod (p ^ s)) x = 0)
    (hy : ZMod.castHom (pow_dvd_pow p (by omega : t ≤ r)) (ZMod (p ^ t)) y = 0) :
    x * y = 0 := by
  have : NeZero (p ^ r) := ⟨pow_ne_zero r hp.ne_zero⟩
  have hdx : p ^ s ∣ x.val := by
    rw [← ZMod.natCast_eq_zero_iff]
    have h1 : ZMod.castHom (pow_dvd_pow p (by omega : s ≤ r)) (ZMod (p ^ s))
        (x.val : ZMod (p ^ r)) = (x.val : ZMod (p ^ s)) := map_natCast _ _
    rw [← h1, ZMod.natCast_zmod_val, hx]
  have hdy : p ^ t ∣ y.val := by
    rw [← ZMod.natCast_eq_zero_iff]
    have h1 : ZMod.castHom (pow_dvd_pow p (by omega : t ≤ r)) (ZMod (p ^ t))
        (y.val : ZMod (p ^ r)) = (y.val : ZMod (p ^ t)) := map_natCast _ _
    rw [← h1, ZMod.natCast_zmod_val, hy]
  rw [← ZMod.natCast_zmod_val x, ← ZMod.natCast_zmod_val y, ← Nat.cast_mul,
    ZMod.natCast_eq_zero_iff]
  have hmul : p ^ s * p ^ t ∣ x.val * y.val := mul_dvd_mul hdx hdy
  rwa [← pow_add, hst] at hmul

private lemma I_alt_split {p r t v : ℕ} (hp : p.Prime) (ht : 1 ≤ t) :
    I_alt p r (t + 1) v = ∑ j ∈ Finset.range p, I_alt p r t (v * p + j) := by
  simp only [I_alt]
  rw [Finset.sum_sigma']
  refine Finset.sum_bij (fun w _ => ⟨w / p ^ t, w % p ^ t⟩) ?_ ?_ ?_ ?_
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_sigma] at hw ⊢
    have hpt : 0 < p ^ t := pow_pos hp.pos t
    refine ⟨Nat.div_lt_of_lt_mul (by rw [pow_succ'] at hw; linarith),
      Nat.mod_lt w hpt, fun hd => hw.2 ?_⟩
    have h1 : p ∣ p ^ t * (w / p ^ t) := dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) _
    have h2 := Nat.div_add_mod w (p ^ t)
    exact h2 ▸ dvd_add h1 hd
  · intro w1 _ w2 _ heq
    have h1 : w1 / p ^ t = w2 / p ^ t := congrArg Sigma.fst heq
    have h2 : w1 % p ^ t = w2 % p ^ t := congrArg Sigma.snd heq
    rw [← Nat.div_add_mod w1 (p ^ t), ← Nat.div_add_mod w2 (p ^ t), h1, h2]
  · intro ⟨j, rem⟩ hjr
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter] at hjr
    have hpt : 0 < p ^ t := pow_pos hp.pos t
    refine ⟨j * p ^ t + rem, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨?_, fun hd => hjr.2.2 ?_⟩
      · rw [pow_succ']
        have : (j + 1) * p ^ t ≤ p * p ^ t := Nat.mul_le_mul_right _ hjr.1
        nlinarith
      · have hp1 : p ∣ j * p ^ t := dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) j
        exact (Nat.dvd_add_right hp1).mp hd
    · apply Sigma.ext
      · dsimp only
        rw [mul_comm j (p ^ t), Nat.mul_add_div hpt, Nat.div_eq_of_lt hjr.2.1, add_zero]
      · refine heq_of_eq ?_
        dsimp only
        rw [mul_comm j (p ^ t), Nat.mul_add_mod, Nat.mod_eq_of_lt hjr.2.1]
  · intro w _
    have h1 := Nat.div_add_mod w (p ^ t)
    have h2 : v * p ^ (t + 1) + w = (v * p + w / p ^ t) * p ^ t + w % p ^ t := by
      rw [pow_succ]; nlinarith
    rw [h2]

/-- Per-p^r-block vanishing in ZMod (p^r) via downward telescoping. -/
private lemma nonmul_block_zmod_zero {p M r Q : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hMr : p ^ r ∣ M) (hr : 1 ≤ r) (hQM : (Q + 1) * p ^ r ≤ M) :
    ∑ u ∈ (Finset.range (p ^ r)).filter (fun u => ¬ p ∣ u),
      ((gFun M (Q * p ^ r + u - 1) : ZMod (p ^ r)) *
        ((-1 : ZMod (p ^ r)) ^ (Q * p ^ r + u - 1) *
          (((Q * p ^ r + u : ℕ) : ZMod (p ^ r))⁻¹) ^ 2)) = 0 := by
  let S : ℕ → ZMod (p ^ r) := fun t =>
    ∑ v ∈ Finset.range (p ^ (r - t)),
      (gFun M (Q * p ^ r + v * p ^ t) : ZMod (p ^ r)) *
        I_alt p r t (Q * p ^ (r - t) + v)
  -- Step 1: LHS = S 1
  have hS1 : ∑ u ∈ (Finset.range (p ^ r)).filter (fun u => ¬ p ∣ u),
      ((gFun M (Q * p ^ r + u - 1) : ZMod (p ^ r)) *
        ((-1 : ZMod (p ^ r)) ^ (Q * p ^ r + u - 1) *
          (((Q * p ^ r + u : ℕ) : ZMod (p ^ r))⁻¹) ^ 2)) = S 1 := by
    simp only [S, I_alt, Finset.mul_sum, Finset.sum_sigma']
    refine Finset.sum_bij (fun u _ => ⟨u / p, u % p⟩) ?_ ?_ ?_ ?_
    · intro u hu
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_sigma] at hu ⊢
      refine ⟨Nat.div_lt_of_lt_mul ?_, ?_, fun hd => hu.2 ?_⟩
      · rw [← pow_succ', show r - 1 + 1 = r by omega]; exact hu.1
      · rw [pow_one]; exact Nat.mod_lt u hp.pos
      · have h1 := Nat.div_add_mod u p
        exact h1 ▸ dvd_add (dvd_mul_right p _) hd
    · intro u1 _ u2 _ heq
      have h1 : u1 / p = u2 / p := congrArg Sigma.fst heq
      have h2 : u1 % p = u2 % p := congrArg Sigma.snd heq
      rw [← Nat.div_add_mod u1 p, ← Nat.div_add_mod u2 p, h1, h2]
    · intro ⟨v, w⟩ hvw
      simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter] at hvw
      rw [pow_one] at hvw
      refine ⟨v * p + w, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨?_, fun hd => hvw.2.2 ((Nat.dvd_add_right (dvd_mul_left p v)).mp hd)⟩
        have h1 : (v + 1) * p ≤ p ^ (r - 1) * p := Nat.mul_le_mul_right p hvw.1
        rw [← pow_succ, show r - 1 + 1 = r by omega] at h1
        nlinarith
      · apply Sigma.ext
        · dsimp only
          rw [mul_comm v p, Nat.mul_add_div hp.pos, Nat.div_eq_of_lt hvw.2.1, add_zero]
        · refine heq_of_eq ?_
          dsimp only
          rw [mul_comm v p, Nat.mul_add_mod, Nat.mod_eq_of_lt hvw.2.1]
    · intro u hu
      simp only [Finset.mem_filter, Finset.mem_range] at hu
      have hu1 : 1 ≤ u := Nat.pos_of_ne_zero (fun h => hu.2 (h ▸ dvd_zero p))
      have hmod1 : 1 ≤ u % p := Nat.pos_of_ne_zero (fun h => hu.2 (Nat.dvd_of_mod_eq_zero h))
      have hmodlt : u % p < p := Nat.mod_lt u hp.pos
      have hdiv := Nat.div_add_mod u p
      have hidx_eq : Q * p ^ r + u = (Q * p ^ (r - 1) + u / p) * p ^ 1 + u % p := by
        rw [pow_one, add_mul, mul_assoc, ← pow_succ, show r - 1 + 1 = r by omega]
        linarith
      have hg_eq : (gFun M (Q * p ^ r + u - 1) : ZMod (p ^ r)) =
          (gFun M (Q * p ^ r + (u / p) * p ^ 1) : ZMod (p ^ r)) := by
        have hpr_eq : Q * p ^ (r - 1) * p = Q * p ^ r := by
          rw [mul_assoc, ← pow_succ, show r - 1 + 1 = r by omega]
        have hblk := gFun_block_cong (p := p) (M := M) (r := r) (t := 1)
          (v := Q * p ^ (r - 1) + u / p)
          (q1 := Q * p ^ r + (u / p) * p ^ 1) (q2 := Q * p ^ r + u - 1)
          hp hMr le_rfl hr
          (by rw [pow_one, add_mul, hpr_eq])
          (by
            rw [pow_one]
            have hlt : u / p * p < u := by rw [mul_comm]; omega
            omega)
          (by
            rw [pow_one, add_mul, add_mul, hpr_eq]
            have h1 : Q * p ^ r + u / p * p + 1 * p = Q * p ^ r + p * (u / p) + p := by ring
            omega)
          (by
            have h1 : Q * p ^ r + p ^ r = (Q + 1) * p ^ r := by ring
            have h2 : (Q * p ^ (r - 1) + u / p + 1) * p ^ 1 ≤ (Q + 1) * p ^ r := by
              rw [pow_one, add_mul, add_mul, hpr_eq]
              have h3 : u / p * p + 1 * p ≤ p ^ r := by
                have h4 : u / p * p = p * (u / p) := mul_comm _ _
                have h5 : p * (u / p) + p ≤ p ^ r := by
                  have hdivlt : u / p < p ^ (r - 1) := by
                    refine Nat.div_lt_of_lt_mul ?_
                    rw [← pow_succ', show r - 1 + 1 = r by omega]; exact hu.1
                  have hmul : (u / p + 1) * p ≤ p ^ (r - 1) * p := Nat.mul_le_mul_right p hdivlt
                  rw [← pow_succ, show r - 1 + 1 = r by omega] at hmul
                  linarith
                omega
              linarith
            omega)
        rw [show r + 1 - 1 = r by omega] at hblk
        exact hblk.symm
      rw [hg_eq, hidx_eq]
  -- Step 2: S t = S (t + 1) for 1 ≤ t < r
  have hstep : ∀ t, 1 ≤ t → t < r → S t = S (t + 1) := by
    intro t ht1 htr
    have hsplit : S (t + 1) = ∑ v ∈ Finset.range (p ^ (r - t)),
        (gFun M (Q * p ^ r + (v / p) * p ^ (t + 1)) : ZMod (p ^ r)) *
          I_alt p r t (Q * p ^ (r - t) + v) := by
      simp only [S]
      have h1 : ∀ w ∈ Finset.range (p ^ (r - (t + 1))),
          (gFun M (Q * p ^ r + w * p ^ (t + 1)) : ZMod (p ^ r)) *
            I_alt p r (t + 1) (Q * p ^ (r - (t + 1)) + w) =
          ∑ j ∈ Finset.range p,
            (gFun M (Q * p ^ r + w * p ^ (t + 1)) : ZMod (p ^ r)) *
              I_alt p r t ((Q * p ^ (r - (t + 1)) + w) * p + j) := by
        intro w _
        rw [I_alt_split hp ht1, Finset.mul_sum]
      rw [Finset.sum_congr rfl h1, Finset.sum_sigma']
      symm
      refine Finset.sum_bij (fun v _ => ⟨v / p, v % p⟩) ?_ ?_ ?_ ?_
      · intro v hv
        simp only [Finset.mem_range, Finset.mem_sigma] at hv ⊢
        refine ⟨Nat.div_lt_of_lt_mul ?_, Nat.mod_lt v hp.pos⟩
        rw [← pow_succ', show r - (t + 1) + 1 = r - t by omega]; exact hv
      · intro v1 _ v2 _ heq
        have h1 : v1 / p = v2 / p := congrArg Sigma.fst heq
        have h2 : v1 % p = v2 % p := congrArg Sigma.snd heq
        rw [← Nat.div_add_mod v1 p, ← Nat.div_add_mod v2 p, h1, h2]
      · intro ⟨w, j⟩ hwj
        simp only [Finset.mem_sigma, Finset.mem_range] at hwj
        refine ⟨w * p + j, ?_, ?_⟩
        · rw [Finset.mem_range]
          have h1 : (w + 1) * p ≤ p ^ (r - (t + 1)) * p := Nat.mul_le_mul_right p hwj.1
          rw [← pow_succ, show r - (t + 1) + 1 = r - t by omega] at h1
          nlinarith
        · apply Sigma.ext
          · dsimp only
            rw [mul_comm w p, Nat.mul_add_div hp.pos, Nat.div_eq_of_lt hwj.2, add_zero]
          · refine heq_of_eq ?_
            dsimp only
            rw [mul_comm w p, Nat.mul_add_mod, Nat.mod_eq_of_lt hwj.2]
      · intro v _
        congr 2
        have hdiv := Nat.div_add_mod v p
        rw [add_mul, mul_assoc, ← pow_succ, show r - (t + 1) + 1 = r - t by omega]
        linarith
    rw [hsplit]
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
    refine Finset.sum_eq_zero fun v hv => ?_
    rw [Finset.mem_range] at hv
    rw [← sub_mul]
    refine mul_zero_of_proj_eq_zero hp (s := r - t) (t := t) (by omega) _ _ ?_
      (proj_I_alt_eq_zero hp h5 ht1 (by omega))
    -- Show castHom (gFun(Q*p^r + v*p^t) - gFun(Q*p^r + (v/p)*p^(t+1))) = 0 in ZMod (p^(r-t))
    rw [map_sub, map_intCast, map_intCast, sub_eq_zero]
    have hpr_eq : Q * p ^ (r - (t + 1)) * p ^ (t + 1) = Q * p ^ r := by
      rw [mul_assoc, ← pow_add, show r - (t + 1) + (t + 1) = r by omega]
    have hblk := gFun_block_cong (p := p) (M := M) (r := r) (t := t + 1)
      (v := Q * p ^ (r - (t + 1)) + v / p)
      (q1 := Q * p ^ r + (v / p) * p ^ (t + 1))
      (q2 := Q * p ^ r + v * p ^ t)
      hp hMr (by omega) (by omega)
      (by rw [add_mul, hpr_eq])
      (by
        have hdiv := Nat.div_add_mod v p
        have hle : (v / p) * p ≤ v := by rw [mul_comm]; omega
        have hmul := Nat.mul_le_mul_right (p ^ t) hle
        rw [mul_assoc, ← pow_succ'] at hmul
        omega)
      (by
        have hdiv := Nat.div_add_mod v p
        have hmod : v % p < p := Nat.mod_lt v hp.pos
        have hpt : 0 < p ^ t := pow_pos hp.pos t
        have h1 : v < (v / p + 1) * p := by nlinarith
        have h2 : v * p ^ t < (v / p + 1) * p ^ (t + 1) := by
          have := Nat.mul_lt_mul_of_pos_right h1 hpt
          rwa [mul_assoc, ← pow_succ'] at this
        rw [add_mul, add_mul, hpr_eq]
        linarith)
      (by
        have hdivlt : v / p < p ^ (r - (t + 1)) := by
          refine Nat.div_lt_of_lt_mul ?_
          rw [← pow_succ', show r - (t + 1) + 1 = r - t by omega]; exact hv
        have h1 : (v / p + 1) * p ^ (t + 1) ≤ p ^ (r - (t + 1)) * p ^ (t + 1) :=
          Nat.mul_le_mul_right _ hdivlt
        rw [← pow_add, show r - (t + 1) + (t + 1) = r by omega] at h1
        have h2 : (Q * p ^ (r - (t + 1)) + v / p + 1) * p ^ (t + 1) =
            Q * p ^ r + (v / p + 1) * p ^ (t + 1) := by
          rw [show Q * p ^ (r - (t + 1)) + v / p + 1 = Q * p ^ (r - (t + 1)) + (v / p + 1) by omega,
            add_mul, hpr_eq]
        have h3 : Q * p ^ r + p ^ r = (Q + 1) * p ^ r := by ring
        omega)
    rw [show r + 1 - (t + 1) = r - t by omega] at hblk
    exact hblk.symm
  -- Step 3: S r = 0
  have hSr : S r = 0 := by
    simp only [S, Nat.sub_self, pow_zero, Finset.range_one, Finset.sum_singleton, zero_mul, add_zero, mul_one]
    have h0 := proj_I_alt_eq_zero (p := p) (r := r) (t := r) (v := Q) hp h5 hr le_rfl
    have : NeZero (p ^ r) := ⟨pow_ne_zero r hp.ne_zero⟩
    have hid : ZMod.castHom (pow_dvd_pow p (le_rfl : r ≤ r)) (ZMod (p ^ r)) (I_alt p r r Q) = I_alt p r r Q := by
      conv_lhs => rw [← ZMod.natCast_zmod_val (I_alt p r r Q)]
      rw [map_natCast, ZMod.natCast_zmod_val]
    rw [hid] at h0
    rw [h0, mul_zero]
  -- Combine: S 1 = S r = 0
  have hchain : ∀ k, k ≤ r - 1 → S 1 = S (1 + k) := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      rw [ih (by omega), show 1 + (k + 1) = (1 + k) + 1 by omega]
      exact hstep (1 + k) (by omega) (by omega)
  rw [hS1, hchain (r - 1) le_rfl, show 1 + (r - 1) = r by omega, hSr]

/-- Non-multiple sum is divisible by p^(3*r). -/
private lemma nonmul_sum_dvd {p n r : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (_hn : 0 < n) (hr : 0 < r) :
    p ^ (3 * r) ∣ ∑ k ∈ (Finset.range (n * p ^ r + 1)).filter (fun k => ¬ p ∣ k),
      (n * p ^ r).choose k * (n * p ^ r + k - 1).choose k := by
  set M := n * p ^ r
  have hMr : p ^ r ∣ M := dvd_mul_left (p ^ r) n
  -- Exclude k = M since p ∣ M
  have hfilt : (Finset.range (M + 1)).filter (fun k => ¬ p ∣ k) =
      (Finset.range M).filter (fun k => ¬ p ∣ k) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hlt, hnd⟩
      refine ⟨?_, hnd⟩
      have hne : k ≠ M := fun h => hnd (h ▸ dvd_trans (dvd_pow_self p (by omega)) hMr)
      omega
    · rintro ⟨hlt, hnd⟩; exact ⟨by omega, hnd⟩
  rw [hfilt]
  -- Split range (n * p^r) into n blocks of length p^r
  have hsplit : ∑ k ∈ (Finset.range M).filter (fun k => ¬ p ∣ k),
        M.choose k * (M + k - 1).choose k =
      ∑ Q ∈ Finset.range n,
        ∑ u ∈ (Finset.range (p ^ r)).filter (fun u => ¬ p ∣ u),
          M.choose (Q * p ^ r + u) * (M + (Q * p ^ r + u) - 1).choose (Q * p ^ r + u) := by
    rw [Finset.sum_sigma']
    refine Finset.sum_bij (fun k _ => ⟨k / p ^ r, k % p ^ r⟩) ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_sigma] at hk ⊢
      have hpr : 0 < p ^ r := pow_pos hp.pos r
      refine ⟨Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hk.1),
        Nat.mod_lt k hpr, fun hd => hk.2 ?_⟩
      have h1 : p ∣ p ^ r * (k / p ^ r) := dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) _
      have h2 := Nat.div_add_mod k (p ^ r)
      exact h2 ▸ dvd_add h1 hd
    · intro k1 _ k2 _ heq
      have h1 : k1 / p ^ r = k2 / p ^ r := congrArg Sigma.fst heq
      have h2 : k1 % p ^ r = k2 % p ^ r := congrArg Sigma.snd heq
      rw [← Nat.div_add_mod k1 (p ^ r), ← Nat.div_add_mod k2 (p ^ r), h1, h2]
    · intro ⟨Q, u⟩ hQu
      simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter] at hQu
      have hpr : 0 < p ^ r := pow_pos hp.pos r
      refine ⟨Q * p ^ r + u, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨?_, fun hd => hQu.2.2 ?_⟩
        · have h1 : (Q + 1) * p ^ r ≤ M := Nat.mul_le_mul_right _ hQu.1
          have h2 : Q * p ^ r + p ^ r = (Q + 1) * p ^ r := by ring
          omega
        · have hp1 : p ∣ Q * p ^ r := dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) Q
          exact (Nat.dvd_add_right hp1).mp hd
      · apply Sigma.ext
        · dsimp only
          rw [mul_comm Q (p ^ r), Nat.mul_add_div hpr, Nat.div_eq_of_lt hQu.2.1, add_zero]
        · refine heq_of_eq ?_
          dsimp only
          rw [mul_comm Q (p ^ r), Nat.mul_add_mod, Nat.mod_eq_of_lt hQu.2.1]
    · intro k _
      have hdiv := Nat.div_add_mod k (p ^ r)
      rw [mul_comm (k / p ^ r), hdiv]
  rw [hsplit]
  refine Finset.dvd_sum fun Q hQ => ?_
  rw [Finset.mem_range] at hQ
  have hQM : (Q + 1) * p ^ r ≤ M := Nat.mul_le_mul_right _ hQ
  -- Work in ℤ: p^(2*r) ∣ M^2, so write T_M(k) = p^(2*r) * q(k)
  -- First show p^(2*r) ∣ M.choose k * (M + k - 1).choose k for every k with ¬ p ∣ k
  have hterm_dvd : ∀ u ∈ (Finset.range (p ^ r)).filter (fun u => ¬ p ∣ u),
      p ^ (2 * r) ∣ M.choose (Q * p ^ r + u) * (M + (Q * p ^ r + u) - 1).choose (Q * p ^ r + u) := by
    intro u hu
    simp only [Finset.mem_filter, Finset.mem_range] at hu
    set k := Q * p ^ r + u
    have hu1 : 1 ≤ u := Nat.pos_of_ne_zero (fun h => hu.2 (h ▸ dvd_zero p))
    have hk1 : 1 ≤ k := by omega
    have hkM : k ≤ M := by
      have h2 : Q * p ^ r + p ^ r = (Q + 1) * p ^ r := by ring
      omega
    have hnd_k : ¬ p ∣ k := fun hd => hu.2 <| by
      have hp1 : p ∣ Q * p ^ r := dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) Q
      exact (Nat.dvd_add_right hp1).mp hd
    have heq := term_mul_sq_eq hk1 hkM
    have hM2 : ((p ^ (2 * r) : ℕ) : ℤ) ∣ ((k : ℤ) ^ 2) * ((M.choose k * (M + k - 1).choose k : ℕ) : ℤ) := by
      rw [heq]
      have h1 : p ^ (2 * r) ∣ M ^ 2 := by
        rw [mul_comm, pow_mul]; exact pow_dvd_pow_of_dvd hMr 2
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr h1) _) _
    have hnd_k2 : ¬ (p : ℤ) ∣ ((k : ℤ) ^ 2) := by
      intro hd
      have hp_int : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
      exact hnd_k (Int.natCast_dvd_natCast.mp (hp_int.dvd_of_dvd_pow hd))
    exact Int.natCast_dvd_natCast.mp (int_dvd_of_coprime_mul hp hnd_k2 hM2)
  -- Express sum as p^(2*r) * ∑ (T_M(k) / p^(2*r)), then show inner sum is 0 in ZMod (p^r)
  have hdiv_sum : ∑ u ∈ (Finset.range (p ^ r)).filter (fun u => ¬ p ∣ u),
        M.choose (Q * p ^ r + u) * (M + (Q * p ^ r + u) - 1).choose (Q * p ^ r + u) =
      p ^ (2 * r) * ∑ u ∈ (Finset.range (p ^ r)).filter (fun u => ¬ p ∣ u),
        (M.choose (Q * p ^ r + u) * (M + (Q * p ^ r + u) - 1).choose (Q * p ^ r + u)) / p ^ (2 * r) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u hu => (Nat.mul_div_cancel' (hterm_dvd u hu)).symm
  rw [hdiv_sum, show 3 * r = 2 * r + r by omega, pow_add]
  refine mul_dvd_mul_left (p ^ (2 * r)) ?_
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sum]
  -- Show each term equals n^2 * gFun(k-1) * (-1)^(k-1) * (k⁻¹)^2 in ZMod (p^r)
  have hterm_zmod : ∀ u ∈ (Finset.range (p ^ r)).filter (fun u => ¬ p ∣ u),
      (((M.choose (Q * p ^ r + u) * (M + (Q * p ^ r + u) - 1).choose (Q * p ^ r + u)) / p ^ (2 * r) : ℕ) :
        ZMod (p ^ r)) =
      ((n : ZMod (p ^ r)) ^ 2) *
        ((gFun M (Q * p ^ r + u - 1) : ZMod (p ^ r)) *
          ((-1 : ZMod (p ^ r)) ^ (Q * p ^ r + u - 1) *
            (((Q * p ^ r + u : ℕ) : ZMod (p ^ r))⁻¹) ^ 2)) := by
    intro u hu
    simp only [Finset.mem_filter, Finset.mem_range] at hu
    set k := Q * p ^ r + u
    have hu1 : 1 ≤ u := Nat.pos_of_ne_zero (fun h => hu.2 (h ▸ dvd_zero p))
    have hk1 : 1 ≤ k := by omega
    have hkM : k ≤ M := by
      have h2 : Q * p ^ r + p ^ r = (Q + 1) * p ^ r := by ring
      omega
    have hnd_k : ¬ p ∣ k := fun hd => hu.2 <| by
      have hp1 : p ∣ Q * p ^ r := dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) Q
      exact (Nat.dvd_add_right hp1).mp hd
    set q := (M.choose k * (M + k - 1).choose k) / p ^ (2 * r)
    have hq_mul : p ^ (2 * r) * q = M.choose k * (M + k - 1).choose k :=
      Nat.mul_div_cancel' (hterm_dvd u (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hu.1, hu.2⟩))
    have heq := term_mul_sq_eq hk1 hkM
    have hM2_eq : (M : ℤ) ^ 2 = ((p ^ (2 * r) : ℕ) : ℤ) * (n : ℤ) ^ 2 := by
      have : M ^ 2 = p ^ (2 * r) * n ^ 2 := by
        simp only [M, mul_pow, ← pow_mul, mul_comm r 2]; ring
      exact_mod_cast this
    have hq_int : ((k : ℤ) ^ 2) * (q : ℤ) = (n : ℤ) ^ 2 * (-1 : ℤ) ^ (k - 1) * gFun M (k - 1) := by
      have hpne : ((p ^ (2 * r) : ℕ) : ℤ) ≠ 0 := by positivity
      apply mul_left_cancel₀ hpne
      have h1 : ((p ^ (2 * r) : ℕ) : ℤ) * (((k : ℤ) ^ 2) * (q : ℤ)) =
          ((k : ℤ) ^ 2) * ((M.choose k * (M + k - 1).choose k : ℕ) : ℤ) := by
        rw [← hq_mul]; push_cast; ring
      rw [h1, heq, hM2_eq]; ring
    have hq_zmod : ((k : ZMod (p ^ r)) ^ 2) * (q : ZMod (p ^ r)) =
        ((n : ZMod (p ^ r)) ^ 2) * (-1 : ZMod (p ^ r)) ^ (k - 1) * (gFun M (k - 1) : ZMod (p ^ r)) := by
      have h := congrArg (Int.cast (R := ZMod (p ^ r))) hq_int
      simpa using h
    have hu_k : IsUnit (k : ZMod (p ^ r)) := isUnit_zmod_pow hp hnd_k
    have hu_k2 : IsUnit ((k : ZMod (p ^ r)) ^ 2) := hu_k.pow 2
    apply hu_k2.mul_left_cancel
    rw [hq_zmod]
    have hkinv : (k : ZMod (p ^ r)) ^ 2 * (((k : ZMod (p ^ r))⁻¹) ^ 2) = 1 := by
      rw [← mul_pow, ZMod.mul_inv_of_unit _ hu_k, one_pow]
    calc ((n : ZMod (p ^ r)) ^ 2) * (-1 : ZMod (p ^ r)) ^ (k - 1) * (gFun M (k - 1) : ZMod (p ^ r))
        = ((n : ZMod (p ^ r)) ^ 2) * (-1 : ZMod (p ^ r)) ^ (k - 1) * (gFun M (k - 1) : ZMod (p ^ r)) *
            ((k : ZMod (p ^ r)) ^ 2 * (((k : ZMod (p ^ r))⁻¹) ^ 2)) := by rw [hkinv, mul_one]
      _ = ((k : ZMod (p ^ r)) ^ 2) *
            (((n : ZMod (p ^ r)) ^ 2) *
              ((gFun M (k - 1) : ZMod (p ^ r)) *
                ((-1 : ZMod (p ^ r)) ^ (k - 1) * (((k : ZMod (p ^ r))⁻¹) ^ 2)))) := by ring
  rw [Finset.sum_congr rfl hterm_zmod, ← Finset.mul_sum,
    nonmul_block_zmod_zero hp h5 hMr hr hQM, mul_zero]

/-! ### Part 4: Main theorem -/

theorem main_proof :
    ∀ p n k : ℕ, p.Prime → 5 ≤ p → 0 < n → 0 < k →
      a_seq (n * p ^ k) ≡ a_seq (n * p ^ (k - 1)) [MOD p ^ (3 * k)] := by
  intro p n r hp h5 hn hr
  set M := n * p ^ r
  set N := n * p ^ (r - 1)
  have hMp : M = p * N := mul_pow_eq_mul_pred p n r hr
  rw [← ZMod.natCast_eq_natCast_iff, ← sub_eq_zero]
  have hsplit : a_seq M =
      (∑ j ∈ Finset.range (N + 1), M.choose (p * j) * (M + p * j - 1).choose (p * j)) +
      (∑ k ∈ (Finset.range (M + 1)).filter (fun k => ¬ p ∣ k), M.choose k * (M + k - 1).choose k) := by
    simp only [a_seq, OMA.S_oeis_a123164.a]
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (M + 1)) (fun k => p ∣ k)]
    congr 1
    refine Finset.sum_bij (fun k _ => k / p) ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
      rcases hk.2 with ⟨j, rfl⟩
      rw [Nat.mul_div_cancel_left j hp.pos]
      rw [hMp] at hk; nlinarith [hp.pos]
    · intro k1 hk1 k2 hk2 heq
      simp only [Finset.mem_filter] at hk1 hk2
      rw [← Nat.mul_div_cancel' hk1.2, ← Nat.mul_div_cancel' hk2.2, heq]
    · intro j hj
      rw [Finset.mem_range] at hj
      refine ⟨p * j, ?_, Nat.mul_div_cancel_left j hp.pos⟩
      simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨?_, dvd_mul_right p j⟩
      rw [hMp]; nlinarith [hp.pos]
    · intro k hk
      simp only [Finset.mem_filter] at hk
      rw [Nat.mul_div_cancel' hk.2]
  have hdvd_int : ((p ^ (3 * r) : ℕ) : ℤ) ∣ (a_seq M : ℤ) - (a_seq N : ℤ) := by
    rw [hsplit]
    have hdiff : (((∑ j ∈ Finset.range (N + 1), M.choose (p * j) * (M + p * j - 1).choose (p * j)) +
          (∑ k ∈ (Finset.range (M + 1)).filter (fun k => ¬ p ∣ k), M.choose k * (M + k - 1).choose k) : ℕ) : ℤ) -
        (a_seq N : ℤ) =
      (∑ j ∈ Finset.range (N + 1),
        (((M.choose (p * j) * (M + p * j - 1).choose (p * j) : ℕ) : ℤ) -
         ((N.choose j * (N + j - 1).choose j : ℕ) : ℤ))) +
      ((∑ k ∈ (Finset.range (M + 1)).filter (fun k => ¬ p ∣ k), M.choose k * (M + k - 1).choose k : ℕ) : ℤ) := by
      simp only [a_seq, OMA.S_oeis_a123164.a, Nat.cast_add, Nat.cast_sum, Finset.sum_sub_distrib]; ring
    rw [hdiff]
    refine dvd_add ?_ (Int.natCast_dvd_natCast.mpr (nonmul_sum_dvd hp h5 hn hr))
    refine Finset.dvd_sum fun j hj => ?_
    rw [Finset.mem_range] at hj
    exact mul_term_diff_dvd hp h5 hn hr (by omega)
  have hz : (((a_seq M : ℤ) - (a_seq N : ℤ) : ℤ) : ZMod (p ^ (3 * r))) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd_int
  simpa using hz


end OMA_A123164

theorem OMA.solution : type_of% @OMA.S_oeis_a123164.main := OMA_A123164.main_proof
