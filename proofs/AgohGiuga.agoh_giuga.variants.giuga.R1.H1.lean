import OMAReductions.R_AgohGiuga_agoh_giuga_variants_giuga_R1
import Mathlib.Tactic

/-!
# Proofs of AgohGiuga H2 and H1

For any strong Giuga number `n`:
- `prove_AgohGiuga_H2`: every prime factor `p` of `n` satisfies `p ∣ (n / p - 1)`.
- `prove_AgohGiuga_H1`: `n` is a Carmichael number.
-/

open AgohGiuga BigOperators

private lemma sum_Ioo_zero_eq_sum_range {p : ℕ} (f : ℕ → ZMod p) (hf0 : f 0 = 0) (n : ℕ) :
    ∑ i ∈ Finset.Ioo 0 n, f i = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases hn : n = 0
    · subst hn
      have h01 : Finset.Ioo 0 1 = ∅ := by
        ext x
        simp only [Finset.mem_Ioo, Finset.notMem_empty, iff_false]
        omega
      simp [h01, hf0]
    · have hIoo : Finset.Ioo 0 (n + 1) = insert n (Finset.Ioo 0 n) := by
        ext x
        simp only [Finset.mem_Ioo, Finset.mem_insert]
        omega
      have hnotin : n ∉ Finset.Ioo 0 n := by simp
      rw [hIoo, Finset.sum_insert hnotin, Finset.sum_range_succ, ih, add_comm]

private lemma sum_range_add_eq {α : Type*} [AddCommMonoid α] (f : ℕ → α) (a b : ℕ) :
    ∑ x ∈ Finset.range (a + b), f x =
      ∑ x ∈ Finset.range a, f x + ∑ x ∈ Finset.range b, f (a + x) := by
  induction b with
  | zero => simp
  | succ b ih => rw [Nat.add_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ, add_assoc]

private lemma sum_range_mul_zmod_pow (p k q : ℕ) :
    ∑ i ∈ Finset.range (q * p), (i : ZMod p) ^ k =
      (q : ZMod p) * ∑ r ∈ Finset.range p, (r : ZMod p) ^ k := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.succ_mul, sum_range_add_eq, ih]
    have hshift : ∑ r ∈ Finset.range p, ((q * p + r : ℕ) : ZMod p) ^ k =
        ∑ r ∈ Finset.range p, (r : ZMod p) ^ k := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add]
    rw [hshift, Nat.cast_add, Nat.cast_one]
    ring

private lemma strongGiuga_prime_props {n p : ℕ} (hn : IsStrongGiuga n) (hp : p.Prime)
    (hpn : p ∣ n) : (p - 1) ∣ (n - 1) ∧ p ∣ (n / p - 1) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hcomp, hdvd_n⟩ := hn
  have hn1 : 1 < n := hcomp.1
  have hk_pos : 0 < n - 1 := by omega
  have hp_dvd_sum : p ∣ 1 + ∑ i ∈ Finset.Ioo 0 n, i ^ (n - 1) := dvd_trans hpn hdvd_n
  have hzmod_zero : ((1 + ∑ i ∈ Finset.Ioo 0 n, i ^ (n - 1) : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hp_dvd_sum
  push_cast at hzmod_zero
  have hf0 : ((0 : ℕ) : ZMod p) ^ (n - 1) = 0 := by
    rw [Nat.cast_zero]
    exact zero_pow (by omega)
  rw [sum_Ioo_zero_eq_sum_range (fun i => (i : ZMod p) ^ (n - 1)) hf0 n] at hzmod_zero
  let q : ℕ := n / p
  have hqp : q * p = n := Nat.div_mul_cancel hpn
  have hrange_qp := sum_range_mul_zmod_pow p (n - 1) q
  rw [hqp] at hrange_qp
  rw [hrange_qp] at hzmod_zero
  have hinj : Set.InjOn (fun r : ℕ => (r : ZMod p)) (Finset.range p) := by
    intro r1 hr1 r2 hr2 heq
    dsimp only at heq
    simp only [Finset.coe_range, Set.mem_Iio] at hr1 hr2
    rcases le_total r1 r2 with hle | hle
    · have hsub : ((r2 - r1 : ℕ) : ZMod p) = 0 := by
        rw [Nat.cast_sub hle, heq, sub_self]
      obtain ⟨c, hc⟩ := (ZMod.natCast_eq_zero_iff _ _).mp hsub
      rcases eq_or_ne c 0 with rfl | hc0
      · omega
      · have hge : p ≤ p * c := Nat.le_mul_of_pos_right p (Nat.pos_of_ne_zero hc0)
        omega
    · have hsub : ((r1 - r2 : ℕ) : ZMod p) = 0 := by
        rw [Nat.cast_sub hle, heq, sub_self]
      obtain ⟨c, hc⟩ := (ZMod.natCast_eq_zero_iff _ _).mp hsub
      rcases eq_or_ne c 0 with rfl | hc0
      · omega
      · have hge : p ≤ p * c := Nat.le_mul_of_pos_right p (Nat.pos_of_ne_zero hc0)
        omega
  have himg : (Finset.range p).image (fun r : ℕ => (r : ZMod p)) = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_image_of_injOn hinj, Finset.card_range, Finset.card_univ, ZMod.card]
  let S : ZMod p := ∑ x : ZMod p, x ^ (n - 1)
  have hsum_eq_S : ∑ r ∈ Finset.range p, (r : ZMod p) ^ (n - 1) = S := by
    dsimp [S]
    rw [← himg, Finset.sum_image hinj]
  rw [hsum_eq_S] at hzmod_zero
  have hS_ne : S ≠ 0 := by
    intro hS0
    rw [hS0, mul_zero, add_zero] at hzmod_zero
    exact one_ne_zero hzmod_zero
  have hu_pow : ∀ u : (ZMod p)ˣ, (u : ZMod p) ^ (n - 1) = 1 := by
    intro u
    have hinj_u : Function.Injective (fun x : ZMod p => (u : ZMod p) * x) :=
      mul_right_injective₀ u.ne_zero
    have himg_u : Finset.univ.image (fun x : ZMod p => (u : ZMod p) * x) = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      rw [Finset.card_image_of_injective _ hinj_u]
    have hS_mul : (u : ZMod p) ^ (n - 1) * S = S := by
      dsimp [S]
      conv_rhs => rw [← himg_u]
      rw [Finset.sum_image (fun x _ y _ h => hinj_u h), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [mul_pow]
    have hsub : ((u : ZMod p) ^ (n - 1) - 1) * S = 0 := by
      rw [sub_mul, one_mul, hS_mul, sub_self]
    rcases mul_eq_zero.mp hsub with hu0 | hS0
    · exact sub_eq_zero.mp hu0
    · exact absurd hS0 hS_ne
  have hkorselt : (p - 1) ∣ (n - 1) := by
    let ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
    have hgk : g ^ (n - 1) = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, hu_pow g, Units.val_one]
    have hdvd_ord : orderOf g ∣ (n - 1) := orderOf_dvd_iff_pow_eq_one.mpr hgk
    rw [orderOf_eq_card_of_forall_mem_zpowers hg] at hdvd_ord
    have hcard : Nat.card (ZMod p)ˣ = p - 1 := by simp [Nat.totient_prime hp]
    rwa [hcard] at hdvd_ord
  have h1S : 1 + S = 0 := by
    have hS_erase : S = ∑ x ∈ Finset.univ.erase (0 : ZMod p), (1 : ZMod p) := by
      dsimp [S]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod p)), zero_pow (by omega), zero_add]
      apply Finset.sum_congr rfl
      intro x hx
      have hx0 : x ≠ 0 := Finset.ne_of_mem_erase hx
      obtain ⟨u, rfl⟩ := isUnit_iff_ne_zero.mpr hx0
      exact hu_pow u
    have huniv_one : ∑ _x : ZMod p, (1 : ZMod p) = 0 := by
      rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_one, ZMod.natCast_self]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod p))] at huniv_one
    rwa [hS_erase]
  have hS_neg1 : S = -1 := eq_neg_of_add_eq_zero_right h1S
  rw [hS_neg1] at hzmod_zero
  have hq_sub1 : (q : ZMod p) - 1 = 0 := by linear_combination -hzmod_zero
  have hq_ge1 : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with hq0 | hq_pos
    · rw [hq0, zero_mul] at hqp
      omega
    · exact hq_pos
  have hcast_q : ((q - 1 : ℕ) : ZMod p) = 0 := by
    rw [Nat.cast_sub hq_ge1, Nat.cast_one]
    exact hq_sub1
  exact ⟨hkorselt, (ZMod.natCast_eq_zero_iff _ _).mp hcast_q⟩

theorem prove_AgohGiuga_H2 :
    ∀ n : ℕ, IsStrongGiuga n → ∀ p ∈ n.primeFactors, p ∣ (n / p - 1) := by
  intro n hn p hp_mem
  obtain ⟨hp, hpn, _⟩ := Nat.mem_primeFactors.mp hp_mem
  exact (strongGiuga_prime_props hn hp hpn).2

theorem prove_AgohGiuga_H1 :
    ∀ n : ℕ, IsStrongGiuga n → IsCarmichael n := by
  intro n hn
  rw [AgohGiuga.korselts_criterion n hn.1]
  refine ⟨?_, fun p hp hpn => (strongGiuga_prime_props hn hp hpn).1⟩
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  have : Fact p.Prime := ⟨hp⟩
  have hpn : p ∣ n := dvd_of_mul_left_dvd hpp
  have hgiuga : p ∣ (n / p - 1) := (strongGiuga_prime_props hn hp hpn).2
  have hqp : n / p * p = n := Nat.div_mul_cancel hpn
  obtain ⟨m, hm⟩ := hpp
  have hq_eq : n / p = p * m := by
    apply Nat.eq_of_mul_eq_mul_right hp.pos
    rw [hqp, hm]
    ring
  have hp_dvd_q : p ∣ n / p := ⟨m, hq_eq⟩
  have hcomp1 : 1 < n := hn.1.1
  have hq_ge1 : 1 ≤ n / p := by
    by_contra hlt
    have hq0 : n / p = 0 := by omega
    rw [hq0, zero_mul] at hqp
    omega
  have hz0 : ((n / p : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hp_dvd_q
  have hz1 : ((n / p - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hgiuga
  have hq_split : n / p = (n / p - 1) + 1 := by omega
  rw [hq_split, Nat.cast_add, hz1, zero_add, Nat.cast_one] at hz0
  exact one_ne_zero hz0

theorem OMA.solution : OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R1.H1 :=
  prove_AgohGiuga_H1
