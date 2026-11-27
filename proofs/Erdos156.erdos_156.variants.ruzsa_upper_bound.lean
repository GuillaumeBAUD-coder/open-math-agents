import FormalConjectures.ErdosProblems.«156»
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.NumberTheory.Bertrand
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
Ruzsa (1998) upper bound for the smallest maximal Sidon set in `{1, ..., N}`:
`minMaximalSidonSet N = O((N * log N) ^ (1 / 3))`.

Construction: for a prime `p` around `(1000 * N * log N) ^ (1 / 3)` and `q = p^2 + p + 1`,
take a Singer perfect difference set `B ⊆ ZMod q` of size `p + 1` (constructed from a
hyperplane in `GaloisField p 3`), and lift `B` to `A₀(d) = {b.val + q * d(b) + 1 | b ∈ B}`
with `d : B → Fin K`, `K = N / q`. Every `A₀(d)` is Sidon, and by a first-moment bound over
`d` using `(p - 1) / 12` vertex-disjoint triples `b₁ + b₂ - b₃ ≡ r (mod q)` for each residue
`r`, there exists `d` leaving at most `1` element of `{1, ..., N}` unblocked. Extending
`A₀(d)` to a maximal Sidon set in `{1, ..., N}` gives size at most `p + 2`.

Credit: @kDylanHayes.
-/

open Finset Filter

namespace OMA

/- ### Part 1: Singer perfect difference set modulo `p^2 + p + 1` -/

set_option maxHeartbeats 600000 in
private lemma singer_exists_of_field (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [Fintype K]
    [Algebra (ZMod p) K] (hK_finrank : Module.finrank (ZMod p) K = 3) :
    ∃ B : Finset (ZMod (p ^ 2 + p + 1)),
      B.card = p + 1 ∧
      (∀ a ∈ B, ∀ b ∈ B, ∀ c ∈ B, ∀ d ∈ B,
        a ≠ b → c ≠ d → a - b = c - d → a = c ∧ b = d) ∧
      (∀ x : ZMod (p ^ 2 + p + 1), x ≠ 0 → ∃ a ∈ B, ∃ b ∈ B, a - b = x) := by
  classical
  have hp : p.Prime := Fact.out
  let q : ℕ := p ^ 2 + p + 1
  have hq_pos : 0 < q := by positivity
  have : NeZero q := ⟨hq_pos.ne'⟩
  have hK_card : Fintype.card K = p ^ 3 := by
    have h1 := Module.card_eq_pow_finrank (K := ZMod p) (V := K)
    rw [ZMod.card, hK_finrank] at h1
    exact h1
  have hp_ge2 : 2 ≤ p := hp.two_le
  have hmul_q : (p - 1) * q = p ^ 3 - 1 := by
    dsimp [q]
    zify [show 1 ≤ p by omega, show 1 ≤ p ^ 3 by exact one_le_pow₀ (by omega)]
    ring
  -- Generator `g` of `Kˣ`
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hK_units_card : Fintype.card Kˣ = p ^ 3 - 1 := by
    rw [Fintype.card_units, hK_card]
  have hord_g : orderOf g = p ^ 3 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, hK_units_card]
  -- Algebra map `ZMod p → K`
  let ι : ZMod p →+* K := algebraMap (ZMod p) K
  have hι_inj : Function.Injective ι := RingHom.injective ι
  -- Elements of `K` with `x ^ (p - 1) = 1` are precisely `ι '' (ZMod p)ˣ`
  have hpow_mem_range : ∀ u : Kˣ, u ^ (p - 1) = 1 → ∃ c : (ZMod p)ˣ, (u : K) = ι c := by
    intro u hu
    have hroot : (u : K) ^ p = (u : K) := by
      have h1 : (u : K) ^ (p - 1) = 1 := by rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]
      calc (u : K) ^ p = (u : K) ^ (p - 1 + 1) := by congr 1; omega
        _ = (u : K) ^ (p - 1) * (u : K) := pow_succ _ _
        _ = 1 * (u : K) := by rw [h1]
        _ = (u : K) := one_mul _
    let P : Polynomial K := Polynomial.X ^ p - Polynomial.X
    have hP_ne : P ≠ 0 := by
      intro h0
      have hdeg := congrArg Polynomial.natDegree h0
      have hdegP : P.natDegree = p := by
        dsimp [P]
        rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
        · exact Polynomial.natDegree_X_pow p
        · rw [Polynomial.natDegree_X, Polynomial.natDegree_X_pow]; omega
      rw [hdegP, Polynomial.natDegree_zero] at hdeg
      omega
    have hS_sub : (Finset.univ.image ι) ⊆ P.roots.toFinset := by
      intro x hx
      obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hx
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hP_ne, Polynomial.IsRoot.def]
      simp only [P, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
        ← map_pow, ZMod.pow_card, sub_self]
    have hS_card : (Finset.univ.image ι).card = p := by
      rw [Finset.card_image_of_injective _ hι_inj, Finset.card_univ, ZMod.card]
    have hroots_le : P.roots.toFinset.card ≤ p := by
      calc P.roots.toFinset.card ≤ P.roots.card := Multiset.toFinset_card_le _
        _ ≤ P.natDegree := Polynomial.card_roots' P
        _ ≤ p := by
          dsimp [P]
          exact le_trans (Polynomial.natDegree_sub_le _ _)
            (max_le (Polynomial.natDegree_X_pow_le p) (by rw [Polynomial.natDegree_X]; omega))
    have hEq : Finset.univ.image ι = P.roots.toFinset :=
      Finset.eq_of_subset_of_card_le hS_sub (by omega)
    have hu_mem : (u : K) ∈ P.roots.toFinset := by
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hP_ne, Polynomial.IsRoot.def]
      simp only [P, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, hroot, sub_self]
    rw [← hEq] at hu_mem
    obtain ⟨c, _, hc⟩ := Finset.mem_image.mp hu_mem
    have hc_ne : c ≠ 0 := by
      intro h0; subst h0; rw [map_zero] at hc; exact u.ne_zero hc.symm
    exact ⟨Units.mk0 c hc_ne, hc.symm⟩
  -- Bijection `(ZMod p)ˣ × Fin q ≃ Kˣ` given by `(c, i) ↦ ι(c) * g ^ i`
  let φ : (ZMod p)ˣ × Fin q → Kˣ := fun ⟨c, i⟩ => Units.map ι.toMonoidHom c * g ^ i.1
  have hφ_inj : Function.Injective φ := by
    rintro ⟨c₁, i₁⟩ ⟨c₂, i₂⟩ heq
    have hpow_eq : ∀ {a b : Fin q} {d₁ d₂ : (ZMod p)ˣ},
        a.1 ≤ b.1 → Units.map ι.toMonoidHom d₁ * g ^ a.1 = Units.map ι.toMonoidHom d₂ * g ^ b.1 →
        a = b ∧ d₁ = d₂ := by
      intro a b d₁ d₂ hab h
      have hgb : g ^ (b.1 - a.1) = Units.map ι.toMonoidHom (d₂⁻¹ * d₁) := by
        rw [map_mul, map_inv]
        apply mul_left_cancel (a := Units.map ι.toMonoidHom d₂ * g ^ a.1)
        calc Units.map ι.toMonoidHom d₂ * g ^ a.1 * g ^ (b.1 - a.1)
            = Units.map ι.toMonoidHom d₂ * g ^ (a.1 + (b.1 - a.1)) := by rw [mul_assoc, pow_add]
          _ = Units.map ι.toMonoidHom d₂ * g ^ b.1 := by rw [Nat.add_sub_of_le hab]
          _ = Units.map ι.toMonoidHom d₁ * g ^ a.1 := h.symm
          _ = Units.map ι.toMonoidHom d₂ * g ^ a.1 *
                ((Units.map ι.toMonoidHom d₂)⁻¹ * Units.map ι.toMonoidHom d₁) := by
              rw [mul_comm (Units.map ι.toMonoidHom d₂) (g ^ a.1), mul_assoc,
                ← mul_assoc (Units.map ι.toMonoidHom d₂), mul_inv_cancel, one_mul, mul_comm]
      have hp1 : (g ^ (b.1 - a.1)) ^ (p - 1) = 1 := by
        rw [hgb, ← map_pow]
        have hcard_u : Fintype.card (ZMod p)ˣ = p - 1 := by rw [Fintype.card_units, ZMod.card]
        rw [← hcard_u, pow_card_eq_one, map_one]
      rw [← pow_mul] at hp1
      have hdvd : p ^ 3 - 1 ∣ (b.1 - a.1) * (p - 1) := by
        rw [← hord_g]
        exact orderOf_dvd_of_pow_eq_one hp1
      rw [← hmul_q, mul_comm (p - 1) q] at hdvd
      have hqdvd : q ∣ b.1 - a.1 :=
        (Nat.mul_dvd_mul_iff_right (show 0 < p - 1 by omega)).mp hdvd
      have hba : b.1 - a.1 = 0 := Nat.eq_zero_of_dvd_of_lt hqdvd (by omega)
      have hab_eq : a = b := Fin.ext (by omega)
      subst hab_eq
      have hd_eq : Units.map ι.toMonoidHom d₁ = Units.map ι.toMonoidHom d₂ :=
        mul_right_cancel h
      have hd_eq' : d₁ = d₂ := by
        ext
        exact hι_inj (congrArg Units.val hd_eq)
      exact ⟨rfl, hd_eq'⟩
    rcases le_total i₁.1 i₂.1 with hle | hle
    · obtain ⟨hi, hc⟩ := hpow_eq hle heq
      exact Prod.ext hc hi
    · obtain ⟨hi, hc⟩ := hpow_eq hle heq.symm
      exact Prod.ext hc.symm hi.symm
  have hφ_bij : Function.Bijective φ := by
    refine (Fintype.bijective_iff_injective_and_card φ).mpr ⟨hφ_inj, ?_⟩
    rw [Fintype.card_prod, Fintype.card_units, ZMod.card, Fintype.card_fin, hK_units_card, hmul_q]
  -- Pick a nonzero linear functional `f : K →ₗ[ZMod p] ZMod p` from a basis of `K` over `ZMod p`
  let bas := Module.finBasisOfFinrankEq (ZMod p) K hK_finrank
  let f : K →ₗ[ZMod p] ZMod p := bas.coord 0
  have hf_surj : Function.Surjective f := by
    intro y
    refine ⟨y • bas 0, ?_⟩
    rw [map_smul, show f (bas 0) = 1 from by simp [f], smul_eq_mul, mul_one]
  have hker_rank : Module.finrank (ZMod p) (LinearMap.ker f) = 2 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker f
    have hrange : LinearMap.range f = ⊤ := LinearMap.range_eq_top.mpr hf_surj
    rw [hrange, finrank_top, Module.finrank_self, hK_finrank] at h1
    omega
  have hker_card : Fintype.card (LinearMap.ker f) = p ^ 2 := by
    have h1 := Module.card_eq_pow_finrank (K := ZMod p) (V := LinearMap.ker f)
    rw [ZMod.card, hker_rank] at h1
    exact h1
  -- Define `B₀ : Finset (Fin q)` as `{i | f (g ^ i) = 0}` and push to `ZMod q`
  let B₀ : Finset (Fin q) := Finset.univ.filter (fun i : Fin q => f ((g ^ i.1 : Kˣ) : K) = 0)
  have hB₀_card : B₀.card = p + 1 := by
    let kerUnits : Finset Kˣ := Finset.univ.filter (fun u : Kˣ => f (u : K) = 0)
    have hkerU_card : kerUnits.card = p ^ 2 - 1 := by
      have hbij : kerUnits.card + 1 = Fintype.card (LinearMap.ker f) := by
        have h1 : (Finset.univ.filter (fun x : K => f x = 0)).card = Fintype.card (LinearMap.ker f) := by
          rw [Fintype.card_subtype]
          congr 1
          ext x
          simp [LinearMap.mem_ker]
        rw [← h1]
        have h0 : (0 : K) ∈ Finset.univ.filter (fun x : K => f x = 0) := by
          simp
        rw [← Finset.card_erase_add_one h0]
        congr 1
        refine Finset.card_bij (fun u _ => (u : K)) ?_ ?_ ?_
        · intro u hu
          simp only [kerUnits, Finset.mem_filter, Finset.mem_univ, true_and] at hu
          simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨u.ne_zero, hu⟩
        · intro u₁ _ u₂ _ h
          exact Units.ext h
        · intro x hx
          simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hx
          exact ⟨Units.mk0 x hx.1, by simp [kerUnits, hx.2], rfl⟩
      omega
    have hprod_card : kerUnits.card = (p - 1) * B₀.card := by
      have hcard_eq : kerUnits.card = ((Finset.univ : Finset (ZMod p)ˣ) ×ˢ B₀).card := by
        symm
        refine Finset.card_bij (fun (pair : (ZMod p)ˣ × Fin q) _ => φ pair) ?_ ?_ ?_
        · rintro ⟨c, i⟩ hi
          simp only [Finset.mem_product, Finset.mem_univ, true_and, B₀, Finset.mem_filter] at hi
          simp only [kerUnits, Finset.mem_filter, Finset.mem_univ, true_and]
          change f (ι c * (g ^ i.1 : Kˣ)) = 0
          rw [← Algebra.smul_def, map_smul, hi, smul_zero]
        · intro a _ b _ h
          exact hφ_inj h
        · intro u hu
          simp only [kerUnits, Finset.mem_filter, Finset.mem_univ, true_and] at hu
          obtain ⟨⟨c, i⟩, rfl⟩ := hφ_bij.2 u
          refine ⟨(c, i), ?_, rfl⟩
          simp only [Finset.mem_product, Finset.mem_univ, true_and, B₀, Finset.mem_filter]
          change f (ι c * (g ^ i.1 : Kˣ)) = 0 at hu
          rw [← Algebra.smul_def, map_smul, smul_eq_mul] at hu
          exact (mul_eq_zero.mp hu).resolve_left c.ne_zero
      rw [hcard_eq, Finset.card_product, Finset.card_univ, Fintype.card_units, ZMod.card]
    have hmul : (p - 1) * (p + 1) = p ^ 2 - 1 := by
      zify [show 1 ≤ p by omega, show 1 ≤ p ^ 2 by exact one_le_pow₀ (by omega)]
      ring
    have : (p - 1) * B₀.card = (p - 1) * (p + 1) := by omega
    exact Nat.eq_of_mul_eq_mul_left (show 0 < p - 1 by omega) this
  -- Key property: if `k : ℕ` with `0 < k < q`, then `g ^ k` cannot preserve `ker f`
  have hgk_not_in_F : ∀ k : ℕ, 0 < k → k < q → ¬ ∃ c : (ZMod p)ˣ, (g ^ k : Kˣ) = Units.map ι.toMonoidHom c := by
    rintro k hk0 hkq ⟨c, hc⟩
    have h1 : φ (1, ⟨k, hkq⟩) = φ (c, ⟨0, hq_pos⟩) := by
      simp [φ, hc]
    have h2_pair : ((1 : (ZMod p)ˣ), (⟨k, hkq⟩ : Fin q)) = (c, ⟨0, hq_pos⟩) := hφ_inj h1
    have h2 := congrArg Prod.snd h2_pair
    have h3 := congrArg Fin.val h2
    dsimp only at h3
    omega
  -- Map `B₀` into `ZMod q` via `i ↦ (i.1 : ZMod q)`
  let castZ : Fin q ↪ ZMod q :=
    ⟨fun i => (i.1 : ZMod q), fun i j h => Fin.ext (by
      have := congrArg ZMod.val h
      rwa [ZMod.val_natCast_of_lt i.isLt, ZMod.val_natCast_of_lt j.isLt] at this)⟩
  let B : Finset (ZMod q) := B₀.map castZ
  have hB_card : B.card = p + 1 := by rw [Finset.card_map, hB₀_card]
  have hB_inj : ∀ a ∈ B, ∀ b ∈ B, ∀ c ∈ B, ∀ d ∈ B,
      a ≠ b → c ≠ d → a - b = c - d → a = c ∧ b = d := by
    intro a ha b hb c hc d hd hab hcd hdiff
    obtain ⟨ia, hia, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨ib, hib, rfl⟩ := Finset.mem_map.mp hb
    obtain ⟨ic, hic, rfl⟩ := Finset.mem_map.mp hc
    obtain ⟨id', hid', rfl⟩ := Finset.mem_map.mp hd
    by_contra hne
    have hac : ia ≠ ic := by
      intro h; subst h
      apply hne
      refine ⟨rfl, ?_⟩
      have : (castZ ib : ZMod q) = castZ id' := by
        have := hdiff
        linear_combination -this
      exact this
    -- Let `k : ℕ` be `(ic - ia : ZMod q).val`; since `ia ≠ ic`, `0 < k < q`
    let k : ℕ := (castZ ic - castZ ia).val
    have hk_lt : k < q := ZMod.val_lt _
    have hk_pos : 0 < k := by
      apply Nat.pos_of_ne_zero
      intro h0
      have hsub : castZ ic - castZ ia = 0 := by
        rw [← ZMod.natCast_zmod_val (castZ ic - castZ ia),
          show (castZ ic - castZ ia).val = k from rfl, h0, Nat.cast_zero]
      exact hac (castZ.injective (sub_eq_zero.mp hsub).symm)
    -- Also `k = (id' - ib).val`
    have hk_eq_bd : castZ id' - castZ ib = (k : ZMod q) := by
      have h1 : castZ id' - castZ ib = castZ ic - castZ ia := by linear_combination hdiff
      rw [h1, ZMod.natCast_zmod_val]
    have hk_eq_ac : castZ ic - castZ ia = (k : ZMod q) := (ZMod.natCast_zmod_val _).symm
    -- Show `g ^ q` is in `ι '' (ZMod p)ˣ`
    have hgq_mem : ∃ c₀ : (ZMod p)ˣ, ((g ^ q : Kˣ) : K) = ι c₀ := by
      apply hpow_mem_range (g ^ q)
      rw [← pow_mul, mul_comm q (p - 1), hmul_q, ← hord_g, pow_orderOf_eq_one]
    obtain ⟨c₀, hc₀⟩ := hgq_mem
    -- Show `(g ^ k) * (g ^ ia)` and `(g ^ k) * (g ^ ib)` lie in `ker f`
    have hmul_ker : ∀ (u v : Fin q), u ∈ B₀ → v ∈ B₀ → castZ v - castZ u = (k : ZMod q) →
        f (((g ^ k : Kˣ) : K) * ((g ^ u.1 : Kˣ) : K)) = 0 := by
      intro u v hu hv hvu
      have hcong : ((u.1 + k : ℕ) : ZMod q) = (v.1 : ZMod q) := by
        have : (v.1 : ZMod q) - (u.1 : ZMod q) = (k : ZMod q) := hvu
        push_cast
        linear_combination -this
      have hmod : (u.1 + k) % q = v.1 := by
        have := congrArg ZMod.val hcong
        rw [ZMod.val_natCast, ZMod.val_natCast_of_lt v.isLt] at this
        exact this
      have hdiv : u.1 + k = v.1 + q * ((u.1 + k) / q) := by
        have := Nat.div_add_mod (u.1 + k) q
        omega
      have hpow : ((g ^ k : Kˣ) : K) * ((g ^ u.1 : Kˣ) : K) =
          ι (c₀ ^ ((u.1 + k) / q) : (ZMod p)ˣ) * ((g ^ v.1 : Kˣ) : K) := by
        have h1 : (g ^ k : Kˣ) * (g ^ u.1 : Kˣ) = g ^ (u.1 + k) := by
          rw [← pow_add, add_comm]
        have h2 : (g ^ (u.1 + k) : Kˣ) = (g ^ q) ^ ((u.1 + k) / q) * g ^ v.1 := by
          conv_lhs => rw [hdiv]
          rw [pow_add, pow_mul, mul_comm]
        have h3 : (((g ^ k : Kˣ) : K) * ((g ^ u.1 : Kˣ) : K)) = ((g ^ (u.1 + k) : Kˣ) : K) := by
          exact_mod_cast congrArg Units.val h1
        rw [h3, h2]
        simp only [Units.val_mul, Units.val_pow_eq_pow_val, hc₀, Units.val_pow_eq_pow_val, map_pow]
      rw [hpow, ← Algebra.smul_def, map_smul]
      have hv0 : f ((g ^ v.1 : Kˣ) : K) = 0 := (Finset.mem_filter.mp hv).2
      rw [hv0, smul_zero]
    have hka : f (((g ^ k : Kˣ) : K) * ((g ^ ia.1 : Kˣ) : K)) = 0 :=
      hmul_ker ia ic hia hic hk_eq_ac
    have hkb : f (((g ^ k : Kˣ) : K) * ((g ^ ib.1 : Kˣ) : K)) = 0 :=
      hmul_ker ib id' hib hid' hk_eq_bd
    -- `g ^ ia` and `g ^ ib` are linearly independent over `ZMod p`
    have hab_fin : ia ≠ ib := fun h => hab (congrArg castZ h)
    have hlin : LinearIndependent (ZMod p) ![((g ^ ia.1 : Kˣ) : K), ((g ^ ib.1 : Kˣ) : K)] := by
      rw [Fintype.linearIndependent_iff]
      intro coeff hsum
      rw [Fin.sum_univ_two] at hsum
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Algebra.smul_def] at hsum
      have hc0 : coeff 0 = 0 := by
        by_contra h0
        have hc1 : coeff 1 ≠ 0 := by
          intro h1
          rw [h1, map_zero, zero_mul, add_zero] at hsum
          rcases mul_eq_zero.mp hsum with hι0 | hg0
          · exact h0 (hι_inj (hι0.trans (map_zero ι).symm))
          · exact (g ^ ia.1).ne_zero hg0
        let u0 : (ZMod p)ˣ := ⟨coeff 0, (coeff 0)⁻¹, mul_inv_cancel₀ h0, inv_mul_cancel₀ h0⟩
        let u1 : (ZMod p)ˣ := ⟨-coeff 1, (-coeff 1)⁻¹, mul_inv_cancel₀ (neg_ne_zero.mpr hc1),
          inv_mul_cancel₀ (neg_ne_zero.mpr hc1)⟩
        have heq_u : φ (u0, ia) = φ (u1, ib) := by
          apply Units.ext
          change ι (coeff 0) * ((g ^ ia.1 : Kˣ) : K) = ι (-coeff 1) * ((g ^ ib.1 : Kˣ) : K)
          rw [map_neg, neg_mul]
          exact eq_neg_of_add_eq_zero_left hsum
        have heq_p : (u0, ia) = (u1, ib) := hφ_inj heq_u
        exact hab_fin (congrArg Prod.snd heq_p)
      have hc1 : coeff 1 = 0 := by
        rw [hc0, map_zero, zero_mul, zero_add] at hsum
        rcases mul_eq_zero.mp hsum with hι0 | hg0
        · exact hι_inj (hι0.trans (map_zero ι).symm)
        · exact absurd hg0 (g ^ ib.1).ne_zero
      intro idx
      fin_cases idx <;> assumption
    -- Therefore `g ^ ia` and `g ^ ib` span `ker f` (since both have dimension 2)
    let va : LinearMap.ker f := ⟨((g ^ ia.1 : Kˣ) : K), (Finset.mem_filter.mp hia).2⟩
    let vb : LinearMap.ker f := ⟨((g ^ ib.1 : Kˣ) : K), (Finset.mem_filter.mp hib).2⟩
    let S : Submodule (ZMod p) (LinearMap.ker f) := Submodule.span (ZMod p) {va, vb}
    have hS_top : S = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [hker_rank]
      have hli_sub : LinearIndependent (ZMod p) ![va, vb] := by
        rw [Fintype.linearIndependent_iff]
        intro coeff hsum
        have hsum' : ∑ i : Fin 2, coeff i • (![((g ^ ia.1 : Kˣ) : K), ((g ^ ib.1 : Kˣ) : K)] i) = 0 := by
          have := congrArg Subtype.val hsum
          simp only [Fin.sum_univ_two, AddSubmonoidClass.coe_finset_sum, SetLike.val_smul,
            Matrix.cons_val_zero, Matrix.cons_val_one, ZeroMemClass.coe_zero] at this ⊢
          exact this
        exact Fintype.linearIndependent_iff.mp hlin coeff hsum'
      have hspan_eq : S = Submodule.span (ZMod p) (Set.range ![va, vb]) := by
        dsimp [S]
        congr 1
        ext x
        simp only [Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto
      rw [hspan_eq, finrank_span_eq_card hli_sub, Fintype.card_fin]
    -- Hence multiplication by `g ^ k` maps `ker f` into `ker f`
    have hmul_pres : ∀ v ∈ LinearMap.ker f, ((g ^ k : Kˣ) : K) * v ∈ LinearMap.ker f := by
      intro v hv
      have hvS : (⟨v, hv⟩ : LinearMap.ker f) ∈ S := hS_top.symm ▸ Submodule.mem_top
      rw [show S = Submodule.span (ZMod p) {va, vb} from rfl, Submodule.mem_span_pair] at hvS
      obtain ⟨c₁, c₂, hcomb⟩ := hvS
      have hv_eq : v = c₁ • ((g ^ ia.1 : Kˣ) : K) + c₂ • ((g ^ ib.1 : Kˣ) : K) := by
        have := congrArg Subtype.val hcomb
        exact this.symm
      rw [LinearMap.mem_ker, hv_eq, mul_add, map_add, Algebra.mul_smul_comm, Algebra.mul_smul_comm,
        map_smul, map_smul, hka, hkb, smul_zero, smul_zero, add_zero]
    -- Now `va`, `g^k * va`, `g^(2k) * va` are 3 vectors in the 2D space `ker f`, hence linearly dependent!
    let α : K := ((g ^ k : Kˣ) : K)
    let w0 : LinearMap.ker f := va
    let w1 : LinearMap.ker f := ⟨α * va.1, hmul_pres va.1 va.2⟩
    let w2 : LinearMap.ker f := ⟨α * w1.1, hmul_pres w1.1 w1.2⟩
    have hdep : ¬ LinearIndependent (ZMod p) ![w0, w1, w2] := by
      intro hli
      have hle := hli.fintype_card_le_finrank
      rw [Fintype.card_fin, hker_rank] at hle
      omega
    rw [Fintype.linearIndependent_iff] at hdep
    push Not at hdep
    obtain ⟨coeff, hsum, idx, hidx⟩ := hdep
    have hpoly : (ι (coeff 0) + ι (coeff 1) * α + ι (coeff 2) * α ^ 2) * va.1 = 0 := by
      rw [Fin.sum_univ_three] at hsum
      have hval := congrArg Subtype.val hsum
      simp only [Submodule.coe_add, SetLike.val_smul, ZeroMemClass.coe_zero,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, Algebra.smul_def, w0, w1, w2] at hval
      linear_combination hval
    have hpoly0 : ι (coeff 0) + ι (coeff 1) * α + ι (coeff 2) * α ^ 2 = 0 :=
      (mul_eq_zero.mp hpoly).resolve_right (g ^ ia.1).ne_zero
    -- So the minimal polynomial of `α` over `ZMod p` has degree ≤ 2
    have hdeg_le : (minpoly (ZMod p) α).natDegree ≤ 2 := by
      let Q : Polynomial (ZMod p) :=
        Polynomial.C (coeff 0) + Polynomial.C (coeff 1) * Polynomial.X +
        Polynomial.C (coeff 2) * Polynomial.X ^ 2
      have hQ_ne : Q ≠ 0 := by
        intro h0
        have hc0 : Q.coeff 0 = 0 := by rw [h0, Polynomial.coeff_zero]
        have hc1 : Q.coeff 1 = 0 := by rw [h0, Polynomial.coeff_zero]
        have hc2 : Q.coeff 2 = 0 := by rw [h0, Polynomial.coeff_zero]
        simp only [Q, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul,
          Polynomial.coeff_X, Polynomial.coeff_X_pow] at hc0 hc1 hc2
        fin_cases idx
        · exact hidx (by simpa using hc0)
        · exact hidx (by simpa using hc1)
        · exact hidx (by simpa using hc2)
      have hQ_aeval : Polynomial.aeval α Q = 0 := by
        simp only [Q, map_add, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
        exact hpoly0
      have hdvd := minpoly.dvd (ZMod p) α hQ_aeval
      have hQ_deg : Q.natDegree ≤ 2 := by
        dsimp [Q]
        refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
        · refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
          · rw [Polynomial.natDegree_C]; omega
          · exact le_trans (Polynomial.natDegree_C_mul_le _ _) (by rw [Polynomial.natDegree_X]; omega)
        · exact le_trans (Polynomial.natDegree_C_mul_le _ _) (Polynomial.natDegree_X_pow_le 2)
      exact le_trans (Polynomial.natDegree_le_of_dvd hdvd hQ_ne) hQ_deg
    -- On the other hand `minpoly.natDegree` divides `finrank (ZMod p) K = 3`
    have hdvd3 : (minpoly (ZMod p) α).natDegree ∣ 3 := by
      have hint : IsIntegral (ZMod p) α := Algebra.IsIntegral.isIntegral α
      have hmul := Module.finrank_mul_finrank (ZMod p) (IntermediateField.adjoin (ZMod p) {α}) K
      rw [IntermediateField.adjoin.finrank hint, hK_finrank] at hmul
      exact ⟨Module.finrank (IntermediateField.adjoin (ZMod p) {α}) K, hmul.symm⟩
    have hdeg_pos : 0 < (minpoly (ZMod p) α).natDegree :=
      minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral α)
    have hdeg1 : (minpoly (ZMod p) α).natDegree = 1 := by
      have hdiv : (minpoly (ZMod p) α).natDegree = 1 ∨ (minpoly (ZMod p) α).natDegree = 3 :=
        (Nat.dvd_prime Nat.prime_three).mp hdvd3
      omega
    -- Degree 1 minimal polynomial means `α ∈ ι '' (ZMod p)`
    have hα_in_F : ∃ c : ZMod p, α = ι c := by
      have hint : IsIntegral (ZMod p) α := Algebra.IsIntegral.isIntegral α
      have hmonic := minpoly.monic hint
      have heval := minpoly.aeval (ZMod p) α
      have hcoeff1 : (minpoly (ZMod p) α).coeff 1 = 1 := by
        rw [← hdeg1]; exact hmonic.leadingCoeff
      have hsum_mp := Polynomial.as_sum_range_C_mul_X_pow (minpoly (ZMod p) α)
      rw [hdeg1, Finset.sum_range_succ, Finset.sum_range_one, hcoeff1] at hsum_mp
      have haeval_mp := congrArg (Polynomial.aeval α) hsum_mp
      rw [heval] at haeval_mp
      simp only [map_add, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X,
        pow_zero, mul_one, pow_one, map_one, one_mul] at haeval_mp
      refine ⟨-(minpoly (ZMod p) α).coeff 0, ?_⟩
      rw [map_neg]
      exact eq_neg_of_add_eq_zero_right haeval_mp.symm
    obtain ⟨c, hc⟩ := hα_in_F
    have hc_ne : c ≠ 0 := by
      intro h0; subst h0; rw [map_zero] at hc; exact (g ^ k).ne_zero hc
    exact hgk_not_in_F k hk_pos hk_lt ⟨Units.mk0 c hc_ne, Units.ext hc⟩
  -- Surjectivity of `(a, b) ↦ a - b` onto `ZMod q \ {0}` by counting
  have hB_surj : ∀ x : ZMod q, x ≠ 0 → ∃ a ∈ B, ∃ b ∈ B, a - b = x := by
    let img : Finset (ZMod q) := B.offDiag.image (fun pair => pair.1 - pair.2)
    have himg_sub : img ⊆ Finset.univ.erase 0 := by
      intro x hx
      obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hx
      have hne : a ≠ b := (Finset.mem_offDiag.mp hab).2.2
      exact Finset.mem_erase.mpr ⟨sub_ne_zero.mpr hne, Finset.mem_univ _⟩
    have himg_card : img.card = (Finset.univ.erase (0 : ZMod q)).card := by
      have hinj_on : Set.InjOn (fun pair : ZMod q × ZMod q => pair.1 - pair.2) (B.offDiag : Set _) := by
        rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd heq
        simp only [Finset.mem_coe, Finset.mem_offDiag] at hab hcd
        obtain ⟨hac, hbd⟩ := hB_inj a hab.1 b hab.2.1 c hcd.1 d hcd.2.1 hab.2.2 hcd.2.2 heq
        exact Prod.ext hac hbd
      rw [Finset.card_image_of_injOn hinj_on, Finset.offDiag_card, hB_card,
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
      dsimp [q]
      zify [show p + 1 ≤ (p + 1) * (p + 1) by nlinarith, show 1 ≤ p ^ 2 + p + 1 by omega]
      ring
    have himg_eq : img = Finset.univ.erase 0 :=
      Finset.eq_of_subset_of_card_le himg_sub himg_card.ge
    intro x hx
    have hx_mem : x ∈ img := himg_eq.symm ▸ Finset.mem_erase.mpr ⟨hx, Finset.mem_univ _⟩
    obtain ⟨⟨a, b⟩, hab, heq⟩ := Finset.mem_image.mp hx_mem
    obtain ⟨ha, hb, _⟩ := Finset.mem_offDiag.mp hab
    exact ⟨a, ha, b, hb, heq⟩
  exact ⟨B, hB_card, hB_inj, hB_surj⟩

private lemma singer_exists (p : ℕ) (hp : p.Prime) :
    ∃ B : Finset (ZMod (p ^ 2 + p + 1)),
      B.card = p + 1 ∧
      (∀ a ∈ B, ∀ b ∈ B, ∀ c ∈ B, ∀ d ∈ B,
        a ≠ b → c ≠ d → a - b = c - d → a = c ∧ b = d) ∧
      (∀ x : ZMod (p ^ 2 + p + 1), x ≠ 0 → ∃ a ∈ B, ∃ b ∈ B, a - b = x) := by
  haveI : Fact p.Prime := ⟨hp⟩
  letI : Fintype (GaloisField p 3) := Fintype.ofFinite (GaloisField p 3)
  exact singer_exists_of_field p (GaloisField p 3) (GaloisField.finrank p (by norm_num))

/-! ### Part 2: Disjoint triples `b₁ + b₂ - b₃ = r` in a perfect difference set -/

private structure DisjointTriple (q : ℕ) (B : Finset (ZMod q)) (r : ZMod q) where
  b1 : ZMod q
  b2 : ZMod q
  b3 : ZMod q
  hb1 : b1 ∈ B
  hb2 : b2 ∈ B
  hb3 : b3 ∈ B
  h13 : b1 ≠ b3
  h23 : b2 ≠ b3
  heq : b1 + b2 - b3 = r

private def DisjointTriple.verts {q : ℕ} {B : Finset (ZMod q)} {r : ZMod q}
    (t : DisjointTriple q B r) : Finset (ZMod q) :=
  {t.b1, t.b2, t.b3}

private lemma exists_disjoint_triples {p : ℕ} {B : Finset (ZMod (p ^ 2 + p + 1))}
    (hcard : B.card = p + 1)
    (hinj : ∀ a ∈ B, ∀ b ∈ B, ∀ c ∈ B, ∀ d ∈ B,
      a ≠ b → c ≠ d → a - b = c - d → a = c ∧ b = d)
    (hsurj : ∀ x : ZMod (p ^ 2 + p + 1), x ≠ 0 → ∃ a ∈ B, ∃ b ∈ B, a - b = x)
    (r : ZMod (p ^ 2 + p + 1)) (hr : r ∉ B) :
    ∀ T : ℕ, 12 * T ≤ p →
      ∃ L : List (DisjointTriple (p ^ 2 + p + 1) B r),
        L.length = T ∧
        L.Pairwise (fun t₁ t₂ => Disjoint t₁.verts t₂.verts) := by
  classical
  let q := p ^ 2 + p + 1
  intro T
  induction T with
  | zero =>
    intro _
    exact ⟨[], rfl, List.Pairwise.nil⟩
  | succ T ih =>
    intro hT
    obtain ⟨L, hL_len, hL_pw⟩ := ih (by omega)
    let S : Finset (ZMod q) := L.foldr (fun t acc => t.verts ∪ acc) ∅
    have hS_mem_all : ∀ (l : List (DisjointTriple q B r)) (x : ZMod q),
        x ∈ l.foldr (fun (t : DisjointTriple q B r) acc => t.verts ∪ acc) ∅ ↔
          ∃ t ∈ l, x ∈ t.verts := by
      intro l x
      induction l with
      | nil => simp
      | cons hd tl ihtl =>
        simp only [List.foldr_cons, Finset.mem_union, List.mem_cons, exists_eq_or_imp]
        exact or_congr_right ihtl
    have hS_mem : ∀ x, x ∈ S ↔ ∃ t ∈ L, x ∈ t.verts := hS_mem_all L
    have hS_card : S.card ≤ 3 * T := by
      have hfold : ∀ (l : List (DisjointTriple q B r)),
          (l.foldr (fun (t : DisjointTriple q B r) acc => t.verts ∪ acc) ∅).card ≤ 3 * l.length := by
        intro l
        induction l with
        | nil => simp
        | cons hd tl ihtl =>
          simp only [List.foldr_cons, List.length_cons]
          have hv : hd.verts.card ≤ 3 := by
            dsimp [DisjointTriple.verts]
            exact le_trans (Finset.card_insert_le _ _)
              (Nat.add_le_add_right (le_trans (Finset.card_insert_le _ _) (by simp)) 1)
          have hu := Finset.card_union_le hd.verts
            (tl.foldr (fun (t : DisjointTriple q B r) acc => t.verts ∪ acc) ∅)
          omega
      simpa [S, hL_len] using hfold L
    -- For each `b1 ∈ B`, since `r ∉ B`, `r - b1 ≠ 0`, so choose unique `(b2, b3)` in `B` with `b2 - b3 = r - b1`
    have hex : ∀ b1 : B, ∃ p23 : ZMod q × ZMod q,
        p23.1 ∈ B ∧ p23.2 ∈ B ∧ p23.1 - p23.2 = r - b1.1 := by
      intro b1
      have hne : r - b1.1 ≠ 0 := sub_ne_zero.mpr (fun h => hr (h ▸ b1.2))
      obtain ⟨b2, hb2, b3, hb3, heq⟩ := hsurj (r - b1.1) hne
      exact ⟨(b2, b3), hb2, hb3, heq⟩
    choose f hf1 hf2 hfeq using hex
    -- Bound the three bad subsets of `B.attach`:
    let bad1 : Finset B := B.attach.filter (fun b1 => b1.1 ∈ S)
    let bad2 : Finset B := B.attach.filter (fun b1 => (f b1).1 ∈ S)
    let bad3 : Finset B := B.attach.filter (fun b1 => (f b1).2 ∈ S)
    have hbad1_card : bad1.card ≤ S.card := by
      refine Finset.card_le_card_of_injOn Subtype.val ?_ ?_
      · intro b1 hb1; exact (Finset.mem_filter.mp hb1).2
      · intro a _ b _ h; exact Subtype.ext h
    have hbad2_card : bad2.card ≤ S.card := by
      refine Finset.card_le_card_of_injOn (fun b1 => (f b1).1) ?_ ?_
      · intro b1 hb1; exact (Finset.mem_filter.mp hb1).2
      · intro a ha b hb heq
        have ha_diff : a.1 - (f a).2 = r - (f a).1 := by linear_combination hfeq a
        have hb_diff : b.1 - (f b).2 = r - (f b).1 := by linear_combination hfeq b
        have ha_ne : a.1 ≠ (f a).2 := by
          intro h; rw [h, sub_self] at ha_diff
          exact hr ((sub_eq_zero.mp ha_diff.symm) ▸ hf1 a)
        have hb_ne : b.1 ≠ (f b).2 := by
          intro h; rw [h, sub_self] at hb_diff
          exact hr ((sub_eq_zero.mp hb_diff.symm) ▸ hf1 b)
        have hEq := hinj a.1 a.2 (f a).2 (hf2 a) b.1 b.2 (f b).2 (hf2 b) ha_ne hb_ne
          (by dsimp only at heq; rw [ha_diff, hb_diff, heq])
        exact Subtype.ext hEq.1
    have hbad3_card : bad3.card ≤ 2 * S.card := by
      have hfib : bad3.card = ∑ s ∈ S, (bad3.filter (fun b1 => (f b1).2 = s)).card :=
        Finset.card_eq_sum_card_fiberwise (fun b1 hb1 => (Finset.mem_filter.mp hb1).2)
      rw [hfib]
      calc ∑ s ∈ S, (bad3.filter (fun b1 => (f b1).2 = s)).card
          ≤ ∑ _s ∈ S, 2 := by
            refine Finset.sum_le_sum fun s _ => ?_
            let Fs := bad3.filter (fun b1 => (f b1).2 = s)
            by_cases hne : Fs.Nonempty
            · obtain ⟨b0, hb0⟩ := hne
              have hb0_s : (f b0).2 = s := (Finset.mem_filter.mp hb0).2
              have hsub : Fs.image Subtype.val ⊆ {b0.1, (f b0).1} := by
                intro x hx
                obtain ⟨b1, hb1, rfl⟩ := Finset.mem_image.mp hx
                have hb1_s : (f b1).2 = s := (Finset.mem_filter.mp hb1).2
                have hsum : b1.1 + (f b1).1 = b0.1 + (f b0).1 := by
                  have h1 := hfeq b1
                  have h0 := hfeq b0
                  rw [hb1_s] at h1
                  rw [hb0_s] at h0
                  linear_combination h1 - h0
                simp only [Finset.mem_insert, Finset.mem_singleton]
                by_cases h10 : b1.1 = b0.1
                · exact Or.inl h10
                · right
                  have h20 : (f b0).1 ≠ (f b1).1 := by
                    intro h; apply h10; linear_combination hsum + h
                  have hdiff : b1.1 - b0.1 = (f b0).1 - (f b1).1 := by linear_combination hsum
                  exact (hinj b1.1 b1.2 b0.1 b0.2 (f b0).1 (hf1 b0) (f b1).1 (hf1 b1)
                    h10 h20 hdiff).1
              have hle := Finset.card_le_card hsub
              rw [Finset.card_image_of_injective _ Subtype.val_injective] at hle
              exact le_trans hle (le_trans (Finset.card_insert_le _ _) (by simp))
            · rw [show bad3.filter (fun b1 => (f b1).2 = s) = Fs from rfl,
                Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
              omega
        _ = S.card * 2 := by simp
        _ = 2 * S.card := mul_comm _ _
    have hbad_lt : (bad1 ∪ bad2 ∪ bad3).card < B.attach.card := by
      have hu1 := Finset.card_union_le (bad1 ∪ bad2) bad3
      have hu2 := Finset.card_union_le bad1 bad2
      rw [Finset.card_attach, hcard]
      omega
    obtain ⟨b1, _, hb1_good⟩ := Finset.exists_mem_notMem_of_card_lt_card hbad_lt
    simp only [Finset.mem_union, bad1, bad2, bad3, Finset.mem_filter, Finset.mem_attach,
      true_and, not_or] at hb1_good
    obtain ⟨⟨hb1S, hb2S⟩, hb3S⟩ := hb1_good
    have h13 : b1.1 ≠ (f b1).2 := by
      intro h
      have h0 := hfeq b1
      rw [← h] at h0
      have hr_eq : r = (f b1).1 := by linear_combination -h0
      exact hr (hr_eq ▸ hf1 b1)
    have h23 : (f b1).1 ≠ (f b1).2 := by
      intro h
      have h0 := hfeq b1
      rw [h, sub_self] at h0
      exact hr ((sub_eq_zero.mp h0.symm) ▸ b1.2)
    let t_new : DisjointTriple q B r := {
      b1 := b1.1
      b2 := (f b1).1
      b3 := (f b1).2
      hb1 := b1.2
      hb2 := hf1 b1
      hb3 := hf2 b1
      h13 := h13
      h23 := h23
      heq := by linear_combination hfeq b1
    }
    refine ⟨t_new :: L, by simp [hL_len], List.Pairwise.cons ?_ hL_pw⟩
    intro t ht
    rw [Finset.disjoint_left]
    intro x hx hx'
    have hxS : x ∈ S := (hS_mem x).mpr ⟨t, ht, hx'⟩
    simp only [DisjointTriple.verts, t_new, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hb1S hxS
    · exact hb2S hxS
    · exact hb3S hxS

/-! ### Part 3: Counting solutions to `u + v - w = s` and `2u - w = s` in `Fin K` -/

private lemma card_sub_interval_good (K : ℕ) (hK : 16 ≤ K) (s : ℤ)
    (hs1 : -1 ≤ s) (hs2 : s ≤ (K : ℤ) + 1) :
    ∃ I : Finset (Fin K), K / 8 ≤ I.card ∧
      ∀ u ∈ I, ∀ v ∈ I, 0 ≤ (u.1 : ℤ) + v.1 - s ∧ (u.1 : ℤ) + v.1 - s < K := by
  by_cases hs : s ≤ (K / 2 : ℕ)
  · let lo := K / 4 + 1
    let hi := K / 2 - 1
    let I : Finset (Fin K) := Finset.univ.filter (fun u : Fin K => lo ≤ u.1 ∧ u.1 ≤ hi)
    refine ⟨I, ?_, ?_⟩
    · have hbij : I.card = (Finset.Icc lo hi).card := by
        refine Finset.card_bij (fun u _ => u.1) ?_ ?_ ?_
        · intro u hu
          simp only [I, Finset.mem_filter, Finset.mem_univ, true_and] at hu
          exact Finset.mem_Icc.mpr hu
        · intro a _ b _ h; exact Fin.ext h
        · intro x hx
          have hx' := Finset.mem_Icc.mp hx
          exact ⟨⟨x, by omega⟩, by simp [I, hx'], rfl⟩
      rw [hbij, Nat.card_Icc]
      dsimp [lo, hi]
      omega
    · intro u hu v hv
      simp only [I, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
      omega
  · let lo := K / 2 + 1
    let hi := 3 * K / 4
    let I : Finset (Fin K) := Finset.univ.filter (fun u : Fin K => lo ≤ u.1 ∧ u.1 ≤ hi)
    refine ⟨I, ?_, ?_⟩
    · have hbij : I.card = (Finset.Icc lo hi).card := by
        refine Finset.card_bij (fun u _ => u.1) ?_ ?_ ?_
        · intro u hu
          simp only [I, Finset.mem_filter, Finset.mem_univ, true_and] at hu
          exact Finset.mem_Icc.mpr hu
        · intro a _ b _ h; exact Fin.ext h
        · intro x hx
          have hx' := Finset.mem_Icc.mp hx
          exact ⟨⟨x, by omega⟩, by simp [I, hx'], rfl⟩
      rw [hbij, Nat.card_Icc]
      dsimp [lo, hi]
      omega
    · intro u hu v hv
      simp only [I, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
      omega

private lemma bad_triple_card_le {q K : ℕ} {B : Finset (ZMod q)} {r : ZMod q}
    (t : DisjointTriple q B r) (hK : 16 ≤ K) (s : ℤ)
    (hs1 : -1 ≤ s) (hs2 : s ≤ (K : ℤ) + 1) :
    ((Finset.univ.filter (fun d : t.verts → Fin K =>
      ((d ⟨t.b1, by simp [DisjointTriple.verts]⟩).1 : ℤ) +
      ((d ⟨t.b2, by simp [DisjointTriple.verts]⟩).1 : ℤ) -
      ((d ⟨t.b3, by simp [DisjointTriple.verts]⟩).1 : ℤ) ≠ s)).card : ℝ) ≤
      (K : ℝ) ^ t.verts.card * (1 - 1 / (256 * (K : ℝ))) := by
  classical
  obtain ⟨I, hI_card, hI_good⟩ := card_sub_interval_good K hK s hs1 hs2
  let P : (t.verts → Fin K) → Prop := fun d =>
    ((d ⟨t.b1, by simp [DisjointTriple.verts]⟩).1 : ℤ) +
    ((d ⟨t.b2, by simp [DisjointTriple.verts]⟩).1 : ℤ) -
    ((d ⟨t.b3, by simp [DisjointTriple.verts]⟩).1 : ℤ) = s
  have hcomp : (Finset.univ.filter (fun d : t.verts → Fin K => ¬ P d)).card +
      (Finset.univ.filter P).card = K ^ t.verts.card := by
    rw [add_comm, Finset.card_filter_add_card_filter_not]
    simp [Fintype.card_pi, Fintype.card_fin]
  have hI_real : (K : ℝ) / 16 ≤ (I.card : ℝ) := by
    have h1 : (K : ℕ) ≤ 16 * (K / 8) := by omega
    have h2 : (K : ℝ) ≤ 16 * ((K / 8 : ℕ) : ℝ) := by exact_mod_cast h1
    have h3 : ((K / 8 : ℕ) : ℝ) ≤ (I.card : ℝ) := by exact_mod_cast hI_card
    linarith
  have hK_pos : (0 : ℝ) < K := by positivity
  have hgood_lb : (K : ℝ) ^ t.verts.card / (256 * (K : ℝ)) ≤ ((Finset.univ.filter P).card : ℝ) := by
    by_cases h12 : t.b1 = t.b2
    · have hv_card : t.verts.card = 2 := by
        dsimp [DisjointTriple.verts]
        rw [h12, Finset.insert_idem, Finset.card_pair (h12 ▸ t.h13)]
      have hcard_ge : I.card ≤ (Finset.univ.filter P).card := by
        let embed : Fin K → (t.verts → Fin K) := fun u x =>
          if x.1 = t.b3 then
            if h : 0 ≤ (u.1 : ℤ) + u.1 - s ∧ (u.1 : ℤ) + u.1 - s < K then
              ⟨((u.1 : ℤ) + u.1 - s).toNat, by omega⟩
            else u
          else u
        refine Finset.card_le_card_of_injOn embed ?_ ?_
        · intro u hu
          rw [Finset.mem_coe, Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          have hg := hI_good u hu u hu
          dsimp only [P, embed]
          simp only [t.h13, t.h23, ↓reduceIte, dif_pos hg]
          omega
        · intro u₁ _ u₂ _ heq
          have h1 := congrFun heq ⟨t.b1, by simp [DisjointTriple.verts]⟩
          simpa [embed, t.h13] using h1
      rw [hv_card]
      have hcard_real : (I.card : ℝ) ≤ ((Finset.univ.filter P).card : ℝ) := by exact_mod_cast hcard_ge
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    · have hv_card : t.verts.card = 3 := by
        dsimp [DisjointTriple.verts]
        rw [Finset.card_insert_of_notMem, Finset.card_pair t.h23]
        simp [h12, t.h13]
      have hcard_ge : (I ×ˢ I).card ≤ (Finset.univ.filter P).card := by
        let embed : Fin K × Fin K → (t.verts → Fin K) := fun uv x =>
          if x.1 = t.b1 then uv.1
          else if x.1 = t.b2 then uv.2
          else
            if h : 0 ≤ (uv.1.1 : ℤ) + uv.2.1 - s ∧ (uv.1.1 : ℤ) + uv.2.1 - s < K then
              ⟨((uv.1.1 : ℤ) + uv.2.1 - s).toNat, by omega⟩
            else uv.1
        refine Finset.card_le_card_of_injOn embed ?_ ?_
        · rintro ⟨u, v⟩ huv
          rw [Finset.mem_coe, Finset.mem_product] at huv
          rw [Finset.mem_coe, Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          have hg := hI_good u huv.1 v huv.2
          dsimp only [P, embed]
          simp only [↓reduceIte, Ne.symm h12, Ne.symm t.h13, Ne.symm t.h23, dif_pos hg]
          omega
        · rintro ⟨u₁, v₁⟩ _ ⟨u₂, v₂⟩ _ heq
          have h1 := congrFun heq ⟨t.b1, by simp [DisjointTriple.verts]⟩
          have h2 := congrFun heq ⟨t.b2, by simp [DisjointTriple.verts]⟩
          simp only [embed, ↓reduceIte, Ne.symm h12] at h1 h2
          exact Prod.ext h1 h2
      rw [hv_card]
      rw [Finset.card_product] at hcard_ge
      have hcard_real : (I.card : ℝ) * (I.card : ℝ) ≤ ((Finset.univ.filter P).card : ℝ) := by
        exact_mod_cast hcard_ge
      have hsq : ((K : ℝ) / 16) * ((K : ℝ) / 16) ≤ (I.card : ℝ) * (I.card : ℝ) :=
        mul_le_mul hI_real hI_real (by positivity) (by positivity)
      rw [div_le_iff₀ (by positivity)]
      nlinarith
  have hcomp_r : ((Finset.univ.filter (fun d : t.verts → Fin K => ¬ P d)).card : ℝ) +
      ((Finset.univ.filter P).card : ℝ) = (K : ℝ) ^ t.verts.card := by
    exact_mod_cast hcomp
  have hmul : (K : ℝ) ^ t.verts.card * (1 - 1 / (256 * (K : ℝ))) =
      (K : ℝ) ^ t.verts.card - (K : ℝ) ^ t.verts.card / (256 * (K : ℝ)) := by ring
  linarith

/- ### Part 4: Product bound for pairwise disjoint triples -/

open scoped Classical in
private lemma bad_list_card_le {q K : ℕ} {B : Finset (ZMod q)} {r : ZMod q}
    (hK : 16 ≤ K) (target : DisjointTriple q B r → ℤ)
    (htarget : ∀ t, -1 ≤ target t ∧ target t ≤ (K : ℤ) + 1) :
    ∀ (L : List (DisjointTriple q B r)) (V : Finset (ZMod q))
      (hsub : ∀ t ∈ L, t.verts ⊆ V),
      L.Pairwise (fun t₁ t₂ => Disjoint t₁.verts t₂.verts) →
      ((Finset.univ.filter (fun d : V → Fin K =>
        ∀ (t : DisjointTriple q B r) (ht : t ∈ L),
          ((d ⟨t.b1, (hsub t ht) (by simp [DisjointTriple.verts])⟩).1 : ℤ) +
          ((d ⟨t.b2, (hsub t ht) (by simp [DisjointTriple.verts])⟩).1 : ℤ) -
          ((d ⟨t.b3, (hsub t ht) (by simp [DisjointTriple.verts])⟩).1 : ℤ) ≠
            target t)).card : ℝ) ≤
        (K : ℝ) ^ V.card * (1 - 1 / (256 * (K : ℝ))) ^ L.length := by
  classical
  intro L
  induction L with
  | nil =>
    intro V hsub _
    have hle : (Finset.univ.filter (fun d : V → Fin K =>
        ∀ (t : DisjointTriple q B r) (ht : t ∈ ([] : List _)),
          ((d ⟨t.b1, (hsub t ht) (by simp [DisjointTriple.verts])⟩).1 : ℤ) +
          ((d ⟨t.b2, (hsub t ht) (by simp [DisjointTriple.verts])⟩).1 : ℤ) -
          ((d ⟨t.b3, (hsub t ht) (by simp [DisjointTriple.verts])⟩).1 : ℤ) ≠
            target t)).card ≤ (Finset.univ : Finset (V → Fin K)).card :=
      Finset.card_filter_le _ _
    have hcard : ((Finset.univ : Finset (V → Fin K)).card : ℝ) = (K : ℝ) ^ V.card := by
      simp [Fintype.card_pi, Fintype.card_fin]
    rw [List.length_nil, pow_zero, mul_one, ← hcard]
    exact_mod_cast hle
  | cons hd tl ih =>
    intro V hsub hpw
    rw [List.pairwise_cons] at hpw
    obtain ⟨hdisj, hpw_tl⟩ := hpw
    let V₁ : Finset (ZMod q) := hd.verts
    let V₂ : Finset (ZMod q) := V \ V₁
    have hV₁_sub : V₁ ⊆ V := hsub hd List.mem_cons_self
    have hsub_tl : ∀ t ∈ tl, t.verts ⊆ V₂ := by
      intro t ht x hx
      rw [Finset.mem_sdiff]
      exact ⟨hsub t (List.mem_cons_of_mem _ ht) hx,
        Finset.disjoint_left.mp (hdisj t ht).symm hx⟩
    have hcard_V : V₁.card + V₂.card = V.card := by
      dsimp [V₂]
      rw [Finset.card_sdiff_of_subset hV₁_sub]
      have := Finset.card_le_card hV₁_sub
      omega
    let BadV : Finset (V → Fin K) := Finset.univ.filter (fun d : V → Fin K =>
      ∀ (t : DisjointTriple q B r) (ht : t ∈ hd :: tl),
        ((d ⟨t.b1, (hsub t ht) (by simp [DisjointTriple.verts])⟩).1 : ℤ) +
        ((d ⟨t.b2, (hsub t ht) (by simp [DisjointTriple.verts])⟩).1 : ℤ) -
        ((d ⟨t.b3, (hsub t ht) (by simp [DisjointTriple.verts])⟩).1 : ℤ) ≠ target t)
    let Bad₁ : Finset (V₁ → Fin K) := Finset.univ.filter (fun d : V₁ → Fin K =>
      ((d ⟨hd.b1, by simp [V₁, DisjointTriple.verts]⟩).1 : ℤ) +
      ((d ⟨hd.b2, by simp [V₁, DisjointTriple.verts]⟩).1 : ℤ) -
      ((d ⟨hd.b3, by simp [V₁, DisjointTriple.verts]⟩).1 : ℤ) ≠ target hd)
    let Bad₂ : Finset (V₂ → Fin K) := Finset.univ.filter (fun d : V₂ → Fin K =>
      ∀ (t : DisjointTriple q B r) (ht : t ∈ tl),
        ((d ⟨t.b1, (hsub_tl t ht) (by simp [DisjointTriple.verts])⟩).1 : ℤ) +
        ((d ⟨t.b2, (hsub_tl t ht) (by simp [DisjointTriple.verts])⟩).1 : ℤ) -
        ((d ⟨t.b3, (hsub_tl t ht) (by simp [DisjointTriple.verts])⟩).1 : ℤ) ≠ target t)
    have hcard_le : BadV.card ≤ (Bad₁ ×ˢ Bad₂).card := by
      let split : (V → Fin K) → (V₁ → Fin K) × (V₂ → Fin K) :=
        fun d => (fun x => d ⟨x.1, hV₁_sub x.2⟩, fun x => d ⟨x.1, (Finset.mem_sdiff.mp x.2).1⟩)
      refine Finset.card_le_card_of_injOn split ?_ ?_
      · intro d hdV
        rw [Finset.mem_coe, Finset.mem_filter] at hdV
        rw [Finset.mem_coe, Finset.mem_product, Finset.mem_filter, Finset.mem_filter]
        refine ⟨⟨Finset.mem_univ _, hdV.2 hd List.mem_cons_self⟩,
          ⟨Finset.mem_univ _, fun t ht => hdV.2 t (List.mem_cons_of_mem _ ht)⟩⟩
      · intro d₁ _ d₂ _ heq
        funext ⟨x, hx⟩
        by_cases hx₁ : x ∈ V₁
        · exact congrFun (congrArg Prod.fst heq) ⟨x, hx₁⟩
        · exact congrFun (congrArg Prod.snd heq) ⟨x, Finset.mem_sdiff.mpr ⟨hx, hx₁⟩⟩
    rw [Finset.card_product] at hcard_le
    have h1 := bad_triple_card_le hd hK (target hd) (htarget hd).1 (htarget hd).2
    have h2 := ih V₂ hsub_tl hpw_tl
    have hcard_r : (BadV.card : ℝ) ≤ (Bad₁.card : ℝ) * (Bad₂.card : ℝ) := by exact_mod_cast hcard_le
    have hK_nn : (0 : ℝ) ≤ K := by positivity
    have hfac_nn : 0 ≤ 1 - 1 / (256 * (K : ℝ)) := by
      have : (1 : ℝ) ≤ 256 * (K : ℝ) := by
        have : (16 : ℝ) ≤ K := by exact_mod_cast hK
        linarith
      rw [sub_nonneg, div_le_one (by positivity)]
      exact this
    calc (BadV.card : ℝ)
        ≤ (Bad₁.card : ℝ) * (Bad₂.card : ℝ) := hcard_r
      _ ≤ ((K : ℝ) ^ V₁.card * (1 - 1 / (256 * (K : ℝ)))) *
          ((K : ℝ) ^ V₂.card * (1 - 1 / (256 * (K : ℝ))) ^ tl.length) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = (K : ℝ) ^ (V₁.card + V₂.card) * (1 - 1 / (256 * (K : ℝ))) ^ (tl.length + 1) := by
          rw [pow_add, pow_succ]; ring
      _ = (K : ℝ) ^ V.card * (1 - 1 / (256 * (K : ℝ))) ^ (hd :: tl).length := by
          rw [hcard_V, List.length_cons]

/- ### Part 5: Ruzsa's lifting, first-moment bound, and maximal Sidon extension -/

private lemma exists_maximal_sidon_of_prime {N p : ℕ} (hp : p.Prime)
    (hK : 16 ≤ N / (p ^ 2 + p + 1))
    (hprob : (N : ℝ) * (1 - 1 / (256 * ((N / (p ^ 2 + p + 1) : ℕ) : ℝ))) ^ (p / 12) ≤ 1) :
    ∃ A : Finset ℕ, Set.IsMaximalSidonSetIn (A : Set ℕ) N ∧
      A.card ≤ p + 2 + 2 * (N / (p ^ 2 + p + 1)) := by
  classical
  let q : ℕ := p ^ 2 + p + 1
  let K : ℕ := N / q
  have hq_pos : 0 < q := by positivity
  have : NeZero q := ⟨hq_pos.ne'⟩
  have hK_pos : 0 < K := by dsimp [K, q]; omega
  obtain ⟨B, hB_card, hB_inj, hB_surj⟩ := singer_exists p hp
  -- Lift `B` via `d : B → Fin K` to `A₀(d) = {b.val + q * (d b).val + 1 | b ∈ B}`
  let lift (d : B → Fin K) (b : B) : ℕ := b.1.val + q * (d b).1 + 1
  let A₀ (d : B → Fin K) : Finset ℕ := B.attach.image (lift d)
  have hlift_mem_Icc : ∀ d b, lift d b ∈ Finset.Icc 1 N := by
    intro d b
    rw [Finset.mem_Icc]
    refine ⟨by dsimp [lift]; omega, ?_⟩
    have hb_lt : b.1.val < q := ZMod.val_lt b.1
    have hd_le : (d b).1 + 1 ≤ K := (d b).isLt
    have hqK : q * K ≤ N := Nat.mul_div_le N q
    have h1 : q * (d b).1 + q ≤ q * K := by
      calc q * (d b).1 + q = q * ((d b).1 + 1) := by ring
        _ ≤ q * K := Nat.mul_le_mul_left q hd_le
    dsimp [lift]
    omega
  have hlift_inj : ∀ d, Function.Injective (lift d) := by
    intro d b₁ b₂ heq
    have hmod : (b₁.1.val : ZMod q) = (b₂.1.val : ZMod q) := by
      have h1 : (lift d b₁ - 1 : ℕ) = lift d b₂ - 1 := congrArg (· - 1) heq
      dsimp [lift] at h1
      have h2 := congrArg (Nat.cast (R := ZMod q)) h1
      simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul,
        add_zero] at h2
      exact h2
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at hmod
    exact Subtype.ext hmod
  have hA₀_card : ∀ d, (A₀ d).card = p + 1 := by
    intro d
    rw [Finset.card_image_of_injective _ (hlift_inj d), Finset.card_attach, hB_card]
  have hA₀_sidon : ∀ d, IsSidon (A₀ d : Set ℕ) := by
    intro d i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hsum
    simp only [Finset.mem_coe, A₀, Finset.mem_image, Finset.mem_attach, true_and] at hi₁ hj₁ hi₂ hj₂
    obtain ⟨b₁, rfl⟩ := hi₁
    obtain ⟨c₁, rfl⟩ := hj₁
    obtain ⟨b₂, rfl⟩ := hi₂
    obtain ⟨c₂, rfl⟩ := hj₂
    have hmod : b₁.1 + b₂.1 = c₁.1 + c₂.1 := by
      have h1 : (lift d b₁ - 1) + (lift d b₂ - 1) = (lift d c₁ - 1) + (lift d c₂ - 1) := by
        dsimp [lift] at hsum ⊢; omega
      have h2 := congrArg (Nat.cast (R := ZMod q)) h1
      simp only [lift, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self,
        zero_mul, add_zero, ZMod.natCast_zmod_val] at h2
      exact h2
    by_cases h11 : b₁.1 = c₁.1
    · have h22 : b₂.1 = c₂.1 := by linear_combination hmod - h11
      exact Or.inl ⟨congrArg (lift d) (Subtype.ext h11), congrArg (lift d) (Subtype.ext h22)⟩
    · have h21 : c₂.1 ≠ b₂.1 := by
        intro h; apply h11; linear_combination hmod + h
      have hdiff : b₁.1 - c₁.1 = c₂.1 - b₂.1 := by linear_combination hmod
      have hEq := hB_inj b₁.1 b₁.2 c₁.1 c₁.2 c₂.1 c₂.2 b₂.1 b₂.2 h11 h21 hdiff
      exact Or.inr ⟨congrArg (lift d) (Subtype.ext hEq.1), congrArg (lift d) (Subtype.ext hEq.2.symm)⟩
  -- For each `n ∈ Icc 1 N` with `((n - 1 : ℕ) : ZMod q) ∉ B`, bound the number of `d` where `n` is unblocked
  let Unblocked (d : B → Fin K) : Finset ℕ :=
    (Finset.Icc 1 N).filter (fun n => ((n - 1 : ℕ) : ZMod q) ∉ B ∧
      ∀ a₁ ∈ A₀ d, ∀ a₂ ∈ A₀ d, ∀ a₃ ∈ A₀ d, n + a₃ ≠ a₁ + a₂)
  have hbad_n : ∀ n ∈ Finset.Icc 1 N,
      ((Finset.univ.filter (fun d : B → Fin K => n ∈ Unblocked d)).card : ℝ) ≤
        (K : ℝ) ^ B.card * (1 - 1 / (256 * (K : ℝ))) ^ (p / 12) := by
    intro n hn
    let r : ZMod q := ((n - 1 : ℕ) : ZMod q)
    by_cases hr : r ∈ B
    · have hempty : Finset.univ.filter (fun d : B → Fin K => n ∈ Unblocked d) = ∅ := by
        ext d
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Unblocked, Finset.notMem_empty,
          iff_false, not_and]
        intro _ hnotB
        exact absurd hr hnotB
      rw [hempty, Finset.card_empty, Nat.cast_zero]
      have hfac_nn : 0 ≤ 1 - 1 / (256 * (K : ℝ)) := by
        have : (16 : ℝ) ≤ K := by exact_mod_cast hK
        rw [sub_nonneg, div_le_one (by positivity)]; linarith
      positivity
    · obtain ⟨L, hL_len, hL_pw⟩ := exists_disjoint_triples hB_card hB_inj hB_surj r hr (p / 12) (by omega)
      -- For each triple `t ∈ L`, compute the exact target `s(t) : ℤ` so that `d(b1)+d(b2)-d(b3) = s(t)` implies `n + lift d b3 = lift d b1 + lift d b2`
      let m : ℕ := (n - 1) / q
      have hm_le : m ≤ K := Nat.div_le_div_right ((Nat.sub_le n 1).trans (Finset.mem_Icc.mp hn).2)
      have hn_decomp : n - 1 = r.val + q * m := by
        dsimp [r, m]
        rw [ZMod.val_natCast, add_comm]
        exact (Nat.div_add_mod (n - 1) q).symm
      -- For `t : DisjointTriple q B r`, `r.val + t.b3.val - t.b1.val - t.b2.val` is divisible by `q`
      have hc_div : ∀ t : DisjointTriple q B r,
          ∃ c : ℤ, -1 ≤ c ∧ c ≤ 1 ∧
            (r.val : ℤ) + (t.b3.val : ℤ) - (t.b1.val : ℤ) - (t.b2.val : ℤ) = (q : ℤ) * c := by
        intro t
        have hcong : (((r.val : ℤ) + (t.b3.val : ℤ) - (t.b1.val : ℤ) - (t.b2.val : ℤ) : ℤ) : ZMod q) = 0 := by
          push_cast
          simp only [ZMod.natCast_zmod_val]
          linear_combination -t.heq
        obtain ⟨c, hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp hcong
        have hrb : r.val < q := ZMod.val_lt r
        have hb1 : t.b1.val < q := ZMod.val_lt t.b1
        have hb2 : t.b2.val < q := ZMod.val_lt t.b2
        have hb3 : t.b3.val < q := ZMod.val_lt t.b3
        have hc_lo : -1 ≤ c := by nlinarith
        have hc_hi : c ≤ 1 := by nlinarith
        exact ⟨c, hc_lo, hc_hi, hc⟩
      choose cf hcf_lo hcf_hi hcf_eq using hc_div
      let target : DisjointTriple q B r → ℤ := fun t => (m : ℤ) + cf t
      have htarget : ∀ t, -1 ≤ target t ∧ target t ≤ (K : ℤ) + 1 := by
        intro t
        dsimp [target]
        have h1 := hcf_lo t
        have h2 := hcf_hi t
        have hm_le' : (m : ℤ) ≤ (K : ℤ) := by exact_mod_cast hm_le
        have hm_nn : (0 : ℤ) ≤ (m : ℤ) := Nat.cast_nonneg m
        omega
      have hsub_bad : Finset.univ.filter (fun d : B → Fin K => n ∈ Unblocked d) ⊆
          Finset.univ.filter (fun d : B → Fin K =>
            ∀ (t : DisjointTriple q B r) (_ht : t ∈ L),
              ((d ⟨t.b1, t.hb1⟩).1 : ℤ) + ((d ⟨t.b2, t.hb2⟩).1 : ℤ) - ((d ⟨t.b3, t.hb3⟩).1 : ℤ) ≠
                target t) := by
        intro d hd
        rw [Finset.mem_filter] at hd ⊢
        refine ⟨Finset.mem_univ _, fun t _ heq => ?_⟩
        have hunb := (Finset.mem_filter.mp hd.2).2.2
        have hmem1 : lift d ⟨t.b1, t.hb1⟩ ∈ A₀ d := Finset.mem_image_of_mem _ (Finset.mem_attach _ _)
        have hmem2 : lift d ⟨t.b2, t.hb2⟩ ∈ A₀ d := Finset.mem_image_of_mem _ (Finset.mem_attach _ _)
        have hmem3 : lift d ⟨t.b3, t.hb3⟩ ∈ A₀ d := Finset.mem_image_of_mem _ (Finset.mem_attach _ _)
        apply hunb _ hmem1 _ hmem2 _ hmem3
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
        have hcf := hcf_eq t
        dsimp [target] at heq
        dsimp [lift]
        zify [hn1] at hn_decomp ⊢
        nlinarith
      have hsub_L : ∀ t ∈ L, t.verts ⊆ B := by
        intro t _ x hx
        simp only [DisjointTriple.verts, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact t.hb1
        · exact t.hb2
        · exact t.hb3
      have hbound := bad_list_card_le hK target htarget L B hsub_L hL_pw
      rw [hL_len] at hbound
      have hle_card : ((Finset.univ.filter (fun d : B → Fin K => n ∈ Unblocked d)).card : ℝ) ≤
          ((Finset.univ.filter (fun d : B → Fin K =>
            ∀ (t : DisjointTriple q B r) (_ht : t ∈ L),
              ((d ⟨t.b1, t.hb1⟩).1 : ℤ) + ((d ⟨t.b2, t.hb2⟩).1 : ℤ) - ((d ⟨t.b3, t.hb3⟩).1 : ℤ) ≠
                target t)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub_bad
      exact hle_card.trans (le_of_eq_of_le (by congr 2; ext d; simp) hbound)
  -- Sum over `n ∈ Icc 1 N` and apply pigeonhole over `d : B → Fin K`
  have hsum_le : ∑ d : B → Fin K, ((Unblocked d).card : ℝ) ≤
      ((Finset.univ : Finset (B → Fin K)).card : ℝ) * 1 := by
    have hswap : ∑ d : B → Fin K, (Unblocked d).card =
        ∑ n ∈ Finset.Icc 1 N, (Finset.univ.filter (fun d : B → Fin K => n ∈ Unblocked d)).card := by
      simp_rw [Finset.card_eq_sum_ones]
      trans ∑ d : B → Fin K, ∑ n ∈ Finset.Icc 1 N, if n ∈ Unblocked d then 1 else 0
      · refine Finset.sum_congr rfl fun d _ => ?_
        rw [← Finset.sum_filter]
        congr 1
        ext n
        simp only [Finset.mem_filter, Unblocked]
        tauto
      · rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [← Finset.sum_filter]
    have hswap_r : ∑ d : B → Fin K, ((Unblocked d).card : ℝ) =
        ∑ n ∈ Finset.Icc 1 N, ((Finset.univ.filter (fun d : B → Fin K => n ∈ Unblocked d)).card : ℝ) := by
      exact_mod_cast hswap
    rw [hswap_r]
    calc ∑ n ∈ Finset.Icc 1 N, ((Finset.univ.filter (fun d : B → Fin K => n ∈ Unblocked d)).card : ℝ)
        ≤ ∑ _n ∈ Finset.Icc 1 N, ((K : ℝ) ^ B.card * (1 - 1 / (256 * (K : ℝ))) ^ (p / 12)) :=
          Finset.sum_le_sum hbad_n
      _ = ((Finset.Icc 1 N).card : ℝ) * ((K : ℝ) ^ B.card * (1 - 1 / (256 * (K : ℝ))) ^ (p / 12)) := by
          simp
      _ = (K : ℝ) ^ B.card * ((N : ℝ) * (1 - 1 / (256 * (K : ℝ))) ^ (p / 12)) := by
          rw [Nat.card_Icc]; simp; ring
      _ ≤ (K : ℝ) ^ B.card * 1 := by
          exact mul_le_mul_of_nonneg_left hprob (by positivity)
      _ = ((Finset.univ : Finset (B → Fin K)).card : ℝ) * 1 := by
          simp [Fintype.card_pi, Fintype.card_fin]
  have huniv_ne : (Finset.univ : Finset (B → Fin K)).Nonempty :=
    ⟨fun _ => ⟨0, hK_pos⟩, Finset.mem_univ _⟩
  have hsum_le' : ∑ d : B → Fin K, ((Unblocked d).card : ℝ) ≤ ∑ _d : B → Fin K, (1 : ℝ) := by
    simpa [Finset.sum_const, nsmul_eq_mul] using hsum_le
  obtain ⟨d, _, hd_le⟩ := Finset.exists_le_of_sum_le huniv_ne hsum_le'
  have hU_card : (Unblocked d).card ≤ 1 := by exact_mod_cast hd_le
  -- Pick a maximum-cardinality Sidon set `A ⊆ Icc 1 N` containing `A₀ d`
  let F : Finset (Finset ℕ) :=
    (Finset.Icc 1 N).powerset.filter (fun S => A₀ d ⊆ S ∧ IsSidon (S : Set ℕ))
  have hF_ne : F.Nonempty := by
    refine ⟨A₀ d, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, Finset.Subset.refl _, hA₀_sidon d⟩⟩
    intro x hx
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hx
    exact hlift_mem_Icc d b
  obtain ⟨A, hAF, hA_max⟩ := Finset.exists_max_image F Finset.card hF_ne
  obtain ⟨hA_pow, hA₀_sub, hA_sidon⟩ := Finset.mem_filter.mp hAF
  have hA_Icc : (A : Set ℕ) ⊆ Set.Icc 1 N := by
    intro x hx
    exact Finset.mem_Icc.mp (Finset.mem_powerset.mp hA_pow hx)
  have hA_maximal : Set.IsMaximalSidonSetIn (A : Set ℕ) N := by
    refine ⟨hA_Icc, hA_sidon, fun x hxIcc hxA hSid => ?_⟩
    have hAx_mem : insert x A ∈ F := by
      rw [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨?_, hA₀_sub.trans (Finset.subset_insert x A), ?_⟩
      · intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hyA
        · exact Finset.mem_Icc.mpr hxIcc
        · exact Finset.mem_powerset.mp hA_pow hyA
      · rw [Finset.coe_insert, Set.insert_eq, Set.union_comm]
        exact hSid
    have hle := hA_max (insert x A) hAx_mem
    rw [Finset.card_insert_of_notMem hxA] at hle
    omega
  -- Bound `A.card`: split `A \ A₀ d` into `r ∉ B` (⊆ `Unblocked d`, size ≤ 1) and `r ∈ B` (size ≤ `2 * K`)
  let U₁ : Finset ℕ := (A \ A₀ d).filter (fun x => ((x - 1 : ℕ) : ZMod q) ∉ B)
  let U₂ : Finset ℕ := (A \ A₀ d).filter (fun x => ((x - 1 : ℕ) : ZMod q) ∈ B)
  have hU₁_sub : U₁ ⊆ Unblocked d := by
    intro x hx
    obtain ⟨hx_diff, hx_notB⟩ := Finset.mem_filter.mp hx
    obtain ⟨hxA, hx_notA₀⟩ := Finset.mem_sdiff.mp hx_diff
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_powerset.mp hA_pow hxA, hx_notB, fun a₁ ha₁ a₂ ha₂ a₃ ha₃ heq => ?_⟩
    rcases hA_sidon x hxA a₁ (hA₀_sub ha₁) a₃ (hA₀_sub ha₃) a₂ (hA₀_sub ha₂) heq with
      ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact hx_notA₀ ha₁
    · exact hx_notA₀ ha₂
  have hU₁_card : U₁.card ≤ 1 := (Finset.card_le_card hU₁_sub).trans hU_card
  have hU₂_card : U₂.card ≤ 2 * K := by
    -- Map `x ∈ U₂` to `(x - lift d b_x) / q` in `Finset.Icc (-K : ℤ) K \ {0}`
    let T : Finset ℤ := (Finset.Icc (-(K : ℤ)) (K : ℤ)).erase 0
    have hT_card : T.card = 2 * K := by
      rw [Finset.card_erase_of_mem (Finset.mem_Icc.mpr ⟨by omega, by omega⟩), Int.card_Icc]
      omega
    rw [← hT_card]
    let φ : ℕ → ℤ := fun x =>
      if h : ((x - 1 : ℕ) : ZMod q) ∈ B then
        ((x : ℤ) - (lift d ⟨((x - 1 : ℕ) : ZMod q), h⟩ : ℤ)) / (q : ℤ)
      else 0
    have hφ_mul : ∀ x ∈ U₂, ∃ h : ((x - 1 : ℕ) : ZMod q) ∈ B,
        (x : ℤ) - (lift d ⟨((x - 1 : ℕ) : ZMod q), h⟩ : ℤ) = (q : ℤ) * φ x := by
      intro x hx
      have hxB : ((x - 1 : ℕ) : ZMod q) ∈ B := (Finset.mem_filter.mp hx).2
      refine ⟨hxB, ?_⟩
      simp only [φ, dif_pos hxB]
      have hx1 : 1 ≤ x := (Finset.mem_Icc.mp (Finset.mem_powerset.mp hA_pow
        (Finset.mem_sdiff.mp (Finset.mem_filter.mp hx).1).1)).1
      have hdvd : (q : ℤ) ∣ ((x : ℤ) - (lift d ⟨((x - 1 : ℕ) : ZMod q), hxB⟩ : ℤ)) := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        have h1 : (x : ℤ) - (lift d ⟨((x - 1 : ℕ) : ZMod q), hxB⟩ : ℤ) =
            ((x - 1 : ℕ) : ℤ) - (((((x - 1 : ℕ) : ZMod q).val : ℕ) : ℤ) + (q : ℤ) * ((d ⟨_, hxB⟩).1 : ℤ)) := by
          dsimp [lift]; omega
        rw [h1]
        push_cast
        simp only [ZMod.natCast_zmod_val, ZMod.natCast_self, zero_mul, add_zero, sub_self]
      exact (Int.mul_ediv_cancel' hdvd).symm
    refine Finset.card_le_card_of_injOn φ ?_ ?_
    · intro x hx
      obtain ⟨hxB, hmul⟩ := hφ_mul x hx
      have hxA : x ∈ A := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hx).1).1
      have hx_notA₀ : x ∉ A₀ d := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hx).1).2
      have hx_Icc := Finset.mem_Icc.mp (Finset.mem_powerset.mp hA_pow hxA)
      have hl_Icc := Finset.mem_Icc.mp (hlift_mem_Icc d ⟨_, hxB⟩)
      have hne0 : φ x ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hmul
        have heq : x = lift d ⟨((x - 1 : ℕ) : ZMod q), hxB⟩ := by omega
        exact hx_notA₀ (heq ▸ Finset.mem_image_of_mem _ (Finset.mem_attach _ _))
      have hqK1 : N < q * (K + 1) := by
        have := Nat.lt_div_mul_add hq_pos (a := N)
        dsimp [K]; linarith
      have hlo : -(K : ℤ) ≤ φ x := by nlinarith
      have hhi : φ x ≤ (K : ℤ) := by nlinarith
      exact Finset.mem_erase.mpr ⟨hne0, Finset.mem_Icc.mpr ⟨hlo, hhi⟩⟩
    · intro x hx y hy hφeq
      obtain ⟨hxB, hxm⟩ := hφ_mul x hx
      obtain ⟨hyB, hym⟩ := hφ_mul y hy
      let ax := lift d ⟨((x - 1 : ℕ) : ZMod q), hxB⟩
      let ay := lift d ⟨((y - 1 : ℕ) : ZMod q), hyB⟩
      have hdiff_eq : (x : ℤ) - (ax : ℤ) = (y : ℤ) - (ay : ℤ) := by
        rw [hxm, hym, hφeq]
      have hsum : x + ay = y + ax := by omega
      have hxA : x ∈ A := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hx).1).1
      have hyA : y ∈ A := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hy).1).1
      have haxA : ax ∈ A := hA₀_sub (Finset.mem_image_of_mem _ (Finset.mem_attach _ _))
      have hayA : ay ∈ A := hA₀_sub (Finset.mem_image_of_mem _ (Finset.mem_attach _ _))
      rcases hA_sidon x hxA y hyA ay hayA ax haxA hsum with ⟨hxy, _⟩ | ⟨hxax, _⟩
      · exact hxy
      · exfalso
        have hx_notA₀ : x ∉ A₀ d := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hx).1).2
        exact hx_notA₀ (hxax ▸ Finset.mem_image_of_mem _ (Finset.mem_attach _ _))
  have hA_card_bound : A.card ≤ p + 2 + 2 * K := by
    have hsplit : (A \ A₀ d).card = U₁.card + U₂.card := by
      dsimp [U₁, U₂]
      rw [add_comm]
      exact (Finset.card_filter_add_card_filter_not _).symm
    have htotal : A.card = (A₀ d).card + (A \ A₀ d).card := by
      rw [Finset.card_sdiff_of_subset hA₀_sub]
      have := Finset.card_le_card hA₀_sub
      omega
    rw [htotal, hA₀_card d, hsplit]
    omega
  exact ⟨A, hA_maximal, hA_card_bound⟩

private theorem ruzsa_upper_bound_proof :
    (fun N ↦ (Erdos156.minMaximalSidonSet N : ℝ)) =O[atTop]
      (fun N ↦ ((N : ℝ) * Real.log N) ^ (1 / 3 : ℝ)) := by
  classical
  -- Use `isLittleO_log_rpow_atTop` to show `(log N)^2 / N^(1/3) → 0`
  have hlog_little : (fun N : ℕ => (Real.log (N : ℝ)) ^ 2) =o[atTop] (fun N : ℕ => (N : ℝ) ^ (1 / 3 : ℝ)) := by
    have h1 := isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 6 by norm_num)
    have h2 : (fun x : ℝ => (Real.log x) ^ 2) =o[atTop] (fun x : ℝ => ((x ^ (1 / 6 : ℝ)) ^ 2)) := by
      simpa [pow_two] using h1.mul h1
    have h3 : (fun x : ℝ => (Real.log x) ^ 2) =o[atTop] (fun x : ℝ => x ^ (1 / 3 : ℝ)) := by
      refine h2.congr' (Eventually.of_forall fun _ => rfl) ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
      norm_num
    exact h3.comp_tendsto tendsto_natCast_atTop_atTop
  have hev_small : ∀ᶠ N : ℕ in atTop,
      (Real.log (N : ℝ)) ^ 2 ≤ (1 / (10 ^ 15 : ℝ)) * (N : ℝ) ^ (1 / 3 : ℝ) := by
    have hb := hlog_little.bound (show (0 : ℝ) < 1 / (10 ^ 15 : ℝ) by norm_num)
    filter_upwards [hb, eventually_ge_atTop 2] with N hN hN2
    have hN_pos : (0 : ℝ) < N := by positivity
    have h1 : ‖(Real.log (N : ℝ)) ^ 2‖ = (Real.log (N : ℝ)) ^ 2 :=
      Real.norm_of_nonneg (sq_nonneg _)
    have h2 : ‖(N : ℝ) ^ (1 / 3 : ℝ)‖ = (N : ℝ) ^ (1 / 3 : ℝ) :=
      Real.norm_of_nonneg (Real.rpow_nonneg hN_pos.le _)
    rwa [h1, h2] at hN
  rw [Asymptotics.isBigO_iff]
  refine ⟨100, ?_⟩
  filter_upwards [hev_small, eventually_ge_atTop 1000000] with N hlogN hNbig
  have hN_pos : (0 : ℝ) < N := by positivity
  have hlog_ge1 : (1 : ℝ) ≤ Real.log (N : ℝ) := by
    have : Real.exp 1 ≤ (N : ℝ) := by
      have he : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
      have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast (show 3 ≤ N by omega)
      linarith
    exact (Real.le_log_iff_exp_le hN_pos).mpr this
  let L : ℝ := ((N : ℝ) * Real.log (N : ℝ)) ^ (1 / 3 : ℝ)
  have hL_pos : 0 < L := Real.rpow_pos_of_pos (mul_pos hN_pos (by linarith)) _
  have hL_ge : (100 : ℝ) ≤ L := by
    have h1 : (100 : ℝ) ^ (3 : ℕ) ≤ (N : ℝ) * Real.log (N : ℝ) := by
      have hN1 : (1000000 : ℝ) ≤ N := by exact_mod_cast hNbig
      nlinarith
    have h2 : ((100 : ℝ) ^ (3 : ℕ)) ^ (1 / 3 : ℝ) ≤ L :=
      Real.rpow_le_rpow (by positivity) h1 (by norm_num)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 100)] at h2
    norm_num at h2
    exact h2
  let P : ℕ := ⌈(4000 * (N : ℝ) * Real.log (N : ℝ)) ^ (1 / 3 : ℝ)⌉₊ + 150
  have hP_pos : P ≠ 0 := by omega
  obtain ⟨p, hp_prime, hP_lt_p, hp_le_2P⟩ := Nat.exists_prime_lt_and_le_two_mul P hP_pos
  have hp_ge150 : 150 ≤ p := by omega
  have hP_le : (P : ℝ) ≤ 17 * L + 151 := by
    have h4000 : (4000 : ℝ) ^ (1 / 3 : ℝ) ≤ 17 := by
      have h1 : (4000 : ℝ) ≤ (17 : ℝ) ^ (3 : ℕ) := by norm_num
      have h2 := Real.rpow_le_rpow (by norm_num) h1 (by norm_num : (0 : ℝ) ≤ 1 / 3)
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 17)] at h2
      norm_num at h2
      exact h2
    have hmul : (4000 * (N : ℝ) * Real.log (N : ℝ)) ^ (1 / 3 : ℝ) =
        (4000 : ℝ) ^ (1 / 3 : ℝ) * L := by
      rw [mul_assoc, Real.mul_rpow (by norm_num) (by positivity)]
    have hceil : (⌈(4000 * (N : ℝ) * Real.log (N : ℝ)) ^ (1 / 3 : ℝ)⌉₊ : ℝ) ≤
        (4000 * (N : ℝ) * Real.log (N : ℝ)) ^ (1 / 3 : ℝ) + 1 :=
      (Nat.ceil_lt_add_one (by positivity)).le
    dsimp [P]
    push_cast
    nlinarith
  have hp_le : (p : ℝ) ≤ 38 * L := by
    have hp2 : (p : ℝ) ≤ 2 * (P : ℝ) := by exact_mod_cast hp_le_2P
    nlinarith
  have hp_cube : 4000 * (N : ℝ) * Real.log (N : ℝ) ≤ (p : ℝ) ^ 3 := by
    have h1 : (4000 * (N : ℝ) * Real.log (N : ℝ)) ^ (1 / 3 : ℝ) ≤ (p : ℝ) := by
      have h2 : (4000 * (N : ℝ) * Real.log (N : ℝ)) ^ (1 / 3 : ℝ) ≤
          (⌈(4000 * (N : ℝ) * Real.log (N : ℝ)) ^ (1 / 3 : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
      have h3 : (⌈(4000 * (N : ℝ) * Real.log (N : ℝ)) ^ (1 / 3 : ℝ)⌉₊ : ℝ) ≤ (p : ℝ) := by
        exact_mod_cast (show ⌈(4000 * (N : ℝ) * Real.log (N : ℝ)) ^ (1 / 3 : ℝ)⌉₊ ≤ p by omega)
      linarith
    have h2 := pow_le_pow_left₀ (by positivity) h1 3
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)] at h2
    norm_num at h2
    exact h2
  have hL3 : L ^ 3 = (N : ℝ) * Real.log (N : ℝ) := by
    dsimp [L]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hL_sq_le : L ^ 2 ≤ (1 / 100000 : ℝ) * (N : ℝ) := by
    have hcube : (L ^ 2) ^ 3 ≤ ((1 / 100000 : ℝ) * (N : ℝ)) ^ 3 := by
      have hN13 : (N : ℝ) ^ (1 / 3 : ℝ) ≤ (N : ℝ) := by
        have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
        calc (N : ℝ) ^ (1 / 3 : ℝ) ≤ (N : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
          _ = N := Real.rpow_one _
      calc (L ^ 2) ^ 3 = (L ^ 3) ^ 2 := by ring
        _ = (N : ℝ) ^ 2 * (Real.log (N : ℝ)) ^ 2 := by rw [hL3]; ring
        _ ≤ (N : ℝ) ^ 2 * ((1 / (10 ^ 15 : ℝ)) * (N : ℝ) ^ (1 / 3 : ℝ)) :=
            mul_le_mul_of_nonneg_left hlogN (by positivity)
        _ ≤ (N : ℝ) ^ 2 * ((1 / (10 ^ 15 : ℝ)) * (N : ℝ)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hN13 (by norm_num)) (by positivity)
        _ = ((1 / 100000 : ℝ) * (N : ℝ)) ^ 3 := by ring
    by_contra hlt
    push Not at hlt
    have hgt : ((1 / 100000 : ℝ) * (N : ℝ)) ^ 3 < (L ^ 2) ^ 3 :=
      pow_lt_pow_left₀ hlt (by positivity) (by norm_num)
    linarith
  have hK_ge16 : 16 ≤ N / (p ^ 2 + p + 1) := by
    rw [Nat.le_div_iff_mul_le (by positivity)]
    have hq_le : (p ^ 2 + p + 1 : ℝ) ≤ 2 * (p : ℝ) ^ 2 := by
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp_prime.two_le
      nlinarith
    have h16q : (16 * (p ^ 2 + p + 1) : ℝ) ≤ (N : ℝ) := by
      nlinarith [sq_nonneg ((p : ℝ) - 38 * L)]
    exact_mod_cast h16q
  let K : ℕ := N / (p ^ 2 + p + 1)
  have hK_pos : (0 : ℝ) < K := by
    have : 0 < K := by dsimp [K]; omega
    positivity
  have hK_le : (K : ℝ) ≤ (N : ℝ) / ((p : ℝ) ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    have h1 : K * (p ^ 2) ≤ K * (p ^ 2 + p + 1) := Nat.mul_le_mul_left K (by omega)
    have h2 : K * (p ^ 2 + p + 1) ≤ N := Nat.div_mul_le_self N _
    exact_mod_cast h1.trans h2
  have hprob : (N : ℝ) * (1 - 1 / (256 * (K : ℝ))) ^ (p / 12) ≤ 1 := by
    have h1 : 1 - 1 / (256 * (K : ℝ)) ≤ Real.exp (-(1 / (256 * (K : ℝ)))) := by
      have := Real.add_one_le_exp (-(1 / (256 * (K : ℝ))))
      linarith
    have hfac_nn : 0 ≤ 1 - 1 / (256 * (K : ℝ)) := by
      have : (16 : ℝ) ≤ K := by exact_mod_cast hK_ge16
      rw [sub_nonneg, div_le_one (by positivity)]; linarith
    have hpow := pow_le_pow_left₀ hfac_nn h1 (p / 12)
    rw [← Real.exp_nat_mul] at hpow
    have hexp_le : Real.exp ((p / 12 : ℕ) * -(1 / (256 * (K : ℝ)))) ≤ 1 / (N : ℝ) := by
      rw [show (1 : ℝ) / (N : ℝ) = Real.exp (-Real.log (N : ℝ)) by
        rw [Real.exp_neg, Real.exp_log hN_pos, one_div], Real.exp_le_exp]
      have hT_ge : (p : ℝ) / 13 ≤ ((p / 12 : ℕ) : ℝ) := by
        have h12 : p ≤ 13 * (p / 12) := by omega
        have h12r : (p : ℝ) ≤ 13 * ((p / 12 : ℕ) : ℝ) := by exact_mod_cast h12
        linarith
      have hdiv_ge : Real.log (N : ℝ) ≤ ((p / 12 : ℕ) : ℝ) / (256 * (K : ℝ)) := by
        rw [le_div_iff₀ (by positivity)]
        have h256 : 256 * (K : ℝ) * Real.log (N : ℝ) ≤ 256 * ((N : ℝ) / (p : ℝ) ^ 2) * Real.log (N : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK_le (by norm_num)) (by linarith)
        have h3328 : 256 * ((N : ℝ) / (p : ℝ) ^ 2) * Real.log (N : ℝ) ≤ (p : ℝ) / 13 := by
          have hp_pos : (0 : ℝ) < p := by positivity
          rw [show 256 * ((N : ℝ) / (p : ℝ) ^ 2) * Real.log (N : ℝ) =
              (256 * (N : ℝ) * Real.log (N : ℝ)) / (p : ℝ) ^ 2 by ring]
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
        linarith
      have hneg : ((p / 12 : ℕ) : ℝ) * -(1 / (256 * (K : ℝ))) = -(((p / 12 : ℕ) : ℝ) / (256 * (K : ℝ))) := by ring
      linarith
    calc (N : ℝ) * (1 - 1 / (256 * (K : ℝ))) ^ (p / 12)
        ≤ (N : ℝ) * Real.exp ((p / 12 : ℕ) * -(1 / (256 * (K : ℝ)))) :=
          mul_le_mul_of_nonneg_left hpow hN_pos.le
      _ ≤ (N : ℝ) * (1 / (N : ℝ)) := mul_le_mul_of_nonneg_left hexp_le hN_pos.le
      _ = 1 := mul_one_div_cancel hN_pos.ne'
  obtain ⟨A, hA_max, hA_card⟩ := exists_maximal_sidon_of_prime hp_prime hK_ge16 hprob
  have hmin_le : Erdos156.minMaximalSidonSet N ≤ A.card := by
    unfold Erdos156.minMaximalSidonSet
    apply Nat.sInf_le
    rw [Finset.mem_coe, Finset.mem_image]
    refine ⟨A, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, hA_max⟩, rfl⟩
    intro x hx
    exact Finset.mem_Icc.mpr (hA_max.1 hx)
  have hK_le_L : (K : ℝ) ≤ L := by
    have hp_ge_L : L ≤ (p : ℝ) := by
      have : L ^ 3 ≤ (p : ℝ) ^ 3 := by nlinarith
      by_contra hlt
      push Not at hlt
      have : (p : ℝ) ^ 3 < L ^ 3 := pow_lt_pow_left₀ hlt (by positivity) (by norm_num)
      linarith
    calc (K : ℝ) ≤ (N : ℝ) / (p : ℝ) ^ 2 := hK_le
      _ ≤ (N : ℝ) / L ^ 2 := div_le_div_of_nonneg_left hN_pos.le (by positivity)
          (pow_le_pow_left₀ hL_pos.le hp_ge_L 2)
      _ ≤ ((N : ℝ) * Real.log (N : ℝ)) / L ^ 2 :=
          div_le_div_of_nonneg_right (le_mul_of_one_le_right hN_pos.le hlog_ge1) (by positivity)
      _ = L ^ 3 / L ^ 2 := by rw [hL3]
      _ = L := by field_simp
  have hbound_real : (Erdos156.minMaximalSidonSet N : ℝ) ≤ 100 * L := by
    have h1 : (Erdos156.minMaximalSidonSet N : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hmin_le
    have h2 : (A.card : ℝ) ≤ (p : ℝ) + 2 + 2 * (K : ℝ) := by exact_mod_cast hA_card
    linarith
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg hL_pos.le]
  exact hbound_real

end OMA

theorem OMA.solution : type_of% @Erdos156.erdos_156.variants.ruzsa_upper_bound :=
  OMA.ruzsa_upper_bound_proof
