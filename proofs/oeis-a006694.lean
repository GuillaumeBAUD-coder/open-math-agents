import OMAStatements.S_oeis_a006694

/-!
# A006694: `a ((3^n - 1) / 2) = n`

Modulo `3^n`, the orbit of a nonzero residue `x` under multiplication by `2` is determined by the
exact power of `3` dividing `x`, and every exponent `v < n` occurs.  So the orbits are indexed by
`Fin n`.

* Multiplication by `2^k` preserves the power of `3`, since `2` is coprime to `3`.
* `2` generates the units modulo `3^n`: `4 = 1 + 3` has order `3^(n-1)` and `2` has even order
  (it already has order `2` modulo `3`), so `2` has order `2 * 3^(n-1) = φ(3^n)`.  Writing
  `x = 3^v u` and `y = 3^v w` with `u`, `w` prime to `3`, some power of `2` carries `u` to `w`.
-/

namespace OMA.S_oeis_a006694

lemma orderOf_two_zmod_three : orderOf (2 : ZMod 3) = 2 :=
  orderOf_eq_prime (by decide) (by decide)

lemma orderOf_two_zmod (m : ℕ) : orderOf (2 : ZMod (3 ^ (m + 1))) = 2 * 3 ^ m := by
  have heven : 2 ∣ orderOf (2 : ZMod (3 ^ (m + 1))) := by
    have hd : 3 ∣ 3 ^ (m + 1) := dvd_pow_self 3 (by omega)
    have h := orderOf_map_dvd (ZMod.castHom hd (ZMod 3)).toMonoidHom (2 : ZMod (3 ^ (m + 1)))
    have h2 : (ZMod.castHom hd (ZMod 3)).toMonoidHom (2 : ZMod (3 ^ (m + 1))) = 2 :=
      map_ofNat (ZMod.castHom hd (ZMod 3)) 2
    rwa [h2, orderOf_two_zmod_three] at h
  have h4 : orderOf ((2 : ZMod (3 ^ (m + 1))) ^ 2) = 3 ^ m := by
    have h := ZMod.orderOf_one_add_mul_prime (p := 3) Nat.prime_three (by decide) 1
      (by decide) m
    have e : (1 + ((3 : ℕ) : ZMod (3 ^ (m + 1))) * ((1 : ℤ) : ZMod (3 ^ (m + 1))))
        = (2 : ZMod (3 ^ (m + 1))) ^ 2 := by
      push_cast
      ring
    rwa [e] at h
  rw [orderOf_pow' _ two_ne_zero, Nat.gcd_eq_right heven] at h4
  have := Nat.div_mul_cancel heven
  omega

lemma coprime_three_pow {u m : ℕ} (hu : ¬ 3 ∣ u) : Nat.Coprime u (3 ^ m) :=
  Nat.Coprime.pow_right m ((Nat.prime_three.coprime_iff_not_dvd.mpr hu).symm)

/-- Every residue prime to `3` is a power of `2` times any other one, modulo `3^(m+1)`. -/
lemma exists_two_pow (m u w : ℕ) (hu : ¬ 3 ∣ u) (hw : ¬ 3 ∣ w) :
    ∃ k : ℕ, (w : ZMod (3 ^ (m + 1))) = 2 ^ k * (u : ZMod (3 ^ (m + 1))) := by
  have h2 : Nat.Coprime 2 (3 ^ (m + 1)) := coprime_three_pow (by decide)
  set g : (ZMod (3 ^ (m + 1)))ˣ := ZMod.unitOfCoprime 2 h2 with hg
  have hgval : (g : ZMod (3 ^ (m + 1))) = 2 := by
    rw [hg, ZMod.coe_unitOfCoprime]
    norm_num
  have hord : orderOf g = 2 * 3 ^ m := by
    rw [← orderOf_units, hgval, orderOf_two_zmod]
  have hcard : Nat.card (ZMod (3 ^ (m + 1)))ˣ = 2 * 3 ^ m := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime_pow Nat.prime_three (by omega)]
    simp [Nat.mul_comm]
  have htop : Subgroup.zpowers g = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hord, hcard]
  set U := ZMod.unitOfCoprime u (coprime_three_pow (m := m + 1) hu) with hU
  set W := ZMod.unitOfCoprime w (coprime_three_pow (m := m + 1) hw) with hW
  have hmem : W * U⁻¹ ∈ Submonoid.powers g := by
    rw [mem_powers_iff_mem_zpowers, htop]
    trivial
  obtain ⟨k, hk⟩ := hmem
  refine ⟨k, ?_⟩
  have hk' : g ^ k = W * U⁻¹ := hk
  have : W = g ^ k * U := by rw [hk', inv_mul_cancel_right]
  have := congrArg (fun z : (ZMod (3 ^ (m + 1)))ˣ => (z : ZMod (3 ^ (m + 1)))) this
  simpa [hU, hW, hgval] using this

/-- The power of `3` in a nonzero residue is the same for `x` and `2^k x`. -/
lemma padicValNat_val_two_pow_mul (n k : ℕ) (x y : ZMod (3 ^ n)) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : y = 2 ^ k * x) : padicValNat 3 y.val = padicValNat 3 x.val := by
  have : NeZero (3 ^ n) := ⟨pow_ne_zero n (by decide)⟩
  have hx0 : x.val ≠ 0 := (ZMod.val_ne_zero x).mpr hx
  have hy0 : y.val ≠ 0 := (ZMod.val_ne_zero y).mpr hy
  have hmod : y.val ≡ 2 ^ k * x.val [MOD 3 ^ n] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, h]
  have key : ∀ j, j ≤ n → (3 ^ j ∣ y.val ↔ 3 ^ j ∣ x.val) := by
    intro j hj
    have hm := hmod.of_dvd (pow_dvd_pow 3 hj)
    rw [hm.dvd_iff dvd_rfl]
    have hc : Nat.Coprime (3 ^ j) (2 ^ k) :=
      Nat.Coprime.pow j k (by decide)
    exact hc.dvd_mul_left
  have hlt : ∀ z : ℕ, z ≠ 0 → z < 3 ^ n → padicValNat 3 z < n := by
    intro z hz hzn
    have hle : 3 ^ padicValNat 3 z ≤ z := Nat.le_of_dvd (Nat.pos_of_ne_zero hz) pow_padicValNat_dvd
    exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 3)).mp (lt_of_le_of_lt hle hzn)
  have hxn := hlt _ hx0 (ZMod.val_lt x)
  have hyn := hlt _ hy0 (ZMod.val_lt y)
  apply le_antisymm
  · exact (padicValNat_dvd_iff_le hx0).mp ((key _ hyn.le).mp pow_padicValNat_dvd)
  · exact (padicValNat_dvd_iff_le hy0).mp ((key _ hxn.le).mpr pow_padicValNat_dvd)

lemma card_cosets (n N : ℕ) (hN : N = 3 ^ n) :
    Nat.card (Quot (fun x y : {x : ZMod N // x ≠ 0} => SameCoset N x.1 y.1)) = n := by
  subst hN
  have : NeZero (3 ^ n) := ⟨pow_ne_zero n (by decide)⟩
  have hx0 : ∀ x : {x : ZMod (3 ^ n) // x ≠ 0}, x.1.val ≠ 0 :=
    fun x => (ZMod.val_ne_zero x.1).mpr x.2
  have hlt : ∀ x : {x : ZMod (3 ^ n) // x ≠ 0}, padicValNat 3 x.1.val < n := by
    intro x
    have hle : 3 ^ padicValNat 3 x.1.val ≤ x.1.val :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero (hx0 x)) pow_padicValNat_dvd
    exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 3)).mp
      (lt_of_le_of_lt hle (ZMod.val_lt x.1))
  let f : Quot (fun x y : {x : ZMod (3 ^ n) // x ≠ 0} => SameCoset (3 ^ n) x.1 y.1) → Fin n :=
    Quot.lift (fun x => ⟨padicValNat 3 x.1.val, hlt x⟩) (by
      rintro x y ⟨k, hk⟩
      exact Fin.ext (padicValNat_val_two_pow_mul n k x.1 y.1 x.2 y.2 hk).symm)
  have hf : Function.Bijective f := by
    constructor
    · intro p q
      induction p using Quot.ind with | _ x => ?_
      induction q using Quot.ind with | _ y => ?_
      intro hpq
      have hv : padicValNat 3 x.1.val = padicValNat 3 y.1.val := congrArg Fin.val hpq
      apply Quot.sound
      have hn : n ≠ 0 := by
        have := hlt x
        omega
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      have split : ∀ z : ℕ, z ≠ 0 → ∃ u, z = 3 ^ padicValNat 3 z * u ∧ ¬ 3 ∣ u := by
        intro z hz
        obtain ⟨u, hu⟩ : 3 ^ padicValNat 3 z ∣ z := pow_padicValNat_dvd
        refine ⟨u, hu, ?_⟩
        rintro ⟨t, ht⟩
        apply pow_succ_padicValNat_not_dvd (p := 3) hz
        refine ⟨t, ?_⟩
        rw [pow_succ, mul_assoc, ← ht]
        exact hu
      obtain ⟨u, hu, hu3⟩ := split _ (hx0 x)
      obtain ⟨w, hw, hw3⟩ := split _ (hx0 y)
      rw [← hv] at hw
      obtain ⟨k, hk⟩ := exists_two_pow m u w hu3 hw3
      refine ⟨k, ?_⟩
      have ex : x.1 = ((3 ^ padicValNat 3 x.1.val * u : ℕ) : ZMod (3 ^ (m + 1))) := by
        rw [← hu, ZMod.natCast_zmod_val]
      have ey : y.1 = ((3 ^ padicValNat 3 x.1.val * w : ℕ) : ZMod (3 ^ (m + 1))) := by
        rw [← hw, ZMod.natCast_zmod_val]
      generalize padicValNat 3 x.1.val = v at ex ey
      rw [ex, ey]
      push_cast at hk ⊢
      rw [hk]
      ring
    · intro i
      have hpow : 3 ^ i.val < 3 ^ n := Nat.pow_lt_pow_right (by decide) i.2
      have hval : ((3 ^ i.val : ℕ) : ZMod (3 ^ n)).val = 3 ^ i.val :=
        ZMod.val_natCast_of_lt hpow
      have hne : ((3 ^ i.val : ℕ) : ZMod (3 ^ n)) ≠ 0 := by
        intro h
        rw [h, ZMod.val_zero] at hval
        exact pow_ne_zero i.val (by decide : (3 : ℕ) ≠ 0) hval.symm
      refine ⟨Quot.mk _ ⟨_, hne⟩, Fin.ext ?_⟩
      show padicValNat 3 ((3 ^ i.val : ℕ) : ZMod (3 ^ n)).val = i.val
      rw [hval]
      exact padicValNat.prime_pow i.val
  rw [Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Fintype.card_fin]

end OMA.S_oeis_a006694

theorem OMA.solution : type_of% @OMA.S_oeis_a006694.main := by
  intro n
  refine OMA.S_oeis_a006694.card_cosets n _ ?_
  have hodd : (3 ^ n) % 2 = 1 := by rw [Nat.pow_mod]; simp
  have hpos : 0 < 3 ^ n := pow_pos (by decide) n
  omega
