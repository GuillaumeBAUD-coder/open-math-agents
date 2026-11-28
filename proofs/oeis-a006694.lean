import OMAStatements.S_oeis_a006694
open ZMod
namespace OMA.S_oeis_a006694
abbrev Z (m:ℕ) := ZMod (3^(m+1))
lemma o : orderOf (2:ZMod 3) = 2 := orderOf_eq_prime (by decide) (by decide)
lemma C {u m:ℕ} (h:¬3∣u) : Nat.Coprime u (3^m) := Nat.prime_three.coprime_pow_of_not_dvd h
lemma B {n z:ℕ} (hz:z≠0) (h:z<3^n) : padicValNat 3 z < n :=
  (Nat.pow_lt_pow_iff_right (by decide:1<3)).mp
    (lt_of_le_of_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero hz) pow_padicValNat_dvd) h)
lemma O (m:ℕ) : orderOf (2:Z m) = 2*3^m := by
  have e : 2∣orderOf (2:Z m) := by
    have dv : 3∣3^(m+1) := dvd_pow_self 3 (by omega)
    have ch := ZMod.castHom dv (ZMod 3)
    have h := orderOf_map_dvd ch.toMonoidHom (2:Z m)
    have h2 : ch.toMonoidHom (2:Z m) = 2 := map_ofNat ch 2
    rwa [h2, o] at h
  have f : orderOf ((2:Z m)^2) = 3^m := by
    have h := orderOf_one_add_mul_prime Nat.prime_three (by decide) 1 (by decide) m
    have q : (1+((3:ℕ):Z m)*((1:ℤ):Z m)) = (2:Z m)^2 := by ring
    rwa [q] at h
  rw [orderOf_pow' _ two_ne_zero, Nat.gcd_eq_right e] at f
  omega
lemma E (m u w:ℕ) (hu:¬3∣u) (hw:¬3∣w) :
    ∃ k, (w:Z m) = 2^k*(u:ZMod _) := by
  set g : (Z m)ˣ := unitOfCoprime 2 (C (by decide)) with hg
  have v : (g:Z m) = 2 := by simp [hg]
  have t : Subgroup.zpowers g = ⊤ := Subgroup.eq_top_of_card_eq _ (by
    rw [Nat.card_zpowers, ← orderOf_units, v, O, Nat.card_eq_fintype_card,
      card_units_eq_totient, Nat.totient_prime_pow Nat.prime_three (by omega)]
    simp [Nat.mul_comm])
  set U := unitOfCoprime u (C hu) with hU
  set W := unitOfCoprime w (C hw) with hW
  have q : W*U⁻¹∈Submonoid.powers g := by simp [mem_powers_iff_mem_zpowers, t]
  obtain ⟨k, hk⟩ := q
  beta_reduce at hk
  have j : W = g^k*U := by rw [hk, inv_mul_cancel_right]
  exact ⟨k, by simpa [hU, hW, v] using congrArg Units.val j⟩
lemma K (n N:ℕ) (hN:N = 3^n) :
    Nat.card (Quot (fun x y : {x:ZMod N//x≠0} => SameCoset _ x.1 y.1)) = n := by
  subst hN
  have : NeZero (3^n) := ⟨pow_ne_zero n (by decide)⟩
  have z0 (x:{x:ZMod (3^n)//x≠0}) : x.1.val≠0 := (val_ne_zero x.1).mpr x.2
  have lt (x:{x:ZMod (3^n)//x≠0}) : padicValNat 3 x.1.val < n :=
    B (z0 x) (val_lt x.1)
  let f : Quot (fun x y : {x:ZMod (3^n)//x≠0} => SameCoset _ x.1 y.1) → Fin n :=
    Quot.lift (fun x => ⟨padicValNat 3 x.1.val, lt x⟩) (by
      rintro x y ⟨k, hk⟩
      have e : padicValNat 3 y.1.val = padicValNat 3 x.1.val := by
        have x0 : x.1.val≠0 := (val_ne_zero x.1).mpr x.2
        have y0 : y.1.val≠0 := (val_ne_zero y.1).mpr y.2
        have md : y.1.val≡2^k*x.1.val[MOD 3^n] := by
          rw [← natCast_eq_natCast_iff]; push_cast; rw [natCast_zmod_val, natCast_zmod_val, hk]
        have ky (j:ℕ) (hj:j≤n) : 3^j∣y.1.val↔3^j∣x.1.val := by
          have hm := md.of_dvd (pow_dvd_pow 3 hj)
          rw [hm.dvd_iff dvd_rfl]
          exact (Nat.Coprime.pow j k (by decide)).dvd_mul_left
        have xn := B x0 (val_lt x.1)
        have yn := B y0 (val_lt y.1)
        exact le_antisymm ((padicValNat_dvd_iff_le x0).mp ((ky _ yn.le).mp pow_padicValNat_dvd))
          ((padicValNat_dvd_iff_le y0).mp ((ky _ xn.le).mpr pow_padicValNat_dvd))
      exact Fin.ext e.symm)
  have bj : Function.Bijective f := by
    constructor
    · intro p q pq
      obtain ⟨x, rfl⟩ := Quot.exists_rep p
      obtain ⟨y, rfl⟩ := Quot.exists_rep q
      have hv : padicValNat 3 x.1.val = padicValNat 3 y.1.val := congrArg Fin.val pq
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n:=n) (by have := lt x; omega)
      have sp (z:ℕ) (hz:z≠0) : ∃ u, z = 3^padicValNat 3 z*u∧¬3∣u := by
        rw [← Nat.factorization_def z Nat.prime_three]
        exact ⟨_, (Nat.ordProj_mul_ordCompl_eq_self z 3).symm,
          Nat.not_dvd_ordCompl Nat.prime_three hz⟩
      obtain ⟨u, hu, hu3⟩ := sp _ (z0 x)
      obtain ⟨w, hw, hw3⟩ := sp _ (z0 y)
      rw [← hv] at hw
      obtain ⟨k, hk⟩ := E m u w hu3 hw3
      exact Quot.sound ⟨k, by
        rw [← natCast_zmod_val x.1, ← natCast_zmod_val y.1, hu, hw, hv]
        push_cast at ⊢
        rw [hk]
        ring⟩
    · intro i
      have pw : 3^i.val < 3^n := Nat.pow_lt_pow_right (by decide) i.2
      have hv : ((3^i.val:ℕ):ZMod (3^n)).val = 3^i.val := val_natCast_of_lt pw
      have ne : ((3^i.val:ℕ):ZMod (3^n))≠0 :=
        (val_ne_zero _).mp (by rw [hv]; exact pow_ne_zero _ (by decide))
      exact ⟨Quot.mk _ ⟨_, ne⟩, Fin.ext (show padicValNat 3 ((3^i.val:ℕ):ZMod (3^n)).val = i.val from by
        rw [hv]; exact padicValNat.prime_pow _)⟩
  rw [Nat.card_eq_of_bijective f bj]
  simp
end OMA.S_oeis_a006694
theorem OMA.solution : type_of% @OMA.S_oeis_a006694.main := by
  intro n
  have o : (3^n)%2 = 1 := by simp [Nat.pow_mod]
  have p : 0 < 3^n := by positivity
  exact OMA.S_oeis_a006694.K n (2*((3^n-1)/2)+1) (by omega)
