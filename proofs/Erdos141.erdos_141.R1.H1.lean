import OMAReductions.R_Erdos141_erdos_141_R1

namespace OMA.Erdos141Cert

private def powModAux : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, _, acc => acc
  | fuel + 1, a, k, m, acc =>
    if k = 0 then acc
    else powModAux fuel ((a * a) % m) (k / 2) m (if k % 2 = 1 then (acc * a) % m else acc)

private def powMod (a k m : ℕ) : ℕ :=
  powModAux 400 (a % m) k m (1 % m)

private lemma powModAux_eq (m : ℕ) (hm : 1 < m) :
    ∀ (fuel a k acc : ℕ), k < 2 ^ fuel → acc < m →
      powModAux fuel a k m acc = (acc * a ^ k) % m := by
  intro fuel
  induction fuel with
  | zero =>
    intro a k acc hk hacc
    have hk0 : k = 0 := by simpa using hk
    subst hk0
    simp [powModAux, Nat.mod_eq_of_lt hacc]
  | succ fuel ih =>
    intro a k acc hk hacc
    rw [powModAux]
    split_ifs with hk0 hmod
    · subst hk0; simp [Nat.mod_eq_of_lt hacc]
    · have hk2 : k / 2 < 2 ^ fuel := by
        rw [Nat.pow_succ] at hk; omega
      have hacc' : (acc * a) % m < m := Nat.mod_lt _ (by omega)
      rw [ih ((a * a) % m) (k / 2) ((acc * a) % m) hk2 hacc']
      have hk_eq : k = 2 * (k / 2) + 1 := by omega
      have h1 : (acc * a % m) * (a * a % m) ^ (k / 2) % m = acc * a * (a * a) ^ (k / 2) % m := by
        rw [Nat.mul_mod (acc * a % m), Nat.mod_mod, Nat.pow_mod (a * a % m), Nat.mod_mod,
            ← Nat.pow_mod, ← Nat.mul_mod]
      rw [h1]
      congr 1
      conv_rhs => rw [hk_eq, pow_add, pow_one, pow_mul, sq]
      ring
    · have hk2 : k / 2 < 2 ^ fuel := by
        rw [Nat.pow_succ] at hk; omega
      rw [ih ((a * a) % m) (k / 2) acc hk2 hacc]
      have hk_eq : k = 2 * (k / 2) := by omega
      have h1 : acc * (a * a % m) ^ (k / 2) % m = acc * (a * a) ^ (k / 2) % m := by
        rw [Nat.mul_mod acc, Nat.pow_mod (a * a % m), Nat.mod_mod, ← Nat.pow_mod, ← Nat.mul_mod]
      rw [h1]
      congr 1
      conv_rhs => rw [hk_eq, pow_mul, sq]

private lemma powMod_eq {a k m : ℕ} (hm : 1 < m) (hk : k < 2 ^ 400) :
    powMod a k m = a ^ k % m := by
  rw [powMod, powModAux_eq m hm 400 (a % m) k (1 % m) hk (Nat.mod_lt _ (by omega))]
  rw [Nat.mod_eq_of_lt hm, one_mul, Nat.pow_mod, Nat.mod_mod, ← Nat.pow_mod]

private lemma not_prime_of_dvd {m f : ℕ} (hf1 : 1 < f) (hfm : f < m) (hdvd : m % f = 0) :
    ¬ m.Prime := by
  intro hp
  rcases hp.eq_one_or_self_of_dvd f (Nat.dvd_of_mod_eq_zero hdvd) with rfl | rfl <;> omega

private lemma not_prime_of_fermat {m : ℕ} (hm : 2 < m) (hpow : powMod 2 (m - 1) m ≠ 1)
    (hlt : m < 2 ^ 400) : ¬ m.Prime := by
  intro hp
  have : Fact m.Prime := ⟨hp⟩
  have h20 : (2 : ZMod m) ≠ 0 := by
    intro h
    have hd : m ∣ 2 := (ZMod.natCast_eq_zero_iff 2 m).mp (by simpa using h)
    have hle : m ≤ 2 := Nat.le_of_dvd (by omega) hd
    omega
  have hz : ((2 ^ (m - 1) : ℕ) : ZMod m) = ((1 : ℕ) : ZMod m) := by
    simpa [Nat.cast_pow] using ZMod.pow_card_sub_one_eq_one h20
  have hmod : 2 ^ (m - 1) % m = 1 := by
    have hme : 2 ^ (m - 1) ≡ 1 [MOD m] := (ZMod.natCast_eq_natCast_iff _ _ _).mp hz
    rwa [Nat.ModEq, Nat.mod_eq_of_lt (by omega : 1 < m)] at hme
  rw [powMod_eq (by omega) (by omega)] at hpow
  exact hpow hmod

private lemma pow_dvd_of_prime_pow_dvd {q e k ord : ℕ} (hq : q.Prime) (he : 1 ≤ e)
    (hk_dvd : q ^ e ∣ k) (hord_dvd : ord ∣ k) (hnot : ¬ ord ∣ k / q) :
    q ^ e ∣ ord := by
  by_contra hndvd
  have hord_pos : 0 < ord := by
    by_contra h0
    have : ord = 0 := by omega
    rw [this] at hndvd
    exact hndvd (dvd_zero _)
  have hk_pos : 0 < k := by
    by_contra h0
    have : k = 0 := by omega
    rw [this] at hnot
    exact hnot (by simp)
  have hvp_lt : ord.factorization q < e := by
    by_contra hge
    have hge' : e ≤ ord.factorization q := by omega
    exact hndvd ((Nat.Prime.pow_dvd_iff_le_factorization hq (by omega)).mpr hge')
  have hkq_pos : 0 < k / q := by
    have : q ∣ k := dvd_trans (dvd_pow_self q (by omega)) hk_dvd
    exact Nat.div_pos (Nat.le_of_dvd hk_pos this) hq.pos
  apply hnot
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p m hp hpm
  by_cases hpq : p = q
  · subst hpq
    have hm_le : m ≤ ord.factorization p := (Nat.Prime.pow_dvd_iff_le_factorization hp (by omega)).mp hpm
    have hm_le_e1 : m ≤ e - 1 := by omega
    have hqe1 : p ^ (e - 1) ∣ k / p := by
      have hq_dvd : p ^ e = p * p ^ (e - 1) := by
        conv_lhs => rw [← Nat.sub_add_cancel he, Nat.pow_succ']
      rw [hq_dvd] at hk_dvd
      rcases hk_dvd with ⟨t, ht⟩
      refine ⟨t, ?_⟩
      rw [ht, mul_assoc, Nat.mul_div_right _ hq.pos]
    exact dvd_trans (Nat.pow_dvd_pow p hm_le_e1) hqe1
  · have hpm_k : p ^ m ∣ k := dvd_trans hpm hord_dvd
    have hcop : Nat.Coprime (p ^ m) q :=
      Nat.Coprime.pow_left m ((Nat.coprime_primes hp hq).mpr hpq)
    have hq_dvd_k : q ∣ k := dvd_trans (dvd_pow_self q (by omega)) hk_dvd
    have : p ^ m ∣ q * (k / q) := by rwa [Nat.mul_div_cancel' hq_dvd_k]
    exact hcop.dvd_of_dvd_mul_left this

private lemma prod_dvd_of_nodup {ord : ℕ} :
    ∀ (qs : List (ℕ × ℕ × ℕ)),
      (qs.map Prod.fst).Nodup →
      (∀ x ∈ qs, x.1.Prime ∧ x.1 ^ x.2.1 ∣ ord) →
      (qs.map (fun x => x.1 ^ x.2.1)).prod ∣ ord := by
  intro qs
  induction qs with
  | nil => intro _ _; simp
  | cons x xs ih =>
    intro hnd hqs
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    have h1 := hqs x (by simp)
    have h2 : (xs.map (fun y => y.1 ^ y.2.1)).prod ∣ ord :=
      ih hnd.2 (fun y hy => hqs y (by simp [hy]))
    have hcop : Nat.Coprime (x.1 ^ x.2.1) (xs.map (fun y => y.1 ^ y.2.1)).prod := by
      rw [Nat.coprime_list_prod_right_iff]
      intro z hz
      simp only [List.mem_map] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      have hne : x.1 ≠ y.1 := fun h => hnd.1 ⟨y, hy, h.symm⟩
      have hy_p := (hqs y (by simp [hy])).1
      exact ((Nat.coprime_primes h1.1 hy_p).mpr hne).pow x.2.1 y.2.1
    simp only [List.map_cons, List.prod_cons]
    exact hcop.mul_dvd_of_dvd_of_dvd h1.2 h2

private lemma pocklington_step {N F R a : ℕ} (hN : 1 < N) (hNlt : N < 2 ^ 400)
    (hFR : N - 1 = F * R) (hF_gt : N < F * F)
    (ha1 : powMod a (N - 1) N = 1)
    (qs : List (ℕ × ℕ × ℕ))
    (hnd : (qs.map Prod.fst).Nodup)
    (hF_prod : F = (qs.map (fun x => x.1 ^ x.2.1)).prod)
    (hqs : ∀ x ∈ qs, x.1.Prime ∧ 1 ≤ x.2.1 ∧
      ((powMod a ((N - 1) / x.1) N + N - 1) * x.2.2) % N = 1) :
    N.Prime := by
  by_contra hnp
  set r := N.minFac
  have hr_prime : r.Prime := Nat.minFac_prime (by omega)
  have hr_dvd : r ∣ N := Nat.minFac_dvd N
  have hr_sq : r * r ≤ N := by simpa [sq] using Nat.minFac_sq_le_self (by omega) hnp
  have : Fact r.Prime := ⟨hr_prime⟩
  have ha1_mod : a ^ (N - 1) % N = 1 := by
    rwa [powMod_eq hN (by omega)] at ha1
  have ha1_ge : 1 ≤ a ^ (N - 1) := by
    by_contra h0
    have : a ^ (N - 1) = 0 := by omega
    rw [this] at ha1_mod
    simp at ha1_mod
  have har_pow : (a : ZMod r) ^ (N - 1) = 1 := by
    have hdiv : N ∣ a ^ (N - 1) - 1 := by
      refine ⟨a ^ (N - 1) / N, ?_⟩
      have hda := Nat.div_add_mod (a ^ (N - 1)) N
      rw [ha1_mod] at hda
      omega
    have hr_div : r ∣ a ^ (N - 1) - 1 := dvd_trans hr_dvd hdiv
    have hmod : (a ^ (N - 1) - 1) % r = 0 := Nat.mod_eq_zero_of_dvd hr_div
    have h1 : a ^ (N - 1) ≡ 1 [MOD r] := by
      rw [Nat.ModEq, show a ^ (N - 1) = (a ^ (N - 1) - 1) + 1 by omega,
          Nat.add_mod, hmod, zero_add, Nat.mod_mod]
    rw [← ZMod.natCast_eq_natCast_iff] at h1
    simpa [Nat.cast_pow] using h1
  have ha_ne0 : (a : ZMod r) ≠ 0 := by
    intro h0
    have hN1 : 1 ≤ N - 1 := by
      have hF0 : F ≠ 0 := by intro h; rw [h] at hF_gt; simp at hF_gt
      have hR0 : R ≠ 0 := by intro h; rw [h, mul_zero] at hFR; omega
      rw [hFR]; exact Nat.mul_pos (Nat.pos_of_ne_zero hF0) (Nat.pos_of_ne_zero hR0)
    rw [← Nat.sub_add_cancel hN1, pow_succ, h0, mul_zero] at har_pow
    exact one_ne_zero har_pow.symm
  have hord_dvd_r : orderOf (a : ZMod r) ∣ r - 1 := by
    rw [orderOf_dvd_iff_pow_eq_one]
    exact ZMod.pow_card_sub_one_eq_one ha_ne0
  have hord_dvd_N1 : orderOf (a : ZMod r) ∣ N - 1 := by
    rwa [orderOf_dvd_iff_pow_eq_one]
  have hF_dvd_ord : F ∣ orderOf (a : ZMod r) := by
    rw [hF_prod]
    apply prod_dvd_of_nodup qs hnd
    intro x hx
    obtain ⟨hx_p, hx_e, hx_inv⟩ := hqs x hx
    refine ⟨hx_p, ?_⟩
    have hx_dvd : x.1 ^ x.2.1 ∣ N - 1 := by
      rw [hFR]
      refine dvd_trans ?_ (dvd_mul_right F R)
      rw [hF_prod]
      exact List.dvd_prod (List.mem_map.mpr ⟨x, hx, rfl⟩)
    apply pow_dvd_of_prime_pow_dvd hx_p hx_e hx_dvd hord_dvd_N1
    intro hdiv_q
    rw [orderOf_dvd_iff_pow_eq_one] at hdiv_q
    have hpow_q : a ^ ((N - 1) / x.1) % N = powMod a ((N - 1) / x.1) N :=
      (powMod_eq hN (lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))).symm
    have hdvd_cast : ∀ t : ℕ, ((t % N : ℕ) : ZMod r) = (t : ZMod r) := by
      intro t
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr ((Nat.mod_modEq t N).of_dvd hr_dvd)
    have hmod_r : (((powMod a ((N - 1) / x.1) N + N - 1) * x.2.2 : ℕ) : ZMod r) = (1 : ZMod r) := by
      have h1 := congrArg (fun t : ℕ => (t : ZMod r)) hx_inv
      rw [hdvd_cast] at h1
      simpa using h1
    have hpow_z : ((powMod a ((N - 1) / x.1) N : ℕ) : ZMod r) = (a : ZMod r) ^ ((N - 1) / x.1) := by
      rw [← hpow_q, hdvd_cast]
      simp [Nat.cast_pow]
    have hsub1 : (powMod a ((N - 1) / x.1) N + N - 1 : ℕ) =
        powMod a ((N - 1) / x.1) N + (N - 1) := by omega
    have hN_r : (N : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff N r).mpr hr_dvd
    rw [Nat.cast_mul, hsub1, Nat.cast_add, Nat.cast_sub (by omega), hN_r, zero_sub, hpow_z,
        hdiv_q] at hmod_r
    simp at hmod_r
  have hF_dvd_r1 : F ∣ r - 1 := dvd_trans hF_dvd_ord hord_dvd_r
  have hr_gt_F : F < r := by
    have hF_pos : 0 < F := by
      by_contra h0; have : F = 0 := by omega
      rw [this] at hF_gt; simp at hF_gt
    have hr1_pos : 0 < r - 1 := Nat.sub_pos_of_lt hr_prime.one_lt
    have := Nat.le_of_dvd hr1_pos hF_dvd_r1
    omega
  have : F * F < r * r := Nat.mul_self_lt_mul_self hr_gt_F
  omega

private def lucasUVAux : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ × ℕ × ℕ
  | 0, _, _, _, _, _, m => (0, 2 % m, 1 % m)
  | fuel + 1, P, D, Q, inv2, k, m =>
    if k = 0 then (0, 2 % m, 1 % m)
    else
      let res := lucasUVAux fuel P D Q inv2 (k / 2) m
      let u := res.1
      let v := res.2.1
      let qk := res.2.2
      let u2 := (u * v) % m
      let v2 := (v * v + 2 * m - 2 * qk) % m
      let q2 := (qk * qk) % m
      if k % 2 = 0 then (u2, v2, q2)
      else
        let u21 := ((P * u2 + v2) * inv2) % m
        let v21 := ((D * u2 + P * v2) * inv2) % m
        let q21 := (q2 * Q) % m
        (u21, v21, q21)

private def lucasU (P D Q k m : ℕ) : ℕ :=
  (lucasUVAux 400 P D Q ((m + 1) / 2) k m).1

private structure QuadExt (r : ℕ) (D : ZMod r) where
  x : ZMod r
  y : ZMod r

private lemma QuadExt.ext_iff {r : ℕ} {D : ZMod r} (a b : QuadExt r D) :
    a = b ↔ a.x = b.x ∧ a.y = b.y := by
  cases a; cases b; simp

private lemma QuadExt.ext {r : ℕ} {D : ZMod r} {a b : QuadExt r D}
    (hx : a.x = b.x) (hy : a.y = b.y) : a = b :=
  (QuadExt.ext_iff a b).mpr ⟨hx, hy⟩

private instance (r : ℕ) (D : ZMod r) : Zero (QuadExt r D) := ⟨⟨0, 0⟩⟩
private instance (r : ℕ) (D : ZMod r) : One (QuadExt r D) := ⟨⟨1, 0⟩⟩
private instance (r : ℕ) (D : ZMod r) : Add (QuadExt r D) := ⟨fun a b => ⟨a.x + b.x, a.y + b.y⟩⟩
private instance (r : ℕ) (D : ZMod r) : Neg (QuadExt r D) := ⟨fun a => ⟨-a.x, -a.y⟩⟩
private instance (r : ℕ) (D : ZMod r) : Mul (QuadExt r D) :=
  ⟨fun a b => ⟨a.x * b.x + D * a.y * b.y, a.x * b.y + a.y * b.x⟩⟩

@[simp] private lemma quadExt_zero_x (r : ℕ) (D : ZMod r) : (0 : QuadExt r D).x = 0 := rfl
@[simp] private lemma quadExt_zero_y (r : ℕ) (D : ZMod r) : (0 : QuadExt r D).y = 0 := rfl
@[simp] private lemma quadExt_one_x (r : ℕ) (D : ZMod r) : (1 : QuadExt r D).x = 1 := rfl
@[simp] private lemma quadExt_one_y (r : ℕ) (D : ZMod r) : (1 : QuadExt r D).y = 0 := rfl
@[simp] private lemma quadExt_add_x {r : ℕ} {D : ZMod r} (a b : QuadExt r D) : (a + b).x = a.x + b.x := rfl
@[simp] private lemma quadExt_add_y {r : ℕ} {D : ZMod r} (a b : QuadExt r D) : (a + b).y = a.y + b.y := rfl
@[simp] private lemma quadExt_neg_x {r : ℕ} {D : ZMod r} (a : QuadExt r D) : (-a).x = -a.x := rfl
@[simp] private lemma quadExt_neg_y {r : ℕ} {D : ZMod r} (a : QuadExt r D) : (-a).y = -a.y := rfl
@[simp] private lemma quadExt_mul_x {r : ℕ} {D : ZMod r} (a b : QuadExt r D) :
    (a * b).x = a.x * b.x + D * a.y * b.y := rfl
@[simp] private lemma quadExt_mul_y {r : ℕ} {D : ZMod r} (a b : QuadExt r D) :
    (a * b).y = a.x * b.y + a.y * b.x := rfl

private instance (r : ℕ) (D : ZMod r) : CommRing (QuadExt r D) where
  add_assoc a b c := by apply QuadExt.ext <;> simp [add_assoc]
  zero_add a := by apply QuadExt.ext <;> simp
  add_zero a := by apply QuadExt.ext <;> simp
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel a := by apply QuadExt.ext <;> simp
  add_comm a b := by apply QuadExt.ext <;> simp [add_comm]
  left_distrib a b c := by apply QuadExt.ext <;> simp <;> ring
  right_distrib a b c := by apply QuadExt.ext <;> simp <;> ring
  zero_mul a := by apply QuadExt.ext <;> simp
  mul_zero a := by apply QuadExt.ext <;> simp
  mul_assoc a b c := by apply QuadExt.ext <;> simp <;> ring
  one_mul a := by apply QuadExt.ext <;> simp
  mul_one a := by apply QuadExt.ext <;> simp
  mul_comm a b := by apply QuadExt.ext <;> simp <;> ring

private lemma quadExt_charP {r : ℕ} (D : ZMod r) (hr : r.Prime) :
    CharP (QuadExt r D) r := by
  constructor
  intro n
  have h1 : (n : QuadExt r D) = ⟨(n : ZMod r), 0⟩ := by
    induction n with
    | zero => apply QuadExt.ext <;> simp
    | succ n ih =>
      rw [Nat.cast_succ, ih]
      apply QuadExt.ext <;> simp
  rw [h1, QuadExt.ext_iff]
  simp [ZMod.natCast_eq_zero_iff]

private lemma lucasUV_spec {r : ℕ} [Fact r.Prime] (hr : r.Prime) (hr_odd : r ≠ 2)
    (P Q D : ZMod r) (hD : D = P ^ 2 - 4 * Q) :
    ∀ k : ℕ, ∃ U V : ZMod r,
      (⟨P / 2, (1 : ZMod r) / 2⟩ : QuadExt r D) ^ k = ⟨V / 2, U / 2⟩ ∧
      (⟨P / 2, (-1 : ZMod r) / 2⟩ : QuadExt r D) ^ k = ⟨V / 2, (-U) / 2⟩ ∧
      (⟨V / 2, U / 2⟩ : QuadExt r D) * ⟨V / 2, (-U) / 2⟩ = ⟨Q ^ k, 0⟩ := by
  have h2ne0 : (2 : ZMod r) ≠ 0 := by
    intro h
    have hd : r ∣ 2 := (ZMod.natCast_eq_zero_iff 2 r).mp (by simpa using h)
    have hle : r ≤ 2 := Nat.le_of_dvd (by omega) hd
    have := hr.two_le
    omega
  intro k
  induction k with
  | zero =>
    refine ⟨0, 2, ?_, ?_, ?_⟩
    · apply QuadExt.ext <;> simp [div_self h2ne0]
    · apply QuadExt.ext <;> simp [div_self h2ne0]
    · apply QuadExt.ext <;> simp [div_self h2ne0]
  | succ k ih =>
    obtain ⟨U, V, hα, hβ, hQ⟩ := ih
    refine ⟨(P * U + V) / 2, (D * U + P * V) / 2, ?_, ?_, ?_⟩
    · rw [pow_succ, hα]
      apply QuadExt.ext
      · change V / 2 * (P / 2) + D * (U / 2) * ((1 : ZMod r) / 2) = (D * U + P * V) / 2 / 2
        field_simp [h2ne0]; ring
      · change V / 2 * ((1 : ZMod r) / 2) + U / 2 * (P / 2) = (P * U + V) / 2 / 2
        field_simp [h2ne0]; ring
    · rw [pow_succ, hβ]
      apply QuadExt.ext <;> dsimp <;> field_simp [h2ne0] <;> ring
    · have hmul : (⟨(D * U + P * V) / 2 / 2, (P * U + V) / 2 / 2⟩ : QuadExt r D) *
          ⟨(D * U + P * V) / 2 / 2, (-((P * U + V) / 2)) / 2⟩ =
          (⟨V / 2, U / 2⟩ * ⟨V / 2, (-U) / 2⟩) * (⟨P / 2, (1 : ZMod r) / 2⟩ * ⟨P / 2, (-1 : ZMod r) / 2⟩) := by
        apply QuadExt.ext <;> dsimp <;> field_simp [h2ne0] <;> ring
      rw [hmul, hQ]
      apply QuadExt.ext
      · dsimp; rw [hD, pow_succ]; field_simp [h2ne0]; ring
      · dsimp; ring

private lemma lucasUVAux_sound {m r : ℕ} [Fact r.Prime] (hr : r.Prime) (hr_odd : r ≠ 2) (hr_dvd : r ∣ m)
    (hm_odd : m % 2 = 1) (P_n D_n Q_n : ℕ)
    (hD : (D_n : ZMod r) = (P_n : ZMod r) ^ 2 - 4 * (Q_n : ZMod r)) :
    ∀ (fuel k : ℕ), k < 2 ^ fuel →
      let res := lucasUVAux fuel P_n D_n Q_n ((m + 1) / 2) k m
      res.1 < m ∧ res.2.1 < m ∧ res.2.2 < m ∧
      (⟨(P_n : ZMod r) / 2, (1 : ZMod r) / 2⟩ : QuadExt r D_n) ^ k =
        ⟨(res.2.1 : ZMod r) / 2, (res.1 : ZMod r) / 2⟩ ∧
      (res.2.2 : ZMod r) = (Q_n : ZMod r) ^ k := by
  have hm_pos : 0 < m := by omega
  have hm_ge3 : 3 ≤ m := by
    have := hr.two_le
    have := Nat.le_of_dvd hm_pos hr_dvd
    omega
  have h2ne0 : (2 : ZMod r) ≠ 0 := by
    intro h
    have hd : r ∣ 2 := (ZMod.natCast_eq_zero_iff 2 r).mp (by simpa using h)
    have hle : r ≤ 2 := Nat.le_of_dvd (by omega) hd
    have := hr.two_le
    omega
  have hinv2 : (((m + 1) / 2 : ℕ) : ZMod r) = (1 : ZMod r) / 2 := by
    have h1 : 2 * ((m + 1) / 2) = m + 1 := by omega
    have h2 : (2 : ZMod r) * (((m + 1) / 2 : ℕ) : ZMod r) = 1 := by
      have := congrArg (fun t : ℕ => (t : ZMod r)) h1
      have hm_r : (m : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff m r).mpr hr_dvd
      simpa [hm_r] using this
    exact (eq_div_iff h2ne0).mpr (by rw [mul_comm]; exact h2)
  have hmod_r : ∀ t : ℕ, ((t % m : ℕ) : ZMod r) = (t : ZMod r) := by
    intro t
    rcases hr_dvd with ⟨c, hc⟩
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mpr
    rw [Nat.ModEq]
    have h2 := congrArg (· % r) (Nat.mod_add_div t m)
    rw [hc, mul_assoc, Nat.add_mul_mod_self_left] at h2
    rwa [← hc] at h2
  intro fuel
  induction fuel with
  | zero =>
    intro k hk
    have hk0 : k = 0 := by simpa using hk
    subst hk0
    simp only [lucasUVAux]
    refine ⟨hm_pos, Nat.mod_lt _ hm_pos, Nat.mod_lt _ hm_pos, ?_, ?_⟩
    · apply QuadExt.ext <;> simp [Nat.mod_eq_of_lt (by omega : 2 < m), div_self h2ne0]
    · simp [Nat.mod_eq_of_lt (by omega : 1 < m)]
  | succ fuel ih =>
    intro k hk
    rw [lucasUVAux]
    split_ifs with hk0 hkeven
    · subst hk0
      refine ⟨hm_pos, Nat.mod_lt _ hm_pos, Nat.mod_lt _ hm_pos, ?_, ?_⟩
      · rw [hmod_r]; apply QuadExt.ext <;> simp [div_self h2ne0]
      · rw [hmod_r]; simp
    · have hk2 : k / 2 < 2 ^ fuel := by rw [Nat.pow_succ] at hk; omega
      obtain ⟨hu_lt, hv_lt, hq_lt, hpow, hqk⟩ := ih (k / 2) hk2
      set res := lucasUVAux fuel P_n D_n Q_n ((m + 1) / 2) (k / 2) m
      refine ⟨Nat.mod_lt _ hm_pos, Nat.mod_lt _ hm_pos, Nat.mod_lt _ hm_pos, ?_, ?_⟩
      · have hk_eq : k = (k / 2) * 2 := by omega
        rw [hk_eq, pow_mul, hpow, sq]
        have hsub : res.2.1 * res.2.1 + 2 * m - 2 * res.2.2 =
            res.2.1 * res.2.1 + (2 * m - 2 * res.2.2) := by omega
        rw [hmod_r, hmod_r, hsub, Nat.cast_add, Nat.cast_sub (by omega)]
        have hm_r : (m : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff m r).mpr hr_dvd
        obtain ⟨U', V', hα', hβ', hQ'⟩ := lucasUV_spec hr hr_odd P_n Q_n D_n hD (k / 2)
        have hUV : (U' : ZMod r) = res.1 ∧ (V' : ZMod r) = res.2.1 := by
          have := hα'.symm.trans hpow
          rw [QuadExt.ext_iff] at this
          exact ⟨mul_right_cancel₀ (inv_ne_zero h2ne0) (by simpa [div_eq_mul_inv] using this.2),
                 mul_right_cancel₀ (inv_ne_zero h2ne0) (by simpa [div_eq_mul_inv] using this.1)⟩
        have hQ_eq : (V' / 2) * (V' / 2) + (D_n : ZMod r) * (U' / 2) * ((-U') / 2) = (Q_n : ZMod r) ^ (k / 2) := by
          exact congrArg QuadExt.x hQ'
        rw [hUV.1, hUV.2] at hQ_eq
        apply QuadExt.ext
        · simp only [Nat.cast_mul, hm_r, mul_zero, zero_sub, hqk]
          dsimp
          field_simp [h2ne0] at hQ_eq ⊢
          linear_combination -hQ_eq
        · simp only [Nat.cast_mul]; dsimp; field_simp [h2ne0]; ring
      · have hk_eq : k = 2 * (k / 2) := by omega
        rw [hmod_r, Nat.cast_mul, hqk]
        conv_rhs => rw [hk_eq, pow_mul, sq]
        ring
    · have hk2 : k / 2 < 2 ^ fuel := by rw [Nat.pow_succ] at hk; omega
      obtain ⟨hu_lt, hv_lt, hq_lt, hpow, hqk⟩ := ih (k / 2) hk2
      set res := lucasUVAux fuel P_n D_n Q_n ((m + 1) / 2) (k / 2) m
      refine ⟨Nat.mod_lt _ hm_pos, Nat.mod_lt _ hm_pos, Nat.mod_lt _ hm_pos, ?_, ?_⟩
      · have hk_eq : k = (k / 2) * 2 + 1 := by omega
        rw [hk_eq, pow_add, pow_one, pow_mul, hpow, sq]
        have hsub : res.2.1 * res.2.1 + 2 * m - 2 * res.2.2 =
            res.2.1 * res.2.1 + (2 * m - 2 * res.2.2) := by omega
        have hm_r : (m : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff m r).mpr hr_dvd
        obtain ⟨U', V', hα', hβ', hQ'⟩ := lucasUV_spec hr hr_odd P_n Q_n D_n hD (k / 2)
        have hUV : (U' : ZMod r) = res.1 ∧ (V' : ZMod r) = res.2.1 := by
          have := hα'.symm.trans hpow
          rw [QuadExt.ext_iff] at this
          exact ⟨mul_right_cancel₀ (inv_ne_zero h2ne0) (by simpa [div_eq_mul_inv] using this.2),
                 mul_right_cancel₀ (inv_ne_zero h2ne0) (by simpa [div_eq_mul_inv] using this.1)⟩
        have hQ_eq : (V' / 2) * (V' / 2) + (D_n : ZMod r) * (U' / 2) * ((-U') / 2) = (Q_n : ZMod r) ^ (k / 2) := by
          exact congrArg QuadExt.x hQ'
        rw [hUV.1, hUV.2] at hQ_eq
        rw [hmod_r, hmod_r]
        simp only [Nat.cast_mul, Nat.cast_add, hinv2]
        rw [hmod_r, hmod_r, hsub, Nat.cast_add, Nat.cast_sub (by omega)]
        simp only [Nat.cast_mul, hm_r, mul_zero, zero_sub, hqk]
        apply QuadExt.ext <;> dsimp <;> field_simp [h2ne0] at hQ_eq ⊢
        · linear_combination -(P_n : ZMod r) * hQ_eq
        · linear_combination -hQ_eq
      · have hk_eq : k = 2 * (k / 2) + 1 := by omega
        rw [hmod_r, Nat.cast_mul, hmod_r, Nat.cast_mul, hqk]
        conv_rhs => rw [hk_eq, pow_add, pow_one, pow_mul, sq]
        ring

private lemma morrison_step {N F R P D_n Q_n D_inv Q_inv : ℕ}
    (hN : 1 < N) (hN_odd : N % 2 = 1) (hNlt : N + 1 < 2 ^ 400)
    (hFR : N + 1 = F * R) (hF_gt : N < (F - 1) * (F - 1))
    (hD_mod : (D_n : ℤ) ≡ (P : ℤ) ^ 2 - 4 * (Q_n : ℤ) [ZMOD N])
    (hD_inv : (D_n * D_inv) % N = 1)
    (hQ_inv : (Q_n * Q_inv) % N = 1)
    (hU0 : lucasU P D_n Q_n (N + 1) N = 0)
    (qs : List (ℕ × ℕ × ℕ))
    (hnd : (qs.map Prod.fst).Nodup)
    (hF_prod : F = (qs.map (fun x => x.1 ^ x.2.1)).prod)
    (hqs : ∀ x ∈ qs, x.1.Prime ∧ 1 ≤ x.2.1 ∧
      (lucasU P D_n Q_n ((N + 1) / x.1) N * x.2.2) % N = 1) :
    N.Prime := by
  by_contra hnp
  set r := N.minFac
  have hr_prime : r.Prime := Nat.minFac_prime (by omega)
  have hr_dvd : r ∣ N := Nat.minFac_dvd N
  have hr_sq : r * r ≤ N := by simpa [sq] using Nat.minFac_sq_le_self (by omega) hnp
  have hr_odd : r ≠ 2 := by
    intro h2; rw [h2] at hr_dvd; omega
  have : Fact r.Prime := ⟨hr_prime⟩
  have h2ne0 : (2 : ZMod r) ≠ 0 := by
    intro h
    have hd : r ∣ 2 := (ZMod.natCast_eq_zero_iff 2 r).mp (by simpa using h)
    have hle : r ≤ 2 := Nat.le_of_dvd (by omega) hd
    have := hr_prime.two_le
    omega
  have hD : (D_n : ZMod r) = (P : ZMod r) ^ 2 - 4 * (Q_n : ZMod r) := by
    have hd1 : (D_n : ℤ) ≡ (P : ℤ) ^ 2 - 4 * (Q_n : ℤ) [ZMOD r] := hD_mod.of_dvd (Int.natCast_dvd_natCast.mpr hr_dvd)
    rw [← ZMod.intCast_eq_intCast_iff] at hd1
    simpa using hd1
  have hD_ne0 : (D_n : ZMod r) ≠ 0 := by
    intro h0
    have hdvd_cast : ((D_n * D_inv % N : ℕ) : ZMod r) = ((D_n * D_inv : ℕ) : ZMod r) := by
      rcases hr_dvd with ⟨c, hc⟩
      apply (ZMod.natCast_eq_natCast_iff _ _ _).mpr
      rw [Nat.ModEq]
      have h2 := congrArg (· % r) (Nat.mod_add_div (D_n * D_inv) N)
      rw [hc, mul_assoc, Nat.add_mul_mod_self_left] at h2
      rwa [← hc] at h2
    have h1 := congrArg (fun t : ℕ => (t : ZMod r)) hD_inv
    rw [hdvd_cast, Nat.cast_mul, h0, zero_mul] at h1
    exact (zero_ne_one : (0 : ZMod r) ≠ 1) (by simpa using h1)
  have hQ_ne0 : (Q_n : ZMod r) ≠ 0 := by
    intro h0
    have hdvd_cast : ((Q_n * Q_inv % N : ℕ) : ZMod r) = ((Q_n * Q_inv : ℕ) : ZMod r) := by
      rcases hr_dvd with ⟨c, hc⟩
      apply (ZMod.natCast_eq_natCast_iff _ _ _).mpr
      rw [Nat.ModEq]
      have h2 := congrArg (· % r) (Nat.mod_add_div (Q_n * Q_inv) N)
      rw [hc, mul_assoc, Nat.add_mul_mod_self_left] at h2
      rwa [← hc] at h2
    have h1 := congrArg (fun t : ℕ => (t : ZMod r)) hQ_inv
    rw [hdvd_cast, Nat.cast_mul, h0, zero_mul] at h1
    exact (zero_ne_one : (0 : ZMod r) ≠ 1) (by simpa using h1)
  set α : QuadExt r D_n := ⟨(P : ZMod r) / 2, (1 : ZMod r) / 2⟩
  set β : QuadExt r D_n := ⟨(P : ZMod r) / 2, (-1 : ZMod r) / 2⟩
  have hαβ : α * β = ⟨(Q_n : ZMod r), 0⟩ := by
    apply QuadExt.ext <;> simp only [α, β]
    · change (P : ZMod r) / 2 * ((P : ZMod r) / 2) + (D_n : ZMod r) * (1 / 2) * (-1 / 2) = (Q_n : ZMod r)
      rw [hD]; field_simp [h2ne0]; ring
    · change (P : ZMod r) / 2 * (-1 / 2) + 1 / 2 * ((P : ZMod r) / 2) = 0
      ring
  set βinv : QuadExt r D_n := ⟨(Q_n : ZMod r)⁻¹, 0⟩ * α
  have hβ_inv : β * βinv = 1 := by
    calc β * βinv = ⟨(Q_n : ZMod r)⁻¹, 0⟩ * (α * β) := by simp [βinv]; ring
      _ = ⟨(Q_n : ZMod r)⁻¹, 0⟩ * ⟨(Q_n : ZMod r), 0⟩ := by rw [hαβ]
      _ = 1 := by apply QuadExt.ext <;> simp [inv_mul_cancel₀ hQ_ne0]
  set γ : QuadExt r D_n := α * βinv
  have hγ_inv : γ * (β * ⟨(Q_n : ZMod r)⁻¹, 0⟩ * β) = 1 := by
    -- Actually simpler: α * (⟨Q⁻¹, 0⟩ * β) = 1!
    have hα_inv : α * (⟨(Q_n : ZMod r)⁻¹, 0⟩ * β) = 1 := by
      calc α * (⟨(Q_n : ZMod r)⁻¹, 0⟩ * β) = ⟨(Q_n : ZMod r)⁻¹, 0⟩ * (α * β) := by ring
        _ = ⟨(Q_n : ZMod r)⁻¹, 0⟩ * ⟨(Q_n : ZMod r), 0⟩ := by rw [hαβ]
        _ = 1 := by apply QuadExt.ext <;> simp [inv_mul_cancel₀ hQ_ne0]
    calc γ * (β * ⟨(Q_n : ZMod r)⁻¹, 0⟩ * β) = (α * (βinv * β)) * (⟨(Q_n : ZMod r)⁻¹, 0⟩ * β) := by
          simp [γ]; ring
      _ = α * (⟨(Q_n : ZMod r)⁻¹, 0⟩ * β) := by rw [mul_comm βinv β, hβ_inv, mul_one]
      _ = 1 := hα_inv
  have hγ_iff : ∀ k : ℕ, k < 2 ^ 400 →
      (γ ^ k = 1 ↔ (lucasU P D_n Q_n k N : ZMod r) = 0) := by
    intro k hk
    have hpow_γ : γ ^ k * β ^ k = α ^ k := by
      rw [← mul_pow]
      have : γ * β = α := by calc γ * β = α * (β * βinv) := by simp [γ]; ring
        _ = α * 1 := by rw [hβ_inv]
        _ = α := mul_one _
      rw [this]
    have hαβ_eq : γ ^ k = 1 ↔ α ^ k = β ^ k := by
      constructor
      · intro h; rw [← hpow_γ, h, one_mul]
      · intro h
        calc γ ^ k = γ ^ k * (β ^ k * βinv ^ k) := by rw [← mul_pow, hβ_inv, one_pow, mul_one]
          _ = (γ ^ k * β ^ k) * βinv ^ k := by ring
          _ = α ^ k * βinv ^ k := by rw [hpow_γ]
          _ = β ^ k * βinv ^ k := by rw [h]
          _ = 1 := by rw [← mul_pow, hβ_inv, one_pow]
    rw [hαβ_eq]
    obtain ⟨_, _, _, hα_sound, _⟩ := lucasUVAux_sound hr_prime hr_odd hr_dvd hN_odd P D_n Q_n hD 400 k hk
    obtain ⟨U', V', hα', hβ', _⟩ := lucasUV_spec hr_prime hr_odd P Q_n D_n hD k
    have hUV : (U' : ZMod r) = (lucasU P D_n Q_n k N : ZMod r) ∧
        (V' : ZMod r) = ((lucasUVAux 400 P D_n Q_n ((N + 1) / 2) k N).2.1 : ZMod r) := by
      have := hα'.symm.trans hα_sound
      rw [QuadExt.ext_iff] at this
      exact ⟨mul_right_cancel₀ (inv_ne_zero h2ne0) (by simpa [div_eq_mul_inv, lucasU] using this.2),
             mul_right_cancel₀ (inv_ne_zero h2ne0) (by simpa [div_eq_mul_inv] using this.1)⟩
    rw [hα', hβ', hUV.1, QuadExt.ext_iff]
    constructor
    · intro ⟨_, hy⟩
      dsimp at hy
      have hy2 : ((lucasU P D_n Q_n k N : ZMod r) / 2) * 2 =
          (-((lucasU P D_n Q_n k N : ZMod r)) / 2) * 2 := congrArg (· * 2) hy
      rw [div_mul_cancel₀ _ h2ne0, neg_div, neg_mul, div_mul_cancel₀ _ h2ne0] at hy2
      -- U = -U -> 2*U = 0 -> U = 0
      have h2u : (2 : ZMod r) * (lucasU P D_n Q_n k N : ZMod r) = 0 := by
        linear_combination hy2
      exact (mul_eq_zero.mp h2u).resolve_left h2ne0
    · intro hu0
      simp [hu0]
  have hγ_r : γ ^ (r - 1) = 1 ∨ γ ^ (r + 1) = 1 := by
    haveI : CharP (QuadExt r D_n) r := quadExt_charP D_n hr_prime
    have hpow_re : ∀ a : ZMod r, (⟨a, 0⟩ : QuadExt r D_n) ^ r = ⟨a, 0⟩ := by
      intro a
      have : ∀ m : ℕ, (⟨a, 0⟩ : QuadExt r D_n) ^ m = ⟨a ^ m, 0⟩ := by
        intro m; induction m with
        | zero => apply QuadExt.ext <;> simp
        | succ m ih => rw [pow_succ, ih]; apply QuadExt.ext <;> simp [pow_succ]
      rw [this r, ZMod.pow_card]
    have hpow_im : ∀ b : ZMod r,
        (⟨0, b⟩ : QuadExt r D_n) ^ r = ⟨0, b * (D_n : ZMod r) ^ ((r - 1) / 2)⟩ := by
      intro b
      have hr_eq : r = 2 * ((r - 1) / 2) + 1 := by
        have hr_mod : r % 2 = 1 := hr_prime.eq_two_or_odd.resolve_left hr_odd
        omega
      have hsq : ∀ m : ℕ, (⟨0, b⟩ : QuadExt r D_n) ^ (2 * m) = ⟨b ^ (2 * m) * (D_n : ZMod r) ^ m, 0⟩ := by
        intro m; induction m with
        | zero => apply QuadExt.ext <;> simp
        | succ m ih =>
          rw [mul_add, mul_one, pow_add, ih, sq]
          apply QuadExt.ext <;> simp [pow_add, pow_mul] <;> ring
      conv_lhs => arg 2; rw [hr_eq]
      rw [pow_add, pow_one, hsq]
      apply QuadExt.ext <;> dsimp
      · simp
      · simp only [mul_zero, add_zero]
        rw [mul_right_comm, ← pow_succ, ← hr_eq, ZMod.pow_card]
    have hα_split : α = ⟨(P : ZMod r) / 2, 0⟩ + ⟨0, 1 / 2⟩ := by apply QuadExt.ext <;> simp [α]
    have hβ_split : β = ⟨(P : ZMod r) / 2, 0⟩ + ⟨0, -1 / 2⟩ := by apply QuadExt.ext <;> simp [β]
    have hα_r : α ^ r = ⟨(P : ZMod r) / 2, ((1 : ZMod r) / 2) * (D_n : ZMod r) ^ ((r - 1) / 2)⟩ := by
      rw [hα_split, add_pow_char, hpow_re, hpow_im]; apply QuadExt.ext <;> dsimp <;> ring
    have hβ_r : β ^ r = ⟨(P : ZMod r) / 2, ((-1 : ZMod r) / 2) * (D_n : ZMod r) ^ ((r - 1) / 2)⟩ := by
      rw [hβ_split, add_pow_char, hpow_re, hpow_im]; apply QuadExt.ext <;> dsimp <;> ring
    have hε_sq : ((D_n : ZMod r) ^ ((r - 1) / 2)) ^ 2 = 1 := by
      have hr_mod : r % 2 = 1 := hr_prime.eq_two_or_odd.resolve_left hr_odd
      rw [← pow_mul, show ((r - 1) / 2) * 2 = r - 1 by omega]
      exact ZMod.pow_card_sub_one_eq_one hD_ne0
    rcases sq_eq_one_iff.mp hε_sq with hε1 | hεm1
    · left
      have hα_fix : α ^ r = α := by rw [hα_r, hε1]; apply QuadExt.ext <;> simp [α]
      have hβ_fix : β ^ r = β := by rw [hβ_r, hε1]; apply QuadExt.ext <;> simp [β]
      have hγr_eq : γ ^ r = γ := by
        have h1 : γ ^ r * β ^ r = α ^ r := by
          rw [← mul_pow]; congr 1; calc γ * β = α * (β * βinv) := by simp [γ]; ring
            _ = α := by rw [hβ_inv, mul_one]
        rw [hα_fix, hβ_fix] at h1
        calc γ ^ r = γ ^ r * (β * βinv) := by rw [hβ_inv, mul_one]
          _ = (γ ^ r * β) * βinv := by ring
          _ = α * βinv := by rw [h1]
          _ = γ := rfl
      have hr1 : 1 ≤ r := hr_prime.pos
      calc γ ^ (r - 1) = γ ^ (r - 1) * (γ * (β * ⟨(Q_n : ZMod r)⁻¹, 0⟩ * β)) := by rw [hγ_inv, mul_one]
        _ = (γ ^ (r - 1) * γ) * (β * ⟨(Q_n : ZMod r)⁻¹, 0⟩ * β) := by ring
        _ = γ ^ r * (β * ⟨(Q_n : ZMod r)⁻¹, 0⟩ * β) := by rw [← pow_succ, Nat.sub_add_cancel hr1]
        _ = γ * (β * ⟨(Q_n : ZMod r)⁻¹, 0⟩ * β) := by rw [hγr_eq]
        _ = 1 := hγ_inv
    · right
      have hα_swap : α ^ r = β := by rw [hα_r, hεm1]; apply QuadExt.ext <;> [simp [β]; (simp [β]; ring)]
      have hβ_swap : β ^ r = α := by rw [hβ_r, hεm1]; apply QuadExt.ext <;> [simp [α]; (simp [α]; ring)]
      have hαβ_r1 : α ^ (r + 1) = β ^ (r + 1) := by
        rw [pow_succ, pow_succ, hα_swap, hβ_swap, mul_comm]
      calc γ ^ (r + 1) = γ ^ (r + 1) * (β ^ (r + 1) * βinv ^ (r + 1)) := by
            rw [← mul_pow, hβ_inv, one_pow, mul_one]
        _ = (γ ^ (r + 1) * β ^ (r + 1)) * βinv ^ (r + 1) := by ring
        _ = α ^ (r + 1) * βinv ^ (r + 1) := by
            congr 1; rw [← mul_pow]; congr 1
            calc γ * β = α * (β * βinv) := by simp [γ]; ring
              _ = α := by rw [hβ_inv, mul_one]
        _ = β ^ (r + 1) * βinv ^ (r + 1) := by rw [hαβ_r1]
        _ = 1 := by rw [← mul_pow, hβ_inv, one_pow]
  have hord_dvd_N1 : orderOf γ ∣ N + 1 := by
    rw [orderOf_dvd_iff_pow_eq_one, hγ_iff (N + 1) (by omega), hU0]
    simp
  have hF_dvd_ord : F ∣ orderOf γ := by
    rw [hF_prod]
    apply prod_dvd_of_nodup qs hnd
    intro x hx
    obtain ⟨hx_p, hx_e, hx_inv⟩ := hqs x hx
    refine ⟨hx_p, ?_⟩
    have hx_dvd : x.1 ^ x.2.1 ∣ N + 1 := by
      rw [hFR]
      refine dvd_trans ?_ (dvd_mul_right F R)
      rw [hF_prod]
      exact List.dvd_prod (List.mem_map.mpr ⟨x, hx, rfl⟩)
    apply pow_dvd_of_prime_pow_dvd hx_p hx_e hx_dvd hord_dvd_N1
    intro hdiv_q
    rw [orderOf_dvd_iff_pow_eq_one, hγ_iff ((N + 1) / x.1) (lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))] at hdiv_q
    have hdvd_cast : ((lucasU P D_n Q_n ((N + 1) / x.1) N * x.2.2 % N : ℕ) : ZMod r) =
        ((lucasU P D_n Q_n ((N + 1) / x.1) N * x.2.2 : ℕ) : ZMod r) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr ((Nat.mod_modEq _ N).of_dvd hr_dvd)
    have h1 := congrArg (fun t : ℕ => (t : ZMod r)) hx_inv
    rw [hdvd_cast, Nat.cast_mul, hdiv_q, zero_mul] at h1
    exact (zero_ne_one : (0 : ZMod r) ≠ 1) (by simpa using h1)
  have hF_le : F ≤ r + 1 := by
    rcases hγ_r with h1 | h2
    · have hdvd : F ∣ r - 1 := dvd_trans hF_dvd_ord (orderOf_dvd_iff_pow_eq_one.mpr h1)
      have hr1_pos : 0 < r - 1 := Nat.sub_pos_of_lt hr_prime.one_lt
      have := Nat.le_of_dvd hr1_pos hdvd
      omega
    · have hdvd : F ∣ r + 1 := dvd_trans hF_dvd_ord (orderOf_dvd_iff_pow_eq_one.mpr h2)
      exact Nat.le_of_dvd (by omega) hdvd
  have hF1_le : F - 1 ≤ r := by omega
  have : (F - 1) * (F - 1) ≤ r * r := Nat.mul_le_mul hF1_le hF1_le
  omega

private lemma lt_two_pow_400_of_lt {n : ℕ} (h : n < 10 ^ 100) : n < 2 ^ 400 := by
  have h1 : 10 ^ 100 < 2 ^ 200 * 2 ^ 200 := by decide
  have h2 : 2 ^ 200 * 2 ^ 200 = 2 ^ 400 := by rw [← pow_add]
  omega

private def checkGapItem (p idx w : ℕ) : Bool :=
  let m := p + idx
  if w = 0 then
    decide (2 < m) && (powMod 2 (m - 1) m != 1) && decide (m < 10 ^ 100)
  else
    decide (1 < w) && decide (w < m) && (m % w == 0)

private lemma checkGapItem_sound (p idx w : ℕ) (h : checkGapItem p idx w = true) :
    ¬ (p + idx).Prime := by
  simp only [checkGapItem] at h
  split_ifs at h with hw
  · simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne] at h
    exact not_prime_of_fermat h.1.1 h.1.2 (lt_two_pow_400_of_lt h.2)
  · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    exact not_prime_of_dvd h.1.1 h.1.2 h.2

private def checkGapList (p idx : ℕ) : List ℕ → Bool
  | [] => true
  | w :: ws => checkGapItem p idx w && checkGapList p (idx + 1) ws

private lemma checkGapList_sound (p : ℕ) : ∀ (ws : List ℕ) (idx : ℕ),
    checkGapList p idx ws = true →
    ∀ j < ws.length, ¬ (p + idx + j).Prime := by
  intro ws
  induction ws with
  | nil => intro idx _ j hj; simp at hj
  | cons w ws ih =>
    intro idx h j hj
    simp only [checkGapList, Bool.and_eq_true] at h
    cases j with
    | zero => simpa using checkGapItem_sound p idx w h.1
    | succ j' =>
      have hj' : j' < ws.length := by simpa using hj
      rw [show p + idx + (j' + 1) = p + (idx + 1) + j' by omega]
      exact ih (idx + 1) h.2 j' hj'



private lemma p_base_2 : Nat.Prime 2 := by decide
private lemma p_base_3 : Nat.Prime 3 := by decide
private lemma p_base_5 : Nat.Prime 5 := by decide
private lemma p_base_7 : Nat.Prime 7 := by decide
private lemma p_base_11 : Nat.Prime 11 := by decide
private lemma p_base_13 : Nat.Prime 13 := by decide
private lemma p_base_17 : Nat.Prime 17 := by decide
private lemma p_base_19 : Nat.Prime 19 := by decide
private lemma p_base_23 : Nat.Prime 23 := by decide
private lemma p_base_29 : Nat.Prime 29 := by decide
private lemma p_base_37 : Nat.Prime 37 := by decide
private lemma p_base_43 : Nat.Prime 43 := by decide
private lemma p_base_47 : Nat.Prime 47 := by decide
private lemma p_base_53 : Nat.Prime 53 := by decide
private lemma p_base_59 : Nat.Prime 59 := by decide
private lemma p_base_71 : Nat.Prime 71 := by decide
private lemma p_base_73 : Nat.Prime 73 := by decide
private lemma p_base_83 : Nat.Prime 83 := by decide
private lemma p_base_89 : Nat.Prime 89 := by decide

set_option maxRecDepth 4096 in
private lemma p_cert_0 : Nat.Prime 101 := by
  refine pocklington_step (F := 25) (R := 4) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(5, 2, 72)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_base_5, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_1 : Nat.Prime 103 := by
  refine pocklington_step (F := 17) (R := 6) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(17, 1, 18)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_base_17, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_2 : Nat.Prime 107 := by
  refine pocklington_step (F := 53) (R := 2) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(53, 1, 36)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_base_53, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_3 : Nat.Prime 127 := by
  refine pocklington_step (F := 63) (R := 2) (a := 3) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(3, 2, 6), (7, 1, 85)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ⟨p_base_3, by decide, by rfl⟩
  · exact ⟨p_base_7, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_4 : Nat.Prime 131 := by
  refine pocklington_step (F := 13) (R := 10) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(13, 1, 110)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_base_13, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_5 : Nat.Prime 139 := by
  refine pocklington_step (F := 23) (R := 6) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(23, 1, 64)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_base_23, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_6 : Nat.Prime 173 := by
  refine pocklington_step (F := 43) (R := 4) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(43, 1, 150)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_base_43, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_7 : Nat.Prime 181 := by
  refine pocklington_step (F := 45) (R := 4) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(3, 2, 104), (5, 1, 103)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ⟨p_base_3, by decide, by rfl⟩
  · exact ⟨p_base_5, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_8 : Nat.Prime 233 := by
  refine pocklington_step (F := 29) (R := 8) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(29, 1, 53)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_base_29, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_9 : Nat.Prime 263 := by
  refine pocklington_step (F := 131) (R := 2) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(131, 1, 88)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_4, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_10 : Nat.Prime 277 := by
  refine pocklington_step (F := 23) (R := 12) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(23, 1, 60)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_base_23, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_11 : Nat.Prime 293 := by
  refine pocklington_step (F := 73) (R := 4) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(73, 1, 254)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_base_73, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_12 : Nat.Prime 401 := by
  refine pocklington_step (F := 25) (R := 16) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(5, 2, 305)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_base_5, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_13 : Nat.Prime 499 := by
  refine pocklington_step (F := 83) (R := 6) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(83, 1, 301)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_base_83, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_14 : Nat.Prime 587 := by
  refine pocklington_step (F := 293) (R := 2) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(293, 1, 196)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_11, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_15 : Nat.Prime 613 := by
  refine pocklington_step (F := 153) (R := 4) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(3, 2, 182), (17, 1, 197)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ⟨p_base_3, by decide, by rfl⟩
  · exact ⟨p_base_17, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_16 : Nat.Prime 641 := by
  refine pocklington_step (F := 640) (R := 1) (a := 3) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(2, 7, 320), (5, 1, 632)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ⟨p_base_2, by decide, by rfl⟩
  · exact ⟨p_base_5, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_17 : Nat.Prime 647 := by
  refine pocklington_step (F := 323) (R := 2) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(17, 1, 534), (19, 1, 591)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ⟨p_base_17, by decide, by rfl⟩
  · exact ⟨p_base_19, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_18 : Nat.Prime 691 := by
  refine pocklington_step (F := 115) (R := 6) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(5, 1, 211), (23, 1, 404)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ⟨p_base_5, by decide, by rfl⟩
  · exact ⟨p_base_23, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_19 : Nat.Prime 751 := by
  refine pocklington_step (F := 125) (R := 6) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(5, 3, 732)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_base_5, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_20 : Nat.Prime 809 := by
  refine pocklington_step (F := 101) (R := 8) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(101, 1, 717)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_0, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_21 : Nat.Prime 877 := by
  refine pocklington_step (F := 73) (R := 12) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(73, 1, 251)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_base_73, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_22 : Nat.Prime 1087 := by
  refine pocklington_step (F := 181) (R := 6) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(181, 1, 1018)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_7, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_23 : Nat.Prime 1103 := by
  refine pocklington_step (F := 551) (R := 2) (a := 3) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(19, 1, 335), (29, 1, 454)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ⟨p_base_19, by decide, by rfl⟩
  · exact ⟨p_base_29, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_24 : Nat.Prime 1109 := by
  refine pocklington_step (F := 277) (R := 4) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(277, 1, 74)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_10, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_25 : Nat.Prime 1283 := by
  refine pocklington_step (F := 641) (R := 2) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(641, 1, 428)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_16, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_26 : Nat.Prime 1597 := by
  refine pocklington_step (F := 133) (R := 12) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(7, 1, 1140), (19, 1, 799)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ⟨p_base_7, by decide, by rfl⟩
  · exact ⟨p_base_19, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_27 : Nat.Prime 1787 := by
  refine pocklington_step (F := 47) (R := 38) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(47, 1, 356)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_base_47, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_28 : Nat.Prime 2017 := by
  refine pocklington_step (F := 63) (R := 32) (a := 3) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(3, 2, 1246), (7, 1, 682)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ⟨p_base_3, by decide, by rfl⟩
  · exact ⟨p_base_7, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_29 : Nat.Prime 2393 := by
  refine pocklington_step (F := 299) (R := 8) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(13, 1, 2268), (23, 1, 1884)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ⟨p_base_13, by decide, by rfl⟩
  · exact ⟨p_base_23, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_30 : Nat.Prime 2689 := by
  refine pocklington_step (F := 2688) (R := 1) (a := 19) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(2, 7, 1344), (3, 1, 2558), (7, 1, 284)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact ⟨p_base_2, by decide, by rfl⟩
  · exact ⟨p_base_3, by decide, by rfl⟩
  · exact ⟨p_base_7, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_31 : Nat.Prime 6131 := by
  refine pocklington_step (F := 613) (R := 10) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(613, 1, 5256)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_15, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_32 : Nat.Prime 9689 := by
  refine pocklington_step (F := 173) (R := 56) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(173, 1, 3756)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_6, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_33 : Nat.Prime 12263 := by
  refine pocklington_step (F := 6131) (R := 2) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(6131, 1, 4088)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_31, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_34 : Nat.Prime 13309 := by
  refine pocklington_step (F := 1109) (R := 12) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(1109, 1, 13296)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_24, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_35 : Nat.Prime 14627 := by
  refine pocklington_step (F := 7313) (R := 2) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(71, 1, 1662), (103, 1, 9269)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ⟨p_base_71, by decide, by rfl⟩
  · exact ⟨p_cert_1, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_36 : Nat.Prime 15443 := by
  refine pocklington_step (F := 1103) (R := 14) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(1103, 1, 15328)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_23, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_37 : Nat.Prime 23671 := by
  refine pocklington_step (F := 263) (R := 90) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(263, 1, 163)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_9, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_38 : Nat.Prime 23971 := by
  refine pocklington_step (F := 799) (R := 30) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(17, 1, 21610), (47, 1, 249)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ⟨p_base_17, by decide, by rfl⟩
  · exact ⟨p_base_47, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_39 : Nat.Prime 26417 := by
  refine pocklington_step (F := 1651) (R := 16) (a := 3) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(13, 1, 25094), (127, 1, 12328)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ⟨p_base_13, by decide, by rfl⟩
  · exact ⟨p_cert_3, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_40 : Nat.Prime 37489 := by
  refine pocklington_step (F := 781) (R := 48) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(11, 1, 20593), (71, 1, 23110)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ⟨p_base_11, by decide, by rfl⟩
  · exact ⟨p_base_71, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_41 : Nat.Prime 77513 := by
  refine pocklington_step (F := 9689) (R := 8) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(9689, 1, 22190)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_32, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_42 : Nat.Prime 90073 := by
  refine pocklington_step (F := 11259) (R := 8) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(3, 4, 69029), (139, 1, 25219)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ⟨p_base_3, by decide, by rfl⟩
  · exact ⟨p_cert_5, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_43 : Nat.Prime 92269 := by
  refine pocklington_step (F := 2563) (R := 36) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(11, 1, 36383), (233, 1, 42385)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ⟨p_base_11, by decide, by rfl⟩
  · exact ⟨p_cert_8, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_44 : Nat.Prime 168499 := by
  refine pocklington_step (F := 851) (R := 198) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(23, 1, 39508), (37, 1, 55730)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ⟨p_base_23, by decide, by rfl⟩
  · exact ⟨p_base_37, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_45 : Nat.Prime 172751 := by
  refine pocklington_step (F := 691) (R := 250) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(691, 1, 121639)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_18, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_46 : Nat.Prime 191441 := by
  refine pocklington_step (F := 2393) (R := 80) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(2393, 1, 70781)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_29, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_47 : Nat.Prime 292541 := by
  refine pocklington_step (F := 14627) (R := 20) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(14627, 1, 44963)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_35, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_48 : Nat.Prime 360293 := by
  refine pocklington_step (F := 90073) (R := 4) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(90073, 1, 312254)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_42, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_49 : Nat.Prime 382883 := by
  refine pocklington_step (F := 191441) (R := 2) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(191441, 1, 127628)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_46, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_50 : Nat.Prime 492673 := by
  refine pocklington_step (F := 1283) (R := 384) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(1283, 1, 125009)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_25, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_51 : Nat.Prime 511289 := by
  refine pocklington_step (F := 809) (R := 632) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(809, 1, 47570)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_20, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_52 : Nat.Prime 612613 := by
  refine pocklington_step (F := 2431) (R := 252) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(11, 1, 288883), (13, 1, 582810), (17, 1, 93278)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact ⟨p_base_11, by decide, by rfl⟩
  · exact ⟨p_base_13, by decide, by rfl⟩
  · exact ⟨p_base_17, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_53 : Nat.Prime 720653 := by
  refine pocklington_step (F := 2689) (R := 268) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(2689, 1, 31786)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_30, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_54 : Nat.Prime 930157 := by
  refine pocklington_step (F := 77513) (R := 12) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(77513, 1, 702331)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_41, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_55 : Nat.Prime 2161759 := by
  refine pocklington_step (F := 360293) (R := 6) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(360293, 1, 377450)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_48, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_56 : Nat.Prime 4728973 := by
  refine pocklington_step (F := 13589) (R := 348) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(107, 1, 14586), (127, 1, 3774494)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ⟨p_cert_2, by decide, by rfl⟩
  · exact ⟨p_cert_3, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_57 : Nat.Prime 16382297 := by
  refine pocklington_step (F := 292541) (R := 56) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(292541, 1, 6894135)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_47, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_58 : Nat.Prime 19189553 := by
  refine pocklington_step (F := 1199347) (R := 16) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(751, 1, 4433126), (1597, 1, 13343704)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ⟨p_cert_19, by decide, by rfl⟩
  · exact ⟨p_cert_26, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_59 : Nat.Prime 43243117 := by
  refine pocklington_step (F := 514799) (R := 84) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(587, 1, 8846339), (877, 1, 20020276)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ⟨p_cert_14, by decide, by rfl⟩
  · exact ⟨p_cert_21, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_60 : Nat.Prime 60534853 := by
  refine pocklington_step (F := 720653) (R := 84) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(720653, 1, 47882269)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_53, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_61 : Nat.Prime 131058377 := by
  refine pocklington_step (F := 16382297) (R := 8) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(16382297, 1, 57562895)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_57, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_62 : Nat.Prime 159967427 := by
  refine pocklington_step (F := 172751) (R := 926) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(172751, 1, 41258784)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_45, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_63 : Nat.Prime 183577111 := by
  refine pocklington_step (F := 6119237) (R := 30) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(499, 1, 134427660), (12263, 1, 94334592)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ⟨p_cert_13, by decide, by rfl⟩
  · exact ⟨p_cert_33, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_64 : Nat.Prime 335730821 := by
  refine pocklington_step (F := 16786541) (R := 20) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(1087, 1, 119594750), (15443, 1, 82649103)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ⟨p_cert_22, by decide, by rfl⟩
  · exact ⟨p_cert_36, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_65 : Nat.Prime 590027507 := by
  refine pocklington_step (F := 511289) (R := 1154) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(511289, 1, 218654289)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_51, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_66 : Nat.Prime 2359050787 := by
  refine pocklington_step (F := 131058377) (R := 18) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(131058377, 1, 1691911588)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_61, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_67 : Nat.Prime 2635661359 := by
  refine pocklington_step (F := 168499) (R := 15642) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(168499, 1, 1446838804)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_44, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_68 : Nat.Prime 3262224011 := by
  refine pocklington_step (F := 19189553) (R := 170) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(19189553, 1, 97956934)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_58, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_69 : Nat.Prime 3795902063 := by
  refine pocklington_step (F := 382883) (R := 9914) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(382883, 1, 1532700695)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_49, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_70 : Nat.Prime 22829695829 := by
  refine pocklington_step (F := 335730821) (R := 68) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(335730821, 1, 4705137741)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_64, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_71 : Nat.Prime 61405386641 := by
  refine pocklington_step (F := 808817) (R := 75920) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(401, 1, 7446159922), (2017, 1, 54694340368)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ⟨p_cert_12, by decide, by rfl⟩
  · exact ⟨p_cert_28, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_72 : Nat.Prime 189795103151 := by
  refine pocklington_step (F := 3795902063) (R := 50) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(3795902063, 1, 111478983433)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_69, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_73 : Nat.Prime 285161549693 := by
  refine pocklington_step (F := 612613) (R := 465484) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(612613, 1, 78533992807)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_52, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_74 : Nat.Prime 528124563007 := by
  refine pocklington_step (F := 3336521) (R := 158286) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(89, 1, 107347000193), (37489, 1, 18832046160)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ⟨p_base_89, by decide, by rfl⟩
  · exact ⟨p_cert_40, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_75 : Nat.Prime 582536588861 := by
  refine pocklington_step (F := 47207179) (R := 12340) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(1787, 1, 332676391224), (26417, 1, 201832987303)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ⟨p_cert_27, by decide, by rfl⟩
  · exact ⟨p_cert_39, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_76 : Nat.Prime 3495219533167 := by
  refine pocklington_step (F := 582536588861) (R := 6) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(582536588861, 1, 610276426426)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_75, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_77 : Nat.Prime 3572455363121 := by
  refine pocklington_step (F := 4728973) (R := 755440) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(4728973, 1, 1984755175780)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_56, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_78 : Nat.Prime 14134419850597 := by
  refine pocklington_step (F := 11662062583) (R := 1212) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(23671, 1, 4474457509971), (492673, 1, 9856654717779)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ⟨p_cert_37, by decide, by rfl⟩
  · exact ⟨p_cert_50, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_79 : Nat.Prime 15427219380457 := by
  refine pocklington_step (F := 54879263) (R := 281112) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(59, 1, 811643150632), (930157, 1, 501124317731)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ⟨p_base_59, by decide, by rfl⟩
  · exact ⟨p_cert_54, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_80 : Nat.Prime 79933803662777 := by
  refine pocklington_step (F := 159967427) (R := 499688) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(159967427, 1, 77909534175641)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_62, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_81 : Nat.Prime 544896287951143 := by
  refine pocklington_step (F := 319030039) (R := 1707978) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(13309, 1, 198467205195858), (23971, 1, 488537189128978)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ⟨p_cert_34, by decide, by rfl⟩
  · exact ⟨p_cert_38, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_82 : Nat.Prime 1165527773351003 := by
  refine pocklington_step (F := 183577111) (R := 6348982) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(183577111, 1, 97788386481268)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_63, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_83 : Nat.Prime 2575135369222133 := by
  refine pocklington_step (F := 528124563007) (R := 4876) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(528124563007, 1, 106786003600507)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_74, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_84 : Nat.Prime 4859376605767591 := by
  refine pocklington_step (F := 5585490351457) (R := 870) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(92269, 1, 4077973777090106), (60534853, 1, 3950369285857841)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ⟨p_cert_43, by decide, by rfl⟩
  · exact ⟨p_cert_60, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_85 : Nat.Prime 5097516880429559 := by
  refine pocklington_step (F := 189795103151) (R := 26858) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(189795103151, 1, 1914907462955171)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_72, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_86 : Nat.Prime 14619981347353801 := by
  refine pocklington_step (F := 2359050787) (R := 6197400) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(2359050787, 1, 12160287663076540)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_66, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_87 : Nat.Prime 58312519269211093 := by
  refine pocklington_step (F := 4859376605767591) (R := 12) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(4859376605767591, 1, 44115307618074717)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_84, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_88 : Nat.Prime 1863545304792909061 := by
  refine pocklington_step (F := 544896287951143) (R := 3420) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(544896287951143, 1, 1366497088644278769)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_81, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_89 : Nat.Prime 5865121461868259203 := by
  refine pocklington_step (F := 3572455363121) (R := 1641762) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(3572455363121, 1, 3460802355175536046)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_77, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_90 : Nat.Prime 733831205403172013089 := by
  refine pocklington_step (F := 1705272899273) (R := 430330656) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(647, 1, 255485104695563773821), (2635661359, 1, 287682243920249274649)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ⟨p_cert_17, by decide, by rfl⟩
  · exact ⟨p_cert_67, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_91 : Nat.Prime 974736250413007345943 := by
  refine pocklington_step (F := 14134419850597) (R := 68961886) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(14134419850597, 1, 359708224636530337780)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_78, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_92 : Nat.Prime 1975395304598545436017 := by
  refine pocklington_step (F := 93481197362803) (R := 21131472) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(2161759, 1, 651551571932394388416), (43243117, 1, 1269861832938072466931)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ⟨p_cert_55, by decide, by rfl⟩
  · exact ⟨p_cert_59, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_93 : Nat.Prime 1310045520555081872947393 := by
  refine pocklington_step (F := 974736250413007345943) (R := 1344) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(974736250413007345943, 1, 570793830069133077334130)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_91, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_94 : Nat.Prime 1339318016517813805619527 := by
  refine pocklington_step (F := 1975395304598545436017) (R := 678) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(1975395304598545436017, 1, 923284084056555225651832)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_92, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_95 : Nat.Prime 75946695343942045545950611 := by
  refine pocklington_step (F := 5865121461868259203) (R := 12948870) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(5865121461868259203, 1, 47250267131996286617002546)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_89, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_96 : Nat.Prime 6053413019594444547884628917 := by
  refine pocklington_step (F := 1863545304792909061) (R := 3248331556) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(1863545304792909061, 1, 3538458305872572614170904016)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_88, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_97 : Nat.Prime 90778245483882153483569567724259 := by
  refine pocklington_step (F := 74475581897190350119) (R := 1218899445582) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(3262224011, 1, 77050352803863445727813738737982), (22829695829, 1, 2640924868571916928795353963729)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ⟨p_cert_68, by decide, by rfl⟩
  · exact ⟨p_cert_70, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_98 : Nat.Prime 1024734370178869815789881312791361 := by
  refine pocklington_step (F := 17510455214045399851213) (R := 58521286720) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(61405386641, 1, 645639805544040872511256654504586), (285161549693, 1, 905118720743194589378876618969850)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ⟨p_cert_71, by decide, by rfl⟩
  · exact ⟨p_cert_73, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_99 : Nat.Prime 10731686646196985543603831722141297 := by
  refine pocklington_step (F := 74525601709701288497248831403759) (R := 144) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(5097516880429559, 1, 1331321781266853469141992570556193), (14619981347353801, 1, 2587566792639175561074684472971242)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ⟨p_cert_85, by decide, by rfl⟩
  · exact ⟨p_cert_86, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_100 : Nat.Prime 23567721955657194776649723510218140673 := by
  refine pocklington_step (F := 9000663443054413884183985211) (R := 2618442752) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(3495219533167, 1, 14379635667927183283854189591595628328), (2575135369222133, 1, 7821212503536496703242394515925570031)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ⟨p_cert_76, by decide, by rfl⟩
  · exact ⟨p_cert_83, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_101 : Nat.Prime 8373094558265845827516770230329627536146799 := by
  refine pocklington_step (F := 1339318016517813805619527) (R := 6251759817310333474) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(1339318016517813805619527, 1, 5178223221842659679703612611256555290377657)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_94, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_102 : Nat.Prime 11594902353095303515194099337049142451792171 := by
  refine pocklington_step (F := 432980596682838512775074039123) (R := 26779265495790) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(590027507, 1, 9807208768522780531850766614684986852609130), (733831205403172013089, 1, 1301911182536784272352610362371852297998608)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ⟨p_cert_65, by decide, by rfl⟩
  · exact ⟨p_cert_90, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_103 : Nat.Prime 165337136995061861490728657086431249608356451 := by
  refine pocklington_step (F := 90778245483882153483569567724259) (R := 1821329946550) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(90778245483882153483569567724259, 1, 153370661469452957837401717707885007698135750)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_97, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_104 : Nat.Prime 334130122469124376448502703576854973706716799 := by
  refine pocklington_step (F := 6053413019594444547884628917) (R := 55196980841645894) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(6053413019594444547884628917, 1, 181915495314446404925648333593586507870091119)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_96, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_105 : Nat.Prime 472362132581542660756039516449996870043763098571 := by
  refine pocklington_step (F := 1310045520555081872947393) (R := 360569251350439491132490) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(1310045520555081872947393, 1, 406825892391744503310519113415479346407666765669)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_93, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_106 : Nat.Prime 166537906346951949512555048980432872272371711730863 := by
  refine pocklington_step (F := 899600027393245632546611809501) (R := 185124390035342441862) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(15427219380457, 1, 39057201613079480624385422182372329371683082774819), (58312519269211093, 1, 150546077987673143778764084279227584095502992488768)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ⟨p_cert_79, by decide, by rfl⟩
  · exact ⟨p_cert_87, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_107 : Nat.Prime 728274111385521052829569445746150935678229317157831 := by
  refine pocklington_step (F := 75946695343942045545950611) (R := 9589279797986792496994530) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(75946695343942045545950611, 1, 452120970544462201596496052141138845831662587932049)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_95, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_108 : Nat.Prime 33130398017892703170199385707457091187665982909665133 := by
  refine pocklington_step (F := 10731686646196985543603831722141297) (R := 3087156670720832556) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(10731686646196985543603831722141297, 1, 23993097326830489423758988915940931999887767071559242)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_99, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_109 : Nat.Prime 172065054976772107675581285529480503164616022973170886021 := by
  refine pocklington_step (F := 8373094558265845827516770230329627536146799) (R := 20549756577980) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(8373094558265845827516770230329627536146799, 1, 1550052167613201207600332327553308669936632580025548070)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_101, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_110 : Nat.Prime 297944641350014385275436610378443430138886610872100450151 := by
  refine pocklington_step (F := 166537906346951949512555048980432872272371711730863) (R := 1789050) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(166537906346951949512555048980432872272371711730863, 1, 209681213676700588119032984193871739562122051465519805954)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_106, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_111 : Nat.Prime 40687297931583212434454439521483153605327032354191178561100493 := by
  refine pocklington_step (F := 23567721955657194776649723510218140673) (R := 1726399267953712238758604) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(23567721955657194776649723510218140673, 1, 27174229451042374022000151346438806794806652593030293847499415)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_100, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_112 : Nat.Prime 6297297448939257420492825692420433831955731153612194642748437393 := by
  refine pocklington_step (F := 172065054976772107675581285529480503164616022973170886021) (R := 36598352) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(172065054976772107675581285529480503164616022973170886021, 1, 4211629293977890069171274827215561147629079400150266607937329162)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_109, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_113 : Nat.Prime 30463286638653519166134094991866993173323371437334932151335007280987 := by
  refine morrison_step (F := 81910915952377226282035462149816197123802869497) (R := 371907532524294899004) (P := 3) (D_n := 5) (Q_n := 1) (D_inv := 12185314655461407666453637996746797269329348574933972860534002912395) (Q_inv := 1) (by decide) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by decide) (by rfl) (by rfl) (by rfl) [(79933803662777, 1, 29484697245702635739981206887858110142744241194341233631508365849028), (1024734370178869815789881312791361, 1, 18754954513226371559930190343653497128085973194981374702749524506254)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ⟨p_cert_80, by decide, by rfl⟩
  · exact ⟨p_cert_98, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_114 : Nat.Prime 192019039709655797000518669217368441905319430371651523196922661390472359 := by
  refine morrison_step (F := 728274111385521052829569445746150935678229317157831) (R := 263663140990066177560) (P := 5) (D_n := 21) (Q_n := 1) (D_inv := 173731512118260006809993081672857161723860437002922806701977646019951182) (Q_inv := 1) (by decide) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by decide) (by rfl) (by rfl) (by rfl) [(728274111385521052829569445746150935678229317157831, 1, 24198512993152417780880709749869534899505638214091412502462663726868685)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_107, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_115 : Nat.Prime 6912685429547608692018672091825263908591499493379454835089215810057004923 := by
  refine morrison_step (F := 192019039709655797000518669217368441905319430371651523196922661390472359) (R := 36) (P := 3) (D_n := 5) (Q_n := 1) (D_inv := 4147611257728565215211203255095158345154899696027672901053529486034202954) (Q_inv := 1) (by decide) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by decide) (by rfl) (by rfl) (by rfl) [(192019039709655797000518669217368441905319430371651523196922661390472359, 1, 1789436296772981197587537082362006663979829219929556143045535914513691975)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_114, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_116 : Nat.Prime 393611374074037671879681905117616665050606458308994467075786487154686310109 := by
  refine pocklington_step (F := 11594902353095303515194099337049142451792171) (R := 33946933064853419022884855692948) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(11594902353095303515194099337049142451792171, 1, 170271188570270343619495627682997522831047490330779315996886805188841456995)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_102, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_117 : Nat.Prime 61471288489178400502227511463990027154771532183167217954139642300211427949197 := by
  refine pocklington_step (F := 165337136995061861490728657086431249608356451) (R := 371793594629707231288085555124996) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(165337136995061861490728657086431249608356451, 1, 17695973085258846841239025041937883666283212189320265631688295449515113635205)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_103, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_118 : Nat.Prime 446092199703710200243488189611814726284358184224501445344992905869145850914339049 := by
  refine pocklington_step (F := 472362132581542660756039516449996870043763098571) (R := 944386031254743838879040713448888) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(472362132581542660756039516449996870043763098571, 1, 148991556945905528991719627925018681344140791478996544551241017077363605307080511)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_105, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_119 : Nat.Prime 377109641529044894298736527542654303159124707098151931139669646378559239309522472503 := by
  refine pocklington_step (F := 393611374074037671879681905117616665050606458308994467075786487154686310109) (R := 958076078) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(393611374074037671879681905117616665050606458308994467075786487154686310109, 1, 238140000338108520947135002006762782448156229867678486062472266002757140440447987778)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_116, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_120 : Nat.Prime 234876680162126157297178268809232186812812382998116376287449808741638003961276470137365651 := by
  refine pocklington_step (F := 33130398017892703170199385707457091187665982909665133) (R := 7089461467842207256807226302421873050) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(33130398017892703170199385707457091187665982909665133, 1, 50305187117369928908534131514166298946792126731159273925534527048800922190114785262003109)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_108, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_121 : Nat.Prime 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719 := by
  refine pocklington_step (F := 6297297448939257420492825692420433831955731153612194642748437393) (R := 16038145456623871470444377526) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(6297297448939257420492825692420433831955731153612194642748437393, 1, 38235612578568515427131151707386209695658082846155532414704702811064990028448024618000130501)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_112, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_122 : Nat.Prime 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 := by
  refine morrison_step (F := 234876680162126157297178268809232186812812382998116376287449808741638003961276470137365651) (R := 430) (P := 5) (D_n := 21) (Q_n := 1) (D_inv := 52903176055564605905507295784174678267838217694337640944744647397521321844611319226178072820) (Q_inv := 1) (by decide) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by decide) (by rfl) (by rfl) (by rfl) [(234876680162126157297178268809232186812812382998116376287449808741638003961276470137365651, 1, 64119459959313523214033193154960806906264872614654337041483108849173325217984121529238779915)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_120, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_123 : Nat.Prime 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 := by
  refine pocklington_step (F := 297944641350014385275436610378443430138886610872100450151) (R := 338978986203906000646394540200464438) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(297944641350014385275436610378443430138886610872100450151, 1, 53273605658701141961477383397041739024175717914477463853493148547090195074653359017228127102)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_110, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_124 : Nat.Prime 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 := by
  refine pocklington_step (F := 40687297931583212434454439521483153605327032354191178561100493) (R := 2482272787923724442180914498236) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(40687297931583212434454439521483153605327032354191178561100493, 1, 73907865146105575538404603169709105029221091458844786809102730399796142567130870272501517243)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_111, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_125 : Nat.Prime 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 := by
  refine pocklington_step (F := 30463286638653519166134094991866993173323371437334932151335007280987) (R := 3315366909280354840871034) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(30463286638653519166134094991866993173323371437334932151335007280987, 1, 19634206805123167267230919830402435798246395731963882920946111189443413598378722171928743778)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_113, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_126 : Nat.Prime 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 := by
  refine morrison_step (F := 377109641529044894298736527542654303159124707098151931139669646378559239309522472503) (R := 267818590) (P := 5) (D_n := 21) (Q_n := 1) (D_inv := 52903176055564605905507295784174678267838217694337640944744647397521321844611319226178073260) (Q_inv := 1) (by decide) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by decide) (by rfl) (by rfl) (by rfl) [(377109641529044894298736527542654303159124707098151931139669646378559239309522472503, 1, 48571232394634552147243142671673904933326288733426974252808876501201171220969960447970857298)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_119, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_127 : Nat.Prime 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 := by
  refine pocklington_step (F := 389437937650936471119067068790964706311950012216137343599397) (R := 259340353636117769962203863414874) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(1165527773351003, 1, 53609391795759484181794903925555100743626029002376407766785743533819440040954124767019932604), (334130122469124376448502703576854973706716799, 1, 74103519836115573990275798972213816498396677457603798406575270215258822155375981421156210149)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ⟨p_cert_82, by decide, by rfl⟩
  · exact ⟨p_cert_104, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_128 : Nat.Prime 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 := by
  refine pocklington_step (F := 446092199703710200243488189611814726284358184224501445344992905869145850914339049) (R := 226403807412) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(446092199703710200243488189611814726284358184224501445344992905869145850914339049, 1, 98899326705884627896298055072121266916582326864482315005071549119653127296964150819337081843)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_118, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_129 : Nat.Prime 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 := by
  refine pocklington_step (F := 61471288489178400502227511463990027154771532183167217954139642300211427949197) (R := 1642994232787134) (a := 2) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by rfl) [(61471288489178400502227511463990027154771532183167217954139642300211427949197, 1, 40397255647511581288211954147483703318249304336836541429486988906485208356346028438398742943)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_117, by decide, by rfl⟩
set_option maxRecDepth 4096 in
private lemma p_cert_130 : Nat.Prime 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 := by
  refine morrison_step (F := 6912685429547608692018672091825263908591499493379454835089215810057004923) (R := 14610381667016469070) (P := 5) (D_n := 21) (Q_n := 1) (D_inv := 52903176055564605905507295784174678267838217694337640944744647397521321844611319226178073700) (Q_inv := 1) (by decide) (by decide) (lt_two_pow_400_of_lt (by decide)) (by rfl) (by decide) (by decide) (by rfl) (by rfl) (by rfl) [(6912685429547608692018672091825263908591499493379454835089215810057004923, 1, 79539641659384379754690590832327263434422239975851133338004133044566241618577628799157817349)] (by decide) (by rfl) ?_
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨p_cert_115, by decide, by rfl⟩

private lemma p_cpap_0 : Nat.Prime (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719 + 0 * 210) := p_cert_121
private lemma p_cpap_1 : Nat.Prime (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719 + 1 * 210) := p_cert_122
private lemma p_cpap_2 : Nat.Prime (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719 + 2 * 210) := p_cert_123
private lemma p_cpap_3 : Nat.Prime (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719 + 3 * 210) := p_cert_124
private lemma p_cpap_4 : Nat.Prime (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719 + 4 * 210) := p_cert_125
private lemma p_cpap_5 : Nat.Prime (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719 + 5 * 210) := p_cert_126
private lemma p_cpap_6 : Nat.Prime (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719 + 6 * 210) := p_cert_127
private lemma p_cpap_7 : Nat.Prime (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719 + 7 * 210) := p_cert_128
private lemma p_cpap_8 : Nat.Prime (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719 + 8 * 210) := p_cert_129
private lemma p_cpap_9 : Nat.Prime (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719 + 9 * 210) := p_cert_130

set_option maxRecDepth 4096 in
private lemma gap_0 (m : ℕ) (hm1 : 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719 < m) (hm2 : m < 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929) : ¬ m.Prime := by
  have hj : m - (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719 + 1) < 209 := by omega
  have hm_eq : m = 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719 + 1 + (m - (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719 + 1)) := by omega
  rw [hm_eq]
  exact checkGapList_sound 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719 [2, 3, 2, 0, 2, 5, 2, 3, 2, 11, 2, 53, 2, 3, 2, 5, 2, 61, 2, 3, 2, 17, 2, 13, 2, 3, 2, 137, 2, 7, 2, 3, 2, 23, 2, 5, 2, 3, 2, 31, 2, 73, 2, 3, 2, 5, 2, 19, 2, 3, 2, 41, 2, 11, 2, 3, 2, 7, 2, 29, 2, 3, 2, 103, 2, 5, 2, 3, 2, 37, 2, 7, 2, 3, 2, 5, 2, 47, 2, 3, 2, 43, 2, 71, 2, 3, 2, 67, 2, 17, 2, 3, 2, 139, 2, 5, 2, 3, 2, 7, 2, 13, 2, 3, 2, 5, 2, 151, 2, 3, 2, 59, 2, 7, 2, 3, 2, 29, 2, 11, 2, 3, 2, 17, 2, 5, 2, 3, 2, 89, 2, 0, 2, 3, 2, 5, 2, 83, 2, 3, 2, 7, 2, 37, 2, 3, 2, 179, 2, 127, 2, 3, 2, 13, 2, 5, 2, 3, 2, 0, 2, 19, 2, 3, 2, 5, 2, 43, 2, 3, 2, 23, 2, 163, 2, 3, 2, 13121, 2, 13, 2, 3, 2, 7, 2, 5, 2, 3, 2, 109, 2, 17, 2, 3, 2, 5, 2, 7, 2, 3, 2, 173, 2, 149, 2, 3, 2, 11, 2] 1 (by rfl) (m - (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719 + 1)) hj
set_option maxRecDepth 4096 in
private lemma gap_1 (m : ℕ) (hm1 : 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 < m) (hm2 : m < 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139) : ¬ m.Prime := by
  have hj : m - (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 + 1) < 209 := by omega
  have hm_eq : m = 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 + 1 + (m - (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 + 1)) := by omega
  rw [hm_eq]
  exact checkGapList_sound 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 [2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 67, 2, 3, 2, 5, 2, 4271, 2, 3, 2, 13, 2, 29, 2, 3, 2, 19, 2, 7, 2, 3, 2, 601, 2, 5, 2, 3, 2, 263, 2, 11, 2, 3, 2, 5, 2, 13, 2, 3, 2, 61, 2, 23, 2, 3, 2, 7, 2, 103, 2, 3, 2, 11, 2, 5, 2, 3, 2, 79, 2, 7, 2, 3, 2, 5, 2, 31, 2, 3, 2, 29, 2, 17, 2, 3, 2, 41, 2, 0, 2, 3, 2, 83, 2, 5, 2, 3, 2, 7, 2, 251, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 7, 2, 3, 2, 17, 2, 53, 2, 3, 2, 73, 2, 5, 2, 3, 2, 11, 2, 167, 2, 3, 2, 5, 2, 59, 2, 3, 2, 7, 2, 0, 2, 3, 2, 157, 2, 47, 2, 3, 2, 563, 2, 5, 2, 3, 2, 97, 2, 139, 2, 3, 2, 5, 2, 181, 2, 3, 2, 113, 2, 11, 2, 3, 2, 13, 2, 19, 2, 3, 2, 7, 2, 5, 2, 3, 2, 223, 2, 23, 2, 3, 2, 5, 2, 7, 2, 3, 2, 31, 2, 13, 2, 3, 2, 191, 2] 1 (by rfl) (m - (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 + 1)) hj
set_option maxRecDepth 4096 in
private lemma gap_2 (m : ℕ) (hm1 : 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 < m) (hm2 : m < 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349) : ¬ m.Prime := by
  have hj : m - (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 + 1) < 209 := by omega
  have hm_eq : m = 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 + 1 + (m - (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 + 1)) := by omega
  rw [hm_eq]
  exact checkGapList_sound 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 [2, 3, 2, 367, 2, 5, 2, 3, 2, 17, 2, 0, 2, 3, 2, 5, 2, 79, 2, 3, 2, 487, 2, 0, 2, 3, 2, 23, 2, 7, 2, 3, 2, 47, 2, 5, 2, 3, 2, 2741, 2, 41, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 31, 2, 3, 2, 7, 2, 73, 2, 3, 2, 3329, 2, 5, 2, 3, 2, 67, 2, 7, 2, 3, 2, 5, 2, 17, 2, 3, 2, 149, 2, 19, 2, 3, 2, 0, 2, 71, 2, 3, 2, 37, 2, 5, 2, 3, 2, 7, 2, 11597, 2, 3, 2, 5, 2, 107, 2, 3, 2, 17, 2, 7, 2, 3, 2, 11, 2, 23, 2, 3, 2, 13, 2, 5, 2, 3, 2, 241, 2, 739, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 97, 2, 3, 2, 0, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 19, 2, 11, 2, 3, 2, 5, 2, 37, 2, 3, 2, 193, 2, 0, 2, 3, 2, 31, 2, 17, 2, 3, 2, 7, 2, 5, 2, 3, 2, 613, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13, 2, 67, 2, 3, 2, 61, 2] 1 (by rfl) (m - (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 + 1)) hj
set_option maxRecDepth 4096 in
private lemma gap_3 (m : ℕ) (hm1 : 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 < m) (hm2 : m < 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559) : ¬ m.Prime := by
  have hj : m - (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 + 1) < 209 := by omega
  have hm_eq : m = 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 + 1 + (m - (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 + 1)) := by omega
  rw [hm_eq]
  exact checkGapList_sound 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 [2, 3, 2, 17, 2, 5, 2, 3, 2, 29, 2, 47, 2, 3, 2, 5, 2, 11, 2, 3, 2, 71, 2, 32183, 2, 3, 2, 127, 2, 7, 2, 3, 2, 89, 2, 5, 2, 3, 2, 11, 2, 157, 2, 3, 2, 5, 2, 23, 2, 3, 2, 103, 2, 43, 2, 3, 2, 7, 2, 0, 2, 3, 2, 19, 2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 41, 2, 3, 2, 151, 2, 11, 2, 3, 2, 4679, 2, 313, 2, 3, 2, 23, 2, 5, 2, 3, 2, 7, 2, 19, 2, 3, 2, 5, 2, 0, 2, 3, 2, 107, 2, 7, 2, 3, 2, 2347, 2, 61, 2, 3, 2, 53, 2, 5, 2, 3, 2, 281, 2, 0, 2, 3, 2, 5, 2, 0, 2, 3, 2, 7, 2, 20963, 2, 3, 2, 13, 2, 11, 2, 3, 2, 31, 2, 5, 2, 3, 2, 41, 2, 131, 2, 3, 2, 5, 2, 0, 2, 3, 2, 11, 2, 13, 2, 3, 2, 19, 2, 37, 2, 3, 2, 7, 2, 5, 2, 3, 2, 59, 2, 0, 2, 3, 2, 5, 2, 7, 2, 3, 2, 0, 2, 113, 2, 3, 2, 17, 2] 1 (by rfl) (m - (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 + 1)) hj
set_option maxRecDepth 4096 in
private lemma gap_4 (m : ℕ) (hm1 : 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 < m) (hm2 : m < 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769) : ¬ m.Prime := by
  have hj : m - (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 + 1) < 209 := by omega
  have hm_eq : m = 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 + 1 + (m - (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 + 1)) := by omega
  rw [hm_eq]
  exact checkGapList_sound 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 [2, 3, 2, 109, 2, 5, 2, 3, 2, 137, 2, 937, 2, 3, 2, 5, 2, 227, 2, 3, 2, 23, 2, 179, 2, 3, 2, 11, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 103, 2, 3, 2, 67, 2, 173, 2, 3, 2, 7, 2, 3499, 2, 3, 2, 1009, 2, 5, 2, 3, 2, 269, 2, 7, 2, 3, 2, 5, 2, 73, 2, 3, 2, 19, 2, 47, 2, 3, 2, 139, 2, 29, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 43, 2, 3, 2, 5, 2, 0, 2, 3, 2, 97, 2, 7, 2, 3, 2, 37, 2, 13, 2, 3, 2, 4871, 2, 5, 2, 3, 2, 31, 2, 2699, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 0, 2, 3, 2, 29, 2, 397, 2, 3, 2, 61, 2, 5, 2, 3, 2, 11, 2, 101, 2, 3, 2, 5, 2, 17, 2, 3, 2, 13, 2, 151, 2, 3, 2, 47, 2, 89, 2, 3, 2, 7, 2, 5, 2, 3, 2, 27259, 2, 31, 2, 3, 2, 5, 2, 7, 2, 3, 2, 17, 2, 11, 2, 3, 2, 431, 2] 1 (by rfl) (m - (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 + 1)) hj
set_option maxRecDepth 4096 in
private lemma gap_5 (m : ℕ) (hm1 : 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 < m) (hm2 : m < 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979) : ¬ m.Prime := by
  have hj : m - (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 + 1) < 209 := by omega
  have hm_eq : m = 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 + 1 + (m - (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 + 1)) := by omega
  rw [hm_eq]
  exact checkGapList_sound 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 [2, 3, 2, 131, 2, 5, 2, 3, 2, 113, 2, 109, 2, 3, 2, 5, 2, 0, 2, 3, 2, 53, 2, 19, 2, 3, 2, 71, 2, 7, 2, 3, 2, 0, 2, 5, 2, 3, 2, 13, 2, 23, 2, 3, 2, 5, 2, 149, 2, 3, 2, 181, 2, 29, 2, 3, 2, 7, 2, 11, 2, 3, 2, 43, 2, 5, 2, 3, 2, 3253, 2, 7, 2, 3, 2, 5, 2, 331, 2, 3, 2, 11, 2, 83, 2, 3, 2, 23, 2, 2693, 2, 3, 2, 17, 2, 5, 2, 3, 2, 7, 2, 163, 2, 3, 2, 5, 2, 367, 2, 3, 2, 29, 2, 7, 2, 3, 2, 13, 2, 107, 2, 3, 2, 59, 2, 5, 2, 3, 2, 37, 2, 191, 2, 3, 2, 5, 2, 19, 2, 3, 2, 7, 2, 13, 2, 3, 2, 11, 2, 41, 2, 3, 2, 101, 2, 5, 2, 3, 2, 73, 2, 17, 2, 3, 2, 5, 2, 31, 2, 3, 2, 179, 2, 1949, 2, 3, 2, 79, 2, 23, 2, 3, 2, 7, 2, 5, 2, 3, 2, 173, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11801, 2, 37, 2, 3, 2, 0, 2] 1 (by rfl) (m - (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 + 1)) hj
set_option maxRecDepth 4096 in
private lemma gap_6 (m : ℕ) (hm1 : 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 < m) (hm2 : m < 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189) : ¬ m.Prime := by
  have hj : m - (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 + 1) < 209 := by omega
  have hm_eq : m = 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 + 1 + (m - (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 + 1)) := by omega
  rw [hm_eq]
  exact checkGapList_sound 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 [2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 13, 2, 3, 2, 5, 2, 29, 2, 3, 2, 41, 2, 53, 2, 3, 2, 26891, 2, 7, 2, 3, 2, 67, 2, 5, 2, 3, 2, 47, 2, 19, 2, 3, 2, 5, 2, 11, 2, 3, 2, 227, 2, 17, 2, 3, 2, 7, 2, 190507, 2, 3, 2, 13, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 10771, 2, 3, 2, 31, 2, 167, 2, 3, 2, 17, 2, 13, 2, 3, 2, 239, 2, 5, 2, 3, 2, 7, 2, 71, 2, 3, 2, 5, 2, 23, 2, 3, 2, 43, 2, 7, 2, 3, 2, 19, 2, 2389, 2, 3, 2, 107, 2, 5, 2, 3, 2, 53, 2, 0, 2, 3, 2, 5, 2, 137, 2, 3, 2, 7, 2, 31, 2, 3, 2, 0, 2, 59, 2, 3, 2, 23, 2, 5, 2, 3, 2, 127, 2, 0, 2, 3, 2, 5, 2, 13, 2, 3, 2, 0, 2, 631, 2, 3, 2, 257, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 17, 2, 29, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 181, 2, 3, 2, 503, 2] 1 (by rfl) (m - (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 + 1)) hj
set_option maxRecDepth 4096 in
private lemma gap_7 (m : ℕ) (hm1 : 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 < m) (hm2 : m < 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399) : ¬ m.Prime := by
  have hj : m - (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 + 1) < 209 := by omega
  have hm_eq : m = 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 + 1 + (m - (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 + 1)) := by omega
  rw [hm_eq]
  exact checkGapList_sound 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 [2, 3, 2, 4603, 2, 5, 2, 3, 2, 13, 2, 61, 2, 3, 2, 5, 2, 47, 2, 3, 2, 19, 2, 0, 2, 3, 2, 109, 2, 7, 2, 3, 2, 71, 2, 5, 2, 3, 2, 29, 2, 113, 2, 3, 2, 5, 2, 17, 2, 3, 2, 10169, 2, 26783, 2, 3, 2, 7, 2, 19, 2, 3, 2, 97, 2, 5, 2, 3, 2, 311, 2, 7, 2, 3, 2, 5, 2, 317, 2, 3, 2, 17, 2, 89, 2, 3, 2, 13, 2, 0, 2, 3, 2, 191, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 131, 2, 3, 2, 47, 2, 7, 2, 3, 2, 42013, 2, 31, 2, 3, 2, 11, 2, 5, 2, 3, 2, 0, 2, 53, 2, 3, 2, 5, 2, 101, 2, 3, 2, 7, 2, 157, 2, 3, 2, 151, 2, 17, 2, 3, 2, 37, 2, 5, 2, 3, 2, 43, 2, 83, 2, 3, 2, 5, 2, 11, 2, 3, 2, 0, 2, 19, 2, 3, 2, 73, 2, 0, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 13, 2, 3, 2, 5, 2, 7, 2, 3, 2, 137, 2, 127, 2, 3, 2, 167, 2] 1 (by rfl) (m - (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 + 1)) hj
set_option maxRecDepth 4096 in
private lemma gap_8 (m : ℕ) (hm1 : 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 < m) (hm2 : m < 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609) : ¬ m.Prime := by
  have hj : m - (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 + 1) < 209 := by omega
  have hm_eq : m = 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 + 1 + (m - (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 + 1)) := by omega
  rw [hm_eq]
  exact checkGapList_sound 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 [2, 3, 2, 29, 2, 5, 2, 3, 2, 23, 2, 41, 2, 3, 2, 5, 2, 37, 2, 3, 2, 79, 2, 11, 2, 3, 2, 53, 2, 7, 2, 3, 2, 13, 2, 5, 2, 3, 2, 19, 2, 17, 2, 3, 2, 5, 2, 97, 2, 3, 2, 89, 2, 907, 2, 3, 2, 7, 2, 13, 2, 3, 2, 0, 2, 5, 2, 3, 2, 193, 2, 7, 2, 3, 2, 5, 2, 19, 2, 3, 2, 139, 2, 59, 2, 3, 2, 38333, 2, 11, 2, 3, 2, 41, 2, 5, 2, 3, 2, 7, 2, 23, 2, 3, 2, 5, 2, 71, 2, 3, 2, 11, 2, 7, 2, 3, 2, 83, 2, 29, 2, 3, 2, 163, 2, 5, 2, 3, 2, 101, 2, 107, 2, 3, 2, 5, 2, 13, 2, 3, 2, 7, 2, 17, 2, 3, 2, 23, 2, 67, 2, 3, 2, 19, 2, 5, 2, 3, 2, 131, 2, 1933, 2, 3, 2, 5, 2, 61, 2, 3, 2, 5779, 2, 521, 2, 3, 2, 11, 2, 79, 2, 3, 2, 7, 2, 5, 2, 3, 2, 13, 2, 19, 2, 3, 2, 5, 2, 7, 2, 3, 2, 59, 2, 281, 2, 3, 2, 43, 2] 1 (by rfl) (m - (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 + 1)) hj

end OMA.Erdos141Cert

theorem OMA.solution : OMA.R_Erdos141_erdos_141_R1.H1 := by
  intro k hk7 hk10
  refine OMA.R_Erdos141_erdos_141_R1.cpap (p := 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719) (d := 210) (k := k) (by decide) ?_ ?_
  · intro n hn
    have hn10 : n < 10 := by omega
    interval_cases n
    · exact OMA.Erdos141Cert.p_cpap_0
    · exact OMA.Erdos141Cert.p_cpap_1
    · exact OMA.Erdos141Cert.p_cpap_2
    · exact OMA.Erdos141Cert.p_cpap_3
    · exact OMA.Erdos141Cert.p_cpap_4
    · exact OMA.Erdos141Cert.p_cpap_5
    · exact OMA.Erdos141Cert.p_cpap_6
    · exact OMA.Erdos141Cert.p_cpap_7
    · exact OMA.Erdos141Cert.p_cpap_8
    · exact OMA.Erdos141Cert.p_cpap_9
  · intro n hn m hm1 hm2
    have hn9 : n < 9 := by omega
    interval_cases n
    · simpa [show 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719 + 0 * 210 = 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719 by rfl, show 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719 + (0 + 1) * 210 = 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 by rfl] using OMA.Erdos141Cert.gap_0 m (by simpa using hm1) (by simpa using hm2)
    · simpa [show 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719 + 1 * 210 = 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 by rfl, show 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719 + (1 + 1) * 210 = 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 by rfl] using OMA.Erdos141Cert.gap_1 m (by simpa using hm1) (by simpa using hm2)
    · simpa [show 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719 + 2 * 210 = 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 by rfl, show 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719 + (2 + 1) * 210 = 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 by rfl] using OMA.Erdos141Cert.gap_2 m (by simpa using hm1) (by simpa using hm2)
    · simpa [show 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719 + 3 * 210 = 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 by rfl, show 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719 + (3 + 1) * 210 = 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 by rfl] using OMA.Erdos141Cert.gap_3 m (by simpa using hm1) (by simpa using hm2)
    · simpa [show 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719 + 4 * 210 = 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 by rfl, show 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719 + (4 + 1) * 210 = 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 by rfl] using OMA.Erdos141Cert.gap_4 m (by simpa using hm1) (by simpa using hm2)
    · simpa [show 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719 + 5 * 210 = 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 by rfl, show 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719 + (5 + 1) * 210 = 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 by rfl] using OMA.Erdos141Cert.gap_5 m (by simpa using hm1) (by simpa using hm2)
    · simpa [show 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719 + 6 * 210 = 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 by rfl, show 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719 + (6 + 1) * 210 = 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 by rfl] using OMA.Erdos141Cert.gap_6 m (by simpa using hm1) (by simpa using hm2)
    · simpa [show 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719 + 7 * 210 = 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 by rfl, show 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719 + (7 + 1) * 210 = 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 by rfl] using OMA.Erdos141Cert.gap_7 m (by simpa using hm1) (by simpa using hm2)
    · simpa [show 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719 + 8 * 210 = 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 by rfl, show 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719 + (8 + 1) * 210 = 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 by rfl] using OMA.Erdos141Cert.gap_8 m (by simpa using hm1) (by simpa using hm2)
