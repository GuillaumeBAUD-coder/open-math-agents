import FormalConjectures.GreensOpenProblems.«21»

-- Problem: Ben Green's Open Problem 21 — fox kleitman
-- Upstream: formal-conjectures FormalConjectures/GreensOpenProblems/21.lean:87 (declaration Green21.green_21.variants.fox_kleitman)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace FK
theorem tri_col {G : Type*} [CommGroup G] [Finite G] (g : G) (hg : g ≠ 1) :
    ∃ χ : G → Fin 3, ∀ u, χ (g * u) ≠ χ u := by
  classical
  have hfin : IsOfFinOrder g := isOfFinOrder_of_finite g
  have hn : 2 ≤ orderOf g := by
    have h0 : 0 < orderOf g := hfin.orderOf_pos
    have h1 : orderOf g ≠ 1 := by rwa [Ne, orderOf_eq_one_iff]
    omega
  let r : G → G := fun u => (QuotientGroup.mk u : G ⧸ Subgroup.zpowers g).out
  have hr : ∀ u, ∃ j : ℕ, g ^ j * r u = u := by
    intro u
    have h1 : (QuotientGroup.mk (r u) : G ⧸ Subgroup.zpowers g) = QuotientGroup.mk u :=
      QuotientGroup.out_eq' _
    rw [QuotientGroup.eq] at h1
    obtain ⟨j, hj⟩ := (mem_powers_iff_mem_zpowers).mpr h1
    refine ⟨j, ?_⟩
    change g ^ j = _ at hj
    rw [hj, mul_comm, mul_inv_cancel_left]
  have hrg : ∀ u, r (g * u) = r u := by
    intro u
    have : (QuotientGroup.mk (g * u) : G ⧸ Subgroup.zpowers g) = QuotientGroup.mk u := by
      rw [QuotientGroup.eq]
      have : (g * u)⁻¹ * u = g⁻¹ := by
        rw [mul_inv_rev, mul_assoc, mul_comm g⁻¹ u, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [this]
      exact Subgroup.inv_mem _ (Subgroup.mem_zpowers g)
    simp only [r, this]
  let j : G → ℕ := fun u => Nat.find (hr u)
  have hj : ∀ u, g ^ j u * r u = u := fun u => Nat.find_spec (hr u)
  have hjmin : ∀ u m, g ^ m * r u = u → j u ≤ m := fun u m h => Nat.find_min' (hr u) h
  have hjlt : ∀ u, j u < orderOf g := by
    intro u
    by_contra hcon
    have hcon' : orderOf g ≤ j u := by omega
    have h1 : g ^ (j u - orderOf g) * r u = u := by
      have := hj u
      rw [← Nat.sub_add_cancel hcon', pow_add, pow_orderOf_eq_one, mul_one] at this
      exact this
    have := hjmin u _ h1
    have h0 : 0 < orderOf g := hfin.orderOf_pos
    omega
  let χ : G → Fin 3 := fun u => if j u = orderOf g - 1 then 2 else ⟨j u % 2, by omega⟩
  refine ⟨χ, fun u => ?_⟩
  have hu := hjlt u
  by_cases hA : j u + 1 < orderOf g
  · have e1 : g ^ (j u + 1) * r (g * u) = g * u := by
      rw [hrg, pow_succ, mul_comm (g ^ j u) g, mul_assoc, hj]
    have e2 : g ^ j (g * u) * r u = g ^ (j u + 1) * r u := by
      have := hj (g * u)
      rw [hrg] at this
      rw [this, ← hrg u, e1]
    have e3 : g ^ j (g * u) = g ^ (j u + 1) := mul_right_cancel e2
    have e4 : j (g * u) = j u + 1 := pow_injOn_Iio_orderOf (hjlt _) hA e3
    simp only [χ, e4]
    split_ifs with h1 h2 h2
    · omega
    · simp [Fin.ext_iff]; omega
    · simp [Fin.ext_iff]; omega
    · simp only [ne_eq, Fin.mk.injEq]; omega
  · have hB : j u + 1 = orderOf g := by omega
    have e1 : g * u = r u := by
      have := hj u
      calc g * u = g * (g ^ j u * r u) := by rw [this]
        _ = g ^ (j u + 1) * r u := by rw [pow_succ', mul_assoc]
        _ = r u := by rw [hB, pow_orderOf_eq_one, one_mul]
    have e2 : j (g * u) = 0 := by
      have := hjmin (g * u) 0 (by rw [pow_zero, one_mul, hrg, e1])
      omega
    simp only [χ, e2]
    split_ifs with h1 h2
    · omega
    · omega
    · simp [Fin.ext_iff]
    · omega
theorem isUnit_of_not_dvd {p : ℕ} (hp : p.Prime) (K : ℕ) (c : ℤ) (hc : ¬ (p : ℤ) ∣ c) :
    IsUnit (c : ZMod (p ^ K)) := by
  have hc' : ¬ p ∣ c.natAbs := fun h => hc (Int.natCast_dvd.mpr h)
  have hcop : c.natAbs.Coprime (p ^ K) :=
    Nat.Coprime.pow_right K ((Nat.coprime_comm).mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hc'))
  have hu : IsUnit ((c.natAbs : ℕ) : ZMod (p ^ K)) := (ZMod.isUnit_iff_coprime _ _).mpr hcop
  rcases Int.natAbs_eq c with h | h
  · rw [h, Int.cast_natCast]; exact hu
  · rw [h, Int.cast_neg, Int.cast_natCast]; exact hu.neg

theorem unit_col {p : ℕ} (hp : p.Prime) (K : ℕ) (c1 c2 : ℤ) (h1 : ¬ (p : ℤ) ∣ c1)
    (h2 : ¬ (p : ℤ) ∣ c2) (h12 : ¬ (p : ℤ) ^ K ∣ c1 + c2) :
    ∃ χ : ℕ → Fin 3, ∀ u1 u2 : ℕ, Nat.Coprime u1 p → Nat.Coprime u2 p → χ u1 = χ u2 →
      ¬ (p : ℤ) ^ K ∣ c1 * u1 + c2 * u2 := by
  classical
  have : NeZero (p ^ K) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hA := isUnit_of_not_dvd hp K c1 h1
  have hB := isUnit_of_not_dvd hp K c2 h2
  set A := hA.unit
  set B := hB.unit
  have hAc : (A : ZMod (p ^ K)) = c1 := IsUnit.unit_spec hA
  have hBc : (B : ZMod (p ^ K)) = c2 := IsUnit.unit_spec hB
  have hdvd : ∀ z : ℤ, (p : ℤ) ^ K ∣ z ↔ (z : ZMod (p ^ K)) = 0 := by
    intro z
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rfl
  set g : (ZMod (p ^ K))ˣ := -(A * B⁻¹)
  have hg : g ≠ 1 := by
    intro hg1
    apply h12
    rw [hdvd]
    have hBB : (B : ZMod (p ^ K)) * ((B⁻¹ : (ZMod (p ^ K))ˣ) : ZMod (p ^ K)) = 1 := Units.mul_inv B
    have : ((g : (ZMod (p ^ K))ˣ) : ZMod (p ^ K)) = 1 := by rw [hg1]; rfl
    simp only [g, Units.val_neg, Units.val_mul] at this
    push_cast
    rw [← hAc, ← hBc]
    linear_combination (-(B : ZMod (p ^ K))) * this - (A : ZMod (p ^ K)) * hBB
  obtain ⟨χ0, hχ0⟩ := tri_col g hg
  let χ : ℕ → Fin 3 := fun u => if h : Nat.Coprime u (p ^ K) then χ0 (ZMod.unitOfCoprime u h) else 0
  refine ⟨χ, fun u1 u2 hu1 hu2 hχ hd => ?_⟩
  have hu1' : Nat.Coprime u1 (p ^ K) := Nat.Coprime.pow_right K hu1
  have hu2' : Nat.Coprime u2 (p ^ K) := Nat.Coprime.pow_right K hu2
  simp only [χ] at hχ
  rw [dif_pos hu1', dif_pos hu2'] at hχ
  apply hχ0 (ZMod.unitOfCoprime u1 hu1')
  rw [hχ]
  congr 1
  apply Units.ext
  rw [hdvd] at hd
  push_cast at hd
  have hBB : (B : ZMod (p ^ K)) * ((B⁻¹ : (ZMod (p ^ K))ˣ) : ZMod (p ^ K)) = 1 := Units.mul_inv B
  simp only [g, Units.val_neg, Units.val_mul, ZMod.coe_unitOfCoprime]
  rw [← hAc, ← hBc] at hd
  linear_combination (-((B⁻¹ : (ZMod (p ^ K))ˣ) : ZMod (p ^ K))) * hd + (u2 : ZMod (p ^ K)) * hBB

def Good (a1 a2 a3 : ℤ) : Prop := ∃ col : ℕ → Fin 24, ∀ x1 x2 x3 : ℕ, 0 < x1 → 0 < x2 → 0 < x3 →
  col x1 = col x2 → col x1 = col x3 → a1 * x1 + a2 * x2 + a3 * x3 ≠ 0

theorem good_of_col {α : Type} [Fintype α] (hα : Fintype.card α ≤ 24) {a1 a2 a3 : ℤ}
    (col : ℕ → α) (H : ∀ x1 x2 x3 : ℕ, 0 < x1 → 0 < x2 → 0 < x3 →
      col x1 = col x2 → col x1 = col x3 → a1 * x1 + a2 * x2 + a3 * x3 ≠ 0) : Good a1 a2 a3 := by
  classical
  let e := Fintype.equivFin α
  refine ⟨fun x => Fin.castLE hα (e (col x)), fun x1 x2 x3 h1 h2 h3 h12 h13 => ?_⟩
  have hinj : Function.Injective (fun y : α => Fin.castLE hα (e y)) :=
    (Fin.castLE_injective hα).comp e.injective
  exact H x1 x2 x3 h1 h2 h3 (hinj h12) (hinj h13)

def vp (p : ℕ) (z : ℤ) : ℕ := z.natAbs.factorization p

theorem pow_dvd_iff_vp {p : ℕ} (hp : p.Prime) {z : ℤ} (hz : z ≠ 0) (n : ℕ) :
    (p : ℤ) ^ n ∣ z ↔ n ≤ vp p z := by
  rw [← Int.natCast_pow, Int.natCast_dvd, hp.pow_dvd_iff_le_factorization (Int.natAbs_ne_zero.mpr hz)]
  rfl

theorem decomp_int {p : ℕ} (hp : p.Prime) {z : ℤ} (hz : z ≠ 0) :
    ∃ c : ℤ, z = (p : ℤ) ^ vp p z * c ∧ ¬ (p : ℤ) ∣ c := by
  obtain ⟨c, hc⟩ := (pow_dvd_iff_vp hp hz _).mpr le_rfl
  refine ⟨c, hc, fun hdvd => ?_⟩
  have h1 : (p : ℤ) ^ (vp p z + 1) ∣ (p : ℤ) ^ vp p z * c := by
    rw [pow_succ]; exact mul_dvd_mul_left _ hdvd
  rw [← hc] at h1
  have := (pow_dvd_iff_vp hp hz _).mp h1
  omega

theorem decomp_nat {p : ℕ} (hp : p.Prime) {x : ℕ} (hx : 0 < x) :
    (x : ℤ) = (p : ℤ) ^ x.factorization p * ((x / p ^ x.factorization p : ℕ) : ℤ) ∧
      Nat.Coprime (x / p ^ x.factorization p) p := by
  refine ⟨?_, (Nat.coprime_comm).mp (Nat.coprime_ordCompl hp hx.ne')⟩
  have := Nat.ordProj_mul_ordCompl_eq_self x p
  exact_mod_cast this.symm

theorem not_dvd_of_coprime {p : ℕ} (hp : p.Prime) {u : ℕ} (hu : Nat.Coprime u p) :
    ¬ (p : ℤ) ∣ (u : ℤ) := by
  intro h
  have h' : p ∣ u := by exact_mod_cast h
  have := Nat.Coprime.coprime_dvd_left h' hu
  rw [Nat.coprime_self] at this
  exact hp.one_lt.ne' this

theorem not_dvd_mul {p : ℕ} (hp : p.Prime) {a b : ℤ} (ha : ¬ (p : ℤ) ∣ a) (hb : ¬ (p : ℤ) ∣ b) :
    ¬ (p : ℤ) ∣ a * b := by
  intro h
  rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd h with h | h
  · exact ha h
  · exact hb h

theorem no_strict_min {p : ℕ} (hp : p.Prime) {w1 w2 w3 : ℤ} {n1 n2 n3 : ℕ}
    (hw1 : ¬ (p : ℤ) ∣ w1)
    (hsum : (p : ℤ) ^ n1 * w1 + (p : ℤ) ^ n2 * w2 + (p : ℤ) ^ n3 * w3 = 0)
    (h2 : n1 < n2) (h3 : n1 < n3) : False := by
  have d2 : (p : ℤ) ^ (n1 + 1) ∣ (p : ℤ) ^ n2 * w2 :=
    Dvd.dvd.mul_right (pow_dvd_pow _ h2) _
  have d3 : (p : ℤ) ^ (n1 + 1) ∣ (p : ℤ) ^ n3 * w3 :=
    Dvd.dvd.mul_right (pow_dvd_pow _ h3) _
  have d1 : (p : ℤ) ^ (n1 + 1) ∣ (p : ℤ) ^ n1 * w1 := by
    have : (p : ℤ) ^ n1 * w1 = -((p : ℤ) ^ n2 * w2 + (p : ℤ) ^ n3 * w3) := by linarith
    rw [this]
    exact (dvd_add d2 d3).neg_right
  rw [pow_succ] at d1
  have hp0 : (p : ℤ) ^ n1 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  exact hw1 ((mul_dvd_mul_iff_left hp0).mp d1)

theorem no_min3 {p : ℕ} (hp : p.Prime) {w1 w2 w3 : ℤ} {n1 n2 n3 : ℕ}
    (hw1 : ¬ (p : ℤ) ∣ w1) (hw2 : ¬ (p : ℤ) ∣ w2) (hw3 : ¬ (p : ℤ) ∣ w3)
    (hsum : (p : ℤ) ^ n1 * w1 + (p : ℤ) ^ n2 * w2 + (p : ℤ) ^ n3 * w3 = 0) :
    ¬ (n1 < n2 ∧ n1 < n3) ∧ ¬ (n2 < n1 ∧ n2 < n3) ∧ ¬ (n3 < n1 ∧ n3 < n2) :=
  ⟨fun h => no_strict_min hp hw1 hsum h.1 h.2,
   fun h => no_strict_min hp hw2 (w2 := w1) (w3 := w3) (n2 := n1) (n3 := n3)
     (by linear_combination hsum) h.1 h.2,
   fun h => no_strict_min hp hw3 (w2 := w1) (w3 := w2) (n2 := n1) (n3 := n2)
     (by linear_combination hsum) h.1 h.2⟩

theorem eq_case {p : ℕ} (hp : p.Prime) {w1 w2 w3 : ℤ} {n n3 k : ℕ}
    (hw3 : ¬ (p : ℤ) ∣ w3) (hk : ¬ (p : ℤ) ^ (k + 1) ∣ w1 + w2)
    (hsum : (p : ℤ) ^ n * w1 + (p : ℤ) ^ n * w2 + (p : ℤ) ^ n3 * w3 = 0) :
    n ≤ n3 ∧ n3 ≤ n + k := by
  constructor
  · by_contra hc
    replace hc : n3 < n := by omega
    exact no_strict_min hp hw3 (n2 := n) (n3 := n) (w2 := w1) (w3 := w2) (by linarith) hc hc
  · by_contra hc
    replace hc : n + k < n3 := by omega
    apply hk
    have hp0 : (p : ℤ) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
    have : (p : ℤ) ^ n * (p : ℤ) ^ (k + 1) ∣ (p : ℤ) ^ n * (w1 + w2) := by
      have e : (p : ℤ) ^ n * (w1 + w2) = -((p : ℤ) ^ n3 * w3) := by linarith
      rw [e, ← pow_add]
      exact (Dvd.dvd.mul_right (pow_dvd_pow _ (by omega)) _).neg_right
    exact (mul_dvd_mul_iff_left hp0).mp this

theorem sep2 {d X : ℕ} (hd : 0 < d) : ((X + d) / d) % 2 ≠ (X / d) % 2 := by
  rw [Nat.add_div_right X hd]
  omega

theorem sep7 {L Y Z : ℕ} (hL : 0 < L) (hZY : Z ≤ Y) (h1 : L ≤ 7 * (Y - Z)) (h2 : 7 * (Y - Z) ≤ 7 * L) :
    (7 * Y / L) % 8 ≠ (7 * Z / L) % 8 := by
  have e1 : (7 * Z + L) / L = 7 * Z / L + 1 := Nat.add_div_right _ hL
  have e2 : (7 * Z + 7 * L) / L = 7 * Z / L + 7 := Nat.add_mul_div_right _ _ hL
  have l1 : (7 * Z + L) / L ≤ 7 * Y / L := Nat.div_le_div_right (by omega)
  have l2 : 7 * Y / L ≤ (7 * Z + 7 * L) / L := Nat.div_le_div_right (by omega)
  omega


theorem sep2' {d X Y : ℕ} (hd : 0 < d) (h : Y = X + d) : (Y / d) % 2 ≠ (X / d) % 2 := by
  subst h; exact sep2 hd

theorem term_eq {p : ℕ} {a c : ℤ} {x : ℕ} {e X : ℕ} {u : ℕ} (ha : a = (p : ℤ) ^ e * c)
    (hx : (x : ℤ) = (p : ℤ) ^ X * (u : ℤ)) : a * x = (p : ℤ) ^ (e + X) * (c * u) := by
  rw [ha, hx, pow_add]; ring

theorem good_distinct {p : ℕ} (hp : p.Prime) {a1 a2 a3 : ℤ} (h1 : a1 ≠ 0) (h2 : a2 ≠ 0)
    (h3 : a3 ≠ 0) (h12 : vp p a1 ≠ vp p a2) (h13 : vp p a1 ≠ vp p a3) (h23 : vp p a2 ≠ vp p a3) :
    Good a1 a2 a3 := by
  obtain ⟨c1, hc1, hc1'⟩ := decomp_int hp h1
  obtain ⟨c2, hc2, hc2'⟩ := decomp_int hp h2
  obtain ⟨c3, hc3, hc3'⟩ := decomp_int hp h3
  set e1 := vp p a1
  set e2 := vp p a2
  set e3 := vp p a3
  let δ : ℕ → ℕ → ℕ := fun a b => a - b + (b - a)
  let s : ℕ → ℕ → Fin 2 := fun d X => ⟨(X / d) % 2, Nat.mod_lt _ (by norm_num)⟩
  let col : ℕ → Fin 2 × Fin 2 × Fin 2 := fun x =>
    (s (δ e1 e2) (x.factorization p), s (δ e1 e3) (x.factorization p),
      s (δ e2 e3) (x.factorization p))
  refine good_of_col (by simp) col (fun x1 x2 x3 hx1 hx2 hx3 hc12 hc13 hsum => ?_)
  obtain ⟨hx1e, hu1⟩ := decomp_nat hp hx1
  obtain ⟨hx2e, hu2⟩ := decomp_nat hp hx2
  obtain ⟨hx3e, hu3⟩ := decomp_nat hp hx3
  set X1 := x1.factorization p
  set X2 := x2.factorization p
  set X3 := x3.factorization p
  have w1 := not_dvd_mul hp hc1' (not_dvd_of_coprime hp hu1)
  have w2 := not_dvd_mul hp hc2' (not_dvd_of_coprime hp hu2)
  have w3 := not_dvd_mul hp hc3' (not_dvd_of_coprime hp hu3)
  rw [term_eq hc1 hx1e, term_eq hc2 hx2e, term_eq hc3 hx3e] at hsum
  obtain ⟨m1, m2, m3⟩ := no_min3 hp w1 w2 w3 hsum
  have hc23 : col x2 = col x3 := hc12.symm.trans hc13
  have k12 := congrArg (fun c => (c.1 : ℕ)) hc12
  have k13 := congrArg (fun c => (c.2.1 : ℕ)) hc13
  have k23 := congrArg (fun c => (c.2.2 : ℕ)) hc23
  simp only [col, s] at k12 k13 k23
  have pos : ∀ a b : ℕ, a ≠ b → 0 < δ a b := fun a b h => by simp only [δ]; omega
  rcases (show e1 + X1 = e2 + X2 ∨ e1 + X1 = e3 + X3 ∨ e2 + X2 = e3 + X3 by omega) with h | h | h
  · rcases Nat.lt_or_gt_of_ne h12 with h' | h'
    · exact sep2' (pos _ _ h12) (show X1 = X2 + δ e1 e2 by simp only [δ]; omega) k12
    · exact sep2' (pos _ _ h12) (show X2 = X1 + δ e1 e2 by simp only [δ]; omega) k12.symm
  · rcases Nat.lt_or_gt_of_ne h13 with h' | h'
    · exact sep2' (pos _ _ h13) (show X1 = X3 + δ e1 e3 by simp only [δ]; omega) k13
    · exact sep2' (pos _ _ h13) (show X3 = X1 + δ e1 e3 by simp only [δ]; omega) k13.symm
  · rcases Nat.lt_or_gt_of_ne h23 with h' | h'
    · exact sep2' (pos _ _ h23) (show X2 = X3 + δ e2 e3 by simp only [δ]; omega) k23
    · exact sep2' (pos _ _ h23) (show X3 = X2 + δ e2 e3 by simp only [δ]; omega) k23.symm

theorem good_core {p : ℕ} (hp : p.Prime) {c1 c2 c3 : ℤ} {β γ k : ℕ}
    (h1 : ¬ (p : ℤ) ∣ c1) (h2 : ¬ (p : ℤ) ∣ c2) (h3 : ¬ (p : ℤ) ∣ c3)
    (hk : ¬ (p : ℤ) ^ (k + 1) ∣ c1 + c2) (C0 : ℕ → Fin 8)
    (hC0 : ∀ X X3 : ℕ, β + X ≤ γ + X3 → γ + X3 ≤ β + X + k → C0 X ≠ C0 X3) :
    Good ((p : ℤ) ^ β * c1) ((p : ℤ) ^ β * c2) ((p : ℤ) ^ γ * c3) := by
  obtain ⟨χ, hχ⟩ := unit_col hp (k + 1) c1 c2 h1 h2 hk
  let col : ℕ → Fin 8 × Fin 3 := fun x =>
    (C0 (x.factorization p), χ (x / p ^ x.factorization p))
  refine good_of_col (by simp) col (fun x1 x2 x3 hx1 hx2 hx3 hc12 hc13 hsum => ?_)
  obtain ⟨hx1e, hu1⟩ := decomp_nat hp hx1
  obtain ⟨hx2e, hu2⟩ := decomp_nat hp hx2
  obtain ⟨hx3e, hu3⟩ := decomp_nat hp hx3
  set X1 := x1.factorization p
  set X2 := x2.factorization p
  set X3 := x3.factorization p
  have w1 := not_dvd_mul hp h1 (not_dvd_of_coprime hp hu1)
  have w2 := not_dvd_mul hp h2 (not_dvd_of_coprime hp hu2)
  have w3 := not_dvd_mul hp h3 (not_dvd_of_coprime hp hu3)
  rw [term_eq rfl hx1e, term_eq rfl hx2e, term_eq rfl hx3e] at hsum
  have a12 := congrArg Prod.fst hc12
  have a13 := congrArg Prod.fst hc13
  have b12 := congrArg Prod.snd hc12
  simp only [col] at a12 a13 b12
  obtain ⟨m1, m2, m3⟩ := no_min3 hp w1 w2 w3 hsum
  rcases lt_trichotomy X1 X2 with h | h | h
  · exact hC0 X1 X3 (by omega) (by omega) a13
  · have hk' := hχ _ _ hu1 hu2 b12
    have hsum' : (p : ℤ) ^ (β + X1) * (c1 * ((x1 / p ^ X1 : ℕ) : ℤ)) +
        (p : ℤ) ^ (β + X1) * (c2 * ((x2 / p ^ X2 : ℕ) : ℤ)) +
        (p : ℤ) ^ (γ + X3) * (c3 * ((x3 / p ^ X3 : ℕ) : ℤ)) = 0 := by
      have e : (p : ℤ) ^ (β + X2) = (p : ℤ) ^ (β + X1) := by rw [h]
      rw [e] at hsum; exact hsum
    have := eq_case hp w3 (by
      intro hd; apply hk'; convert hd using 1) hsum'
    exact hC0 X1 X3 this.1 this.2 a13
  · exact hC0 X2 X3 (by omega) (by omega) (a12.symm.trans a13)


theorem good_L6 {p : ℕ} (hp : p.Prime) {a1 a2 a3 : ℤ} (h1 : a1 ≠ 0) (h2 : a2 ≠ 0) (h3 : a3 ≠ 0)
    (h12 : a1 + a2 ≠ 0) (e1 : vp p a1 = 0) (e2 : vp p a2 = 0) (e3 : 0 < vp p a3)
    (hk : 7 * vp p (a1 + a2) ≤ 6 * vp p a3) : Good a1 a2 a3 := by
  obtain ⟨c3, hc3, hc3'⟩ := decomp_int hp h3
  have n1 : ¬ (p : ℤ) ∣ a1 := by
    rw [← pow_one (p : ℤ), pow_dvd_iff_vp hp h1]; omega
  have n2 : ¬ (p : ℤ) ∣ a2 := by
    rw [← pow_one (p : ℤ), pow_dvd_iff_vp hp h2]; omega
  have hk' : ¬ (p : ℤ) ^ (vp p (a1 + a2) + 1) ∣ a1 + a2 := by
    rw [pow_dvd_iff_vp hp h12]; omega
  have key := good_core hp n1 n2 hc3' hk' (β := 0) (γ := vp p a3)
    (fun X => ⟨(7 * X / vp p a3) % 8, Nat.mod_lt _ (by norm_num)⟩) (by
      intro X X3 hA hB hC
      simp only [Fin.mk.injEq] at hC
      exact sep7 e3 (by omega : X3 ≤ X) (by omega) (by omega) hC)
  rw [pow_zero, one_mul, one_mul, ← hc3] at key
  exact key

theorem good_L5 {p : ℕ} (hp : p.Prime) {a1 a2 a3 : ℤ} (h1 : a1 ≠ 0) (h2 : a2 ≠ 0) (h3 : a3 ≠ 0)
    (h12 : a1 + a2 ≠ 0) (e3 : vp p a3 = 0) (e12 : vp p a1 = vp p a2) (e1 : 0 < vp p a1)
    (hk : vp p (a1 + a2) ≤ 7 * vp p a1) : Good a1 a2 a3 := by
  obtain ⟨c1, hc1, hc1'⟩ := decomp_int hp h1
  obtain ⟨c2, hc2, hc2'⟩ := decomp_int hp h2
  rw [← e12] at hc2
  have n3 : ¬ (p : ℤ) ∣ a3 := by
    rw [← pow_one (p : ℤ), pow_dvd_iff_vp hp h3]; omega
  have e : a1 + a2 = (p : ℤ) ^ vp p a1 * (c1 + c2) := by rw [mul_add, ← hc1, ← hc2]
  have hβ : vp p a1 ≤ vp p (a1 + a2) := by
    rw [← pow_dvd_iff_vp hp h12, e]
    exact dvd_mul_right _ _
  have hk' : ¬ (p : ℤ) ^ (vp p (a1 + a2) - vp p a1 + 1) ∣ c1 + c2 := by
    intro hd
    have h' := mul_dvd_mul_left ((p : ℤ) ^ vp p a1) hd
    rw [← e, ← pow_add, pow_dvd_iff_vp hp h12] at h'
    omega
  have key := good_core hp hc1' hc2' n3 hk' (β := vp p a1) (γ := 0)
    (fun X => ⟨(7 * X / (7 * vp p a1)) % 8, Nat.mod_lt _ (by norm_num)⟩) (by
      intro X X3 hA hB hC
      simp only [Fin.mk.injEq] at hC
      exact sep7 (by omega : 0 < 7 * vp p a1) (by omega : X ≤ X3) (by omega) (by omega) hC.symm)
  rw [pow_zero, one_mul, ← hc1, ← hc2] at key
  exact key

theorem good_swap12 {a1 a2 a3 : ℤ} (h : Good a1 a2 a3) : Good a2 a1 a3 := by
  obtain ⟨col, hc⟩ := h
  refine ⟨col, fun x1 x2 x3 h1 h2 h3 c12 c13 hs => ?_⟩
  exact hc x2 x1 x3 h2 h1 h3 c12.symm (c12.symm.trans c13) (by linarith)

theorem good_swap23 {a1 a2 a3 : ℤ} (h : Good a1 a2 a3) : Good a1 a3 a2 := by
  obtain ⟨col, hc⟩ := h
  refine ⟨col, fun x1 x2 x3 h1 h2 h3 c12 c13 hs => ?_⟩
  exact hc x1 x3 x2 h1 h3 h2 c13 c12 (by linarith)

theorem good_neg {a1 a2 a3 : ℤ} (h : Good a1 a2 a3) : Good (-a1) (-a2) (-a3) := by
  obtain ⟨col, hc⟩ := h
  refine ⟨col, fun x1 x2 x3 h1 h2 h3 c12 c13 hs => ?_⟩
  exact hc x1 x2 x3 h1 h2 h3 c12 c13 (by linarith)

theorem good_scale {a1 a2 a3 : ℤ} (g : ℤ) (hg : g ≠ 0) (h : Good a1 a2 a3) :
    Good (g * a1) (g * a2) (g * a3) := by
  obtain ⟨col, hc⟩ := h
  refine ⟨col, fun x1 x2 x3 h1 h2 h3 c12 c13 hs => ?_⟩
  apply hc x1 x2 x3 h1 h2 h3 c12 c13
  have : g * (a1 * x1 + a2 * x2 + a3 * x3) = 0 := by linear_combination hs
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hg
  · exact h

theorem good_arch {T V W : ℤ} (hT : 0 < T) (hTV : T < V) (hVW : V ≤ W)
    (h : (V + W) * T ^ 22 ≤ V ^ 23) : Good T (-V) (-W) := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hVr : (T : ℝ) < V := by exact_mod_cast hTV
  have hWr : (V : ℝ) ≤ W := by exact_mod_cast hVW
  have hr : ((V : ℝ) + W) * (T : ℝ) ^ 22 ≤ (V : ℝ) ^ 23 := by exact_mod_cast h
  set d : ℝ := (V : ℝ) / T with hd_def
  have hd : 1 < d := by rw [hd_def, one_lt_div hTr]; exact hVr
  set L := Real.log d with hL_def
  have hL : 0 < L := Real.log_pos hd
  let f : ℕ → ℤ := fun x => ⌊Real.log (x : ℝ) / L⌋
  let col : ℕ → ZMod 24 := fun x => ((f x : ℤ) : ZMod 24)
  refine good_of_col (by simp) col (fun x1 x2 x3 hx1 hx2 hx3 c12 c13 hsum => ?_)
  set M := max x2 x3 with hM_def
  have hcM : col x1 = col M := by
    rcases max_choice x2 x3 with h' | h' <;> rw [hM_def, h'] <;> assumption
  have hMpos : 0 < M := lt_max_of_lt_left hx2
  have hsumr : (T : ℝ) * x1 = V * x2 + W * x3 := by
    have : (T : ℤ) * x1 = V * x2 + W * x3 := by linarith
    exact_mod_cast this
  have hx2M : (x2 : ℝ) ≤ M := by exact_mod_cast le_max_left x2 x3
  have hx3M : (x3 : ℝ) ≤ M := by exact_mod_cast le_max_right x2 x3
  have hMle : (M : ℝ) ≤ x2 + x3 := by
    have : M ≤ x2 + x3 := max_le (by omega) (by omega)
    exact_mod_cast this
  have hx2p : (0 : ℝ) ≤ x2 := by positivity
  have hx3p : (0 : ℝ) ≤ x3 := by positivity
  have hMr : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hx1r : (0 : ℝ) < x1 := by exact_mod_cast hx1
  have lo : (V : ℝ) * M ≤ T * x1 := by
    rw [hsumr]; nlinarith
  have hi : (T : ℝ) * x1 ≤ (V + W) * M := by
    rw [hsumr]; nlinarith
  have lo' : d * M ≤ x1 := by
    rw [hd_def, div_mul_eq_mul_div, div_le_iff₀ hTr]; linarith
  have hlog1 : L + Real.log M ≤ Real.log x1 := by
    rw [hL_def, ← Real.log_mul (by positivity) hMr.ne']
    exact Real.log_le_log (by positivity) lo'
  have hf1 : f M + 1 ≤ f x1 := by
    have : Real.log M / L + 1 ≤ Real.log x1 / L := by
      rw [div_add_one hL.ne', div_le_div_iff_of_pos_right hL]; linarith
    have := Int.floor_le_floor this
    rw [Int.floor_add_one] at this
    exact this
  have hdiv : (24 : ℤ) ∣ f x1 - f M := by
    have := (ZMod.intCast_eq_intCast_iff_dvd_sub (f M) (f x1) 24).mp hcM.symm
    exact_mod_cast this
  have hf24 : f M + 24 ≤ f x1 := by omega
  have k1 : ((f x1 : ℤ) : ℝ) ≤ Real.log x1 / L := Int.floor_le _
  have k2 : Real.log M / L < ((f M : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  have k3 : ((f M : ℤ) : ℝ) + 24 ≤ ((f x1 : ℤ) : ℝ) := by exact_mod_cast hf24
  have k4 : Real.log M + 23 * L < Real.log x1 := by
    have : Real.log M / L + 23 < Real.log x1 / L := by linarith
    rw [← sub_pos] at this ⊢
    have e : Real.log x1 / L - (Real.log M / L + 23) = (Real.log x1 - (Real.log M + 23 * L)) / L := by
      field_simp
    rw [e] at this
    exact (div_pos_iff_of_pos_right hL).mp this
  have k5 : (M : ℝ) * d ^ 23 < x1 := by
    rw [← Real.log_lt_log_iff (by positivity) hx1r, Real.log_mul hMr.ne' (by positivity),
      Real.log_pow]
    push_cast
    linarith
  have k6 : (T : ℝ) * (M * d ^ 23) < (V + W) * M := by
    calc (T : ℝ) * (M * d ^ 23) < T * x1 := by gcongr
      _ ≤ (V + W) * M := hi
  have k7 : (T : ℝ) * d ^ 23 < V + W := by
    have : (T * d ^ 23) * M < (V + W) * M := by linarith
    exact lt_of_mul_lt_mul_right this hMr.le
  have k8 : (V : ℝ) ^ 23 < (V + W) * T ^ 22 := by
    rw [hd_def, div_pow] at k7
    have e : (T : ℝ) * ((V : ℝ) ^ 23 / (T : ℝ) ^ 23) = (V : ℝ) ^ 23 / (T : ℝ) ^ 22 := by
      field_simp
    rw [e, div_lt_iff₀ (by positivity)] at k7
    exact k7
  linarith

theorem caseM {T V W : ℤ} (hT : 0 < T) (hTV : T < V) (hVW : V < W)
    (H3 : (T * V * W) ^ 42 ≤ ((V - T) * (T + W) * (W - V)) ^ 12 * (T + W - V) ^ 37)
    (H4 : (T * V) ^ 6 * W ^ 42 ≤ (T + W) ^ 7 * (W - V) ^ 7 * (V - T) ^ 49) : False := by
  revert H3 H4
  have hV : 0 < V := by linarith
  have hW : 0 < W := by linarith
  have hV1 : 1 ≤ V := by linarith
  have hT1 : 1 ≤ T := by linarith
  have q1 : (T + W) * (W - V) < W ^ 2 := by nlinarith
  have q2 : 0 < (T + W) * (W - V) := mul_pos (by linarith) (by linarith)
  have hP : (V - T) * (T + W) * (W - V) < V * W ^ 2 := by
    rw [mul_assoc]; exact mul_lt_mul'' (by linarith) q1 (by linarith) q2.le
  have hP0 : 0 ≤ (V - T) * (T + W) * (W - V) := by
    rw [mul_assoc]; exact mul_nonneg (by linarith) q2.le
  have s0 : 0 ≤ T + W - V := by linarith
  have s1 : T + W - V ≤ W := by linarith
  have r0 : 0 ≤ V - T := by linarith
  have r1 : V - T ≤ V := by linarith
  intro H3 H4
  have A1 : (T * V * W) ^ 42 < (V * W ^ 2) ^ 12 * W ^ 37 := by
    calc (T * V * W) ^ 42 ≤ _ := H3
      _ ≤ ((V - T) * (T + W) * (W - V)) ^ 12 * W ^ 37 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ s0 s1 37) (pow_nonneg hP0 _)
      _ < (V * W ^ 2) ^ 12 * W ^ 37 :=
          mul_lt_mul_of_pos_right (pow_lt_pow_left₀ hP hP0 (by norm_num)) (by positivity)
  have B1 : T ^ 42 * V ^ 30 < W ^ 19 := by
    have : (T ^ 42 * V ^ 30) * (V ^ 12 * W ^ 42) < W ^ 19 * (V ^ 12 * W ^ 42) := by
      calc (T ^ 42 * V ^ 30) * (V ^ 12 * W ^ 42) = (T * V * W) ^ 42 := by ring
        _ < (V * W ^ 2) ^ 12 * W ^ 37 := A1
        _ = W ^ 19 * (V ^ 12 * W ^ 42) := by ring
    exact lt_of_mul_lt_mul_right this (by positivity)
  have A2 : (T * V) ^ 6 * W ^ 42 < (W ^ 2) ^ 7 * V ^ 49 := by
    calc (T * V) ^ 6 * W ^ 42 ≤ _ := H4
      _ = ((T + W) * (W - V)) ^ 7 * (V - T) ^ 49 := by rw [mul_pow]
      _ ≤ ((T + W) * (W - V)) ^ 7 * V ^ 49 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ r0 r1 49) (pow_nonneg q2.le _)
      _ < (W ^ 2) ^ 7 * V ^ 49 :=
          mul_lt_mul_of_pos_right (pow_lt_pow_left₀ q1 q2.le (by norm_num)) (by positivity)
  have B2 : T ^ 6 * W ^ 28 < V ^ 43 := by
    have : (T ^ 6 * W ^ 28) * (V ^ 6 * W ^ 14) < V ^ 43 * (V ^ 6 * W ^ 14) := by
      calc (T ^ 6 * W ^ 28) * (V ^ 6 * W ^ 14) = (T * V) ^ 6 * W ^ 42 := by ring
        _ < (W ^ 2) ^ 7 * V ^ 49 := A2
        _ = V ^ 43 * (V ^ 6 * W ^ 14) := by ring
    exact lt_of_mul_lt_mul_right this (by positivity)
  clear H3 H4 A1 A2
  have C1 : V ^ 30 < W ^ 19 :=
    lt_of_le_of_lt (le_mul_of_one_le_left (by positivity) (one_le_pow₀ hT1)) B1
  have C2 : W ^ 28 < V ^ 43 :=
    lt_of_le_of_lt (le_mul_of_one_le_left (by positivity) (one_le_pow₀ hT1)) B2
  have : V ^ 840 < V ^ 817 := by
    calc V ^ 840 = (V ^ 30) ^ 28 := by ring
      _ < (W ^ 19) ^ 28 := pow_lt_pow_left₀ C1 (by positivity) (by norm_num)
      _ = (W ^ 28) ^ 19 := by ring
      _ < (V ^ 43) ^ 19 := pow_lt_pow_left₀ C2 (by positivity) (by norm_num)
      _ = V ^ 817 := by ring
  exact absurd this (not_lt.mpr (pow_le_pow_right₀ hV1 (by norm_num)))

theorem caseS {T V W : ℤ} (hT : 0 < T) (hTV : T < V) (hVW : V ≤ W)
    (h : 3 ≤ T ∨ (T ≤ 2 ∧ V ^ 23 < (V + W) * T ^ 22))
    (H3 : (T * V * W) ^ 42 ≤ ((V - T) * (W - T) * (V + W)) ^ 12 * (V + W - T) ^ 37)
    (H4 : (T * V) ^ 6 * W ^ 42 ≤ (W - T) ^ 7 * (V + W) ^ 7 * (V - T) ^ 49) : False := by
  revert H3 H4
  have hV : 0 < V := by linarith
  have hW : 0 < W := by linarith
  have q1 : (V - T) * (W - T) < V * W :=
    mul_lt_mul'' (by linarith) (by linarith) (by linarith) (by linarith)
  have q0 : 0 ≤ (V - T) * (W - T) := mul_nonneg (by linarith) (by linarith)
  have hP : (V - T) * (W - T) * (V + W) < V * W * (2 * W) :=
    mul_lt_mul q1 (by linarith) (by linarith) (by positivity)
  have hP0 : 0 ≤ (V - T) * (W - T) * (V + W) := mul_nonneg q0 (by linarith)
  have q3 : (W - T) * (V + W) < W * (2 * W) :=
    mul_lt_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have q4 : 0 ≤ (W - T) * (V + W) := mul_nonneg (by linarith) (by linarith)
  have s0 : 0 ≤ V + W - T := by linarith
  have s1 : V + W - T ≤ 2 * W := by linarith
  have r0 : 0 ≤ V - T := by linarith
  have r1 : V - T ≤ V := by linarith
  have F0 : (V + W) * T ^ 22 ≤ 2 * W * T ^ 22 :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  intro H3 H4
  have A1 : (T * V * W) ^ 42 < (V * W * (2 * W)) ^ 12 * (2 * W) ^ 37 := by
    calc (T * V * W) ^ 42 ≤ _ := H3
      _ ≤ ((V - T) * (W - T) * (V + W)) ^ 12 * (2 * W) ^ 37 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ s0 s1 37) (pow_nonneg hP0 _)
      _ < (V * W * (2 * W)) ^ 12 * (2 * W) ^ 37 :=
          mul_lt_mul_of_pos_right (pow_lt_pow_left₀ hP hP0 (by norm_num)) (by positivity)
  have B1 : T ^ 42 * V ^ 30 < 2 ^ 49 * W ^ 19 := by
    have : (T ^ 42 * V ^ 30) * (V ^ 12 * W ^ 42) < (2 ^ 49 * W ^ 19) * (V ^ 12 * W ^ 42) := by
      calc (T ^ 42 * V ^ 30) * (V ^ 12 * W ^ 42) = (T * V * W) ^ 42 := by ring
        _ < _ := A1
        _ = (2 ^ 49 * W ^ 19) * (V ^ 12 * W ^ 42) := by ring
    exact lt_of_mul_lt_mul_right this (by positivity)
  have A2 : (T * V) ^ 6 * W ^ 42 < (W * (2 * W)) ^ 7 * V ^ 49 := by
    calc (T * V) ^ 6 * W ^ 42 ≤ _ := H4
      _ = ((W - T) * (V + W)) ^ 7 * (V - T) ^ 49 := by rw [mul_pow]
      _ ≤ ((W - T) * (V + W)) ^ 7 * V ^ 49 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ r0 r1 49) (pow_nonneg q4 _)
      _ < (W * (2 * W)) ^ 7 * V ^ 49 :=
          mul_lt_mul_of_pos_right (pow_lt_pow_left₀ q3 q4 (by norm_num)) (by positivity)
  have B2 : T ^ 6 * W ^ 28 < 2 ^ 7 * V ^ 43 := by
    have : (T ^ 6 * W ^ 28) * (V ^ 6 * W ^ 14) < (2 ^ 7 * V ^ 43) * (V ^ 6 * W ^ 14) := by
      calc (T ^ 6 * W ^ 28) * (V ^ 6 * W ^ 14) = (T * V) ^ 6 * W ^ 42 := by ring
        _ < _ := A2
        _ = (2 ^ 7 * V ^ 43) * (V ^ 6 * W ^ 14) := by ring
    exact lt_of_mul_lt_mul_right this (by positivity)
  clear H3 H4 A1 A2
  rcases h with h | ⟨h2, h⟩
  · generalize hc : (2 : ℤ) = c at B1 B2
    have hc0 : 0 < c := hc ▸ two_pos
    have E : T ^ 1290 * V ^ 840 < c ^ 1505 * V ^ 817 := by
      calc T ^ 1290 * V ^ 840 = (T ^ 42 * V ^ 30) ^ 28 * T ^ 114 := by ring
        _ < (c ^ 49 * W ^ 19) ^ 28 * T ^ 114 :=
            mul_lt_mul_of_pos_right (pow_lt_pow_left₀ B1 (by positivity) (by norm_num))
              (by positivity)
        _ = c ^ 1372 * (T ^ 6 * W ^ 28) ^ 19 := by ring
        _ < c ^ 1372 * (c ^ 7 * V ^ 43) ^ 19 :=
            mul_lt_mul_of_pos_left (pow_lt_pow_left₀ B2 (by positivity) (by norm_num))
              (by positivity)
        _ = c ^ 1505 * V ^ 817 := by ring
    have e1 : (3 : ℤ) ^ 1290 ≤ T ^ 1290 := pow_le_pow_left₀ (by norm_num) h _
    have e2 : V ^ 817 ≤ V ^ 840 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have e3 : c ^ 1505 < 3 ^ 1290 := by
      rw [← hc]
      calc (2 : ℤ) ^ 1505 = (2 ^ 7) ^ 215 := by rw [← pow_mul]
        _ < (3 ^ 6) ^ 215 := pow_lt_pow_left₀ (by norm_num) (by norm_num) (by norm_num)
        _ = 3 ^ 1290 := by rw [← pow_mul]
    have e4 : (3 : ℤ) ^ 1290 * V ^ 817 ≤ T ^ 1290 * V ^ 840 :=
      mul_le_mul e1 e2 (by positivity) (by positivity)
    have e5 : c ^ 1505 * V ^ 817 < 3 ^ 1290 * V ^ 817 :=
      mul_lt_mul_of_pos_right e3 (by positivity)
    exact absurd (lt_of_lt_of_le e5 e4) (not_lt.mpr E.le)
  · have F1 : V ^ 23 < 2 * W * T ^ 22 := lt_of_lt_of_le h F0
    have F : V ^ 601 * V ^ 43 < (2 ^ 35 * T ^ 610) * V ^ 43 := by
      calc V ^ 601 * V ^ 43 = (V ^ 23) ^ 28 := by ring
        _ < (2 * W * T ^ 22) ^ 28 := pow_lt_pow_left₀ F1 (by positivity) (by norm_num)
        _ = (2 ^ 28 * T ^ 610) * (T ^ 6 * W ^ 28) := by ring
        _ < (2 ^ 28 * T ^ 610) * (2 ^ 7 * V ^ 43) := mul_lt_mul_of_pos_left B2 (by positivity)
        _ = (2 ^ 35 * T ^ 610) * V ^ 43 := by ring
    have G := lt_of_mul_lt_mul_right F (by positivity)
    have hT12 : T = 1 ∨ T = 2 := by omega
    rcases hT12 with rfl | rfl
    · have : (2 : ℤ) ^ 601 ≤ V ^ 601 := pow_le_pow_left₀ (by norm_num) (by linarith) _
      have e : (2 : ℤ) ^ 35 * 1 ^ 610 < 2 ^ 601 := by
        rw [one_pow, mul_one]; exact pow_lt_pow_right₀ (by norm_num) (by norm_num)
      exact absurd (lt_of_lt_of_le e this) (not_lt.mpr G.le)
    · have : (3 : ℤ) ^ 601 ≤ V ^ 601 := pow_le_pow_left₀ (by norm_num) (by linarith) _
      have e : (2 : ℤ) ^ 35 * 2 ^ 610 < 3 ^ 601 := by
        calc (2 : ℤ) ^ 35 * 2 ^ 610 < 2 ^ 646 := by
              rw [← pow_add]; exact pow_lt_pow_right₀ (by norm_num) (by norm_num)
          _ = (2 ^ 38) ^ 17 := by rw [← pow_mul]
          _ < (3 ^ 35) ^ 17 := pow_lt_pow_left₀ (by norm_num) (by norm_num) (by norm_num)
          _ = 3 ^ 595 := by rw [← pow_mul]
          _ ≤ 3 ^ 601 := pow_le_pow_right₀ (by norm_num) (by norm_num)
      exact absurd (lt_of_lt_of_le e this) (not_lt.mpr G.le)

theorem caseL {T V W S : ℤ} (hT : 2 ≤ T) (hTV : T ≤ V) (hVW : V < W) (hS0 : 0 ≤ S) (hSW : S < W)
    (H3 : (T * V * W) ^ 42 ≤ ((T + V) * (W - T) * (W - V)) ^ 12 * S ^ 37)
    (H4 : (T * V) ^ 6 * W ^ 42 ≤ (W - T) ^ 7 * (W - V) ^ 7 * (T + V) ^ 49) : False := by
  revert H3 H4
  have hV : 0 < V := by linarith
  have hW : 0 < W := by linarith
  have q1 : (T + V) * (W - T) < 2 * V * W :=
    mul_lt_mul' (by linarith) (by linarith) (by linarith) (by linarith)
  have q0 : 0 ≤ (T + V) * (W - T) := mul_nonneg (by linarith) (by linarith)
  have hP : (T + V) * (W - T) * (W - V) < 2 * V * W * W :=
    mul_lt_mul'' q1 (by linarith) q0 (by linarith)
  have hP0 : 0 ≤ (T + V) * (W - T) * (W - V) := mul_nonneg q0 (by linarith)
  have q3 : (W - T) * (W - V) < W * W :=
    mul_lt_mul'' (by linarith) (by linarith) (by linarith) (by linarith)
  have q4 : 0 ≤ (W - T) * (W - V) := mul_nonneg (by linarith) (by linarith)
  have r0 : 0 ≤ T + V := by linarith
  have r1 : T + V ≤ 2 * V := by linarith
  intro H3 H4
  have A1 : (T * V * W) ^ 42 < (2 * V * W * W) ^ 12 * W ^ 37 := by
    calc (T * V * W) ^ 42 ≤ _ := H3
      _ ≤ ((T + V) * (W - T) * (W - V)) ^ 12 * W ^ 37 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hS0 hSW.le 37) (pow_nonneg hP0 _)
      _ < (2 * V * W * W) ^ 12 * W ^ 37 :=
          mul_lt_mul_of_pos_right (pow_lt_pow_left₀ hP hP0 (by norm_num)) (by positivity)
  have B1 : T ^ 42 * V ^ 30 < 2 ^ 12 * W ^ 19 := by
    have : (T ^ 42 * V ^ 30) * (V ^ 12 * W ^ 42) < (2 ^ 12 * W ^ 19) * (V ^ 12 * W ^ 42) := by
      calc (T ^ 42 * V ^ 30) * (V ^ 12 * W ^ 42) = (T * V * W) ^ 42 := by ring
        _ < _ := A1
        _ = (2 ^ 12 * W ^ 19) * (V ^ 12 * W ^ 42) := by ring
    exact lt_of_mul_lt_mul_right this (by positivity)
  have A2 : (T * V) ^ 6 * W ^ 42 < (W * W) ^ 7 * (2 * V) ^ 49 := by
    calc (T * V) ^ 6 * W ^ 42 ≤ _ := H4
      _ = ((W - T) * (W - V)) ^ 7 * (T + V) ^ 49 := by rw [mul_pow]
      _ ≤ ((W - T) * (W - V)) ^ 7 * (2 * V) ^ 49 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ r0 r1 49) (pow_nonneg q4 _)
      _ < (W * W) ^ 7 * (2 * V) ^ 49 :=
          mul_lt_mul_of_pos_right (pow_lt_pow_left₀ q3 q4 (by norm_num)) (by positivity)
  have B2 : T ^ 6 * W ^ 28 < 2 ^ 49 * V ^ 43 := by
    have : (T ^ 6 * W ^ 28) * (V ^ 6 * W ^ 14) < (2 ^ 49 * V ^ 43) * (V ^ 6 * W ^ 14) := by
      calc (T ^ 6 * W ^ 28) * (V ^ 6 * W ^ 14) = (T * V) ^ 6 * W ^ 42 := by ring
        _ < _ := A2
        _ = (2 ^ 49 * V ^ 43) * (V ^ 6 * W ^ 14) := by ring
    exact lt_of_mul_lt_mul_right this (by positivity)
  clear H3 H4 A1 A2
  generalize hc : (2 : ℤ) = c at B1 B2
  have hc0 : 0 < c := hc ▸ two_pos
  have E : T ^ 1290 * V ^ 840 < c ^ 1267 * V ^ 817 := by
    calc T ^ 1290 * V ^ 840 = (T ^ 42 * V ^ 30) ^ 28 * T ^ 114 := by ring
      _ < (c ^ 12 * W ^ 19) ^ 28 * T ^ 114 :=
          mul_lt_mul_of_pos_right (pow_lt_pow_left₀ B1 (by positivity) (by norm_num))
            (by positivity)
      _ = c ^ 336 * (T ^ 6 * W ^ 28) ^ 19 := by ring
      _ < c ^ 336 * (c ^ 49 * V ^ 43) ^ 19 :=
          mul_lt_mul_of_pos_left (pow_lt_pow_left₀ B2 (by positivity) (by norm_num))
            (by positivity)
      _ = c ^ 1267 * V ^ 817 := by ring
  have e1 : c ^ 1290 ≤ T ^ 1290 := pow_le_pow_left₀ hc0.le (hc ▸ hT) _
  have e2 : V ^ 817 ≤ V ^ 840 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have e3 : c ^ 1267 < c ^ 1290 := pow_lt_pow_right₀ (by rw [← hc]; norm_num) (by norm_num)
  have e4 : c ^ 1290 * V ^ 817 ≤ T ^ 1290 * V ^ 840 :=
    mul_le_mul e1 e2 (by positivity) (by positivity)
  have e5 : c ^ 1267 * V ^ 817 < c ^ 1290 * V ^ 817 :=
    mul_lt_mul_of_pos_right e3 (by positivity)
  exact absurd (lt_of_lt_of_le e5 e4) (not_lt.mpr E.le)

theorem caseL1 {V W : ℤ} (hV : 1 ≤ V) (hVW : V + 2 ≤ W)
    (H11 : (V * W) ^ 42 ≤ (W - V) ^ 12 * (W - V - 1) ^ 49)
    (H12 : W ^ 42 ≤ (W - V) ^ 6 * (1 + V) ^ 49) : False := by
  revert H11 H12
  have hW : 0 < W := by linarith
  have a0 : 0 ≤ W - V := by linarith
  have a1 : W - V < W := by linarith
  have b0 : 0 ≤ W - V - 1 := by linarith
  have b1 : W - V - 1 ≤ W := by linarith
  intro H11 H12
  have A1 : (V * W) ^ 42 < W ^ 12 * W ^ 49 := by
    calc (V * W) ^ 42 ≤ _ := H11
      _ ≤ (W - V) ^ 12 * W ^ 49 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ b0 b1 49) (pow_nonneg a0 _)
      _ < W ^ 12 * W ^ 49 :=
          mul_lt_mul_of_pos_right (pow_lt_pow_left₀ a1 a0 (by norm_num)) (by positivity)
  have B1 : V ^ 42 < W ^ 19 := by
    have : V ^ 42 * W ^ 42 < W ^ 19 * W ^ 42 := by
      calc V ^ 42 * W ^ 42 = (V * W) ^ 42 := by ring
        _ < _ := A1
        _ = W ^ 19 * W ^ 42 := by ring
    exact lt_of_mul_lt_mul_right this (by positivity)
  have A2 : W ^ 42 < W ^ 6 * (1 + V) ^ 49 := by
    calc W ^ 42 ≤ _ := H12
      _ < W ^ 6 * (1 + V) ^ 49 :=
          mul_lt_mul_of_pos_right (pow_lt_pow_left₀ a1 a0 (by norm_num)) (by positivity)
  have B2 : W ^ 36 < (1 + V) ^ 49 := by
    have : W ^ 36 * W ^ 6 < (1 + V) ^ 49 * W ^ 6 := by
      calc W ^ 36 * W ^ 6 = W ^ 42 := by ring
        _ < _ := A2
        _ = (1 + V) ^ 49 * W ^ 6 := by ring
    exact lt_of_mul_lt_mul_right this (by positivity)
  clear H11 H12 A1 A2
  rcases eq_or_lt_of_le hV with hV1 | hV2
  · subst hV1
    have : (3 : ℤ) ^ 36 ≤ W ^ 36 := pow_le_pow_left₀ (by norm_num) (by linarith) _
    have e : ((1 : ℤ) + 1) ^ 49 < 3 ^ 36 := by norm_num
    exact absurd (lt_of_lt_of_le e this) (not_lt.mpr B2.le)
  · have hV2' : 2 ≤ V := by linarith
    have key : (1 + V) ^ 13 ≤ V ^ 21 := by
      have h1 : (2 + 2 * V) ^ 13 ≤ (3 * V) ^ 13 := pow_le_pow_left₀ (by linarith) (by linarith) _
      have h2 : (2 : ℤ) ^ 8 ≤ V ^ 8 := pow_le_pow_left₀ (by norm_num) hV2' _
      have h3 : (2 : ℤ) ^ 13 * (1 + V) ^ 13 ≤ 2 ^ 13 * V ^ 21 := by
        calc (2 : ℤ) ^ 13 * (1 + V) ^ 13 = (2 + 2 * V) ^ 13 := by
              rw [← mul_pow]; congr 1; ring
          _ ≤ (3 * V) ^ 13 := h1
          _ = 3 ^ 13 * V ^ 13 := by rw [mul_pow]
          _ ≤ 2 ^ 13 * 2 ^ 8 * V ^ 13 :=
              mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
          _ ≤ 2 ^ 13 * V ^ 8 * V ^ 13 :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by norm_num))
                (by positivity)
          _ = 2 ^ 13 * V ^ 21 := by ring
      exact le_of_mul_le_mul_left h3 (by norm_num)
    have : V ^ 1512 < V ^ 1512 := by
      calc V ^ 1512 = (V ^ 42) ^ 36 := by ring
        _ < (W ^ 19) ^ 36 := pow_lt_pow_left₀ B1 (by positivity) (by norm_num)
        _ = (W ^ 36) ^ 19 := by ring
        _ < ((1 + V) ^ 49) ^ 19 := pow_lt_pow_left₀ B2 (by positivity) (by norm_num)
        _ = (1 + V) ^ 931 := by rw [← pow_mul]
        _ ≤ (1 + V) ^ 936 := pow_le_pow_right₀ (by linarith) (by norm_num)
        _ = ((1 + V) ^ 13) ^ 72 := by rw [← pow_mul]
        _ ≤ (V ^ 21) ^ 72 := pow_le_pow_left₀ (by positivity) key _
        _ = V ^ 1512 := by ring
    exact lt_irrefl _ this

theorem arith_core (e1 e2 e3 f12 f13 f23 f123 : ℕ)
  (Z : e1 = 0 ∨ e2 = 0 ∨ e3 = 0)
  (D : ¬ (e1 ≠ e2 ∧ e1 ≠ e3 ∧ e2 ≠ e3))
  (L63 : e1 = 0 → e2 = 0 → 0 < e3 → 6 * e3 < 7 * f12)
  (L62 : e1 = 0 → e3 = 0 → 0 < e2 → 6 * e2 < 7 * f13)
  (L61 : e2 = 0 → e3 = 0 → 0 < e1 → 6 * e1 < 7 * f23)
  (L53 : e3 = 0 → e1 = e2 → 0 < e1 → 7 * e1 < f12)
  (L52 : e2 = 0 → e1 = e3 → 0 < e1 → 7 * e1 < f13)
  (L51 : e1 = 0 → e2 = e3 → 0 < e2 → 7 * e2 < f23)
  (U3 : min f12 e3 ≤ f123) (U2 : min f13 e2 ≤ f123) (U1 : min f23 e1 ≤ f123) :
  42 * (e1 + e2 + e3) ≤ 12 * (f12 + f13 + f23) + 37 * f123 ∧
  6 * e1 + 6 * e2 + 42 * e3 ≤ 7 * f13 + 7 * f23 + 49 * f12 ∧
  (e1 = 0 → 42 * (e2 + e3) ≤ 12 * f23 + 49 * f123 ∧ 42 * e3 ≤ 6 * f23 + 49 * f12) := by
  rcases Nat.eq_zero_or_pos e1 with h1 | h1 <;> rcases Nat.eq_zero_or_pos e2 with h2 | h2 <;>
    rcases Nat.eq_zero_or_pos e3 with h3 | h3
  · clear L63 L62 L61 L53 L52 L51 Z D
    refine ⟨by omega, by omega, fun h => ⟨by omega, by omega⟩⟩
  · have := L63 h1 h2 h3
    clear L63 L62 L61 L53 L52 L51 Z D
    refine ⟨by omega, by omega, fun h => ⟨by omega, by omega⟩⟩
  · have := L62 h1 h3 h2
    clear L63 L62 L61 L53 L52 L51 Z D
    refine ⟨by omega, by omega, fun h => ⟨by omega, by omega⟩⟩
  · have e : e2 = e3 := by clear L63 L62 L61 L53 L52 L51 Z; omega
    have := L51 h1 e h2
    clear L63 L62 L61 L53 L52 L51 Z D
    refine ⟨by omega, by omega, fun h => ⟨by omega, by omega⟩⟩
  · have := L61 h2 h3 h1
    clear L63 L62 L61 L53 L52 L51 Z D
    refine ⟨by omega, by omega, fun h => ⟨by omega, by omega⟩⟩
  · have e : e1 = e3 := by clear L63 L62 L61 L53 L52 L51 Z; omega
    have := L52 h2 e h1
    clear L63 L62 L61 L53 L52 L51 Z D
    refine ⟨by omega, by omega, fun h => ⟨by omega, by omega⟩⟩
  · have e : e1 = e2 := by clear L63 L62 L61 L53 L52 L51 Z; omega
    have := L53 h3 e h1
    clear L63 L62 L61 L53 L52 L51 Z D
    refine ⟨by omega, by omega, fun h => ⟨by omega, by omega⟩⟩
  · clear L63 L62 L61 L53 L52 L51 D; omega

theorem vp_mul {p : ℕ} {z w : ℤ} (hz : z ≠ 0) (hw : w ≠ 0) : vp p (z * w) = vp p z + vp p w := by
  simp only [vp, Int.natAbs_mul,
    Nat.factorization_mul (Int.natAbs_ne_zero.mpr hz) (Int.natAbs_ne_zero.mpr hw), Finsupp.add_apply]

theorem vp_pow {p : ℕ} (z : ℤ) (n : ℕ) : vp p (z ^ n) = n * vp p z := by
  simp only [vp, Int.natAbs_pow, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]

theorem vp_one (p : ℕ) : vp p 1 = 0 := by
  simp [vp]

theorem abs_le_of_vp {N M : ℤ} (hN : N ≠ 0) (hM : M ≠ 0)
    (h : ∀ p : ℕ, p.Prime → vp p N ≤ vp p M) : |N| ≤ |M| := by
  have hN' := Int.natAbs_ne_zero.mpr hN
  have hM' := Int.natAbs_ne_zero.mpr hM
  have hd : N.natAbs ∣ M.natAbs := by
    rw [← Nat.factorization_le_iff_dvd hN' hM', Finsupp.le_def]
    intro p
    by_cases hp : p.Prime
    · exact h p hp
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero hM') hd
  rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs]
  exact_mod_cast this

theorem per_prime {p : ℕ} (hp : p.Prime) {a1 a2 a3 : ℤ} (h1 : a1 ≠ 0) (h2 : a2 ≠ 0)
    (h3 : a3 ≠ 0) (s12 : a1 + a2 ≠ 0) (s13 : a1 + a3 ≠ 0) (s23 : a2 + a3 ≠ 0)
    (s123 : a1 + a2 + a3 ≠ 0) (cop : ¬ ((p : ℤ) ∣ a1 ∧ (p : ℤ) ∣ a2 ∧ (p : ℤ) ∣ a3))
    (hG : ¬ Good a1 a2 a3) :
    42 * (vp p a1 + vp p a2 + vp p a3) ≤
        12 * (vp p (a1 + a2) + vp p (a1 + a3) + vp p (a2 + a3)) + 37 * vp p (a1 + a2 + a3) ∧
    6 * vp p a1 + 6 * vp p a2 + 42 * vp p a3 ≤
        7 * vp p (a1 + a3) + 7 * vp p (a2 + a3) + 49 * vp p (a1 + a2) ∧
    (vp p a1 = 0 → 42 * (vp p a2 + vp p a3) ≤ 12 * vp p (a2 + a3) + 49 * vp p (a1 + a2 + a3) ∧
        42 * vp p a3 ≤ 6 * vp p (a2 + a3) + 49 * vp p (a1 + a2)) := by
  have Z : vp p a1 = 0 ∨ vp p a2 = 0 ∨ vp p a3 = 0 := by
    by_contra hc
    apply cop
    refine ⟨?_, ?_, ?_⟩
    · rw [← pow_one (p : ℤ), pow_dvd_iff_vp hp h1]; omega
    · rw [← pow_one (p : ℤ), pow_dvd_iff_vp hp h2]; omega
    · rw [← pow_one (p : ℤ), pow_dvd_iff_vp hp h3]; omega
  have D : ¬ (vp p a1 ≠ vp p a2 ∧ vp p a1 ≠ vp p a3 ∧ vp p a2 ≠ vp p a3) := fun h =>
    hG (good_distinct hp h1 h2 h3 h.1 h.2.1 h.2.2)
  have L63 : vp p a1 = 0 → vp p a2 = 0 → 0 < vp p a3 → 6 * vp p a3 < 7 * vp p (a1 + a2) :=
    fun e1 e2 e3 => by
      by_contra hc
      exact hG (good_L6 hp h1 h2 h3 s12 e1 e2 e3 (by omega))
  have L62 : vp p a1 = 0 → vp p a3 = 0 → 0 < vp p a2 → 6 * vp p a2 < 7 * vp p (a1 + a3) :=
    fun e1 e3 e2 => by
      by_contra hc
      exact hG (good_swap23 (good_L6 hp h1 h3 h2 s13 e1 e3 e2 (by omega)))
  have L61 : vp p a2 = 0 → vp p a3 = 0 → 0 < vp p a1 → 6 * vp p a1 < 7 * vp p (a2 + a3) :=
    fun e2 e3 e1 => by
      by_contra hc
      exact hG (good_swap12 (good_swap23 (good_L6 hp h2 h3 h1 s23 e2 e3 e1 (by omega))))
  have L53 : vp p a3 = 0 → vp p a1 = vp p a2 → 0 < vp p a1 → 7 * vp p a1 < vp p (a1 + a2) :=
    fun e3 e12 e1 => by
      by_contra hc
      exact hG (good_L5 hp h1 h2 h3 s12 e3 e12 e1 (by omega))
  have L52 : vp p a2 = 0 → vp p a1 = vp p a3 → 0 < vp p a1 → 7 * vp p a1 < vp p (a1 + a3) :=
    fun e2 e13 e1 => by
      by_contra hc
      exact hG (good_swap23 (good_L5 hp h1 h3 h2 s13 e2 e13 e1 (by omega)))
  have L51 : vp p a1 = 0 → vp p a2 = vp p a3 → 0 < vp p a2 → 7 * vp p a2 < vp p (a2 + a3) :=
    fun e1 e23 e2 => by
      by_contra hc
      exact hG (good_swap12 (good_swap23 (good_L5 hp h2 h3 h1 s23 e1 e23 e2 (by omega))))
  have U3 : min (vp p (a1 + a2)) (vp p a3) ≤ vp p (a1 + a2 + a3) := by
    rw [← pow_dvd_iff_vp hp s123]
    exact dvd_add ((pow_dvd_iff_vp hp s12 _).mpr (min_le_left _ _))
      ((pow_dvd_iff_vp hp h3 _).mpr (min_le_right _ _))
  have U2 : min (vp p (a1 + a3)) (vp p a2) ≤ vp p (a1 + a2 + a3) := by
    have e : a1 + a2 + a3 = (a1 + a3) + a2 := by ring
    rw [e]
    rw [e] at s123
    rw [← pow_dvd_iff_vp hp s123]
    exact dvd_add ((pow_dvd_iff_vp hp s13 _).mpr (min_le_left _ _))
      ((pow_dvd_iff_vp hp h2 _).mpr (min_le_right _ _))
  have U1 : min (vp p (a2 + a3)) (vp p a1) ≤ vp p (a1 + a2 + a3) := by
    have e : a1 + a2 + a3 = (a2 + a3) + a1 := by ring
    rw [e]
    rw [e] at s123
    rw [← pow_dvd_iff_vp hp s123]
    exact dvd_add ((pow_dvd_iff_vp hp s23 _).mpr (min_le_left _ _))
      ((pow_dvd_iff_vp hp h1 _).mpr (min_le_right _ _))
  exact arith_core _ _ _ _ _ _ _ Z D L63 L62 L61 L53 L52 L51 U3 U2 U1

def NR (a1 a2 a3 : ℤ) : Prop :=
  a1 ≠ 0 ∧ a2 ≠ 0 ∧ a3 ≠ 0 ∧ a1 + a2 ≠ 0 ∧ a1 + a3 ≠ 0 ∧ a2 + a3 ≠ 0 ∧ a1 + a2 + a3 ≠ 0

def Cop (a1 a2 a3 : ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ¬ ((p : ℤ) ∣ a1 ∧ (p : ℤ) ∣ a2 ∧ (p : ℤ) ∣ a3)

theorem ineqs {a1 a2 a3 : ℤ} (hn : NR a1 a2 a3) (hc : Cop a1 a2 a3) (hG : ¬ Good a1 a2 a3) :
    (|a1| * |a2| * |a3|) ^ 42 ≤ (|a1 + a2| * |a1 + a3| * |a2 + a3|) ^ 12 * |a1 + a2 + a3| ^ 37 ∧
    (|a1| * |a2|) ^ 6 * |a3| ^ 42 ≤ |a1 + a3| ^ 7 * |a2 + a3| ^ 7 * |a1 + a2| ^ 49 ∧
    (a1 = 1 → (|a2| * |a3|) ^ 42 ≤ |a2 + a3| ^ 12 * |a1 + a2 + a3| ^ 49 ∧
      |a3| ^ 42 ≤ |a2 + a3| ^ 6 * |a1 + a2| ^ 49) := by
  obtain ⟨h1, h2, h3, s12, s13, s23, s123⟩ := hn
  have per := fun p (hp : p.Prime) => per_prime hp h1 h2 h3 s12 s13 s23 s123 (hc p hp) hG
  refine ⟨?_, ?_, fun ha1 => ⟨?_, ?_⟩⟩
  · have := abs_le_of_vp (N := (a1 * a2 * a3) ^ 42)
      (M := ((a1 + a2) * (a1 + a3) * (a2 + a3)) ^ 12 * (a1 + a2 + a3) ^ 37)
      (by positivity) (by positivity) (fun p hp => by
        rw [vp_pow, vp_mul (mul_ne_zero h1 h2) h3, vp_mul h1 h2,
          vp_mul (pow_ne_zero _ (mul_ne_zero (mul_ne_zero s12 s13) s23)) (pow_ne_zero _ s123),
          vp_pow, vp_pow, vp_mul (mul_ne_zero s12 s13) s23, vp_mul s12 s13]
        have := (per p hp).1
        omega)
    simpa only [abs_mul, abs_pow] using this
  · have := abs_le_of_vp (N := (a1 * a2) ^ 6 * a3 ^ 42)
      (M := (a1 + a3) ^ 7 * (a2 + a3) ^ 7 * (a1 + a2) ^ 49)
      (by positivity) (by positivity) (fun p hp => by
        rw [vp_mul (pow_ne_zero _ (mul_ne_zero h1 h2)) (pow_ne_zero _ h3), vp_pow, vp_pow,
          vp_mul h1 h2,
          vp_mul (mul_ne_zero (pow_ne_zero _ s13) (pow_ne_zero _ s23)) (pow_ne_zero _ s12),
          vp_mul (pow_ne_zero _ s13) (pow_ne_zero _ s23), vp_pow, vp_pow, vp_pow]
        have := (per p hp).2.1
        omega)
    simpa only [abs_mul, abs_pow] using this
  · have := abs_le_of_vp (N := (a2 * a3) ^ 42)
      (M := (a2 + a3) ^ 12 * (a1 + a2 + a3) ^ 49)
      (by positivity) (by positivity) (fun p hp => by
        rw [vp_pow, vp_mul h2 h3, vp_mul (pow_ne_zero _ s23) (pow_ne_zero _ s123), vp_pow, vp_pow]
        have := ((per p hp).2.2 (by rw [ha1]; exact vp_one p)).1
        omega)
    simpa only [abs_mul, abs_pow] using this
  · have := abs_le_of_vp (N := a3 ^ 42)
      (M := (a2 + a3) ^ 6 * (a1 + a2) ^ 49)
      (by positivity) (by positivity) (fun p hp => by
        rw [vp_pow, vp_mul (pow_ne_zero _ s23) (pow_ne_zero _ s12), vp_pow, vp_pow]
        have := ((per p hp).2.2 (by rw [ha1]; exact vp_one p)).2
        omega)
    simpa only [abs_mul, abs_pow] using this

theorem caseM' {T V W A B C D : ℤ} (hT : 0 < T) (hTV : T < V) (hVW : V < W)
    (eA : A = V - T) (eB : B = T + W) (eC : C = W - V) (eD : D = T + W - V)
    (H3 : (T * V * W) ^ 42 ≤ (A * B * C) ^ 12 * D ^ 37)
    (H4 : (T * V) ^ 6 * W ^ 42 ≤ B ^ 7 * C ^ 7 * A ^ 49) : False := by
  subst eA eB eC eD
  exact caseM hT hTV hVW H3 H4

theorem caseS' {T V W A B C D : ℤ} (hT : 0 < T) (hTV : T < V) (hVW : V ≤ W)
    (h : 3 ≤ T ∨ (T ≤ 2 ∧ V ^ 23 < (V + W) * T ^ 22))
    (eA : A = V - T) (eB : B = W - T) (eC : C = V + W) (eD : D = V + W - T)
    (H3 : (T * V * W) ^ 42 ≤ (A * B * C) ^ 12 * D ^ 37)
    (H4 : (T * V) ^ 6 * W ^ 42 ≤ B ^ 7 * C ^ 7 * A ^ 49) : False := by
  subst eA eB eC eD
  exact caseS hT hTV hVW h H3 H4

theorem caseL' {T V W A B C D : ℤ} (hT : 2 ≤ T) (hTV : T ≤ V) (hVW : V < W)
    (hD0 : 0 ≤ D) (hDW : D < W) (eA : A = T + V) (eB : B = W - T) (eC : C = W - V)
    (H3 : (T * V * W) ^ 42 ≤ (A * B * C) ^ 12 * D ^ 37)
    (H4 : (T * V) ^ 6 * W ^ 42 ≤ B ^ 7 * C ^ 7 * A ^ 49) : False := by
  subst eA eB eC
  exact caseL hT hTV hVW hD0 hDW H3 H4

theorem caseL1' {V W A C D : ℤ} (hV : 1 ≤ V) (hVW : V + 2 ≤ W)
    (eA : A = 1 + V) (eC : C = W - V) (eD : D = W - V - 1)
    (H11 : (V * W) ^ 42 ≤ C ^ 12 * D ^ 49) (H12 : W ^ 42 ≤ C ^ 6 * A ^ 49) : False := by
  subst eA eC eD
  exact caseL1 hV hVW H11 H12

theorem good_pos {a1 a2 a3 : ℤ} (h1 : 0 < a1) (h2 : 0 < a2) (h3 : 0 < a3) : Good a1 a2 a3 := by
  refine good_of_col (α := Fin 1) (by simp) (fun _ => 0) (fun x1 x2 x3 hx1 hx2 hx3 _ _ => ?_)
  have : (0 : ℤ) < a1 * x1 + a2 * x2 + a3 * x3 := by positivity
  exact this.ne'

theorem main_pos {a1 a2 a3 : ℤ} (hn : NR a1 a2 a3) (hc : Cop a1 a2 a3) (ha1 : 0 < a1)
    (o12 : a1 ≤ |a2|) (o23 : |a2| ≤ |a3|) : Good a1 a2 a3 := by
  by_contra hG
  have hn' := hn
  obtain ⟨h1, h2, h3, s12, s13, s23, s123⟩ := hn'
  have eT : |a1| = a1 := abs_of_pos ha1
  rcases lt_or_gt_of_ne h2 with n2 | p2 <;> rcases lt_or_gt_of_ne h3 with n3 | p3
  · -- a2 < 0, a3 < 0
    have eV : |a2| = -a2 := abs_of_neg n2
    have eW : |a3| = -a3 := abs_of_neg n3
    have hTV : |a1| < |a2| := by
      rw [eT, eV]; rw [eV] at o12; exact lt_of_le_of_ne o12 (fun h => s12 (by omega))
    have hVW : |a2| ≤ |a3| := o23
    have eA : |a1 + a2| = |a2| - |a1| := by
      rw [eT, eV, abs_of_neg (by rw [eT, eV] at hTV; omega)]; ring
    have eB : |a1 + a3| = |a3| - |a1| := by
      rw [eT, eW, abs_of_neg (by rw [eT, eV] at hTV; rw [eV, eW] at hVW; omega)]; ring
    have eC : |a2 + a3| = |a2| + |a3| := by
      rw [eV, eW, abs_of_neg (by omega)]; ring
    have eD : |a1 + a2 + a3| = |a2| + |a3| - |a1| := by
      rw [eT, eV, eW, abs_of_neg (by rw [eT, eV] at hTV; omega)]; ring
    have hT0 : 0 < |a1| := by rw [eT]; exact ha1
    by_cases hT3 : 3 ≤ |a1|
    · exact caseS' hT0 hTV hVW (Or.inl hT3) eA eB eC eD (ineqs hn hc hG).1 (ineqs hn hc hG).2.1
    · by_cases harch : (|a2| + |a3|) * |a1| ^ 22 ≤ |a2| ^ 23
      · have key := good_arch hT0 hTV hVW harch
        rw [eT, eV, eW, neg_neg, neg_neg] at key
        exact hG key
      · exact caseS' hT0 hTV hVW (Or.inr ⟨by omega, lt_of_not_ge harch⟩) eA eB eC eD
          (ineqs hn hc hG).1 (ineqs hn hc hG).2.1
  · -- a2 < 0 < a3
    have eV : |a2| = -a2 := abs_of_neg n2
    have eW : |a3| = a3 := abs_of_pos p3
    have hTV : |a1| < |a2| := by
      rw [eT, eV]; rw [eV] at o12; exact lt_of_le_of_ne o12 (fun h => s12 (by omega))
    have hVW : |a2| < |a3| := by
      rw [eV, eW]; rw [eV, eW] at o23; exact lt_of_le_of_ne o23 (fun h => s23 (by omega))
    have eA : |a1 + a2| = |a2| - |a1| := by
      rw [eT, eV, abs_of_neg (by rw [eT, eV] at hTV; omega)]; ring
    have eB : |a1 + a3| = |a1| + |a3| := by
      rw [eT, eW, abs_of_pos (by omega)]
    have eC : |a2 + a3| = |a3| - |a2| := by
      rw [eV, eW, abs_of_pos (by rw [eV, eW] at hVW; omega)]; ring
    have eD : |a1 + a2 + a3| = |a1| + |a3| - |a2| := by
      rw [eT, eV, eW, abs_of_pos (by rw [eV, eW] at hVW; omega)]; ring
    have hT0 : 0 < |a1| := by rw [eT]; exact ha1
    exact caseM' hT0 hTV hVW eA eB eC eD (ineqs hn hc hG).1 (ineqs hn hc hG).2.1
  · -- a3 < 0 < a2
    have eV : |a2| = a2 := abs_of_pos p2
    have eW : |a3| = -a3 := abs_of_neg n3
    have hTV : |a1| ≤ |a2| := by rw [eT]; exact o12
    have hVW : |a2| < |a3| := by
      rw [eV, eW]; rw [eV, eW] at o23; exact lt_of_le_of_ne o23 (fun h => s23 (by omega))
    have eA : |a1 + a2| = |a1| + |a2| := by
      rw [eT, eV, abs_of_pos (by omega)]
    have o12' : a1 ≤ a2 := by rw [← eV]; exact o12
    have hVW' : a2 < -a3 := by rw [← eV, ← eW]; exact hVW
    have eB : |a1 + a3| = |a3| - |a1| := by
      rw [eT, eW, abs_of_neg (by omega)]
      ring
    have eC : |a2 + a3| = |a3| - |a2| := by
      rw [eV, eW, abs_of_neg (by rw [eV, eW] at hVW; omega)]; ring
    have hD0 : 0 ≤ |a1 + a2 + a3| := abs_nonneg _
    have hDW : |a1 + a2 + a3| < |a3| := by
      rw [eW, abs_lt]
      rw [eT, eV] at hTV
      rw [eV, eW] at hVW
      constructor <;> omega
    by_cases hT2 : 2 ≤ |a1|
    · exact caseL' hT2 hTV hVW hD0 hDW eA eB eC (ineqs hn hc hG).1 (ineqs hn hc hG).2.1
    · have ha11 : a1 = 1 := by rw [eT] at hT2; omega
      have hV1 : 1 ≤ |a2| := by rw [eV]; omega
      have hVW2 : |a2| + 2 ≤ |a3| := by
        rw [eV, eW]; rw [eV, eW] at hVW; subst ha11; omega
      have eA' : |a1 + a2| = 1 + |a2| := by rw [eA, eT, ha11]
      have eD : |a1 + a2 + a3| = |a3| - |a2| - 1 := by
        rw [eV, eW, abs_of_neg (by rw [eV, eW] at hVW2; subst ha11; omega)]; subst ha11; ring
      exact caseL1' hV1 hVW2 eA' eC eD ((ineqs hn hc hG).2.2 ha11).1 ((ineqs hn hc hG).2.2 ha11).2
  · exact hG (good_pos ha1 p2 p3)

theorem NR_neg {a1 a2 a3 : ℤ} (h : NR a1 a2 a3) : NR (-a1) (-a2) (-a3) := by
  obtain ⟨h1, h2, h3, s12, s13, s23, s123⟩ := h
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem NR_swap12 {a1 a2 a3 : ℤ} (h : NR a1 a2 a3) : NR a2 a1 a3 := by
  obtain ⟨h1, h2, h3, s12, s13, s23, s123⟩ := h
  exact ⟨h2, h1, h3, by omega, s23, s13, by omega⟩

theorem NR_swap23 {a1 a2 a3 : ℤ} (h : NR a1 a2 a3) : NR a1 a3 a2 := by
  obtain ⟨h1, h2, h3, s12, s13, s23, s123⟩ := h
  exact ⟨h1, h3, h2, s13, s12, by omega, by omega⟩

theorem Cop_neg {a1 a2 a3 : ℤ} (h : Cop a1 a2 a3) : Cop (-a1) (-a2) (-a3) :=
  fun p hp h' => h p hp ⟨dvd_neg.mp h'.1, dvd_neg.mp h'.2.1, dvd_neg.mp h'.2.2⟩

theorem Cop_swap12 {a1 a2 a3 : ℤ} (h : Cop a1 a2 a3) : Cop a2 a1 a3 :=
  fun p hp h' => h p hp ⟨h'.2.1, h'.1, h'.2.2⟩

theorem Cop_swap23 {a1 a2 a3 : ℤ} (h : Cop a1 a2 a3) : Cop a1 a3 a2 :=
  fun p hp h' => h p hp ⟨h'.1, h'.2.2, h'.2.1⟩

theorem main_sorted {a1 a2 a3 : ℤ} (hn : NR a1 a2 a3) (hc : Cop a1 a2 a3)
    (o12 : |a1| ≤ |a2|) (o23 : |a2| ≤ |a3|) : Good a1 a2 a3 := by
  rcases lt_or_gt_of_ne hn.1 with n1 | p1
  · have key := main_pos (NR_neg hn) (Cop_neg hc) (by omega)
      (by rw [abs_neg, ← abs_of_neg n1]; exact o12) (by rw [abs_neg, abs_neg]; exact o23)
    have := good_neg key
    simpa only [neg_neg] using this
  · exact main_pos hn hc p1 (by rw [← abs_of_pos p1]; exact o12) o23

theorem main_cop {a1 a2 a3 : ℤ} (hn : NR a1 a2 a3) (hc : Cop a1 a2 a3) : Good a1 a2 a3 := by
  rcases le_total |a1| |a2| with h12 | h12 <;> rcases le_total |a2| |a3| with h23 | h23 <;>
    rcases le_total |a1| |a3| with h13 | h13
  · exact main_sorted hn hc h12 h23
  · exact main_sorted hn hc h12 h23
  · exact good_swap23 (main_sorted (NR_swap23 hn) (Cop_swap23 hc) h13 h23)
  · exact good_swap23 (good_swap12
      (main_sorted (NR_swap12 (NR_swap23 hn)) (Cop_swap12 (Cop_swap23 hc)) h13 h12))
  · exact good_swap12 (main_sorted (NR_swap12 hn) (Cop_swap12 hc) h12 h13)
  · exact good_swap12 (good_swap23
      (main_sorted (NR_swap23 (NR_swap12 hn)) (Cop_swap23 (Cop_swap12 hc)) h23 h13))
  · exact main_sorted hn hc (h13.trans h23) (h12.trans h13)
  · exact good_swap12 (good_swap23 (good_swap12 (main_sorted
      (NR_swap12 (NR_swap23 (NR_swap12 hn))) (Cop_swap12 (Cop_swap23 (Cop_swap12 hc))) h23 h12)))

theorem main_nr {a1 a2 a3 : ℤ} (hn : NR a1 a2 a3) : Good a1 a2 a3 := by
  set g := Int.gcd a1 (Int.gcd a2 a3) with hg_def
  have hg0 : g ≠ 0 := fun h => hn.1 (Int.gcd_eq_zero_iff.mp h).1
  have d1 : (g : ℤ) ∣ a1 := Int.gcd_dvd_left _ _
  have d23 : (g : ℤ) ∣ (Int.gcd a2 a3 : ℤ) := Int.gcd_dvd_right _ _
  have d2 : (g : ℤ) ∣ a2 := d23.trans (Int.gcd_dvd_left _ _)
  have d3 : (g : ℤ) ∣ a3 := d23.trans (Int.gcd_dvd_right _ _)
  obtain ⟨b1, hb1⟩ := d1
  obtain ⟨b2, hb2⟩ := d2
  obtain ⟨b3, hb3⟩ := d3
  obtain ⟨h1, h2, h3, s12, s13, s23, s123⟩ := hn
  have hnb : NR b1 b2 b3 := by
    refine ⟨fun h => h1 (by rw [hb1, h, mul_zero]), fun h => h2 (by rw [hb2, h, mul_zero]),
      fun h => h3 (by rw [hb3, h, mul_zero]), fun h => s12 (by rw [hb1, hb2, ← mul_add, h, mul_zero]),
      fun h => s13 (by rw [hb1, hb3, ← mul_add, h, mul_zero]),
      fun h => s23 (by rw [hb2, hb3, ← mul_add, h, mul_zero]),
      fun h => s123 (by rw [hb1, hb2, hb3, ← mul_add, ← mul_add, h, mul_zero])⟩
  have hcb : Cop b1 b2 b3 := by
    intro p hp ⟨q1, q2, q3⟩
    have e1 : ((g * p : ℕ) : ℤ) ∣ a1 := by rw [hb1]; push_cast; exact mul_dvd_mul_left _ q1
    have e2 : ((g * p : ℕ) : ℤ) ∣ a2 := by rw [hb2]; push_cast; exact mul_dvd_mul_left _ q2
    have e3 : ((g * p : ℕ) : ℤ) ∣ a3 := by rw [hb3]; push_cast; exact mul_dvd_mul_left _ q3
    have e23 : g * p ∣ Int.gcd a2 a3 := Int.dvd_gcd e2 e3
    have e123 : g * p ∣ g := Int.dvd_gcd e1 (by exact_mod_cast e23)
    have : p ∣ 1 := Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero hg0) (by rw [mul_one]; exact e123)
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  have key := good_scale (g : ℤ) (by exact_mod_cast hg0) (main_cop hnb hcb)
  rw [← hb1, ← hb2, ← hb3] at key
  exact key

end FK

theorem OMA.solution : type_of% @Green21.green_21.variants.fox_kleitman := by
  intro a ha
  have hI := (Green21.not_radoCondition_iff a).mp ha
  have hne : ∀ I : Finset (Fin 3), I.Nonempty → ∑ i ∈ I, a i ≠ 0 := fun I hI0 hs =>
    hI0.ne_empty (hI I hs)
  have hn : FK.NR (a 0) (a 1) (a 2) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using hne {0} (by simp)
    · simpa using hne {1} (by simp)
    · simpa using hne {2} (by simp)
    · simpa [Finset.sum_pair] using hne {0, 1} (by simp)
    · simpa [Finset.sum_pair] using hne {0, 2} (by simp)
    · simpa [Finset.sum_pair] using hne {1, 2} (by simp)
    · simpa [Fin.sum_univ_three] using hne Finset.univ (by simp)
  obtain ⟨col, hcol⟩ := FK.main_nr hn
  apply Nat.sInf_le
  refine ⟨col, fun x hx hmono => ?_⟩
  rw [Fin.sum_univ_three]
  exact hcol (x 0) (x 1) (x 2) (hx 0) (hx 1) (hx 2) (hmono 0 1) (hmono 0 2)
