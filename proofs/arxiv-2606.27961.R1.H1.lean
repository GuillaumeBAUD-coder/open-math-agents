import OMAReductions.R_arxiv_2606_27961_R1

-- Step arxiv-2606.27961.R1.H1: hypothesis H1 of reduction arxiv-2606.27961.R1
-- Credit: @ptc-prover-bot

/-! Lemma 6.4 of Barcau–Paşol–Ţurcaş (arXiv:2606.27961), proved directly for a section `s`.
Write `D_u(x) = s(x+u) - s(x)`, so `reduce (D_u x) = u` and `c(u) = #range D_u`.
* Cycle: `∑_{i<p} D_u(x + i u) = 0`; hence `c(u) ≥ 2` for `u ≠ 0`, and if `range D_u = {a, b}`
  then `a - b ∈ K_u := { p•y : reduce y ∈ ⟨u⟩ }` (count the `a`'s: `n (a-b) + p b = 0`).
* Curl: `D_u(x+v) - D_u(x) = D_v(x+u) - D_v(x)`; for independent `u, v` with `c(u) = c(v) = 2`
  both sides lie in `K_u ∩ K_v = 0`, so `D_u` is `v`-invariant and `D_v` is `u`-invariant.
* For `w = λu + μv` (`λ, μ ≠ 0`): `D_w(x) = D_{λu}(x) + D_{μv}(x)`, the two summands vary
  independently and their differences lie in `K_u`, `K_v`, so `c(w) ≥ 2·2`.
* Writing `w = αu + βv`: `c(w) ≥ g(α) g(β)` with `g(0) = 1`, `g(≠0) = 2`, and
  `∑_w c(w) ≥ (∑_α g α)^2 = (2p-1)^2`. -/

open OMA.S_arxiv_2606_27961 Finset

namespace OMA.ArxivH1

variable {p : ℕ} [hp : Fact p.Prime]

instance neZeroSq : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.out.ne_zero⟩

/-- Reduction modulo `p` on `ZMod (p^2)`. -/
noncomputable def φ : ZMod (p ^ 2) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p)

lemma val_cast (z : ZMod (p ^ 2)) : ((z.val : ℕ) : ZMod p) = φ z := by
  rw [φ, ZMod.castHom_apply, ZMod.cast_eq_val]

lemma red_eq (x : Plane (p ^ 2)) : reduce p x = (φ x.1, φ x.2) := by
  simp only [reduce, val_cast]

lemma red_add (x y : Plane (p ^ 2)) : reduce p (x + y) = reduce p x + reduce p y := by
  simp only [red_eq, Prod.fst_add, Prod.snd_add, map_add, Prod.mk_add_mk]

lemma red_sub (x y : Plane (p ^ 2)) : reduce p (x - y) = reduce p x - reduce p y := by
  simp only [red_eq, Prod.fst_sub, Prod.snd_sub, map_sub, Prod.mk_sub_mk]

lemma red_nsmul (n : ℕ) (x : Plane (p ^ 2)) : reduce p (n • x) = n • reduce p x := by
  simp only [red_eq, Prod.smul_fst, Prod.smul_snd, map_nsmul, Prod.smul_mk]

lemma red_zero : reduce p (0 : Plane (p ^ 2)) = 0 := by
  simp only [red_eq, Prod.fst_zero, Prod.snd_zero, map_zero, Prod.mk_zero_zero]

lemma φ_eq_zero_iff (z : ZMod (p ^ 2)) : φ z = 0 ↔ ∃ y, z = (p : ZMod (p ^ 2)) * y := by
  constructor
  · intro h
    rw [← val_cast, ZMod.natCast_eq_zero_iff] at h
    obtain ⟨m, hm⟩ := h
    exact ⟨m, by rw [← ZMod.natCast_zmod_val z, hm]; push_cast; ring⟩
  · rintro ⟨y, rfl⟩
    rw [map_mul, map_natCast, ZMod.natCast_self, zero_mul]

lemma mul_eq_zero_iff (z : ZMod (p ^ 2)) : (p : ZMod (p ^ 2)) * z = 0 ↔ φ z = 0 := by
  constructor
  · intro h
    have h' : ((p * z.val : ℕ) : ZMod (p ^ 2)) = 0 := by
      push_cast; rw [ZMod.natCast_zmod_val]; exact h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have h3 : p * p ∣ p * z.val := Nat.dvd_trans ⟨1, by ring⟩ h'
    have := Nat.dvd_of_mul_dvd_mul_left hp.out.pos h3
    rw [← val_cast, ZMod.natCast_eq_zero_iff]; exact this
  · intro h
    obtain ⟨y, rfl⟩ := (φ_eq_zero_iff z).mp h
    rw [← mul_assoc, show ((p : ZMod (p ^ 2)) * p) = ((p ^ 2 : ℕ) : ZMod (p ^ 2)) by push_cast; ring,
      ZMod.natCast_self, zero_mul]

lemma nsmul_pair (n : ℕ) (x : Plane (p ^ 2)) : n • x = ((n : ZMod (p ^ 2)) * x.1, (n : ZMod (p ^ 2)) * x.2) := by
  ext <;> simp [nsmul_eq_mul]

lemma kerP (z : Plane (p ^ 2)) : reduce p z = 0 ↔ ∃ y : Plane (p ^ 2), z = p • y := by
  rw [red_eq, Prod.mk_eq_zero, φ_eq_zero_iff, φ_eq_zero_iff]
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨(a, b), by rw [nsmul_pair]; ext <;> simp [ha, hb]⟩
  · rintro ⟨y, rfl⟩
    rw [nsmul_pair]; exact ⟨⟨y.1, rfl⟩, ⟨y.2, rfl⟩⟩

lemma mulP (z : Plane (p ^ 2)) : p • z = 0 ↔ reduce p z = 0 := by
  rw [nsmul_pair, Prod.mk_eq_zero, mul_eq_zero_iff, mul_eq_zero_iff, red_eq, Prod.mk_eq_zero]

lemma p_smul_plane (x : Plane p) : p • x = 0 := by
  ext <;> simp [nsmul_eq_mul]

lemma pp_zero (y : Plane (p ^ 2)) : p • (p • y) = 0 := by
  rw [mulP, red_nsmul, p_smul_plane]

/-- `K u = { p • y : reduce y ∈ ⟨u⟩ }`. -/
def K (u : Plane p) : Set (Plane (p ^ 2)) :=
  {z | ∃ y : Plane (p ^ 2), z = p • y ∧ ∃ t : ZMod p, reduce p y = t • u}

lemma K_zero (u : Plane p) : (0 : Plane (p ^ 2)) ∈ K u :=
  ⟨0, by simp, 0, by simp [red_zero]⟩

lemma K_add {u : Plane p} {a b : Plane (p ^ 2)} (ha : a ∈ K u) (hb : b ∈ K u) : a + b ∈ K u := by
  obtain ⟨y, rfl, t, ht⟩ := ha
  obtain ⟨y', rfl, t', ht'⟩ := hb
  exact ⟨y + y', by rw [nsmul_add], t + t', by rw [red_add, ht, ht', add_smul]⟩

lemma K_neg {u : Plane p} {a : Plane (p ^ 2)} (ha : a ∈ K u) : -a ∈ K u := by
  obtain ⟨y, rfl, t, ht⟩ := ha
  refine ⟨-y, by rw [smul_neg], -t, ?_⟩
  have : reduce p (-y) = -reduce p y := by
    have h := red_add y (-y); rw [add_neg_cancel, red_zero] at h
    exact (neg_eq_of_add_eq_zero_right h.symm).symm
  rw [this, ht, neg_smul]

lemma K_sub {u : Plane p} {a b : Plane (p ^ 2)} (ha : a ∈ K u) (hb : b ∈ K u) : a - b ∈ K u := by
  rw [sub_eq_add_neg]; exact K_add ha (K_neg hb)

lemma K_sum {u : Plane p} (S : Finset ℕ) (f : ℕ → Plane (p ^ 2)) (hf : ∀ i ∈ S, f i ∈ K u) :
    ∑ i ∈ S, f i ∈ K u := by
  induction S using Finset.induction_on with
  | empty => simpa using K_zero u
  | insert a S ha ih =>
    rw [sum_insert ha]
    exact K_add (hf a (mem_insert_self a S)) (ih fun i hi => hf i (mem_insert_of_mem hi))

lemma K_inter {u v : Plane p} (hind : u.1 * v.2 ≠ u.2 * v.1) {z : Plane (p ^ 2)}
    (hu : z ∈ K u) (hv : z ∈ K v) : z = 0 := by
  obtain ⟨y, rfl, t, ht⟩ := hu
  obtain ⟨y', hy', t', ht'⟩ := hv
  have h1 : p • (y - y') = 0 := by rw [nsmul_sub, hy', sub_self]
  rw [mulP, red_sub, ht, ht', sub_eq_zero] at h1
  have e1 := congrArg Prod.fst h1
  have e2 := congrArg Prod.snd h1
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at e1 e2
  have hdet : t * (u.1 * v.2 - u.2 * v.1) = 0 := by
    have : t * (u.1 * v.2 - u.2 * v.1) = (t * u.1) * v.2 - (t * u.2) * v.1 := by ring
    rw [this, e1, e2]; ring
  have ht0 : t = 0 := by
    rcases mul_eq_zero.mp hdet with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) hind
  rw [ht0, zero_smul, kerP] at ht
  obtain ⟨w, rfl⟩ := ht
  exact pp_zero w

variable (s : Plane p → Plane (p ^ 2))

/-- The difference function `D_u(x) = s(x+u) - s(x)`. -/
def D (u x : Plane p) : Plane (p ^ 2) := s (x + u) - s x

variable {s}

lemma red_D (hs : Function.RightInverse s (reduce p)) (u x : Plane p) : reduce p (D s u x) = u := by
  rw [D, red_sub, hs (x + u), hs x]; abel

lemma tele (u x : Plane p) (n : ℕ) : ∑ i ∈ range n, D s u (x + i • u) = s (x + n • u) - s x := by
  have := Finset.sum_range_sub (fun i => s (x + i • u)) n
  simp only [zero_smul, add_zero] at this
  rw [← this]
  apply sum_congr rfl
  intro i _
  rw [D, succ_nsmul, add_assoc]

lemma cycle (u x : Plane p) : ∑ i ∈ range p, D s u (x + i • u) = 0 := by
  rw [tele, p_smul_plane, add_zero, sub_self]

lemma two_values (hs : Function.RightInverse s (reduce p)) {u : Plane p} (hu : u ≠ 0) :
    ∃ x y, D s u x ≠ D s u y := by
  by_contra h
  push Not at h
  have hc := cycle (s := s) u 0
  rw [sum_congr rfl (fun i _ => h (0 + i • u) 0), sum_const, card_range, mulP, red_D hs] at hc
  exact hu hc

lemma ncard_two_le {f : Plane p → Plane (p ^ 2)} {x y : Plane p} (h : f x ≠ f y) :
    2 ≤ (Set.range f).ncard := by
  have hsub : ({f x, f y} : Set (Plane (p ^ 2))) ⊆ Set.range f := by
    rintro _ (rfl | rfl) <;> exact ⟨_, rfl⟩
  calc 2 = ({f x, f y} : Set (Plane (p ^ 2))).ncard := (Set.ncard_pair h).symm
    _ ≤ _ := Set.ncard_le_ncard hsub (Set.finite_range f)

/-- If `D_u` takes exactly two values, all its differences lie in `K u`. -/
lemma diff_mem_K (hs : Function.RightInverse s (reduce p)) {u : Plane p} (hu : u ≠ 0)
    (hc : (Set.range (D s u)).ncard = 2) (x y : Plane p) : D s u x - D s u y ∈ K u := by
  classical
  obtain ⟨a, b, hab, hrange⟩ := Set.ncard_eq_two.mp hc
  have hmem : ∀ z, D s u z = a ∨ D s u z = b := by
    intro z
    have : D s u z ∈ Set.range (D s u) := ⟨z, rfl⟩
    rw [hrange] at this
    simpa using this
  have ha : reduce p a = u := by
    obtain ⟨z, hz⟩ : a ∈ Set.range (D s u) := by rw [hrange]; simp
    rw [← hz, red_D hs]
  have hb : reduce p b = u := by
    obtain ⟨z, hz⟩ : b ∈ Set.range (D s u) := by rw [hrange]; simp
    rw [← hz, red_D hs]
  -- count the `a`'s along the cycle through `0`
  set S := (range p).filter (fun i => D s u (0 + i • u) = a) with hS
  set n := S.card with hn
  have hnp : n ≤ p := by
    have := card_filter_le (range p) (fun i => D s u (0 + i • u) = a)
    rwa [card_range] at this
  have hsum : n • a + (p - n) • b = 0 := by
    have hc0 := cycle (s := s) u 0
    rw [sum_congr rfl (fun i _ => show D s u (0 + i • u) =
      if D s u (0 + i • u) = a then a else b by
        rcases hmem (0 + i • u) with h | h
        · rw [if_pos h, h]
        · rw [if_neg (by rw [h]; exact Ne.symm hab), h]),
      sum_ite, sum_const, sum_const] at hc0
    have hcomp : ((range p).filter (fun i => ¬ D s u (0 + i • u) = a)).card = p - n := by
      have := card_filter_add_card_filter_not (s := range p)
        (fun i => D s u (0 + i • u) = a)
      rw [card_range] at this; rw [hn, hS]; omega
    rw [hcomp] at hc0; exact hc0
  have hkey : n • (a - b) + p • b = 0 := by
    rw [nsmul_sub, sub_nsmul b hnp] at *
    rw [← hsum]; abel
  have hab0 : reduce p (a - b) = 0 := by rw [red_sub, ha, hb, sub_self]
  obtain ⟨e, he⟩ := (kerP _).mp hab0
  have hn0 : 0 < n := by
    by_contra h0
    have : n = 0 := by omega
    rw [this, zero_smul, zero_add, mulP, hb] at hkey
    exact hu hkey
  have hnlt : n < p := by
    by_contra h1
    have : n = p := by omega
    rw [this] at hsum
    rw [Nat.sub_self, zero_smul, add_zero, mulP, ha] at hsum
    exact hu hsum
  have h2 : p • (n • e + b) = 0 := by
    rw [nsmul_add, smul_comm p n e, ← he]; exact hkey
  rw [mulP, red_add, red_nsmul] at h2
  rw [hb] at h2
  have hnz : (n : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd; exact absurd (Nat.le_of_dvd hn0 hdvd) (by omega)
  have hred : reduce p e = (-(n : ZMod p)⁻¹) • u := by
    have h3 : (n : ZMod p) • reduce p e = -u := by
      rw [Nat.cast_smul_eq_nsmul]; exact eq_neg_of_add_eq_zero_left h2
    rw [neg_smul, ← smul_neg, ← h3, smul_smul, inv_mul_cancel₀ hnz, one_smul]
  have habK : a - b ∈ K u := ⟨e, he, _, hred⟩
  rcases hmem x with hx | hx <;> rcases hmem y with hy | hy <;> rw [hx, hy]
  · rw [sub_self]; exact K_zero u
  · exact habK
  · rw [← neg_sub]; exact K_neg habK
  · rw [sub_self]; exact K_zero u

lemma curl (u v x : Plane p) : D s u (x + v) - D s u x = D s v (x + u) - D s v x := by
  simp only [D]; rw [show x + v + u = x + u + v by abel]; abel

lemma sm_val (α : ZMod p) (u : Plane p) : α • u = α.val • u := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]

section Mixed

variable (hs : Function.RightInverse s (reduce p)) {u v : Plane p} (hu : u ≠ 0) (hv : v ≠ 0)
  (hind : u.1 * v.2 ≠ u.2 * v.1)
  (hcu : (Set.range (D s u)).ncard = 2) (hcv : (Set.range (D s v)).ncard = 2)
include hs hu hv hind hcu hcv

lemma inv_u (x : Plane p) : D s u (x + v) = D s u x := by
  have h1 := diff_mem_K hs hu hcu (x + v) x
  have h2 := diff_mem_K hs hv hcv (x + u) x
  rw [← curl] at h2
  exact sub_eq_zero.mp (K_inter hind h1 h2)

lemma inv_v (x : Plane p) : D s v (x + u) = D s v x := by
  have h1 := diff_mem_K hs hu hcu (x + v) x
  have h2 := diff_mem_K hs hv hcv (x + u) x
  rw [curl] at h1
  exact sub_eq_zero.mp (K_inter hind h1 h2)

omit hs hu hv hind hcu hcv in
lemma D_nsmul (w x : Plane p) (n : ℕ) : D s (n • w) x = ∑ i ∈ range n, D s w (x + i • w) := by
  rw [tele]; rfl

lemma iter_u (n j : ℕ) (x : Plane p) : D s (n • u) (x + j • v) = D s (n • u) x := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [D_nsmul] at ih ⊢
    rw [← ih]
    apply sum_congr rfl
    intro i _
    rw [show x + (j + 1) • v + i • u = (x + j • v + i • u) + v by rw [succ_nsmul]; abel,
      inv_u hs hu hv hind hcu hcv]

lemma iter_v (n j : ℕ) (x : Plane p) : D s (n • v) (x + j • u) = D s (n • v) x := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [D_nsmul] at ih ⊢
    rw [← ih]
    apply sum_congr rfl
    intro i _
    rw [show x + (j + 1) • u + i • v = (x + j • u + i • v) + u by rw [succ_nsmul]; abel,
      inv_v hs hu hv hind hcu hcv]

lemma iterK_u (n : ℕ) (x y : Plane p) : D s (n • u) x - D s (n • u) y ∈ K u := by
  rw [D_nsmul, D_nsmul, ← sum_sub_distrib]
  exact K_sum _ _ fun i _ => diff_mem_K hs hu hcu _ _

lemma iterK_v (n : ℕ) (x y : Plane p) : D s (n • v) x - D s (n • v) y ∈ K v := by
  rw [D_nsmul, D_nsmul, ← sum_sub_distrib]
  exact K_sum _ _ fun i _ => diff_mem_K hs hv hcv _ _

lemma mixed (n m : ℕ) (x : Plane p) : D s (n • u + m • v) x = D s (n • u) x + D s (m • v) x := by
  have h := iter_v hs hu hv hind hcu hcv m n x
  rw [← h]; simp only [D]; rw [show x + (n • u + m • v) = x + n • u + m • v by abel]; abel

lemma mixed_four (n m : ℕ) (hnu : n • u ≠ 0) (hmv : m • v ≠ 0)
    (hsurj : ∀ y : Plane p, ∃ α β : ZMod p, y = α • u + β • v) :
    4 ≤ (Set.range (D s (n • u + m • v))).ncard := by
  obtain ⟨x1, x1', h1⟩ := two_values hs hnu
  obtain ⟨y1, y1', h2⟩ := two_values hs hmv
  have comb : ∀ x y : Plane p, ∃ z, D s (n • u) z = D s (n • u) x ∧
      D s (m • v) z = D s (m • v) y := by
    intro x y
    obtain ⟨α, β, hab⟩ := hsurj (y - x)
    refine ⟨x + β.val • v, iter_u hs hu hv hind hcu hcv n β.val x, ?_⟩
    have hz : x + β.val • v = y + (-α).val • u := by
      rw [← sm_val, ← sm_val, neg_smul]
      have : y = x + (α • u + β • v) := by rw [← hab]; abel
      rw [this]; abel
    rw [hz, iter_v hs hu hv hind hcu hcv m (-α).val y]
  choose Z hZ1 hZ2 using comb
  let X : Bool → Plane p := fun t => if t then x1 else x1'
  let Y : Bool → Plane p := fun t => if t then y1 else y1'
  have hX : ∀ t t', D s (n • u) (X t) = D s (n • u) (X t') → t = t' := by
    intro t t' h; cases t <;> cases t' <;> simp_all [X]
  have hY : ∀ t t', D s (m • v) (Y t) = D s (m • v) (Y t') → t = t' := by
    intro t t' h; cases t <;> cases t' <;> simp_all [Y]
  let F : Bool × Bool → Plane (p ^ 2) := fun tt => D s (n • u + m • v) (Z (X tt.1) (Y tt.2))
  have hFv : ∀ tt : Bool × Bool, F tt = D s (n • u) (X tt.1) + D s (m • v) (Y tt.2) := by
    intro tt
    show D s (n • u + m • v) (Z (X tt.1) (Y tt.2)) = _
    rw [mixed hs hu hv hind hcu hcv, hZ1, hZ2]
  have hF : Function.Injective F := by
    rintro ⟨t1, t2⟩ ⟨t1', t2'⟩ h
    rw [hFv, hFv] at h
    have hd : D s (n • u) (X t1) - D s (n • u) (X t1') =
        D s (m • v) (Y t2') - D s (m • v) (Y t2) := by
      rw [sub_eq_sub_iff_add_eq_add, h, add_comm]
    have k1 := iterK_u hs hu hv hind hcu hcv n (X t1) (X t1')
    have k2 := iterK_v hs hu hv hind hcu hcv m (Y t2') (Y t2)
    rw [hd] at k1
    have z := K_inter hind k1 k2
    rw [z] at hd
    have e1 := hX _ _ (sub_eq_zero.mp hd)
    have e2 := hY _ _ (sub_eq_zero.mp z).symm
    rw [e1, e2]
  have hsub : ((univ.image F : Finset (Plane (p ^ 2))) : Set (Plane (p ^ 2))) ⊆
      Set.range (D s (n • u + m • v)) := by
    intro w hw
    rw [coe_image, coe_univ, Set.image_univ] at hw
    obtain ⟨tt, rfl⟩ := hw
    exact ⟨_, rfl⟩
  have := Set.ncard_le_ncard hsub (Set.finite_range _)
  rw [Set.ncard_coe_finset, card_image_of_injective _ hF] at this
  simpa using this

end Mixed

lemma basis_inj {u v : Plane p} (hind : u.1 * v.2 ≠ u.2 * v.1) :
    Function.Injective (fun ab : ZMod p × ZMod p => ab.1 • u + ab.2 • v) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only at h
  have e1 := congrArg Prod.fst h
  have e2 := congrArg Prod.snd h
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at e1 e2
  have hdet : u.1 * v.2 - u.2 * v.1 ≠ 0 := sub_ne_zero.mpr hind
  have ha : (a - c) * (u.1 * v.2 - u.2 * v.1) = 0 := by linear_combination v.2 * e1 - v.1 * e2
  have hb : (b - d) * (u.1 * v.2 - u.2 * v.1) = 0 := by linear_combination u.1 * e2 - u.2 * e1
  have hac := sub_eq_zero.mp ((mul_eq_zero.mp ha).resolve_right hdet)
  have hbd := sub_eq_zero.mp ((mul_eq_zero.mp hb).resolve_right hdet)
  rw [hac, hbd]

theorem H1_proof : OMA.R_arxiv_2606_27961_R1.H1 := by
  intro p _ hpr _ s hs c hex
  haveI : Fact p.Prime := ⟨hpr⟩
  obtain ⟨u, v, hind, hcu, hcv⟩ := hex
  change (Set.range (D s u)).ncard = 2 at hcu
  change (Set.range (D s v)).ncard = 2 at hcv
  have hu : u ≠ 0 := by rintro rfl; exact hind (by simp)
  have hv : v ≠ 0 := by rintro rfl; exact hind (by simp)
  set e : ZMod p × ZMod p → Plane p := fun ab => ab.1 • u + ab.2 • v with he_def
  have he : Function.Bijective e := (basis_inj hind).bijective_of_finite
  let g : ZMod p → ℕ := fun a => if a = 0 then 1 else 2
  have hc : ∀ w, c w = (Set.range (D s w)).ncard := fun w => rfl
  have he0 : ∀ a b : ZMod p, e (a, b) = 0 → a = 0 ∧ b = 0 := by
    intro a b h0
    have := he.1 (h0.trans (show (0 : Plane p) = e (0, 0) by simp [he_def]))
    exact Prod.mk.inj this
  have hsurj : ∀ y : Plane p, ∃ α β : ZMod p, y = α • u + β • v := by
    intro y
    obtain ⟨⟨α, β⟩, hab⟩ := he.2 y
    exact ⟨α, β, hab.symm⟩
  have hpt : ∀ ab : ZMod p × ZMod p, g ab.1 * g ab.2 ≤ c (e ab) := by
    rintro ⟨a, b⟩
    rw [hc]
    show (if a = 0 then 1 else 2) * (if b = 0 then 1 else 2) ≤ _
    by_cases ha : a = 0 <;> by_cases hb : b = 0
    · rw [if_pos ha, if_pos hb]
      exact (Set.ncard_pos (Set.finite_range _)).mpr (Set.range_nonempty _)
    · rw [if_pos ha, if_neg hb, one_mul]
      obtain ⟨x, y, hxy⟩ := two_values hs (fun h0 => hb (he0 a b h0).2)
      exact ncard_two_le hxy
    · rw [if_neg ha, if_pos hb, mul_one]
      obtain ⟨x, y, hxy⟩ := two_values hs (fun h0 => ha (he0 a b h0).1)
      exact ncard_two_le hxy
    · rw [if_neg ha, if_neg hb]
      have hew : e (a, b) = a.val • u + b.val • v := by
        show a • u + b • v = _
        rw [sm_val a u, sm_val b v]
      rw [hew]
      have hnu : a.val • u ≠ 0 := by rw [← sm_val]; exact smul_ne_zero ha hu
      have hmv : b.val • v ≠ 0 := by rw [← sm_val]; exact smul_ne_zero hb hv
      exact mixed_four hs hu hv hind hcu hcv a.val b.val hnu hmv hsurj
  have hsum : ∑ ab : ZMod p × ZMod p, c (e ab) = ∑ w, c w :=
    Fintype.sum_bijective e he _ _ (fun _ => rfl)
  have hg : ∑ a : ZMod p, g a = 2 * p - 1 := by
    have hcard := card_filter_add_card_filter_not (s := (univ : Finset (ZMod p))) (fun a => a = 0)
    rw [filter_eq' univ (0 : ZMod p), if_pos (mem_univ _), card_singleton, card_univ,
      ZMod.card] at hcard
    simp only [g]
    rw [sum_ite, sum_const, sum_const, filter_eq' univ (0 : ZMod p), if_pos (mem_univ _),
      card_singleton]
    have hp1 := hpr.one_lt
    simp only [smul_eq_mul, mul_one]
    omega
  calc (2 * p - 1) ^ 2 = (∑ a : ZMod p, g a) * ∑ b : ZMod p, g b := by rw [hg, sq]
    _ = ∑ ab : ZMod p × ZMod p, g ab.1 * g ab.2 := by
        rw [sum_mul_sum, ← Fintype.sum_prod_type']
    _ ≤ ∑ ab : ZMod p × ZMod p, c (e ab) := sum_le_sum fun ab _ => hpt ab
    _ = ∑ w, c w := hsum

end OMA.ArxivH1

theorem OMA.solution : OMA.R_arxiv_2606_27961_R1.H1 := OMA.ArxivH1.H1_proof
