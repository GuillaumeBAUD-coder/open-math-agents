import FormalConjectures.ErdosProblems.«402»
import Mathlib

-- Credit: @enriquegil50
-- Reduction of the equality case. H1 and H2 are separate proof obligations.
-- Reference: Balasubramanian and Soundararajan, Acta Arith. 75 (1996), 1-38.

namespace OMA.R_Erdos402_erdos_402_variants_equality_R1

lemma divides_scale_from_factors {A : Finset ℕ} (h0 : 0 ∉ A) (hne : A.Nonempty)
    (hg : A.gcd id = 1) (D : ℕ) (hD : ∀ a ∈ A, ∀ k ∈ Finset.Icc 1 A.card, k ∣ a → k ∣ D)
    (h : ∀ a ∈ A, ∀ b ∈ A, (a / A.card : ℚ) ≤ a.gcd b) :
    ∀ a ∈ A, a ∣ D := by
  intro a ha
  have ha0 : 0 < a := Nat.pos_of_ne_zero (fun e => h0 (e ▸ ha))
  have hn : (0 : ℚ) < A.card := by exact_mod_cast Finset.card_pos.mpr hne
  have H : a ∣ A.gcd (fun b => D * id b) := by
    apply Finset.dvd_gcd_iff.mpr
    intro b hb
    let g := a.gcd b
    have hg0 : 0 < g := Nat.gcd_pos_of_pos_left b ha0
    have hga : g ∣ a := Nat.gcd_dvd_left a b
    have hgb : g ∣ b := Nat.gcd_dvd_right a b
    have hmul : a ≤ g * A.card := by
      exact_mod_cast (div_le_iff₀ hn).mp (h a ha b hb)
    have he : a / g * g = a := Nat.div_mul_cancel hga
    have hle : a / g ≤ A.card := by
      exact Nat.le_of_mul_le_mul_right (by simpa [he, Nat.mul_comm g] using hmul : a / g * g ≤ A.card * g) hg0
    have hpos : 0 < a / g := Nat.div_pos (Nat.le_of_dvd ha0 hga) hg0
    rw [← he]
    exact Nat.mul_dvd_mul (hD a ha _ (Finset.mem_Icc.mpr ⟨hpos, hle⟩) (Nat.div_dvd_of_dvd hga)) hgb
  rw [Finset.gcd_mul_left (f := id), hg] at H
  simpa using H

lemma divides_scale {A : Finset ℕ} (h0 : 0 ∉ A) (hne : A.Nonempty)
    (hg : A.gcd id = 1) (D : ℕ) (hD : ∀ k ∈ Finset.Icc 1 A.card, k ∣ D)
    (h : ∀ a ∈ A, ∀ b ∈ A, (a / A.card : ℚ) ≤ a.gcd b) :
    ∀ a ∈ A, a ∣ D := by
  exact divides_scale_from_factors h0 hne hg D (fun _ _ k hk _ => hD k hk) h

lemma small_cases {A : Finset ℕ} (h0 : 0 ∉ A) (hne : A.Nonempty)
    (hg : A.gcd id = 1) (hn : A.card ≤ 4)
    (h : ∀ a ∈ A, ∀ b ∈ A, (a / A.card : ℚ) ≤ a.gcd b) :
    A = Finset.Icc 1 A.card ∨
  A = (Finset.Icc 1 A.card).image ((Finset.Icc 1 A.card).lcm id / ·) ∨
  A = {2, 3, 4, 6} := by
  have hD : ∀ k ∈ Finset.Icc 1 A.card, k ∣ 12 := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
    have hk4 : k ≤ 4 := hk2.trans hn
    interval_cases k <;> decide
  have sub : A ⊆ Nat.divisors 12 := by
    intro a ha
    exact Nat.mem_divisors.mpr ⟨divides_scale h0 hne hg 12 hD h a ha, by decide⟩
  have cert : ∀ B ∈ (Nat.divisors 12).powerset, B.Nonempty → B.card ≤ 4 →
      B.gcd id = 1 → (∀ a ∈ B, ∀ b ∈ B, a ≤ a.gcd b * B.card) →
      (B = Finset.Icc 1 B.card ∨
       B = (Finset.Icc 1 B.card).image ((Finset.Icc 1 B.card).lcm id / ·) ∨
       B = {2,3,4,6}) := by decide
  apply cert A (Finset.mem_powerset.mpr sub) hne hn hg
  intro a ha b hb
  have hp : (0 : ℚ) < A.card := by exact_mod_cast Finset.card_pos.mpr hne
  exact_mod_cast (div_le_iff₀ hp).mp (h a ha b hb)

lemma interval_of_one {A : Finset ℕ} (h0 : 0 ∉ A) (h1 : 1 ∈ A)
    (h : ∀ a ∈ A, ∀ b ∈ A, (a / A.card : ℚ) ≤ a.gcd b) :
    A = Finset.Icc 1 A.card := by
  have hp : (0 : ℚ) < A.card := by exact_mod_cast Finset.card_pos.mpr ⟨1,h1⟩
  apply Finset.eq_of_subset_of_card_le
  · intro a ha
    have ha0 := Nat.pos_of_ne_zero (fun e => h0 (e ▸ ha) : a ≠ 0)
    have hu : (a : ℚ) ≤ A.card := by simpa using (div_le_iff₀ hp).mp (h a ha 1 h1)
    exact Finset.mem_Icc.mpr ⟨ha0, by exact_mod_cast hu⟩
  · simp

lemma reciprocal_of_top {A : Finset ℕ} (h0 : 0 ∉ A) (hg : A.gcd id = 1)
    {m : ℕ} (hm : m ∈ A) (htop : ∀ a ∈ A, a ∣ m)
    (h : ∀ a ∈ A, ∀ b ∈ A, (a / A.card : ℚ) ≤ a.gcd b) :
    A = (Finset.Icc 1 A.card).image ((Finset.Icc 1 A.card).lcm id / ·) := by
  let I := Finset.Icc 1 A.card
  have hm0 : 0 < m := Nat.pos_of_ne_zero (fun e => h0 (e ▸ hm))
  have hp : (0 : ℚ) < A.card := by exact_mod_cast Finset.card_pos.mpr ⟨m,hm⟩
  have inv (a : ℕ) (ha : a ∈ A) : m / (m / a) = a := by
    exact Nat.div_div_self (htop a ha) (by omega)
  have hsub : A.image (m / ·) ⊆ I := by
    intro k hk
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hk
    have ha0 : 0 < a := Nat.pos_of_ne_zero (fun e => h0 (e ▸ ha))
    have hb : m ≤ a * A.card := by
      have hh := (div_le_iff₀ hp).mp (h m hm a ha)
      rw [Nat.gcd_eq_right (htop a ha)] at hh
      exact_mod_cast hh
    have he := Nat.div_mul_cancel (htop a ha)
    exact Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hm0 (htop a ha)) ha0,
      Nat.le_of_mul_le_mul_right (by simpa only [he, Nat.mul_comm a] using hb : m / a * a ≤ A.card * a) ha0⟩
  have himg : A.image (m / ·) = I := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [Finset.card_image_of_injOn]
    · simp [I]
    · intro a ha b hb heq
      simpa only [inv a ha, inv b hb] using congrArg (m / ·) heq
  have hd1 : I.lcm id ∣ m := by
    apply Finset.lcm_dvd
    intro k hk
    rw [← himg] at hk
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hk
    exact Nat.div_dvd_of_dvd (htop a ha)
  have hd2 : m ∣ I.lcm id := divides_scale h0 ⟨m,hm⟩ hg _ (fun k hk => Finset.dvd_lcm (f := id) hk) h m hm
  have heq := Nat.dvd_antisymm hd2 hd1
  change A = I.image (I.lcm id / ·)
  rw [← heq]
  apply Finset.eq_of_subset_of_card_le
  · intro a ha
    exact Finset.mem_image.mpr ⟨m/a, hsub (Finset.mem_image_of_mem _ ha), inv a ha⟩
  · exact (Finset.card_image_le).trans (by simp [I])

lemma two_sides {X Y : Finset ℕ} {n : ℕ} (hx : X.Nonempty) (hy : Y.Nonempty)
    (hx0 : 0 ∉ X) (hy0 : 0 ∉ Y) (hn : 5 ≤ n) (hs : X.card + Y.card = n)
    (hprod : ∀ x ∈ X, ∀ y ∈ Y, x*y ≤ n) : X.card = 1 ∨ Y.card = 1 := by
  have bound {S : Finset ℕ} (hsn : S.Nonempty) (hz : 0 ∉ S) : S.card ≤ S.max' hsn := by
    have sub : S ⊆ Finset.Icc 1 (S.max' hsn) := by
      intro x hx
      exact Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero (fun e => hz (e ▸ hx)), S.le_max' x hx⟩
    simpa using Finset.card_le_card sub
  have hp := (Nat.mul_le_mul (bound hx hx0) (bound hy hy0)).trans
    (hprod _ (X.max'_mem hx) _ (Y.max'_mem hy))
  have hxpos := Finset.card_pos.mpr hx
  have hypos := Finset.card_pos.mpr hy
  by_contra! bad
  obtain ⟨r, hr⟩ : ∃ r, X.card = r+2 := ⟨X.card-2, by omega⟩
  obtain ⟨s, ht⟩ : ∃ s, Y.card = s+2 := ⟨Y.card-2, by omega⟩
  rw [hr, ht] at hs hp
  nlinarith [Nat.zero_le (r*s)]

lemma large_prime {A : Finset ℕ} (h0 : 0 ∉ A) (hg : A.gcd id = 1) (hn : 5 ≤ A.card)
    (h : ∀ a ∈ A, ∀ b ∈ A, (a / A.card : ℚ) ≤ a.gcd b)
    {p : ℕ} (hp : p.Prime) (hp2 : A.card < 2*p) (hw : ∃ a ∈ A, p ∣ a) :
    1 ∈ A ∨ ∃ m ∈ A, ∀ a ∈ A, a ∣ m := by
  let C := A.filter (fun x => p ∣ x)
  let V := A.filter (fun x => ¬ p ∣ x)
  obtain ⟨a, ha, hpa⟩ := hw
  have cn : C.Nonempty := ⟨a, Finset.mem_filter.mpr ⟨ha,hpa⟩⟩
  have vn : V.Nonempty := by
    by_contra! empty
    have hall : p ∣ A.gcd id := Finset.dvd_gcd (fun x hx => by
      by_contra bad
      have hv : x ∈ V := Finset.mem_filter.mpr ⟨hx,bad⟩
      simp [empty] at hv)
    exact hp.not_dvd_one (hg ▸ hall)
  have pos {a : ℕ} (ha : a ∈ A) : 0 < a := Nat.pos_of_ne_zero (fun e => h0 (e ▸ ha))
  have hnq : (0 : ℚ) < A.card := by exact_mod_cast (by omega : 0 < A.card)
  have ratios (a b : ℕ) (ha : a ∈ A) (hb : b ∈ A) : a ≤ (a.gcd b)*A.card := by
    exact_mod_cast (div_le_iff₀ hnq).mp (h a ha b hb)
  have cross {c v : ℕ} (hc : c ∈ C) (hv : v ∈ V) : c / p = c.gcd v := by
    obtain ⟨hcA,hpc⟩ := Finset.mem_filter.mp hc
    obtain ⟨hvA,hpv⟩ := Finset.mem_filter.mp hv
    let d := c.gcd v
    have hd : 0 < d := Nat.gcd_pos_of_pos_left v (pos hcA)
    have he : c/d*d = c := Nat.div_mul_cancel (Nat.gcd_dvd_left c v)
    have hqpos := Nat.div_pos (Nat.gcd_le_left v (pos hcA)) hd
    have hqle : c/d ≤ A.card := Nat.le_of_mul_le_mul_right
      (by simpa only [he, Nat.mul_comm A.card] using ratios c v hcA hvA : c/d*d ≤ A.card*d) hd
    have hpd : ¬ p ∣ d := fun k => hpv (k.trans (Nat.gcd_dvd_right c v))
    have hdiv : p ∣ c/d := (hp.dvd_mul.mp (he.symm ▸ hpc)).resolve_right hpd
    obtain ⟨k,hk⟩ := hdiv
    have hk1 : k = 1 := by
      have : 0 < p*k := hk ▸ hqpos
      by_contra hne
      have hk2 : 2 ≤ k := by cases k <;> simp_all; omega
      have := Nat.mul_le_mul_left p hk2
      omega
    rw [hk, hk1, mul_one] at he
    change c/p = d
    rw [←he, Nat.mul_div_cancel_left _ hp.pos]
  let g := V.gcd id
  have gd {v : ℕ} (hv : v ∈ V) : g ∣ v := Finset.gcd_dvd hv
  have gp : 0 < g := by
    obtain ⟨v,hv⟩ := vn
    exact Nat.pos_of_dvd_of_pos (gd hv) (pos (Finset.mem_filter.mp hv).1)
  have cg {c : ℕ} (hc : c ∈ C) : c/p ∣ g := Finset.dvd_gcd (fun v hv => by
    change c/p ∣ v
    rw [cross hc hv]
    exact Nat.gcd_dvd_right c v)
  have pc {c : ℕ} (hc : c ∈ C) : p*(c/p) = c := Nat.mul_div_cancel' (Finset.mem_filter.mp hc).2
  have cD {c : ℕ} (hc : c ∈ C) : c ∣ p*g := pc hc ▸ Nat.mul_dvd_mul_left p (cg hc)
  have dpos : 0 < p*g := Nat.mul_pos hp.pos gp
  let X := C.image ((p*g) / ·)
  let Y := V.image (· / g)
  have xc : X.card = C.card := Finset.card_image_of_injOn (by
    intro c hc d hd e
    simpa only [Nat.div_div_self (cD hc) dpos.ne', Nat.div_div_self (cD hd) dpos.ne'] using congrArg ((p*g) / ·) e)
  have yc : Y.card = V.card := Finset.card_image_of_injOn (by
    intro v hv w hw e
    exact (Nat.div_left_inj (gd hv) (gd hw)).mp e)
  have xz {c : ℕ} (hc : c ∈ C) : 0 < p*g/c := Nat.div_pos (Nat.le_of_dvd dpos (cD hc)) (pos (Finset.mem_filter.mp hc).1)
  have yz {v : ℕ} (hv : v ∈ V) : 0 < v/g := Nat.div_pos (Nat.le_of_dvd (pos (Finset.mem_filter.mp hv).1) (gd hv)) gp
  have nxy : X.card + Y.card = A.card := by rw [xc, yc]; exact Finset.card_filter_add_card_filter_not (fun x => p ∣ x)
  have prod {c v : ℕ} (hc : c ∈ C) (hv : v ∈ V) : (p*g/c)*(v/g) ≤ A.card := by
    let d := c.gcd v
    have hd : 0 < d := Nat.gcd_pos_of_pos_left v (pos (Finset.mem_filter.mp hc).1)
    have he : p*d = c := by simpa only [d, ←cross hc hv] using pc hc
    have f : (p*g/c)*d = g := by
      apply Nat.eq_of_mul_eq_mul_left hp.pos
      calc p*((p*g/c)*d) = (p*g/c)*(p*d) := by ring
           _ = p*g := by rw [he, Nat.div_mul_cancel (cD hc)]
    apply Nat.le_of_mul_le_mul_right _ hd
    calc (p*g/c)*(v/g)*d = (v/g)*((p*g/c)*d) := by ring
         _ = v := by rw [f, Nat.div_mul_cancel (gd hv)]
         _ ≤ A.card*d := by simpa [d, Nat.gcd_comm, Nat.mul_comm] using ratios v c (Finset.mem_filter.mp hv).1 (Finset.mem_filter.mp hc).1
  have single := two_sides (cn.image _) (vn.image _)
    (by rintro hmem; obtain ⟨c,hc,e⟩ := Finset.mem_image.mp hmem; exact (xz hc).ne' e)
    (by rintro hmem; obtain ⟨v,hv,e⟩ := Finset.mem_image.mp hmem; exact (yz hv).ne' e)
    hn nxy (by intro x hx y hy; obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hx; obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hy; exact prod hc hv)
  have ps : p ≤ A.card := by
    obtain ⟨c,hc⟩ := cn
    obtain ⟨v,hv⟩ := vn
    have hh := ratios c v (Finset.mem_filter.mp hc).1 (Finset.mem_filter.mp hv).1
    rw [←cross hc hv, ←pc hc] at hh
    have hp0 : 0 < c/p := Nat.div_pos (Nat.le_of_dvd (pos (Finset.mem_filter.mp hc).1) (Finset.mem_filter.mp hc).2) hp.pos
    apply Nat.le_of_mul_le_mul_right _ hp0
    calc p*(c/p) = c := pc hc
         _ ≤ (c/p)*A.card := by simpa only [pc hc] using hh
         _ = A.card*(c/p) := Nat.mul_comm _ _
  change X.card = 1 ∨ Y.card = 1 at single
  rw [xc,yc] at single
  rcases single with hc1 | hv1
  · left
    obtain ⟨c,hcset⟩ := Finset.card_eq_one.mp hc1
    have hc : c ∈ C := hcset ▸ Finset.mem_singleton_self c
    have hdvd : c/p ∣ A.gcd id := Finset.dvd_gcd (fun x hx => by
      by_cases k : p ∣ x
      · have hxC : x ∈ C := Finset.mem_filter.mpr ⟨hx,k⟩
        have e : x = c := Finset.mem_singleton.mp (hcset ▸ hxC)
        change c/p ∣ x
        rw [e]
        exact Nat.div_dvd_of_dvd (Finset.mem_filter.mp hc).2
      · exact (cg hc).trans (gd (Finset.mem_filter.mpr ⟨hx,k⟩)))
    rw [hg] at hdvd
    have hone : c/p = 1 := Nat.eq_one_of_dvd_one hdvd
    have hi : A = Finset.Icc 1 A.card := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        refine Finset.mem_Icc.mpr ⟨pos hx, ?_⟩
        by_cases k : p ∣ x
        · have hxC : x ∈ C := Finset.mem_filter.mpr ⟨hx,k⟩
          have e : x = c := Finset.mem_singleton.mp (hcset ▸ hxC)
          have ec : p = c := by simpa only [hone,mul_one] using pc hc
          simpa only [e, ←ec] using ps
        · have hv : x ∈ V := Finset.mem_filter.mpr ⟨hx,k⟩
          simpa only [Nat.gcd_comm x c, ←cross hc hv, hone, one_mul] using ratios x c hx (Finset.mem_filter.mp hc).1
      · simp
    exact hi.symm ▸ Finset.mem_Icc.mpr ⟨by decide, by omega⟩
  · right
    obtain ⟨v,hvset⟩ := Finset.card_eq_one.mp hv1
    have hv : v ∈ V := hvset ▸ Finset.mem_singleton_self v
    have gv : g = v := by simp [g,hvset]
    have divA (x : ℕ) (hx : x ∈ A) : x ∣ p*g := by
      by_cases k : p ∣ x
      · exact cD (Finset.mem_filter.mpr ⟨hx,k⟩)
      · have hxV : x ∈ V := Finset.mem_filter.mpr ⟨hx,k⟩
        have e : x = v := Finset.mem_singleton.mp (hvset ▸ hxV)
        simp [e,gv]
    have imageEq : A.image ((p*g)/·) = Finset.Icc 1 A.card := by
      apply Finset.eq_of_subset_of_card_le
      · intro t ht
        obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ht
        refine Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd dpos (divA x hx)) (pos hx),?_⟩
        by_cases k : p ∣ x
        · have h1 : v/g = 1 := by rw [gv, Nat.div_self (pos (Finset.mem_filter.mp hv).1)]
          simpa only [h1,mul_one] using prod (Finset.mem_filter.mpr ⟨hx,k⟩) hv
        · have hxV : x ∈ V := Finset.mem_filter.mpr ⟨hx,k⟩
          have e : x = g := (Finset.mem_singleton.mp (hvset ▸ hxV)).trans gv.symm
          simpa only [e,Nat.mul_div_cancel _ gp] using ps
      · rw [Finset.card_image_of_injOn]
        · simp
        · intro x hx y hy e
          simpa only [Nat.div_div_self (divA x hx) dpos.ne',Nat.div_div_self (divA y hy) dpos.ne'] using congrArg ((p*g)/·) e
    have one : 1 ∈ A.image ((p*g)/·) := imageEq.symm ▸ Finset.mem_Icc.mpr ⟨by decide,by omega⟩
    obtain ⟨m,hm,he⟩ := Finset.mem_image.mp one
    have me : m = p*g := by simpa only [he, one_mul] using Nat.div_mul_cancel (divA m hm)
    exact ⟨m,hm,fun a ha => me.symm ▸ divA a ha⟩

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 16000 in
lemma through_eight {A : Finset ℕ} (h0 : 0 ∉ A) (hne : A.Nonempty)
    (hg : A.gcd id = 1) (hn : A.card ≤ 8)
    (h : ∀ a ∈ A, ∀ b ∈ A, (a / A.card : ℚ) ≤ a.gcd b) :
    A = Finset.Icc 1 A.card ∨
  A = (Finset.Icc 1 A.card).image ((Finset.Icc 1 A.card).lcm id / ·) ∨
  A = {2, 3, 4, 6} := by
  by_cases hs : A.card ≤ 4
  · exact small_cases h0 hne hg hs h
  by_cases hp : ∃ p : ℕ, p.Prime ∧ A.card < 2*p ∧ ∃ a ∈ A, p ∣ a
  · obtain ⟨p,hpr,hp2,hw⟩ := hp
    rcases large_prime h0 hg (by omega) h hpr hp2 hw with hone | ⟨m,hm,ht⟩
    · exact Or.inl (interval_of_one h0 hone h)
    · exact Or.inr (Or.inl (reciprocal_of_top h0 hg hm ht h))
  have hd : ∀ a ∈ A, a ∣ 24 := by
    apply divides_scale_from_factors h0 hne hg 24 _ h
    intro a ha k hk hka
    obtain ⟨hk1,hkn⟩ := Finset.mem_Icc.mp hk
    have hk9 := hkn.trans hn
    interval_cases k <;> first | decide | exact (hp ⟨5, by decide, by omega, a, ha, hka⟩).elim | exact (hp ⟨7, by decide, by omega, a, ha, hka⟩).elim
  have cert : ∀ B ∈ (Nat.divisors 24).powerset, B.Nonempty → B.card ≤ 8 →
      B.gcd id = 1 → (∀ a ∈ B, ∀ b ∈ B, a ≤ a.gcd b * B.card) →
      (B = Finset.Icc 1 B.card ∨ B = (Finset.Icc 1 B.card).image ((Finset.Icc 1 B.card).lcm id / ·) ∨ B = {2,3,4,6}) := by decide
  apply cert A (Finset.mem_powerset.mpr (fun a ha => Nat.mem_divisors.mpr ⟨hd a ha, by decide⟩)) hne hn hg
  intro a ha b hb
  have hpq : (0 : ℚ) < A.card := by exact_mod_cast Finset.card_pos.mpr hne
  exact_mod_cast (div_le_iff₀ hpq).mp (h a ha b hb)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 16000 in
lemma through_nine {A : Finset ℕ} (h0 : 0 ∉ A) (hne : A.Nonempty)
    (hg : A.gcd id = 1) (hn : A.card ≤ 9)
    (h : ∀ a ∈ A, ∀ b ∈ A, (a / A.card : ℚ) ≤ a.gcd b) :
    A = Finset.Icc 1 A.card ∨
  A = (Finset.Icc 1 A.card).image ((Finset.Icc 1 A.card).lcm id / ·) ∨
  A = {2, 3, 4, 6} := by
  by_cases hs : A.card ≤ 8
  · exact through_eight h0 hne hg hs h
  by_cases hp : ∃ p : ℕ, p.Prime ∧ A.card < 2*p ∧ ∃ a ∈ A, p ∣ a
  · obtain ⟨p,hpr,hp2,hw⟩ := hp
    rcases large_prime h0 hg (by omega) h hpr hp2 hw with hone | ⟨m,hm,ht⟩
    · exact Or.inl (interval_of_one h0 hone h)
    · exact Or.inr (Or.inl (reciprocal_of_top h0 hg hm ht h))
  have hd : ∀ a ∈ A, a ∣ 72 := by
    apply divides_scale_from_factors h0 hne hg 72 _ h
    intro a ha k hk hka
    obtain ⟨hk1,hkn⟩ := Finset.mem_Icc.mp hk
    have hk9 := hkn.trans hn
    interval_cases k <;> first | decide | exact (hp ⟨5, by decide, by omega, a, ha, hka⟩).elim | exact (hp ⟨7, by decide, by omega, a, ha, hka⟩).elim
  have cert : ∀ B ∈ (Nat.divisors 72).powersetCard 9, B.Nonempty → B.card ≤ 9 →
      B.gcd id = 1 → (∀ a ∈ B, ∀ b ∈ B, a ≤ a.gcd b * B.card) →
      (B = Finset.Icc 1 B.card ∨ B = (Finset.Icc 1 B.card).image ((Finset.Icc 1 B.card).lcm id / ·) ∨ B = {2,3,4,6}) := by decide
  apply cert A (Finset.mem_powersetCard.mpr ⟨fun a ha => Nat.mem_divisors.mpr ⟨hd a ha, by decide⟩, by omega⟩) hne hn hg
  intro a ha b hb
  have hpq : (0 : ℚ) < A.card := by exact_mod_cast Finset.card_pos.mpr hne
  exact_mod_cast (div_le_iff₀ hpq).mp (h a ha b hb)

/-- Finite range of Section 3 of Balasubramanian and Soundararajan (1996).
For each cardinality the search is restricted to divisors of a known integer. -/
def H1 : Prop := ∀ n : ℕ, 10 ≤ n → n ≤ 2220000000000 →
  ∀ A ∈ (Nat.divisors ((Finset.Icc 1 n).lcm id)).powersetCard n, A.gcd id = 1 →
    (∀ a ∈ A, ∀ b ∈ A, a ≤ a.gcd b * n) → ∃ p : ℕ, p.Prime ∧ n < 2*p ∧ ∃ a ∈ A, p ∣ a

/-- Analytic range of Sections 4–6. For a set supported on small primes,
some ordered pair must violate the directed quotient bound. -/
def H2 : Prop := ∀ (n : ℕ) (A : Finset ℕ), 2220000000000 < n → A.card = n →
  0 ∉ A → A.gcd id = 1 → (∀ a ∈ A, ∀ p : ℕ, p.Prime → p ∣ a → 2*p ≤ n) →
  ∃ a ∈ A, ∃ b ∈ A, a.gcd b * n < a

theorem main : H1 → H2 → type_of% @Erdos402.erdos_402.variants.equality := by
  intro finiteRange analyticRange A h0 hne hg h
  by_cases hs : A.card ≤ 9
  · exact through_nine h0 hne hg hs h
  have hn : (0 : ℚ) < A.card := by exact_mod_cast Finset.card_pos.mpr hne
  have rect (a : ℕ) (ha : a ∈ A) (b : ℕ) (hb : b ∈ A) : a ≤ a.gcd b * A.card := by
    exact_mod_cast (div_le_iff₀ hn).mp (h a ha b hb)
  have prime : ∃ p : ℕ, p.Prime ∧ A.card < 2*p ∧ ∃ a ∈ A, p ∣ a := by
    by_cases mid : A.card ≤ 2220000000000
    · let I := Finset.Icc 1 A.card
      have Dpos : I.lcm id ≠ 0 := by
        intro hz
        simp [I, Finset.lcm_eq_zero_iff] at hz
      have sub : A ⊆ (I.lcm id).divisors := by
        intro a ha
        refine Nat.mem_divisors.mpr ⟨?_, Dpos⟩
        exact divides_scale h0 hne hg _ (fun k hk => Finset.dvd_lcm (f := id) hk) h a ha
      exact finiteRange _ (by omega) mid A (Finset.mem_powersetCard.mpr ⟨sub,rfl⟩) hg rect
    · by_contra missing
      have smooth : ∀ a ∈ A, ∀ p : ℕ, p.Prime → p ∣ a → 2*p ≤ A.card := by
        intro a ha p pr dvd
        by_contra! greater
        exact missing ⟨p,pr,greater,a,ha,dvd⟩
      obtain ⟨a,ha,b,hb,hab⟩ := analyticRange _ A (by omega) rfl h0 hg smooth
      exact (not_lt_of_ge (rect a ha b hb)) hab
  obtain ⟨p,pr,hp,hw⟩ := prime
  rcases large_prime h0 hg (by omega) h pr hp hw with hone | ⟨m,hm,ht⟩
  · exact Or.inl (interval_of_one h0 hone h)
  · exact Or.inr (Or.inl (reciprocal_of_top h0 hg hm ht h))

end OMA.R_Erdos402_erdos_402_variants_equality_R1
