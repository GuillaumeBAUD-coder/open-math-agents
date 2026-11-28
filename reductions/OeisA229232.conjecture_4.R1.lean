import FormalConjectures.OEIS.«229232»

/-!
# Reciprocal primitive elements and a Hamilton path

The exponent reflections in the selection notes suggest alternating two allowed
products. Taking a primitive element and its inverse makes their shifted ratio
a generator. A reversal of the final segment closes the resulting path if two
explicit shifted powers are primitive.
-/

namespace OMA.R_OeisA229232_conjecture_4_R1

private theorem chooseRoot (F : Type*) [Field F] [Fintype F] (hq : 7 < Fintype.card F) :
    ∃ g h : Fˣ, orderOf g = Fintype.card F - 1 ∧ (h : F)^2 = 1 + (g : F) := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have ho := orderOf_eq_card_of_forall_mem_zpowers hg
  rw [Nat.card_units, Nat.card_eq_fintype_card] at ho
  have hn : 1 + (g : F) ≠ 0 := by
    intro he
    have hsq : g ^ 2 = 1 := by
      apply Units.ext
      change (g : F)^2 = 1
      have : (g : F) = -1 := by linear_combination he
      rw [this]
      ring
    have := orderOf_le_of_pow_eq_one (by decide : 0 < 2) hsq
    omega
  let u := Units.mk0 (1 + (g : F)) hn
  obtain ⟨z, hz⟩ := hg u
  have hz' : (↑(g ^ z) : F) = 1 + (g : F) := congrArg Units.val hz
  rcases Int.even_or_odd z with ⟨k, hk⟩ | ⟨k, hk⟩
  · refine ⟨g, g ^ k, ho, ?_⟩
    rw [← hz', hk, zpow_add]
    simp [pow_two]
  · refine ⟨g⁻¹, g ^ k, by simpa using ho, ?_⟩
    rw [hk, show 2*k+1 = k+k+1 by omega, zpow_add, zpow_add] at hz'
    simp only [zpow_one, Units.val_mul] at hz'
    simp only [Units.val_inv_eq_inv_val]
    rw [← mul_left_inj' g.ne_zero]
    calc
      (↑(g ^ k) : F)^2 * (g : F) = 1 + (g : F) := by linear_combination hz'
      _ = (1 + (g : F)⁻¹) * (g : F) := by field_simp; ring

private theorem path (F : Type*) [Field F] [Fintype F]
    (m : ℕ) (hm : m = Fintype.card F - 1) (g h : Fˣ)
    (hg : orderOf g = m) (hh : (h : F)^2 = 1 + (g : F)) :
    let e := fun i : ℕ => if i % 2 = 0 then i / 2 else m - 1 - i / 2
    ∃ a : Fin m ≃ Fˣ, (∀ i, a i = h * g ^ e i) ∧
      ∀ i : ℕ, ∀ hi : i + 1 < m,
        IsPrimitiveRoot ((a ⟨i, by omega⟩ : F) * (a ⟨i+1, hi⟩ : F) - 1) m := by
  classical
  intro e
  let f (i : Fin m) := h * g ^ e i
  have hel (i : Fin m) : e i < m := by dsimp [e]; split <;> omega
  have hinj : Function.Injective f := by
    intro i j hij
    have heq : e i = e j := by
      apply pow_injOn_Iio_orderOf (x := g) (hg ▸ hel i) (hg ▸ hel j)
      exact mul_left_cancel hij
    apply Fin.ext
    dsimp [e] at heq
    split at heq <;> split at heq <;> omega
  have hc : Fintype.card (Fin m) = Fintype.card Fˣ := by simp [Fintype.card_units, hm]
  let a := Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).2 ⟨hinj,hc⟩)
  refine ⟨a, fun _ => rfl, ?_⟩
  intro i hi
  change IsPrimitiveRoot ((↑(h * g ^ e i) : F) * ↑(h * g ^ e (i+1)) - 1) m
  have he : (↑(h * g ^ e i) : F) * ↑(h * g ^ e (i+1)) =
      (h : F)^2 * (g : F)^(e i + e (i+1)) := by
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, pow_add]
    ring
  rw [he, hh]
  have hg' : IsPrimitiveRoot (g : F) m := IsPrimitiveRoot.iff_orderOf.mpr (orderOf_units.trans hg)
  have hpow := hg'.pow_eq_one
  by_cases hp : i % 2 = 0
  · have hs : e i + e (i+1) + 1 = m := by dsimp [e]; split <;> split <;> omega
    have hx : (g : F)^(e i + e (i+1)) * g = 1 := by rwa [← pow_succ, hs]
    have hy : (1+(g : F)) * (g : F)^(e i + e (i+1)) - 1 = (g : F)⁻¹ := by
      field_simp
      linear_combination (1+(g : F))*hx
    rw [hy]
    exact hg'.inv
  · have hs : e i + e (i+1) = m := by dsimp [e]; split <;> split <;> omega
    simpa [hs,hpow] using hg'

private theorem closePath {V : Type*} {m : ℕ} (hm : 0 < m)
    (a : Fin m ≃ V) (R : V → V → Prop) (symm : ∀ {u v}, R u v → R v u)
    (adj : ∀ i : ℕ, ∀ hi : i + 1 < m, R (a ⟨i, by omega⟩) (a ⟨i+1, hi⟩))
    (k : ℕ) (hk : k+1 < m)
    (hl : R (a ⟨k, by omega⟩) (a ⟨m-1, by omega⟩))
    (hr : R (a ⟨k+1, hk⟩) (a ⟨0, hm⟩)) :
    ∃ b : Fin m ≃ V, ∀ i : Fin m, R (b i) (b ⟨(i.val+1)%m, Nat.mod_lt _ hm⟩) := by
  let f (i : Fin m) : Fin m := if hi : i.val ≤ k then i else ⟨m+k-i.val, by omega⟩
  have inv : Function.Involutive f := by
    intro i
    apply Fin.ext
    dsimp [f]
    by_cases hi : i.val ≤ k
    · simp [hi]
    · simp [hi, show ¬ m + k - i.val ≤ k by omega]; omega
  let b := (inv.toPerm f).trans a
  refine ⟨b, ?_⟩
  intro i
  change R (a (f i)) (a (f ⟨_, _⟩))
  by_cases hlast : i.val+1 = m
  · have hval : i.val = m-1 := by omega
    convert hr using 1 <;> congr 2 <;> apply Fin.ext <;> simp [f, hval, show m-1+1 = m by omega, show ¬ m-1 ≤ k by omega]; omega
  · have hi : i.val+1 < m := by omega
    have hmod := Nat.mod_eq_of_lt hi
    by_cases hpre : i.val < k
    · simpa [f,hmod, show i.val ≤ k by omega, show i.val+1 ≤ k by omega] using adj i.val hi
    · by_cases heq : i.val = k
      · convert hl using 1 <;> congr 2 <;> apply Fin.ext <;> simp [f,heq,Nat.mod_eq_of_lt hk]; omega
      · have hp : ¬ i.val ≤ k := by omega
        have hp' : ¬ i.val+1 ≤ k := by omega
        have hbound : m+k-(i.val+1)+1 < m := by omega
        convert symm (adj (m+k-(i.val+1)) hbound) using 1 <;> congr 2 <;>
          apply Fin.ext <;> simp [f,hmod,hp,hp']; omega

private theorem enoughNeighbors {F : Type*} [Field F] [Fintype F] {m : ℕ}
    (hm : 2 < m) (g : Fˣ) (hg : orderOf g = m)
    (a : Fin m ≃ Fˣ) (x : Fˣ) :
    open Classical in
    m.totient ≤ (Finset.univ.filter (fun i : Fin m =>
      IsPrimitiveRoot ((x : F) * (a i : F) - 1) m)).card := by
  classical
  let P := Finset.univ.filter (fun i : Fin m => IsPrimitiveRoot ((x : F) * (a i : F) - 1) m)
  have hs : primitiveRoots m F ⊆ P.image (fun i => (x : F) * (a i : F) - 1) := by
    intro y hy
    have hr := isPrimitiveRoot_of_mem_primitiveRoots hy
    have hne : y+1 ≠ 0 := by
      intro h
      have he : y = -1 := by linear_combination h
      have hd := hr.dvd_of_pow_eq_one 2 (by rw [he]; ring)
      have := Nat.le_of_dvd (by decide : 0 < 2) hd
      omega
    let u := Units.mk0 (y+1) hne / x
    have hu : (x : F) * (a (a.symm u) : F) - 1 = y := by
      simp [u, mul_div_cancel₀, x.ne_zero]
    exact Finset.mem_image.mpr ⟨a.symm u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu ▸ hr⟩, hu⟩
  have hprim : IsPrimitiveRoot (g : F) m := IsPrimitiveRoot.iff_orderOf.mpr (orderOf_units.trans hg)
  rw [← hprim.card_primitiveRoots]
  exact (Finset.card_le_card hs).trans Finset.card_image_le

private theorem densePivot {F : Type*} [Field F] [Fintype F] {m : ℕ}
    (hm : 2 < m) (g : Fˣ) (hg : orderOf g = m) (hd : m+1 < 2*m.totient)
    (a : Fin m ≃ Fˣ) :
    ∃ k : ℕ, ∃ hk : k+1 < m,
      IsPrimitiveRoot ((a ⟨m-1, by omega⟩ : F) * (a ⟨k, by omega⟩ : F) - 1) m ∧
      IsPrimitiveRoot ((a ⟨0, by omega⟩ : F) * (a ⟨k+1, hk⟩ : F) - 1) m := by
  classical
  let last : Fin m := ⟨m-1, by omega⟩
  let first : Fin m := ⟨0, by omega⟩
  let U := Finset.univ.filter (fun i : Fin m => IsPrimitiveRoot ((a last : F) * (a i : F) - 1) m)
  let V := Finset.univ.filter (fun i : Fin m => IsPrimitiveRoot ((a first : F) * (a (finRotate m i) : F) - 1) m)
  have hu : m.totient ≤ U.card := enoughNeighbors hm g hg a (a last)
  have hv : m.totient ≤ V.card := enoughNeighbors hm g hg ((finRotate m).trans a) (a first)
  have hcard := Finset.card_union_add_card_inter U V
  have hle : (U ∪ V).card ≤ m := by simpa using Finset.card_le_univ (U ∪ V)
  obtain ⟨i, hi, hne⟩ : ∃ i ∈ U ∩ V, i ∉ ({last} : Finset (Fin m)) :=
    Finset.exists_mem_notMem_of_card_lt_card (by simp; omega)
  have hi' : i.val + 1 < m := by
    have hl : i ≠ last := by simpa using hne
    contrapose! hl
    apply Fin.ext
    dsimp [last]
    omega
  have hrot : finRotate m i = ⟨i.val+1, hi'⟩ := by
    have : NeZero m := ⟨by omega⟩
    rw [finRotate_apply]
    apply Fin.ext
    change (i.val + 1 % m) % m = i.val+1
    rw [Nat.mod_eq_of_lt (by omega : 1 < m), Nat.mod_eq_of_lt hi']
  obtain ⟨hu', hv'⟩ := Finset.mem_inter.mp hi
  exact ⟨i.val, hi', (Finset.mem_filter.mp hu').2, hrot ▸ (Finset.mem_filter.mp hv').2⟩

/-- Every field in the conjecture admits a spanning path of primitive adjacencies. -/
theorem reciprocalPath (F : Type*) [Field F] [Fintype F] (hq : 7 < Fintype.card F) :
    let m := Fintype.card F - 1
    ∃ (g : Fˣ) (a : Fin m ≃ Fˣ), orderOf g = m ∧ ∀ i : ℕ, ∀ hi : i+1 < m,
      IsPrimitiveRoot ((a ⟨i, by omega⟩ : F) * (a ⟨i+1, hi⟩ : F) - 1) m := by
  intro m
  obtain ⟨g,h,hg,hh⟩ := chooseRoot F hq
  obtain ⟨a,_,ha⟩ := path F m rfl g h hg hh
  exact ⟨g,a,hg,ha⟩

/-- Intersecting two sets of possible cuts closes the reciprocal path. -/
theorem cycle_of_totient (F : Type*) [Field F] [Fintype F] (hq : 7 < Fintype.card F)
    (hd : Fintype.card F < 2 * (Fintype.card F - 1).totient) :
    let m := Fintype.card F - 1
    ∃ a : Fin m ≃ Fˣ, ∀ i : Fin m, IsPrimitiveRoot
      ((a i : F) * (a ⟨(i.val+1)%m, Nat.mod_lt _ (by omega)⟩ : F) - 1) m := by
  intro m
  have hm : 2 < m := by dsimp [m]; omega
  obtain ⟨g,a,hg,ha⟩ := reciprocalPath F hq
  obtain ⟨k,hk,hl,hr⟩ := densePivot hm g hg (by
    have hcard : m+1 = Fintype.card F := by dsimp [m]; omega
    rwa [hcard]) a
  let R := fun x y : Fˣ => IsPrimitiveRoot ((x:F)*(y:F)-1) m
  have sym : ∀ {x y}, R x y → R y x := by intro x y; simp [R,mul_comm]
  exact closePath (by omega) a R sym ha k hk (sym hl) (sym hr)

theorem densePrimeDegree (p : ℕ) (hp : p.Prime) (hp' : 2 < p) :
    let m := 2^p-1
    m+1 < 2*m.totient := by
  intro m
  have hpow : p+1 < 2^p := by
    induction p with
    | zero => omega
    | succ p ih =>
      by_cases h : p ≤ 2
      · interval_cases p <;> norm_num at *
      · have := Nat.lt_two_pow_self (n := p)
        rw [pow_succ]; omega
  have hm : m+1 = 2^p := by dsimp [m]; omega
  have hp_lt : p < m := by omega
  have hfac (r : ℕ) (hr : r ∈ m.primeFactors) : p < r := by
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hrd := Nat.dvd_of_mem_primeFactors hr
    have : Fact r.Prime := ⟨hrp⟩
    have h1 : (2 : ZMod r)^p = 1 := by
      have h0 := (ZMod.natCast_eq_zero_iff m r).2 hrd
      have hx := congrArg (fun x : ℕ => (x : ZMod r)) hm
      simpa [h0] using hx.symm
    have hat : orderOf (2 : ZMod r) = p := by
      rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one h1) with h | h
      · have htwo := orderOf_eq_one_iff.mp h
        have : (1 : ZMod r) = 0 := by linear_combination htwo
        exact (one_ne_zero this).elim
      · exact h
    have h2 : (2 : ZMod r) ≠ 0 := by
      intro h
      simp [h,hp.ne_zero] at h1
    have he := ZMod.pow_card_sub_one_eq_one h2
    have hd := orderOf_dvd_of_pow_eq_one he
    rw [hat] at hd
    have := Nat.le_of_dvd (show 0 < r-1 by have := hrp.two_le; omega) hd
    omega
  have hsmall : 2*m.primeFactors.card < p := by
    have hb : 4^m.primeFactors.card ≤ ∏ r ∈ m.primeFactors, r := by
      simpa using Finset.prod_le_prod' (s := m.primeFactors) (f := fun _ => 4) (g := id)
        (fun r hr => show 4 ≤ r by have := hfac r hr; omega)
    have hle := Nat.le_of_dvd (show 0 < m by omega) (Nat.prod_primeFactors_dvd m)
    have hpowers : (2:ℕ)^(2*m.primeFactors.card) < 2^p := by
      rw [pow_mul]
      change 4^m.primeFactors.card < 2^p
      omega
    exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hpowers
  have hprod : (1-1/((p:ℚ)+1))^m.primeFactors.card ≤
      ∏ r ∈ m.primeFactors, (1 - (r:ℚ)⁻¹) := by
    rw [← Finset.prod_const]
    apply Finset.prod_le_prod
    · intro i hi
      have : (1:ℚ) ≤ p+1 := by linarith [Nat.cast_nonneg (α := ℚ) p]
      have := one_div_le_one_div_of_le (by norm_num : (0:ℚ) < 1) this
      linarith
    · intro r hr
      have hs : (p:ℚ)+1 ≤ r := by exact_mod_cast hfac r hr
      have := one_div_le_one_div_of_le (by positivity : (0:ℚ) < p+1) hs
      simpa [one_div] using sub_le_sub_left this 1
  have bern := one_add_mul_le_pow (show (-2:ℚ) ≤ -(1/((p:ℚ)+1)) by
    have : (1:ℚ) ≤ p+1 := by linarith [Nat.cast_nonneg (α := ℚ) p]
    have := one_div_le_one_div_of_le (by norm_num : (0:ℚ)<1) this
    linarith) m.primeFactors.card
  have hlow : 1 - (m.primeFactors.card:ℚ) / ((p:ℚ)+1) ≤ ∏ r ∈ m.primeFactors, (1 - (r:ℚ)⁻¹) := by
    apply le_trans _ hprod
    convert bern using 1 <;> ring
  have ht := mul_le_mul_of_nonneg_left hlow (by positivity : (0:ℚ) ≤ m)
  rw [← Nat.totient_eq_mul_prod_factors] at ht
  have hcard : 2*(m.primeFactors.card:ℚ)+1 ≤ p := by exact_mod_cast hsmall
  have hpm : (p:ℚ)+1 ≤ m := by exact_mod_cast hp_lt
  have hpos : (0:ℚ) < p+1 := by positivity
  field_simp [hpos.ne'] at ht
  have htw : (m:ℚ)+1 < 2*m.totient := by
    by_contra! h
    nlinarith [mul_nonneg (sub_nonneg.mpr h) hpos.le,
      mul_nonneg (sub_nonneg.mpr hcard) (Nat.cast_nonneg (α := ℚ) m)]
  exact_mod_cast htw

theorem cycle_of_card_eq_25 (F : Type*) [Field F] [Fintype F] (hq : Fintype.card F = 25) :
    ∃ a : Fin 24 ≃ Fˣ, ∀ i : Fin 24, IsPrimitiveRoot
      ((a i : F) * (a ⟨(i.val+1)%24, Nat.mod_lt _ (by decide)⟩ : F) - 1) 24 := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  have : CharP F 5 := charP_of_card_eq_prime_pow (p := 5) (f := 2) hq
  have h5 : (5 : F) = 0 := CharP.cast_eq_zero F 5
  obtain ⟨v, hv⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  rw [Nat.card_units, Nat.card_eq_fintype_card, hq] at hv
  let z : F := ↑(v^8)
  have hz : IsPrimitiveRoot z 3 := by
    apply IsPrimitiveRoot.iff_orderOf.mpr
    change orderOf (↑(v^8) : F) = 3
    rw [orderOf_units, orderOf_pow, hv]
    decide
  have hquad : z^2 + z + 1 = 0 := by
    apply (mul_eq_zero.mp (show (z-1)*(z^2+z+1)=0 by linear_combination hz.pow_eq_one)).resolve_left
    exact sub_ne_zero.mpr (hz.ne_one (by decide))
  let t := 2*z-2
  have ht : t^2+t+2=0 := by
    dsimp [t]
    linear_combination 4*hquad - 2*z*h5
  have h3 : t^3=2-t := by linear_combination (t-1)*ht
  have h5' : t^5=-1-t := by
    linear_combination (t^2-1)*h3 + 2*ht - h5
  have h6 : t^6=2 := by
    linear_combination t*h5' - ht
  have h8 : t^8=z := by
    calc
      t^8 = 2*t^2 := by linear_combination t^2*h6
      _ = z := by dsimp [t] at ht ⊢; linear_combination 2*ht - z*h5
  have h12 : t^12 = -1 := by
    linear_combination (t^6+2)*h6 + h5
  have h24 : t^24 = 1 := by linear_combination (t^12-1)*h12
  have hprim : IsPrimitiveRoot t 24 := by
    apply IsPrimitiveRoot.iff_orderOf.mpr
    have hd := orderOf_dvd_of_pow_eq_one h24
    have h8' : ¬ orderOf t ∣ 8 := by
      rw [orderOf_dvd_iff_pow_eq_one, h8]
      exact hz.ne_one (by decide)
    have h12' : ¬ orderOf t ∣ 12 := by
      rw [orderOf_dvd_iff_pow_eq_one, h12]
      intro h
      have : (1:F)=0 := by linear_combination h5 + 2*h
      exact one_ne_zero this
    have hl := Nat.le_of_dvd (by decide : 0 < 24) hd
    have rule : ∀ d : Fin 25, d.val ∣ 24 → ¬ d.val ∣ 8 → ¬ d.val ∣ 12 → d.val = 24 := by decide
    exact rule ⟨orderOf t, Nat.lt_succ_of_le hl⟩ hd h8' h12'
  have ht0 := hprim.ne_zero (by decide : 24 ≠ 0)
  let u := Units.mk0 t ht0
  let b : Fin 24 → Fin 24 := ![0,8,1,7,6,2,11,22,10,3,5,4,9,23,14,19,18,15,17,16,21,12,20,13]
  have inj : Function.Injective b := by decide +kernel
  let f (i : Fin 24) : Fˣ := u^(b i).val
  have hu : orderOf u = 24 := orderOf_units.symm.trans hprim.eq_orderOf.symm
  have finj : Function.Injective f := by
    intro i j he
    apply inj
    apply Fin.ext
    exact pow_injOn_Iio_orderOf (x := u) (show (b i).val < orderOf u by rw [hu]; exact (b i).isLt) (show (b j).val < orderOf u by rw [hu]; exact (b j).isLt) he
  have hc : Fintype.card (Fin 24) = Fintype.card Fˣ := by simp [Fintype.card_units, hq]
  let a := Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).2 ⟨finj,hc⟩)
  have hedges : ∀ i : Fin 24,
      let s := ((b i).val + (b ⟨(i.val+1)%24, Nat.mod_lt _ (by decide)⟩).val)%24
      s = 8 ∨ s = 9 ∨ s = 13 := by decide +kernel
  refine ⟨a, fun i => ?_⟩
  let j : Fin 24 := ⟨(i.val+1)%24, Nat.mod_lt _ (by decide)⟩
  change IsPrimitiveRoot (t^(b i).val * t^(b j).val - 1) 24
  rw [← pow_add, ← pow_mod_orderOf, ← hprim.eq_orderOf]
  have he := hedges i
  change _ % 24 = 8 ∨ _ % 24 = 9 ∨ _ % 24 = 13 at he
  rcases he with he | he | he
  · rw [show ((b i).val+(b j).val)%24 = 8 from he]
    have h19 : t^19 = 8*t := by linear_combination t*(t^12+2*t^6+4)*h6
    have hh : t^8-1=t^19 := by
      rw [h8,h19]
      dsimp [t]
      linear_combination (3-3*z)*h5
    rw [hh]
    exact hprim.pow_of_coprime 19 (by decide)
  · rw [show ((b i).val+(b j).val)%24 = 9 from he]
    have hh : t^9-1=t^11 := by
      linear_combination (t^3-t^5)*h6 + 2*h3 - 2*h5' + h5
    rw [hh]
    exact hprim.pow_of_coprime 11 (by decide)
  · rw [show ((b i).val+(b j).val)%24 = 13 from he]
    have hh : t^13-1=t^5 := by linear_combination t*h12 - h5'
    rw [hh]
    exact hprim.pow_of_coprime 5 (by decide)

private theorem transferCycle
    (solve : ∀ (K : Type) [Field K] [Fintype K] (m : ℕ) (hm : 6 < m),
      Fintype.card K = m+1 → ∃ a : Fin m ≃ Kˣ, ∀ i : Fin m,
        IsPrimitiveRoot ((a i : K)*(a ⟨(i.val+1)%m, Nat.mod_lt _ (by omega)⟩ : K)-1) m)
    (F : Type*) [Field F] [Fintype F] (m : ℕ) (hm : 6 < m) (hc : Fintype.card F = m+1) :
    ∃ a : Fin m ≃ Fˣ, ∀ i : Fin m,
        IsPrimitiveRoot ((a i : F)*(a ⟨(i.val+1)%m, Nat.mod_lt _ (by omega)⟩ : F)-1) m := by
  classical
  let K := Shrink.{0} F
  let E : K ≃+* F := Shrink.ringEquiv.{0,_} F
  let : Fintype K := Fintype.ofEquiv F E.symm.toEquiv
  obtain ⟨a,ha⟩ := solve K m hm ((Fintype.card_congr E.toEquiv).trans hc)
  let u := Units.mapEquiv E.toMulEquiv
  refine ⟨a.trans u.toEquiv, fun i => ?_⟩
  have he := (ha i).map_of_injective E.injective
  change IsPrimitiveRoot (E _ * E _ - 1) m
  simpa only [map_sub, map_mul, map_one] using he

/-- In odd characteristic the starting factor 1+g must be a square for the
chosen orientation of the generator. The order-25 field is handled explicitly. -/
def H1 : Prop := ∀ (F : Type) [Field F] [Fintype F],
    let q := Fintype.card F
    let m := q-1
    let e := fun i : ℕ => if i % 2 = 0 then i / 2 else m-1-i/2
    7 < q → q % 2 = 1 → q ≠ 25 →
    ∃ (g : Fˣ) (k : ℕ), orderOf g = m ∧ IsSquare (1+(g:F)) ∧ k+1 < m ∧
      IsPrimitiveRoot ((1+(g:F))*(g:F)^(m/2+e k)-1) m ∧
      IsPrimitiveRoot ((1+(g:F))*(g:F)^e (k+1)-1) m

/-- The sparse even-characteristic case. Squaring permutes the units here. -/
def H2 : Prop := ∀ (F : Type) [Field F] [Fintype F],
    let q := Fintype.card F
    let m := q-1
    let e := fun i : ℕ => if i % 2 = 0 then i / 2 else m-1-i/2
    7 < q → q % 2 = 0 → 2*m.totient ≤ q →
    (∀ p : ℕ, p.Prime → q ≠ 2^p) →
    ∃ (g : Fˣ) (k : ℕ), orderOf g = m ∧ k+1 < m ∧
      IsPrimitiveRoot ((1+(g:F))*(g:F)^(m/2+e k)-1) m ∧
      IsPrimitiveRoot ((1+(g:F))*(g:F)^e (k+1)-1) m

theorem main : H1 → H2 → type_of% @OeisA229232.conjecture_4 := by
  intro oddCase evenCase K _ _ hK
  apply transferCycle ?_ K (Fintype.card K-1) (by omega) (by omega)
  intro F _ _ n hn hc
  have hq : 7 < Fintype.card F := by omega
  obtain rfl : n = Fintype.card F - 1 := by omega
  classical
  let q := Fintype.card F
  let m := q-1
  have hqm : m+1 = q := by dsimp [m,q]; omega
  have hm : 2 < m := by dsimp [m,q]; omega
  let e := fun i : ℕ => if i % 2 = 0 then i / 2 else m-1-i/2
  let R := fun x y : Fˣ => IsPrimitiveRoot ((x:F)*(y:F)-1) m
  have sym : ∀ {u v}, R u v → R v u := by intro u v; simp [R,mul_comm]
  change ∃ a : Fin m ≃ Fˣ, ∀ i, R (a i) (a ⟨(i.val+1)%m, _⟩)
  by_cases h25 : q = 25
  · have hh : m = 24 := by omega
    have small (t : ℕ) (ht : t = 24) :
        ∃ a : Fin t ≃ Fˣ, ∀ i : Fin t, IsPrimitiveRoot
          ((a i : F) * (a ⟨(i.val + 1) % t, Nat.mod_lt _ (by omega)⟩ : F) - 1) t := by
      subst t
      exact cycle_of_card_eq_25 F h25
    exact small m hh
  by_cases hd : m+1 < 2*m.totient
  · exact cycle_of_totient F hq (show q < 2*m.totient by omega)
  have witness : ∃ (g h : Fˣ) (k : ℕ), orderOf g = m ∧ (h:F)^2 = 1+(g:F) ∧
      k+1 < m ∧ IsPrimitiveRoot ((1+(g:F))*(g:F)^(m/2+e k)-1) m ∧
      IsPrimitiveRoot ((1+(g:F))*(g:F)^e (k+1)-1) m := by
    have hn (g : Fˣ) (hg : orderOf g = m) : 1+(g:F) ≠ 0 := by
      intro he
      have heq : (g:F) = -1 := by linear_combination he
      have hp : g^2 = 1 := by apply Units.ext; change (g:F)^2 = 1; rw [heq]; ring
      have := orderOf_le_of_pow_eq_one (by decide : 0 < 2) hp
      omega
    by_cases hodd : q % 2 = 1
    · obtain ⟨g,k,hg,⟨x,hx⟩,hk,hl,hr⟩ := oddCase F hq hodd h25
      have hsq : x^2 = 1+(g:F) := by simpa only [pow_two] using hx.symm
      have hx0 : x ≠ 0 := by intro h; apply hn g hg; rw [← hsq,h]; norm_num
      exact ⟨g,Units.mk0 x hx0,k,hg,hsq,hk,hl,hr⟩
    · have heven : q % 2 = 0 := by omega
      have hexc (p : ℕ) (hp : p.Prime) : q ≠ 2^p := by
        intro he
        have hp' : 2 < p := by
          by_contra! hc
          interval_cases p <;> norm_num at he <;> change Fintype.card F = _ at he <;> omega
        have hc := densePrimeDegree p hp hp'
        exact hd (by simpa only [m,he] using hc)
      obtain ⟨g,k,hg,hk,hl,hr⟩ := evenCase F hq heven (show 2*m.totient ≤ q by omega) hexc
      let u := Units.mk0 (1+(g:F)) (hn g hg)
      have hp : u^m = 1 := by
        have hc : Nat.card Fˣ = m := by rw [Nat.card_units, Nat.card_eq_fintype_card]
        rw [← hc]
        exact pow_card_eq_one'
      have hs : (u^((m+1)/2))^2 = u := by
        rw [← pow_mul, show (m+1)/2*2 = m+1 by omega, pow_succ, hp, one_mul]
      exact ⟨g,u^((m+1)/2),k,hg, by simpa [u] using congrArg Units.val hs,hk,hl,hr⟩
  obtain ⟨g,h,k,hg,hh,hk,hl,hr⟩ := witness
  obtain ⟨a,ha,adj⟩ := path F m rfl g h hg hh
  have prod (i j : Fin m) : (a i:F)*(a j:F) = (1+(g:F))*(g:F)^(e i + e j) := by
    rw [ha, ha, ← hh]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, pow_add, e]
    ring
  have hlast : e (m-1) = m/2 := by dsimp [e]; split <;> omega
  have hl' : R (a ⟨m-1, by omega⟩) (a ⟨k, by omega⟩) := by
    simpa only [R,prod,hlast] using hl
  have hr' : R (a ⟨0, by omega⟩) (a ⟨k+1,hk⟩) := by
    simpa only [R,prod,show e 0 = 0 from rfl,zero_add] using hr
  exact closePath (by omega) a R sym adj k hk (sym hl') (sym hr')

end OMA.R_OeisA229232_conjecture_4_R1
