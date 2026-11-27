import FormalConjectures.Wikipedia.WilfNumericalSemigroupConjecture

/-!
# Fröberg–Gottlieb–Häggkvist Theorem (Wilf's Conjecture for `embeddingDim S ≤ 3`)

We prove `conductor S ≤ embeddingDim S * sporadicCount S` for any numerical semigroup `S` with
`embeddingDim S ≤ 3`, following Fröberg–Gottlieb–Häggkvist (1987):
1. `conductor S ≤ (PF.card + 1) * sporadicCount S`, where `PF` is the set of pseudo-Frobenius
   numbers of `S`, obtained by injecting every gap below `conductor S` into `PF × (S ∩ [0, c))`.
2. For `embeddingDim S = 1`, `1 ∈ S` so `conductor S = 0`.
3. For `embeddingDim S = 2`, the Apéry set over one generator is an interval, giving `PF.card ≤ 1`.
4. For `embeddingDim S = 3`, the minimal representations in the Apéry set over one generator form a
   2D L-shape with at most two outer corners, giving `PF.card ≤ 2`.
-/

namespace OMA.WilfE3

open AddSubmonoid WilfNumericalSemigroupConjecture

/-- Minimal positive generators of `S`. Its `Set.ncard` is `S.embeddingDim`. -/
def MinGen (S : AddSubmonoid ℕ) : Set ℕ :=
  {x : ℕ | 0 < x ∧ x ∈ S ∧ ¬ ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a ∈ S ∧ b ∈ S ∧ x = a + b}

lemma embeddingDim_eq_ncard_minGen (S : AddSubmonoid ℕ) :
    S.embeddingDim = (MinGen S).ncard := rfl

lemma mul_mem {S : AddSubmonoid ℕ} {a : ℕ} (ha : a ∈ S) (k : ℕ) : k * a ∈ S := by
  simpa [smul_eq_mul] using S.nsmul_mem ha k

lemma exists_mem_minGen {S : AddSubmonoid ℕ} (hS : S.IsNumericalSemigroup) :
    ∃ a, a ∈ MinGen S := by
  have hex : ∃ x, 0 < x ∧ x ∈ S :=
    ⟨S.conductor + 1, Nat.succ_pos _, hS.mem_of_conductor_le (Nat.le_succ _)⟩
  classical
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩
  rintro ⟨u, v, hu, hv, huS, hvS, huv⟩
  have hlt : u < Nat.find hex := by omega
  exact Nat.find_min hex hlt ⟨hu, huS⟩

lemma minGen_finite {S : AddSubmonoid ℕ} (hS : S.IsNumericalSemigroup) : (MinGen S).Finite := by
  let m := S.conductor + 1
  have hm0 : 0 < m := Nat.succ_pos _
  have hmS : m ∈ S := hS.mem_of_conductor_le (Nat.le_succ _)
  have hinj : Set.InjOn (· % m) (MinGen S) := by
    intro x hx y hy hmod
    rcases lt_trichotomy x y with hxy | rfl | hyx
    · have hdv : m ∣ y - x := (Nat.modEq_iff_dvd' hxy.le).mp (show x ≡ y [MOD m] from hmod)
      obtain ⟨k, hk⟩ := hdv
      have hkS : y - x ∈ S := by
        rw [hk, mul_comm]
        exact mul_mem hmS k
      exact absurd ⟨x, y - x, hx.1, by omega, hx.2.1, hkS, by omega⟩ hy.2.2
    · rfl
    · have hdv : m ∣ x - y := (Nat.modEq_iff_dvd' hyx.le).mp (show y ≡ x [MOD m] from hmod.symm)
      obtain ⟨k, hk⟩ := hdv
      have hkS : x - y ∈ S := by
        rw [hk, mul_comm]
        exact mul_mem hmS k
      exact absurd ⟨y, x - y, hy.1, by omega, hy.2.1, hkS, by omega⟩ hx.2.2
  refine Set.Finite.of_finite_image ((Finset.finite_toSet (Finset.range m)).subset ?_) hinj
  rintro _ ⟨x, -, rfl⟩
  simp only [Finset.coe_range, Set.mem_Iio]
  exact Nat.mod_lt x hm0

lemma one_le_embeddingDim {S : AddSubmonoid ℕ} (hS : S.IsNumericalSemigroup) :
    1 ≤ S.embeddingDim := by
  rw [embeddingDim_eq_ncard_minGen]
  exact Set.ncard_pos (minGen_finite hS) |>.mpr (exists_mem_minGen hS)

lemma gen_one {S : AddSubmonoid ℕ} {a : ℕ} (hsub : MinGen S ⊆ {a}) :
    ∀ s : ℕ, s ∈ S → a ∣ s := by
  intro s
  induction s using Nat.strong_induction_on with
  | h s ih =>
    intro hsS
    rcases Nat.eq_zero_or_pos s with rfl | hspos
    · exact dvd_zero a
    · by_cases hsmin : s ∈ MinGen S
      · rw [Set.mem_singleton_iff.mp (hsub hsmin)]
      · have hex : ∃ u v : ℕ, 0 < u ∧ 0 < v ∧ u ∈ S ∧ v ∈ S ∧ s = u + v := by
          by_contra hno
          exact hsmin ⟨hspos, hsS, hno⟩
        obtain ⟨u, v, hu, hv, huS, hvS, huv⟩ := hex
        rw [huv]
        exact Nat.dvd_add (ih u (by omega) huS) (ih v (by omega) hvS)

lemma gen_two {S : AddSubmonoid ℕ} {a b : ℕ} (hsub : MinGen S ⊆ {a, b}) :
    ∀ s : ℕ, s ∈ S → ∃ x y : ℕ, s = x * a + y * b := by
  intro s
  induction s using Nat.strong_induction_on with
  | h s ih =>
    intro hsS
    rcases Nat.eq_zero_or_pos s with rfl | hspos
    · exact ⟨0, 0, by simp⟩
    · by_cases hsmin : s ∈ MinGen S
      · rcases hsub hsmin with rfl | rfl
        · exact ⟨1, 0, by ring⟩
        · exact ⟨0, 1, by ring⟩
      · have hex : ∃ u v : ℕ, 0 < u ∧ 0 < v ∧ u ∈ S ∧ v ∈ S ∧ s = u + v := by
          by_contra hno
          exact hsmin ⟨hspos, hsS, hno⟩
        obtain ⟨u, v, hu, hv, huS, hvS, huv⟩ := hex
        obtain ⟨x₁, y₁, hx₁⟩ := ih u (by omega) huS
        obtain ⟨x₂, y₂, hx₂⟩ := ih v (by omega) hvS
        exact ⟨x₁ + x₂, y₁ + y₂, by rw [huv, hx₁, hx₂]; ring⟩

lemma gen_three {S : AddSubmonoid ℕ} {a b d : ℕ} (hsub : MinGen S ⊆ {a, b, d}) :
    ∀ s : ℕ, s ∈ S → ∃ x y z : ℕ, s = x * a + y * b + z * d := by
  intro s
  induction s using Nat.strong_induction_on with
  | h s ih =>
    intro hsS
    rcases Nat.eq_zero_or_pos s with rfl | hspos
    · exact ⟨0, 0, 0, by simp⟩
    · by_cases hsmin : s ∈ MinGen S
      · rcases hsub hsmin with rfl | rfl | rfl
        · exact ⟨1, 0, 0, by ring⟩
        · exact ⟨0, 1, 0, by ring⟩
        · exact ⟨0, 0, 1, by ring⟩
      · have hex : ∃ u v : ℕ, 0 < u ∧ 0 < v ∧ u ∈ S ∧ v ∈ S ∧ s = u + v := by
          by_contra hno
          exact hsmin ⟨hspos, hsS, hno⟩
        obtain ⟨u, v, hu, hv, huS, hvS, huv⟩ := hex
        obtain ⟨x₁, y₁, z₁, hx₁⟩ := ih u (by omega) huS
        obtain ⟨x₂, y₂, z₂, hx₂⟩ := ih v (by omega) hvS
        exact ⟨x₁ + x₂, y₁ + y₂, z₁ + z₂, by rw [huv, hx₁, hx₂]; ring⟩

/-- Pseudo-Frobenius numbers of `S` as a `Finset ℕ`. -/
noncomputable def PF (S : AddSubmonoid ℕ) : Finset ℕ :=
  open scoped Classical in
  (Finset.range S.conductor).filter (fun f => f ∉ S ∧ ∀ s ∈ S, 0 < s → f + s ∈ S)

lemma mem_PF_iff {S : AddSubmonoid ℕ} {f : ℕ} :
    f ∈ PF S ↔ f < S.conductor ∧ f ∉ S ∧ ∀ s ∈ S, 0 < s → f + s ∈ S := by
  classical
  unfold PF
  rw [Finset.mem_filter, Finset.mem_range]

lemma exists_pf_of_gap {S : AddSubmonoid ℕ} (hS : S.IsNumericalSemigroup) :
    ∀ k : ℕ, ∀ g : ℕ, g < S.conductor → g ∉ S → S.conductor - g ≤ k →
      ∃ f ∈ PF S, g ≤ f ∧ f - g ∈ S := by
  intro k
  induction k with
  | zero =>
    intro g hg _ hk
    omega
  | succ k ih =>
    intro g hg hgS hk
    by_cases hpf : ∀ s ∈ S, 0 < s → g + s ∈ S
    · refine ⟨g, mem_PF_iff.mpr ⟨hg, hgS, hpf⟩, le_rfl, ?_⟩
      rw [Nat.sub_self]
      exact S.zero_mem
    · push Not at hpf
      obtain ⟨s, hsS, hspos, hgsS⟩ := hpf
      have hlt : g + s < S.conductor := by
        by_contra hge
        exact hgsS (hS.mem_of_conductor_le (by omega))
      obtain ⟨f, hfPF, hle, hsub⟩ := ih (g + s) hlt hgsS (by omega)
      refine ⟨f, hfPF, by omega, ?_⟩
      have heq : f - g = (f - (g + s)) + s := by omega
      rw [heq]
      exact S.add_mem hsub hsS

lemma conductor_le_succ_pf_mul_sporadic {S : AddSubmonoid ℕ} (hS : S.IsNumericalSemigroup) :
    S.conductor ≤ ((PF S).card + 1) * sporadicCount S := by
  classical
  let G : Finset ℕ := (Finset.range S.conductor).filter (fun x => x ∉ S)
  let N : Finset ℕ := (Finset.range S.conductor).filter (fun x => x ∈ S)
  have hNcard : N.card = sporadicCount S := by
    unfold sporadicCount
    congr 1
  have hpart : N ∪ G = Finset.range S.conductor := by
    ext x
    simp only [N, G, Finset.mem_union, Finset.mem_filter, Finset.mem_range]
    tauto
  have hdisj : Disjoint N G := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [N, G, Finset.mem_filter] at hx1 hx2
    exact hx2.2 hx1.2
  have hsum : N.card + G.card = S.conductor := by
    rw [← Finset.card_union_of_disjoint hdisj, hpart, Finset.card_range]
  let pick : ℕ → ℕ := fun g =>
    if hg : g < S.conductor ∧ g ∉ S then
      Classical.choose (exists_pf_of_gap hS (S.conductor - g) g hg.1 hg.2 le_rfl)
    else 0
  have hpick : ∀ g ∈ G, pick g ∈ PF S ∧ g ≤ pick g ∧ pick g - g ∈ S := by
    intro g hgG
    have hg : g < S.conductor ∧ g ∉ S := by
      simpa [G, Finset.mem_filter, Finset.mem_range] using hgG
    simpa [pick, hg] using
      Classical.choose_spec (exists_pf_of_gap hS (S.conductor - g) g hg.1 hg.2 le_rfl)
  let phi : ℕ → ℕ × ℕ := fun g => (pick g, pick g - g)
  have hinj : Set.InjOn phi (G : Set ℕ) := by
    intro g₁ hg₁ g₂ hg₂ hphi
    have h1 := (hpick g₁ hg₁).2.1
    have h2 := (hpick g₂ hg₂).2.1
    have hf : pick g₁ = pick g₂ := congrArg Prod.fst hphi
    have hd : pick g₁ - g₁ = pick g₂ - g₂ := congrArg Prod.snd hphi
    omega
  have himg : ∀ g ∈ G, phi g ∈ PF S ×ˢ N := by
    intro g hgG
    obtain ⟨hfPF, hle, hsub⟩ := hpick g hgG
    have hfc : pick g < S.conductor := (mem_PF_iff.mp hfPF).1
    rw [Finset.mem_product]
    refine ⟨hfPF, ?_⟩
    simp only [N, Finset.mem_filter, Finset.mem_range]
    change pick g - g < S.conductor ∧ pick g - g ∈ S
    exact ⟨by omega, hsub⟩
  have hGcard : G.card ≤ (PF S).card * N.card := by
    calc G.card ≤ (PF S ×ˢ N).card := Finset.card_le_card_of_injOn phi himg hinj
      _ = (PF S).card * N.card := Finset.card_product (PF S) N
  rw [← hNcard, ← hsum]
  nlinarith

/- ## Case `e = 1` -/

lemma conductor_eq_zero_of_embeddingDim_eq_one {S : AddSubmonoid ℕ}
    (hS : S.IsNumericalSemigroup) (h1 : S.embeddingDim = 1) : S.conductor = 0 := by
  have hfin : (MinGen S).Finite := minGen_finite hS
  have hcard : hfin.toFinset.card = 1 := by
    rw [← Set.ncard_eq_toFinset_card _ hfin]
    exact h1
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
  have haMin : a ∈ MinGen S := (hfin.mem_toFinset).mp (ha ▸ Finset.mem_singleton_self a)
  have hsub : MinGen S ⊆ {a} := by
    intro x hx
    have hx' : x ∈ hfin.toFinset := (hfin.mem_toFinset).mpr hx
    rw [ha] at hx'
    exact Finset.mem_singleton.mp hx'
  have hc0 : S.conductor ∈ S := hS.mem_of_conductor_le le_rfl
  have hc1 : S.conductor + 1 ∈ S := hS.mem_of_conductor_le (Nat.le_succ _)
  have hd0 : a ∣ S.conductor := gen_one hsub _ hc0
  have hd1 : a ∣ S.conductor + 1 := gen_one hsub _ hc1
  have ha1 : a = 1 := Nat.eq_one_of_dvd_one ((Nat.dvd_add_right hd0).mp hd1)
  have h1S : 1 ∈ S := ha1 ▸ haMin.2.1
  have hall : ∀ m : ℕ, 0 ≤ m → m ∈ S := by
    intro m _
    have := mul_mem h1S m
    simpa using this
  exact Nat.sInf_eq_zero.mpr (Or.inl hall)

/- ## Case `e = 2` -/

lemma mul_sub_left {a x : ℕ} (hx : 0 < x) : a * x - a = (x - 1) * a := by
  cases x with
  | zero => omega
  | succ x' => rw [Nat.add_sub_cancel, Nat.mul_succ, mul_comm, Nat.add_sub_cancel]

lemma succ_mul_sub_add {x a r : ℕ} (hx : 0 < x) : (x * a + r) - a = (x - 1) * a + r := by
  cases x with
  | zero => omega
  | succ x' => rw [Nat.add_sub_cancel, Nat.succ_mul, add_right_comm, Nat.add_sub_cancel]

lemma add_sub_mul {u v c : ℕ} (h : v ≤ u) : v * c + (u - v) * c = u * c := by
  rw [← Nat.add_mul, Nat.add_sub_cancel' h]

lemma sub_mul_add {u v c : ℕ} (h : v ≤ u) : (u - v) * c + v * c = u * c := by
  rw [← Nat.add_mul, Nat.sub_add_cancel h]

lemma pf_card_le_one_of_embeddingDim_eq_two {S : AddSubmonoid ℕ}
    (hS : S.IsNumericalSemigroup) (h2 : S.embeddingDim = 2) : (PF S).card ≤ 1 := by
  have hfin : (MinGen S).Finite := minGen_finite hS
  have hcard : hfin.toFinset.card = 2 := by
    rw [← Set.ncard_eq_toFinset_card _ hfin]
    exact h2
  obtain ⟨a, b, -, hab⟩ := Finset.card_eq_two.mp hcard
  have haMin : a ∈ MinGen S := (hfin.mem_toFinset).mp (hab ▸ Finset.mem_insert_self a {b})
  have hbMin : b ∈ MinGen S :=
    (hfin.mem_toFinset).mp (hab ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self b))
  have ha0 : 0 < a := haMin.1
  have hb0 : 0 < b := hbMin.1
  have haS : a ∈ S := haMin.2.1
  have hbS : b ∈ S := hbMin.2.1
  have hsub : MinGen S ⊆ {a, b} := by
    intro x hx
    have hx' : x ∈ hfin.toFinset := (hfin.mem_toFinset).mpr hx
    rw [hab] at hx'
    simpa using hx'
  have hgen := gen_two hsub
  let InAp : ℕ → Prop := fun w => w ∈ S ∧ (a ≤ w → w - a ∉ S)
  have hAp0 : InAp 0 := ⟨S.zero_mem, fun h => absurd h (by omega)⟩
  have hnot : ¬ InAp (a * b) := by
    intro ⟨_, hsubS⟩
    have hle : a ≤ a * b := Nat.le_mul_of_pos_right a hb0
    have hmem : a * b - a ∈ S := by
      rw [mul_sub_left hb0]
      exact mul_mem haS (b - 1)
    exact hsubS hle hmem
  classical
  have hex : ∃ y : ℕ, ¬ InAp (y * b) := ⟨a, hnot⟩
  let Y := Nat.find hex
  have hYnot : ¬ InAp (Y * b) := Nat.find_spec hex
  have hYpos : 1 ≤ Y := by
    by_contra hlt
    have hY0 : Y = 0 := by omega
    rw [hY0, zero_mul] at hYnot
    exact hYnot hAp0
  have hdown : ∀ {y' y : ℕ}, y' ≤ y → InAp (y * b) → InAp (y' * b) := by
    intro y' y hy' ⟨hyS, hyN⟩
    refine ⟨mul_mem hbS y', fun hle hsubS => ?_⟩
    have hyle : y' * b ≤ y * b := Nat.mul_le_mul_right b hy'
    have hale : a ≤ y * b := le_trans hle hyle
    apply hyN hale
    have heq : y * b - a = (y' * b - a) + (y - y') * b := by
      rw [← add_sub_mul hy']
      omega
    rw [heq]
    exact S.add_mem hsubS (mul_mem hbS (y - y'))
  have hPF_eq : ∀ f ∈ PF S, f + a = (Y - 1) * b := by
    intro f hf
    have hf' := mem_PF_iff.mp hf
    have hfa_Ap : InAp (f + a) := by
      refine ⟨hf'.2.2 a haS ha0, fun _ hsubS => ?_⟩
      apply hf'.2.1
      simpa using hsubS
    obtain ⟨x, y, hxy⟩ := hgen (f + a) hfa_Ap.1
    have hx0 : x = 0 := by
      by_contra hxpos
      apply hfa_Ap.2 (by omega)
      have heq : (f + a) - a = (x - 1) * a + y * b := by
        rw [hxy]
        exact succ_mul_sub_add (Nat.pos_of_ne_zero hxpos)
      rw [heq]
      exact S.add_mem (mul_mem haS (x - 1)) (mul_mem hbS y)
    rw [hx0, zero_mul, zero_add] at hxy
    have hy_Ap : InAp (y * b) := hxy ▸ hfa_Ap
    have hy_lt : y < Y := by
      by_contra hge
      exact hYnot (hdown (by omega) hy_Ap)
    have hnext_not : ¬ InAp ((y + 1) * b) := by
      intro ⟨_, hsubS⟩
      apply hsubS (by nlinarith)
      have heq : (y + 1) * b - a = f + b := by
        rw [Nat.add_mul, one_mul, ← hxy]
        omega
      rw [heq]
      exact hf'.2.2 b hbS hb0
    have hy_ge : Y ≤ y + 1 := by
      by_contra hlt
      exact hnext_not (Nat.find_min hex (by omega) |> not_not.mp)
    have hy_eq : y = Y - 1 := by omega
    rw [hxy, hy_eq]
  have hinj : Set.InjOn (fun f => f + a) (PF S : Set ℕ) :=
    fun _ _ _ _ h => Nat.add_right_cancel h
  have himg : ∀ f ∈ PF S, f + a ∈ ({(Y - 1) * b} : Finset ℕ) := by
    intro f hf
    rw [Finset.mem_singleton]
    exact hPF_eq f hf
  calc (PF S).card ≤ ({(Y - 1) * b} : Finset ℕ).card := Finset.card_le_card_of_injOn _ himg hinj
    _ = 1 := Finset.card_singleton _

/- ## Case `e = 3`: 2D L-shape Apéry theorem -/

lemma modEq_add_right_cancel {a c x y : ℕ} (h : x + c ≡ y + c [MOD a]) : x ≡ y [MOD a] := by
  rw [Nat.modEq_iff_dvd] at h ⊢
  simpa using h

lemma modEq_add_left_cancel {a c x y : ℕ} (h : c + x ≡ c + y [MOD a]) : x ≡ y [MOD a] := by
  rw [add_comm c x, add_comm c y] at h
  exact modEq_add_right_cancel h

lemma exists_mul_of_modEq_lt {a u v : ℕ} (_ha : 0 < a) (huv : u < v) (hm : u ≡ v [MOD a]) :
    ∃ k : ℕ, 1 ≤ k ∧ v = u + k * a := by
  change u % a = v % a at hm
  have h1 := Nat.div_add_mod u a
  have h2 := Nat.div_add_mod v a
  have hdiv : u / a < v / a := by
    have : a * (u / a) < a * (v / a) := by omega
    exact Nat.lt_of_mul_lt_mul_left this
  refine ⟨v / a - u / a, by omega, ?_⟩
  have hdiv_eq : v / a = u / a + (v / a - u / a) := by omega
  rw [hdiv_eq, mul_add] at h2
  nlinarith

lemma pf_card_le_two_of_embeddingDim_eq_three {S : AddSubmonoid ℕ}
    (hS : S.IsNumericalSemigroup) (h3 : S.embeddingDim = 3) : (PF S).card ≤ 2 := by
  have hfin : (MinGen S).Finite := minGen_finite hS
  have hcard : hfin.toFinset.card = 3 := by
    rw [← Set.ncard_eq_toFinset_card _ hfin]
    exact h3
  obtain ⟨a, b, d, -, -, -, habd⟩ := Finset.card_eq_three.mp hcard
  have haMin : a ∈ MinGen S := (hfin.mem_toFinset).mp (habd ▸ by simp)
  have hbMin : b ∈ MinGen S := (hfin.mem_toFinset).mp (habd ▸ by simp)
  have hdMin : d ∈ MinGen S := (hfin.mem_toFinset).mp (habd ▸ by simp)
  have ha0 : 0 < a := haMin.1
  have hb0 : 0 < b := hbMin.1
  have hd0 : 0 < d := hdMin.1
  have haS : a ∈ S := haMin.2.1
  have hbS : b ∈ S := hbMin.2.1
  have hdS : d ∈ S := hdMin.2.1
  have hsub : MinGen S ⊆ {a, b, d} := by
    intro x hx
    have hx' : x ∈ hfin.toFinset := (hfin.mem_toFinset).mpr hx
    rw [habd] at hx'
    simpa using hx'
  have hgen := gen_three hsub
  let InAp : ℕ → Prop := fun w => w ∈ S ∧ (a ≤ w → w - a ∉ S)
  have hAp0 : InAp 0 := ⟨S.zero_mem, fun h => absurd h (by omega)⟩
  have inAp_unique : ∀ {w₁ w₂ : ℕ}, InAp w₁ → InAp w₂ → w₁ ≡ w₂ [MOD a] → w₁ = w₂ := by
    intro w₁ w₂ h1 h2 hm
    rcases lt_trichotomy w₁ w₂ with hlt | rfl | hgt
    · obtain ⟨k, hk1, hweq⟩ := exists_mul_of_modEq_lt ha0 hlt hm
      exfalso
      apply h2.2 (by nlinarith)
      have heq : w₂ - a = w₁ + (k - 1) * a := by
        rw [hweq, add_comm w₁ (k * a), succ_mul_sub_add hk1, add_comm]
      rw [heq]
      exact S.add_mem h1.1 (mul_mem haS (k - 1))
    · rfl
    · obtain ⟨k, hk1, hweq⟩ := exists_mul_of_modEq_lt ha0 hgt hm.symm
      exfalso
      apply h1.2 (by nlinarith)
      have heq : w₁ - a = w₂ + (k - 1) * a := by
        rw [hweq, add_comm w₂ (k * a), succ_mul_sub_add hk1, add_comm]
      rw [heq]
      exact S.add_mem h2.1 (mul_mem haS (k - 1))
  classical
  have inAp_exists : ∀ m : ℕ, ∃ w : ℕ, InAp w ∧ w ≡ m [MOD a] := by
    intro m
    have hex : ∃ w : ℕ, w ∈ S ∧ w ≡ m [MOD a] := by
      refine ⟨m + S.conductor * a, hS.mem_of_conductor_le (by nlinarith), ?_⟩
      change (m + S.conductor * a) % a = m % a
      exact Nat.add_mul_mod_self_right m S.conductor a
    let w := Nat.find hex
    have hw := Nat.find_spec hex
    refine ⟨w, ⟨hw.1, fun hle hsubS => ?_⟩, hw.2⟩
    have hlt : w - a < w := by omega
    have hm : w - a ≡ m [MOD a] := by
      have hsubmod : w - a ≡ w [MOD a] := by
        change (w - a) % a = w % a
        have heq : w = (w - a) + 1 * a := by omega
        conv_rhs => rw [heq]
        rw [Nat.add_mul_mod_self_right]
      exact hsubmod.trans hw.2
    exact Nat.find_min hex hlt ⟨hsubS, hm⟩
  have inAp_rep : ∀ {w : ℕ}, InAp w → ∃ y z : ℕ, y * b + z * d = w := by
    intro w hw
    obtain ⟨x, y, z, hxyz⟩ := hgen w hw.1
    have hx0 : x = 0 := by
      by_contra hxpos
      have hx1 : 1 ≤ x := Nat.pos_of_ne_zero hxpos
      apply hw.2 (by nlinarith)
      have heq : w - a = (x - 1) * a + y * b + z * d := by
        rw [hxyz, add_assoc (x * a), succ_mul_sub_add hx1, add_assoc]
      rw [heq]
      exact S.add_mem (S.add_mem (mul_mem haS (x - 1)) (mul_mem hbS y)) (mul_mem hdS z)
    rw [hx0, zero_mul, zero_add] at hxyz
    exact ⟨y, z, hxyz.symm⟩
  let InL : ℕ → ℕ → Prop := fun y z =>
    InAp (y * b + z * d) ∧ ∀ y' z' : ℕ, y' * b + z' * d = y * b + z * d → z ≤ z'
  have hL00 : InL 0 0 := by
    refine ⟨by simpa using hAp0, fun y' z' _ => Nat.zero_le z'⟩
  have inL_inj : ∀ {y₁ z₁ y₂ z₂ : ℕ}, InL y₁ z₁ → InL y₂ z₂ →
      y₁ * b + z₁ * d ≡ y₂ * b + z₂ * d [MOD a] → y₁ = y₂ ∧ z₁ = z₂ := by
    intro y₁ z₁ y₂ z₂ h1 h2 hm
    have heq := inAp_unique h1.1 h2.1 hm
    have hz12 : z₁ ≤ z₂ := h1.2 y₂ z₂ heq.symm
    have hz21 : z₂ ≤ z₁ := h2.2 y₁ z₁ heq
    have hz : z₁ = z₂ := le_antisymm hz12 hz21
    subst hz
    have hyb : y₁ * b = y₂ * b := by omega
    exact ⟨Nat.eq_of_mul_eq_mul_right hb0 hyb, rfl⟩
  have inL_of_inAp : ∀ {w : ℕ}, InAp w → ∃ y z : ℕ, InL y z ∧ y * b + z * d = w := by
    intro w hw
    have hex : ∃ z : ℕ, ∃ y : ℕ, y * b + z * d = w := by
      obtain ⟨y, z, hyz⟩ := inAp_rep hw
      exact ⟨z, y, hyz⟩
    let z := Nat.find hex
    have hz := Nat.find_spec hex
    obtain ⟨y, hyz⟩ := hz
    refine ⟨y, z, ⟨hyz.symm ▸ hw, fun y' z' h' => ?_⟩, hyz⟩
    by_contra hlt
    exact Nat.find_min hex (by omega) ⟨y', h'.trans hyz⟩
  have inL_exists_mod : ∀ m : ℕ, ∃ y z : ℕ, InL y z ∧ y * b + z * d ≡ m [MOD a] := by
    intro m
    obtain ⟨w, hwAp, hwm⟩ := inAp_exists m
    obtain ⟨y, z, hyzL, rfl⟩ := inL_of_inAp hwAp
    exact ⟨y, z, hyzL, hwm⟩
  have inL_down : ∀ {y z y' z' : ℕ}, InL y z → y' ≤ y → z' ≤ z → InL y' z' := by
    intro y z y' z' ⟨hAp, hmin⟩ hy hz
    refine ⟨?_, ?_⟩
    · refine ⟨S.add_mem (mul_mem hbS y') (mul_mem hdS z'), fun hle hsubS => ?_⟩
      apply hAp.2 (by nlinarith)
      have hsum_eq : y * b + z * d = (y' * b + z' * d) + ((y - y') * b + (z - z') * d) := by
        rw [← add_sub_mul hy, ← add_sub_mul hz]; ring
      have heq : y * b + z * d - a = (y' * b + z' * d - a) + ((y - y') * b + (z - z') * d) := by
        rw [hsum_eq]; omega
      rw [heq]
      exact S.add_mem hsubS (S.add_mem (mul_mem hbS (y - y')) (mul_mem hdS (z - z')))
    · intro y'' z'' h''
      by_contra hlt
      have heq2 : (y'' + (y - y')) * b + (z'' + (z - z')) * d = y * b + z * d := by
        calc (y'' + (y - y')) * b + (z'' + (z - z')) * d
          _ = (y'' * b + z'' * d) + ((y - y') * b + (z - z') * d) := by ring
          _ = (y' * b + z' * d) + ((y - y') * b + (z - z') * d) := by rw [h'']
          _ = y * b + z * d := by rw [← add_sub_mul hy, ← add_sub_mul hz]; ring
      have hbad := hmin (y'' + (y - y')) (z'' + (z - z')) heq2
      omega
  have not_inL_witness : ∀ {y z : ℕ}, ¬ InL y z →
      ∃ y' z' : ℕ, InL y' z' ∧ y' * b + z' * d ≡ y * b + z * d [MOD a] ∧
        (y' * b + z' * d < y * b + z * d ∨ (y' * b + z' * d = y * b + z * d ∧ z' < z)) := by
    intro y z hnotL
    obtain ⟨y', z', hL', hm'⟩ := inL_exists_mod (y * b + z * d)
    have hle : y' * b + z' * d ≤ y * b + z * d := by
      by_contra hlt
      obtain ⟨k, hk1, hweq⟩ := exists_mul_of_modEq_lt ha0 (by omega) hm'.symm
      apply hL'.1.2 (by nlinarith)
      have heq : y' * b + z' * d - a = (y * b + z * d) + (k - 1) * a := by
        rw [hweq, add_comm (y * b + z * d) (k * a), succ_mul_sub_add hk1, add_comm]
      rw [heq]
      exact S.add_mem (S.add_mem (mul_mem hbS y) (mul_mem hdS z)) (mul_mem haS (k - 1))
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact ⟨y', z', hL', hm', Or.inl hlt⟩
    · refine ⟨y', z', hL', hm', Or.inr ⟨heq, ?_⟩⟩
      have hAp_yz : InAp (y * b + z * d) := heq ▸ hL'.1
      have hex_smaller : ∃ y'' z'' : ℕ, y'' * b + z'' * d = y * b + z * d ∧ z'' < z := by
        by_contra hno
        push Not at hno
        exact hnotL ⟨hAp_yz, hno⟩
      obtain ⟨y'', z'', h'', hltz⟩ := hex_smaller
      have hz_le : z' ≤ z'' := hL'.2 y'' z'' (h''.trans heq.symm)
      omega
  have not_inL_a_zero : ¬ InL a 0 := by
    intro ⟨⟨_, hsubS⟩, _⟩
    apply hsubS (by nlinarith)
    have heq : a * b + 0 * d - a = (b - 1) * a := by
      simp only [zero_mul, add_zero]
      exact mul_sub_left hb0
    rw [heq]
    exact mul_mem haS (b - 1)
  have not_inL_zero_a : ¬ InL 0 a := by
    intro ⟨⟨_, hsubS⟩, _⟩
    apply hsubS (by nlinarith)
    have heq : 0 * b + a * d - a = (d - 1) * a := by
      simp only [zero_mul, zero_add]
      exact mul_sub_left hd0
    rw [heq]
    exact mul_mem haS (d - 1)
  have hexY : ∃ y : ℕ, ¬ InL y 0 := ⟨a, not_inL_a_zero⟩
  have hexZ : ∃ z : ℕ, ¬ InL 0 z := ⟨a, not_inL_zero_a⟩
  let Y := Nat.find hexY
  let Z := Nat.find hexZ
  have hYnot : ¬ InL Y 0 := Nat.find_spec hexY
  have hZnot : ¬ InL 0 Z := Nat.find_spec hexZ
  have hYpos : 1 ≤ Y := by
    by_contra hlt
    have hY0 : Y = 0 := by omega
    exact hYnot (hY0 ▸ hL00)
  have hZpos : 1 ≤ Z := by
    by_contra hlt
    have hZ0 : Z = 0 := by omega
    exact hZnot (hZ0 ▸ hL00)
  have hYlt : ∀ y : ℕ, y < Y → InL y 0 := fun y hy => by
    by_contra hnot
    exact Nat.find_min hexY hy hnot
  have hZlt : ∀ z : ℕ, z < Z → InL 0 z := fun z hz => by
    by_contra hnot
    exact Nat.find_min hexZ hz hnot
  obtain ⟨yA, zA, hLA, hmA, hltA⟩ := not_inL_witness hYnot
  have hyA_lt_Y : yA < Y := by
    rcases hltA with hlt | ⟨_, hltz⟩
    · simp only [zero_mul, add_zero] at hlt
      have : yA * b < Y * b := by omega
      exact (Nat.mul_lt_mul_right hb0).mp this
    · omega
  have hyA0 : yA = 0 := by
    by_contra hyApos
    have hL_diff : InL (Y - yA) 0 := hYlt (Y - yA) (by omega)
    have hL_0zA : InL 0 zA := inL_down hLA (Nat.zero_le yA) le_rfl
    have hm_diff : 0 * b + zA * d ≡ (Y - yA) * b + 0 * d [MOD a] := by
      have hm1 : yA * b + (0 * b + zA * d) ≡ yA * b + ((Y - yA) * b + 0 * d) [MOD a] := by
        have hYeq : Y * b + 0 * d = yA * b + ((Y - yA) * b + 0 * d) := by
          simp only [zero_mul, add_zero]
          exact (add_sub_mul hyA_lt_Y.le).symm
        rw [← hYeq]
        simpa only [zero_mul, zero_add] using hmA
      exact modEq_add_left_cancel hm1
    have heq := inL_inj hL_0zA hL_diff hm_diff
    omega
  have hL_0zA : InL 0 zA := hyA0 ▸ hLA
  have hzA_lt_Z : zA < Z := by
    by_contra hge
    exact hZnot (inL_down hL_0zA le_rfl (by omega))
  have hm_zA : zA * d ≡ Y * b [MOD a] := by simpa [hyA0] using hmA
  obtain ⟨yB, zB, hLB, hmB, hltB⟩ := not_inL_witness hZnot
  have hzB_lt_Z : zB < Z := by
    rcases hltB with hlt | ⟨_, hltz⟩
    · simp only [zero_mul, zero_add] at hlt
      have : zB * d < Z * d := by omega
      exact (Nat.mul_lt_mul_right hd0).mp this
    · exact hltz
  have hzB0 : zB = 0 := by
    by_contra hzBpos
    have hL_diff : InL 0 (Z - zB) := hZlt (Z - zB) (by omega)
    have hL_yB0 : InL yB 0 := inL_down hLB le_rfl (Nat.zero_le zB)
    have hm_diff : yB * b + 0 * d ≡ 0 * b + (Z - zB) * d [MOD a] := by
      have hm1 : (yB * b + 0 * d) + zB * d ≡ (0 * b + (Z - zB) * d) + zB * d [MOD a] := by
        have hZeq : 0 * b + Z * d = (0 * b + (Z - zB) * d) + zB * d := by
          simp only [zero_mul, zero_add]
          exact (sub_mul_add hzB_lt_Z.le).symm
        rw [← hZeq]
        simpa only [zero_mul, add_zero] using hmB
      exact modEq_add_right_cancel hm1
    have heq := inL_inj hL_yB0 hL_diff hm_diff
    omega
  have hL_yB0 : InL yB 0 := hzB0 ▸ hLB
  have hyB_lt_Y : yB < Y := by
    by_contra hge
    exact hYnot (inL_down hL_yB0 (by omega) le_rfl)
  have hm_yB : yB * b ≡ Z * d [MOD a] := by simpa [hzB0] using hmB
  have hnot_corner : ¬ InL (Y - yB) (Z - zA) := by
    intro hLc
    have hm1 : (Y - yB) * b + (Z - zA) * d + (yB * b + zA * d) ≡ 0 + (yB * b + zA * d) [MOD a] := by
      have hsum_eq : (Y - yB) * b + (Z - zA) * d + (yB * b + zA * d) = Y * b + Z * d := by
        rw [add_add_add_comm, sub_mul_add hyB_lt_Y.le, sub_mul_add hzA_lt_Z.le]
      rw [hsum_eq, zero_add]
      exact (hm_zA.symm.add hm_yB.symm).trans (by rw [add_comm])
    have hm0 : (Y - yB) * b + (Z - zA) * d ≡ 0 * b + 0 * d [MOD a] := by
      simpa using modEq_add_right_cancel hm1
    have heq := inL_inj hLc hL00 hm0
    omega
  have inL_iff : ∀ y z : ℕ, InL y z ↔ y < Y ∧ z < Z ∧ ¬ (Y - yB ≤ y ∧ Z - zA ≤ z) := by
    intro y z
    constructor
    · intro hL
      refine ⟨?_, ?_, ?_⟩
      · by_contra hge
        exact hYnot (inL_down hL (by omega) (Nat.zero_le z))
      · by_contra hge
        exact hZnot (inL_down hL (Nat.zero_le y) (by omega))
      · rintro ⟨hy, hz⟩
        exact hnot_corner (inL_down hL hy hz)
    · suffices h : ∀ s y z : ℕ, y + z ≤ s →
          y < Y → z < Z → ¬ (Y - yB ≤ y ∧ Z - zA ≤ z) → InL y z by
        exact fun ⟨hy, hz, hnc⟩ => h (y + z) y z le_rfl hy hz hnc
      intro s
      induction s using Nat.strong_induction_on with
      | h s ih =>
        intro y z hsum hyY hzZ hnc
        by_contra hnotL
        obtain ⟨y', z', hL', hm', hlt'⟩ := not_inL_witness hnotL
        have hy'Y : y' < Y := by
          by_contra hge
          exact hYnot (inL_down hL' (by omega) (Nat.zero_le z'))
        have hz'Z : z' < Z := by
          by_contra hge
          exact hZnot (inL_down hL' (Nat.zero_le y') (by omega))
        have hnot_dom : ¬ (y ≤ y' ∧ z ≤ z') := by
          rintro ⟨hy1, hz1⟩
          exact hnotL (inL_down hL' hy1 hz1)
        by_cases h1 : y' < y ∧ z < z'
        · have hm_cross : (y - y') * b + 0 * d ≡ 0 * b + (z' - z) * d [MOD a] := by
            have hm1 : (y' * b + z * d) + ((y - y') * b + 0 * d) ≡
                (y' * b + z * d) + (0 * b + (z' - z) * d) [MOD a] := by
              have hLhs : y' * b + z * d + ((y - y') * b + 0 * d) = y * b + z * d := by
                simp only [zero_mul, add_zero]
                rw [add_right_comm, add_sub_mul h1.1.le]
              have hRhs : y' * b + z * d + (0 * b + (z' - z) * d) = y' * b + z' * d := by
                simp only [zero_mul, zero_add]
                rw [add_assoc, add_sub_mul h1.2.le]
              rw [hLhs, hRhs]
              exact hm'.symm
            exact modEq_add_left_cancel hm1
          have hcross := inL_inj (hYlt (y - y') (by omega)) (hZlt (z' - z) (by omega)) hm_cross
          omega
        by_cases h2 : y < y' ∧ z' < z
        · have hm_cross : (y' - y) * b + 0 * d ≡ 0 * b + (z - z') * d [MOD a] := by
            have hm1 : (y * b + z' * d) + ((y' - y) * b + 0 * d) ≡
                (y * b + z' * d) + (0 * b + (z - z') * d) [MOD a] := by
              have hLhs : y * b + z' * d + ((y' - y) * b + 0 * d) = y' * b + z' * d := by
                simp only [zero_mul, add_zero]
                rw [add_right_comm, add_sub_mul h2.1.le]
              have hRhs : y * b + z' * d + (0 * b + (z - z') * d) = y * b + z * d := by
                simp only [zero_mul, zero_add]
                rw [add_assoc, add_sub_mul h2.2.le]
              rw [hLhs, hRhs]
              exact hm'
            exact modEq_add_left_cancel hm1
          have hcross := inL_inj (hYlt (y' - y) (by omega)) (hZlt (z - z') (by omega)) hm_cross
          omega
        have hle_both : y' ≤ y ∧ z' ≤ z := by omega
        by_cases hy'z' : 0 < y' + z'
        · have hnotL_sub : ¬ InL (y - y') (z - z') := by
            intro hLsub
            have hm1 : (y - y') * b + (z - z') * d + (y' * b + z' * d) ≡ 0 + (y' * b + z' * d) [MOD a] := by
              have hLhs : (y - y') * b + (z - z') * d + (y' * b + z' * d) = y * b + z * d := by
                rw [add_add_add_comm, sub_mul_add hle_both.1, sub_mul_add hle_both.2]
              rw [hLhs, zero_add]
              exact hm'.symm
            have hm0 : (y - y') * b + (z - z') * d ≡ 0 * b + 0 * d [MOD a] := by
              simpa using modEq_add_right_cancel hm1
            have heq := inL_inj hLsub hL00 hm0
            omega
          have hLsub := ih (y - y' + (z - z')) (by omega) (y - y') (z - z') le_rfl
            (by omega) (by omega) (by intro ⟨hyc, hzc⟩; apply hnc; exact ⟨by omega, by omega⟩)
          exact hnotL_sub hLsub
        · have hy'0 : y' = 0 := by omega
          have hz'0 : z' = 0 := by omega
          have hm0 : y * b + z * d ≡ 0 [MOD a] := by simpa [hy'0, hz'0] using hm'.symm
          have hypos : 0 < y := by
            by_contra hy0
            have : y = 0 := by omega
            exact hnotL (this ▸ hZlt z hzZ)
          have hzpos : 0 < z := by
            by_contra hz0
            have : z = 0 := by omega
            exact hnotL (this ▸ hYlt y hyY)
          by_cases hy_small : y < Y - yB
          · have hhm : (y + yB) * b + 0 * d ≡ 0 * b + (Z - z) * d [MOD a] := by
              have hm1 : (y + yB) * b + z * d ≡ (0 * b + (Z - z) * d) + z * d [MOD a] := by
                have hm_lhs : (y + yB) * b + z * d = (y * b + z * d) + yB * b := by
                  rw [Nat.add_mul]; ring
                have hm_rhs : (0 * b + (Z - z) * d) + z * d = 0 + Z * d := by
                  simp only [zero_mul, zero_add, sub_mul_add hzZ.le]
                rw [hm_lhs, hm_rhs]
                exact hm0.add hm_yB
              simpa using modEq_add_right_cancel hm1
            have heq := inL_inj (hYlt (y + yB) (by omega)) (hZlt (Z - z) (by omega)) hhm
            omega
          · have hz_small : z < Z - zA := by omega
            have hhm : (Y - y) * b + 0 * d ≡ 0 * b + (z + zA) * d [MOD a] := by
              have hm1 : y * b + ((Y - y) * b + 0 * d) ≡ y * b + (0 * b + (z + zA) * d) [MOD a] := by
                have hm_lhs : y * b + ((Y - y) * b + 0 * d) = Y * b := by
                  simp only [zero_mul, add_zero, add_sub_mul hyY.le]
                have hm_rhs : y * b + (0 * b + (z + zA) * d) = (y * b + z * d) + zA * d := by
                  rw [Nat.add_mul]; ring
                rw [hm_lhs, hm_rhs]
                simpa [zero_add] using hm0.symm.add hm_zA.symm
              exact modEq_add_left_cancel hm1
            have heq := inL_inj (hYlt (Y - y) (by omega)) (hZlt (z + zA) (by omega)) hhm
            omega
  let c₁ := (Y - yB - 1) * b + (Z - 1) * d
  let c₂ := (Y - 1) * b + (Z - zA - 1) * d
  have hPF_mem : ∀ f ∈ PF S, f + a ∈ ({c₁, c₂} : Finset ℕ) := by
    intro f hf
    have hf' := mem_PF_iff.mp hf
    have hfa_Ap : InAp (f + a) := by
      refine ⟨hf'.2.2 a haS ha0, fun _ hsubS => ?_⟩
      apply hf'.2.1
      simpa using hsubS
    obtain ⟨y, z, hL, hfa_eq⟩ := inL_of_inAp hfa_Ap
    have hnot_y1 : ¬ InL (y + 1) z := by
      intro hL1
      apply hL1.1.2 (by nlinarith)
      have heq : (y + 1) * b + z * d - a = f + b := by
        rw [Nat.add_mul, one_mul, add_assoc, add_comm b (z * d), ← add_assoc, hfa_eq]
        omega
      rw [heq]
      exact hf'.2.2 b hbS hb0
    have hnot_z1 : ¬ InL y (z + 1) := by
      intro hL1
      apply hL1.1.2 (by nlinarith)
      have heq : y * b + (z + 1) * d - a = f + d := by
        rw [Nat.add_mul, one_mul, ← add_assoc, hfa_eq]
        omega
      rw [heq]
      exact hf'.2.2 d hdS hd0
    rw [inL_iff] at hL hnot_y1 hnot_z1
    obtain ⟨hyY, hzZ, hnc⟩ := hL
    rw [Finset.mem_insert, Finset.mem_singleton]
    by_cases hy_small : y < Y - yB
    · have hz_eq : z = Z - 1 := by
        by_contra hne
        exact hnot_z1 ⟨hyY, by omega, fun ⟨hy', _⟩ => by omega⟩
      have hy_eq : y = Y - yB - 1 := by
        by_contra hne
        exact hnot_y1 ⟨by omega, by omega, fun ⟨hy', _⟩ => by omega⟩
      left
      rw [← hfa_eq, hy_eq, hz_eq]
    · have hz_small : z < Z - zA := by omega
      have hy_eq : y = Y - 1 := by
        by_contra hne
        exact hnot_y1 ⟨by omega, hzZ, fun ⟨_, hz'⟩ => by omega⟩
      have hz_eq : z = Z - zA - 1 := by
        by_contra hne
        exact hnot_z1 ⟨hyY, by omega, fun ⟨_, hz'⟩ => by omega⟩
      right
      rw [← hfa_eq, hy_eq, hz_eq]
  have hinj : Set.InjOn (fun f => f + a) (PF S : Set ℕ) :=
    fun _ _ _ _ h => Nat.add_right_cancel h
  calc (PF S).card ≤ ({c₁, c₂} : Finset ℕ).card := Finset.card_le_card_of_injOn _ hPF_mem hinj
    _ ≤ 2 := Finset.card_le_two

end OMA.WilfE3

theorem OMA.solution : type_of% @WilfNumericalSemigroupConjecture.wilf_conjecture_embedding_dim_le_three := by
  intro S hS he
  have hge1 : 1 ≤ S.embeddingDim := OMA.WilfE3.one_le_embeddingDim hS
  rcases Nat.lt_or_eq_of_le he with hlt3 | he3
  · rcases Nat.lt_or_eq_of_le (by omega : S.embeddingDim ≤ 2) with hlt2 | he2
    · have he1 : S.embeddingDim = 1 := by omega
      rw [OMA.WilfE3.conductor_eq_zero_of_embeddingDim_eq_one hS he1]
      exact Nat.zero_le _
    · calc S.conductor ≤ ((OMA.WilfE3.PF S).card + 1) * WilfNumericalSemigroupConjecture.sporadicCount S :=
          OMA.WilfE3.conductor_le_succ_pf_mul_sporadic hS
        _ ≤ (1 + 1) * WilfNumericalSemigroupConjecture.sporadicCount S := by
          gcongr
          exact OMA.WilfE3.pf_card_le_one_of_embeddingDim_eq_two hS he2
        _ = S.embeddingDim * WilfNumericalSemigroupConjecture.sporadicCount S := by rw [he2]
  · calc S.conductor ≤ ((OMA.WilfE3.PF S).card + 1) * WilfNumericalSemigroupConjecture.sporadicCount S :=
        OMA.WilfE3.conductor_le_succ_pf_mul_sporadic hS
      _ ≤ (2 + 1) * WilfNumericalSemigroupConjecture.sporadicCount S := by
        gcongr
        exact OMA.WilfE3.pf_card_le_two_of_embeddingDim_eq_three hS he3
      _ = S.embeddingDim * WilfNumericalSemigroupConjecture.sporadicCount S := by rw [he3]
