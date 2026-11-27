import FormalConjectures.ErdosProblems.«862»

/-! For each point of a finite Sidon set choose one of two widely separated lifts. At one distinguished point take both lifts. Every maximal extension remembers the chosen lifts, since a Sidon set cannot repeat a nonzero difference. -/

-- Credit: @marcusbuffett
-- The finite Ruzsa construction below is from the checked Erdős 30 Singer H2 proof by @ldy985.
-- Ruzsa's construction. Write p = q + 1 and let g generate the units of ZMod p. For i < q take the
-- integer x_i = i + q * k_i with k_i < p chosen so that x_i ≡ g ^ i (mod p); so x_i ≡ i (mod q).
-- If x_a + x_c = x_b + x_d then a + c ≡ b + d (mod q), hence g^a * g^c = g^b * g^d, and also
-- g^a + g^c = g^b + g^d in the field ZMod p. Equal sum and product force {g^a, g^c} = {g^b, g^d},
-- and g ^ i is injective on i < q. The set is { 1 + x_i : i < q }, inside {1, …, p * (p - 1)}.

namespace OMA.Ruzsa

/-- Ruzsa's construction: for a prime `q + 1`, the `q` integers `1 + i + q * k_i`, `i < q`, where
`k_i` is chosen so that the number is `≡ 1 + g ^ i (mod q + 1)` for a primitive root `g`, form a
Sidon set inside `{1, …, (q + 1) q}`. -/
theorem ruzsa_succ (q : ℕ) (hp : (q + 1).Prime) : ∃ A : Finset ℕ,
    A ⊆ Finset.Icc 1 ((q + 1) * q) ∧ IsSidon (A : Set ℕ) ∧ A.card = q := by
  have : Fact (q + 1).Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ : ∃ g : (ZMod (q + 1))ˣ, orderOf g = q := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod (q + 1))ˣ)
    refine ⟨g, ?_⟩
    rw [hg, Nat.card_eq_fintype_card, ZMod.card_units (q + 1)]
    simp
  obtain ⟨u, hu⟩ : ∃ u : ℕ → ZMod (q + 1), ∀ i, u i = ((g ^ i : (ZMod (q + 1))ˣ) : ZMod (q + 1)) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ → ℕ, ∀ i, k i = (i + (q + 1) - (u i).val) % (q + 1) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℕ, ∀ i, f i = 1 + i + q * k i := ⟨_, fun _ => rfl⟩
  have hk_lt : ∀ i, k i < q + 1 := fun i => by
    rw [hk]
    exact Nat.mod_lt _ (Nat.succ_pos q)
  have hqcast : ((q : ℕ) : ZMod (q + 1)) = -1 := by
    have h0 : ((q + 1 : ℕ) : ZMod (q + 1)) = 0 := ZMod.natCast_self (q + 1)
    push_cast at h0
    linear_combination h0
  have hkcast : ∀ i, ((k i : ℕ) : ZMod (q + 1)) = (i : ZMod (q + 1)) - u i := by
    intro i
    have hval : (u i).val ≤ i + (q + 1) := (ZMod.val_lt (u i)).le.trans (Nat.le_add_left _ _)
    have h0 : ((q + 1 : ℕ) : ZMod (q + 1)) = 0 := ZMod.natCast_self (q + 1)
    rw [hk, ZMod.natCast_mod, Nat.cast_sub hval, Nat.cast_add, h0, ZMod.natCast_zmod_val]
    ring
  have hfcast : ∀ i, ((f i : ℕ) : ZMod (q + 1)) = 1 + u i := by
    intro i
    rw [hf]
    push_cast
    rw [hqcast, hkcast]
    ring
  have hu_inj : ∀ a b, a < q → b < q → u a = u b → a = b := by
    intro a b ha hb hab
    rw [hu, hu] at hab
    have h1 : g ^ a = g ^ b := Units.ext hab
    have h2 : a ≡ b [MOD orderOf g] := pow_eq_pow_iff_modEq.1 h1
    rw [hg] at h2
    exact Nat.ModEq.eq_of_lt_of_lt h2 ha hb
  have hf_mod : ∀ i, f i % q = (1 + i) % q := by
    intro i
    rw [hf]
    exact Nat.add_mul_mod_self_left _ _ _
  refine ⟨(Finset.range q).image f, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
    have hi' := Finset.mem_range.1 hi
    have hki := hk_lt i
    rw [Finset.mem_Icc, hf]
    refine ⟨by omega, ?_⟩
    have h1 : q * k i ≤ q * q := Nat.mul_le_mul_left q (by omega)
    have h2 : (q + 1) * q = q * q + q := by ring
    omega
  · intro x hx y hy z hz w hw hsum
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hz)
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hw)
    have ha' := Finset.mem_range.1 ha
    have hb' := Finset.mem_range.1 hb
    have hc' := Finset.mem_range.1 hc
    have hd' := Finset.mem_range.1 hd
    -- the sum of the exponents is determined modulo q
    have hmod : a + c ≡ b + d [MOD q] := by
      have e : a + c + q * (k a + k c + 0) + 2 = b + d + q * (k b + k d + 0) + 2 := by
        have := hsum
        rw [hf a, hf b, hf c, hf d] at this
        simp only [Nat.mul_add, Nat.add_zero]
        omega
      have e' : a + c + q * (k a + k c + 0) = b + d + q * (k b + k d + 0) := by omega
      have e2 := congrArg (· % q) e'
      simp only [Nat.add_mul_mod_self_left] at e2
      exact e2
    have hgpow : g ^ (a + c) = g ^ (b + d) := pow_eq_pow_iff_modEq.2 (by rw [hg]; exact hmod)
    have hprod : u a * u c = u b * u d := by
      rw [hu, hu, hu, hu, ← Units.val_mul, ← Units.val_mul, ← pow_add, ← pow_add, hgpow]
    have hadd : u a + u c = u b + u d := by
      have e := congrArg (Nat.cast : ℕ → ZMod (q + 1)) hsum
      rw [Nat.cast_add, Nat.cast_add, hfcast, hfcast, hfcast, hfcast] at e
      linear_combination e
    have hzero : (u a - u b) * (u a - u d) = 0 := by
      linear_combination (u a) * hadd - hprod
    rcases mul_eq_zero.1 hzero with h | h
    · have hab : a = b := hu_inj a b ha' hb' (sub_eq_zero.1 h)
      have hcd : c = d := by
        apply hu_inj c d hc' hd'
        rw [hab] at hadd
        exact add_left_cancel hadd
      exact Or.inl ⟨by rw [hab], by rw [hcd]⟩
    · have had : a = d := hu_inj a d ha' hd' (sub_eq_zero.1 h)
      have hcb : c = b := by
        apply hu_inj c b hc' hb'
        rw [had] at hadd
        have : u d + u c = u d + u b := by rw [hadd]; ring
        exact add_left_cancel this
      exact Or.inr ⟨by rw [had], by rw [hcb]⟩
  · rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hij
    have hi' : i < q := Finset.mem_range.1 (Finset.mem_coe.1 hi)
    have hj' : j < q := Finset.mem_range.1 (Finset.mem_coe.1 hj)
    have h1 : (1 + i) % q = (1 + j) % q := by rw [← hf_mod, ← hf_mod, hij]
    have h2 : (1 + i) ≡ (1 + j) [MOD q] := h1
    have h3 : i ≡ j [MOD q] := Nat.ModEq.add_left_cancel' 1 h2
    exact Nat.ModEq.eq_of_lt_of_lt h3 hi' hj'

theorem ruzsa (p : ℕ) (hp : p.Prime) : ∃ A : Finset ℕ,
    A ⊆ Finset.Icc 1 (p * (p - 1)) ∧ IsSidon (A : Set ℕ) ∧ A.card = p - 1 := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.pos; omega⟩
  simpa using ruzsa_succ q hp

end OMA.Ruzsa


open Finset Filter
namespace Count862

private theorem maximal_extension {S : Finset ℕ} {N : ℕ} (hS : S ⊆ Icc 1 N)
    (hsid : IsSidon (S : Set ℕ)) : ∃ A : Finset ℕ,
    S ⊆ A ∧ A ⊆ Icc 1 N ∧ Set.IsMaximalSidonSetIn (A : Set ℕ) N := by
  classical
  let F := (Icc 1 N).powerset.filter (fun C : Finset ℕ => S ⊆ C ∧ IsSidon (C : Set ℕ))
  have hF : S ∈ F := mem_filter.mpr ⟨mem_powerset.mpr hS, Subset.rfl, hsid⟩
  obtain ⟨A,ha,hm⟩ := F.exists_max_image Finset.card ⟨_,hF⟩
  obtain ⟨hA,hSA,hsi⟩ := mem_filter.mp ha
  have hA' := mem_powerset.mp hA
  refine ⟨A,hSA,hA',fun x hx => mem_Icc.mp (hA' hx),hsi,?_⟩
  intro x hx hxa hnew
  have hmem : insert x A ∈ F := by
    apply mem_filter.mpr
    refine ⟨mem_powerset.mpr (insert_subset (mem_Icc.mpr hx) hA'), hSA.trans (subset_insert ..), ?_⟩
    simpa [Set.union_singleton] using hnew
  have h := hm _ hmem
  rw [card_insert_of_notMem hxa] at h
  omega

private def seed (B T : Finset ℕ) (w D : ℕ) : Finset ℕ :=
  (B \ T) ∪ (insert w T).image (· + D)

private def Lift (T : Finset ℕ) (w D a x : ℕ) : Prop :=
  (x = a ∧ a ∉ T) ∨ (x = a + D ∧ (a ∈ T ∨ a = w))

private theorem same {T : Finset ℕ} {w D a b x y u v : ℕ}
    (hx : Lift T w D a x) (hy : Lift T w D b y)
    (hu : Lift T w D a u) (hv : Lift T w D b v) (h : x+y=u+v) :
    (x=u ∧ y=v) ∨ (x=v ∧ y=u) := by
  by_cases ha : a ∈ T <;> by_cases hb : b ∈ T <;>
    simp [Lift, ha, hb] at hx hy hu hv <;> omega

private theorem seed_ok {B T : Finset ℕ} {w M : ℕ} (hw : w ∈ B)
    (ht : T ⊆ B.erase w) (hb : B ⊆ Icc 1 M) (hs : IsSidon (B : Set ℕ)) :
    let D := 2*M+1
    seed B T w D ⊆ Icc 1 (3*M+1) ∧ IsSidon ((seed B T w D : Finset ℕ) : Set ℕ) := by
  let D := 2*M+1
  have rep {x} (hx : x ∈ seed B T w D) : ∃ a ∈ B, Lift T w D a x := by
    rcases mem_union.mp hx with lo | high
    · obtain ⟨h1,h2⟩ := mem_sdiff.mp lo
      exact ⟨x,h1,Or.inl ⟨rfl,h2⟩⟩
    · obtain ⟨a,ha,rfl⟩ := mem_image.mp high
      rcases mem_insert.mp ha with rfl | ha
      · exact ⟨_,hw,Or.inr ⟨rfl,Or.inr rfl⟩⟩
      · exact ⟨a,mem_of_mem_erase (ht ha),Or.inr ⟨rfl,Or.inl ha⟩⟩
  constructor
  · intro x hx
    obtain ⟨a,ha,h⟩ := rep hx
    have := mem_Icc.mp (hb ha)
    rcases h with h | h <;> apply mem_Icc.mpr <;> dsimp [D] at * <;> omega
  · intro x hx u hu y hy v hv h
    obtain ⟨a,ha,hx'⟩ := rep hx
    obtain ⟨b,hb',hy'⟩ := rep hy
    obtain ⟨c,hc,hu'⟩ := rep hu
    obtain ⟨d,hd,hv'⟩ := rep hv
    have heq : a+b=c+d := by
      have := mem_Icc.mp (hb ha)
      have := mem_Icc.mp (hb hb')
      have := mem_Icc.mp (hb hc)
      have := mem_Icc.mp (hb hd)
      rcases hx' with h1 | h1 <;> rcases hy' with h2 | h2 <;>
        rcases hu' with h3 | h3 <;> rcases hv' with h4 | h4 <;> dsimp [D] at * <;> omega
    rcases hs a ha c hc b hb' d hd heq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact same hx' hy' hu' hv' h
    · exact (same hx' hy' hv' hu' (h.trans (Nat.add_comm ..))).symm

private theorem count {N M : ℕ} (hn : 3*M+1 ≤ N) (B : Finset ℕ)
    (hb : B ⊆ Icc 1 M) (hs : IsSidon (B : Set ℕ)) {w : ℕ} (hw : w ∈ B) :
    2^(B.card-1) ≤ Erdos862.numMaximalSidonSets N := by
  classical
  let D := 2*M+1
  let F := (B.erase w).powerset
  let G := (Icc 1 N).powerset.filter (fun A : Finset ℕ => Set.IsMaximalSidonSetIn (A : Set ℕ) N)
  have ext (T : Finset ℕ) (ht : T ∈ F) :
      ∃ A ∈ G, seed B T w D ⊆ A := by
    obtain ⟨lo,sid⟩ := seed_ok hw (mem_powerset.mp ht) hb hs
    obtain ⟨A,hSA,hA,hmax⟩ := maximal_extension (lo.trans (Icc_subset_Icc_right hn)) sid
    exact ⟨A,mem_filter.mpr ⟨mem_powerset.mpr hA,hmax⟩,hSA⟩
  choose! f hf hsub using ext
  have recover (T : Finset ℕ) (ht : T ∈ F) (a : ℕ) (ha : a ∈ B.erase w) :
      a ∈ T ↔ a+D ∈ f T := by
    have inc := hsub T ht
    have hasHigh {x : ℕ} (hx : x ∈ insert w T) : x+D ∈ f T :=
      inc (mem_union_right _ (mem_image_of_mem _ hx))
    refine ⟨fun h => hasHigh (mem_insert_of_mem h), ?_⟩
    intro h
    by_contra hnot
    have hasLow {x : ℕ} (hx : x ∈ B) (hx' : x ∉ T) : x ∈ f T :=
      inc (mem_union_left _ (mem_sdiff.mpr ⟨hx,hx'⟩))
    have wnot : w ∉ T := fun h => notMem_erase w B (mem_powerset.mp ht h)
    have hsid := (mem_filter.mp (hf T ht)).2.2.1
    have bad := hsid a (hasLow (mem_of_mem_erase ha) hnot) w (hasLow hw wnot)
      (w+D) (hasHigh (mem_insert_self ..)) (a+D) h (by omega)
    have := (mem_erase.mp ha).1
    dsimp [D] at bad
    omega
  have inj : Set.InjOn f F := by
    intro T ht U hu heq
    ext a
    by_cases ha : a ∈ B.erase w
    · rw [recover T ht a ha, recover U hu a ha, heq]
    · exact iff_of_false (fun h => ha (mem_powerset.mp ht h)) (fun h => ha (mem_powerset.mp hu h))
  have hcount := card_le_card_of_injOn f hf inj
  have eq : (G : Set (Finset ℕ)) = {A : Finset ℕ | A ⊆ Icc 1 N ∧ Set.IsMaximalSidonSetIn (A : Set ℕ) N} := by
    ext A; simp [G]
  rw [Erdos862.numMaximalSidonSets, ← eq, Set.ncard_coe_finset]
  simpa [F,card_erase_of_mem hw] using hcount

end Count862

theorem OMA.solution : type_of% @Erdos862.erdos_862.variants.lower_bound := by
  intro ε hε
  filter_upwards [eventually_ge_atTop 1600] with N hN
  let t := N.sqrt / 4
  have ht0 : 40 ≤ N.sqrt := Nat.le_sqrt.mpr (by simpa using hN)
  have ht : 10 ≤ t := by dsimp [t]; omega
  obtain ⟨p,hp,hpt,hp2⟩ := Nat.exists_prime_lt_and_le_two_mul t (by omega)
  obtain ⟨B,hB,hs,hcard⟩ := OMA.Ruzsa.ruzsa p hp
  have hne : B.Nonempty := card_pos.mp (by rw [hcard]; omega)
  obtain ⟨w,hw⟩ := hne
  have hfour : 4*t ≤ N.sqrt := by dsimp [t]; omega
  have hn' : 3*(p*(p-1))+1 ≤ N := by
    have h1 := Nat.mul_le_mul hp2 hp2
    have h2 := Nat.mul_le_mul hfour hfour
    have h3 := Nat.mul_le_mul_left p (Nat.sub_le p 1)
    nlinarith [Nat.sqrt_le N]
  have hnum := Count862.count hn' B hB hs hw
  have hsqrt : Real.sqrt N ≤ (N.sqrt : ℝ)+1 := by
    have hsq := Nat.sqrt_lt.mp (show N.sqrt < N.sqrt+1 by omega)
    have hr : (N : ℝ) < ((N.sqrt:ℝ)+1)*((N.sqrt:ℝ)+1) := by exact_mod_cast hsq
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) N),Real.sqrt_nonneg (N : ℝ)]
  have htup : N.sqrt+1 ≤ 4*t+4 := by dsimp [t]; omega
  have hrup : (N.sqrt : ℝ)+1 ≤ 4*(t:ℝ)+4 := by exact_mod_cast htup
  have he : (0.16-ε)*Real.sqrt N ≤ ((B.card-1 : ℕ) : ℝ) := by
    have ha : t ≤ (B.card-1)+1 := by rw [hcard]; omega
    have hb : (t : ℝ) ≤ ((B.card-1 : ℕ) : ℝ)+1 := by exact_mod_cast ha
    have ht' : (10 : ℝ) ≤ t := by exact_mod_cast ht
    nlinarith [mul_nonneg hε.le (Real.sqrt_nonneg (N : ℝ))]
  rw [← Real.sqrt_eq_rpow]
  calc (2 : ℝ)^((0.16-ε)*Real.sqrt N) ≤ 2^((B.card-1 : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) he
    _ = (2:ℝ)^(B.card-1) := Real.rpow_natCast .. 
    _ ≤ _ := by exact_mod_cast hnum
