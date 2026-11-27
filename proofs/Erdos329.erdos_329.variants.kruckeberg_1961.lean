import FormalConjectures.ErdosProblems.«329»

/-!
# An infinite Sidon set with square-root upper density 1/√2

Use Ruzsa's finite Sidon construction (formalized by @ldy985). Delete the
upper endpoint of each short difference and shift the resulting block above
its own diameter. This lets the block extend any previously chosen finite
Sidon set. Taking increasingly large primes gives upper density at least
1/√2. Thinning by rank gives equality. The elementary signed-difference
bound for the density and the union argument adapt the checked Erdős 329
lower-bound proof.
-/
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


namespace OMA.Kruckeberg

open Filter Erdos329 Finset
open scoped Topology

lemma sidon_bound (B : Set ℕ) (hB : IsSidon B) (N : ℕ) :
    Erdos329.sqrtPartialDensity B N ≤ 3 := by
  unfold Erdos329.sqrtPartialDensity
  have hfin : (B ∩ Set.Icc 1 N).Finite := (Set.finite_Icc 1 N).subset Set.inter_subset_right
  rw [Set.ncard_eq_toFinset_card _ hfin]
  set s := hfin.toFinset with hs
  have hmem : ∀ x, x ∈ s ↔ x ∈ B ∧ 1 ≤ x ∧ x ≤ N := by
    intro x; rw [hs, Set.Finite.mem_toFinset]; simp
  have hcard : s.offDiag.card ≤ (Finset.Icc (-(N : ℤ)) N).card := by
    apply Finset.card_le_card_of_injOn (fun q : ℕ × ℕ => (q.2 : ℤ) - q.1)
    · intro q hq
      rw [Finset.mem_coe, Finset.mem_offDiag] at hq
      simp only [Finset.mem_coe, Finset.mem_Icc]
      have := (hmem _).1 hq.1
      have := (hmem _).1 hq.2.1
      constructor <;> omega
    · intro q hq q' hq' e
      simp only [Finset.mem_coe, Finset.mem_offDiag] at hq hq'
      simp only at e
      have e' : q.2 + q'.1 = q'.2 + q.1 := by omega
      rcases hB q.2 ((hmem _).1 hq.2.1).1 q'.2 ((hmem _).1 hq'.2.1).1 q'.1
        ((hmem _).1 hq'.1).1 q.1 ((hmem _).1 hq.1).1 e' with ⟨x1, x2⟩ | ⟨x1, x2⟩
      · exact Prod.ext x2.symm x1
      · exact absurd x1.symm hq.2.2
  rw [Finset.offDiag_card, Int.card_Icc] at hcard
  have hk : s.card * s.card ≤ 2 * N + 1 + s.card := by omega
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  have hk2 : s.card ^ 2 ≤ 9 * N := by
    rcases le_or_gt s.card 3 with h3 | h3
    · nlinarith
    · nlinarith
  have hsq : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
  rw [div_le_iff₀ hsq]
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ N by positivity)
  have hk3 : ((s.card : ℝ)) ^ 2 ≤ 9 * (N : ℝ) := by exact_mod_cast hk2
  have hk0 : (0 : ℝ) ≤ s.card := by positivity
  nlinarith

private lemma prune (B : Finset ℕ) (hs : IsSidon (B : Set ℕ)) (m : ℕ) :
    ∃ C ⊆ B, B.card ≤ C.card + m ∧ ∀ x ∈ C, ∀ y ∈ C, x < y → x + m < y := by
  classical
  let P := (B ×ˢ B).filter fun z => z.1 < z.2 ∧ z.2 ≤ z.1 + m
  let bad := P.image Prod.snd
  have hm : P.card ≤ m := by
    have maps : Set.MapsTo (fun z : ℕ × ℕ => z.2-z.1) (P : Set _) (Icc 1 m : Finset ℕ) := by
      intro z hz
      simp only [P, mem_coe, mem_filter, mem_product, mem_Icc] at hz ⊢
      omega
    have inj : Set.InjOn (fun z : ℕ × ℕ => z.2-z.1) (P : Set _) := by
      intro z hz v hv he
      simp only [P, mem_coe, mem_filter, mem_product] at hz hv
      dsimp at he
      obtain ⟨h1,h2⟩ | ⟨h1,_⟩ :=
        hs z.2 hz.1.2 v.2 hv.1.2 v.1 hv.1.1 z.1 hz.1.1 (by omega)
      · exact Prod.ext h2.symm h1
      · omega
    simpa using card_le_card_of_injOn _ maps inj
  have hbad : bad.card ≤ m := (card_image_le).trans hm
  refine ⟨B \ bad, sdiff_subset, ?_, ?_⟩
  · have := card_le_card (show B ⊆ (B \ bad) ∪ bad by intro x hx; by_cases h : x ∈ bad <;> simp [hx,h])
    have := card_union_le (B \ bad) bad
    omega
  · intro x hx y hy hxy
    by_contra! h
    apply (mem_sdiff.mp hy).2
    exact mem_image.mpr ⟨(x,y),mem_filter.mpr ⟨mem_product.mpr
      ⟨(mem_sdiff.mp hx).1,(mem_sdiff.mp hy).1⟩,hxy,h⟩,rfl⟩

private lemma join {S D : Finset ℕ} {m L : ℕ} (hm : 2*m ≤ L)
    (hS : ∀ x ∈ S, x ≤ m) (hD : ∀ x ∈ D, L < x ∧ x + m ≤ 2*L)
    (gap : ∀ x ∈ D, ∀ y ∈ D, x < y → x + m < y)
    (ss : IsSidon (S : Set ℕ)) (sd : IsSidon (D : Set ℕ)) :
    IsSidon (↑(S ∪ D) : Set ℕ) := by
  have sep (x y) (hx : x ∈ D) (hy : y ∈ D) (h1 : x ≤ y+m) (h2 : y ≤ x+m) : x=y := by
    rcases lt_trichotomy x y with h | h | h
    · have := gap x hx y hy h; omega
    · exact h
    · have := gap y hy x hx h; omega
  intro a ha c hc b hb d hd h
  simp only [mem_coe, mem_union] at ha hb hc hd
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc <;>
    rcases hd with hd | hd
  all_goals first
    | exact ss a ha c hc b hb d hd h
    | exact sd a ha c hc b hb d hd h
    | skip
  all_goals
    try have ha' := hS _ ha
    try have ha' := hD _ ha
    try have hb' := hS _ hb
    try have hb' := hD _ hb
    try have hc' := hS _ hc
    try have hc' := hD _ hc
    try have hd' := hS _ hd
    try have hd' := hD _ hd
    try have e1 := sep a c ha hc (by omega) (by omega)
    try have e2 := sep a d ha hd (by omega) (by omega)
    try have e3 := sep b c hb hc (by omega) (by omega)
    try have e4 := sep b d hb hd (by omega) (by omega)
    omega

private lemma extend (S : Finset ℕ) (hs : IsSidon (S : Set ℕ)) (j : ℕ) :
    ∃ T : Finset ℕ, S ⊆ T ∧ IsSidon (T : Set ℕ) ∧ ∃ N ≥ j,
      (1 - 1/((j:ℝ)+1)) / Real.sqrt 2 ≤ sqrtPartialDensity T N := by
  classical
  let m := S.sup id
  obtain ⟨p,hp,prime⟩ := Nat.exists_infinite_primes ((j+1)*(m+1)+1)
  have hp0 := prime.pos
  have hm : m+1 ≤ p := by nlinarith [Nat.zero_le (j*m)]
  have hj : j ≤ p := by nlinarith [Nat.zero_le (j*m)]
  obtain ⟨B,hB,hBs,hBc⟩ := OMA.Ruzsa.ruzsa p prime
  obtain ⟨C,hCB,hCc,hgap⟩ := prune B hBs m
  let D := C.image (fun x => p^2+x)
  have hdmem (x : ℕ) : x ∈ D ↔ ∃ y ∈ C, p^2+y=x := mem_image
  have hD (x) (hx : x ∈ D) : p^2 < x ∧ x+m ≤ 2*p^2 := by
    obtain ⟨y,hy,rfl⟩ := (hdmem x).mp hx
    have hyb := mem_Icc.mp (hB (hCB hy))
    have hh : p*(p-1)+p=p^2 := by rw [← Nat.mul_succ, show (p-1).succ = p by omega]; ring
    omega
  have sd : IsSidon (D : Set ℕ) := by
    rintro a ha c hc b hb d hd e
    obtain ⟨a,haC,rfl⟩ := (hdmem _).mp ha
    obtain ⟨b,hbC,rfl⟩ := (hdmem _).mp hb
    obtain ⟨c,hcC,rfl⟩ := (hdmem _).mp hc
    obtain ⟨d,hdC,rfl⟩ := (hdmem _).mp hd
    rcases hBs a (hCB haC) c (hCB hcC) b (hCB hbC) d (hCB hdC) (by omega) with h | h <;> omega
  have hsep (x) (hx : x ∈ D) (y) (hy : y ∈ D) (hlt : x < y) : x+m < y := by
    obtain ⟨a,haC,rfl⟩ := (hdmem _).mp hx
    obtain ⟨b,hbC,rfl⟩ := (hdmem _).mp hy
    have := hgap a haC b hbC (by omega)
    omega
  refine ⟨S ∪ D, subset_union_left, join (by nlinarith [prime.two_le, Nat.sub_add_cancel hp0, sq_nonneg (p:ℤ)])
      (fun x hx => le_sup (f := id) hx) hD hsep hs sd, 2*p^2,
      by nlinarith [Nat.le_self_pow (by decide : 2 ≠ 0) p], ?_⟩
  have hcnt := Set.ncard_le_ncard (show (D : Set ℕ) ⊆ (↑(S ∪ D) : Set ℕ) ∩ Set.Icc 1 (2*p^2) by
    intro x hx
    obtain ⟨h1,h2⟩ := hD x hx
    exact ⟨mem_union_right _ hx, by omega,by omega⟩)
    ((Set.finite_Icc _ _).subset Set.inter_subset_right)
  rw [Set.ncard_coe_finset, show D.card=C.card from card_image_of_injective _ (fun _ _ e => Nat.add_left_cancel e)] at hcnt
  unfold sqrtPartialDensity
  rw [show ((2*p^2:ℕ):ℝ) = 2*(p:ℝ)^2 by push_cast; ring,
    Real.sqrt_mul (by norm_num), Real.sqrt_sq (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
  have hcount : p ≤ ((↑(S ∪ D) : Set ℕ) ∩ Set.Icc 1 (2*p^2)).ncard + (m+1) := by omega
  have hp' : ((j:ℝ)+1) * (m+1) ≤ (p:ℝ) := by exact_mod_cast (show (j+1)*(m+1) ≤ p by omega)
  have hc' : (p:ℝ) ≤ (((↑(S ∪ D) : Set ℕ) ∩ Set.Icc 1 (2*p^2)).ncard:ℝ) + (m+1) := by exact_mod_cast hcount
  have ht : (m:ℝ)+1 ≤ p/((j:ℝ)+1) := (le_div_iff₀ (by positivity)).mpr (by linarith)
  have ht' := mul_le_mul_of_nonneg_right (show (1-1/((j:ℝ)+1))*p ≤
      (((↑(S ∪ D) : Set ℕ) ∩ Set.Icc 1 (2*p^2)).ncard:ℝ) by
    rw [sub_mul,one_mul,one_div,← div_eq_inv_mul]; linarith) (Real.sqrt_nonneg 2)
  linarith

private abbrev Stage := {S : Finset ℕ // IsSidon (S : Set ℕ)}

private noncomputable def stage : ℕ → Stage
  | 0 => ⟨∅, by simp [IsSidon]⟩
  | j+1 =>
    let e := extend (stage j).1 (stage j).2 j
    ⟨e.choose,e.choose_spec.2.1⟩

private lemma stage_spec (j : ℕ) : (stage j).1 ⊆ (stage (j+1)).1 ∧
    ∃ N ≥ j, (1-1/((j:ℝ)+1))/Real.sqrt 2 ≤ sqrtPartialDensity (stage (j+1)).1 N := by
  have h := (extend (stage j).1 (stage j).2 j).choose_spec
  exact ⟨h.1,h.2.2⟩

private def blocks : Set ℕ := ⋃ j, ((stage j).1 : Set ℕ)

private lemma blocks_sidon : IsSidon blocks := by
  have mono : Monotone (fun j => (stage j).1) := monotone_nat_of_le_succ fun j => (stage_spec j).1
  rintro a ha b hb c hc d hd e
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp ha
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hb
  obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hc
  obtain ⟨l,hl⟩ := Set.mem_iUnion.mp hd
  let u := max (max i j) (max k l)
  exact (stage u).2 a (mono (show i ≤ u by dsimp [u]; omega) hi)
    b (mono (show j ≤ u by dsimp [u]; omega) hj)
    c (mono (show k ≤ u by dsimp [u]; omega) hk)
    d (mono (show l ≤ u by dsimp [u]; omega) hl) e

private lemma density_nonneg (A : Set ℕ) (n : ℕ) : 0 ≤ sqrtPartialDensity A n := by
  unfold sqrtPartialDensity
  positivity

private lemma density_bdd (A : Set ℕ) (hs : IsSidon A) :
    atTop.IsBoundedUnder (· ≤ ·) (sqrtPartialDensity A) :=
  isBoundedUnder_of ⟨3, sidon_bound A hs⟩

private lemma density_cobdd (A : Set ℕ) (f : Filter ℕ) [f.NeBot] :
    f.IsCoboundedUnder (· ≤ ·) (sqrtPartialDensity A) :=
  IsCoboundedUnder.of_frequently_ge (Eventually.of_forall (density_nonneg A)).frequently

private lemma dense_blocks : 1/Real.sqrt 2 ≤ sidonUpperDensity blocks := by
  choose n hn hd using fun j => (stage_spec j).2
  have ht : Tendsto n atTop atTop := tendsto_atTop_mono hn tendsto_id
  have hlim : Tendsto (fun j : ℕ => (1-1/((j:ℝ)+1))/Real.sqrt 2) atTop (𝓝 (1/Real.sqrt 2)) := by
    simpa using ((tendsto_const_nhds (x := (1:ℝ))).sub tendsto_one_div_add_atTop_nhds_zero_nat).div_const (Real.sqrt 2)
  have hle (j : ℕ) : (1-1/((j:ℝ)+1))/Real.sqrt 2 ≤ sqrtPartialDensity blocks (n j) := by
    refine (hd j).trans ?_
    unfold sqrtPartialDensity
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    exact_mod_cast Set.ncard_le_ncard (Set.inter_subset_inter_left _ (Set.subset_iUnion
      (fun i => ((stage i).1 : Set ℕ)) (j+1))) ((Set.finite_Icc _ _).subset Set.inter_subset_right)
  refine le_of_forall_lt_imp_le_of_dense fun b hb => ?_
  apply le_limsup_of_frequently_le _ (density_bdd blocks blocks_sidon)
  have hev := hlim.eventually (lt_mem_nhds hb)
  rw [frequently_atTop]
  intro m
  obtain ⟨j,hj⟩ := (hev.and (ht.eventually_ge_atTop m)).exists
  exact ⟨n j,hj.2,hj.1.le.trans (hle j)⟩

private noncomputable def count (A : Set ℕ) (n : ℕ) : ℕ := (A ∩ Set.Icc 1 n).ncard

private lemma count_zero (A : Set ℕ) : count A 0 = 0 := by simp [count]

private lemma count_succ (A : Set ℕ) (n : ℕ) [Decidable (n+1 ∈ A)] :
    count A (n+1) = count A n + if n+1 ∈ A then 1 else 0 := by
  classical
  by_cases h : n+1 ∈ A
  · rw [if_pos h]
    have eq : A ∩ Set.Icc 1 (n+1) = insert (n+1) (A ∩ Set.Icc 1 n) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_insert_iff]
      constructor
      · rintro ⟨hx,h1,h2⟩
        by_cases he : x=n+1
        · exact Or.inl he
        · exact Or.inr ⟨hx,h1,by omega⟩
      · rintro (rfl | ⟨hx,h1,h2⟩) <;> exact ⟨by assumption,by omega,by omega⟩
    unfold count
    rw [eq,Set.ncard_insert_of_notMem (by simp) ((Set.finite_Icc _ _).subset Set.inter_subset_right)]
  · rw [if_neg h,add_zero]
    unfold count
    congr 1
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Icc]
    constructor
    · rintro ⟨hx,h1,h2⟩
      have he : x ≠ n+1 := fun e => h (e ▸ hx)
      exact ⟨hx,h1,by omega⟩
    · rintro ⟨hx,h1,h2⟩
      exact ⟨hx,h1,by omega⟩

private def thin (A : Set ℕ) (t : ℝ) : Set ℕ :=
  {n | n ∈ A ∧ ⌊t * count A (n-1)⌋₊ < ⌊t * count A n⌋₊}

private lemma thin_count (A : Set ℕ) {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) (n : ℕ) :
    count (thin A t) n = ⌊t*count A n⌋₊ := by
  classical
  induction n with
  | zero => simp [count_zero]
  | succ n ih =>
    rw [count_succ (thin A t),ih]
    have mem : n+1 ∈ thin A t ↔ n+1 ∈ A ∧ ⌊t*count A n⌋₊ < ⌊t*count A (n+1)⌋₊ := by
      simp [thin]
    by_cases ha : n+1 ∈ A
    · have hc := count_succ A n
      rw [if_pos ha] at hc
      have h0 : 0 ≤ t * (count A n : ℝ) := by positivity
      have hf : ⌊t*count A n⌋₊ ≤ ⌊t*count A (n+1)⌋₊ := by
        apply Nat.floor_mono
        rw [hc]; push_cast; nlinarith
      have hg : ⌊t*count A (n+1)⌋₊ ≤ ⌊t*count A n⌋₊+1 := by
        rw [← Nat.floor_add_one h0]
        apply Nat.floor_mono
        rw [hc]; push_cast; nlinarith
      split_ifs with h
      · have := (mem.mp h).2; omega
      · have he : ¬⌊t*count A n⌋₊ < ⌊t*count A (n+1)⌋₊ := fun e => h (mem.mpr ⟨ha,e⟩)
        omega
    · rw [if_neg (fun hx => ha (mem.mp hx).1),count_succ A n,if_neg ha]
      simp

private lemma thin_density (A : Set ℕ) (hs : IsSidon A) {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) :
    sidonUpperDensity (thin A t) = t*sidonUpperDensity A := by
  let B := thin A t
  have sub : B ⊆ A := fun _ hx => hx.1
  have hsB : IsSidon B := fun a ha b hb c hc d hd => hs a (sub ha) b (sub hb) c (sub hc) d (sub hd)
  have hbounds (n : ℕ) :
      0 ≤ t * sqrtPartialDensity A n - sqrtPartialDensity B n ∧
      t * sqrtPartialDensity A n - sqrtPartialDensity B n ≤ 1 / Real.sqrt n := by
    change 0 ≤ t * ((count A n : ℝ)/_) - (count (thin A t) n : ℝ)/_ ∧ _
    change 0 ≤ t * ((count A n : ℝ)/Real.sqrt n) - (count (thin A t) n : ℝ)/Real.sqrt n ∧
      t * ((count A n : ℝ)/Real.sqrt n) - (count (thin A t) n : ℝ)/Real.sqrt n ≤ _
    rw [thin_count A ht ht',← mul_div_assoc,← sub_div]
    have hpos : 0 ≤ t*(count A n : ℝ) := by positivity
    exact ⟨div_nonneg (sub_nonneg.mpr (Nat.floor_le hpos)) (Real.sqrt_nonneg _),
      div_le_div_of_nonneg_right (by linarith [Nat.lt_floor_add_one (t*(count A n:ℝ))]) (Real.sqrt_nonneg _)⟩
  have her : Tendsto (fun n => t*sqrtPartialDensity A n - sqrtPartialDensity B n) atTop (𝓝 0) :=
    squeeze_zero (fun n => (hbounds n).1) (fun n => (hbounds n).2)
      (tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop))
  have hmap := (show Monotone (fun x : ℝ => t*x) from fun _ _ h => mul_le_mul_of_nonneg_left h ht).map_limsup_of_continuousAt
    (sqrtPartialDensity A) (continuous_const.mul continuous_id).continuousAt (density_bdd A hs) (density_cobdd A atTop)
  apply le_antisymm
  · unfold sidonUpperDensity
    rw [hmap]
    exact limsup_le_limsup (Eventually.of_forall fun n => sub_nonneg.mp (hbounds n).1)
      (density_cobdd B atTop) (isBoundedUnder_of ⟨t*3,fun n => mul_le_mul_of_nonneg_left (sidon_bound A hs n) ht⟩)
  · obtain ⟨φ,hφ,hφtop⟩ := exists_seq_tendsto_limsup (density_cobdd A atTop) (density_bdd A hs)
    have htend := (hφ.const_mul t).sub (her.comp hφtop)
    have hB : Tendsto (sqrtPartialDensity B ∘ φ) atTop (𝓝 (t*sidonUpperDensity A)) := by
      simpa [Function.comp_def,sidonUpperDensity] using htend
    exact hB.limsup_eq.symm.le.trans (hφtop.limsup_comp_le_limsup (density_cobdd B _) (density_bdd B hsB))

end OMA.Kruckeberg

theorem OMA.solution : type_of% @Erdos329.erdos_329.variants.kruckeberg_1961 := by
  open OMA.Kruckeberg Erdos329 in
    let t := (1 / Real.sqrt 2) / sidonUpperDensity blocks
    have hd := dense_blocks
    have hpos : 0 < sidonUpperDensity blocks := lt_of_lt_of_le (by positivity) hd
    have ht : 0 ≤ t := by dsimp [t]; positivity
    have h1 : t ≤ 1 := (div_le_one hpos).mpr hd
    refine ⟨thin blocks t, ?_, ?_⟩
    · intro a ha b hb c hc d hdd
      exact blocks_sidon a ha.1 b hb.1 c hc.1 d hdd.1
    · rw [thin_density blocks blocks_sidon ht h1]
      exact div_mul_cancel₀ _ hpos.ne'
