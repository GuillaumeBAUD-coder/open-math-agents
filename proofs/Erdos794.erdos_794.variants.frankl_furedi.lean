import FormalConjectures.ErdosProblems.«794»

-- Problem: Erdős Problem 794 — frankl furedi
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/794.lean:123 (declaration Erdos794.erdos_794.variants.frankl_furedi)
-- Credit: @senamakel (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Finset Filter

namespace OMA794

/-- base-6 digit -/
def dig (j x : ℕ) : ℕ := x / 6 ^ j % 6

lemma dig_lt (j x : ℕ) : dig j x < 6 := Nat.mod_lt _ (by norm_num)

lemma dig_eq_of_mod_eq {i j x y : ℕ} (hij : i < j) (h : x % 6 ^ j = y % 6 ^ j) :
    dig i x = dig i y := by
  have key : ∀ u : ℕ, dig i u = u % 6 ^ j / 6 ^ i % 6 := by
    intro u
    have e : 6 ^ j = 6 ^ i * 6 ^ (j - i) := by rw [← pow_add]; congr 1; omega
    rw [e, Nat.mod_mul_right_div_self, dig]
    have hd : 6 ∣ 6 ^ (j - i) := dvd_pow_self 6 (by omega)
    rw [Nat.mod_mod_of_dvd _ hd]
  rw [key x, key y, h]

lemma mod_pow_eq_of_dig {x y : ℕ} :
    ∀ k, (∀ i < k, dig i x = dig i y) → x % 6 ^ k = y % 6 ^ k := by
  intro k
  induction k with
  | zero => intro _; simp [Nat.mod_one]
  | succ k ih =>
    intro h
    rw [Nat.mod_pow_succ, Nat.mod_pow_succ, ih (fun i hi => h i (by omega))]
    have := h k (by omega)
    unfold dig at this
    rw [this]

lemma exists_dig_ne {x y : ℕ} (hxy : x ≠ y) : ∃ i, dig i x ≠ dig i y := by
  by_contra hc
  push Not at hc
  have hk : x < 6 ^ (x + y + 1) ∧ y < 6 ^ (x + y + 1) := by
    constructor
    · calc x < x + y + 1 := by omega
        _ < 6 ^ (x + y + 1) := Nat.lt_pow_self (by norm_num)
    · calc y < x + y + 1 := by omega
        _ < 6 ^ (x + y + 1) := Nat.lt_pow_self (by norm_num)
  have := mod_pow_eq_of_dig (x + y + 1) (fun i _ => hc i)
  rw [Nat.mod_eq_of_lt hk.1, Nat.mod_eq_of_lt hk.2] at this
  exact hxy this

/-- the ten blocks of the (6,3,2)-design, as sorted triples -/
def DS : Finset (ℕ × ℕ × ℕ) :=
  {(0,1,2),(0,1,3),(0,2,4),(0,3,5),(0,4,5),(1,2,5),(1,3,4),(1,4,5),(2,3,4),(2,3,5)}

def D10 : Finset (Finset ℕ) := DS.image (fun t => {t.1, t.2.1, t.2.2})

lemma DS_card : #DS = 10 := by decide

lemma DS_prop : ∀ t ∈ DS, t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ t.2.2 < 6 := by decide

lemma D10_inj : ∀ t ∈ DS, ∀ t' ∈ DS,
    ({t.1, t.2.1, t.2.2} : Finset ℕ) = {t'.1, t'.2.1, t'.2.2} → t = t' := by decide

lemma D10_card : ∀ s ∈ D10, #s = 3 := by decide

/-- the key finite check -/
def P (s : Finset ℕ) : Prop := s ∈ D10 ∨ #s = 1

instance : DecidablePred P := fun s => by unfold P; infer_instance

lemma finite_check' : ∀ w x y z : Fin 6, ¬ (w = x ∧ x = y ∧ y = z) →
    (if P {(w : ℕ), (x : ℕ), (y : ℕ)} then 1 else 0) +
      (if P {(w : ℕ), (x : ℕ), (z : ℕ)} then 1 else 0) +
      (if P {(w : ℕ), (y : ℕ), (z : ℕ)} then 1 else 0) +
      (if P {(x : ℕ), (y : ℕ), (z : ℕ)} then 1 else 0) ≤ 2 := by
  decide

lemma finite_check {w x y z : ℕ} (hw : w < 6) (hx : x < 6) (hy : y < 6) (hz : z < 6)
    (h : ¬ (w = x ∧ x = y ∧ y = z)) :
    (if P {w, x, y} then 1 else 0) + (if P {w, x, z} then 1 else 0) +
      (if P {w, y, z} then 1 else 0) + (if P {x, y, z} then 1 else 0) ≤ 2 := by
  have := finite_check' ⟨w, hw⟩ ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ (by
    intro h'; apply h; simp only [Fin.mk.injEq] at h'; exact h')
  simpa using this


lemma c1 {α : Type*} [DecidableEq α] (p : α → Prop) [DecidablePred p] (x : α) (s : Finset α) :
    #((insert x s).filter p) ≤ (if p x then 1 else 0) + #(s.filter p) := by
  rw [Finset.filter_insert]
  split_ifs
  · exact (Finset.card_insert_le _ _).trans (by omega)
  · omega

lemma c4 {α : Type*} [DecidableEq α] (p : α → Prop) [DecidablePred p] (a b c d : α) :
    #(({a, b, c, d} : Finset α).filter p) ≤
      (if p a then 1 else 0) + (if p b then 1 else 0) + (if p c then 1 else 0) +
        (if p d then 1 else 0) := by
  have h1 := c1 p a {b, c, d}
  have h2 := c1 p b {c, d}
  have h3 := c1 p c {d}
  have h4 : #(({d} : Finset α).filter p) ≤ (if p d then 1 else 0) := by
    rw [Finset.filter_singleton]; split_ifs <;> simp
  omega

noncomputable def H (n : ℕ) : Finset (Finset (Fin n)) := by
  classical
  exact (powersetCard 3 (univ : Finset (Fin n))).filter (fun e => ∃ j,
    (∀ i < j, ∀ u ∈ e, ∀ v ∈ e, dig i u.val = dig i v.val) ∧
      e.image (fun u => dig j u.val) ∈ D10)

lemma H_uniform (n : ℕ) : ∀ e ∈ H n, #e = 3 := by
  classical
  intro e he
  unfold H at he
  rw [Finset.mem_filter, Finset.mem_powersetCard] at he
  exact he.1.2

lemma image_card_one {n : ℕ} {e : Finset (Fin n)} (hne : e.Nonempty) (f : Fin n → ℕ)
    (h : ∀ u ∈ e, ∀ v ∈ e, f u = f v) : #(e.image f) = 1 := by
  obtain ⟨u0, hu0⟩ := hne
  rw [Finset.card_eq_one]
  refine ⟨f u0, ?_⟩
  ext y
  simp only [Finset.mem_image, Finset.mem_singleton]
  constructor
  · rintro ⟨u, hu, rfl⟩; exact h u hu u0 hu0
  · rintro rfl; exact ⟨u0, hu0, rfl⟩

lemma K4_free (n : ℕ) (S : Finset (Fin n)) (hS : #S = 4) :
    ∀ T : Finset (Finset (Fin n)), (∀ e ∈ T, e ∈ H n ∧ e ⊆ S) → #T ≤ 2 := by
  intro T hT
  obtain ⟨a, t, hat, rfl, ht⟩ := Finset.card_eq_succ.1 hS
  obtain ⟨b, c, d, hbc, hbd, hcd, rfl⟩ := Finset.card_eq_three.1 ht
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hat
  obtain ⟨hab, hac, had⟩ := hat
  set S : Finset (Fin n) := insert a {b, c, d} with hSdef
  have hQ : ∃ i, ∃ u ∈ S, ∃ v ∈ S, dig i u.val ≠ dig i v.val := by
    obtain ⟨i, hi⟩ := exists_dig_ne (Fin.val_injective.ne hab)
    exact ⟨i, a, by simp [hSdef], b, by simp [hSdef], hi⟩
  classical
  set j0 := Nat.find hQ with hj0
  have hspec := Nat.find_spec hQ
  rw [← hj0] at hspec
  set d0 : Fin n → ℕ := fun u => dig j0 u.val with hd0
  have hclaim : ∀ e ∈ H n, e ⊆ S → P (e.image d0) := by
    intro e he heS
    have he3 := H_uniform n e he
    unfold H at he
    rw [Finset.mem_filter] at he
    obtain ⟨-, j, hagree, himg⟩ := he
    have hne : e.Nonempty := by rw [← Finset.card_pos, he3]; norm_num
    rcases lt_trichotomy j j0 with hlt | heq | hgt
    · exfalso
      have hmin := Nat.find_min hQ (hj0 ▸ hlt)
      push Not at hmin
      have h1 := image_card_one hne (fun u => dig j u.val)
        (fun u hu v hv => hmin u (heS hu) v (heS hv))
      have h3 := D10_card _ himg
      omega
    · subst heq
      exact Or.inl himg
    · exact Or.inr (image_card_one hne d0 (fun u hu v hv => hagree j0 hgt u hu v hv))
  have hsub : T ⊆ (({{a, b, c}, {a, b, d}, {a, c, d}, {b, c, d}} : Finset (Finset (Fin n)))).filter
      (fun e => P (e.image d0)) := by
    intro e he
    obtain ⟨heH, heS⟩ := hT e he
    have he3 := H_uniform n e heH
    rw [Finset.mem_filter]
    refine ⟨?_, hclaim e heH heS⟩
    have hlt : #e < #S := by
      rw [he3, hSdef, Finset.card_insert_of_notMem (by simp [hab, hac, had]),
        Finset.card_eq_three.2 ⟨b, c, d, hbc, hbd, hcd, rfl⟩]
      omega
    obtain ⟨m, hmS, hme⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    have hsub2 : e ⊆ S.erase m := fun u hu =>
      Finset.mem_erase.2 ⟨fun h => hme (h ▸ hu), heS hu⟩
    have hcard : #(S.erase m) = 3 := by
      rw [Finset.card_erase_of_mem hmS, hSdef, Finset.card_insert_of_notMem (by simp [hab, hac, had]),
        Finset.card_eq_three.2 ⟨b, c, d, hbc, hbd, hcd, rfl⟩]
    have heq : e = S.erase m := Finset.eq_of_subset_of_card_le hsub2 (by rw [hcard, he3])
    rw [heq]
    simp only [hSdef, Finset.mem_insert, Finset.mem_singleton] at hmS
    rcases hmS with rfl | rfl | rfl | rfl
    · simp [hSdef, Finset.erase_insert_eq_erase, hab, hac, had, Finset.erase_eq_of_notMem]
    · simp [hSdef, Finset.erase_insert_of_ne, hab, hac, had, hbc, hbd, hcd, Ne.symm hab]
    · simp [hSdef, Finset.erase_insert_of_ne, hab, hac, had, hbc, hbd, hcd, Ne.symm hac,
        Ne.symm hbc]
    · simp [hSdef, Finset.erase_insert_of_ne, hab, hac, had, hbc, hbd, hcd, Ne.symm had,
        Ne.symm hbd, Ne.symm hcd]
  refine (Finset.card_le_card hsub).trans ((c4 _ _ _ _ _).trans ?_)
  have himg : ∀ x y z : Fin n, ({x, y, z} : Finset (Fin n)).image d0 = {d0 x, d0 y, d0 z} := by
    intro x y z; simp [Finset.image_insert, Finset.image_singleton]
  simp only [himg]
  refine finite_check (dig_lt _ _) (dig_lt _ _) (dig_lt _ _) (dig_lt _ _) ?_
  rintro ⟨h1, h2, h3⟩
  obtain ⟨u, hu, v, hv, huv⟩ := hspec
  simp only [hSdef, Finset.mem_insert, Finset.mem_singleton] at hu hv
  apply huv
  change d0 u = d0 v
  rcases hu with rfl | rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl | rfl <;> omega


/-- vertices of `Fin n` with residue `c` modulo `6 ^ j` and digit `p` at place `j` -/
noncomputable def F (n j c p : ℕ) : Finset (Fin n) :=
  (univ : Finset (Fin n)).filter (fun x => x.val % 6 ^ j = c ∧ dig j x.val = p)

lemma F_card (n j c p : ℕ) (hc : c < 6 ^ j) (hp : p < 6) : n / 6 ^ (j + 1) ≤ #(F n j c p) := by
  have hpos : 0 < 6 ^ j := by positivity
  have hval : ∀ k < n / 6 ^ (j + 1), c + p * 6 ^ j + k * 6 ^ (j + 1) < n := by
    intro k hk
    have h1 : (k + 1) * 6 ^ (j + 1) ≤ n := (Nat.le_div_iff_mul_le (by positivity)).1 hk
    have h2 : c + p * 6 ^ j < 6 ^ (j + 1) := by
      rw [pow_succ]
      nlinarith
    nlinarith
  rcases Nat.eq_zero_or_pos (n / 6 ^ (j + 1)) with h0 | h0
  · rw [h0]; exact Nat.zero_le _
  have hn : 0 < n := by
    have := hval 0 h0
    omega
  let g : ℕ → Fin n := fun k => if h : k < n / 6 ^ (j + 1) then ⟨_, hval k h⟩ else ⟨0, hn⟩
  have hform : ∀ k, c + p * 6 ^ j + k * 6 ^ (j + 1) = c + 6 ^ j * (p + 6 * k) := by
    intro k; rw [pow_succ]; ring
  calc n / 6 ^ (j + 1) = #(range (n / 6 ^ (j + 1))) := by simp
    _ ≤ #(F n j c p) := by
      refine Finset.card_le_card_of_injOn g ?_ ?_
      · intro k hk
        rw [Finset.coe_range, Set.mem_Iio] at hk
        simp only [F, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, g, dif_pos hk]
        rw [hform]
        constructor
        · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]
        · unfold dig
          rw [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hc, zero_add,
            Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hp]
      · intro k hk k' hk' hkk
        rw [Finset.coe_range, Set.mem_Iio] at hk hk'
        simp only [g, dif_pos hk, dif_pos hk', Fin.mk.injEq] at hkk
        have : k * 6 ^ (j + 1) = k' * 6 ^ (j + 1) := by omega
        exact Nat.eq_of_mul_eq_mul_right (by positivity) this

/-- the block of triples -/
noncomputable def Bk (n j c : ℕ) (t : ℕ × ℕ × ℕ) : Finset (Finset (Fin n)) :=
  ((F n j c t.1) ×ˢ (F n j c t.2.1) ×ˢ (F n j c t.2.2)).image
    (fun xyz => {xyz.1, xyz.2.1, xyz.2.2})

lemma Bk_inv {n j c : ℕ} {t : ℕ × ℕ × ℕ} {e : Finset (Fin n)} (he : e ∈ Bk n j c t) :
    (∀ u ∈ e, u.val % 6 ^ j = c) ∧ e.image (fun u => dig j u.val) = {t.1, t.2.1, t.2.2} ∧
      e.Nonempty := by
  unfold Bk at he
  obtain ⟨⟨x, y, z⟩, hxyz, rfl⟩ := Finset.mem_image.1 he
  simp only [Finset.mem_product, F, Finset.mem_filter, Finset.mem_univ, true_and] at hxyz
  obtain ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩, ⟨hz1, hz2⟩⟩ := hxyz
  refine ⟨?_, ?_, ⟨x, by simp⟩⟩
  · intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl <;> assumption
  · simp [Finset.image_insert, hx2, hy2, hz2]

lemma Bk_sub_H {n j c : ℕ} {t : ℕ × ℕ × ℕ} (ht : t ∈ DS) : Bk n j c t ⊆ H n := by
  classical
  intro e he
  obtain ⟨hres, himg, -⟩ := Bk_inv he
  have hdist := DS_prop t ht
  unfold Bk at he
  obtain ⟨⟨x, y, z⟩, hxyz, rfl⟩ := Finset.mem_image.1 he
  simp only [Finset.mem_product, F, Finset.mem_filter, Finset.mem_univ, true_and] at hxyz
  obtain ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩, ⟨hz1, hz2⟩⟩ := hxyz
  have hxy : x ≠ y := by rintro rfl; omega
  have hxz : x ≠ z := by rintro rfl; omega
  have hyz : y ≠ z := by rintro rfl; omega
  unfold H
  simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
  refine ⟨Finset.card_eq_three.2 ⟨x, y, z, hxy, hxz, hyz, rfl⟩, j, ?_, ?_⟩
  · intro i hi u hu v hv
    exact dig_eq_of_mod_eq hi ((hres u hu).trans (hres v hv).symm)
  · simp only at himg
    rw [himg]
    exact Finset.mem_image.2 ⟨t, ht, rfl⟩

lemma Bk_card {n j c : ℕ} {t : ℕ × ℕ × ℕ} (ht : t ∈ DS) :
    #(Bk n j c t) = #(F n j c t.1) * #(F n j c t.2.1) * #(F n j c t.2.2) := by
  have hdist := DS_prop t ht
  unfold Bk
  rw [Finset.card_image_of_injOn, Finset.card_product, Finset.card_product, mul_assoc]
  rintro ⟨x, y, z⟩ hxyz ⟨x', y', z'⟩ hxyz' heq
  simp only [Finset.coe_product, Set.mem_prod, F, Finset.coe_filter, Finset.mem_univ, true_and,
    Set.mem_setOf_eq] at hxyz hxyz'
  simp only at heq
  obtain ⟨⟨-, hx⟩, ⟨-, hy⟩, ⟨-, hz⟩⟩ := hxyz
  obtain ⟨⟨-, hx'⟩, ⟨-, hy'⟩, ⟨-, hz'⟩⟩ := hxyz'
  have m1 : x' ∈ ({x, y, z} : Finset (Fin n)) := by rw [heq]; simp
  have m2 : y' ∈ ({x, y, z} : Finset (Fin n)) := by rw [heq]; simp
  have m3 : z' ∈ ({x, y, z} : Finset (Fin n)) := by rw [heq]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at m1 m2 m3
  have e1 : x' = x := by
    rcases m1 with h | h | h <;> subst h <;> first | rfl | omega
  have e2 : y' = y := by
    rcases m2 with h | h | h <;> subst h <;> first | rfl | omega
  have e3 : z' = z := by
    rcases m3 with h | h | h <;> subst h <;> first | rfl | omega
  rw [e1, e2, e3]

lemma Bk_disj {n : ℕ} {j c j' c' : ℕ} {t t' : ℕ × ℕ × ℕ} (ht : t ∈ DS) (ht' : t' ∈ DS)
    {e : Finset (Fin n)} (he : e ∈ Bk n j c t) (he' : e ∈ Bk n j' c' t') :
    j = j' ∧ c = c' ∧ t = t' := by
  obtain ⟨r1, i1, ⟨u0, hu0⟩⟩ := Bk_inv he
  obtain ⟨r2, i2, -⟩ := Bk_inv he'
  have c3 : ∀ s ∈ DS, #({s.1, s.2.1, s.2.2} : Finset ℕ) = 3 := by decide
  have hjj : j = j' := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have h1 := image_card_one ⟨u0, hu0⟩ (fun u => dig j u.val)
        (fun u hu v hv => dig_eq_of_mod_eq hlt ((r2 u hu).trans (r2 v hv).symm))
      rw [i1, c3 t ht] at h1
      omega
    · have h1 := image_card_one ⟨u0, hu0⟩ (fun u => dig j' u.val)
        (fun u hu v hv => dig_eq_of_mod_eq hlt ((r1 u hu).trans (r1 v hv).symm))
      rw [i2, c3 t' ht'] at h1
      omega
  subst hjj
  refine ⟨rfl, (r1 u0 hu0).symm.trans (r2 u0 hu0), D10_inj t ht t' ht' (i1.symm.trans i2)⟩

lemma H_card_ge (n D : ℕ) :
    ∑ j ∈ range D, 6 ^ j * 10 * (n / 6 ^ (j + 1)) ^ 3 ≤ #(H n) := by
  classical
  let I : Finset (Σ _ : ℕ, ℕ × (ℕ × ℕ × ℕ)) := (range D).sigma (fun j => range (6 ^ j) ×ˢ DS)
  let B : (Σ _ : ℕ, ℕ × (ℕ × ℕ × ℕ)) → Finset (Finset (Fin n)) := fun i => Bk n i.1 i.2.1 i.2.2
  have hdisj : (I : Set (Σ _ : ℕ, ℕ × (ℕ × ℕ × ℕ))).PairwiseDisjoint B := by
    rintro ⟨j, c, t⟩ hi ⟨j', c', t'⟩ hi' hne
    simp only [I, Finset.coe_sigma, Set.mem_sigma_iff, Finset.coe_range, Set.mem_Iio,
      Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hi hi'
    rw [Function.onFun, Finset.disjoint_left]
    intro e he he'
    obtain ⟨rfl, rfl, rfl⟩ := Bk_disj hi.2.2 hi'.2.2 he he'
    exact hne rfl
  have hsub : I.biUnion B ⊆ H n := by
    intro e he
    obtain ⟨⟨j, c, t⟩, hi, he⟩ := Finset.mem_biUnion.1 he
    simp only [I, Finset.mem_sigma, Finset.mem_range, Finset.mem_product] at hi
    exact Bk_sub_H hi.2.2 he
  refine le_trans ?_ (Finset.card_le_card hsub)
  rw [Finset.card_biUnion hdisj, Finset.sum_sigma]
  refine Finset.sum_le_sum (fun j hj => ?_)
  calc 6 ^ j * 10 * (n / 6 ^ (j + 1)) ^ 3
      = ∑ _p ∈ range (6 ^ j) ×ˢ DS, (n / 6 ^ (j + 1)) ^ 3 := by
        rw [Finset.sum_const, Finset.card_product, Finset.card_range, DS_card, smul_eq_mul]
    _ ≤ ∑ p ∈ range (6 ^ j) ×ˢ DS, #(B ⟨j, p⟩) := by
        refine Finset.sum_le_sum (fun p hp => ?_)
        obtain ⟨c, t⟩ := p
        rw [Finset.mem_product, Finset.mem_range] at hp
        have hd := DS_prop t hp.2
        show _ ≤ #(Bk n j c t)
        rw [Bk_card hp.2, pow_succ, pow_two]
        have h1 := F_card n j c t.1 hp.1 (by omega)
        have h2 := F_card n j c t.2.1 hp.1 (by omega)
        have h3 := F_card n j c t.2.2 hp.1 hd.2.2
        exact Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3


lemma cube_lb (n k : ℕ) (hk : 0 < k) :
    ((n : ℝ) / k) ^ 3 - 3 * ((n : ℝ) / k) ^ 2 ≤ ((n / k : ℕ) : ℝ) ^ 3 := by
  set a : ℝ := (n : ℝ) / k with ha
  set m : ℝ := ((n / k : ℕ) : ℝ) with hm
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  have ha0 : 0 ≤ a := by positivity
  have hlt : a < m + 1 := by
    have h1 : n < n / k * k + k := Nat.lt_div_mul_add hk
    have h2 : (n : ℝ) < (m + 1) * k := by
      have : ((n : ℕ) : ℝ) < ((n / k * k + k : ℕ) : ℝ) := by exact_mod_cast h1
      push_cast at this
      rw [hm]; linarith
    rw [ha, div_lt_iff₀ (by exact_mod_cast hk)]
    exact h2
  rcases le_or_gt 1 a with h1 | h1
  · have h2 : a - 1 ≤ m := by linarith
    have h3 : (a - 1) ^ 3 ≤ m ^ 3 := pow_le_pow_left₀ (by linarith) h2 3
    nlinarith
  · have : a ^ 3 - 3 * a ^ 2 ≤ 0 := by nlinarith
    nlinarith [pow_nonneg hm0 3]

lemma term_eq (n j : ℕ) :
    (6 : ℝ) ^ j * 10 * (((n : ℝ) / ((6 ^ (j + 1) : ℕ) : ℝ)) ^ 3 -
        3 * ((n : ℝ) / ((6 ^ (j + 1) : ℕ) : ℝ)) ^ 2) =
      10 * (n : ℝ) ^ 3 / 216 * (1 / 36) ^ j - 30 * (n : ℝ) ^ 2 / 36 * (1 / 6) ^ j := by
  have hy : (0 : ℝ) < 6 ^ j := by positivity
  have e36 : ((1 : ℝ) / 36) ^ j = 1 / ((6 : ℝ) ^ j) ^ 2 := by
    rw [one_div_pow, ← pow_mul, mul_comm, pow_mul]; norm_num
  have e6 : ((1 : ℝ) / 6) ^ j = 1 / (6 : ℝ) ^ j := by rw [one_div_pow]
  rw [e36, e6]
  push_cast
  rw [pow_succ]
  field_simp
  ring

theorem main (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∃ H : Finset (Finset (Fin n)), H.IsUniform 3 ∧
      ¬ H.ContainsSubgraph 4 3 ∧ (2 / 7 - ε) * (n.choose 3 : ℝ) ≤ (H.card : ℝ) := by
  obtain ⟨D, hD⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 36 : ℝ) < 1)
  filter_upwards [eventually_ge_atTop ⌈12 / ε⌉₊] with n hn
  refine ⟨H n, H_uniform n, ?_, ?_⟩
  · rintro ⟨S, hS, hk⟩
    have h2 := K4_free n S hS _ (fun e he => Finset.mem_filter.1 he)
    exact absurd hk (not_le.2 (lt_of_le_of_lt h2 (by norm_num)))
  · have hnR : 12 / ε ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hεn : 12 ≤ ε * n := by
      rw [div_le_iff₀ hε] at hnR; linarith
    -- lower bound on #H
    have hc := H_card_ge n D
    have hcR : ∑ j ∈ range D, (6 : ℝ) ^ j * 10 * (((n / 6 ^ (j + 1) : ℕ) : ℝ)) ^ 3 ≤
        ((H n).card : ℝ) := by exact_mod_cast hc
    have hterm : ∀ j ∈ range D,
        10 * (n : ℝ) ^ 3 / 216 * (1 / 36) ^ j - 30 * (n : ℝ) ^ 2 / 36 * (1 / 6) ^ j ≤
          (6 : ℝ) ^ j * 10 * (((n / 6 ^ (j + 1) : ℕ) : ℝ)) ^ 3 := by
      intro j _
      rw [← term_eq]
      have := cube_lb n (6 ^ (j + 1)) (by positivity)
      have h6 : (0 : ℝ) ≤ (6 : ℝ) ^ j * 10 := by positivity
      exact mul_le_mul_of_nonneg_left this h6
    have hsum := Finset.sum_le_sum hterm
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
    have g36 : ∑ j ∈ range D, ((1 : ℝ) / 36) ^ j = (1 - (1 / 36) ^ D) * (36 / 35) := by
      rw [geom_sum_eq (by norm_num)]
      field_simp
      ring
    have g6 : ∑ j ∈ range D, ((1 : ℝ) / 6) ^ j ≤ 6 / 5 := by
      rw [geom_sum_eq (by norm_num)]
      have : (0 : ℝ) ≤ (1 / 6) ^ D := by positivity
      rw [div_le_iff_of_neg (by norm_num)]
      linarith
    rw [g36] at hsum
    have hHlow : (n : ℝ) ^ 3 / 21 * (1 - (1 / 36) ^ D) - (n : ℝ) ^ 2 ≤ ((H n).card : ℝ) := by
      have h2 : 30 * (n : ℝ) ^ 2 / 36 * ∑ j ∈ range D, ((1 : ℝ) / 6) ^ j ≤ (n : ℝ) ^ 2 := by
        have : 0 ≤ 30 * (n : ℝ) ^ 2 / 36 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left g6 this]
      nlinarith [hsum, hcR, h2]
    -- upper bound on choose
    have hch : (n.choose 3 : ℝ) ≤ (n : ℝ) ^ 3 / 6 := by
      have := Nat.choose_le_pow_div (α := ℝ) 3 n
      norm_num [Nat.factorial] at this
      exact this
    have hch0 : (0 : ℝ) ≤ n.choose 3 := Nat.cast_nonneg _
    have hrD : (0 : ℝ) ≤ (1 / 36) ^ D := by positivity
    rcases le_or_gt (2 / 7) ε with hbig | hsmall
    · have : (2 / 7 - ε) * (n.choose 3 : ℝ) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) hch0
      exact this.trans (Nat.cast_nonneg _)
    · have h1 : (2 / 7 - ε) * (n.choose 3 : ℝ) ≤ (2 / 7 - ε) * ((n : ℝ) ^ 3 / 6) :=
        mul_le_mul_of_nonneg_left hch (by linarith)
      have hn3 : (0 : ℝ) ≤ (n : ℝ) ^ 3 := by positivity
      have h3 : (n : ℝ) ^ 3 / 21 * (1 / 36) ^ D ≤ ε * (n : ℝ) ^ 3 / 12 := by
        have : (n : ℝ) ^ 3 * (1 / 36) ^ D ≤ (n : ℝ) ^ 3 * ε :=
          mul_le_mul_of_nonneg_left hD.le hn3
        nlinarith
      have h4 : (n : ℝ) ^ 2 ≤ ε * (n : ℝ) ^ 3 / 12 := by
        have : (n : ℝ) ^ 2 * 12 ≤ (n : ℝ) ^ 2 * (ε * n) :=
          mul_le_mul_of_nonneg_left hεn (by positivity)
        nlinarith
      nlinarith

end OMA794

theorem OMA.solution : type_of% @Erdos794.erdos_794.variants.frankl_furedi := by
  intro ε hε
  exact OMA794.main ε hε
