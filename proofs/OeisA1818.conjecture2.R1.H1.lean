import OMAReductions.R_OeisA1818_conjecture2_R1
import Mathlib.Tactic

-- Step OeisA1818.conjecture2.R1.H1: hypothesis H1 of reduction OeisA1818.conjecture2.R1
-- Credit: @green-notes

section Seq

def hSeq : ℕ → ℤ
  | 0 => 0
  | n + 1 =>
    if n = 0 then 1
    else - ∑ k ∈ (Finset.Ico 1 n).attach, (n.choose k.1 : ℤ) * hSeq k.1 * hSeq (n - k.1)
termination_by n => n
decreasing_by
  · exact Nat.lt_succ_of_lt (Finset.mem_Ico.mp k.2).2
  · have hk := (Finset.mem_Ico.mp k.2).1; omega

lemma hSeq_zero : hSeq 0 = 0 := by rw [hSeq]
lemma hSeq_one : hSeq 1 = 1 := by rw [hSeq]; simp
lemma hSeq_succ_succ (m : ℕ) :
    hSeq (m + 2) = - ∑ k ∈ Finset.Ico 1 (m + 1), ((m + 1).choose k : ℤ) * hSeq k * hSeq (m + 1 - k) := by
  rw [hSeq]
  simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
  rw [Finset.sum_attach (Finset.Ico 1 (m + 1)) (fun k => ((m + 1).choose k : ℤ) * hSeq k * hSeq (m + 1 - k))]

lemma hSeq_even : ∀ r : ℕ, hSeq (2 * r) = 0 := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    rcases r with _ | r
    · exact hSeq_zero
    · have h2 : 2 * (r + 1) = 2 * r + 2 := by omega
      rw [h2, hSeq_succ_succ]
      have hsum : ∑ k ∈ Finset.Ico 1 (2 * r + 1), ((2 * r + 1).choose k : ℤ) * hSeq k * hSeq (2 * r + 1 - k) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        rw [Finset.mem_Ico] at hk
        by_cases hk_even : k % 2 = 0
        · obtain ⟨q, hq⟩ : ∃ q, k = 2 * q := ⟨k / 2, by omega⟩
          have hq_lt : q < r + 1 := by omega
          rw [hq, ih q hq_lt]
          ring
        · obtain ⟨q, hq⟩ : ∃ q, 2 * r + 1 - k = 2 * q := ⟨(2 * r + 1 - k) / 2, by omega⟩
          have hq_lt : q < r + 1 := by omega
          rw [hq, ih q hq_lt]
          ring
      rw [hsum, neg_zero]

def wSeq : ℕ → ℤ
  | 0 => 1
  | n + 1 => wSeq n - ∑ k ∈ (Finset.Ico 1 (n + 1)).attach, (n.choose k.1 : ℤ) * hSeq k.1 * wSeq (n - k.1)
termination_by n => n
decreasing_by
  · omega
  · have hk := (Finset.mem_Ico.mp k.2).1; omega

lemma wSeq_zero : wSeq 0 = 1 := by rw [wSeq]

lemma wSeq_succ (n : ℕ) :
    wSeq (n + 1) = wSeq n - ∑ k ∈ (Finset.Ico 1 (n + 1)), (n.choose k : ℤ) * hSeq k * wSeq (n - k) := by
  rw [wSeq]
  rw [Finset.sum_attach (Finset.Ico 1 (n + 1)) (fun k => (n.choose k : ℤ) * hSeq k * wSeq (n - k))]

lemma wSeq_eq_hSeq : ∀ n : ℕ, 1 ≤ n → wSeq n = hSeq n := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | m
    · omega
    · rw [wSeq_succ, wSeq_zero, hSeq_one]
      simp
    · rw [wSeq_succ, hSeq_succ_succ]
      have htop := Finset.sum_Ico_succ_top (a := 1) (b := m + 1) (by omega)
        (fun k => ((m + 1).choose k : ℤ) * hSeq k * wSeq (m + 1 - k))
      rw [htop]
      have h1 : wSeq (m + 1) = hSeq (m + 1) := ih (m + 1) (by omega) (by omega)
      have hsub : m + 1 - (m + 1) = 0 := Nat.sub_self _
      rw [hsub, Nat.choose_self, Nat.cast_one, one_mul, wSeq_zero, mul_one, h1]
      have hcong : ∑ k ∈ Finset.Ico 1 (m + 1), ((m + 1).choose k : ℤ) * hSeq k * wSeq (m + 1 - k) =
          ∑ k ∈ Finset.Ico 1 (m + 1), ((m + 1).choose k : ℤ) * hSeq k * hSeq (m + 1 - k) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_Ico] at hk
        rw [ih (m + 1 - k) (by omega) (by omega)]
      rw [hcong]
      ring

lemma wSeq_even_pos (r : ℕ) (hr : 1 ≤ r) : wSeq (2 * r) = 0 := by
  rw [wSeq_eq_hSeq (2 * r) (by omega), hSeq_even]

end Seq

section Alg

variable {α : Type*} [DecidableEq α] {R : Type*} [CommRing R] [Inv R]

noncomputable def fVal (x : α → R) (a b : α) : R :=
  if a = b then 1 else (x a + x b) * (x a - x b)⁻¹

noncomputable def gVal (x : α → R) (a b : α) : R :=
  if a = b then 0 else (x a - x b)⁻¹

noncomputable def mVal (x : α → R) (a b : α) : R :=
  (2 * x a) * (2 * x b) * (gVal x a b * gVal x b a)

lemma inv_neg_of_unit (hinv : ∀ v : R, IsUnit v → v * v⁻¹ = 1) {u : R} (hu : IsUnit u) :
    (-u)⁻¹ = -u⁻¹ := by
  have h1 : u * u⁻¹ = 1 := hinv u hu
  have h2 : (-u) * (-u)⁻¹ = 1 := hinv (-u) hu.neg
  calc (-u)⁻¹ = (-u)⁻¹ * (u * u⁻¹) := by rw [h1, mul_one]
    _ = -((-u) * (-u)⁻¹) * u⁻¹ := by ring
    _ = -u⁻¹ := by rw [h2]; ring

lemma fVal_symm (hinv : ∀ v : R, IsUnit v → v * v⁻¹ = 1) {x : α → R}
    (hx : ∀ a b, a ≠ b → IsUnit (x a - x b)) {a b : α} (hab : a ≠ b) :
    fVal x b a = - fVal x a b := by
  simp only [fVal, if_neg hab, if_neg hab.symm]
  have hneg : x b - x a = -(x a - x b) := by ring
  rw [hneg, inv_neg_of_unit hinv (hx a b hab)]
  ring

lemma gVal_symm (hinv : ∀ v : R, IsUnit v → v * v⁻¹ = 1) {x : α → R}
    (hx : ∀ a b, a ≠ b → IsUnit (x a - x b)) {a b : α} (hab : a ≠ b) :
    gVal x b a = - gVal x a b := by
  simp only [gVal, if_neg hab, if_neg hab.symm]
  have hneg : x b - x a = -(x a - x b) := by ring
  rw [hneg, inv_neg_of_unit hinv (hx a b hab)]

lemma mul_cancel_unit {u a b : R} (hinv : ∀ v : R, IsUnit v → v * v⁻¹ = 1) (hu : IsUnit u)
    (heq : a * u = b * u) : a = b := by
  calc a = a * (u * u⁻¹) := by rw [hinv u hu, mul_one]
    _ = (a * u) * u⁻¹ := by ring
    _ = (b * u) * u⁻¹ := by rw [heq]
    _ = b * (u * u⁻¹) := by ring
    _ = b := by rw [hinv u hu, mul_one]

lemma fVal_insert (hinv : ∀ v : R, IsUnit v → v * v⁻¹ = 1) {x : α → R}
    (hx : ∀ a b, a ≠ b → IsUnit (x a - x b)) {a z b : α}
    (haz : a ≠ z) (hzb : z ≠ b) (hab : a ≠ b) :
    fVal x a z * fVal x z b = -1 + fVal x a b * (fVal x a z - fVal x b z) := by
  rw [fVal_symm hinv hx hzb]
  simp only [fVal, if_neg haz, if_neg hzb, if_neg hab]
  set d1 := x a - x z
  set d2 := x z - x b
  set d3 := x a - x b
  have u1 : IsUnit d1 := hx a z haz
  have u2 : IsUnit d2 := hx z b hzb
  have u3 : IsUnit d3 := hx a b hab
  apply mul_cancel_unit hinv ((u1.mul u2).mul u3)
  have h1 : d1⁻¹ * d1 = 1 := by rw [mul_comm]; exact hinv d1 u1
  have h2 : d2⁻¹ * d2 = 1 := by rw [mul_comm]; exact hinv d2 u2
  have h3 : d3⁻¹ * d3 = 1 := by rw [mul_comm]; exact hinv d3 u3
  calc
    (x a + x z) * d1⁻¹ * ((x z + x b) * d2⁻¹) * (d1 * d2 * d3)
      = (x a + x z) * (x z + x b) * (d1⁻¹ * d1) * (d2⁻¹ * d2) * d3 := by ring
    _ = (x a + x z) * (x z + x b) * d3 := by rw [h1, h2]; ring
    _ = (-(d1 * d2 * d3)) + (x a + x b) * ((x a + x z) * d2 + (x z + x b) * d1) := by
        dsimp [d1, d2, d3]; ring
    _ = (-(d1 * d2 * d3)) + (x a + x b) * (d3⁻¹ * d3) *
          ((x a + x z) * (d1⁻¹ * d1) * d2 + (x z + x b) * (d2⁻¹ * d2) * d1) := by
        rw [h1, h2, h3]; ring
    _ = (-1 + (x a + x b) * d3⁻¹ * ((x a + x z) * d1⁻¹ - -((x z + x b) * d2⁻¹))) * (d1 * d2 * d3) := by
        ring

lemma gVal_insert (hinv : ∀ v : R, IsUnit v → v * v⁻¹ = 1) {x : α → R}
    (hx : ∀ a b, a ≠ b → IsUnit (x a - x b)) {a z b : α}
    (haz : a ≠ z) (hzb : z ≠ b) (hab : a ≠ b) :
    gVal x a z * gVal x z b = gVal x a b * (gVal x a z - gVal x b z) := by
  rw [gVal_symm hinv hx hzb]
  simp only [gVal, if_neg haz, if_neg hzb, if_neg hab]
  set d1 := x a - x z
  set d2 := x z - x b
  set d3 := x a - x b
  have u1 : IsUnit d1 := hx a z haz
  have u2 : IsUnit d2 := hx z b hzb
  have u3 : IsUnit d3 := hx a b hab
  apply mul_cancel_unit hinv ((u1.mul u2).mul u3)
  have h1 : d1⁻¹ * d1 = 1 := by rw [mul_comm]; exact hinv d1 u1
  have h2 : d2⁻¹ * d2 = 1 := by rw [mul_comm]; exact hinv d2 u2
  have h3 : d3⁻¹ * d3 = 1 := by rw [mul_comm]; exact hinv d3 u3
  calc
    d1⁻¹ * d2⁻¹ * (d1 * d2 * d3) = (d1⁻¹ * d1) * (d2⁻¹ * d2) * d3 := by ring
    _ = d3 := by rw [h1, h2]; ring
    _ = (d3⁻¹ * d3) * ((d1⁻¹ * d1) * d2 + (d2⁻¹ * d2) * d1) := by
        rw [h1, h2, h3]
        dsimp [d1, d2, d3]; ring
    _ = d3⁻¹ * (d1⁻¹ - -d2⁻¹) * (d1 * d2 * d3) := by ring

lemma one_add_fVal_mul (hinv : ∀ v : R, IsUnit v → v * v⁻¹ = 1) {x : α → R}
    (hx : ∀ a b, a ≠ b → IsUnit (x a - x b)) {a b : α} (hab : a ≠ b) :
    1 + fVal x a b * fVal x b a = mVal x a b := by
  rw [fVal_symm hinv hx hab, mVal, gVal_symm hinv hx hab]
  simp only [fVal, gVal, if_neg hab]
  set d := x a - x b
  have u : IsUnit d := hx a b hab
  apply mul_cancel_unit hinv (u.mul u)
  have hd : d⁻¹ * d = 1 := by rw [mul_comm]; exact hinv d u
  calc
    (1 + (x a + x b) * d⁻¹ * -((x a + x b) * d⁻¹)) * (d * d)
      = d * d - (x a + x b) * (x a + x b) * (d⁻¹ * d) * (d⁻¹ * d) := by ring
    _ = d * d - (x a + x b) * (x a + x b) := by rw [hd]; ring
    _ = -(4 * x a * x b) := by dsimp [d]; ring
    _ = (2 * x a) * (2 * x b) * (d⁻¹ * d * -(d⁻¹ * d)) := by rw [hd]; ring
    _ = 2 * x a * (2 * x b) * (d⁻¹ * -d⁻¹) * (d * d) := by ring

end Alg

section Lists

variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
def consEmb (a : α) : List α ↪ List α :=
  ⟨fun l => a :: l, fun _ _ h => (List.cons.inj h).2⟩

omit [DecidableEq α] in
lemma consEmb_apply (a : α) (l : List α) : consEmb a l = a :: l := rfl

def ordLists (S : Finset α) : Finset (List α) :=
  if _ : S = ∅ then {[]}
  else S.attach.biUnion fun a =>
    (ordLists (S.erase a.1)).map (consEmb a.1)
termination_by S.card
decreasing_by exact Finset.card_erase_lt_of_mem a.2

lemma mem_ordLists : ∀ (S : Finset α) (l : List α), l ∈ ordLists S ↔ l.Nodup ∧ l.toFinset = S := by
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    intro l
    rw [ordLists]
    split_ifs with hS
    · subst hS
      simp only [Finset.mem_singleton]
      constructor
      · rintro rfl; simp
      · rintro ⟨_, hl⟩
        rw [← List.toFinset_eq_empty_iff]
        exact hl
    · simp only [Finset.mem_biUnion, Finset.mem_attach, Finset.mem_map, consEmb_apply, true_and]
      constructor
      · rintro ⟨⟨a, ha⟩, l', hl', rfl⟩
        have hsub : S.erase a ⊂ S := Finset.erase_ssubset ha
        rw [ih _ hsub] at hl'
        refine ⟨List.nodup_cons.mpr ⟨?_, hl'.1⟩, ?_⟩
        · intro hmem
          have hmem' := List.mem_toFinset.mpr hmem
          rw [hl'.2] at hmem'
          exact (Finset.notMem_erase a S) hmem'
        · rw [List.toFinset_cons, hl'.2, Finset.insert_erase ha]
      · rintro ⟨hnodup, hfin⟩
        rcases l with _ | ⟨a, l'⟩
        · simp at hfin
          exact (hS hfin.symm).elim
        · have ha : a ∈ S := by rw [← hfin]; simp
          have ha_not : a ∉ l' := (List.nodup_cons.mp hnodup).1
          have hsub : S.erase a ⊂ S := Finset.erase_ssubset ha
          refine ⟨⟨a, ha⟩, l', (ih _ hsub l').mpr ⟨(List.nodup_cons.mp hnodup).2, ?_⟩, rfl⟩
          ext x
          simp only [List.mem_toFinset, Finset.mem_erase, ne_eq]
          constructor
          · intro hx
            refine ⟨fun hxa => ha_not (hxa ▸ hx), ?_⟩
            rw [← hfin]
            simp [hx]
          · rintro ⟨hxa, hx⟩
            rw [← hfin, List.mem_toFinset, List.mem_cons] at hx
            exact hx.resolve_left hxa

lemma length_of_mem_ordLists {S : Finset α} {l : List α} (hl : l ∈ ordLists S) :
    l.length = S.card := by
  have ⟨hn, hf⟩ := (mem_ordLists S l).mp hl
  rw [← hn.dedup, ← List.card_toFinset, hf]

lemma ordLists_empty : ordLists (∅ : Finset α) = {[]} := by rw [ordLists]; simp

lemma ordLists_singleton (a : α) : ordLists ({a} : Finset α) = {[a]} := by
  ext l
  rw [mem_ordLists, Finset.mem_singleton]
  constructor
  · rintro ⟨hn, hf⟩
    have hlen : l.length = 1 := by rw [← hn.dedup, ← List.card_toFinset, hf]; simp
    rcases l with _ | ⟨x, _ | ⟨y, t⟩⟩ <;> simp at hlen
    have hx : x ∈ ({a} : Finset α) := by rw [← hf]; simp
    simp only [Finset.mem_singleton] at hx
    simp [hx]
  · rintro rfl; simp

lemma insert_list_props (z : α) : ∀ (l : List α) (k : ℕ),
    z ∉ l → k ≤ l.length →
    (l.take k ++ z :: l.drop k).erase z = l ∧ (l.take k ++ z :: l.drop k).idxOf z = k := by
  intro l
  induction l with
  | nil =>
    intro k _ hk
    simp at hk
    subst hk
    simp
  | cons a t ih =>
    intro k hz hk
    have haz : a ≠ z := fun h => hz (by simp [h])
    have hzt : z ∉ t := fun h => hz (by simp [h])
    cases k with
    | zero =>
      simp [List.erase_cons_head, List.idxOf_cons_self]
    | succ k' =>
      have hk' : k' ≤ t.length := by simpa using hk
      have ⟨he, hi⟩ := ih k' hzt hk'
      simp only [List.take_succ_cons, List.drop_succ_cons, List.cons_append]
      rw [List.erase_cons_tail (h := by simp [haz]), he,
        List.idxOf_cons_ne _ haz, hi]
      exact ⟨rfl, rfl⟩

lemma split_erase_idxOf (z : α) : ∀ (l' : List α),
    z ∈ l' → l'.Nodup →
    (l'.erase z).take (l'.idxOf z) ++ z :: (l'.erase z).drop (l'.idxOf z) = l' := by
  intro l'
  induction l' with
  | nil => intro h; simp at h
  | cons a t ih =>
    intro hz hnd
    have htnd : t.Nodup := (List.nodup_cons.mp hnd).2
    by_cases haz : a = z
    · subst haz
      simp [List.erase_cons_head, List.idxOf_cons_self]
    · have hzt : z ∈ t := (List.mem_cons.mp hz).resolve_left (Ne.symm haz)
      rw [List.erase_cons_tail (h := by simp [haz]), List.idxOf_cons_ne _ haz]
      simp only [List.take_succ_cons, List.drop_succ_cons, List.cons_append]
      rw [ih hzt htnd]

lemma ordLists_insert_sum {R : Type*} [AddCommMonoid R] {S : Finset α} {z : α} (hz : z ∉ S)
    (F : List α → R) :
    ∑ l' ∈ ordLists (insert z S), F l' =
      ∑ l ∈ ordLists S, ∑ k ∈ Finset.range (l.length + 1), F (l.take k ++ z :: l.drop k) := by
  have hsig :
      ∑ l ∈ ordLists S, ∑ k ∈ Finset.range (l.length + 1), F (l.take k ++ z :: l.drop k) =
        ∑ lk ∈ (ordLists S).sigma (fun l => Finset.range (l.length + 1)),
          F (lk.1.take lk.2 ++ z :: lk.1.drop lk.2) :=
    Finset.sum_sigma' (ordLists S) (fun l => Finset.range (l.length + 1))
      (fun l k => F (l.take k ++ z :: l.drop k))
  rw [hsig]
  refine Finset.sum_bij'
    (fun l' _ => ⟨l'.erase z, l'.idxOf z⟩)
    (fun lk _ => lk.1.take lk.2 ++ z :: lk.1.drop lk.2)
    ?_ ?_ ?_ ?_ ?_
  · intro l' hl'
    rw [mem_ordLists] at hl'
    have hzl : z ∈ l' := by rw [← List.mem_toFinset, hl'.2]; exact Finset.mem_insert_self z S
    have he_mem : l'.erase z ∈ ordLists S := by
      rw [mem_ordLists]
      refine ⟨hl'.1.erase z, ?_⟩
      ext x
      simp only [List.mem_toFinset]
      rw [hl'.1.mem_erase_iff, ← List.mem_toFinset, hl'.2, Finset.mem_insert]
      constructor
      · rintro ⟨hxz, rfl | hx⟩
        · exact (hxz rfl).elim
        · exact hx
      · intro hx
        exact ⟨fun h => hz (h ▸ hx), Or.inr hx⟩
    rw [Finset.mem_sigma]
    refine ⟨he_mem, Finset.mem_range.mpr ?_⟩
    have hlen : (l'.erase z).length + 1 = l'.length := by
      rw [List.length_erase_of_mem hzl]; have := List.length_pos_of_mem hzl; omega
    rw [hlen]
    exact List.idxOf_lt_length_of_mem hzl
  · rintro ⟨l, k⟩ hlk
    rw [Finset.mem_sigma, mem_ordLists, Finset.mem_range] at hlk
    dsimp only at hlk
    rw [mem_ordLists]
    have hzl : z ∉ l := fun h => hz (hlk.1.2 ▸ List.mem_toFinset.mpr h)
    have hperm : (l.take k ++ z :: l.drop k).Perm (z :: l) := by
      simpa using List.perm_append_comm_assoc (l.take k) [z] (l.drop k)
        |>.trans (by simp [List.take_append_drop])
    refine ⟨?_, ?_⟩
    · rw [hperm.nodup_iff, List.nodup_cons]
      exact ⟨hzl, hlk.1.1⟩
    · ext x
      simp only [List.mem_toFinset, Finset.mem_insert]
      rw [hperm.mem_iff, List.mem_cons, ← List.mem_toFinset, hlk.1.2]
  · intro l' hl'
    rw [mem_ordLists] at hl'
    have hzl : z ∈ l' := by rw [← List.mem_toFinset, hl'.2]; exact Finset.mem_insert_self z S
    exact split_erase_idxOf z l' hzl hl'.1
  · rintro ⟨l, k⟩ hlk
    rw [Finset.mem_sigma, mem_ordLists, Finset.mem_range] at hlk
    dsimp only at hlk
    have hzl : z ∉ l := fun h => hz (hlk.1.2 ▸ List.mem_toFinset.mpr h)
    have ⟨he, hi⟩ := insert_list_props z l k hzl (by omega)
    dsimp only
    refine Sigma.ext he (heq_of_eq hi)
  · intro l' hl'
    rw [mem_ordLists] at hl'
    have hzl : z ∈ l' := by rw [← List.mem_toFinset, hl'.2]; exact Finset.mem_insert_self z S
    dsimp only
    rw [split_erase_idxOf z l' hzl hl'.1]

lemma ordLists_rotate_sum {R : Type*} [AddCommMonoid R] (a : α) {S : Finset α} (ha : a ∈ S)
    (F : List α → R) :
    ∑ l' ∈ ordLists S, F l' =
      ∑ l ∈ ordLists (S.erase a), ∑ k ∈ Finset.range (l.length + 1),
        F (l.drop k ++ a :: l.take k) := by
  have hS : insert a (S.erase a) = S := Finset.insert_erase ha
  conv_lhs => rw [← hS, ordLists_insert_sum (Finset.notMem_erase a S) F]
  have hsig1 :
      ∑ l ∈ ordLists (S.erase a), ∑ k ∈ Finset.range (l.length + 1),
          F (l.take k ++ a :: l.drop k) =
        ∑ lk ∈ (ordLists (S.erase a)).sigma (fun l => Finset.range (l.length + 1)),
          F (lk.1.take lk.2 ++ a :: lk.1.drop lk.2) :=
    Finset.sum_sigma' _ _ _
  have hsig2 :
      ∑ l ∈ ordLists (S.erase a), ∑ k ∈ Finset.range (l.length + 1),
          F (l.drop k ++ a :: l.take k) =
        ∑ lk ∈ (ordLists (S.erase a)).sigma (fun l => Finset.range (l.length + 1)),
          F (lk.1.drop lk.2 ++ a :: lk.1.take lk.2) :=
    Finset.sum_sigma' _ _ _
  rw [hsig1, hsig2]
  refine Finset.sum_bij'
    (fun lk _ => ⟨lk.1.drop lk.2 ++ lk.1.take lk.2, lk.1.length - lk.2⟩)
    (fun lk _ => ⟨lk.1.drop lk.2 ++ lk.1.take lk.2, lk.1.length - lk.2⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨l, k⟩ hlk
    rw [Finset.mem_sigma, mem_ordLists, Finset.mem_range] at hlk ⊢
    dsimp only at hlk ⊢
    have hperm : (l.drop k ++ l.take k).Perm l :=
      (List.perm_append_comm).trans (by simp [List.take_append_drop])
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact hperm.nodup_iff.mpr hlk.1.1
    · ext x; simp only [List.mem_toFinset]; rw [hperm.mem_iff, ← List.mem_toFinset, hlk.1.2]
    · rw [hperm.length_eq]; omega
  · rintro ⟨l, k⟩ hlk
    rw [Finset.mem_sigma, mem_ordLists, Finset.mem_range] at hlk ⊢
    dsimp only at hlk ⊢
    have hperm : (l.drop k ++ l.take k).Perm l :=
      (List.perm_append_comm).trans (by simp [List.take_append_drop])
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact hperm.nodup_iff.mpr hlk.1.1
    · ext x; simp only [List.mem_toFinset]; rw [hperm.mem_iff, ← List.mem_toFinset, hlk.1.2]
    · rw [hperm.length_eq]; omega
  · rintro ⟨l, k⟩ hlk
    rw [Finset.mem_sigma, Finset.mem_range] at hlk
    dsimp only at hlk
    have hlen : (l.drop k).length = l.length - k := List.length_drop
    have hlen2 : (l.drop k ++ l.take k).length = l.length := by
      rw [List.length_append, List.length_drop, List.length_take]; omega
    have hd : (l.drop k ++ l.take k).drop (l.length - k) = l.take k := by
      rw [List.drop_append_of_le_length (by omega), ← hlen, List.drop_length, List.nil_append]
    have ht : (l.drop k ++ l.take k).take (l.length - k) = l.drop k := by
      rw [List.take_append_of_le_length (by omega), ← hlen, List.take_length]
    refine Sigma.ext ?_ (heq_of_eq ?_)
    · dsimp only; rw [hd, ht, List.take_append_drop]
    · dsimp only; rw [hlen2]; omega
  · rintro ⟨l, k⟩ hlk
    rw [Finset.mem_sigma, Finset.mem_range] at hlk
    dsimp only at hlk
    have hlen : (l.drop k).length = l.length - k := List.length_drop
    have hlen2 : (l.drop k ++ l.take k).length = l.length := by
      rw [List.length_append, List.length_drop, List.length_take]; omega
    have hd : (l.drop k ++ l.take k).drop (l.length - k) = l.take k := by
      rw [List.drop_append_of_le_length (by omega), ← hlen, List.drop_length, List.nil_append]
    have ht : (l.drop k ++ l.take k).take (l.length - k) = l.drop k := by
      rw [List.take_append_of_le_length (by omega), ← hlen, List.take_length]
    refine Sigma.ext ?_ (heq_of_eq ?_)
    · dsimp only; rw [hd, ht, List.take_append_drop]
    · dsimp only; rw [hlen2]; omega
  · rintro ⟨l, k⟩ hlk
    rw [Finset.mem_sigma, Finset.mem_range] at hlk
    dsimp only at hlk
    have hlen : (l.drop k).length = l.length - k := List.length_drop
    have hd : (l.drop k ++ l.take k).drop (l.length - k) = l.take k := by
      rw [List.drop_append_of_le_length (by omega), ← hlen, List.drop_length, List.nil_append]
    have ht : (l.drop k ++ l.take k).take (l.length - k) = l.drop k := by
      rw [List.take_append_of_le_length (by omega), ← hlen, List.take_length]
    dsimp only
    rw [ht, hd]

end Lists

section PathCycle

variable {α : Type*} [DecidableEq α] {R : Type*} [CommRing R] [Inv R]

def chainProd (w : α → α → R) : α → List α → R
  | _, [] => 1
  | cur, b :: l => w cur b * chainProd w b l

def pathProd (w : α → α → R) : List α → R
  | [] => 1
  | a :: l => chainProd w a l

def cycChain (w : α → α → R) (endPt : α) : α → List α → R
  | cur, [] => w cur endPt
  | cur, b :: l => w cur b * cycChain w endPt b l

def tailCyc (w : α → α → R) (endPt : α) : List α → R
  | [] => 1
  | b :: l => cycChain w endPt b l

omit [DecidableEq α] [Inv R] in
lemma chainProd_append (w : α → α → R) : ∀ (cur : α) (l1 l2 : List α),
    chainProd w cur (l1 ++ l2) = chainProd w cur l1 * chainProd w (l1.getLastD cur) l2
  | cur, [], l2 => by simp [chainProd]
  | cur, a :: l1, l2 => by
    simp only [List.cons_append, chainProd]
    rw [chainProd_append w a l1 l2]
    have hlast : (a :: l1).getLastD cur = l1.getLastD a := by
      cases l1 <;> simp [List.getLastD]
    rw [hlast]
    ring

omit [DecidableEq α] [Inv R] in
lemma cycChain_append (w : α → α → R) (endPt : α) : ∀ (cur : α) (l1 l2 : List α),
    cycChain w endPt cur (l1 ++ l2) = chainProd w cur l1 * cycChain w endPt (l1.getLastD cur) l2
  | cur, [], l2 => by simp [chainProd]
  | cur, a :: l1, l2 => by
    simp only [List.cons_append, cycChain, chainProd]
    rw [cycChain_append w endPt a l1 l2]
    have hlast : (a :: l1).getLastD cur = l1.getLastD a := by
      cases l1 <;> simp [List.getLastD]
    rw [hlast]
    ring

omit [DecidableEq α] [Inv R] in
lemma cycChain_eq_chainProd_mul_tailCyc (w : α → α → R) (endPt : α) (cur : α)
    (l1 l2 : List α) :
    cycChain w endPt cur (l1 ++ l2) =
      chainProd w cur l1 * w (l1.getLastD cur) (l2.headD endPt) * tailCyc w endPt l2 := by
  rw [cycChain_append]
  cases l2 with
  | nil => simp [cycChain, tailCyc, List.headD]
  | cons b t => simp [cycChain, tailCyc, List.headD]; ring

omit [DecidableEq α] [Inv R] in
lemma cycChain_insert_at (w : α → α → R) (endPt cur : α) (z : α) (l1 l2 : List α) :
    cycChain w endPt cur (l1 ++ z :: l2) =
      chainProd w cur l1 * w (l1.getLastD cur) z * w z (l2.headD endPt) * tailCyc w endPt l2 := by
  rw [cycChain_append]
  simp only [cycChain]
  cases l2 with
  | nil => simp [cycChain, tailCyc, List.headD]; ring
  | cons b t => simp [cycChain, tailCyc, List.headD]; ring

omit [DecidableEq α] [Inv R] in
lemma pathProd_drop_cons_take (w : α → α → R) (a : α) : ∀ (l1 l2 : List α),
    pathProd w (l2 ++ a :: l1) = chainProd w a l1 * tailCyc w a l2
  | l1, [] => by simp [pathProd, tailCyc]
  | l1, b :: t => by
    simp only [List.cons_append, pathProd, tailCyc]
    have hcy : cycChain w a b (t ++ []) = cycChain w a b t := by simp
    rw [chainProd_append, ← hcy, cycChain_append]
    simp only [cycChain, chainProd]
    ring

omit [DecidableEq α] [Inv R] in
lemma getLastD_eq_getLast' : ∀ {l : List α} (d : α) (hl : l ≠ []),
    l.getLastD d = l.getLast hl
  | [], _, hl => (hl rfl).elim
  | [x], _, _ => by simp [List.getLastD]
  | a :: b :: t, d, _ => by
    have hcons : (a :: b :: t).getLastD d = (b :: t).getLastD a := rfl
    rw [hcons, getLastD_eq_getLast' a (List.cons_ne_nil b t)]
    simp

omit [DecidableEq α] [Inv R] in
lemma pathProd_insert_mid (w : α → α → R) (z : α) : ∀ {l1 l2 : List α} (h1 : l1 ≠ []) (h2 : l2 ≠ []),
    pathProd w (l1 ++ z :: l2) =
      pathProd w l1 * w (l1.getLast h1) z * w z (l2.head h2) * pathProd w l2
  | [], _, h1, _ => (h1 rfl).elim
  | _, [], _, h2 => (h2 rfl).elim
  | a :: t1, b :: t2, h1, _ => by
    simp only [List.cons_append, pathProd]
    rw [chainProd_append]
    have hgd : t1.getLastD a = (a :: t1).getLast h1 :=
      Eq.trans (by cases t1 <;> simp [List.getLastD] : t1.getLastD a = (a :: t1).getLastD a)
        (getLastD_eq_getLast' a h1)
    simp only [chainProd, List.head_cons, hgd]
    ring

omit [DecidableEq α] [Inv R] in
lemma pathProd_split_mid (w : α → α → R) : ∀ {l1 l2 : List α} (h1 : l1 ≠ []) (h2 : l2 ≠ []),
    pathProd w (l1 ++ l2) = pathProd w l1 * w (l1.getLast h1) (l2.head h2) * pathProd w l2
  | [], _, h1, _ => (h1 rfl).elim
  | _, [], _, h2 => (h2 rfl).elim
  | a :: t1, b :: t2, h1, _ => by
    simp only [List.cons_append, pathProd]
    rw [chainProd_append]
    have hgd : t1.getLastD a = (a :: t1).getLast h1 :=
      Eq.trans (by cases t1 <;> simp [List.getLastD] : t1.getLastD a = (a :: t1).getLastD a)
        (getLastD_eq_getLast' a h1)
    simp only [chainProd, List.head_cons, hgd]
    ring

omit [DecidableEq α] [Inv R] in
lemma getLast_take_eq {l : List α} {i : ℕ} (hi : i < l.length) (hne : l.take (i + 1) ≠ []) :
    (l.take (i + 1)).getLast hne = l[i] := by
  have hlen : (l.take (i + 1)).length = i + 1 := List.length_take_of_le (by omega)
  rw [List.getLast_eq_getElem]
  simp only [hlen, Nat.add_sub_cancel]
  exact (List.getElem_take' hi (by omega)).symm

omit [DecidableEq α] [Inv R] in
lemma head_drop_eq {l : List α} {k : ℕ} (hk : k < l.length) (hne : l.drop k ≠ []) :
    (l.drop k).head hne = l[k] := by
  simp [List.head_eq_getElem, List.getElem_drop]

omit [DecidableEq α] [Inv R] in
lemma getLastD_take_eq {a : α} {l : List α} {k : ℕ} (hk : k ≤ l.length) :
    (l.take k).getLastD a = if h : 1 ≤ k then l[k - 1]'(by omega) else a := by
  cases k with
  | zero => simp [List.getLastD]
  | succ k' =>
    have hk' : k' < l.length := by omega
    have hne : l.take (k' + 1) ≠ [] := by
      intro h; have := congr_arg List.length h; rw [List.length_take_of_le hk] at this; simp at this
    rw [getLastD_eq_getLast' a hne, getLast_take_eq hk' hne]
    simp

omit [DecidableEq α] [Inv R] in
lemma headD_drop_eq {a : α} {l : List α} {k : ℕ} (hk : k ≤ l.length) :
    (l.drop k).headD a = if h : k < l.length then l[k] else a := by
  by_cases hklt : k < l.length
  · have hne : l.drop k ≠ [] := by
      intro h; have hlen_d := congr_arg List.length h; simp only [List.length_drop, List.length_nil] at hlen_d; omega
    cases hd : l.drop k with
    | nil => exact (hne hd).elim
    | cons b t =>
      simp only [List.headD, dif_pos hklt]
      have hh := head_drop_eq hklt hne
      rw [← hh]
      simp [hd]
  · have hk_eq : k = l.length := by omega
    subst hk_eq
    simp [List.drop_length, List.headD]

noncomputable def pathSum (w : α → α → R) (S : Finset α) : R :=
  ∑ l ∈ ordLists S, pathProd w l

noncomputable def cycSum (w : α → α → R) (a : α) (U : Finset α) : R :=
  ∑ l ∈ ordLists U, cycChain w a a l

lemma pathSum_singleton (w : α → α → R) (a : α) : pathSum w {a} = 1 := by
  simp [pathSum, ordLists_singleton, pathProd, chainProd]

lemma cycSum_empty (w : α → α → R) (a : α) : cycSum w a ∅ = w a a := by
  simp [cycSum, ordLists_empty, cycChain]

lemma cycSum_singleton (w : α → α → R) (a b : α) : cycSum w a {b} = w a b * w b a := by
  simp [cycSum, ordLists_singleton, cycChain]

lemma pathSum_insert (hinv : ∀ v : R, IsUnit v → v * v⁻¹ = 1) {x : α → R}
    (hx : ∀ a b, a ≠ b → IsUnit (x a - x b)) {S : Finset α} (hS : S.Nonempty)
    {z : α} (hz : z ∉ S) :
    pathSum (fVal x) (insert z S) =
      - ∑ A ∈ S.powerset.filter (fun A => A.Nonempty ∧ A ≠ S),
          pathSum (fVal x) A * pathSum (fVal x) (S \ A) := by
  rw [pathSum, ordLists_insert_sum hz]
  have hinner : ∀ l ∈ ordLists S,
      ∑ k ∈ Finset.range (l.length + 1), pathProd (fVal x) (l.take k ++ z :: l.drop k) =
        - ∑ i ∈ Finset.range (l.length - 1),
            pathProd (fVal x) (l.take (i + 1)) * pathProd (fVal x) (l.drop (i + 1)) := by
    intro l hl
    have ⟨hnodup, hfin⟩ := (mem_ordLists S l).mp hl
    have hm_pos : 0 < l.length := by rw [length_of_mem_ordLists hl]; exact hS.card_pos
    have hzl : z ∉ l := fun h => hz (hfin ▸ List.mem_toFinset.mpr h)
    rcases l with _ | ⟨v0, vt⟩
    · simp at hm_pos
    set l := v0 :: vt
    have hlen : l.length = vt.length + 1 := rfl
    rw [hlen, Finset.sum_range_succ, Finset.sum_range_succ']
    simp only [List.take_zero, List.drop_zero, List.nil_append, Nat.add_sub_cancel]
    have htake_all : l.take (vt.length + 1) = l := by rw [← hlen]; exact List.take_length
    have hdrop_all : l.drop (vt.length + 1) = [] := List.drop_length
    rw [htake_all, hdrop_all]
    have h0_ne : z ≠ v0 := fun h => hzl (by simp [l, h])
    have h0_prod : pathProd (fVal x) (z :: l) = - (fVal x v0 z * pathProd (fVal x) l) := by
      simp only [pathProd, chainProd, l]
      rw [fVal_symm hinv hx h0_ne.symm]
      ring
    have hm_prod : pathProd (fVal x) (l ++ [z]) =
        pathProd (fVal x) l * fVal x (l[vt.length]' (by simp [l])) z := by
      simp only [pathProd, l, List.cons_append]
      rw [chainProd_append]
      simp only [chainProd, mul_one]
      have hlast : vt.getLastD v0 = (v0 :: vt)[vt.length] := by
        cases vt using List.reverseRecOn with
        | nil => simp [List.getLastD]
        | append_singleton u y =>
          simp only [List.length_append, List.length_singleton,
            getLastD_eq_getLast' v0 (List.append_ne_nil_of_right_ne_nil u (List.cons_ne_nil y []))]
          rw [List.getLast_append_singleton]
          simp
      rw [hlast]
    let gv : ℕ → R := fun i => if h : i < l.length then fVal x (l[i]) z else 0
    have hmid :
        ∑ i ∈ Finset.range vt.length,
          pathProd (fVal x) (l.take (i + 1) ++ z :: l.drop (i + 1)) =
        (- ∑ i ∈ Finset.range vt.length,
          pathProd (fVal x) (l.take (i + 1)) * pathProd (fVal x) (l.drop (i + 1))) +
        pathProd (fVal x) l * ∑ i ∈ Finset.range vt.length, (gv i - gv (i + 1)) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      have hne1 : l.take (i + 1) ≠ [] := by
        intro h; have := congr_arg List.length h; rw [List.length_take_of_le (by omega)] at this; simp at this
      have hne2 : l.drop (i + 1) ≠ [] := by
        intro h
        have hlen_d := congr_arg List.length h
        simp only [List.length_drop, List.length_nil] at hlen_d
        omega
      have hlast : (l.take (i + 1)).getLast hne1 = l[i]'(by omega) := getLast_take_eq (by omega) hne1
      have hhead : (l.drop (i + 1)).head hne2 = l[i + 1]'(by omega) := head_drop_eq (by omega) hne2
      rw [pathProd_insert_mid (fVal x) z hne1 hne2, hlast, hhead]
      have hsplit := pathProd_split_mid (fVal x) hne1 hne2
      rw [List.take_append_drop, hlast, hhead] at hsplit
      have hu_ne_z : l[i]'(by omega) ≠ z := fun h => hzl (h ▸ List.getElem_mem _)
      have hz_ne_v : z ≠ l[i + 1]'(by omega) := fun h => hzl (h.symm ▸ List.getElem_mem _)
      have hu_ne_v : l[i]'(by omega) ≠ l[i + 1]'(by omega) := by
        intro h
        have hinj := hnodup.getElem_inj_iff.mp h
        omega
      have hins := fVal_insert hinv hx hu_ne_z hz_ne_v hu_ne_v
      have hgv1 : gv i = fVal x (l[i]'(by omega)) z := dif_pos (by omega)
      have hgv2 : gv (i + 1) = fVal x (l[i + 1]'(by omega)) z := dif_pos (by omega)
      rw [hgv1, hgv2]
      calc
        pathProd (fVal x) (l.take (i + 1)) * fVal x (l[i]) z * fVal x z (l[i + 1]) * pathProd (fVal x) (l.drop (i + 1))
          = (pathProd (fVal x) (l.take (i + 1)) * pathProd (fVal x) (l.drop (i + 1))) *
              (fVal x (l[i]) z * fVal x z (l[i + 1])) := by ring
        _ = (pathProd (fVal x) (l.take (i + 1)) * pathProd (fVal x) (l.drop (i + 1))) *
              (-1 + fVal x (l[i]) (l[i + 1]) * (fVal x (l[i]) z - fVal x (l[i + 1]) z)) := by rw [hins]
        _ = -(pathProd (fVal x) (l.take (i + 1)) * pathProd (fVal x) (l.drop (i + 1))) +
              (pathProd (fVal x) (l.take (i + 1)) * fVal x (l[i]) (l[i + 1]) * pathProd (fVal x) (l.drop (i + 1))) *
                (fVal x (l[i]) z - fVal x (l[i + 1]) z) := by ring
        _ = -(pathProd (fVal x) (l.take (i + 1)) * pathProd (fVal x) (l.drop (i + 1))) +
              pathProd (fVal x) l * (fVal x (l[i]) z - fVal x (l[i + 1]) z) := by rw [← hsplit]
    have htel : ∑ i ∈ Finset.range vt.length, (gv i - gv (i + 1)) = gv 0 - gv vt.length :=
      Finset.sum_range_sub' gv vt.length
    have hgv0 : gv 0 = fVal x v0 z := by simp [gv, l]
    have hgvm : gv vt.length = fVal x (l[vt.length]'(by simp [l])) z := dif_pos (by simp [l])
    rw [h0_prod, hm_prod, hmid, htel, hgv0, hgvm]
    ring
  rw [Finset.sum_congr rfl hinner, Finset.sum_neg_distrib]
  congr 1
  have hL :
      ∑ l ∈ ordLists S, ∑ i ∈ Finset.range (l.length - 1),
          pathProd (fVal x) (l.take (i + 1)) * pathProd (fVal x) (l.drop (i + 1)) =
        ∑ li ∈ (ordLists S).sigma (fun l => Finset.range (l.length - 1)),
          pathProd (fVal x) (li.1.take (li.2 + 1)) * pathProd (fVal x) (li.1.drop (li.2 + 1)) :=
    Finset.sum_sigma' _ _ _
  have hR_prod : ∀ A ∈ S.powerset.filter (fun A => A.Nonempty ∧ A ≠ S),
      pathSum (fVal x) A * pathSum (fVal x) (S \ A) =
        ∑ l1 ∈ ordLists A, ∑ l2 ∈ ordLists (S \ A), pathProd (fVal x) l1 * pathProd (fVal x) l2 := by
    intro A _
    simp only [pathSum, Finset.sum_mul_sum]
  rw [hL, Finset.sum_congr rfl hR_prod]
  let P := S.powerset.filter (fun A => A.Nonempty ∧ A ≠ S)
  let Q := P.sigma (fun A => ordLists A ×ˢ ordLists (S \ A))
  have hR :
      ∑ A ∈ P, ∑ l1 ∈ ordLists A, ∑ l2 ∈ ordLists (S \ A),
          pathProd (fVal x) l1 * pathProd (fVal x) l2 =
        ∑ q ∈ Q, pathProd (fVal x) q.2.1 * pathProd (fVal x) q.2.2 := by
    rw [← Finset.sum_sigma' P (fun A => ordLists A ×ˢ ordLists (S \ A))
      (fun _ p => pathProd (fVal x) p.1 * pathProd (fVal x) p.2)]
    apply Finset.sum_congr rfl
    intro A _
    exact (Finset.sum_product' (ordLists A) (ordLists (S \ A))
      (fun l1 l2 => pathProd (fVal x) l1 * pathProd (fVal x) l2)).symm
  rw [hR]
  refine Finset.sum_bij'
    (fun li _ => ⟨(li.1.take (li.2 + 1)).toFinset, li.1.take (li.2 + 1), li.1.drop (li.2 + 1)⟩)
    (fun q _ => ⟨q.2.1 ++ q.2.2, q.2.1.length - 1⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨l, i⟩ hli
    rw [Finset.mem_sigma, mem_ordLists, Finset.mem_range] at hli
    dsimp only at hli
    have hl1_nd : (l.take (i + 1)).Nodup := hli.1.1.sublist (List.take_sublist _ _)
    have hl2_nd : (l.drop (i + 1)).Nodup := hli.1.1.sublist (List.drop_sublist _ _)
    have hdisj : List.Disjoint (l.take (i + 1)) (l.drop (i + 1)) := by
      have hnd := hli.1.1
      rw [← List.take_append_drop (i + 1) l, List.nodup_append] at hnd
      intro y hy1 hy2
      exact hnd.2.2 y hy1 y hy2 rfl
    have hA_sub : (l.take (i + 1)).toFinset ⊆ S := by
      rw [← hli.1.2]
      intro y hy
      rw [List.mem_toFinset] at hy ⊢
      exact List.mem_of_mem_take hy
    have hA_ne : (l.take (i + 1)).toFinset.Nonempty := by
      have hlen : (l.take (i + 1)).length = i + 1 := List.length_take_of_le (by omega)
      have hcard : (l.take (i + 1)).toFinset.card = i + 1 := by
        rw [List.card_toFinset, hl1_nd.dedup, hlen]
      exact Finset.card_pos.mp (by omega)
    have hA_lt : (l.take (i + 1)).toFinset ≠ S := by
      intro heq
      have hlen1 : (l.take (i + 1)).length = i + 1 := List.length_take_of_le (by omega)
      have hlen2 : l.length = S.card := by rw [← hli.1.2, List.card_toFinset, hli.1.1.dedup]
      have hcard : (l.take (i + 1)).toFinset.card = i + 1 := by
        rw [List.card_toFinset, hl1_nd.dedup, hlen1]
      rw [heq, ← hlen2] at hcard
      omega
    have hl2_fin : (l.drop (i + 1)).toFinset = S \ (l.take (i + 1)).toFinset := by
      ext y
      simp only [Finset.mem_sdiff, List.mem_toFinset]
      rw [← hli.1.2, List.mem_toFinset]
      constructor
      · intro hy
        refine ⟨List.mem_of_mem_drop hy, fun hy1 => hdisj hy1 hy⟩
      · rintro ⟨hyl, hy1⟩
        have hyl' : y ∈ l.take (i + 1) ++ l.drop (i + 1) := by rwa [List.take_append_drop]
        exact (List.mem_append.mp hyl').resolve_left hy1
    rw [Finset.mem_sigma, Finset.mem_product]
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hA_sub, hA_ne, hA_lt⟩,
      (mem_ordLists _ _).mpr ⟨hl1_nd, rfl⟩, (mem_ordLists _ _).mpr ⟨hl2_nd, hl2_fin⟩⟩
  · rintro ⟨A, l1, l2⟩ hq
    rw [Finset.mem_sigma, Finset.mem_product, Finset.mem_filter, Finset.mem_powerset,
      mem_ordLists, mem_ordLists] at hq
    dsimp only at hq
    rcases hq with ⟨⟨hAS, hAne, hAneS⟩, ⟨h1nd, h1fin⟩, ⟨h2nd, h2fin⟩⟩
    have hdisj : List.Disjoint l1 l2 := by
      intro y hy1 hy2
      have hyA : y ∈ A := h1fin ▸ List.mem_toFinset.mpr hy1
      have hySA : y ∈ S \ A := h2fin ▸ List.mem_toFinset.mpr hy2
      exact (Finset.mem_sdiff.mp hySA).2 hyA
    have hl_nd : (l1 ++ l2).Nodup :=
      List.nodup_append.mpr ⟨h1nd, h2nd, fun y hy1 z hy2 h => hdisj (h ▸ hy1) hy2⟩
    have hl_fin : (l1 ++ l2).toFinset = S := by
      ext y
      simp only [List.mem_toFinset, List.mem_append]
      rw [← List.mem_toFinset, h1fin, ← List.mem_toFinset, h2fin, Finset.mem_sdiff]
      constructor
      · rintro (hy | ⟨hy, _⟩); exact hAS hy; exact hy
      · intro hy; by_cases hyA : y ∈ A; exact Or.inl hyA; exact Or.inr ⟨hy, hyA⟩
    have h1len : 0 < l1.length := by
      rw [← h1nd.dedup, ← List.card_toFinset, h1fin]; exact hAne.card_pos
    have h2pos : (S \ A).Nonempty := Finset.sdiff_nonempty.mpr (fun h => hAneS (Finset.Subset.antisymm hAS h))
    have h2len : 0 < l2.length := by
      rw [← h2nd.dedup, ← List.card_toFinset, h2fin]; exact h2pos.card_pos
    rw [Finset.mem_sigma, Finset.mem_range, mem_ordLists]
    dsimp only
    refine ⟨⟨hl_nd, hl_fin⟩, ?_⟩
    rw [List.length_append]
    omega
  · rintro ⟨l, i⟩ hli
    rw [Finset.mem_sigma, Finset.mem_range] at hli
    dsimp only at hli
    have hlen : (l.take (i + 1)).length = i + 1 := List.length_take_of_le (by omega)
    dsimp
    rw [List.take_append_drop, hlen]
    ext <;> simp
  · rintro ⟨A, l1, l2⟩ hq
    rw [Finset.mem_sigma, Finset.mem_product, Finset.mem_filter, Finset.mem_powerset,
      mem_ordLists, mem_ordLists] at hq
    dsimp only at hq
    have h1len : 0 < l1.length := by
      rw [← hq.2.1.1.dedup, ← List.card_toFinset, hq.2.1.2]; exact hq.1.2.1.card_pos
    have hsub : l1.length - 1 + 1 = l1.length := by omega
    dsimp
    rw [hsub, List.take_left, List.drop_left, hq.2.1.2]
  · intro li _; rfl

lemma pathSum_eq_hSeq (hinv : ∀ v : R, IsUnit v → v * v⁻¹ = 1) {x : α → R}
    (hx : ∀ a b, a ≠ b → IsUnit (x a - x b)) :
    ∀ (S : Finset α), S.Nonempty → pathSum (fVal x) S = (hSeq S.card : R) := by
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    intro hS
    have hc : 1 ≤ S.card := hS.card_pos
    rcases Nat.eq_or_lt_of_le hc with h1 | h2
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h1.symm
      rw [pathSum_singleton, Finset.card_singleton, hSeq_one]
      simp
    · obtain ⟨z, hzS⟩ := hS
      let S' := S.erase z
      have hS' : S'.Nonempty := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hzS]; omega)
      have hzS' : z ∉ S' := Finset.notMem_erase z S
      have hins : insert z S' = S := Finset.insert_erase hzS
      have hcardS' : S'.card = S.card - 1 := Finset.card_erase_of_mem hzS
      rw [← hins, pathSum_insert hinv hx hS' hzS']
      have hS_eq : S.card = (S'.card - 1) + 2 := by omega
      rw [hins, hS_eq, hSeq_succ_succ]
      push_cast
      congr 1
      have hpart : S'.powerset.filter (fun A => A.Nonempty ∧ A ≠ S') =
          (Finset.Ico 1 S'.card).biUnion (fun k => S'.powersetCard k) := by
        ext A
        simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_biUnion,
          Finset.mem_Ico, Finset.mem_powersetCard]
        constructor
        · rintro ⟨hAS, hAne, hAneS⟩
          have hlt : A.card < S'.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hAS, hAneS⟩)
          exact ⟨A.card, ⟨hAne.card_pos, hlt⟩, hAS, rfl⟩
        · rintro ⟨k, ⟨hk1, hk2⟩, hAS, rfl⟩
          exact ⟨hAS, Finset.card_pos.mp hk1, fun heq => by subst heq; omega⟩
      rw [hpart, Finset.sum_biUnion]
      · have hcard_add : S'.card - 1 + 1 = S'.card := by omega
        rw [hcard_add]
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_Ico] at hk
        have hterm : ∀ A ∈ S'.powersetCard k,
            pathSum (fVal x) A * pathSum (fVal x) (S' \ A) =
              (hSeq k : R) * (hSeq (S'.card - k) : R) := by
          intro A hA
          rw [Finset.mem_powersetCard] at hA
          have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
          have hSAne : (S' \ A).Nonempty := by
            apply Finset.card_pos.mp
            rw [Finset.card_sdiff_of_subset hA.1, hA.2]
            omega
          have hA_ss : A ⊂ S := (Finset.ssubset_iff_subset_ne.mpr ⟨hA.1, fun heq => by subst heq; omega⟩).trans (Finset.erase_ssubset hzS)
          have hSA_ss : S' \ A ⊂ S := (Finset.sdiff_subset).trans_ssubset (Finset.erase_ssubset hzS)
          rw [ih A hA_ss hAne, ih (S' \ A) hSA_ss hSAne, hA.2, Finset.card_sdiff_of_subset hA.1, hA.2]
        rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]
        push_cast
        ring
      · intro i _ j _ hij
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro B hB1 hB2
        rw [Finset.mem_powersetCard] at hB1 hB2
        exact hij (hB1.2.symm.trans hB2.2)

lemma cycSum_gVal_eq_zero (hinv : ∀ v : R, IsUnit v → v * v⁻¹ = 1) {x : α → R}
    (hx : ∀ a b, a ≠ b → IsUnit (x a - x b)) {a : α} {U : Finset α}
    (haU : a ∉ U) (hU : 2 ≤ U.card) :
    cycSum (gVal x) a U = 0 := by
  obtain ⟨z, hzU⟩ := Finset.card_pos.mp (by omega : 0 < U.card)
  let U' := U.erase z
  have hzU' : z ∉ U' := Finset.notMem_erase z U
  have hU'_ne : U'.Nonempty := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hzU]; omega)
  have hins : insert z U' = U := Finset.insert_erase hzU
  have haz : a ≠ z := fun h => haU (h ▸ hzU)
  have haU' : a ∉ U' := fun h => haU (Finset.erase_subset z U h)
  rw [cycSum, ← hins, ordLists_insert_sum hzU']
  apply Finset.sum_eq_zero
  intro l hl
  have ⟨hnodup, hfin⟩ := (mem_ordLists U' l).mp hl
  have hzl : z ∉ l := fun h => hzU' (hfin ▸ List.mem_toFinset.mpr h)
  have hal : a ∉ l := fun h => haU' (hfin ▸ List.mem_toFinset.mpr h)
  have hm_pos : 0 < l.length := by rw [length_of_mem_ordLists hl]; exact hU'_ne.card_pos
  let gv : ℕ → R := fun k => gVal x (if h : 1 ≤ k ∧ k ≤ l.length then l[k - 1]'(by omega) else a) z
  have hinner :
      ∑ k ∈ Finset.range (l.length + 1), cycChain (gVal x) a a (l.take k ++ z :: l.drop k) =
        cycChain (gVal x) a a l * ∑ k ∈ Finset.range (l.length + 1), (gv k - gv (k + 1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    have hk_le : k ≤ l.length := by omega
    rw [cycChain_insert_at]
    have hsplit := cycChain_eq_chainProd_mul_tailCyc (gVal x) a a (l.take k) (l.drop k)
    rw [List.take_append_drop] at hsplit
    have hu_eq : (l.take k).getLastD a = if h : 1 ≤ k then l[k - 1]'(by omega) else a :=
      getLastD_take_eq hk_le
    have hv_eq : (l.drop k).headD a = if h : k < l.length then l[k] else a :=
      headD_drop_eq hk_le
    set u := (l.take k).getLastD a
    set v := (l.drop k).headD a
    have huz : u ≠ z := by
      rw [hu_eq]; split_ifs with h1
      · exact fun h => hzl (h ▸ List.getElem_mem _)
      · exact haz
    have hzv : z ≠ v := by
      rw [hv_eq]; split_ifs with h1
      · exact fun h => hzl (h.symm ▸ List.getElem_mem _)
      · exact haz.symm
    have huv : u ≠ v := by
      rw [hu_eq, hv_eq]
      split_ifs with h1 h2
      · intro h; have := hnodup.getElem_inj_iff.mp h; omega
      · exact fun h => hal (h ▸ List.getElem_mem _)
      · exact fun h => hal (h.symm ▸ List.getElem_mem _)
      · omega
    have hgv1 : gv k = gVal x u z := by
      dsimp [gv]; rw [hu_eq]
      split_ifs with h1 h2 <;> try rfl
      all_goals omega
    have hgv2 : gv (k + 1) = gVal x v z := by
      dsimp [gv]; rw [hv_eq]
      split_ifs with h1 h2 <;> try rfl
      all_goals omega
    rw [hgv1, hgv2, mul_assoc (chainProd (gVal x) a (l.take k)), gVal_insert hinv hx huz hzv huv]
    calc
      chainProd (gVal x) a (l.take k) * (gVal x u v * (gVal x u z - gVal x v z)) * tailCyc (gVal x) a (l.drop k)
        = (chainProd (gVal x) a (l.take k) * gVal x u v * tailCyc (gVal x) a (l.drop k)) *
            (gVal x u z - gVal x v z) := by ring
      _ = cycChain (gVal x) a a l * (gVal x u z - gVal x v z) := by rw [← hsplit]
  rw [hinner, Finset.sum_range_sub' gv (l.length + 1)]
  have hgv0 : gv 0 = gVal x a z := by simp [gv]
  have hgvm : gv (l.length + 1) = gVal x a z := by simp [gv]
  rw [hgv0, hgvm, sub_self, mul_zero]

lemma cycSum_fVal_eq_neg_hSeq (hinv : ∀ v : R, IsUnit v → v * v⁻¹ = 1) {x : α → R}
    (hx : ∀ a b, a ≠ b → IsUnit (x a - x b)) {a : α} {U : Finset α}
    (haU : a ∉ U) (hU : 2 ≤ U.card) :
    cycSum (fVal x) a U = - (hSeq U.card : R) := by
  obtain ⟨z, hzU⟩ := Finset.card_pos.mp (by omega : 0 < U.card)
  let U' := U.erase z
  have hzU' : z ∉ U' := Finset.notMem_erase z U
  have hU'_ne : U'.Nonempty := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hzU]; omega)
  have hins : insert z U' = U := Finset.insert_erase hzU
  have haz : a ≠ z := fun h => haU (h ▸ hzU)
  have haU' : a ∉ U' := fun h => haU (Finset.erase_subset z U h)
  rw [cycSum, ← hins, ordLists_insert_sum hzU']
  have hinner : ∀ l ∈ ordLists U',
      ∑ k ∈ Finset.range (l.length + 1), cycChain (fVal x) a a (l.take k ++ z :: l.drop k) =
        - ∑ k ∈ Finset.range (l.length + 1),
            pathProd (fVal x) (l.drop k ++ a :: l.take k) := by
    intro l hl
    have ⟨hnodup, hfin⟩ := (mem_ordLists U' l).mp hl
    have hzl : z ∉ l := fun h => hzU' (hfin ▸ List.mem_toFinset.mpr h)
    have hal : a ∉ l := fun h => haU' (hfin ▸ List.mem_toFinset.mpr h)
    have hm_pos : 0 < l.length := by rw [length_of_mem_ordLists hl]; exact hU'_ne.card_pos
    let gv : ℕ → R := fun k => fVal x (if h : 1 ≤ k ∧ k ≤ l.length then l[k - 1]'(by omega) else a) z
    have hcalc :
        ∑ k ∈ Finset.range (l.length + 1), cycChain (fVal x) a a (l.take k ++ z :: l.drop k) =
          (- ∑ k ∈ Finset.range (l.length + 1),
              pathProd (fVal x) (l.drop k ++ a :: l.take k)) +
            cycChain (fVal x) a a l * ∑ k ∈ Finset.range (l.length + 1), (gv k - gv (k + 1)) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range] at hk
      have hk_le : k ≤ l.length := by omega
      rw [cycChain_insert_at]
      have hsplit := cycChain_eq_chainProd_mul_tailCyc (fVal x) a a (l.take k) (l.drop k)
      rw [List.take_append_drop] at hsplit
      have hu_eq : (l.take k).getLastD a = if h : 1 ≤ k then l[k - 1]'(by omega) else a :=
        getLastD_take_eq hk_le
      have hv_eq : (l.drop k).headD a = if h : k < l.length then l[k] else a :=
        headD_drop_eq hk_le
      set u := (l.take k).getLastD a
      set v := (l.drop k).headD a
      have huz : u ≠ z := by
        rw [hu_eq]; split_ifs with h1
        · exact fun h => hzl (h ▸ List.getElem_mem _)
        · exact haz
      have hzv : z ≠ v := by
        rw [hv_eq]; split_ifs with h1
        · exact fun h => hzl (h.symm ▸ List.getElem_mem _)
        · exact haz.symm
      have huv : u ≠ v := by
        rw [hu_eq, hv_eq]
        split_ifs with h1 h2
        · intro h; have := hnodup.getElem_inj_iff.mp h; omega
        · exact fun h => hal (h ▸ List.getElem_mem _)
        · exact fun h => hal (h.symm ▸ List.getElem_mem _)
        · omega
      have hgv1 : gv k = fVal x u z := by
        dsimp [gv]; rw [hu_eq]
        split_ifs with h1 h2 <;> try rfl
        all_goals omega
      have hgv2 : gv (k + 1) = fVal x v z := by
        dsimp [gv]; rw [hv_eq]
        split_ifs with h1 h2 <;> try rfl
        all_goals omega
      rw [hgv1, hgv2, mul_assoc (chainProd (fVal x) a (l.take k)), fVal_insert hinv hx huz hzv huv,
        pathProd_drop_cons_take]
      calc
        chainProd (fVal x) a (l.take k) * (-1 + fVal x u v * (fVal x u z - fVal x v z)) *
            tailCyc (fVal x) a (l.drop k)
          = -(chainProd (fVal x) a (l.take k) * tailCyc (fVal x) a (l.drop k)) +
              (chainProd (fVal x) a (l.take k) * fVal x u v * tailCyc (fVal x) a (l.drop k)) *
                (fVal x u z - fVal x v z) := by ring
        _ = -(chainProd (fVal x) a (l.take k) * tailCyc (fVal x) a (l.drop k)) +
              cycChain (fVal x) a a l * (fVal x u z - fVal x v z) := by rw [← hsplit]
    rw [hcalc, Finset.sum_range_sub' gv (l.length + 1)]
    have hgv0 : gv 0 = fVal x a z := by simp [gv]
    have hgvm : gv (l.length + 1) = fVal x a z := by simp [gv]
    rw [hgv0, hgvm, sub_self, mul_zero, add_zero]
  rw [Finset.sum_congr rfl hinner, Finset.sum_neg_distrib]
  have hrot := ordLists_rotate_sum a (S := insert a U') (Finset.mem_insert_self a U') (pathProd (fVal x))
  rw [Finset.erase_insert haU'] at hrot
  rw [← hrot]
  change - pathSum (fVal x) (insert a U') = - (hSeq (insert z U').card : R)
  rw [pathSum_eq_hSeq hinv hx (insert a U') (Finset.insert_nonempty a U')]
  have hcard_eq : (insert a U').card = (insert z U').card := by
    rw [Finset.card_insert_of_notMem haU', Finset.card_insert_of_notMem hzU']
  rw [hcard_eq]

end PathCycle

section PermDecomp

variable {α : Type*} [Fintype α] [DecidableEq α] {R : Type*} [CommRing R] [Inv R]

def permSet (S : Finset α) : Finset (Equiv.Perm α) :=
  Finset.univ.filter (fun σ => ∀ a, a ∉ S → σ a = a)

noncomputable def permOn (S : Finset α) (M : α → α → R) : R :=
  ∑ σ ∈ permSet S, ∏ a ∈ S, M a (σ a)

omit [Inv R] in
lemma permOn_empty (M : α → α → R) : permOn ∅ M = 1 := by
  have hp : permSet (∅ : Finset α) = {1} := by
    ext σ
    simp [permSet, Equiv.Perm.ext_iff]
  simp [permOn, hp]

omit [Fintype α] [Inv R] in
lemma prod_formPerm_eq_cycChain (M : α → α → R) (a : α) (l : List α)
    (hnd : (a :: l).Nodup) :
    ∏ x ∈ (a :: l).toFinset, M x ((List.formPerm (a :: l)) x) = cycChain M a a l := by
  set L := a :: l
  set c := List.formPerm L
  let gf : ℕ → R := fun i => if h : i < L.length then M (L[i]) (c (L[i])) else 1
  have hbij : ∏ x ∈ L.toFinset, M x (c x) = ∏ i ∈ Finset.range L.length, gf i := by
    symm
    refine Finset.prod_bij (fun i hi => L[i]'(Finset.mem_range.mp hi)) ?_ ?_ ?_ ?_
    · intro i hi; exact List.mem_toFinset.mpr (List.getElem_mem _)
    · intro i1 hi1 i2 hi2 heq
      exact hnd.getElem_inj_iff.mp heq
    · intro x hx
      rw [List.mem_toFinset] at hx
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      exact ⟨i, Finset.mem_range.mpr hi, rfl⟩
    · intro i hi
      simp [gf, Finset.mem_range.mp hi]
  have hLlen : 0 < L.length := by simp [L]
  let elem : ℕ → α := fun j => if h : j < L.length then L[j]'h else a
  have hind : ∀ k : ℕ, k ≤ L.length - 1 →
      ∏ j ∈ Finset.Ico (L.length - 1 - k) L.length, gf j =
        cycChain M a (elem (L.length - 1 - k)) (L.drop (L.length - k)) := by
    intro k
    induction k with
    | zero =>
      intro _
      have hsub1 : L.length - 1 - 0 = L.length - 1 := rfl
      have hico : Finset.Ico (L.length - 1) L.length = {L.length - 1} := by
        ext j; simp only [Finset.mem_Ico, Finset.mem_singleton]; omega
      rw [hsub1, hico, Finset.prod_singleton]
      have hdrop : L.drop (L.length - 0) = [] := by simp [List.drop_length]
      rw [hdrop, cycChain]
      have hc : c (L[L.length - 1]'(by omega)) = a := by
        dsimp [c]
        rw [List.formPerm_apply_getElem L hnd (L.length - 1) (by omega)]
        have hmod : (L.length - 1 + 1) % L.length = 0 := by
          have : L.length - 1 + 1 = L.length := by omega
          rw [this, Nat.mod_self]
        simp [hmod, L]
      simp only [gf, elem, dif_pos (by omega : L.length - 1 < L.length), hc]
    | succ k ih =>
      intro hk
      have hk' : k ≤ L.length - 1 := by omega
      have ih' := ih hk'
      set i := L.length - 1 - (k + 1)
      have hi_lt : i + 1 < L.length := by omega
      have hi1_eq : L.length - 1 - k = i + 1 := by omega
      rw [hi1_eq] at ih'
      have hico : Finset.Ico i L.length = insert i (Finset.Ico (i + 1) L.length) := by
        ext j; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
      have hnot : i ∉ Finset.Ico (i + 1) L.length := by simp
      rw [hico, Finset.prod_insert hnot, ih']
      have hdrop : L.drop (L.length - (k + 1)) = L[i + 1]'hi_lt :: L.drop (L.length - k) := by
        have hidx : L.length - (k + 1) = i + 1 := by omega
        have hidx2 : i + 1 + 1 = L.length - k := by omega
        rw [hidx, List.drop_eq_getElem_cons (i := i + 1) hi_lt, hidx2]
      rw [hdrop, cycChain]
      have hc : c (L[i]'(by omega)) = L[i + 1]'hi_lt := by
        dsimp [c]
        rw [List.formPerm_apply_getElem L hnd i (by omega)]
        have hmod : (i + 1) % L.length = i + 1 := Nat.mod_eq_of_lt hi_lt
        simp [hmod]
      simp only [gf, elem, dif_pos (by omega : i < L.length), dif_pos hi_lt, hc]
  have hres := hind (L.length - 1) le_rfl
  have hsub0 : L.length - 1 - (L.length - 1) = 0 := Nat.sub_self _
  have hico0 : Finset.Ico (L.length - 1 - (L.length - 1)) L.length = Finset.range L.length := by
    rw [hsub0]; ext j; simp [Finset.mem_range]
  rw [hico0] at hres
  rw [hbij, hres]
  have hL0 : elem (L.length - 1 - (L.length - 1)) = a := by simp [elem, hsub0, L]
  have hL1 : L.drop (L.length - (L.length - 1)) = l := by
    have h1 : L.length - (L.length - 1) = 1 := by omega
    rw [h1]; rfl
  rw [hL0, hL1]

omit [Inv R] in
lemma toList_mul_disjoint_of_fix {c σ' : Equiv.Perm α} {a : α}
    (hd : c.Disjoint σ') (hfix : σ' a = a) :
    (c * σ').toList a = c.toList a := by
  have hcyc : (c * σ').cycleOf a = c.cycleOf a := by
    rw [hd.cycleOf_mul_distrib, (Equiv.Perm.cycleOf_eq_one_iff σ').mpr hfix, mul_one]
  apply List.ext_getElem
  · simp [Equiv.Perm.length_toList, hcyc]
  · intro i hi1 hi2
    simp only [Equiv.Perm.toList, List.getElem_iterate, Equiv.Perm.iterate_eq_pow]
    rw [← Equiv.Perm.cycleOf_pow_apply_self (c * σ'), hcyc, Equiv.Perm.cycleOf_pow_apply_self]

omit [Inv R] in
lemma permOn_peel (S : Finset α) {a : α} (ha : a ∈ S) (M : α → α → R) :
    permOn S M = ∑ U ∈ (S.erase a).powerset, cycSum M a U * permOn (S \ insert a U) M := by
  rw [permOn]
  have hR_prod : ∀ U ∈ (S.erase a).powerset,
      cycSum M a U * permOn (S \ insert a U) M =
        ∑ l ∈ ordLists U, ∑ σ' ∈ permSet (S \ insert a U),
          cycChain M a a l * ∏ x ∈ S \ insert a U, M x (σ' x) := by
    intro U _
    simp only [cycSum, permOn, Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl hR_prod]
  let T := (S.erase a).powerset.sigma (fun U => ordLists U ×ˢ permSet (S \ insert a U))
  have hR :
      ∑ U ∈ (S.erase a).powerset, ∑ l ∈ ordLists U, ∑ σ' ∈ permSet (S \ insert a U),
          cycChain M a a l * ∏ x ∈ S \ insert a U, M x (σ' x) =
        ∑ t ∈ T, cycChain M a a t.2.1 * ∏ x ∈ S \ insert a t.1, M x (t.2.2 x) := by
    rw [← Finset.sum_sigma' (S.erase a).powerset (fun U => ordLists U ×ˢ permSet (S \ insert a U))
      (fun U p => cycChain M a a p.1 * ∏ x ∈ S \ insert a U, M x (p.2 x))]
    apply Finset.sum_congr rfl
    intro U _
    exact (Finset.sum_product' (ordLists U) (permSet (S \ insert a U))
      (fun l σ' => cycChain M a a l * ∏ x ∈ S \ insert a U, M x (σ' x))).symm
  rw [hR]
  refine Finset.sum_bij'
    (fun σ _ => ⟨(S.erase a).filter (fun b => σ.SameCycle a b), (σ.toList a).tail, (σ.cycleOf a)⁻¹ * σ⟩)
    (fun t _ => List.formPerm (a :: t.2.1) * t.2.2)
    ?_ ?_ ?_ ?_ ?_
  · intro σ hσ
    rw [permSet, Finset.mem_filter] at hσ
    have hσ_fix : ∀ x, x ∉ S → σ x = x := hσ.2
    let U := (S.erase a).filter (fun b => σ.SameCycle a b)
    have hU_sub : U ⊆ S.erase a := Finset.filter_subset _ _
    have h_same_mem : ∀ x, σ.SameCycle a x → x ∈ insert a U := by
      intro x hx
      by_cases hxa : x = a
      · simp [hxa]
      · have hxS : x ∈ S := by
          by_contra hxn
          have hfx := hσ_fix x hxn
          exact hxa (hx.eq_of_right hfx).symm
        exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hxa, hxS⟩, hx⟩)
    have h_mem_same : ∀ x ∈ insert a U, σ.SameCycle a x := by
      intro x hx
      rw [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact Equiv.Perm.SameCycle.rfl
      · exact (Finset.mem_filter.mp hx).2
    have hl_mem : (σ.toList a).tail ∈ ordLists U := by
      rw [mem_ordLists]
      by_cases hfix : σ a = a
      · have hnil : σ.toList a = [] := Equiv.Perm.toList_eq_nil_iff.mpr (Equiv.Perm.notMem_support.mpr hfix)
        rw [hnil]
        refine ⟨List.nodup_nil, ?_⟩
        ext x
        simp only [List.tail_nil, List.toFinset_nil, Finset.notMem_empty, U, Finset.mem_filter,
          Finset.mem_erase, false_iff, not_and]
        intro hne hsame
        exact hne.1 (hsame.eq_of_left hfix).symm
      · have hpos : 0 < (σ.toList a).length :=
          Equiv.Perm.length_toList_pos_of_mem_support σ a (Equiv.Perm.mem_support.mpr hfix)
        have hhd : (σ.toList a)[0]'hpos = a :=
          Equiv.Perm.toList_getElem_zero σ a (Equiv.Perm.mem_support.mpr hfix)
        have hcons : σ.toList a = a :: (σ.toList a).tail := by
          cases htl : σ.toList a with
          | nil => simp [htl] at hpos
          | cons hd tl =>
            have h0 : hd = a := by simpa [htl] using hhd
            simp [h0]
        have hnd : (a :: (σ.toList a).tail).Nodup := hcons ▸ Equiv.Perm.nodup_toList σ a
        refine ⟨(List.nodup_cons.mp hnd).2, ?_⟩
        ext x
        simp only [List.mem_toFinset, U, Finset.mem_filter, Finset.mem_erase]
        have hxa_not : a ∉ (σ.toList a).tail := (List.nodup_cons.mp hnd).1
        constructor
        · intro hx
          have hmem : x ∈ σ.toList a := hcons ▸ List.mem_cons_of_mem a hx
          have hsame := (Equiv.Perm.mem_toList_iff.mp hmem).1
          have hne : x ≠ a := fun h => hxa_not (h ▸ hx)
          have hxS : x ∈ S := by
            have := h_same_mem x hsame
            rw [Finset.mem_insert] at this
            exact this.resolve_left hne |> Finset.mem_filter.mp |>.1 |> Finset.erase_subset a S
          exact ⟨⟨hne, hxS⟩, hsame⟩
        · rintro ⟨⟨hne, _⟩, hsame⟩
          have hmem : x ∈ σ.toList a :=
            Equiv.Perm.mem_toList_iff.mpr ⟨hsame, Equiv.Perm.mem_support.mpr hfix⟩
          rw [hcons, List.mem_cons] at hmem
          exact hmem.resolve_left hne
    have hσ'_mem : (σ.cycleOf a)⁻¹ * σ ∈ permSet (S \ insert a U) := by
      rw [permSet, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, fun x hx => ?_⟩
      simp only [Equiv.Perm.coe_mul, Function.comp_apply]
      by_cases hxS : x ∈ S
      · have hxU : x ∈ insert a U := by
          by_contra hxn
          exact hx (Finset.mem_sdiff.mpr ⟨hxS, hxn⟩)
        have hsame := h_mem_same x hxU
        rw [← Equiv.Perm.SameCycle.cycleOf_apply hsame]
        exact Equiv.Perm.inv_eq_iff_eq.mpr rfl
      · have hfx := hσ_fix x hxS
        have hnot : ¬ σ.SameCycle a x := fun h => hxS (by
          have := h_same_mem x h
          rw [Finset.mem_insert] at this
          rcases this with rfl | hxU
          · exact ha
          · exact Finset.erase_subset a S (Finset.mem_filter.mp hxU).1)
        rw [hfx, Equiv.Perm.cycleOf_inv, Equiv.Perm.cycleOf_apply_of_not_sameCycle (by
          rwa [Equiv.Perm.sameCycle_inv])]
    rw [Finset.mem_sigma, Finset.mem_product]
    exact ⟨Finset.mem_powerset.mpr hU_sub, hl_mem, hσ'_mem⟩
  · rintro ⟨U, l, σ'⟩ ht
    rw [Finset.mem_sigma, Finset.mem_product, Finset.mem_powerset, permSet, Finset.mem_filter] at ht
    dsimp only at ht
    rcases ht with ⟨hUS, hl_mem, _, hσ'_fix⟩
    rw [permSet, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun x hx => ?_⟩
    have hx_not_U : x ∉ insert a U := by
      intro h; rw [Finset.mem_insert] at h
      rcases h with rfl | hxU
      · exact hx ha
      · exact hx (Finset.erase_subset a S (hUS hxU))
    have hx_not_l : x ∉ a :: l := by
      intro h; rw [List.mem_cons] at h
      rcases h with rfl | hxl
      · exact hx_not_U (Finset.mem_insert_self _ U)
      · exact hx_not_U (Finset.mem_insert_of_mem (((mem_ordLists U l).mp hl_mem).2 ▸ List.mem_toFinset.mpr hxl))
    have hx_not_sdiff : x ∉ S \ insert a U := fun h => hx (Finset.sdiff_subset h)
    simp [Equiv.Perm.coe_mul, hσ'_fix x hx_not_sdiff, List.formPerm_apply_of_notMem hx_not_l]
  · intro σ _
    dsimp
    by_cases hfix : σ a = a
    · have hnil : σ.toList a = [] := Equiv.Perm.toList_eq_nil_iff.mpr (Equiv.Perm.notMem_support.mpr hfix)
      have hcyc : σ.cycleOf a = 1 := (Equiv.Perm.cycleOf_eq_one_iff σ).mpr hfix
      simp [hnil, hcyc]
    · have hpos : 0 < (σ.toList a).length :=
        Equiv.Perm.length_toList_pos_of_mem_support σ a (Equiv.Perm.mem_support.mpr hfix)
      have hhd : (σ.toList a)[0]'hpos = a :=
        Equiv.Perm.toList_getElem_zero σ a (Equiv.Perm.mem_support.mpr hfix)
      have hcons : a :: (σ.toList a).tail = σ.toList a := by
        cases htl : σ.toList a with
        | nil => simp [htl] at hpos
        | cons hd tl =>
          have h0 : hd = a := by simpa [htl] using hhd
          simp [h0]
      rw [hcons, Equiv.Perm.formPerm_toList, mul_inv_cancel_left]
  · rintro ⟨U, l, σ'⟩ ht
    rw [Finset.mem_sigma, Finset.mem_product, Finset.mem_powerset, mem_ordLists, permSet, Finset.mem_filter] at ht
    dsimp only at ht
    rcases ht with ⟨hUS, ⟨hl_nd, hl_fin⟩, _, hσ'_fix⟩
    have haU : a ∉ U := fun h => (Finset.notMem_erase a S) (hUS h)
    have hal : a ∉ l := fun h => haU (hl_fin ▸ List.mem_toFinset.mpr h)
    have hnd : (a :: l).Nodup := List.nodup_cons.mpr ⟨hal, hl_nd⟩
    set c := List.formPerm (a :: l)
    have hsupp_c : c.support ⊆ insert a U := by
      intro x hx
      have hxm : x ∈ a :: l := List.mem_of_formPerm_apply_ne (Equiv.Perm.mem_support.mp hx)
      rw [List.mem_cons] at hxm
      rcases hxm with rfl | hxl
      · exact Finset.mem_insert_self _ U
      · exact Finset.mem_insert_of_mem (hl_fin ▸ List.mem_toFinset.mpr hxl)
    have hdisj : c.Disjoint σ' := by
      rw [Equiv.Perm.disjoint_iff_eq_or_eq]
      intro x
      by_cases hx : x ∈ insert a U
      · right; exact hσ'_fix x (by simp [hx])
      · left; rw [← Equiv.Perm.notMem_support]; exact fun h => hx (hsupp_c h)
    have hσ'a : σ' a = a := hσ'_fix a (by simp)
    have htol : (c * σ').toList a = c.toList a := toList_mul_disjoint_of_fix hdisj hσ'a
    have hcyc_eq : (c * σ').cycleOf a = c := by
      rw [hdisj.cycleOf_mul_distrib, (Equiv.Perm.cycleOf_eq_one_iff σ').mpr hσ'a, mul_one]
      cases l with
      | nil => simp [c]; exact (Equiv.Perm.cycleOf_eq_one_iff 1).mpr rfl
      | cons b t =>
        have hlen : 2 ≤ (a :: b :: t).length := by simp
        have hc_cyc := List.isCycle_formPerm hnd hlen
        have hca : c a ≠ a := (List.formPerm_apply_mem_ne_self_iff _ hnd a (by simp)).mpr hlen
        exact hc_cyc.cycleOf_eq hca
    have htail : ((c * σ').toList a).tail = l := by
      rw [htol]
      cases l with
      | nil => simp [c]
      | cons b t =>
        have hlen : 2 ≤ (a :: b :: t).length := by simp
        have hcl : (a :: b :: t).formPerm.toList a = a :: b :: t :=
          Equiv.Perm.toList_formPerm_nontrivial (a :: b :: t) hlen hnd
        have hcl' : c.toList a = a :: b :: t := by simpa [c] using hcl
        simp [hcl']
    have hU_eq : (S.erase a).filter (fun b => (c * σ').SameCycle a b) = U := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨⟨hne, _⟩, hsame⟩
        have hmem_c : c a ≠ a := by
          intro h
          have hfix_cs : (c * σ') a = a := by simp [h, hσ'a]
          have h1 := hsame.eq_of_left hfix_cs
          exact hne h1.symm
        have hb_mem : b ∈ (c * σ').toList a :=
          Equiv.Perm.mem_toList_iff.mpr ⟨hsame, Equiv.Perm.mem_support.mpr (by simp [hσ'a, hmem_c])⟩
        rw [htol] at hb_mem
        cases htl : l with
        | nil => simp [c, htl] at hmem_c
        | cons b0 t0 =>
          have hcl : (a :: b0 :: t0).formPerm.toList a = a :: b0 :: t0 :=
            Equiv.Perm.toList_formPerm_nontrivial (a :: b0 :: t0) (by simp) (htl ▸ hnd)
          have hca_list : c.toList a = a :: b0 :: t0 := by
            simpa [c, htl] using hcl
          rw [hca_list, List.mem_cons] at hb_mem
          have hbl : b ∈ l := htl ▸ hb_mem.resolve_left hne
          rw [← hl_fin, List.mem_toFinset]
          exact hbl
      · intro hbU
        have hne : b ≠ a := fun h => haU (h ▸ hbU)
        have hbS : b ∈ S := Finset.erase_subset a S (hUS hbU)
        have hbl : b ∈ l := by rw [← List.mem_toFinset, hl_fin]; exact hbU
        refine ⟨⟨hne, hbS⟩, ?_⟩
        have hc_same : c.SameCycle a b := by
          cases htl : l with
          | nil => simp [htl] at hbl
          | cons b0 t0 =>
            have hnd' : (a :: b0 :: t0).Nodup := htl ▸ hnd
            have hc_cyc := List.isCycle_formPerm hnd' (by simp)
            have hca : (a :: b0 :: t0).formPerm a ≠ a :=
              (List.formPerm_apply_mem_ne_self_iff _ hnd' a (by simp)).mpr (by simp)
            have hcb : (a :: b0 :: t0).formPerm b ≠ b :=
              (List.formPerm_apply_mem_ne_self_iff _ hnd' b (by simp [htl ▸ hbl])).mpr (by simp)
            have hres := hc_cyc.sameCycle hca hcb
            simpa [c, htl] using hres
        obtain ⟨n, hn⟩ := hc_same.exists_nat_pow_eq
        refine ⟨n, ?_⟩
        rw [zpow_natCast, ← Equiv.Perm.cycleOf_pow_apply_self (c * σ'), hcyc_eq, hn]
    dsimp
    refine Sigma.ext hU_eq ?_
    exact heq_of_eq (Prod.ext htail (by rw [hcyc_eq, inv_mul_cancel_left]))
  · intro σ hσ
    rw [permSet, Finset.mem_filter] at hσ
    dsimp
    let U := (S.erase a).filter (fun b => σ.SameCycle a b)
    have hsub : insert a U ⊆ S := by
      intro x hx
      rw [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact ha
      · exact Finset.erase_subset a S (Finset.mem_filter.mp hx).1
    rw [← Finset.prod_sdiff hsub, mul_comm]
    congr 1
    · by_cases hfix : σ a = a
      · have hnil : σ.toList a = [] := Equiv.Perm.toList_eq_nil_iff.mpr (Equiv.Perm.notMem_support.mpr hfix)
        have hU0 : U = ∅ := by
          ext b; simp only [U, Finset.mem_filter, Finset.mem_erase, Finset.notMem_empty, iff_false, not_and]
          intro hne hsame; exact hne.1 (hsame.eq_of_left hfix).symm
        simp [hU0, hnil, hfix, cycChain]
      · have hpos : 0 < (σ.toList a).length :=
          Equiv.Perm.length_toList_pos_of_mem_support σ a (Equiv.Perm.mem_support.mpr hfix)
        have hhd : (σ.toList a)[0]'hpos = a :=
          Equiv.Perm.toList_getElem_zero σ a (Equiv.Perm.mem_support.mpr hfix)
        have hcons : a :: (σ.toList a).tail = σ.toList a := by
          cases htl : σ.toList a with
          | nil => simp [htl] at hpos
          | cons hd tl =>
            have h0 : hd = a := by simpa [htl] using hhd
            simp [h0]
        have hnd : (a :: (σ.toList a).tail).Nodup := hcons ▸ Equiv.Perm.nodup_toList σ a
        have hfin : (a :: (σ.toList a).tail).toFinset = insert a U := by
          ext x
          rw [hcons, List.mem_toFinset, Equiv.Perm.mem_toList_iff, Finset.mem_insert]
          constructor
          · rintro ⟨hsame, _⟩
            by_cases hxa : x = a; exact Or.inl hxa
            have hxS : x ∈ S := by
              by_contra hxn
              exact hxa (hsame.eq_of_right (hσ.2 x hxn)).symm
            exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hxa, hxS⟩, hsame⟩)
          · intro hx
            refine ⟨?_, Equiv.Perm.mem_support.mpr hfix⟩
            rcases hx with rfl | hxU
            · exact Equiv.Perm.SameCycle.rfl
            · exact (Finset.mem_filter.mp hxU).2
        rw [← hfin, ← prod_formPerm_eq_cycChain M a _ hnd]
        apply Finset.prod_congr rfl
        intro x hx
        rw [hfin] at hx
        have hsame : σ.SameCycle a x := by
          rw [Finset.mem_insert] at hx
          rcases hx with rfl | hxU
          · exact Equiv.Perm.SameCycle.rfl
          · exact (Finset.mem_filter.mp hxU).2
        rw [hcons, Equiv.Perm.formPerm_toList, hsame.cycleOf_apply]
    · apply Finset.prod_congr rfl
      intro x hx
      rw [Finset.mem_sdiff] at hx
      have hnot : ¬ σ.SameCycle a x := by
        intro hsame
        by_cases hxa : x = a
        · exact hx.2 (hxa ▸ Finset.mem_insert_self a U)
        · exact hx.2 (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hxa, hx.1⟩, hsame⟩))
      have hnot' : ¬ σ.SameCycle a (σ x) := by rwa [Equiv.Perm.sameCycle_apply_right]
      have hinv_eq : (σ.cycleOf a)⁻¹ (σ x) = σ x :=
        Equiv.Perm.inv_eq_iff_eq.mpr (Equiv.Perm.cycleOf_apply_of_not_sameCycle hnot').symm
      have hgoal : σ x = ((σ.cycleOf a)⁻¹ * σ) x := by
        rw [Equiv.Perm.mul_apply, hinv_eq]
      exact congrArg (M x) hgoal

def invSet (U : Finset α) : Finset (Equiv.Perm α) :=
  (permSet U).filter (fun τ => ∀ a ∈ U, τ a ≠ a ∧ τ (τ a) = a)

noncomputable def matchWeight (x : α → R) (U : Finset α) : R :=
  ∑ τ ∈ invSet U, ∏ a ∈ U, (2 * x a) * gVal x a (τ a)

lemma matchWeight_empty (x : α → R) : matchWeight x ∅ = 1 := by
  have hi : invSet (∅ : Finset α) = {1} := by
    ext τ
    simp [invSet, permSet, Equiv.Perm.ext_iff]
  simp [matchWeight, hi]

lemma matchWeight_peel (x : α → R) {V : Finset α} {a : α} (ha : a ∈ V) :
    matchWeight x V = ∑ b ∈ V.erase a, mVal x a b * matchWeight x (V \ {a, b}) := by
  rw [matchWeight]
  have hR_prod : ∀ b ∈ V.erase a,
      mVal x a b * matchWeight x (V \ {a, b}) =
        ∑ τ' ∈ invSet (V \ {a, b}), mVal x a b * ∏ u ∈ V \ {a, b}, (2 * x u) * gVal x u (τ' u) := by
    intro b _; rw [matchWeight, Finset.mul_sum]
  rw [Finset.sum_congr rfl hR_prod,
    Finset.sum_sigma' (V.erase a) (fun b => invSet (V \ {a, b}))
      (fun b τ' => mVal x a b * ∏ u ∈ V \ {a, b}, (2 * x u) * gVal x u (τ' u))]
  refine Finset.sum_bij'
    (fun τ _ => ⟨τ a, Equiv.swap a (τ a) * τ⟩)
    (fun bt _ => Equiv.swap a bt.1 * bt.2)
    ?_ ?_ ?_ ?_ ?_
  · intro τ hτ
    rw [invSet, permSet, Finset.mem_filter, Finset.mem_filter] at hτ
    rcases hτ with ⟨⟨_, hfix⟩, hinv⟩
    obtain ⟨hτa_ne, hττa⟩ := hinv a ha
    have hτa_mem : τ a ∈ V.erase a := by
      refine Finset.mem_erase.mpr ⟨hτa_ne, ?_⟩
      by_contra hnot
      have hfx := hfix (τ a) hnot
      exact hτa_ne (by rw [← hfx, hττa])
    have hτ'_mem : Equiv.swap a (τ a) * τ ∈ invSet (V \ {a, τ a}) := by
      rw [invSet, permSet, Finset.mem_filter, Finset.mem_filter]
      refine ⟨⟨Finset.mem_univ _, fun y hy => ?_⟩, fun y hy => ?_⟩
      · by_cases hyV : y ∈ V
        · have hyab : y = a ∨ y = τ a := by
            by_contra h
            exact hy (Finset.mem_sdiff.mpr ⟨hyV, by simpa using h⟩)
          rcases hyab with rfl | hyb
          · simp [hτa_ne]
          · simp [hyb, hττa]
        · have hτy : τ y = y := hfix y hyV
          have hya : y ≠ a := fun h => hyV (h ▸ ha)
          have hyb : y ≠ τ a := fun h => hyV (h ▸ (Finset.erase_subset a V hτa_mem))
          simp [hτy, Equiv.swap_apply_of_ne_of_ne hya hyb]
      · simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hy
        obtain ⟨hyV, hya, hyb⟩ := hy
        obtain ⟨hτy_ne, hττy⟩ := hinv y hyV
        have hτya : τ y ≠ a := fun h => hyb (by rw [← h, hττy])
        have hτyb : τ y ≠ τ a := fun h => hya (τ.injective h)
        have hswap1 : Equiv.swap a (τ a) (τ y) = τ y := Equiv.swap_apply_of_ne_of_ne hτya hτyb
        simp only [Equiv.Perm.coe_mul, Function.comp_apply, hswap1]
        exact ⟨hτy_ne, by simp [hττy, Equiv.swap_apply_of_ne_of_ne hya hyb]⟩
    rw [Finset.mem_sigma]
    exact ⟨hτa_mem, hτ'_mem⟩
  · rintro ⟨b, τ'⟩ hbt
    rw [Finset.mem_sigma, Finset.mem_erase, invSet, permSet, Finset.mem_filter, Finset.mem_filter] at hbt
    rcases hbt with ⟨⟨hba, hbV⟩, ⟨_, hfix'⟩, hinv'⟩
    rw [invSet, permSet, Finset.mem_filter, Finset.mem_filter]
    have ha_fix : τ' a = a := hfix' a (by simp)
    have hb_fix : τ' b = b := hfix' b (by simp)
    refine ⟨⟨Finset.mem_univ _, fun y hy => ?_⟩, fun y hy => ?_⟩
    · have hya : y ≠ a := fun h => hy (h ▸ ha)
      have hyb : y ≠ b := fun h => hy (h ▸ hbV)
      have hy_sdiff : y ∉ V \ {a, b} := fun h => hy (Finset.sdiff_subset h)
      simp [hfix' y hy_sdiff, Equiv.swap_apply_of_ne_of_ne hya hyb]
    · by_cases hya : y = a
      · rw [hya]; simp [ha_fix, hb_fix]; exact hba
      · by_cases hyb : y = b
        · rw [hyb]; simp [ha_fix, hb_fix]; exact hba.symm
        · have hy_sdiff : y ∈ V \ {a, b} := by simp [hy, hya, hyb]
          obtain ⟨hτ'y_ne, hτ'τ'y⟩ := hinv' y hy_sdiff
          have hτ'ya : τ' y ≠ a := fun h => hya (τ'.injective (h.trans ha_fix.symm))
          have hτ'yb : τ' y ≠ b := fun h => hyb (τ'.injective (h.trans hb_fix.symm))
          have hs1 : Equiv.swap a b (τ' y) = τ' y := Equiv.swap_apply_of_ne_of_ne hτ'ya hτ'yb
          simp only [Equiv.Perm.coe_mul, Function.comp_apply, hs1]
          exact ⟨hτ'y_ne, by simp [hτ'τ'y, Equiv.swap_apply_of_ne_of_ne hya hyb]⟩
  · intro _ _
    dsimp
    rw [← mul_assoc, Equiv.swap_mul_self, one_mul]
  · rintro ⟨b, τ'⟩ hbt
    rw [Finset.mem_sigma, Finset.mem_erase, invSet, permSet, Finset.mem_filter, Finset.mem_filter] at hbt
    rcases hbt with ⟨⟨_, _⟩, ⟨_, hfix'⟩, _⟩
    have ha_fix : τ' a = a := hfix' a (by simp)
    refine Sigma.ext (by simp [ha_fix]) (heq_of_eq ?_)
    dsimp only
    simp only [Equiv.Perm.coe_mul, Function.comp_apply, ha_fix, Equiv.swap_apply_left]
    rw [← mul_assoc, Equiv.swap_mul_self, one_mul]
  · intro τ hτ
    rw [invSet, Finset.mem_filter] at hτ
    obtain ⟨hτa_ne, hττa⟩ := hτ.2 a ha
    have hτa_mem : τ a ∈ V.erase a := by
      rw [permSet, Finset.mem_filter] at hτ
      refine Finset.mem_erase.mpr ⟨hτa_ne, ?_⟩
      by_contra hnot
      have hfix := hτ.1.2 (τ a) hnot
      exact hτa_ne (by rw [← hfix, hττa])
    dsimp
    rw [← Finset.mul_prod_erase V _ ha, ← Finset.mul_prod_erase (V.erase a) _ hτa_mem]
    have hsdiff : (V.erase a).erase (τ a) = V \ {a, τ a} := by
      ext u; simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]; tauto
    rw [hsdiff, hττa]
    have hprod_eq : ∏ u ∈ V \ {a, τ a}, (2 * x u) * gVal x u (τ u) =
        ∏ u ∈ V \ {a, τ a}, (2 * x u) * gVal x u ((Equiv.swap a (τ a) * τ) u) := by
      apply Finset.prod_congr rfl
      intro u hu
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hu
      have hττu := (hτ.2 u hu.1).2
      have hτua : τ u ≠ a := fun h => hu.2.2 (by rw [← h, hττu])
      have hτub : τ u ≠ τ a := fun h => hu.2.1 (τ.injective h)
      simp [Equiv.swap_apply_of_ne_of_ne hτua hτub]
    rw [hprod_eq, mVal]
    simp only [Equiv.Perm.coe_mul, Function.comp_apply]
    ring

omit [Inv R] in
lemma even_card_of_invSet_nonempty : ∀ (U : Finset α), (invSet U).Nonempty → Even U.card := by
  intro U
  induction U using Finset.strongInduction with
  | H U ih =>
    rintro ⟨τ, hτ⟩
    by_cases hU : U = ∅
    · subst hU; simp
    · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hU
      rw [invSet, permSet, Finset.mem_filter, Finset.mem_filter] at hτ
      obtain ⟨hτa_ne, hττa⟩ := hτ.2 a ha
      have hτa_mem : τ a ∈ U := by
        by_contra hnot
        have hfix := hτ.1.2 (τ a) hnot
        exact hτa_ne (by rw [← hfix, hττa])
      let U' := U \ {a, τ a}
      have hU'_ss : U' ⊂ U := by
        rw [Finset.ssubset_iff_of_subset Finset.sdiff_subset]
        exact ⟨a, ha, by simp⟩
      have hτ'_mem : Equiv.swap a (τ a) * τ ∈ invSet U' := by
        rw [invSet, permSet, Finset.mem_filter, Finset.mem_filter]
        refine ⟨⟨Finset.mem_univ _, fun y hy => ?_⟩, fun y hy => ?_⟩
        · by_cases hyU : y ∈ U
          · have hyab : y = a ∨ y = τ a := by
              by_contra h
              exact hy (Finset.mem_sdiff.mpr ⟨hyU, by simpa using h⟩)
            rcases hyab with rfl | hyb
            · simp [hτa_ne]
            · simp [hyb, hττa]
          · have hya : y ≠ a := fun h => hyU (h ▸ ha)
            have hyb : y ≠ τ a := fun h => hyU (h ▸ hτa_mem)
            simp [hτ.1.2 y hyU, Equiv.swap_apply_of_ne_of_ne hya hyb]
        · simp only [U', Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hy
          obtain ⟨hyU, hya, hyb⟩ := hy
          obtain ⟨hτy_ne, hττy⟩ := hτ.2 y hyU
          have hτya : τ y ≠ a := fun h => hyb (by rw [← h, hττy])
          have hτyb : τ y ≠ τ a := fun h => hya (τ.injective h)
          simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hτya hτyb]
          exact ⟨hτy_ne, by simp [hττy, Equiv.swap_apply_of_ne_of_ne hya hyb]⟩
      have hev := ih U' hU'_ss ⟨_, hτ'_mem⟩
      have hcard : U.card = U'.card + 2 := by
        have hsub : {a, τ a} ⊆ U := by intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy; rcases hy with rfl | rfl <;> assumption
        have hc2 : ({a, τ a} : Finset α).card = 2 := Finset.card_pair hτa_ne.symm
        have := Finset.card_sdiff_add_card_inter U {a, τ a}
        rw [Finset.inter_eq_right.mpr hsub, hc2] at this
        change U'.card + 2 = U.card at this
        exact this.symm
      rw [hcard]
      exact hev.add ⟨1, rfl⟩

omit [Fintype α] [Inv R] in
lemma cycChain_mul_right (c : α → R) (w : α → α → R) (endPt : α) :
    ∀ (cur : α) (l : List α),
      (endPt :: l).Nodup →
      cycChain (fun u v => c v * w u v) endPt cur l =
        c endPt * (∏ y ∈ l.toFinset, c y) * cycChain w endPt cur l
  | cur, [], _ => by simp [cycChain]
  | cur, b :: t, hnd => by
    have hnd' : (endPt :: t).Nodup := by
      rw [List.nodup_cons] at hnd ⊢
      exact ⟨fun h => hnd.1 (List.mem_cons_of_mem b h), (List.nodup_cons.mp hnd.2).2⟩
    have hbt : b ∉ t := (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1
    have hbt' : b ∉ t.toFinset := by rwa [List.mem_toFinset]
    simp only [cycChain, List.toFinset_cons, Finset.prod_insert hbt']
    rw [cycChain_mul_right c w endPt b t hnd']
    ring

omit [Fintype α] [Inv R] in
lemma cycSum_mul_right (c : α → R) (w : α → α → R) (a : α) {U : Finset α} (haU : a ∉ U) :
    cycSum (fun u v => c v * w u v) a U = (∏ u ∈ insert a U, c u) * cycSum w a U := by
  simp only [cycSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  have ⟨hl_nd, hl_fin⟩ := (mem_ordLists U l).mp hl
  have hal : a ∉ l := fun h => haU (hl_fin ▸ List.mem_toFinset.mpr h)
  have hnd : (a :: l).Nodup := List.nodup_cons.mpr ⟨hal, hl_nd⟩
  rw [cycChain_mul_right c w a a l hnd, hl_fin, Finset.prod_insert haU]

lemma permOn_gVal_eq_match (hinv : ∀ v : R, IsUnit v → v * v⁻¹ = 1) {x : α → R}
    (hx : ∀ a b, a ≠ b → IsUnit (x a - x b)) :
    ∀ S : Finset α, permOn S (fun a b => (2 * x b) * gVal x a b) = matchWeight x S := by
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    by_cases hS : S = ∅
    · subst hS; rw [permOn_empty, matchWeight_empty]
    · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hS
      rw [permOn_peel S ha, matchWeight_peel x ha]
      have hsingle : ∀ U ∈ (S.erase a).powerset, U.card ≠ 1 →
          cycSum (fun u v => (2 * x v) * gVal x u v) a U = 0 := by
        intro U hU hne1
        rw [Finset.mem_powerset] at hU
        have haU : a ∉ U := fun h => (Finset.notMem_erase a S) (hU h)
        rw [cycSum_mul_right (fun v => 2 * x v) (gVal x) a haU]
        rcases Nat.lt_trichotomy U.card 1 with _ | h1 | h2
        · have hU0 : U = ∅ := Finset.card_eq_zero.mp (by omega)
          subst hU0
          simp [cycSum_empty, gVal]
        · exact (hne1 h1).elim
        · rw [cycSum_gVal_eq_zero hinv hx haU h2, mul_zero]
      have hkeep :
          ∑ U ∈ (S.erase a).powerset,
              cycSum (fun u v => (2 * x v) * gVal x u v) a U *
                permOn (S \ insert a U) (fun u v => (2 * x v) * gVal x u v) =
            ∑ U ∈ (S.erase a).powersetCard 1,
              cycSum (fun u v => (2 * x v) * gVal x u v) a U *
                permOn (S \ insert a U) (fun u v => (2 * x v) * gVal x u v) := by
        have hsub_pc : (S.erase a).powersetCard 1 ⊆ (S.erase a).powerset :=
          fun U hU => Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hU).1
        rw [← Finset.sum_subset hsub_pc]
        intro U hU hU1
        have hne1 : U.card ≠ 1 := fun h => hU1 (Finset.mem_powersetCard.mpr ⟨Finset.mem_powerset.mp hU, h⟩)
        rw [hsingle U hU hne1, zero_mul]
      rw [hkeep]
      refine Finset.sum_bij'
        (fun U hU => Classical.choose (Finset.card_eq_one.mp (Finset.mem_powersetCard.mp hU).2))
        (fun b _ => {b})
        ?_ ?_ ?_ ?_ ?_
      · intro U hU
        have h1 := (Finset.mem_powersetCard.mp hU).2
        have hUeq : U = {Classical.choose (Finset.card_eq_one.mp h1)} :=
          Classical.choose_spec (Finset.card_eq_one.mp h1)
        have hmem := (Finset.mem_powersetCard.mp hU).1
        rw [hUeq] at hmem
        exact hmem (Finset.mem_singleton_self _)
      · intro b hb; exact Finset.mem_powersetCard.mpr ⟨Finset.singleton_subset_iff.mpr hb, Finset.card_singleton b⟩
      · intro U hU
        exact (Classical.choose_spec (Finset.card_eq_one.mp (Finset.mem_powersetCard.mp hU).2)).symm
      · intro _ _; simp
      · intro U hU
        have h1 := (Finset.mem_powersetCard.mp hU).2
        set b := Classical.choose (Finset.card_eq_one.mp h1)
        have hUeq : U = {b} := Classical.choose_spec (Finset.card_eq_one.mp h1)
        conv_lhs => rw [hUeq]
        rw [cycSum_singleton]
        have hsub : S \ insert a {b} ⊂ S := by
          rw [Finset.ssubset_iff_of_subset Finset.sdiff_subset]
          exact ⟨a, ha, by simp⟩
        rw [ih _ hsub]
        have hpair : insert a ({b} : Finset α) = {a, b} := by ext; simp
        rw [hpair, mVal]
        ring

lemma permOn_fVal_eq_match (hinv : ∀ v : R, IsUnit v → v * v⁻¹ = 1) {x : α → R}
    (hx : ∀ a b, a ≠ b → IsUnit (x a - x b)) :
    ∀ S : Finset α, permOn S (fVal x) = ∑ V ∈ S.powerset, matchWeight x V * (wSeq (S \ V).card : R) := by
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    by_cases hS : S = ∅
    · subst hS; simp [permOn_empty, matchWeight_empty, wSeq_zero]
    · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hS
      let S' := S.erase a
      have haS' : a ∉ S' := Finset.notMem_erase a S
      rw [permOn_peel S ha]
      have hcyc_eq : ∀ U ∈ S'.powerset,
          cycSum (fVal x) a U =
            (if U.card = 1 then ∑ b ∈ U, mVal x a b else 0) +
              (if U = ∅ then 1 else - (hSeq U.card : R)) := by
        intro U hU
        rw [Finset.mem_powerset] at hU
        have haU : a ∉ U := fun h => haS' (hU h)
        by_cases hU0 : U = ∅
        · subst hU0; simp [cycSum_empty, fVal]
        · by_cases hU1 : U.card = 1
          · obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp hU1
            have hab : a ≠ b := fun h => haU (by simp [h])
            simp only [Finset.card_singleton, ↓reduceIte, Finset.sum_singleton, hU0, hSeq_one,
              Int.cast_one]
            rw [cycSum_singleton, ← one_add_fVal_mul hinv hx hab]
            ring
          · have hU2 : 2 ≤ U.card := by have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hU0); omega
            simp only [hU1, ↓reduceIte, hU0, zero_add]
            exact cycSum_fVal_eq_neg_hSeq hinv hx haU hU2
      have hsplit1 :
          ∑ U ∈ S'.powerset, cycSum (fVal x) a U * permOn (S \ insert a U) (fVal x) =
            (∑ U ∈ S'.powerset, (if U.card = 1 then ∑ b ∈ U, mVal x a b else 0) * permOn (S \ insert a U) (fVal x)) +
            (∑ U ∈ S'.powerset, (if U = ∅ then (1 : R) else - (hSeq U.card : R)) * permOn (S \ insert a U) (fVal x)) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro U hU
        rw [hcyc_eq U hU, add_mul]
      rw [hsplit1]
      have hpart1 :
          ∑ U ∈ S'.powerset, (if U.card = 1 then ∑ b ∈ U, mVal x a b else 0) * permOn (S \ insert a U) (fVal x) =
            ∑ V ∈ S.powerset.filter (fun V => a ∈ V), matchWeight x V * (wSeq (S \ V).card : R) := by
        have hp1 :
            ∑ U ∈ S'.powerset, (if U.card = 1 then ∑ b ∈ U, mVal x a b else 0) * permOn (S \ insert a U) (fVal x) =
              ∑ b ∈ S', mVal x a b * permOn (S \ {a, b}) (fVal x) := by
          have hkeep1 :
              ∑ U ∈ S'.powerset, (if U.card = 1 then ∑ b ∈ U, mVal x a b else 0) * permOn (S \ insert a U) (fVal x) =
                ∑ U ∈ S'.powersetCard 1, (if U.card = 1 then ∑ b ∈ U, mVal x a b else 0) * permOn (S \ insert a U) (fVal x) := by
            have hsub_pc : S'.powersetCard 1 ⊆ S'.powerset :=
              fun U hU => Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hU).1
            rw [← Finset.sum_subset hsub_pc]
            intro U hU hU1
            have hne1 : U.card ≠ 1 := fun h => hU1 (Finset.mem_powersetCard.mpr ⟨Finset.mem_powerset.mp hU, h⟩)
            simp [hne1]
          rw [hkeep1]
          refine Finset.sum_bij'
            (fun U hU => Classical.choose (Finset.card_eq_one.mp (Finset.mem_powersetCard.mp hU).2))
            (fun b _ => {b})
            ?_ ?_ ?_ ?_ ?_
          · intro U hU
            have h1 := (Finset.mem_powersetCard.mp hU).2
            have hUeq := Classical.choose_spec (Finset.card_eq_one.mp h1)
            have hmem := (Finset.mem_powersetCard.mp hU).1
            rw [hUeq] at hmem; exact hmem (Finset.mem_singleton_self _)
          · intro b hb; exact Finset.mem_powersetCard.mpr ⟨Finset.singleton_subset_iff.mpr hb, Finset.card_singleton b⟩
          · intro U hU; exact (Classical.choose_spec (Finset.card_eq_one.mp (Finset.mem_powersetCard.mp hU).2)).symm
          · intro _ _; simp
          · intro U hU
            have h1 := (Finset.mem_powersetCard.mp hU).2
            set b := Classical.choose (Finset.card_eq_one.mp h1)
            have hUeq := Classical.choose_spec (Finset.card_eq_one.mp h1)
            conv_lhs => rw [hUeq]
            simp only [Finset.card_singleton, ↓reduceIte, Finset.sum_singleton]
            have hpair : insert a ({b} : Finset α) = {a, b} := by ext; simp
            rw [hpair]
        rw [hp1]
        have hih1 : ∀ b ∈ S',
            permOn (S \ {a, b}) (fVal x) =
              ∑ W ∈ (S \ {a, b}).powerset, matchWeight x W * (wSeq ((S \ {a, b}) \ W).card : R) := by
          intro b _
          apply ih
          rw [Finset.ssubset_iff_of_subset Finset.sdiff_subset]
          exact ⟨a, ha, by simp⟩
        rw [Finset.sum_congr rfl (fun b hb => by rw [hih1 b hb, Finset.mul_sum])]
        have hsigL :
            ∑ b ∈ S', ∑ W ∈ (S \ {a, b}).powerset,
                mVal x a b * (matchWeight x W * (wSeq ((S \ {a, b}) \ W).card : R)) =
              ∑ bw ∈ S'.sigma (fun b => (S \ {a, b}).powerset),
                mVal x a bw.1 * matchWeight x bw.2 * (wSeq (S \ insert a (insert bw.1 bw.2)).card : R) := by
          rw [Finset.sum_sigma' _ _ (fun b W => mVal x a b * (matchWeight x W * (wSeq ((S \ {a, b}) \ W).card : R)))]
          apply Finset.sum_congr rfl
          rintro ⟨b, W⟩ _
          have hs : (S \ {a, b}) \ W = S \ insert a (insert b W) := by
            ext u; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]; tauto
          rw [hs]; ring
        have hsigR :
            ∑ V ∈ S.powerset.filter (fun V => a ∈ V), matchWeight x V * (wSeq (S \ V).card : R) =
              ∑ Vb ∈ (S.powerset.filter (fun V => a ∈ V)).sigma (fun V => V.erase a),
                mVal x a Vb.2 * matchWeight x (Vb.1 \ {a, Vb.2}) * (wSeq (S \ Vb.1).card : R) := by
          rw [← Finset.sum_sigma' _ _ (fun V b => mVal x a b * matchWeight x (V \ {a, b}) * (wSeq (S \ V).card : R))]
          apply Finset.sum_congr rfl
          intro V hV
          have haV : a ∈ V := (Finset.mem_filter.mp hV).2
          rw [matchWeight_peel x haV, Finset.sum_mul]
        rw [hsigL, hsigR]
        refine Finset.sum_bij'
          (fun bw _ => ⟨insert a (insert bw.1 bw.2), bw.1⟩)
          (fun Vb _ => ⟨Vb.2, Vb.1 \ {a, Vb.2}⟩)
          ?_ ?_ ?_ ?_ ?_
        · rintro ⟨b, W⟩ hbw
          rw [Finset.mem_sigma, Finset.mem_powerset] at hbw
          have hbS : b ∈ S := Finset.erase_subset a S hbw.1
          have hWS : W ⊆ S := hbw.2.trans Finset.sdiff_subset
          rw [Finset.mem_sigma, Finset.mem_filter, Finset.mem_powerset, Finset.mem_erase]
          have hba : b ≠ a := (Finset.mem_erase.mp hbw.1).1
          exact ⟨⟨fun u hu => by simp only [Finset.mem_insert] at hu; rcases hu with rfl | rfl | hu; exact ha; exact hbS; exact hWS hu,
            Finset.mem_insert_self a _⟩, hba, Finset.mem_insert_of_mem (Finset.mem_insert_self b W)⟩
        · rintro ⟨V, b⟩ hVb
          rw [Finset.mem_sigma, Finset.mem_filter, Finset.mem_powerset, Finset.mem_erase] at hVb
          rw [Finset.mem_sigma, Finset.mem_powerset]
          exact ⟨Finset.mem_erase.mpr ⟨hVb.2.1, hVb.1.1 hVb.2.2⟩,
            Finset.sdiff_subset_sdiff hVb.1.1 Finset.Subset.rfl⟩
        · rintro ⟨b, W⟩ hbw
          rw [Finset.mem_sigma, Finset.mem_powerset] at hbw
          have hba : b ≠ a := (Finset.mem_erase.mp hbw.1).1
          have haW : a ∉ W := fun h => by have := hbw.2 h; simp at this
          have hbW : b ∉ W := fun h => by have := hbw.2 h; simp at this
          dsimp
          ext1
          · rfl
          · apply heq_of_eq
            ext u; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
            constructor
            · rintro ⟨rfl | rfl | hu, hne⟩ <;> tauto
            · intro hu; exact ⟨Or.inr (Or.inr hu), fun h => by rcases h with rfl | rfl <;> contradiction⟩
        · rintro ⟨V, b⟩ hVb
          rw [Finset.mem_sigma, Finset.mem_filter, Finset.mem_erase] at hVb
          dsimp
          refine Sigma.ext ?_ (heq_of_eq rfl)
          ext u; simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton]
          constructor
          · rintro (rfl | rfl | ⟨hu, _⟩); exact hVb.1.2; exact hVb.2.2; exact hu
          · intro hu; by_cases hua : u = a; exact Or.inl hua; by_cases hub : u = b; exact Or.inr (Or.inl hub); exact Or.inr (Or.inr ⟨hu, by tauto⟩)
        · rintro ⟨b, W⟩ hbw
          rw [Finset.mem_sigma, Finset.mem_powerset] at hbw
          have hba : b ≠ a := (Finset.mem_erase.mp hbw.1).1
          have haW : a ∉ W := fun h => by have := hbw.2 h; simp at this
          have hbW : b ∉ W := fun h => by have := hbw.2 h; simp at this
          dsimp
          have hs : insert a (insert b W) \ {a, b} = W := by
            ext u; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]; constructor
            · rintro ⟨rfl | rfl | hu, hne⟩ <;> tauto
            · intro hu; exact ⟨Or.inr (Or.inr hu), fun h => by rcases h with rfl | rfl <;> contradiction⟩
          rw [hs]
      have hpart2 :
          ∑ U ∈ S'.powerset, (if U = ∅ then (1 : R) else - (hSeq U.card : R)) * permOn (S \ insert a U) (fVal x) =
            ∑ V ∈ S.powerset.filter (fun V => a ∉ V), matchWeight x V * (wSeq (S \ V).card : R) := by
        have hSdiff : ∀ U ∈ S'.powerset, S \ insert a U = S' \ U := by
          intro U _
          ext u; simp only [Finset.mem_sdiff, Finset.mem_insert, S', Finset.mem_erase]; tauto
        have hih2 : ∀ U ∈ S'.powerset,
            permOn (S \ insert a U) (fVal x) =
              ∑ V ∈ (S' \ U).powerset, matchWeight x V * (wSeq ((S' \ U) \ V).card : R) := by
          intro U hU
          rw [hSdiff U hU]
          apply ih
          exact (Finset.sdiff_subset).trans_ssubset (Finset.erase_ssubset ha)
        rw [Finset.sum_congr rfl (fun U hU => by rw [hih2 U hU, Finset.mul_sum])]
        have hswap :
            ∑ U ∈ S'.powerset, ∑ V ∈ (S' \ U).powerset,
                (if U = ∅ then (1 : R) else - (hSeq U.card : R)) * (matchWeight x V * (wSeq ((S' \ U) \ V).card : R)) =
              ∑ V ∈ S'.powerset, matchWeight x V *
                ((wSeq (S' \ V).card : R) -
                  ∑ U ∈ (S' \ V).powerset.filter Finset.Nonempty,
                    (hSeq U.card : R) * (wSeq ((S' \ V) \ U).card : R)) := by
          have hsig1 :
              ∑ U ∈ S'.powerset, ∑ V ∈ (S' \ U).powerset,
                  (if U = ∅ then (1 : R) else - (hSeq U.card : R)) * (matchWeight x V * (wSeq ((S' \ U) \ V).card : R)) =
                ∑ UV ∈ S'.powerset.sigma (fun U => (S' \ U).powerset),
                  (if UV.1 = ∅ then (1 : R) else - (hSeq UV.1.card : R)) * (matchWeight x UV.2 * (wSeq ((S' \ UV.1) \ UV.2).card : R)) :=
            Finset.sum_sigma' _ _ _
          have hsig2 :
              ∑ V ∈ S'.powerset, ∑ U ∈ (S' \ V).powerset,
                  (if U = ∅ then (1 : R) else - (hSeq U.card : R)) * (matchWeight x V * (wSeq ((S' \ V) \ U).card : R)) =
                ∑ VU ∈ S'.powerset.sigma (fun V => (S' \ V).powerset),
                  (if VU.2 = ∅ then (1 : R) else - (hSeq VU.2.card : R)) * (matchWeight x VU.1 * (wSeq ((S' \ VU.1) \ VU.2).card : R)) :=
            Finset.sum_sigma' _ _ _
          have hswap_eq :
              ∑ U ∈ S'.powerset, ∑ V ∈ (S' \ U).powerset,
                  (if U = ∅ then (1 : R) else - (hSeq U.card : R)) * (matchWeight x V * (wSeq ((S' \ U) \ V).card : R)) =
                ∑ V ∈ S'.powerset, ∑ U ∈ (S' \ V).powerset,
                  (if U = ∅ then (1 : R) else - (hSeq U.card : R)) * (matchWeight x V * (wSeq ((S' \ V) \ U).card : R)) := by
            rw [hsig1, hsig2]
            refine Finset.sum_bij' (fun p _ => ⟨p.2, p.1⟩) (fun p _ => ⟨p.2, p.1⟩) ?_ ?_ ?_ ?_ ?_
            · rintro ⟨U, V⟩ hp; rw [Finset.mem_sigma, Finset.mem_powerset, Finset.mem_powerset] at hp ⊢
              exact ⟨hp.2.trans Finset.sdiff_subset, Finset.subset_sdiff.mpr ⟨hp.1, (Finset.subset_sdiff.mp hp.2).2.symm⟩⟩
            · rintro ⟨V, U⟩ hp; rw [Finset.mem_sigma, Finset.mem_powerset, Finset.mem_powerset] at hp ⊢
              exact ⟨hp.2.trans Finset.sdiff_subset, Finset.subset_sdiff.mpr ⟨hp.1, (Finset.subset_sdiff.mp hp.2).2.symm⟩⟩
            · rintro ⟨U, V⟩ _; rfl
            · rintro ⟨V, U⟩ _; rfl
            · rintro ⟨U, V⟩ _; dsimp
              have hs : (S' \ U) \ V = (S' \ V) \ U := by
                ext z; simp only [Finset.mem_sdiff]; tauto
              rw [hs]
          rw [hswap_eq]
          apply Finset.sum_congr rfl
          intro V _
          rw [← Finset.sum_filter_add_sum_filter_not ((S' \ V).powerset) (· = ∅)]
          have hf1 : (S' \ V).powerset.filter (· = ∅) = {∅} := by
            ext U; simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
            exact ⟨fun h => h.2, fun h => ⟨h ▸ Finset.empty_subset _, h⟩⟩
          have hf2 : (S' \ V).powerset.filter (fun U => ¬ U = ∅) = (S' \ V).powerset.filter Finset.Nonempty := by
            ext U; simp [Finset.nonempty_iff_ne_empty]
          rw [hf1, hf2, Finset.sum_singleton]
          simp only [↓reduceIte, one_mul, Finset.sdiff_empty]
          have hneg : ∑ U ∈ (S' \ V).powerset.filter Finset.Nonempty,
              (if U = ∅ then (1 : R) else - (hSeq U.card : R)) * (matchWeight x V * (wSeq ((S' \ V) \ U).card : R)) =
              - (matchWeight x V * ∑ U ∈ (S' \ V).powerset.filter Finset.Nonempty,
                  (hSeq U.card : R) * (wSeq ((S' \ V) \ U).card : R)) := by
            rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro U hU
            have hne : U ≠ ∅ := Finset.nonempty_iff_ne_empty.mp (Finset.mem_filter.mp hU).2
            simp only [hne, ↓reduceIte]; ring
          rw [hneg]
          ring
        rw [hswap]
        have hS'_pow : S'.powerset = S.powerset.filter (fun V => a ∉ V) := by
          ext V; simp only [Finset.mem_powerset, Finset.mem_filter, S', Finset.subset_erase]
        rw [hS'_pow]
        apply Finset.sum_congr rfl
        intro V hV
        let T := S' \ V
        have hTcard : (S \ V).card = T.card + 1 := by
          have hs : S \ V = insert a T := by
            have haV : a ∉ V := (Finset.mem_filter.mp hV).2
            ext u; simp only [T, S', Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
            constructor
            · rintro ⟨huS, huV⟩
              by_cases hua : u = a
              · exact Or.inl hua
              · exact Or.inr ⟨⟨hua, huS⟩, huV⟩
            · rintro (rfl | ⟨⟨_, huS⟩, huV⟩)
              · exact ⟨ha, haV⟩
              · exact ⟨huS, huV⟩
          have haT : a ∉ T := fun h => haS' (Finset.sdiff_subset h)
          rw [hs, Finset.card_insert_of_notMem haT]
        rw [hTcard]
        congr 1
        have hpartT : T.powerset.filter Finset.Nonempty =
            (Finset.Ico 1 (T.card + 1)).biUnion (fun k => T.powersetCard k) := by
          ext U
          simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_biUnion,
            Finset.mem_Ico, Finset.mem_powersetCard]
          constructor
          · rintro ⟨hUT, hUne⟩
            exact ⟨U.card, ⟨hUne.card_pos, Nat.lt_succ_of_le (Finset.card_le_card hUT)⟩, hUT, rfl⟩
          · rintro ⟨k, ⟨hk1, _⟩, hUT, rfl⟩
            exact ⟨hUT, Finset.card_pos.mp hk1⟩
        rw [hpartT, Finset.sum_biUnion]
        · have hterm : ∀ k ∈ Finset.Ico 1 (T.card + 1),
              ∑ U ∈ T.powersetCard k, (hSeq U.card : R) * (wSeq (T \ U).card : R) =
                ((T.card.choose k : ℤ) * hSeq k * wSeq (T.card - k) : R) := by
            intro k _
            have h1 : ∀ U ∈ T.powersetCard k,
                (hSeq U.card : R) * (wSeq (T \ U).card : R) = (hSeq k : R) * (wSeq (T.card - k) : R) := by
              intro U hU
              rw [Finset.mem_powersetCard] at hU
              rw [hU.2, Finset.card_sdiff_of_subset hU.1, hU.2]
            rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]
            push_cast; ring
          rw [Finset.sum_congr rfl hterm, wSeq_succ]
          push_cast; ring
        · intro i _ j _ hij
          dsimp only [Function.onFun]
          rw [Finset.disjoint_left]
          intro B hB1 hB2
          rw [Finset.mem_powersetCard] at hB1 hB2
          exact hij (hB1.2.symm.trans hB2.2)
      rw [hpart1, hpart2, add_comm]
      simpa only [not_not] using
        Finset.sum_filter_add_sum_filter_not S.powerset (fun V => a ∉ V)
          (fun V => matchWeight x V * (wSeq (S \ V).card : R))

lemma perm_fVal_eq_perm_gVal (hinv : ∀ v : R, IsUnit v → v * v⁻¹ = 1) {x : α → R}
    (hx : ∀ a b, a ≠ b → IsUnit (x a - x b)) {S : Finset α} (hSev : Even S.card) :
    permOn S (fVal x) = permOn S (fun a b => (2 * x b) * gVal x a b) := by
  rw [permOn_fVal_eq_match hinv hx S, permOn_gVal_eq_match hinv hx S]
  rw [Finset.sum_eq_single S]
  · simp [wSeq_zero]
  · intro V hV hVS
    by_cases hne : (invSet V).Nonempty
    · have hVev := even_card_of_invSet_nonempty V hne
      have hVS_sub := Finset.mem_powerset.mp hV
      have hlt : V.card < S.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hVS_sub, hVS⟩)
      obtain ⟨s, hs⟩ := hSev
      obtain ⟨v, hv⟩ := hVev
      have hdiff : (S \ V).card = 2 * (s - v) := by
        rw [Finset.card_sdiff_of_subset hVS_sub]; omega
      have hr : 1 ≤ s - v := by omega
      rw [hdiff, wSeq_even_pos (s - v) hr]
      simp
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      simp [matchWeight, hne]
  · intro h; exact (h (Finset.mem_powerset.mpr Finset.Subset.rfl)).elim

end PermDecomp

theorem OMA.solution : OMA.R_OeisA1818_conjecture2_R1.H1 := by
  intro p hp hne2
  let R := ZMod (p ^ 2)
  let x : Fin (p - 1) → R := fun i => (i.val : R) + 1
  have hinv : ∀ v : R, IsUnit v → v * v⁻¹ = 1 := ZMod.mul_inv_of_unit
  have hx : ∀ a b : Fin (p - 1), a ≠ b → IsUnit (x a - x b) := by
    intro a b hab
    have hne_val : a.val ≠ b.val := fun h => hab (Fin.ext h)
    by_cases hgt : b.val < a.val
    · have hsub : x a - x b = ((a.val - b.val : ℕ) : R) := by
        dsimp [x]
        rw [Nat.cast_sub hgt.le]
        ring
      rw [hsub, ZMod.isUnit_iff_coprime]
      have hpos : 0 < a.val - b.val := by omega
      have hlt : a.val - b.val < p := by omega
      exact ((hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hpos hlt)).symm).pow_right 2
    · have hlt_ab : a.val < b.val := by omega
      have hsub : x a - x b = - ((b.val - a.val : ℕ) : R) := by
        dsimp [x]
        rw [Nat.cast_sub hlt_ab.le]
        ring
      rw [hsub]
      apply IsUnit.neg
      rw [ZMod.isUnit_iff_coprime]
      have hpos : 0 < b.val - a.val := by omega
      have hlt : b.val - a.val < p := by omega
      exact ((hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hpos hlt)).symm).pow_right 2
  have hev : Even (Finset.univ : Finset (Fin (p - 1))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    have hodd := hp.odd_of_ne_two hne2
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k, by omega⟩
  let M1 : Matrix (Fin (p - 1)) (Fin (p - 1)) R :=
    fun i j => OeisA1818.fEntry (p := p) (i.val + 1) (j.val + 1)
  let M2 : Matrix (Fin (p - 1)) (Fin (p - 1)) R :=
    fun i j => if i = j then 0 else ((i.val : R) - j.val)⁻¹
  have hL : M1.permanent = permOn Finset.univ (fVal x) := by
    rw [← Matrix.permanent_transpose M1, Matrix.permanent]
    have hp_univ : permSet (Finset.univ : Finset (Fin (p - 1))) = Finset.univ := by
      ext σ; simp [permSet]
    rw [permOn, hp_univ]
    apply Finset.sum_congr rfl
    intro σ _
    apply Finset.prod_congr rfl
    intro i _
    rw [Matrix.transpose_apply]
    dsimp only [M1, fVal]
    unfold OeisA1818.fEntry
    by_cases h : i = σ i
    · have heq : i.val + 1 = (σ i).val + 1 := congrArg (fun k : Fin (p - 1) => k.val + 1) h
      rw [if_pos heq, if_pos h]
    · have hne_succ : i.val + 1 ≠ (σ i).val + 1 := fun heq => h (Fin.ext (by omega))
      rw [if_neg hne_succ, if_neg h]
      dsimp only [x]
      congr 1
      · push_cast; ring
      · congr 1; push_cast; ring
  have hR :
      (∏ i ∈ Finset.range (p - 1), 2 * ((i : R) + 1)) * M2.permanent =
        permOn Finset.univ (fun a b => (2 * x b) * gVal x a b) := by
    rw [← Matrix.permanent_transpose M2, Matrix.permanent]
    have hp_univ : permSet (Finset.univ : Finset (Fin (p - 1))) = Finset.univ := by
      ext σ; simp [permSet]
    rw [permOn, hp_univ, Finset.mul_sum]
    have hprod_eq : (∏ i ∈ Finset.range (p - 1), 2 * ((i : R) + 1)) = ∏ i : Fin (p - 1), 2 * x i := by
      rw [← Fin.prod_univ_eq_prod_range (fun i => 2 * ((i : R) + 1)) (p - 1)]
    rw [hprod_eq]
    apply Finset.sum_congr rfl
    intro σ _
    have hσ_prod : (∏ i : Fin (p - 1), 2 * x i) = ∏ i : Fin (p - 1), 2 * x (σ i) := by
      symm; exact Fintype.prod_equiv σ _ _ (fun _ => rfl)
    rw [hσ_prod, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [Matrix.transpose_apply]
    dsimp only [M2, gVal]
    by_cases h : i = σ i
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]
      have hsub : (i.val : R) - (σ i).val = x i - x (σ i) := by dsimp only [x]; ring
      rw [hsub]
  change M1.permanent = (∏ i ∈ Finset.range (p - 1), 2 * ((i : R) + 1)) * M2.permanent
  rw [hL, hR]
  exact perm_fVal_eq_perm_gVal hinv hx hev
