import OMAStatements.S_oeis_a057566
import Mathlib

namespace GridTriples

open OMA.S_oeis_a057566

private abbrev Point (n : ℕ) := Fin 3 × Fin n

private abbrev Triple (n : ℕ) :=
  {S : Finset (Point n) // S.card = 3 ∧ ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S,
    Collinear3 ((p.1 : ℤ), (p.2 : ℤ)) ((q.1 : ℤ), (q.2 : ℤ)) ((r.1 : ℤ), (r.2 : ℤ))}

private abbrev Column (n : ℕ) := Fin 3 × {T : Finset (Fin n) // T.card = 3}
private abbrev Progression (n : ℕ) :=
  {f : Fin 3 → Fin n // (f 0 : ℕ) + (f 2 : ℕ) = 2 * (f 1 : ℕ)}

private def column {n : ℕ} (j : Fin 3) (T : Finset (Fin n)) : Finset (Point n) :=
  T.image fun y => (j, y)

private def graph {n : ℕ} (f : Fin 3 → Fin n) : Finset (Point n) :=
  Finset.univ.image fun j => (j, f j)

@[simp] private theorem mem_column {n : ℕ} {p : Point n} {j : Fin 3} {T : Finset (Fin n)} :
    p ∈ column j T ↔ p.1 = j ∧ p.2 ∈ T := by
  rcases p with ⟨x,y⟩
  constructor
  · intro h
    obtain ⟨v,hv,e⟩ := Finset.mem_image.mp h
    simp_all
  · rintro ⟨rfl,hy⟩
    exact Finset.mem_image.mpr ⟨y,hy,rfl⟩

@[simp] private theorem mem_graph {n : ℕ} {p : Point n} {f : Fin 3 → Fin n} :
    p ∈ graph f ↔ p.2 = f p.1 := by
  rcases p with ⟨x,y⟩
  constructor
  · intro h
    obtain ⟨j,_,e⟩ := Finset.mem_image.mp h
    rcases Prod.mk.inj e with ⟨e₁,e₂⟩
    exact e₂.symm.trans (congrArg f e₁)
  · intro h
    change y = f x at h
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, congrArg (Prod.mk x) h.symm⟩

private def build {n : ℕ} : Column n ⊕ Progression n → Triple n
  | .inl ⟨j,T⟩ => ⟨column j T, by
      rw [column, Finset.card_image_of_injective _ (fun _ _ e => congrArg Prod.snd e)]
      exact T.2, by
      rintro p hp q hq r hr
      rw [mem_column] at hp hq hr
      simp [Collinear3, hp.1, hq.1, hr.1]⟩
  | .inr f => ⟨graph f, by
      unfold graph
      rw [Finset.card_image_of_injective _ (f := fun j : Fin 3 => (j, f.1 j))
        (fun _ _ e => congrArg Prod.fst e)]
      simp, by
      rintro ⟨i,x⟩ hi ⟨j,y⟩ hj ⟨k,z⟩ hk
      simp only [mem_graph] at hi hj hk
      change x = f.1 i at hi
      change y = f.1 j at hj
      change z = f.1 k at hk
      subst x; subst y; subst z
      have hf : (f.1 0 : ℤ) + (f.1 2 : ℤ) = 2 * (f.1 1 : ℤ) := by exact_mod_cast f.2
      have h₂ : (⟨2, by decide⟩ : Fin 3) = 2 := rfl
      fin_cases i <;> fin_cases j <;> fin_cases k <;>
        norm_num [Collinear3, h₂, Fin.val_zero, Fin.val_one, Fin.val_two] <;> linarith⟩

private theorem column_graph_ne {n : ℕ} (c : Column n) (f : Progression n) :
    column c.1 c.2.1 ≠ graph f.1 := by
  intro h
  have hj (i : Fin 3) : i = c.1 := by
    have hi : (i, f.1 i) ∈ graph f.1 := mem_graph.mpr rfl
    have he : (i, f.1 i) ∈ column c.1 c.2.1 := by rwa [h]
    exact (mem_column.mp he).1
  exact (by decide : (0 : Fin 3) ≠ 1) ((hj 0).trans (hj 1).symm)

private theorem build_inj (n : ℕ) : Function.Injective (@build n) := by
  intro u v huv
  have he := congrArg Subtype.val huv
  rcases u with u | u <;> rcases v with v | v
  · change column u.1 u.2.1 = column v.1 v.2.1 at he
    obtain ⟨x,hx⟩ := Finset.card_pos.mp (by rw [u.2.2]; decide : 0 < u.2.1.card)
    have hp : (u.1,x) ∈ column u.1 u.2.1 := mem_column.mpr ⟨rfl,hx⟩
    have ej : u.1 = v.1 := (mem_column.mp (he ▸ hp)).1
    congr 1
    apply Prod.ext ej
    apply Subtype.ext
    ext y
    have h := Finset.ext_iff.mp he (u.1,y)
    simpa [mem_column, ej] using h
  · exact (column_graph_ne u v he).elim
  · exact (column_graph_ne v u he.symm).elim
  · change graph u.1 = graph v.1 at he
    congr 1
    apply Subtype.ext
    funext i
    have h : (i,u.1 i) ∈ graph u.1 := mem_graph.mpr rfl
    exact mem_graph.mp (he ▸ h)

private theorem build_surj (n : ℕ) : Function.Surjective (@build n) := by
  classical
  rintro ⟨S,hcard,hcol⟩
  by_cases h : Set.InjOn Prod.fst (↑S : Set (Point n))
  · have hu : S.image Prod.fst = Finset.univ :=
      (Finset.card_eq_iff_eq_univ _).mp (by rw [Finset.card_image_of_injOn h,hcard]; simp)
    have he (i : Fin 3) : ∃ y : Fin n, (i,y) ∈ S := by
      have hi : i ∈ S.image Prod.fst := by simp [hu]
      obtain ⟨⟨j,y⟩,hp,eq⟩ := Finset.mem_image.mp hi
      change j = i at eq
      exact ⟨y,eq ▸ hp⟩
    choose f hf using he
    have hprog : (f 0 : ℕ) + (f 2 : ℕ) = 2 * (f 1 : ℕ) := by
      have hc := hcol (0,f 0) (hf 0) (1,f 1) (hf 1) (2,f 2) (hf 2)
      change (1 - 0 : ℤ) * ((f 2 : ℤ) - (f 0 : ℤ)) -
        ((f 1 : ℤ) - (f 0 : ℤ)) * (2 - 0) = 0 at hc
      exact_mod_cast (show (f 0 : ℤ) + (f 2 : ℤ) = 2 * (f 1 : ℤ) by linarith)
    refine ⟨.inr ⟨f,hprog⟩, Subtype.ext ?_⟩
    change graph f = S
    ext ⟨i,y⟩
    rw [mem_graph]
    constructor
    · intro hy
      change y = f i at hy
      subst y
      exact hf i
    · intro hy
      exact congrArg Prod.snd (h hy (hf i) rfl)
  · unfold Set.InjOn at h
    push Not at h
    obtain ⟨p,hp,q,hq,hpq,hd⟩ := h
    have hy : (q.2 : ℤ) - (p.2 : ℤ) ≠ 0 := by
      intro hz
      have hval : (q.2 : ℤ) = (p.2 : ℤ) := sub_eq_zero.mp hz
      exact hd (Prod.ext hpq (Fin.ext (by exact_mod_cast hval.symm)))
    have all_x (r : Point n) (hr : r ∈ S) : r.1 = p.1 := by
      have hc := hcol p hp q hq r hr
      unfold Collinear3 at hc
      rw [← hpq] at hc
      simp only [sub_self, zero_mul, zero_sub, neg_eq_zero] at hc
      have hv := sub_eq_zero.mp ((mul_eq_zero.mp hc).resolve_left hy)
      exact Fin.ext (by exact_mod_cast hv)
    let ys := S.image Prod.snd
    have hycard : ys.card = 3 := by
      rw [Finset.card_image_of_injOn (fun a ha b hb e => Prod.ext ((all_x a ha).trans (all_x b hb).symm) e),hcard]
    refine ⟨.inl ⟨p.1,ys,hycard⟩, Subtype.ext ?_⟩
    change column p.1 ys = S
    ext ⟨i,y⟩
    rw [mem_column]
    constructor
    · rintro ⟨rfl,hy⟩
      obtain ⟨⟨j,z⟩,hz,e⟩ := Finset.mem_image.mp hy
      have he := all_x (j,z) hz
      change j = p.1 at he
      change z = y at e
      exact he ▸ e ▸ hz
    · intro hz
      exact ⟨all_x (i,y) hz, Finset.mem_image.mpr ⟨(i,y),hz,rfl⟩⟩

private abbrev Endpoints (n : ℕ) :=
  Σ r : Fin 2, Fin ((n + 1 - r.val) / 2) × Fin ((n + 1 - r.val) / 2)

private def progression {n : ℕ} (v : Endpoints n) : Progression n := by
  rcases v with ⟨r,x,y⟩
  have hx := x.isLt
  have hy := y.isLt
  have hr := r.isLt
  let f : Fin 3 → Fin n :=
    ![⟨2 * x + r, by omega⟩, ⟨x + y + r, by omega⟩, ⟨2 * y + r, by omega⟩]
  exact ⟨f, by change 2 * x.val + r.val + (2 * y.val + r.val) =
    2 * (x.val + y.val + r.val); omega⟩

private theorem progression_bij (n : ℕ) : Function.Bijective (@progression n) := by
  constructor
  · rintro ⟨r,x,y⟩ ⟨s,z,w⟩ h
    have h₀ := congrArg (fun f : Progression n => (f.1 0 : ℕ)) h
    have h₂ := congrArg (fun f : Progression n => (f.1 2 : ℕ)) h
    change 2 * x.val + r.val = 2 * z.val + s.val at h₀
    change 2 * y.val + r.val = 2 * w.val + s.val at h₂
    have hr := r.isLt
    have hs := s.isLt
    have e : r = s := Fin.ext (by omega)
    subst s
    have ex : x = z := Fin.ext (by omega)
    have ey : y = w := Fin.ext (by omega)
    subst z; subst w
    rfl
  · intro f
    let l : ℕ := (f.1 0 : ℕ)
    let m : ℕ := (f.1 1 : ℕ)
    let r : ℕ := (f.1 2 : ℕ)
    have hl : l < n := (f.1 0).isLt
    have hr : r < n := (f.1 2).isLt
    have h : l + r = 2 * m := f.2
    let b : Fin 2 := ⟨l % 2, by omega⟩
    let x : Fin ((n + 1 - b.val) / 2) := ⟨l / 2, by dsimp [b]; omega⟩
    let y : Fin ((n + 1 - b.val) / 2) := ⟨r / 2, by dsimp [b]; omega⟩
    refine ⟨⟨b,x,y⟩, Subtype.ext (funext fun i => Fin.ext ?_)⟩
    fin_cases i
    · change 2 * (l / 2) + l % 2 = l
      omega
    · change l / 2 + r / 2 + l % 2 = m
      omega
    · change 2 * (r / 2) + l % 2 = r
      omega

private theorem count (n : ℕ) :
    a n = 3 * n.choose 3 + ((n + 1) / 2) ^ 2 + (n / 2) ^ 2 := by
  classical
  have h₁ := Fintype.card_congr (Equiv.ofBijective (@build n) ⟨build_inj n, build_surj n⟩)
  have h₂ := Fintype.card_congr (Equiv.ofBijective (@progression n) (progression_bij n))
  have hc : Fintype.card {T : Finset (Fin n) // T.card = 3} = n.choose 3 := by
    let P : Finset (Finset (Fin n)) := Finset.univ.powersetCard 3
    have hP : ∀ T : Finset (Fin n), T ∈ P ↔ T.card = 3 := by simp [P]
    rw [Fintype.card_congr (Equiv.subtypeEquivRight (fun T => (hP T).symm)),
      Fintype.card_coe, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have ha : a n = Fintype.card (Triple n) := by
    unfold a
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
    simp only [← Nat.card_eq_fintype_card]
    rfl
  rw [ha, ← h₁, Fintype.card_sum, Fintype.card_prod, hc, Fintype.card_fin, ← h₂,
    Fintype.card_sigma, Fin.sum_univ_two]
  simp [Fintype.card_prod, pow_two, add_assoc]

private def numerator (z : ℤ) : ℤ := 2 * z ^ 3 - 3 * z ^ 2 - 2 * z + 3

private theorem numerator_mod (z : ℤ) :
    numerator z % 24 = if z % 2 = 0 then 3 else 0 := by
  let r := z % 24
  have hr₀ : 0 ≤ r := Int.emod_nonneg _ (by decide)
  have hr₂₄ : r < 24 := Int.emod_lt_of_pos _ (by decide)
  have h : z ≡ r [ZMOD 24] := (Int.mod_modEq z 24).symm
  have h₂ : z % 2 = r % 2 := h.of_dvd (by decide)
  have hp : numerator z % 24 = numerator r % 24 :=
    ((((h.pow 3).mul_left 2).sub ((h.pow 2).mul_left 3)).sub (h.mul_left 2)).add_right 3
  rw [hp, h₂]
  interval_cases r <;> norm_num [numerator]

theorem prove (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℤ) = 5 * ((2 * n ^ 3 - 3 * n ^ 2 - 2 * n + 3 : ℤ) / 24) +
      ((2 * (n - 1) ^ 3 - 3 * (n - 1) ^ 2 - 2 * (n - 1) + 3 : ℤ) / 24) + n := by
  rw [count]
  have hc : (6 : ℤ) * (n.choose 3 : ℤ) = n * ((n : ℤ) - 1) * ((n : ℤ) - 2) := by
    by_cases h : 2 ≤ n
    · have he := Nat.descFactorial_eq_factorial_mul_choose n 3
      norm_num [Nat.descFactorial_succ, Nat.descFactorial_zero] at he
      have he' := congrArg (fun t : ℕ => (t : ℤ)) he
      push_cast [Nat.cast_sub h, Nat.cast_sub hn] at he'
      nlinarith only [he']
    · have he : n = 1 := by omega
      norm_num [he, Nat.choose_eq_zero_of_lt (by decide : 1 < 3)]
  push_cast
  change 3 * (n.choose 3 : ℤ) + (((n + 1) / 2 : ℕ) : ℤ) ^ 2 + ((n / 2 : ℕ) : ℤ) ^ 2 =
    5 * (numerator n / 24) + numerator ((n : ℤ) - 1) / 24 + n
  push_cast
  let z : ℤ := n
  change 3 * (n.choose 3 : ℤ) + ((z + 1) / 2) ^ 2 + (z / 2) ^ 2 =
    5 * (numerator z / 24) + numerator (z - 1) / 24 + z
  change (6 : ℤ) * (n.choose 3 : ℤ) = z * (z - 1) * (z - 2) at hc
  have h₀ : 24 * (numerator z / 24) + numerator z % 24 = numerator z := by omega
  have h₁ : 24 * (numerator (z - 1) / 24) + numerator (z - 1) % 24 = numerator (z - 1) := by omega
  rw [numerator_mod] at h₀ h₁
  by_cases h : z % 2 = 0
  · have e : (z - 1) % 2 ≠ 0 := by omega
    have hz : z = 2 * (z / 2) := by omega
    have hq : (z + 1) / 2 = z / 2 := by omega
    rw [hq]
    simp only [h, e, if_true, if_false, add_zero] at h₀ h₁
    unfold numerator at h₀ h₁ ⊢
    let q := z / 2
    have hsq : z ^ 2 = 4 * q ^ 2 := by nlinarith only [congrArg (fun k : ℤ => k ^ 2) hz]
    nlinarith only [hc, h₀, h₁, hsq]
  · have e : (z - 1) % 2 = 0 := by omega
    have hz : z = 2 * (z / 2) + 1 := by omega
    have hq : (z + 1) / 2 = z / 2 + 1 := by omega
    rw [hq]
    simp only [h, e, if_true, if_false, add_zero] at h₀ h₁
    unfold numerator at h₀ h₁ ⊢
    let q := z / 2
    have hsq : z ^ 2 = 4 * q ^ 2 + 4 * q + 1 := by
      nlinarith only [congrArg (fun k : ℤ => k ^ 2) hz]
    nlinarith only [hc, h₀, h₁, hsq]

end GridTriples

theorem OMA.solution : type_of% @OMA.S_oeis_a057566.main := GridTriples.prove