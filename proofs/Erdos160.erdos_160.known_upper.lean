import FormalConjectures.ErdosProblems.«160»
import Mathlib.NumberTheory.Bertrand

/-! The twisted cubic coloring is due to leechlattice (https://mathoverflow.net/a/410815).
We use base 8p and record a block number for each digit. In two monochromatic
secants the block translations cancel. Small digits then let us recover each
coordinate of the secant identity without any carries. -/

namespace OMA.Erdos160Twisted

def digit (p u k : ℕ) := u / (8*p)^k % (8*p)

def block (p u k : ℕ) (hp : 0 < p) : Fin 8 :=
  ⟨digit p u k / p, (Nat.div_lt_iff_lt_mul hp).mpr (Nat.mod_lt _ (by positivity))⟩

def coord (p u k : ℕ) : ZMod p := digit p u k

abbrev Palette (p : ℕ) := Fin 8 × Fin 8 × Fin 8 × ZMod p × ZMod p

def color (p : ℕ) (hp : 0 < p) (u : ℕ) : Palette p :=
  (block p u 0 hp, block p u 1 hp, block p u 2 hp,
   coord p u 1 - coord p u 0 ^ 2, coord p u 2 - coord p u 0 ^ 3)

def pack (b x y z : ℤ) := x + b*(y+b*z)

lemma digits_pack (p u : ℕ) (hp : 0 < p) (hu : u < (8*p)^3) :
    (u : ℤ) = pack (8*p) (digit p u 0) (digit p u 1) (digit p u 2) := by
  let b := 8*p
  have hb : 0 < b := by dsimp [b]; positivity
  have h₂ : u / b / b < b := by
    rw [Nat.div_lt_iff_lt_mul hb, Nat.div_lt_iff_lt_mul hb]
    simpa [b, pow_succ] using hu
  have e₀ := Nat.mod_add_div u b
  have e₁ := Nat.mod_add_div (u/b) b
  have h : u = (u%b) + b * ((u/b)%b + b*(u/b/b)) := by
    conv_lhs => rw [← e₀]
    rw [e₁]
  change (u : ℤ) = pack (b : ℕ) (u / b^0 % b : ℕ) (u / b^1 % b : ℕ) (u / b^2 % b : ℕ)
  unfold pack
  rw [pow_two, ← Nat.div_div_eq_div_mul, Nat.mod_eq_of_lt h₂]
  simp only [pow_zero, Nat.div_one, pow_one]
  exact_mod_cast h

lemma coord_zero (p u : ℕ) (hp : 0 < p) (hu : u < (8*p)^3) :
    coord p u 0 = (u : ZMod p) := by
  have h := congrArg (fun x : ℤ => (x : ZMod p)) (digits_pack p u hp hu)
  simpa [pack, coord] using h.symm

lemma digit_diff {p u v : ℕ} [NeZero p] (hp : 0 < p) (k : ℕ)
    (h : block p u k hp = block p v k hp) :
    (digit p u k : ℤ) - digit p v k = ((coord p u k).val : ℤ) - (coord p v k).val := by
  have hb := congrArg Fin.val h
  change digit p u k / p = digit p v k / p at hb
  have ha := Nat.mod_add_div (digit p u k) p
  have hc := Nat.mod_add_div (digit p v k) p
  rw [hb] at ha
  simp [coord, ZMod.val_natCast]
  omega

lemma color_diff {p u v : ℕ} [NeZero p] (hp : 0 < p)
    (hu : u < (8*p)^3) (hv : v < (8*p)^3) (h : color p hp u = color p hp v) :
    (u : ℤ) - v = pack (8*p)
      (((coord p u 0).val : ℤ) - (coord p v 0).val)
      (((coord p u 1).val : ℤ) - (coord p v 1).val)
      (((coord p u 2).val : ℤ) - (coord p v 2).val) := by
  obtain ⟨h₀,h₁,h₂,_,_⟩ := (show _ ∧ _ ∧ _ ∧ _ ∧ _ from by simpa [color, Prod.mk.injEq] using h)
  rw [← digit_diff hp 0 h₀, ← digit_diff hp 1 h₁, ← digit_diff hp 2 h₂,
    digits_pack p u hp hu, digits_pack p v hp hv]
  unfold pack
  ring

lemma color_coords {p u v : ℕ} (hp : 0 < p) (h : color p hp u = color p hp v) :
    coord p v 1 - coord p u 1 = coord p v 0 ^ 2 - coord p u 0 ^ 2 ∧
    coord p v 2 - coord p u 2 = coord p v 0 ^ 3 - coord p u 0 ^ 3 := by
  have h₁ := congrArg (fun a : Palette p => a.2.2.2.1) h
  have h₂ := congrArg (fun a : Palette p => a.2.2.2.2) h
  change _ - _ = _ - _ at h₁ h₂
  exact ⟨by linear_combination -h₁, by linear_combination -h₂⟩

lemma low_zero {b x y : ℤ} (hx : -b < x ∧ x < b) (h : x + b*y = 0) : x = 0 := by
  exact Int.eq_zero_of_abs_lt_dvd ⟨-y, by linarith⟩ (abs_lt.mpr hx)

lemma unpack_zero {b x y z : ℤ} (hb : 0 < b)
    (hx : -b < x ∧ x < b) (hy : -b < y ∧ y < b) (h : pack b x y z = 0) :
    x = 0 ∧ y = 0 ∧ z = 0 := by
  have ex := low_zero hx h
  have h' : y + b*z = 0 := by
    simpa [pack, ex, hb.ne', mul_eq_zero] using h
  have ey := low_zero hy h'
  exact ⟨ex, ey, by simpa [ey, hb.ne', mul_eq_zero] using h'⟩

/-- A proportionality between two monochromatic integer differences holds digit by digit. -/
lemma secants {p : ℕ} [NeZero p] (hp : 0 < p) {u v w x s t : ℕ}
    (hu : u < (8*p)^3) (hv : v < (8*p)^3) (hw : w < (8*p)^3) (hx : x < (8*p)^3)
    (hs : s ≤ 3) (ht : t ≤ 3)
    (e₁ : color p hp v = color p hp u) (e₂ : color p hp x = color p hp w)
    (rel : (t : ℤ)*(v-u) = (s : ℤ)*(x-w)) :
    ∀ k ∈ ({1, 2} : Finset ℕ),
      (t : ZMod p)*(coord p v k - coord p u k) =
      (s : ZMod p)*(coord p x k - coord p w k) := by
  let V (n k : ℕ) : ℤ := (coord p n k).val
  let D (k : ℕ) := (t : ℤ)*(V v k - V u k) - (s : ℤ)*(V x k - V w k)
  have small (n k : ℕ) : 0 ≤ V n k ∧ V n k < p := by
    dsimp only [V]
    exact ⟨Int.natCast_nonneg _, by exact_mod_cast (coord p n k).val_lt⟩
  have bound (k : ℕ) : -(8*(p : ℤ)) < D k ∧ D k < 8*p := by
    have := small u k
    have := small v k
    have := small w k
    have := small x k
    dsimp only [D]
    interval_cases s <;> interval_cases t <;> omega
  rw [color_diff hp hv hu e₁, color_diff hp hx hw e₂] at rel
  have eqn : pack (8*p) (D 0) (D 1) (D 2) = 0 := by
    dsimp [D,V,pack]
    unfold pack at rel
    linear_combination rel
  obtain ⟨_,h₁,h₂⟩ := unpack_zero (by positivity) (bound 0) (bound 1) eqn
  intro k hk
  have h : D k = 0 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl <;> assumption
  have H := congrArg (fun z : ℤ => (z : ZMod p)) h
  simpa [D,V,sub_eq_zero] using H

lemma no_vertical {p : ℕ} [NeZero p] (hp : 0 < p) {u v : ℕ}
    (hu : u < (8*p)^3) (hv : v < (8*p)^3) (e : color p hp v = color p hp u)
    (hx : (v : ZMod p) = u) : v = u := by
  have h₀ : coord p v 0 = coord p u 0 := by rw [coord_zero p v hp hv, coord_zero p u hp hu, hx]
  obtain ⟨h₁,h₂⟩ := color_coords hp e
  rw [h₀, sub_self, sub_eq_zero] at h₁ h₂
  have hh := color_diff hp hv hu e
  rw [h₀,h₁,h₂] at hh
  simp [pack] at hh
  omega

lemma power_secants {p a d : ℕ} [NeZero p] (hp : 0 < p)
    (hm : a+3*d < (8*p)^3) {i s k t : ℕ}
    (hi : i+s ≤ 3) (hk : k+t ≤ 3)
    (e₁ : color p hp (a+(i+s)*d) = color p hp (a+i*d))
    (e₂ : color p hp (a+(k+t)*d) = color p hp (a+k*d)) :
    let f (j : ℕ) := (a : ZMod p) + j*d
    (t : ZMod p)*(f (i+s)^2 - f i^2) = (s : ZMod p)*(f (k+t)^2 - f k^2) ∧
    (t : ZMod p)*(f (i+s)^3 - f i^3) = (s : ZMod p)*(f (k+t)^3 - f k^3) := by
  have b (j : ℕ) (hj : j ≤ 3) : a+j*d < (8*p)^3 :=
    lt_of_le_of_lt (Nat.add_le_add_left (Nat.mul_le_mul_right d hj) _) hm
  have h₁ := color_coords hp e₁.symm
  have h₂ := color_coords hp e₂.symm
  have r := secants (s := s) (t := t) hp (b i (by omega)) (b _ hi) (b k (by omega)) (b _ hk)
    (by omega) (by omega) e₁ e₂ (by push_cast; ring)
  have X := r 1 (by decide)
  have Y := r 2 (by decide)
  rw [h₁.1,h₂.1] at X
  rw [h₁.2,h₂.2] at Y
  simp only [coord_zero p _ hp (b _ hi), coord_zero p _ hp (b _ hk),
    coord_zero p _ hp (b i (by omega)), coord_zero p _ hp (b k (by omega)),
    Nat.cast_add, Nat.cast_mul] at X Y ⊢
  exact ⟨X,Y⟩

/-- Parallel nonzero chords of the twisted cubic have the same unordered endpoints. -/
lemma same_chord {K : Type*} [Field K] {x y z w s t : K}
    (hne : t*(y-x) ≠ 0) (one : t*(y-x) = s*(w-z))
    (two : t*(y^2-x^2) = s*(w^2-z^2))
    (three : t*(y^3-x^3) = s*(w^3-z^3)) :
    (x = z ∧ y = w) ∨ (x = w ∧ y = z) := by
  have sum : x+y = z+w := by
    apply mul_left_cancel₀ hne
    linear_combination two - (w+z)*one
  have quad : x^2+x*y+y^2 = z^2+z*w+w^2 := by
    apply mul_left_cancel₀ hne
    linear_combination three - (w^2+w*z+z^2)*one
  have prod : x*y = z*w := by linear_combination (x+y+z+w)*sum - quad
  have root : (x-z)*(x-w) = 0 := by linear_combination x*sum - prod
  rcases mul_eq_zero.mp root with h | h
  · left; exact ⟨sub_eq_zero.mp h, by linear_combination sum - h⟩
  · right; exact ⟨sub_eq_zero.mp h, by linear_combination sum - h⟩

lemma unique_pair {p a d : ℕ} [Fact p.Prime] (hp : 3 < p) (hd : 0 < d)
    (hm : a+3*d < (8*p)^3) {i j k l : ℕ}
    (hij : i < j) (hjl : j ≤ 3) (hkl : k < l) (hl : l ≤ 3)
    (e₁ : color p (by omega) (a+j*d) = color p (by omega) (a+i*d))
    (e₂ : color p (by omega) (a+l*d) = color p (by omega) (a+k*d)) :
    i = k ∧ j = l := by
  let f (m : ℕ) : ZMod p := a + (m : ZMod p)*d
  have hD : (d : ZMod p) ≠ 0 := by
    intro h
    have b (m : ℕ) (hm' : m ≤ 3) : a+m*d < (8*p)^3 :=
      lt_of_le_of_lt (Nat.add_le_add_left (Nat.mul_le_mul_right d hm') _) hm
    have H := no_vertical (p := p) (by omega) (b _ hjl) (b i (by omega)) e₁.symm
      (by push_cast; simp [h])
    exact (Nat.ne_of_lt (Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_right hij hd) a)) H
  have inj {v w : ℕ} (hv : v ≤ 3) (hw : w ≤ 3) (e : f v = f w) : v = w := by
    have h : (v : ZMod p) = w := mul_right_cancel₀ hD (add_left_cancel e : (v : ZMod p)*d = w*d)
    exact ((ZMod.natCast_eq_natCast_iff ..).mp h).eq_of_lt_of_lt (by omega) (by omega)
  have hj : i+(j-i) = j := by omega
  have hl' : k+(l-k) = l := by omega
  have hpow := power_secants (p := p) (a := a) (d := d) (i := i) (k := k)
    (s := j-i) (t := l-k) (by omega) hm (by omega) (by omega)
    (hj ▸ e₁) (hl' ▸ e₂)
  change (l-k : ℕ) * (f (i+(j-i)) ^ 2 - f i ^ 2) = (j-i : ℕ) * (f (k+(l-k)) ^ 2 - f k ^ 2) ∧
    (l-k : ℕ) * (f (i+(j-i)) ^ 3 - f i ^ 3) = (j-i : ℕ) * (f (k+(l-k)) ^ 3 - f k ^ 3) at hpow
  rw [hj, hl'] at hpow
  have hne : ((l-k : ℕ) : ZMod p) ≠ 0 := by
    intro he
    exact (Nat.not_dvd_of_pos_of_lt (by omega : 0 < l-k) (by omega : l-k < p))
      ((ZMod.natCast_eq_zero_iff (l-k) p).mp he)
  have hji : f j ≠ f i := fun h => hij.ne' (inj hjl (by omega) h)
  have eqn : ((l-k : ℕ) : ZMod p)*(f j-f i) = ((j-i : ℕ) : ZMod p)*(f l-f k) := by
    simp only [f, Nat.cast_sub (Nat.le_of_lt hkl), Nat.cast_sub (Nat.le_of_lt hij)]
    ring
  rcases same_chord (mul_ne_zero hne (sub_ne_zero.mpr hji)) eqn hpow.1 hpow.2 with H | H
  · exact ⟨inj (by omega) (by omega) H.1, inj hjl hl H.2⟩
  · have := inj (by omega) hl H.1
    have := inj hjl (by omega) H.2
    omega

lemma three_colors {α : Type*} (C : ℕ → α)
    (uniq : ∀ i j k l : ℕ, i < j → j ≤ 3 → k < l → l ≤ 3 →
      C i = C j → C k = C l → i = k ∧ j = l) :
    ∃ i j k : Fin 4, C i ≠ C j ∧ C i ≠ C k ∧ C j ≠ C k := by
  have other (i j k l : ℕ) (h : C i = C j) (hij : i < j) (hj : j ≤ 3)
      (hkl : k < l) (hl : l ≤ 3) (hne : ¬(i = k ∧ j = l)) : C k ≠ C l :=
    fun H => hne (uniq i j k l hij hj hkl hl h H)
  by_cases h₁ : C 0 = C 1
  · refine ⟨0,2,3,?_,?_,?_⟩ <;> apply other 0 1 _ _ h₁ <;> decide
  by_cases h₂ : C 0 = C 2
  · refine ⟨0,1,3,?_,?_,?_⟩ <;> apply other 0 2 _ _ h₂ <;> decide
  by_cases h₃ : C 1 = C 2
  · refine ⟨0,1,3,?_,?_,?_⟩ <;> apply other 1 2 _ _ h₃ <;> decide
  exact ⟨0,1,2,h₁,h₂,h₃⟩

/-- Each digit has eight possible blocks. The two field invariants give the other colors. -/
lemma finite_bound {p n : ℕ} [Fact p.Prime] (hp : 3 < p) (hn : n < (8*p)^3) :
    Erdos160.erdos_160.h n ≤ 512*p^2 := by
  classical
  let e := Fintype.equivFin (Palette p)
  let c (u : ℕ) := e (color p (by omega) u)
  have hcard : Fintype.card (Palette p) = 512*p^2 := by simp [Palette]; ring
  rw [← hcard]
  apply Nat.sInf_le
  refine ⟨fun u => c u.val, ?_⟩
  rintro A ⟨hsub, a, d, hcardA, hA⟩
  have mem (j : ℕ) (hj : j ≤ 3) : a+j*d ∈ A := by
    rw [hA]
    exact ⟨j, by exact_mod_cast (show j < 4 by omega), by simp⟩
  have hd : 0 < d := by
    by_contra! hd
    have hz : d = 0 := by omega
    have sing : A = {a} := by
      apply Set.eq_singleton_iff_unique_mem.mpr
      refine ⟨by simpa using mem 0 (by decide), ?_⟩
      intro b hb
      rw [hA] at hb
      obtain ⟨i,hi,rfl⟩ := hb
      simp [hz]
    rw [sing] at hcardA
    norm_num at hcardA
  have hm : a+3*d < (8*p)^3 :=
    lt_of_le_of_lt (Finset.mem_Icc.mp (hsub (mem 3 (by decide)))).2 hn
  obtain ⟨i,j,k,hij,hik,hjk⟩ := three_colors (fun m => c (a+m*d)) (by
    intro i j k l hij hj hkl hl e₁ e₂
    exact unique_pair hp hd hm hij hj hkl hl (e.injective e₁.symm) (e.injective e₂.symm))
  let T := (fun u : Finset.Icc 1 n => c u.val) '' {u | u.val ∈ A}
  have hin (m : Fin 4) : c (a+m.val*d) ∈ T :=
    ⟨⟨_, hsub (mem m.val (by omega))⟩, mem m.val (by omega), rfl⟩
  have sub : {c (a+i.val*d), c (a+j.val*d), c (a+k.val*d)} ⊆ T := by
    exact Set.insert_subset (hin i) (Set.insert_subset (hin j) (Set.singleton_subset_iff.mpr (hin k)))
  have size : ({c (a+i.val*d), c (a+j.val*d), c (a+k.val*d)} : Set _).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨_,_,_,hij,hik,hjk,rfl⟩
  exact size ▸ Set.ncard_le_ncard sub

end OMA.Erdos160Twisted

open Filter OMA.Erdos160Twisted in
theorem OMA.solution : type_of% @Erdos160.erdos_160.known_upper := by
  refine Asymptotics.IsBigO.of_bound 8192 ?_
  filter_upwards [eventually_ge_atTop 64] with n hn
  let x := (n : ℝ) ^ ((1 : ℝ)/3)
  have hx : 1 ≤ x := Real.one_le_rpow (by exact_mod_cast (show 1 ≤ n by omega)) (by norm_num)
  have hx3 : x^3 = (n : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hx2 : x^2 = (n : ℝ) ^ ((2 : ℝ)/3) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hceil := Nat.le_ceil x
  have h4 : 3 < ⌈x⌉₊ := by
    by_contra! bad
    have le3 : x ≤ 3 := le_trans hceil (by exact_mod_cast bad)
    have := pow_le_pow_left₀ (by linarith : 0 ≤ x) le3 3
    rw [hx3] at this
    have : (64 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  obtain ⟨p,hp,hl,hu⟩ := Nat.exists_prime_lt_and_le_two_mul ⌈x⌉₊ (by omega)
  let : Fact p.Prime := ⟨hp⟩
  have hxp : x < p := hceil.trans_lt (by exact_mod_cast hl)
  have hnp : n < (8*p)^3 := by
    have hlt : x < 8*(p : ℝ) := by linarith
    have H := pow_lt_pow_left₀ hlt (by linarith : 0 ≤ x) (by decide : 3 ≠ 0)
    rw [hx3] at H
    exact_mod_cast H
  have hpbound : (p : ℝ) ≤ 4*x := by
    have ha := Nat.ceil_lt_add_one (by linarith : 0 ≤ x)
    have hb : (p : ℝ) ≤ 2*⌈x⌉₊ := by exact_mod_cast hu
    linarith
  have h := finite_bound (p := p) (n := n) (by omega) hnp
  have hr : (Erdos160.erdos_160.h n : ℝ) ≤ 512*(p : ℝ)^2 := by exact_mod_cast h
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), ← hx2]
  nlinarith [mul_nonneg (by linarith : 0 ≤ 4*x - p)
    (by positivity : (0 : ℝ) ≤ 4*x + p)]
