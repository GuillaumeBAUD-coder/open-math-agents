import FormalConjectures.Wikipedia.Kaplansky

/-!
# Torsion-freeness of the Promislow group

The squares of the three nontrivial coset representatives generate the translation subgroup.
Three actions on the integers detect the translation coordinates and rule out torsion in the
other cosets.
-/

namespace OMA

abbrev rels : Set (FreeGroup (Fin 2)) :=
  let a := FreeGroup.of (0 : Fin 2)
  let b := FreeGroup.of (1 : Fin 2)
  {b⁻¹ * a * a * b * a * a, a⁻¹ * b * b * a * b * b}

abbrev P := PresentedGroup rels

def a : P := PresentedGroup.of (rels := rels) (0 : Fin 2)
def b : P := PresentedGroup.of (rels := rels) (1 : Fin 2)
def x : P := a * a
def y : P := b * b
def z : P := (a * b) * (a * b)

theorem relX : b⁻¹ * x * b = x⁻¹ := by
  have h : b⁻¹ * a * a * b * a * a = 1 := by
    have hmem : (FreeGroup.of (1 : Fin 2))⁻¹ * FreeGroup.of 0 * FreeGroup.of 0 *
        FreeGroup.of 1 * FreeGroup.of 0 * FreeGroup.of 0 ∈ rels := by simp [rels]
    simpa only [map_inv, map_mul, PresentedGroup.of, a, b] using PresentedGroup.one_of_mem hmem
  calc
    b⁻¹ * x * b = (b⁻¹ * a * a * b * a * a) * x⁻¹ := by unfold x; group
    _ = x⁻¹ := by rw [h, one_mul]

theorem relY : a⁻¹ * y * a = y⁻¹ := by
  have h : a⁻¹ * b * b * a * b * b = 1 := by
    have hmem : (FreeGroup.of (0 : Fin 2))⁻¹ * FreeGroup.of 1 * FreeGroup.of 1 *
        FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 1 ∈ rels := by simp [rels]
    simpa only [map_inv, map_mul, PresentedGroup.of, a, b] using PresentedGroup.one_of_mem hmem
  calc
    a⁻¹ * y * a = (a⁻¹ * b * b * a * b * b) * y⁻¹ := by unfold y; group
    _ = y⁻¹ := by rw [h, one_mul]

theorem reverse_conjugation (g h : P) (hh : g⁻¹ * h * g = h⁻¹) : g * h * g⁻¹ = h⁻¹ := by
  calc
    g * h * g⁻¹ = g * (h⁻¹)⁻¹ * g⁻¹ := by rw [inv_inv]
    _ = g * (g⁻¹ * h * g)⁻¹ * g⁻¹ := by rw [hh]
    _ = h⁻¹ := by group

theorem b_x : b * x * b⁻¹ = x⁻¹ := reverse_conjugation b x relX
theorem a_y : a * y * a⁻¹ = y⁻¹ := reverse_conjugation a y relY

theorem move_factor {g h k : P} (hh : g * h * g⁻¹ = k) : g * h = k * g := by
  calc
    g * h = (g * h * g⁻¹) * g := by group
    _ = k * g := by rw [hh]

theorem a_z : a * z * a⁻¹ = z⁻¹ := by
  have hxb : x * b = b * x⁻¹ := by
    calc
      x * b = b * (b⁻¹ * x * b) := by group
      _ = b * x⁻¹ := by rw [relX]
  have hya : y * a⁻¹ = a⁻¹ * y⁻¹ := by
    calc
      y * a⁻¹ = a⁻¹ * (a * y * a⁻¹) := by group
      _ = a⁻¹ * y⁻¹ := by rw [a_y]
  calc
    a * z * a⁻¹ = (x * b) * a * b * a⁻¹ := by unfold x z; group
    _ = b * a⁻¹ * b * a⁻¹ := by rw [hxb]; unfold x; group
    _ = b⁻¹ * (y * a⁻¹) * b * a⁻¹ := by unfold y; group
    _ = z⁻¹ := by rw [hya]; unfold y z; group

theorem b_z : b * z * b⁻¹ = z⁻¹ := by
  have ha : a⁻¹ * z * a = z⁻¹ :=
    reverse_conjugation a⁻¹ z (by simpa only [inv_inv] using a_z)
  calc
    b * z * b⁻¹ = a⁻¹ * ((a * b) * z * (a * b)⁻¹) * a := by group
    _ = a⁻¹ * z * a := by
      have hs : (a * b) * z * (a * b)⁻¹ = z := by unfold z; group
      rw [hs]
    _ = z⁻¹ := ha

theorem square_commutes (g h : P) (hh : g * h * g⁻¹ = h⁻¹) : Commute (g * g) h := by
  have htwo : g * (g * h * g⁻¹) * g⁻¹ = h := by
    calc
      g * (g * h * g⁻¹) * g⁻¹ = g * h⁻¹ * g⁻¹ := congrArg (fun u => g * u * g⁻¹) hh
      _ = (g * h * g⁻¹)⁻¹ := by group
      _ = h := by rw [hh, inv_inv]
  apply move_factor
  calc
    (g * g) * h * (g * g)⁻¹ = g * (g * h * g⁻¹) * g⁻¹ := by group
    _ = h := htwo

theorem xy : Commute x y := square_commutes a y a_y
theorem xz : Commute x z := square_commutes a z a_z
theorem yz : Commute y z := square_commutes b z b_z

def word (i j k : ℤ) : P := x ^ i * y ^ j * z ^ k

theorem word_mul (i j k i' j' k' : ℤ) :
    word i j k * word i' j' k' = word (i + i') (j + j') (k + k') := by
  have hx := (xz.zpow_zpow i' k).symm.eq
  have hy := (xy.zpow_zpow i' j).symm.eq
  have hz := (yz.zpow_zpow j' k).symm.eq
  calc
    word i j k * word i' j' k' = x ^ i * y ^ j * (z ^ k * x ^ i') * y ^ j' * z ^ k' := by
      simp only [word, mul_assoc]
    _ = x ^ i * (y ^ j * x ^ i') * (z ^ k * y ^ j') * z ^ k' := by
      simp only [hx, mul_assoc]
    _ = (x ^ i * x ^ i') * (y ^ j * y ^ j') * (z ^ k * z ^ k') := by
      simp only [hy, hz, mul_assoc]
    _ = _ := by simp only [word, zpow_add]

theorem conj_word (g : P) (i j k : ℤ) :
    g * word i j k * g⁻¹ = (g * x * g⁻¹) ^ i * (g * y * g⁻¹) ^ j * (g * z * g⁻¹) ^ k := by
  change MulAut.conj g (word i j k) = _
  simp only [word, map_mul, map_zpow, MulAut.conj_apply]

theorem a_word (i j k : ℤ) : a * word i j k = word i (-j) (-k) * a := by
  apply move_factor
  have hx : a * x * a⁻¹ = x := by unfold x; group
  rw [conj_word, hx, a_y, a_z]
  simp [word, zpow_neg]

theorem b_word (i j k : ℤ) : b * word i j k = word (-i) j (-k) * b := by
  apply move_factor
  have hy : b * y * b⁻¹ = y := by unfold y; group
  rw [conj_word, b_x, hy, b_z]
  simp [word, zpow_neg]

def rep : Fin 4 → P := ![1, a, b, a * b]

def NormalForm (g : P) : Prop := ∃ (i j k : ℤ) (r : Fin 4), g = word i j k * rep r

theorem word_normal {g : P} (hg : NormalForm g) (u v w : ℤ) :
    NormalForm (word u v w * g) := by
  obtain ⟨i, j, k, r, rfl⟩ := hg
  exact ⟨u + i, v + j, w + k, r, by rw [← mul_assoc, word_mul]⟩

theorem bab : b * (a * b) = word (-1) 0 (-1) * a := by
  have ha : a⁻¹ * z * a = z⁻¹ :=
    reverse_conjugation a⁻¹ z (by simpa only [inv_inv] using a_z)
  have ha' : a⁻¹ * z = z⁻¹ * a⁻¹ := move_factor (by simpa only [inv_inv] using ha)
  calc
    b * (a * b) = a⁻¹ * z := by unfold z; group
    _ = z⁻¹ * a⁻¹ := ha'
    _ = z⁻¹ * (x⁻¹ * a) := by unfold x; group
    _ = word (-1) 0 (-1) * a := by
      rw [← mul_assoc, (xz.inv_inv).symm.eq]
      simp [word]

theorem ba : b * a = word (-1) 1 (-1) * (a * b) := by
  have ha : a * y⁻¹ = y * a :=
    move_factor (by rw [show a * y⁻¹ * a⁻¹ = (a * y * a⁻¹)⁻¹ by group, a_y, inv_inv])
  calc
    b * a = (b * (a * b)) * b⁻¹ := by group
    _ = word (-1) 0 (-1) * (a * y⁻¹) * b := by rw [bab]; unfold y; group
    _ = (word (-1) 0 (-1) * word 0 1 0) * (a * b) := by rw [ha]; simp [word, mul_assoc]
    _ = word (-1) 1 (-1) * (a * b) := by rw [word_mul]; norm_num

theorem a_rep (r : Fin 4) : NormalForm (a * rep r) := by
  fin_cases r
  · exact ⟨0, 0, 0, 1, by simp [rep, word]⟩
  · exact ⟨1, 0, 0, 0, by simp [rep, word, x]⟩
  · exact ⟨0, 0, 0, 3, by simp [rep, word]⟩
  · exact ⟨1, 0, 0, 2, by simp [rep, word, x, mul_assoc]⟩

theorem b_rep (r : Fin 4) : NormalForm (b * rep r) := by
  fin_cases r
  · exact ⟨0, 0, 0, 2, by simp [rep, word]⟩
  · exact ⟨-1, 1, -1, 3, by simpa [rep] using ba⟩
  · exact ⟨0, 1, 0, 0, by simp [rep, word, y]⟩
  · exact ⟨-1, 0, -1, 1, by simpa [rep] using bab⟩

theorem left_a {g : P} (hg : NormalForm g) : NormalForm (a * g) := by
  obtain ⟨i, j, k, r, rfl⟩ := hg
  rw [← mul_assoc, a_word, mul_assoc]
  exact word_normal (a_rep r) i (-j) (-k)

theorem left_b {g : P} (hg : NormalForm g) : NormalForm (b * g) := by
  obtain ⟨i, j, k, r, rfl⟩ := hg
  rw [← mul_assoc, b_word, mul_assoc]
  exact word_normal (b_rep r) (-i) j (-k)

theorem left_a_inv {g : P} (hg : NormalForm g) : NormalForm (a⁻¹ * g) := by
  have he : word (-1) 0 0 * (a * g) = a⁻¹ * g := by
    simp only [word, zpow_neg_one, zpow_zero, mul_one, x]
    group
  exact he ▸ word_normal (left_a hg) (-1) 0 0

theorem left_b_inv {g : P} (hg : NormalForm g) : NormalForm (b⁻¹ * g) := by
  have he : word 0 (-1) 0 * (b * g) = b⁻¹ * g := by
    simp only [word, zpow_neg_one, zpow_zero, mul_one, one_mul, y]
    group
  exact he ▸ word_normal (left_b hg) 0 (-1) 0

def preservesForm : Subgroup P where
  carrier := {u | ∀ g, NormalForm g ↔ NormalForm (u * g)}
  one_mem' := by intro g; rw [one_mul]
  mul_mem' := by
    intro u v hu hv g
    rw [mul_assoc]
    exact (hv g).trans (hu (v * g))
  inv_mem' := by
    intro u hu g
    simpa only [mul_inv_cancel_left] using (hu (u⁻¹ * g)).symm

theorem all_normal (g : P) : NormalForm g := by
  have hg : g ∈ preservesForm := PresentedGroup.generated_by rels preservesForm (by
    intro i
    fin_cases i
    · change ∀ h, NormalForm h ↔ NormalForm (a * h)
      intro h
      exact ⟨left_a, fun hh => by simpa only [inv_mul_cancel_left] using left_a_inv hh⟩
    · change ∀ h, NormalForm h ↔ NormalForm (b * h)
      intro h
      exact ⟨left_b, fun hh => by simpa only [inv_mul_cancel_left] using left_b_inv hh⟩) g
  have h₁ : NormalForm 1 := ⟨0, 0, 0, 0, by simp [word, rep]⟩
  exact mul_one g ▸ (hg 1).mp h₁

def shift (d : ℤ) : Equiv.Perm ℤ where
  toFun t := t + d
  invFun t := t - d
  left_inv := by intro t; change t + d - d = t; omega
  right_inv := by intro t; change t - d + d = t; omega

def flip (d : ℤ) : Equiv.Perm ℤ where
  toFun t := d - t
  invFun t := d - t
  left_inv := by intro t; change d - (d - t) = t; omega
  right_inv := by intro t; change d - (d - t) = t; omega

theorem shift_apply (d t : ℤ) : shift d t = t + d := rfl
theorem shift_inv_apply (d t : ℤ) : (shift d)⁻¹ t = t - d := rfl
theorem flip_apply (d t : ℤ) : flip d t = d - t := rfl
theorem flip_inv_apply (d t : ℤ) : (flip d)⁻¹ t = d - t := rfl

@[simp] theorem shift_zero : shift 0 = 1 := by
  ext t
  simp [shift_apply]

theorem shift_mul (i j : ℤ) : shift i * shift j = shift (i + j) := by
  ext t
  simp only [Equiv.Perm.mul_apply, shift_apply]
  omega

theorem shift_mul_flip (i j : ℤ) : shift i * flip j = flip (i + j) := by
  ext t
  simp only [Equiv.Perm.mul_apply, shift_apply, flip_apply]
  omega

theorem flip_mul_shift (i j : ℤ) : flip i * shift j = flip (i - j) := by
  ext t
  simp only [Equiv.Perm.mul_apply, shift_apply, flip_apply]
  omega

theorem flip_mul_flip (i j : ℤ) : flip i * flip j = shift (i - j) := by
  ext t
  simp only [Equiv.Perm.mul_apply, shift_apply, flip_apply]
  omega

def shiftHom : Multiplicative ℤ →* Equiv.Perm ℤ where
  toFun t := shift t.toAdd
  map_one' := shift_zero
  map_mul' t u := (shift_mul t.toAdd u.toAdd).symm

theorem shift_zpow (d k : ℤ) : shift d ^ k = shift (k * d) := by
  calc
    shift d ^ k = shiftHom ((Multiplicative.ofAdd d) ^ k) := (shiftHom.map_zpow _ _).symm
    _ = shift (k * d) := by
      change shift (((Multiplicative.ofAdd d) ^ k).toAdd) = _
      simp

theorem shift_eq_zero_of_pow {d : ℤ} {n : ℕ} (hn : 0 < n) (h : shift d ^ n = 1) : d = 0 := by
  have he : shift d ^ n = shift ((n : ℤ) * d) := by simpa using shift_zpow d n
  rw [he] at h
  have hzero : (n : ℤ) * d = 0 := by
    simpa [shift_apply] using congrArg (fun f : Equiv.Perm ℤ => f 0) h
  exact (mul_eq_zero.mp hzero).resolve_left (by exact_mod_cast hn.ne')

def makeAxis (A B : Equiv.Perm ℤ) (hx : B⁻¹ * A * A * B * A * A = 1)
    (hy : A⁻¹ * B * B * A * B * B = 1) : P →* Equiv.Perm ℤ :=
  PresentedGroup.toGroup (rels := rels) (f := ![A, B]) (by
    intro r hr
    simp only [rels, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl
    · simpa using hx
    · simpa using hy)

@[simp] theorem makeAxis_a (A B : Equiv.Perm ℤ) hx hy : makeAxis A B hx hy a = A := by
  simp [makeAxis, a, PresentedGroup.toGroup.of]

@[simp] theorem makeAxis_b (A B : Equiv.Perm ℤ) hx hy : makeAxis A B hx hy b = B := by
  simp [makeAxis, b, PresentedGroup.toGroup.of]

def axisX : P →* Equiv.Perm ℤ := makeAxis (shift 1) (flip 0)
  (by
    ext t
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply, shift_apply, flip_apply, flip_inv_apply]
    omega)
  (by
    ext t
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply, shift_apply, shift_inv_apply, flip_apply]
    omega)

def axisY : P →* Equiv.Perm ℤ := makeAxis (flip 0) (shift 1)
  (by
    ext t
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply, shift_apply, shift_inv_apply, flip_apply]
    omega)
  (by
    ext t
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply, shift_apply, flip_apply, flip_inv_apply]
    omega)

def axisZ : P →* Equiv.Perm ℤ := makeAxis (flip 0) (flip 1)
  (by
    ext t
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply, flip_apply, flip_inv_apply]
    omega)
  (by
    ext t
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply, flip_apply, flip_inv_apply]
    omega)

@[simp] theorem axisX_a : axisX a = shift 1 := by simp [axisX]
@[simp] theorem axisY_b : axisY b = shift 1 := by simp [axisY]
@[simp] theorem axisZ_a : axisZ a = flip 0 := by simp [axisZ]
@[simp] theorem axisZ_b : axisZ b = flip 1 := by simp [axisZ]

@[simp] theorem axisX_word (i j k : ℤ) : axisX (word i j k) = shift (i * 2) := by
  simp [word, x, y, z, axisX, shift_mul, shift_mul_flip, flip_mul_flip, shift_zpow]

@[simp] theorem axisY_word (i j k : ℤ) : axisY (word i j k) = shift (j * 2) := by
  simp [word, x, y, z, axisY, shift_mul, flip_mul_shift, flip_mul_flip, shift_zpow]

@[simp] theorem axisZ_word (i j k : ℤ) : axisZ (word i j k) = shift (k * (-2)) := by
  simp [word, x, y, z, axisZ, shift_mul, flip_mul_flip, shift_zpow]

end OMA

open OMA

theorem OMA.solution : type_of% @Kaplansky.promislow_group_is_torsionfree := by
  change Monoid.IsTorsionFree P
  apply Monoid.isTorsionFree_iff_forall_isOfFinOrder_imp_eq_one.mpr
  intro g hg
  obtain ⟨i, j, k, r, rfl⟩ := all_normal g
  obtain ⟨n, hn, hp⟩ := hg.exists_pow_eq_one
  have hzero (f : P →* Equiv.Perm ℤ) (d : ℤ) (he : f (word i j k * rep r) = shift d) : d = 0 := by
    apply shift_eq_zero_of_pow hn
    rw [← he, ← map_pow, hp, map_one]
  fin_cases r
  · have hi := hzero axisX (i * 2) (by simp [rep])
    have hj := hzero axisY (j * 2) (by simp [rep])
    have hk := hzero axisZ (k * (-2)) (by simp [rep])
    have hi' : i = 0 := by omega
    have hj' : j = 0 := by omega
    have hk' : k = 0 := by omega
    simp [word, rep, hi', hj', hk']
  · have h := hzero axisX (i * 2 + 1) (by simp [rep, shift_mul])
    omega
  · have h := hzero axisY (j * 2 + 1) (by simp [rep, shift_mul])
    omega
  · have h := hzero axisZ (k * (-2) + (-1)) (by simp [rep, flip_mul_flip, shift_mul])
    omega
