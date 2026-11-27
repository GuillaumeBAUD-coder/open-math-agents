import FormalConjectures.GreensOpenProblems.«95»

/-!
Lower bound for sums of two base-g palindromes (Cilleruelo-Luca-Baxter, Theorem 1.3).
Constructs block-structured palindromes p of length 2*k*B and q of length (2*k-1)*B
with zero inter-block carries, yielding an injective family of sums p + q <= 2*g^(2*k*B).
-/

namespace Green95LowerBound

open Green95

def padDigits (g : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | B + 1, x => (x % g) :: padDigits g B (x / g)

lemma padDigits_length (g B x : ℕ) : (padDigits g B x).length = B := by
  induction B generalizing x with
  | zero => simp [padDigits, Nat.mod_one]
  | succ B ih => simp [padDigits, ih]

lemma padDigits_lt (g B x : ℕ) (hg : 0 < g) : ∀ d ∈ padDigits g B x, d < g := by
  induction B generalizing x with
  | zero => simp [padDigits, Nat.mod_one]
  | succ B ih =>
    intro d hd
    simp only [padDigits, List.mem_cons] at hd
    rcases hd with rfl | hd
    · exact Nat.mod_lt _ hg
    · exact ih (x / g) d hd

lemma ofDigits_padDigits (g B x : ℕ) (hg : 0 < g) :
    Nat.ofDigits g (padDigits g B x) = x % g ^ B := by
  induction B generalizing x with
  | zero => simp [padDigits, Nat.mod_one]
  | succ B ih =>
    simp only [padDigits, Nat.ofDigits, Nat.cast_id, ih (x / g)]
    have hlt : x % g + g * (x / g % g ^ B) < g ^ (B + 1) := by
      have h1 : x % g < g := Nat.mod_lt _ hg
      have h2 : x / g % g ^ B < g ^ B := Nat.mod_lt _ (pow_pos hg B)
      calc x % g + g * (x / g % g ^ B)
          < g + g * (x / g % g ^ B) := by omega
        _ ≤ g + g * (g ^ B - 1) := by
          have : x / g % g ^ B ≤ g ^ B - 1 := by omega
          nlinarith
        _ = g ^ (B + 1) := by
          have hpos : 1 ≤ g ^ B := pow_pos hg B
          zify [hpos]
          ring
    have hdiv : x = g ^ (B + 1) * (x / g / g ^ B) + (x % g + g * (x / g % g ^ B)) := by
      have h1 : x = x % g + g * (x / g) := (Nat.mod_add_div x g).symm
      have h2 : x / g = x / g % g ^ B + g ^ B * (x / g / g ^ B) :=
        (Nat.mod_add_div (x / g) (g ^ B)).symm
      calc x = x % g + g * (x / g % g ^ B + g ^ B * (x / g / g ^ B)) := by rw [← h2, ← h1]
        _ = g ^ (B + 1) * (x / g / g ^ B) + (x % g + g * (x / g % g ^ B)) := by ring
    conv_rhs => rw [hdiv]
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]

lemma padDigits_ofDigits_eq (g : ℕ) (hg : 1 < g) :
    ∀ (l : List ℕ), (∀ d ∈ l, d < g) → padDigits g l.length (Nat.ofDigits g l) = l := by
  intro l hl
  induction l with
  | nil => simp [padDigits, Nat.ofDigits]
  | cons d rest ih =>
    have hd : d < g := hl d (by simp)
    have hrest : ∀ e ∈ rest, e < g := fun e he => hl e (by simp [he])
    have hg0 : 0 < g := by omega
    simp only [List.length_cons, padDigits, Nat.ofDigits, Nat.cast_id]
    have hmod : (d + g * Nat.ofDigits g rest) % g = d := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd]
    have hdiv : (d + g * Nat.ofDigits g rest) / g = Nat.ofDigits g rest := by
      rw [Nat.add_mul_div_left _ _ hg0, Nat.div_eq_of_lt hd, zero_add]
    rw [hmod, hdiv, ih hrest]

def revB (g B x : ℕ) : ℕ :=
  Nat.ofDigits g (padDigits g B x).reverse

lemma revB_lt (g B x : ℕ) (hg : 1 < g) : revB g B x < g ^ B := by
  unfold revB
  have hlen : (padDigits g B x).reverse.length = B := by
    rw [List.length_reverse, padDigits_length]
  calc Nat.ofDigits g (padDigits g B x).reverse
      < g ^ (padDigits g B x).reverse.length := by
        apply Nat.ofDigits_lt_base_pow_length hg
        intro d hd
        rw [List.mem_reverse] at hd
        exact padDigits_lt g B x (by omega) d hd
    _ = g ^ B := by rw [hlen]

lemma padDigits_revB (g B x : ℕ) (hg : 1 < g) :
    padDigits g B (revB g B x) = (padDigits g B x).reverse := by
  have hlen : (padDigits g B x).reverse.length = B := by
    rw [List.length_reverse, padDigits_length]
  have h := padDigits_ofDigits_eq g hg (padDigits g B x).reverse fun d hd => by
    rw [List.mem_reverse] at hd
    exact padDigits_lt g B x (by omega) d hd
  rwa [hlen] at h

lemma revB_revB (g B x : ℕ) (hg : 1 < g) (hx : x < g ^ B) :
    revB g B (revB g B x) = x := by
  change Nat.ofDigits g (padDigits g B (revB g B x)).reverse = x
  rw [padDigits_revB g B x hg, List.reverse_reverse, ofDigits_padDigits g B x (by omega),
    Nat.mod_eq_of_lt hx]

lemma revB_inj (g B : ℕ) (hg : 1 < g) {x y : ℕ} (hx : x < g ^ B) (hy : y < g ^ B)
    (h : revB g B x = revB g B y) : x = y := by
  have h1 := congrArg (revB g B) h
  rwa [revB_revB g B x hg hx, revB_revB g B y hg hy] at h1

lemma padDigits_zero (g B : ℕ) : padDigits g B 0 = List.replicate B 0 := by
  induction B with
  | zero => simp [padDigits, Nat.mod_one]
  | succ B ih => simp [padDigits, ih, List.replicate_succ]

lemma ofDigits_replicate_zero (g k : ℕ) : Nat.ofDigits g (List.replicate k 0) = 0 := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.replicate_succ, Nat.ofDigits, ih]

lemma revB_zero (g B : ℕ) : revB g B 0 = 0 := by
  unfold revB
  rw [padDigits_zero, List.reverse_replicate, ofDigits_replicate_zero]

lemma padDigits_mul_pow (g : ℕ) (hg : 0 < g) :
    ∀ k B x : ℕ, k ≤ B →
      padDigits g B (g ^ k * x) = List.replicate k 0 ++ padDigits g (B - k) x := by
  intro k
  induction k with
  | zero =>
    intro B x _
    simp
  | succ k ih =>
    intro B x hk
    obtain ⟨B', rfl⟩ : ∃ B', B = B' + 1 := ⟨B - 1, by omega⟩
    have hpow : g ^ (k + 1) * x = g * (g ^ k * x) := by ring
    rw [hpow, padDigits, Nat.mul_mod_right, Nat.mul_div_right _ hg]
    rw [ih B' x (by omega), List.replicate_succ]
    simp [Nat.succ_sub_succ]

lemma revB_mul_pow_lt (g B k x : ℕ) (hg : 1 < g) (hk : k ≤ B) :
    revB g B (g ^ k * x) < g ^ (B - k) := by
  unfold revB
  rw [padDigits_mul_pow g (by omega) k B x hk, List.reverse_append, List.reverse_replicate,
    Nat.ofDigits_append, ofDigits_replicate_zero, mul_zero, add_zero]
  have hlen : (padDigits g (B - k) x).reverse.length = B - k := by
    rw [List.length_reverse, padDigits_length]
  calc Nat.ofDigits g (padDigits g (B - k) x).reverse
      < g ^ (padDigits g (B - k) x).reverse.length := by
        apply Nat.ofDigits_lt_base_pow_length hg
        intro d hd
        rw [List.mem_reverse] at hd
        exact padDigits_lt g (B - k) x (by omega) d hd
    _ = g ^ (B - k) := by rw [hlen]

lemma padDigits_lt_pow_append (g : ℕ) (hg : 0 < g) :
    ∀ m x : ℕ, x < g ^ m → padDigits g (m + 1) x = padDigits g m x ++ [0] := by
  intro m
  induction m with
  | zero =>
    intro x hx
    have hx0 : x = 0 := by simpa using hx
    subst hx0
    simp [padDigits]
  | succ m ih =>
    intro x hx
    have hdiv : x / g < g ^ m := by
      rw [Nat.div_lt_iff_lt_mul hg]
      simpa [pow_succ] using hx
    change (x % g) :: padDigits g (m + 1) (x / g) = (x % g) :: (padDigits g m (x / g) ++ [0])
    rw [ih (x / g) hdiv]

lemma revB_one_add_cube_lt (g B v : ℕ) (hg : 1 < g) (hB : 4 ≤ B) (hv : v < g ^ (B - 4)) :
    revB g B (1 + g ^ 3 * v) < g ^ (B - 1) + g ^ (B - 3) := by
  have hg0 : 0 < g := by omega
  obtain ⟨m, rfl⟩ : ∃ m, B = m + 4 := ⟨B - 4, by omega⟩
  have hx1 : (1 + g ^ 3 * v) % g = 1 := by
    have : 1 + g ^ 3 * v = 1 + g * (g ^ 2 * v) := by ring
    rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hg]
  have hx2 : (1 + g ^ 3 * v) / g = g ^ 2 * v := by
    have : 1 + g ^ 3 * v = 1 + g * (g ^ 2 * v) := by ring
    rw [this, Nat.add_mul_div_left _ _ hg0, Nat.div_eq_of_lt hg, zero_add]
  have h1 : padDigits g (m + 4) (1 + g ^ 3 * v) =
      1 :: 0 :: 0 :: padDigits g (m + 1) v := by
    rw [show m + 4 = (m + 3) + 1 by omega, padDigits, hx1, hx2]
    rw [show m + 3 = (m + 2) + 1 by omega, padDigits,
      show g ^ 2 * v = g * (g * v) by ring, Nat.mul_mod_right, Nat.mul_div_right _ hg0]
    rw [show m + 2 = (m + 1) + 1 by omega, padDigits, Nat.mul_mod_right, Nat.mul_div_right _ hg0]
  have h2 : padDigits g (m + 1) v = padDigits g m v ++ [0] :=
    padDigits_lt_pow_append g hg0 m v (by simpa using hv)
  unfold revB
  rw [h1, h2]
  have hrev : ([1, 0, 0] ++ (padDigits g m v ++ [0])).reverse =
      [0] ++ (padDigits g m v).reverse ++ [0, 0, 1] := by
    simp [List.reverse_append]
  change Nat.ofDigits g ([1, 0, 0] ++ (padDigits g m v ++ [0])).reverse < _
  rw [hrev, Nat.ofDigits_append, Nat.ofDigits_append]
  have hlen : (padDigits g m v).reverse.length = m := by
    rw [List.length_reverse, padDigits_length]
  have hr : Nat.ofDigits g (padDigits g m v).reverse < g ^ m := by
    calc Nat.ofDigits g (padDigits g m v).reverse
        < g ^ (padDigits g m v).reverse.length := by
          apply Nat.ofDigits_lt_base_pow_length hg
          intro d hd
          rw [List.mem_reverse] at hd
          exact padDigits_lt g m v hg0 d hd
      _ = g ^ m := by rw [hlen]
  have htail : Nat.ofDigits g [0, 0, 1] = g ^ 2 := by
    simp [Nat.ofDigits]
    ring
  have hzero : Nat.ofDigits g [0] = 0 := by simp [Nat.ofDigits]
  rw [hzero, zero_add, List.length_singleton, pow_one, List.length_append,
    List.length_singleton, hlen, htail]
  have hpow1 : g ^ (1 + m) * g ^ 2 = g ^ (m + 4 - 1) := by
    rw [show m + 4 - 1 = m + 3 by omega, pow_add, pow_add]
    ring
  have hpow2 : g * g ^ m = g ^ (m + 4 - 3) := by
    rw [show m + 4 - 3 = m + 1 by omega, pow_succ']
  rw [hpow1, ← hpow2]
  have hgmul : g * Nat.ofDigits g (padDigits g m v).reverse < g * g ^ m :=
    Nat.mul_lt_mul_of_pos_left hr hg0
  omega

lemma ofDigits_flatDigits (g B : ℕ) (hg : 0 < g) :
    ∀ L : List ℕ, (∀ x ∈ L, x < g ^ B) →
      Nat.ofDigits g (L.flatMap (padDigits g B)) = Nat.ofDigits (g ^ B) L := by
  intro L hL
  induction L with
  | nil => simp [Nat.ofDigits]
  | cons x xs ih =>
    have hx : x < g ^ B := hL x (by simp)
    have hxs : ∀ y ∈ xs, y < g ^ B := fun y hy => hL y (by simp [hy])
    simp only [List.flatMap_cons, Nat.ofDigits_append, padDigits_length,
      ofDigits_padDigits g B x hg, Nat.mod_eq_of_lt hx, ih hxs, Nat.ofDigits]
    rfl

lemma reverse_flatDigits (g B : ℕ) (hg : 1 < g) :
    ∀ L : List ℕ,
      (L.flatMap (padDigits g B)).reverse =
        (L.reverse.map (revB g B)).flatMap (padDigits g B) := by
  intro L
  induction L with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.reverse_append, ih,
      List.reverse_cons, List.map_append, List.map_singleton, List.flatMap_append]
    rw [padDigits_revB g B x hg]

lemma isPalindrome_of_blockList (g B : ℕ) (hg : 1 < g) (hB : 0 < B)
    (L : List ℕ) (hL_lt : ∀ x ∈ L, x < g ^ B)
    (hL_rev : L.reverse.map (revB g B) = L)
    (hL_head : ∃ x xs, L = x :: xs ∧ x % g ≠ 0) :
    IsPalindrome g (Nat.ofDigits (g ^ B) L) := by
  unfold IsPalindrome
  set ds := L.flatMap (padDigits g B)
  have hrev_ds : ds.reverse = ds := by
    dsimp [ds]
    rw [reverse_flatDigits g B hg L, hL_rev]
  have hdig : Nat.digits g (Nat.ofDigits (g ^ B) L) = ds := by
    rw [← ofDigits_flatDigits g B (by omega) L hL_lt]
    apply Nat.digits_ofDigits g hg
    · intro d hd
      simp only [List.mem_flatMap] at hd
      obtain ⟨x, _, hdx⟩ := hd
      exact padDigits_lt g B x (by omega) d hdx
    · intro hne
      obtain ⟨x, xs, rfl, hxmod⟩ := hL_head
      obtain ⟨B', rfl⟩ : ∃ B', B = B' + 1 := ⟨B - 1, by omega⟩
      have hds_eq : ds = (x % g) :: (padDigits g B' (x / g) ++ xs.flatMap (padDigits g (B' + 1))) := by
        simp [ds, padDigits]
      have hds_ne : ds ≠ [] := by
        rw [hds_eq]
        simp
      have hlast : ds.getLast hne = x % g := by
        have h1 : ds.getLast hne = ds.reverse.head (by rw [hrev_ds]; exact hds_ne) := by
          rw [List.getLast_eq_head_reverse]
        rw [h1]
        simp only [hrev_ds]
        rw [List.head_eq_iff_head?_eq_some]
        simp [hds_eq]
      rw [hlast]
      exact hxmod
  rw [hdig, hrev_ds]

lemma map_revB_pal_list (g B : ℕ) (hg : 1 < g)
    (H : List ℕ) (hH : ∀ x ∈ H, x < g ^ B) :
    (H ++ H.reverse.map (revB g B)).reverse.map (revB g B) =
      H ++ H.reverse.map (revB g B) := by
  have hid : (H.map (revB g B)).map (revB g B) = H := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id H]
    apply List.map_congr_left
    intro x hx
    exact revB_revB g B x hg (hH x hx)
  simp [List.map_reverse, hid]

lemma map_revB_pal_list_mid (g B : ℕ) (hg : 1 < g)
    (H : List ℕ) (hH : ∀ x ∈ H, x < g ^ B) :
    (H ++ [0] ++ H.reverse.map (revB g B)).reverse.map (revB g B) =
      H ++ [0] ++ H.reverse.map (revB g B) := by
  have hid : (H.map (revB g B)).map (revB g B) = H := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id H]
    apply List.map_congr_left
    intro x hx
    exact revB_revB g B x hg (hH x hx)
  simp [List.append_assoc, List.map_reverse, revB_zero, hid]

def listAdd : List ℕ → List ℕ → List ℕ
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => (x + y) :: listAdd xs ys

lemma ofDigits_listAdd (G : ℕ) :
    ∀ xs ys : List ℕ, Nat.ofDigits G (listAdd xs ys) = Nat.ofDigits G xs + Nat.ofDigits G ys := by
  intro xs
  induction xs with
  | nil =>
    intro ys
    simp [listAdd, Nat.ofDigits]
  | cons x xs ih =>
    intro ys
    cases ys with
    | nil => simp [listAdd, Nat.ofDigits]
    | cons y ys =>
      simp only [listAdd, Nat.ofDigits, ih ys, Nat.cast_add]
      ring

lemma listAdd_length (xs ys : List ℕ) :
    (listAdd xs ys).length = max xs.length ys.length := by
  induction xs generalizing ys with
  | nil => simp [listAdd]
  | cons x xs ih =>
    cases ys with
    | nil => simp [listAdd]
    | cons y ys => simp [listAdd, ih ys, Nat.succ_max_succ]

lemma listAdd_getD (xs ys : List ℕ) (i : ℕ) :
    (listAdd xs ys).getD i 0 = xs.getD i 0 + ys.getD i 0 := by
  induction xs generalizing ys i with
  | nil => simp [listAdd]
  | cons x xs ih =>
    cases ys with
    | nil => simp [listAdd]
    | cons y ys =>
      cases i with
      | zero => simp [listAdd]
      | succ i =>
        simp only [listAdd, List.getD_cons_succ]
        exact ih ys i

lemma ofDigits_eq_ofDigits_pad (G : ℕ) (hG : 1 < G) (l1 l2 : List ℕ)
    (hlen : l1.length = l2.length)
    (hl1 : ∀ x ∈ l1, x < G) (hl2 : ∀ x ∈ l2, x < G)
    (heq : Nat.ofDigits G l1 = Nat.ofDigits G l2) : l1 = l2 := by
  have h1 := padDigits_ofDigits_eq G hG l1 hl1
  have h2 := padDigits_ofDigits_eq G hG l2 hl2
  rw [← h1, ← h2, hlen, heq]

abbrev Params (g B k : ℕ) :=
  Fin (g ^ (B - 2)) × (Fin (k - 1) → Fin (g ^ (B - 6))) ×
    Fin (g ^ (B - 4)) × (Fin (k - 2) → Fin (g ^ (B - 2)))

def pHalf {g B k : ℕ} (p : Params g B k) : List ℕ :=
  (1 + g * p.1.1) :: (List.ofFn fun i : Fin (k - 1) => g ^ 3 * (p.2.1 i).1)

def qHalf {g B k : ℕ} (p : Params g B k) : List ℕ :=
  (1 + g ^ 3 * p.2.2.1.1) :: (List.ofFn fun i : Fin (k - 2) => g * (p.2.2.2 i).1)

def pList {g B k : ℕ} (p : Params g B k) : List ℕ :=
  pHalf p ++ (pHalf p).reverse.map (revB g B)

def qList {g B k : ℕ} (p : Params g B k) : List ℕ :=
  qHalf p ++ [0] ++ (qHalf p).reverse.map (revB g B)

lemma pHalf_length {g B k : ℕ} (hk : 1 ≤ k) (p : Params g B k) :
    (pHalf p).length = k := by
  simp [pHalf, List.length_ofFn]
  omega

lemma qHalf_length {g B k : ℕ} (hk : 2 ≤ k) (p : Params g B k) :
    (qHalf p).length = k - 1 := by
  simp [qHalf, List.length_ofFn]
  omega

lemma pList_length {g B k : ℕ} (hk : 1 ≤ k) (p : Params g B k) :
    (pList p).length = 2 * k := by
  simp [pList, pHalf_length hk p]
  omega

lemma qList_length {g B k : ℕ} (hk : 2 ≤ k) (p : Params g B k) :
    (qList p).length = 2 * k - 1 := by
  simp [qList, qHalf_length hk p]
  omega

lemma pHalf_lt {g B k : ℕ} (hg : 2 ≤ g) (hB : 6 ≤ B) (p : Params g B k) :
    ∀ x ∈ pHalf p, x < g ^ (B - 1) := by
  intro x hx
  simp only [pHalf, List.mem_cons, List.mem_ofFn] at hx
  rcases hx with rfl | ⟨i, rfl⟩
  · calc 1 + g * p.1.1
        < g + g * p.1.1 := by omega
      _ = g * (p.1.1 + 1) := by ring
      _ ≤ g * g ^ (B - 2) := Nat.mul_le_mul_left g p.1.2
      _ = g ^ (B - 1) := by rw [← pow_succ']; congr 1; omega
  · have hu : (p.2.1 i).1 < g ^ (B - 6) := (p.2.1 i).2
    have hpow1 : g ^ (B - 3) = g ^ 3 * g ^ (B - 6) := by
      rw [← pow_add]
      congr 1
      omega
    have hlt : g ^ 3 * (p.2.1 i).1 < g ^ (B - 3) := by
      rw [hpow1]
      exact Nat.mul_lt_mul_of_pos_left hu (pow_pos (by omega) 3)
    have hle : g ^ (B - 3) ≤ g ^ (B - 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    omega

lemma pList_lt {g B k : ℕ} (hg : 2 ≤ g) (hB : 6 ≤ B) (p : Params g B k) :
    ∀ x ∈ pList p, x < g ^ B := by
  intro x hx
  simp only [pList, List.mem_append, List.mem_map, List.mem_reverse] at hx
  rcases hx with hx | ⟨y, _, rfl⟩
  · have hlt := pHalf_lt hg hB p x hx
    have hle : g ^ (B - 1) ≤ g ^ B := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  · exact revB_lt g B y (by omega)

lemma qHalf_lt {g B k : ℕ} (hg : 2 ≤ g) (hB : 6 ≤ B) (p : Params g B k) :
    ∀ x ∈ qHalf p, x < g ^ (B - 1) := by
  intro x hx
  simp only [qHalf, List.mem_cons, List.mem_ofFn] at hx
  rcases hx with rfl | ⟨i, rfl⟩
  · have hv : p.2.2.1.1 < g ^ (B - 4) := p.2.2.1.2
    have hg3 : 2 ≤ g ^ 3 := by
      have : 2 ^ 3 ≤ g ^ 3 := Nat.pow_le_pow_left hg 3
      omega
    calc 1 + g ^ 3 * p.2.2.1.1
        < g ^ 3 + g ^ 3 * p.2.2.1.1 := by omega
      _ = g ^ 3 * (p.2.2.1.1 + 1) := by ring
      _ ≤ g ^ 3 * g ^ (B - 4) := Nat.mul_le_mul_left _ hv
      _ = g ^ (B - 1) := by rw [← pow_add]; congr 1; omega
  · have hv : (p.2.2.2 i).1 < g ^ (B - 2) := (p.2.2.2 i).2
    have hpow : g ^ (B - 1) = g * g ^ (B - 2) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [hpow]
    exact Nat.mul_lt_mul_of_pos_left hv (by omega)

lemma qList_lt {g B k : ℕ} (hg : 2 ≤ g) (hB : 6 ≤ B) (p : Params g B k) :
    ∀ x ∈ qList p, x < g ^ B := by
  intro x hx
  simp only [qList, List.append_assoc, List.mem_append, List.mem_singleton,
    List.mem_map, List.mem_reverse] at hx
  rcases hx with hx | rfl | ⟨y, _, rfl⟩
  · have hlt := qHalf_lt hg hB p x hx
    have hle : g ^ (B - 1) ≤ g ^ B := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  · exact pow_pos (by omega) B
  · exact revB_lt g B y (by omega)

def palP {g B k : ℕ} (p : Params g B k) : ℕ :=
  Nat.ofDigits (g ^ B) (pList p)

def palQ {g B k : ℕ} (p : Params g B k) : ℕ :=
  Nat.ofDigits (g ^ B) (qList p)

lemma isPalindrome_palP {g B k : ℕ} (hg : 2 ≤ g) (hB : 6 ≤ B) (p : Params g B k) :
    IsPalindrome g (palP p) := by
  apply isPalindrome_of_blockList g B (by omega) (by omega) (pList p)
  · exact pList_lt hg hB p
  · exact map_revB_pal_list g B (by omega) (pHalf p) fun x hx =>
      lt_of_lt_of_le (pHalf_lt hg hB p x hx) (Nat.pow_le_pow_right (by omega) (by omega))
  · refine ⟨1 + g * p.1.1,
      (List.ofFn fun i : Fin (k - 1) => g ^ 3 * (p.2.1 i).1) ++ (pHalf p).reverse.map (revB g B),
      by simp [pList, pHalf], ?_⟩
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    omega

lemma isPalindrome_palQ {g B k : ℕ} (hg : 2 ≤ g) (hB : 6 ≤ B) (p : Params g B k) :
    IsPalindrome g (palQ p) := by
  apply isPalindrome_of_blockList g B (by omega) (by omega) (qList p)
  · exact qList_lt hg hB p
  · exact map_revB_pal_list_mid g B (by omega) (qHalf p) fun x hx =>
      lt_of_lt_of_le (qHalf_lt hg hB p x hx) (Nat.pow_le_pow_right (by omega) (by omega))
  · refine ⟨1 + g ^ 3 * p.2.2.1.1,
      (List.ofFn fun i : Fin (k - 2) => g * (p.2.2.2 i).1) ++ [0] ++ (qHalf p).reverse.map (revB g B),
      by simp [qList, qHalf, List.append_assoc], ?_⟩
    have : 1 + g ^ 3 * p.2.2.1.1 = 1 + g * (g ^ 2 * p.2.2.1.1) := by ring
    rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    omega

lemma pList_getD_0 {g B k : ℕ} (p : Params g B k) :
    (pList p).getD 0 0 = 1 + g * p.1.1 := by
  simp [pList, pHalf]

lemma qList_getD_0 {g B k : ℕ} (p : Params g B k) :
    (qList p).getD 0 0 = 1 + g ^ 3 * p.2.2.1.1 := by
  simp [qList, qHalf]

lemma pList_getD_inner {g B k : ℕ} (hk : 2 ≤ k) (p : Params g B k) (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j < k) :
    (pList p).getD j 0 = g ^ 3 * (p.2.1 ⟨j - 1, by omega⟩).1 := by
  have hlen : (pHalf p).length = k := pHalf_length (by omega) p
  rw [pList, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
  cases j with
  | zero => omega
  | succ m => simp [pHalf, dif_pos (show m < k - 1 by omega)]

lemma qList_getD_inner {g B k : ℕ} (hk : 2 ≤ k) (p : Params g B k) (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j < k - 1) :
    (qList p).getD j 0 = g * (p.2.2.2 ⟨j - 1, by omega⟩).1 := by
  have hlen : (qHalf p).length = k - 1 := qHalf_length hk p
  rw [qList, List.append_assoc, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
  cases j with
  | zero => omega
  | succ m => simp [qHalf, dif_pos (show m < k - 2 by omega)]

lemma qList_getD_mid {g B k : ℕ} (hk : 2 ≤ k) (p : Params g B k) :
    (qList p).getD (k - 1) 0 = 0 := by
  have hlen : (qHalf p).length = k - 1 := qHalf_length hk p
  rw [qList, List.append_assoc, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
  simp [hlen]

lemma qList_getD_top {g B k : ℕ} (hk : 2 ≤ k) (p : Params g B k) :
    (qList p).getD (2 * k - 1) 0 = 0 := by
  have hlen : (qList p).length = 2 * k - 1 := qList_length hk p
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

lemma pList_getD_mirror {g B k : ℕ} (hk : 2 ≤ k) (p : Params g B k) (j : ℕ) (hj : j < k) :
    (pList p).getD (2 * k - 1 - j) 0 = revB g B ((pList p).getD j 0) := by
  have hlen : (pHalf p).length = k := pHalf_length (by omega) p
  have hpos : k ≤ 2 * k - 1 - j := by omega
  rw [pList, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
  have hidx : 2 * k - 1 - j - (pHalf p).length = k - 1 - j := by omega
  rw [hidx]
  have hlt : k - 1 - j < ((pHalf p).reverse.map (revB g B)).length := by simp [hlen]; omega
  rw [List.getElem?_eq_getElem hlt, Option.getD_some, List.getElem_map, List.getElem_reverse]
  have h1 : (pHalf p).length - 1 - (k - 1 - j) = j := by omega
  simp only [h1]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), List.getElem?_eq_getElem (by omega)]
  rfl

lemma qList_getD_mirror {g B k : ℕ} (hk : 2 ≤ k) (p : Params g B k) (j : ℕ) (hj : j < k - 1) :
    (qList p).getD (2 * k - 2 - j) 0 = revB g B ((qList p).getD j 0) := by
  have hlen : (qHalf p).length = k - 1 := qHalf_length hk p
  rw [qList, List.append_assoc, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
  have hlen2 : ([0] ++ (qHalf p).reverse.map (revB g B)).length = k := by simp [hlen]; omega
  have hidx1 : 2 * k - 2 - j - (qHalf p).length = (k - 2 - j) + 1 := by omega
  rw [hidx1]
  have hge : 1 ≤ k - 2 - j + 1 := by omega
  rw [List.getElem?_append_right hge]
  simp only [List.length_singleton, Nat.add_sub_cancel]
  have hlt : k - 2 - j < ((qHalf p).reverse.map (revB g B)).length := by simp [hlen]; omega
  rw [List.getElem?_eq_getElem hlt, Option.getD_some, List.getElem_map, List.getElem_reverse]
  have h1 : (qHalf p).length - 1 - (k - 2 - j) = j := by omega
  simp only [h1]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
    List.getElem?_eq_getElem (by omega)]
  rfl

lemma listAdd_pq_lt {g B k : ℕ} (hg : 2 ≤ g) (hB : 6 ≤ B) (hk : 2 ≤ k) (p : Params g B k) :
    ∀ x ∈ listAdd (pList p) (qList p), x < g ^ B := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  have hlen_p : (pList p).length = 2 * k := pList_length (by omega) p
  have hlen_q : (qList p).length = 2 * k - 1 := qList_length hk p
  have hlen : (listAdd (pList p) (qList p)).length = 2 * k := by
    rw [listAdd_length, hlen_p, hlen_q]
    omega
  rw [hlen] at hi
  have hget : (listAdd (pList p) (qList p))[i] = (pList p).getD i 0 + (qList p).getD i 0 := by
    rw [← listAdd_getD (pList p) (qList p) i, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega), Option.getD_some]
  rw [hget]
  have hp_pow : 2 * g ^ (B - 1) ≤ g ^ B := by
    have hpow : g ^ B = g * g ^ (B - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [hpow]
    exact Nat.mul_le_mul_right _ hg
  have hp_mem : ∀ j < k, (pList p).getD j 0 < g ^ (B - 1) := by
    intro j hj
    rw [pList, List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [pHalf_length (by omega) p]; exact hj)]
    have hmem : (pHalf p)[j]'(by rw [pHalf_length (by omega) p]; exact hj) ∈ pHalf p := List.getElem_mem _
    have hge := pHalf_lt hg hB p _ hmem
    rwa [List.getElem?_eq_getElem (by rw [pHalf_length (by omega) p]; exact hj), Option.getD_some]
  have hp_inner_lt : ∀ j, 1 ≤ j → j < k → (pList p).getD j 0 < g ^ (B - 3) := by
    intro j hj1 hj2
    rw [pList_getD_inner hk p j hj1 hj2]
    have hpow : g ^ (B - 3) = g ^ 3 * g ^ (B - 6) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hpow]
    exact Nat.mul_lt_mul_of_pos_left (p.2.1 ⟨j - 1, by omega⟩).2 (pow_pos (by omega) 3)
  have hp_mirror_lt : ∀ j, 1 ≤ j → j < k → (pList p).getD (2 * k - 1 - j) 0 < g ^ (B - 3) := by
    intro j hj1 hj2
    rw [pList_getD_mirror hk p j hj2, pList_getD_inner hk p j hj1 hj2]
    exact revB_mul_pow_lt g B 3 _ (by omega) (by omega)
  have hq_mem : ∀ j < k - 1, (qList p).getD j 0 < g ^ (B - 1) := by
    intro j hj
    rw [qList, List.append_assoc, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by rw [qHalf_length hk p]; exact hj)]
    have hmem : (qHalf p)[j]'(by rw [qHalf_length hk p]; exact hj) ∈ qHalf p := List.getElem_mem _
    have hge := qHalf_lt hg hB p _ hmem
    rwa [List.getElem?_eq_getElem (by rw [qHalf_length hk p]; exact hj), Option.getD_some]
  have hq_mirror_lt : ∀ j, 1 ≤ j → j < k - 1 → (qList p).getD (2 * k - 2 - j) 0 < g ^ (B - 1) := by
    intro j hj1 hj2
    rw [qList_getD_mirror hk p j hj2, qList_getD_inner hk p j hj1 hj2]
    simpa only [pow_one] using revB_mul_pow_lt g B 1 _ (by omega) (by omega)
  by_cases hi0 : i = 0
  · subst hi0
    have h1 := hp_mem 0 (by omega)
    have h2 := hq_mem 0 (by omega)
    omega
  · by_cases hik1 : i < k - 1
    · have h1 := hp_inner_lt i (by omega) (by omega)
      have h2 := hq_mem i hik1
      have hle : g ^ (B - 3) ≤ g ^ (B - 1) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    · by_cases himid : i = k - 1
      · subst himid
        rw [qList_getD_mid hk p, add_zero]
        have h1 := hp_mem (k - 1) (by omega)
        have hle : g ^ (B - 1) ≤ g ^ B := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      · by_cases hi2k2 : i < 2 * k - 2
        · set j1 := 2 * k - 1 - i
          set j2 := 2 * k - 2 - i
          have hp_eq : (pList p).getD i 0 = (pList p).getD (2 * k - 1 - j1) 0 := by
            congr 1; omega
          have hq_eq : (qList p).getD i 0 = (qList p).getD (2 * k - 2 - j2) 0 := by
            congr 1; omega
          rw [hp_eq, hq_eq]
          have h1 := hp_mirror_lt j1 (by omega) (by omega)
          have h2 := hq_mirror_lt j2 (by omega) (by omega)
          have hle : g ^ (B - 3) ≤ g ^ (B - 1) := Nat.pow_le_pow_right (by omega) (by omega)
          omega
        · by_cases hi_last : i = 2 * k - 2
          · subst hi_last
            have hp_eq : (pList p).getD (2 * k - 2) 0 = (pList p).getD (2 * k - 1 - 1) 0 :=
              congrArg (fun idx => (pList p).getD idx 0) (by omega)
            have hq_eq : (qList p).getD (2 * k - 2) 0 = (qList p).getD (2 * k - 2 - 0) 0 := rfl
            rw [hp_eq, hq_eq, qList_getD_mirror hk p 0 (by omega), qList_getD_0]
            have h1 := hp_mirror_lt 1 (le_refl 1) (by omega)
            have h2 := revB_one_add_cube_lt g B p.2.2.1.1 (by omega) (by omega) p.2.2.1.2
            have h2g : 2 * g ^ (B - 3) ≤ g ^ (B - 1) := by
              have hpow : g ^ (B - 1) = g ^ 2 * g ^ (B - 3) := by
                rw [← pow_add]
                congr 1
                omega
              have hg2 : 2 ≤ g ^ 2 := by
                have : 2 ^ 2 ≤ g ^ 2 := Nat.pow_le_pow_left hg 2
                omega
              rw [hpow]
              exact Nat.mul_le_mul_right _ hg2
            omega
          · have hitop : i = 2 * k - 1 := by omega
            subst hitop
            rw [qList_getD_top hk p, add_zero]
            have hmem : (pList p)[2 * k - 1]'(by rw [pList_length (by omega) p]; omega) ∈ pList p :=
              List.getElem_mem _
            have hlt := pList_lt hg hB p _ hmem
            rwa [List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem (by rw [pList_length (by omega) p]; omega), Option.getD_some]

def sumPQ {g B k : ℕ} (p : Params g B k) : ℕ :=
  palP p + palQ p

lemma sumPQ_pos {g B k : ℕ} (_hg : 2 ≤ g) (_hB : 6 ≤ B) (_hk : 2 ≤ k) (p : Params g B k) :
    0 < sumPQ p := by
  unfold sumPQ palP
  have h0 : pList p = (1 + g * p.1.1) :: ((List.ofFn fun i : Fin (k - 1) => g ^ 3 * (p.2.1 i).1) ++ (pHalf p).reverse.map (revB g B)) := by
    simp [pList, pHalf]
  rw [h0, Nat.ofDigits]
  exact Nat.add_pos_left (Nat.add_pos_left (Nat.add_pos_left Nat.zero_lt_one _) _) _

lemma sumPQ_lt {g B k : ℕ} (hg : 2 ≤ g) (hB : 6 ≤ B) (hk : 2 ≤ k) (p : Params g B k) :
    sumPQ p < g ^ (2 * k * B) := by
  unfold sumPQ palP palQ
  rw [← ofDigits_listAdd (g ^ B) (pList p) (qList p)]
  have hlen : (listAdd (pList p) (qList p)).length = 2 * k := by
    rw [listAdd_length, pList_length (by omega) p, qList_length hk p]
    omega
  have hpow : g ^ (2 * k * B) = (g ^ B) ^ (2 * k) := by
    rw [← pow_mul]
    congr 1
    ring
  rw [hpow, ← hlen]
  apply Nat.ofDigits_lt_base_pow_length (one_lt_pow₀ (by omega) (by omega))
  exact listAdd_pq_lt hg hB hk p

lemma sumPQ_injective (g B k : ℕ) (hg : 2 ≤ g) (hB : 6 ≤ B) (hk : 2 ≤ k) :
    Function.Injective (sumPQ (g := g) (B := B) (k := k)) := by
  intro p p' hsum
  have hG : 1 < g ^ B := one_lt_pow₀ (by omega) (by omega)
  have hlen : (listAdd (pList p) (qList p)).length = (listAdd (pList p') (qList p')).length := by
    rw [listAdd_length, listAdd_length, pList_length (by omega) p, qList_length hk p,
      pList_length (by omega) p', qList_length hk p']
  have hdig : Nat.ofDigits (g ^ B) (listAdd (pList p) (qList p)) =
      Nat.ofDigits (g ^ B) (listAdd (pList p') (qList p')) := by
    rw [ofDigits_listAdd, ofDigits_listAdd]
    exact hsum
  have hlist := ofDigits_eq_ofDigits_pad (g ^ B) hG _ _ hlen
    (listAdd_pq_lt hg hB hk p) (listAdd_pq_lt hg hB hk p') hdig
  have hadd : ∀ i, (pList p).getD i 0 + (qList p).getD i 0 =
      (pList p').getD i 0 + (qList p').getD i 0 := by
    intro i
    rw [← listAdd_getD, ← listAdd_getD, hlist]
  have hp_mem_lt : ∀ q : Params g B k, ∀ j < k, (pList q).getD j 0 < g ^ B := by
    intro q j hj
    have hlt : j < (pList q).length := by rw [pList_length (by omega) q]; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
    exact pList_lt hg hB q _ (List.getElem_mem _)
  have hq_mem_lt : ∀ q : Params g B k, ∀ j < k - 1, (qList q).getD j 0 < g ^ B := by
    intro q j hj
    have hlt : j < (qList q).length := by rw [qList_length hk q]; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
    exact qList_lt hg hB q _ (List.getElem_mem _)
  -- 1. P_0 from index 2*k - 1
  have hP0 : (pList p).getD 0 0 = (pList p').getD 0 0 := by
    have htop := hadd (2 * k - 1)
    rw [qList_getD_top hk p, qList_getD_top hk p', add_zero, add_zero] at htop
    have hm1 := pList_getD_mirror hk p 0 (by omega)
    have hm2 := pList_getD_mirror hk p' 0 (by omega)
    simp only [Nat.sub_zero] at hm1 hm2
    rw [hm1, hm2] at htop
    exact revB_inj g B (by omega) (hp_mem_lt p 0 (by omega)) (hp_mem_lt p' 0 (by omega)) htop
  -- 2. Q_0 from index 0
  have hQ0 : (qList p).getD 0 0 = (qList p').getD 0 0 := by
    have h0 := hadd 0
    rw [hP0] at h0
    omega
  -- 3. Induction on j < k - 1 for P_j and Q_j
  have hPQ : ∀ j, j < k - 1 →
      (pList p).getD j 0 = (pList p').getD j 0 ∧
      (qList p).getD j 0 = (qList p').getD j 0 := by
    intro j
    induction j with
    | zero =>
      intro _
      exact ⟨hP0, hQ0⟩
    | succ j ih =>
      intro hj
      have hprev := ih (by omega)
      have hpj : (pList p).getD (j + 1) 0 = (pList p').getD (j + 1) 0 := by
        have hmir := hadd (2 * k - 1 - (j + 1))
        have hidx1 : (qList p).getD (2 * k - 1 - (j + 1)) 0 =
            (qList p).getD (2 * k - 2 - j) 0 := by congr 1; omega
        have hidx2 : (qList p').getD (2 * k - 1 - (j + 1)) 0 =
            (qList p').getD (2 * k - 2 - j) 0 := by congr 1; omega
        rw [hidx1, hidx2, qList_getD_mirror hk p j (by omega),
          qList_getD_mirror hk p' j (by omega), hprev.2] at hmir
        have hp_eq : (pList p).getD (2 * k - 1 - (j + 1)) 0 =
            (pList p').getD (2 * k - 1 - (j + 1)) 0 := by omega
        rw [pList_getD_mirror hk p (j + 1) (by omega),
          pList_getD_mirror hk p' (j + 1) (by omega)] at hp_eq
        exact revB_inj g B (by omega) (hp_mem_lt p (j + 1) (by omega))
          (hp_mem_lt p' (j + 1) (by omega)) hp_eq
      have hqj : (qList p).getD (j + 1) 0 = (qList p').getD (j + 1) 0 := by
        have hsumj := hadd (j + 1)
        rw [hpj] at hsumj
        omega
      exact ⟨hpj, hqj⟩
  -- 4. P_{k-1} from index k
  have hPk1 : (pList p).getD (k - 1) 0 = (pList p').getD (k - 1) 0 := by
    have hmir := hadd k
    have hidx1 : (qList p).getD k 0 = (qList p).getD (2 * k - 2 - (k - 2)) 0 := by
      congr 1; omega
    have hidx2 : (qList p').getD k 0 = (qList p').getD (2 * k - 2 - (k - 2)) 0 := by
      congr 1; omega
    rw [hidx1, hidx2, qList_getD_mirror hk p (k - 2) (by omega),
      qList_getD_mirror hk p' (k - 2) (by omega), (hPQ (k - 2) (by omega)).2] at hmir
    have hp_eq : (pList p).getD k 0 = (pList p').getD k 0 := by omega
    have hidp1 : (pList p).getD k 0 = (pList p).getD (2 * k - 1 - (k - 1)) 0 := by
      congr 1; omega
    have hidp2 : (pList p').getD k 0 = (pList p').getD (2 * k - 1 - (k - 1)) 0 := by
      congr 1; omega
    rw [hidp1, hidp2, pList_getD_mirror hk p (k - 1) (by omega),
      pList_getD_mirror hk p' (k - 1) (by omega)] at hp_eq
    exact revB_inj g B (by omega) (hp_mem_lt p (k - 1) (by omega))
      (hp_mem_lt p' (k - 1) (by omega)) hp_eq
  -- 5. Reconstruct equality of all 4 fields
  have hu0 : p.1 = p'.1 := by
    ext
    rw [pList_getD_0, pList_getD_0] at hP0
    have h1 : g * p.1.1 = g * p'.1.1 := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega) h1
  have hv0 : p.2.2.1 = p'.2.2.1 := by
    ext
    rw [qList_getD_0, qList_getD_0] at hQ0
    have hpow : 0 < g ^ 3 := pow_pos (by omega) 3
    have h1 : g ^ 3 * p.2.2.1.1 = g ^ 3 * p'.2.2.1.1 := by omega
    exact Nat.eq_of_mul_eq_mul_left hpow h1
  have hu : p.2.1 = p'.2.1 := by
    funext i
    ext
    have hj : i.1 + 1 < k := by omega
    have heq : (pList p).getD (i.1 + 1) 0 = (pList p').getD (i.1 + 1) 0 := by
      by_cases hlt : i.1 + 1 < k - 1
      · exact (hPQ (i.1 + 1) hlt).1
      · have heqk : i.1 + 1 = k - 1 := by omega
        rwa [heqk]
    rw [pList_getD_inner hk p (i.1 + 1) (by omega) hj,
      pList_getD_inner hk p' (i.1 + 1) (by omega) hj] at heq
    have hpow : 0 < g ^ 3 := pow_pos (by omega) 3
    have hfin : (⟨i.1 + 1 - 1, by omega⟩ : Fin (k - 1)) = i := by ext; simp
    rw [hfin] at heq
    exact Nat.eq_of_mul_eq_mul_left hpow heq
  have hv : p.2.2.2 = p'.2.2.2 := by
    funext i
    ext
    have hj : i.1 + 1 < k - 1 := by omega
    have heq := (hPQ (i.1 + 1) hj).2
    rw [qList_getD_inner hk p (i.1 + 1) (by omega) hj,
      qList_getD_inner hk p' (i.1 + 1) (by omega) hj] at heq
    have hfin : (⟨i.1 + 1 - 1, by omega⟩ : Fin (k - 2)) = i := by ext; simp
    rw [hfin] at heq
    exact Nat.eq_of_mul_eq_mul_left (by omega) heq
  rcases p with ⟨a, b, c, d⟩
  rcases p' with ⟨a', b', c', d'⟩
  dsimp at hu0 hv0 hu hv
  subst hu0 hv0 hu hv
  rfl

lemma card_params_ge (g B k : ℕ) (hB : 6 ≤ B) (hk : 2 ≤ k) :
    g ^ ((2 * k - 1) * B - 8 * k + 4) ≤ Fintype.card (Params g B k) := by
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add, ← pow_add]
  apply le_of_eq
  congr 1
  have h8k : 8 * k ≤ (2 * k - 1) * B := by
    have h1 : (2 * k - 1) * 6 ≤ (2 * k - 1) * B := Nat.mul_le_mul_left _ hB
    omega
  zify [show 2 ≤ B by omega, show 6 ≤ B by omega, show 4 ≤ B by omega,
    show 1 ≤ k by omega, show 2 ≤ k by omega, show 1 ≤ 2 * k by omega, h8k]
  ring

lemma card_sums_ge (g B k : ℕ) (hg : 2 ≤ g) (hB : 6 ≤ B) (hk : 2 ≤ k) :
    g ^ ((2 * k - 1) * B - 8 * k + 4) ≤
      ({n : ℕ | 0 < n ∧ n ≤ g ^ (2 * k * B) ∧ n ∈ sumsOfTwo g}).ncard := by
  set S : Set ℕ := {n : ℕ | 0 < n ∧ n ≤ g ^ (2 * k * B) ∧ n ∈ sumsOfTwo g}
  have hS_fin : S.Finite := (Set.finite_Icc 0 (g ^ (2 * k * B))).subset fun n hn => ⟨by omega, hn.2.1⟩
  have hsub : (sumPQ (g := g) (B := B) (k := k)) '' Set.univ ⊆ S := by
    rintro n ⟨p, _, rfl⟩
    refine ⟨sumPQ_pos hg hB hk p, le_of_lt (sumPQ_lt hg hB hk p), ?_⟩
    exact ⟨palP p, palQ p, isPalindrome_palP hg hB p, isPalindrome_palQ hg hB p, rfl⟩
  calc g ^ ((2 * k - 1) * B - 8 * k + 4)
      ≤ Fintype.card (Params g B k) := card_params_ge g B k hB hk
    _ = Nat.card (Params g B k) := (Nat.card_eq_fintype_card).symm
    _ = (Set.univ : Set (Params g B k)).ncard := (Set.ncard_univ _).symm
    _ = ((sumPQ (g := g) (B := B) (k := k)) '' Set.univ).ncard :=
      (Set.ncard_image_of_injective _ (sumPQ_injective g B k hg hB hk)).symm
    _ ≤ S.ncard := Set.ncard_le_ncard hsub hS_fin

end Green95LowerBound

theorem OMA.solution : type_of% @Green95.green_95.variants.lower_bound := by
  intro g hg
  refine ⟨20 * (Real.log (g : ℝ) + 1), ?_, ?_⟩
  · have hlog : 0 < Real.log (g : ℝ) := Real.log_pos (by exact_mod_cast hg)
    linarith
  intro x hx
  set c₁ : ℝ := 20 * (Real.log (g : ℝ) + 1)
  have hx_pos : (0 : ℝ) < x := by linarith
  have hx_gt_one : (1 : ℝ) < x := by linarith
  have hlogx_pos : 0 < Real.log x := Real.log_pos hx_gt_one
  have hlogg_pos : 0 < Real.log (g : ℝ) := Real.log_pos (by exact_mod_cast hg)
  set S : Set ℕ := {n : ℕ | 0 < n ∧ (n : ℝ) ≤ x ∧ n ∈ Green95.sumsOfTwo g}
  have hS_fin : S.Finite := by
    refine (Set.finite_Icc 0 ⌊x⌋₊).subset fun n hn => ⟨Nat.zero_le n, ?_⟩
    exact Nat.le_floor hn.2.1
  by_cases hx_small : x < (g : ℝ) ^ (240 : ℕ)
  · have hlog_lt : Real.log x < 240 * Real.log (g : ℝ) := by
      have := Real.log_lt_log hx_pos hx_small
      simpa [Real.log_pow] using this
    have hc_sq : 240 * Real.log (g : ℝ) < c₁ ^ 2 := by
      dsimp [c₁]
      nlinarith
    have hsqrt_lt : Real.sqrt (Real.log x) < c₁ := by
      have : Real.log x < c₁ ^ 2 := lt_trans hlog_lt hc_sq
      calc Real.sqrt (Real.log x) < Real.sqrt (c₁ ^ 2) := Real.sqrt_lt_sqrt hlogx_pos.le this
        _ = c₁ := Real.sqrt_sq (by positivity)
    have hexp_nonpos : 1 - c₁ / Real.sqrt (Real.log x) ≤ 0 := by
      have hs : 0 < Real.sqrt (Real.log x) := Real.sqrt_pos.mpr hlogx_pos
      rw [sub_nonpos, le_div_iff₀ hs]
      linarith
    have hrpow : x ^ (1 - c₁ / Real.sqrt (Real.log x)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hx_gt_one.le hexp_nonpos
    have h1_mem : (1 : ℕ) ∈ S := by
      refine ⟨by norm_num, by norm_num; linarith, 1, 0, ?_, Green95.isPalindrome_zero g, by norm_num⟩
      unfold Green95.IsPalindrome
      rw [Nat.digits_of_lt g 1 (by norm_num) (by omega)]
      rfl
    have hncard_pos : 1 ≤ S.ncard := Set.ncard_pos hS_fin |>.mpr ⟨1, h1_mem⟩
    have hncard_real : (1 : ℝ) ≤ (S.ncard : ℝ) := by exact_mod_cast hncard_pos
    linarith
  · push Not at hx_small
    set N : ℕ := ⌊x⌋₊
    have hN_ge : g ^ 240 ≤ N := by
      have h1 : (g ^ 240 : ℕ) ≤ ⌊x⌋₊ := Nat.le_floor (by push_cast; exact hx_small)
      exact h1
    set L : ℕ := Nat.log g N
    have hL_ge : 240 ≤ L := Nat.le_log_of_pow_le (by omega) hN_ge
    have hN_pos : N ≠ 0 := by
      have h1 : 1 ≤ g ^ 240 := Nat.one_le_pow 240 g (by omega)
      omega
    have hgL_le : (g : ℝ) ^ L ≤ x := by
      have h1 : g ^ L ≤ N := Nat.pow_log_le_self g hN_pos
      have h2 : (N : ℝ) ≤ x := Nat.floor_le hx_pos.le
      calc (g : ℝ) ^ L = ((g ^ L : ℕ) : ℝ) := by push_cast; rfl
        _ ≤ (N : ℝ) := by exact_mod_cast h1
        _ ≤ x := h2
    have hx_lt_gL1 : x < (g : ℝ) ^ (L + 1) := by
      have h1 : N < g ^ (L + 1) := Nat.lt_pow_succ_log_self (by omega) N
      have h2 : x < (N : ℝ) + 1 := Nat.lt_floor_add_one x
      have h3 : N + 1 ≤ g ^ (L + 1) := h1
      have h4 : ((N + 1 : ℕ) : ℝ) ≤ ((g ^ (L + 1) : ℕ) : ℝ) := by exact_mod_cast h3
      push_cast at h4
      linarith
    set B : ℕ := Nat.sqrt (L / 2)
    have hB_ge : 10 ≤ B := by
      rw [Nat.le_sqrt]
      omega
    have hB_sq : 2 * B ^ 2 ≤ L := by
      have h1 : B * B ≤ L / 2 := Nat.sqrt_le (L / 2)
      rw [sq]
      omega
    have hL_lt_B : L < 2 * (B + 1) ^ 2 := by
      have h1 : L / 2 < (B + 1) * (B + 1) := Nat.lt_succ_sqrt (L / 2)
      rw [sq]
      omega
    set k : ℕ := L / (2 * B)
    have hk_ge : 2 ≤ k := by
      rw [Nat.le_div_iff_mul_le (by omega)]
      nlinarith
    have hk_le : k ≤ 2 * B := by
      rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
      nlinarith
    have h2kB_le : 2 * k * B ≤ L := by
      calc 2 * k * B = k * (2 * B) := by ring
        _ ≤ L := Nat.div_mul_le_self L (2 * B)
    have hL_lt_2k1B : L < 2 * (k + 1) * B := by
      have hmod : L % (2 * B) < 2 * B := Nat.mod_lt L (by omega)
      have hdm : 2 * B * k + L % (2 * B) = L := Nat.div_add_mod L (2 * B)
      linarith
    have hsub_set : {n : ℕ | 0 < n ∧ n ≤ g ^ (2 * k * B) ∧ n ∈ Green95.sumsOfTwo g} ⊆ S := by
      intro n hn
      refine ⟨hn.1, ?_, hn.2.2⟩
      have hpow : (n : ℝ) ≤ (g : ℝ) ^ (2 * k * B) := by exact_mod_cast hn.2.1
      have hpow2 : (g : ℝ) ^ (2 * k * B) ≤ (g : ℝ) ^ L :=
        pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ g)) h2kB_le
      linarith
    have hcard_core := Green95LowerBound.card_sums_ge g B k hg (by omega) hk_ge
    have hcard_S : g ^ ((2 * k - 1) * B - 8 * k + 4) ≤ S.ncard :=
      hcard_core.trans (Set.ncard_le_ncard hsub_set hS_fin)
    have h19B_le_L : 19 * B ≤ L := by nlinarith
    have h8k_le : 8 * k ≤ (2 * k - 1) * B := by
      have h1 : k ≤ 2 * k - 1 := by omega
      have h2 : 8 * k ≤ k * B := by nlinarith
      exact h2.trans (Nat.mul_le_mul_right B h1)
    have hexp_ge : L - 19 * B ≤ (2 * k - 1) * B - 8 * k + 4 := by
      zify [show 1 ≤ 2 * k by omega, h19B_le_L, h8k_le]
      have : (L : ℤ) < (2 * (k : ℤ) + 2) * (B : ℤ) := by exact_mod_cast hL_lt_2k1B
      have : (k : ℤ) ≤ 2 * (B : ℤ) := by exact_mod_cast hk_le
      nlinarith
    have hcard_pow : (g : ℝ) ^ (L - 19 * B) ≤ (S.ncard : ℝ) := by
      have h1 : g ^ (L - 19 * B) ≤ g ^ ((2 * k - 1) * B - 8 * k + 4) :=
        Nat.pow_le_pow_right (by omega) hexp_ge
      exact_mod_cast h1.trans hcard_S
    have hlogx_lt : Real.log x < ((L : ℝ) + 1) * Real.log (g : ℝ) := by
      have := Real.log_lt_log hx_pos hx_lt_gL1
      simpa [Real.log_pow] using this
    have hloggL_le : (L : ℝ) * Real.log (g : ℝ) ≤ Real.log x := by
      have := Real.log_le_log (pow_pos (by exact_mod_cast (by omega : 0 < g)) L) hgL_le
      simpa [Real.log_pow] using this
    have hB_real : (B : ℝ) ≤ Real.sqrt (L : ℝ) :=
      Real.le_sqrt_of_sq_le (by exact_mod_cast (by nlinarith : B ^ 2 ≤ L))
    have hsqrt_g : Real.sqrt (Real.log (g : ℝ)) ≤ Real.log (g : ℝ) + 1 := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith
    have h_loss : (19 * (B : ℝ) + 1) * Real.log (g : ℝ) ≤ c₁ * Real.sqrt (Real.log x) := by
      have hB1 : (19 * (B : ℝ) + 1) ≤ 20 * (B : ℝ) := by
        have : (10 : ℝ) ≤ B := by exact_mod_cast hB_ge
        linarith
      have hmul1 : (19 * (B : ℝ) + 1) * Real.log (g : ℝ) ≤ 20 * Real.sqrt (L : ℝ) * Real.log (g : ℝ) := by
        calc (19 * (B : ℝ) + 1) * Real.log (g : ℝ)
            ≤ 20 * (B : ℝ) * Real.log (g : ℝ) := by nlinarith
          _ ≤ 20 * Real.sqrt (L : ℝ) * Real.log (g : ℝ) := by nlinarith
      have hsq_eq : Real.sqrt (L : ℝ) * Real.log (g : ℝ) =
          Real.sqrt ((L : ℝ) * Real.log (g : ℝ)) * Real.sqrt (Real.log (g : ℝ)) := by
        rw [Real.sqrt_mul (by positivity), mul_assoc, Real.mul_self_sqrt hlogg_pos.le]
      have hmul2 : Real.sqrt ((L : ℝ) * Real.log (g : ℝ)) ≤ Real.sqrt (Real.log x) :=
        Real.sqrt_le_sqrt hloggL_le
      have hmul3 : 20 * Real.sqrt ((L : ℝ) * Real.log (g : ℝ)) * Real.sqrt (Real.log (g : ℝ)) ≤
          20 * Real.sqrt (Real.log x) * (Real.log (g : ℝ) + 1) := by
        have : 0 ≤ Real.sqrt ((L : ℝ) * Real.log (g : ℝ)) := Real.sqrt_nonneg _
        have : 0 ≤ Real.sqrt (Real.log (g : ℝ)) := Real.sqrt_nonneg _
        nlinarith
      dsimp [c₁]
      linarith [hmul1, hsq_eq, hmul3]
    have h_exp_ineq : Real.log x * (1 - c₁ / Real.sqrt (Real.log x)) ≤
        ((L - 19 * B : ℕ) : ℝ) * Real.log (g : ℝ) := by
      have hs : Real.sqrt (Real.log x) ≠ 0 := (Real.sqrt_pos.mpr hlogx_pos).ne'
      have hlhs : Real.log x * (1 - c₁ / Real.sqrt (Real.log x)) =
          Real.log x - c₁ * Real.sqrt (Real.log x) := by
        calc Real.log x * (1 - c₁ / Real.sqrt (Real.log x))
            = Real.log x - c₁ * (Real.log x / Real.sqrt (Real.log x)) := by ring
          _ = Real.log x - c₁ * Real.sqrt (Real.log x) := by
            rw [Real.div_sqrt]
      have hrhs_cast : ((L - 19 * B : ℕ) : ℝ) = (L : ℝ) - 19 * (B : ℝ) := by
        rw [Nat.cast_sub h19B_le_L, Nat.cast_mul]
        norm_num
      rw [hlhs, hrhs_cast]
      linarith
    have hrpow_le : x ^ (1 - c₁ / Real.sqrt (Real.log x)) ≤ (g : ℝ) ^ (L - 19 * B) := by
      rw [Real.rpow_def_of_pos hx_pos, ← Real.rpow_natCast (g : ℝ) (L - 19 * B),
        Real.rpow_def_of_pos (by exact_mod_cast (by omega : 0 < g)), mul_comm (Real.log (g : ℝ))]
      exact Real.exp_le_exp.mpr h_exp_ineq
    exact hrpow_le.trans hcard_pow
