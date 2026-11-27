import FormalConjectures.ErdosProblems.«628»

-- Problem: Erdős Problem 628 — quasi line
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/628.lean:73 (declaration Erdos628.erdos_628.variants.quasi_line)
-- Credit: @divo12 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.Erdos628QL

open SimpleGraph


variable {V : Type*} [DecidableEq V] (G : SimpleGraph V)

def QL : Prop := ∀ v : V, ∃ A B : Set V, A ∪ B = G.neighborSet v ∧ G.IsClique A ∧ G.IsClique B

def Good (s T : ℕ) (S : Finset V) (f : V → ℕ) : Prop :=
  G.IsClique (S : Set V) ∧ S.card = s ∧ (∀ v, v ∉ S → f v < T) ∧
    ∀ u v, u ∉ S → v ∉ S → G.Adj u v → f u ≠ f v

def Arc (S : Finset V) (f : V → ℕ) (x y : V) : Prop :=
  G.Adj x y ∧ y ∉ S ∧ ∀ z, z ∉ S → G.Adj x z → f z = f y → z = y

def IsPath (S : Finset V) (f : V → ℕ) (p : ℕ) (g : ℕ → V) : Prop :=
  g 0 ∈ S ∧ (∀ i, i < p → Arc G S f (g i) (g (i + 1))) ∧
    ∀ i j, i ≤ p → j ≤ p → g i = g j → i = j

structure Hyp (s T : ℕ) : Prop where
  two_le : 2 ≤ s
  ql : QL G
  nocol : ∀ c : V → ℕ, (∀ v, c v < s + T - 1) → ∃ u v, G.Adj u v ∧ c u = c v
  cf : G.CliqueFree (s + T)
  ns : ∀ S : Finset V, G.IsClique (S : Set V) → S.card = s → ∃ f, Good G s T S f

def sw (S : Finset V) (x y : V) : Finset V := insert y (S.erase x)

def fw (f : V → ℕ) (x y : V) : V → ℕ := Function.update f x (f y)

variable {G} {s T : ℕ} {S : Finset V} {f : V → ℕ}

lemma mem_sw {x y v : V} : v ∈ sw S x y ↔ v = y ∨ (v ≠ x ∧ v ∈ S) := by
  simp [sw, Finset.mem_insert, Finset.mem_erase]

lemma fw_self (x y : V) : fw f x y x = f y := by simp [fw]

lemma fw_ne {x y v : V} (h : v ≠ x) : fw f x y v = f v := by
  simp [fw, Function.update_of_ne h]

lemma opp {x : V} {A B : Set V} (hAB : A ∪ B = G.neighborSet x) (hA : G.IsClique A)
    (hB : G.IsClique B) {u v : V} (hu : G.Adj x u) (hv : G.Adj x v) (hne : u ≠ v)
    (hn : ¬ G.Adj u v) : (u ∈ A ↔ v ∉ A) := by
  have hu' : u ∈ A ∪ B := by rw [hAB]; exact hu
  have hv' : v ∈ A ∪ B := by rw [hAB]; exact hv
  constructor
  · intro huA hvA; exact hn (hA huA hvA hne)
  · intro hvA
    by_contra huA
    exact hn (hB (hu'.resolve_left huA) (hv'.resolve_left hvA) hne)

lemma claw (hql : QL G) {x a b c : V} (ha : G.Adj x a) (hb : G.Adj x b) (hc : G.Adj x c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (nab : ¬ G.Adj a b) (nac : ¬ G.Adj a c)
    (nbc : ¬ G.Adj b c) : False := by
  obtain ⟨A, B, hAB, hA, hB⟩ := hql x
  have h1 := opp hAB hA hB ha hb hab nab
  have h2 := opp hAB hA hB ha hc hac nac
  have h3 := opp hAB hA hB hb hc hbc nbc
  tauto

lemma cl_adj (hg : Good G s T S f) {a b : V} (ha : a ∈ S) (hb : b ∈ S) (hne : a ≠ b) :
    G.Adj a b := hg.1 (Finset.mem_coe.2 ha) (Finset.mem_coe.2 hb) hne

lemma nadj (hg : Good G s T S f) {a b : V} (ha : a ∉ S) (hb : b ∉ S) (he : f a = f b) :
    ¬ G.Adj a b := fun e => hg.2.2.2 a b ha hb e he

lemma three (h : Hyp G s T) (hg : Good G s T S f) {x a b c : V} (ha : G.Adj x a)
    (hb : G.Adj x b) (hc : G.Adj x c) (haS : a ∉ S) (hbS : b ∉ S) (hcS : c ∉ S)
    (hfab : f a = f b) (hfac : f a = f c) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : False :=
  claw h.ql ha hb hc hab hac hbc (nadj hg haS hbS hfab) (nadj hg haS hcS hfac)
    (nadj hg hbS hcS (hfab.symm.trans hfac))

lemma nocol' (h : Hyp G s T) (c : V → ℕ) (m : ℕ) (hm : m < s + T)
    (hc : ∀ v, c v < s + T ∧ c v ≠ m) : ∃ u v, G.Adj u v ∧ c u = c v := by
  obtain ⟨u, v, huv, he⟩ := h.nocol (fun v => if c v < m then c v else c v - 1) (by
    intro v; have := hc v; split_ifs <;> omega)
  refine ⟨u, v, huv, ?_⟩
  have hu := hc u; have hv := hc v
  split_ifs at he <;> omega

noncomputable def idx (S : Finset V) (u : V) : ℕ :=
  if h : u ∈ S then ((S.equivFin ⟨u, h⟩ : Fin S.card) : ℕ) else 0

lemma idx_lt {u : V} (hu : u ∈ S) : idx S u < S.card := by
  rw [idx, dif_pos hu]; exact Fin.isLt _

lemma idx_inj {u v : V} (hu : u ∈ S) (hv : v ∈ S) (h : idx S u = idx S v) : u = v := by
  rw [idx, idx, dif_pos hu, dif_pos hv] at h
  have := S.equivFin.injective (Fin.ext h)
  simpa using congrArg Subtype.val this

/-- Lemma 2.5. -/
lemma l25 (h : Hyp G s T) (hg : Good G s T S f) {c : ℕ} (hc : c < T) :
    ∃ z, z ∉ S ∧ f z = c ∧ ∀ u ∈ S, G.Adj u z := by
  classical
  by_contra hne
  push Not at hne
  have hw : ∀ z, ∃ u, z ∉ S → f z = c → u ∈ S ∧ ¬ G.Adj u z := by
    intro z
    by_cases hz : z ∉ S ∧ f z = c
    · obtain ⟨u, hu, hn⟩ := hne z hz.1 hz.2
      exact ⟨u, fun _ _ => ⟨hu, hn⟩⟩
    · exact ⟨z, fun h1 h2 => absurd ⟨h1, h2⟩ hz⟩
  choose w hw using hw
  obtain ⟨hcl, hcard, hlt, hpr⟩ := hg
  let col : V → ℕ := fun v =>
    if v ∈ S then idx S v else if f v = c then idx S (w v) else s + f v
  have c1 : ∀ a, a ∈ S → col a = idx S a := fun a ha => by simp [col, ha]
  have c2 : ∀ a, a ∉ S → f a = c → col a = idx S (w a) := fun a ha hf => by simp [col, ha, hf]
  have c3 : ∀ a, a ∉ S → f a ≠ c → col a = s + f a := fun a ha hf => by simp [col, ha, hf]
  obtain ⟨u, v, huv, heq⟩ := nocol' h col (s + c) (by omega) (by
    intro a
    by_cases ha : a ∈ S
    · rw [c1 a ha]; have := idx_lt ha; omega
    · by_cases hf : f a = c
      · rw [c2 a ha hf]; have := idx_lt (hw a ha hf).1; omega
      · rw [c3 a ha hf]; have := hlt a ha; omega)
  have key : ∀ a b, G.Adj a b → a ∈ S → col a = col b → False := by
    intro a b hab ha he
    rw [c1 a ha] at he
    by_cases hb : b ∈ S
    · rw [c1 b hb] at he
      rw [idx_inj ha hb he] at hab; exact G.irrefl hab
    · by_cases hf : f b = c
      · rw [c2 b hb hf] at he
        have := idx_inj ha (hw b hb hf).1 he
        exact (hw b hb hf).2 (this ▸ hab)
      · rw [c3 b hb hf] at he; have := idx_lt ha; omega
  by_cases hu : u ∈ S
  · exact key u v huv hu heq
  by_cases hv : v ∈ S
  · exact key v u huv.symm hv heq.symm
  by_cases hfu : f u = c <;> by_cases hfv : f v = c
  · exact hpr u v hu hv huv (hfu.trans hfv.symm)
  · rw [c2 u hu hfu, c3 v hv hfv] at heq; have := idx_lt (hw u hu hfu).1; omega
  · rw [c3 u hu hfu, c2 v hv hfv] at heq; have := idx_lt (hw v hv hfv).1; omega
  · rw [c3 u hu hfu, c3 v hv hfv] at heq
    exact hpr u v hu hv huv (by omega)

/-- Lemma 3.2. -/
lemma l32 (h : Hyp G s T) (hg : Good G s T S f) {x y : V} (hx : x ∈ S)
    (hxy : Arc G S f x y) :
    (∀ u ∈ S, G.Adj u y) ∧ Good G s T (sw S x y) (fw f x y) := by
  obtain ⟨z, hzS, hfz, hzc⟩ := l25 h hg (hg.2.2.1 y hxy.2.1)
  have hzy : z = y := hxy.2.2 z hzS (hzc x hx) hfz
  have hyc : ∀ u ∈ S, G.Adj u y := fun u hu => hzy ▸ hzc u hu
  obtain ⟨hcl, hcard, hlt, hpr⟩ := hg
  refine ⟨hyc, ?_, ?_, ?_, ?_⟩
  · have hc' : G.IsClique ((S.erase x : Finset V) : Set V) :=
      hcl.subset (fun a ha => Finset.mem_coe.2 (Finset.mem_of_mem_erase (Finset.mem_coe.1 ha)))
    rw [sw, Finset.coe_insert]
    exact hc'.insert (fun b hb _ => (hyc b (Finset.mem_of_mem_erase hb)).symm)
  · rw [sw, Finset.card_insert_of_notMem (by simp [hxy.2.1]), Finset.card_erase_of_mem hx]
    have := Finset.card_pos.mpr ⟨x, hx⟩
    omega
  · intro v hv
    rw [mem_sw] at hv
    push Not at hv
    by_cases hvx : v = x
    · rw [hvx, fw_self]; exact hlt y hxy.2.1
    · rw [fw_ne hvx]; exact hlt v (hv.2 hvx)
  · intro a b ha hb hab
    rw [mem_sw] at ha hb
    push Not at ha hb
    by_cases hax : a = x
    · have hbx : b ≠ x := fun e => G.irrefl (by rw [hax, e] at hab; exact hab)
      rw [hax, fw_self, fw_ne hbx]
      intro e
      exact hb.1 (hxy.2.2 b (hb.2 hbx) (hax ▸ hab) e.symm)
    · by_cases hbx : b = x
      · rw [hbx, fw_self, fw_ne hax]
        intro e
        exact ha.1 (hxy.2.2 a (ha.2 hax) (hbx ▸ hab.symm) e)
      · rw [fw_ne hax, fw_ne hbx]
        exact hpr a b (ha.2 hax) (hb.2 hbx) hab

/-- Observation 3.4 (in the form used). -/
lemma arc_swap (hg : Good G s T S f) {x y : V} (hx : x ∈ S) (hxy : Arc G S f x y) {z u : V}
    (hzu : Arc G S f z u) (huy : u ≠ y) (hz : z = y ∨ G.Adj z y ∨ ¬ G.Adj z x) :
    Arc G (sw S x y) (fw f x y) z u := by
  obtain ⟨hadj, huS, huniq⟩ := hzu
  have hux : u ≠ x := fun e => huS (e ▸ hx)
  refine ⟨hadj, ?_, ?_⟩
  · rw [mem_sw]; rintro (e | ⟨-, e⟩)
    · exact huy e
    · exact huS e
  · intro w hw hzw hfw
    rw [mem_sw] at hw
    push Not at hw
    rw [fw_ne hux] at hfw
    by_cases hwx : w = x
    · rw [hwx, fw_self] at hfw
      rw [hwx] at hzw
      exfalso
      rcases hz with e | hzy | hzx
      · rw [e] at hadj; exact hg.2.2.2 _ _ hxy.2.1 huS hadj hfw
      · exact huy (huniq y hxy.2.1 hzy hfw).symm
      · exact hzx hzw
    · rw [fw_ne hwx] at hfw
      exact huniq w (hw.2 hwx) hzw hfw

lemma path_notin {p : ℕ} {g : ℕ → V} (hP : IsPath G S f p g) {i : ℕ} (hi : 1 ≤ i) (hip : i ≤ p) :
    g i ∉ S := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  exact (hP.2.1 j (by omega)).2.1

lemma tail' (hg : Good G s T S f) {p : ℕ} {g : ℕ → V} (hP : IsPath G S f p g) (hp : 1 ≤ p)
    {x : V} (hx : x ∈ S) (hx1 : Arc G S f x (g 1))
    (hadj : ∀ i, 2 ≤ i → i < p → G.Adj (g i) (g 1)) :
    IsPath G (sw S x (g 1)) (fw f x (g 1)) (p - 1) (fun i => g (i + 1)) := by
  obtain ⟨h0, harc, hinj⟩ := hP
  refine ⟨?_, ?_, ?_⟩
  · simp [mem_sw]
  · intro i hi
    show Arc G _ _ (g (i + 1)) (g (i + 1 + 1))
    apply arc_swap hg hx hx1 (harc (i + 1) (by omega))
    · intro e; have := hinj (i + 1 + 1) 1 (by omega) (by omega) e; omega
    · rcases Nat.eq_zero_or_pos i with rfl | hi0
      · left; rfl
      · right; left; exact hadj (i + 1) (by omega) (by omega)
  · intro i j hi hj e; have := hinj (i + 1) (j + 1) (by omega) (by omega) e; omega

lemma tail (hg : Good G s T S f) {p : ℕ} {g : ℕ → V} (hP : IsPath G S f p g) (hp : 1 ≤ p)
    (hadj : ∀ i, 2 ≤ i → i < p → G.Adj (g i) (g 1)) :
    IsPath G (sw S (g 0) (g 1)) (fw f (g 0) (g 1)) (p - 1) (fun i => g (i + 1)) :=
  tail' hg hP hp hP.1 (hP.2.1 0 (by omega)) hadj

lemma path_le {p q : ℕ} {g : ℕ → V} (hP : IsPath G S f p g) (hq : q ≤ p) : IsPath G S f q g :=
  ⟨hP.1, fun i hi => hP.2.1 i (by omega), fun i j hi hj e => hP.2.2 i j (by omega) (by omega) e⟩

lemma jump {p : ℕ} {g : ℕ → V} (hP : IsPath G S f p g) {x : V} (hx : x ∈ S) {j : ℕ}
    (hj1 : 1 ≤ j) (hjp : j ≤ p) (harc : Arc G S f x (g j)) :
    IsPath G S f (p - j + 1) (fun i => if i = 0 then x else g (i + j - 1)) := by
  refine ⟨by simp [hx], ?_, ?_⟩
  · intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · show Arc G S f (if 0 = 0 then x else g (0 + j - 1)) (if 0 + 1 = 0 then x else g (0 + 1 + j - 1))
      rw [if_pos rfl, if_neg (by omega), show 0 + 1 + j - 1 = j by omega]; exact harc
    · show Arc G S f (if i = 0 then x else g (i + j - 1)) (if i + 1 = 0 then x else g (i + 1 + j - 1))
      rw [if_neg (by omega), if_neg (by omega), show i + 1 + j - 1 = i + j - 1 + 1 by omega]
      exact hP.2.1 _ (by omega)
  · intro i i' hi hi' e
    have e' : (if i = 0 then x else g (i + j - 1)) = (if i' = 0 then x else g (i' + j - 1)) := e
    by_cases h0 : i = 0 <;> by_cases h0' : i' = 0
    · omega
    · rw [if_pos h0, if_neg h0'] at e'
      exact absurd (e' ▸ hx) (path_notin hP (by omega) (by omega))
    · rw [if_neg h0, if_pos h0'] at e'
      exact absurd (e'.symm ▸ hx) (path_notin hP (by omega) (by omega))
    · rw [if_neg h0, if_neg h0'] at e'
      have := hP.2.2 _ _ (by omega) (by omega) e'
      omega

variable (G) in
def PC (S : Finset V) (p : ℕ) (g : ℕ → V) : Prop :=
  (∀ i ≤ p, ∀ u ∈ S, u ≠ g i → G.Adj u (g i)) ∧ ∀ i ≤ p, ∀ j ≤ p, i ≠ j → G.Adj (g i) (g j)

variable (G) in
def Sep (x : V) (A : Set V) : Prop :=
  ∀ u v, G.Adj x u → G.Adj x v → u ≠ v → ¬ G.Adj u v → (u ∈ A ↔ v ∉ A)

lemma sep_exists (hql : QL G) (x : V) : ∃ A, Sep G x A := by
  obtain ⟨A, B, hAB, hA, hB⟩ := hql x
  exact ⟨A, fun u v hu hv hne hn => opp hAB hA hB hu hv hne hn⟩

lemma alt {x : V} {A : Set V} (hA : Sep G x A) (a b : ℕ → V) (n : ℕ)
    (ha : ∀ j ≤ n, G.Adj x (a j)) (hb : ∀ j, 1 ≤ j → j ≤ n → G.Adj x (b j))
    (h1 : ∀ j, 1 ≤ j → j ≤ n → a (j - 1) ≠ b j ∧ ¬ G.Adj (a (j - 1)) (b j))
    (h2 : ∀ j, 1 ≤ j → j ≤ n → b j ≠ a j ∧ ¬ G.Adj (b j) (a j)) :
    ∀ j ≤ n, (a j ∈ A ↔ a 0 ∈ A) := by
  intro j
  induction j with
  | zero => intro _; exact Iff.rfl
  | succ j ih =>
    intro hj
    have k1 := h1 (j + 1) (by omega) hj
    have k2 := h2 (j + 1) (by omega) hj
    simp only [Nat.add_sub_cancel] at k1
    have e1 := hA _ _ (ha j (by omega)) (hb (j + 1) (by omega) hj) k1.1 k1.2
    have e2 := hA _ _ (hb (j + 1) (by omega) hj) (ha (j + 1) hj) k2.1 k2.2
    have e3 := ih (by omega)
    tauto

lemma seqk1 (hg : Good G s T S f) {p : ℕ} {g : ℕ → V} (hP : IsPath G S f p g) {Y : ℕ → V}
    (hY : ∀ j, 1 ≤ j → j ≤ p → Y j ∉ S ∧ f (Y j) = f (g j) ∧ Y j ≠ g j) :
    ∀ j, 1 ≤ j → j ≤ p → g (j - 1) ≠ Y j ∧ ¬ G.Adj (g (j - 1)) (Y j) := by
  intro j h1 h2
  obtain ⟨hYS, hYf, hYne⟩ := hY j h1 h2
  have harcj : Arc G S f (g (j - 1)) (g j) := by
    have := hP.2.1 (j - 1) (by omega); rwa [show j - 1 + 1 = j by omega] at this
  refine ⟨fun e => ?_, fun e => hYne (harcj.2.2 _ hYS e hYf)⟩
  rcases Nat.eq_zero_or_pos (j - 1) with h0 | h0
  · rw [h0] at e; exact hYS (e ▸ hP.1)
  · exact hg.2.2.2 _ _ (path_notin hP h0 (by omega)) (path_notin hP h1 h2) harcj.1
      (by rw [e, hYf])

lemma seqk2 (hg : Good G s T S f) {p : ℕ} {g : ℕ → V} (hP : IsPath G S f p g) {Y : ℕ → V}
    (hY : ∀ j, 1 ≤ j → j ≤ p → Y j ∉ S ∧ f (Y j) = f (g j) ∧ Y j ≠ g j) :
    ∀ j, 1 ≤ j → j ≤ p → Y j ≠ g j ∧ ¬ G.Adj (Y j) (g j) := fun j h1 h2 =>
  ⟨(hY j h1 h2).2.2, nadj hg (hY j h1 h2).1 (path_notin hP h1 h2) (hY j h1 h2).2.1⟩

/-- The case `s = 2` of Lemma 3.3: a 3-colouring of `S ∪ C_c ∪ C_ℓ`. -/
lemma s2col (h : Hyp G s T) (hg : Good G s T S f) {x x' y u v w : V} {c : ℕ}
    (hx : x ∈ S) (hx' : x' ∈ S) (hxx' : x ≠ x') (hS2 : ∀ a ∈ S, a = x ∨ a = x')
    (hxy : Arc G S f x y) (hx'y : Arc G S f x' y)
    (huS : u ∉ S) (hvS : v ∉ S) (hwS : w ∉ S)
    (hfu : f u = c) (hfv : f v = c) (hfw : f w = c) (hc : c < T) (hcy : c ≠ f y)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (axw : G.Adj x w) (axu : G.Adj x u) (ax'w : G.Adj x' w) (ax'v : G.Adj x' v)
    (ayv : G.Adj y v) (ayu : G.Adj y u)
    (nyw : ¬ G.Adj y w) (nxv : ¬ G.Adj x v) (nx'u : ¬ G.Adj x' u) : False := by
  classical
  have hyS : y ∉ S := hxy.2.1
  have hlt := hg.2.2.1
  have hyT : f y < T := hlt y hyS
  have d_xu : x ≠ u := fun e => huS (e ▸ hx)
  have d_xv : x ≠ v := fun e => hvS (e ▸ hx)
  have d_xw : x ≠ w := fun e => hwS (e ▸ hx)
  have d_xy : x ≠ y := fun e => hyS (e ▸ hx)
  have d_x'u : x' ≠ u := fun e => huS (e ▸ hx')
  have d_x'v : x' ≠ v := fun e => hvS (e ▸ hx')
  have d_x'w : x' ≠ w := fun e => hwS (e ▸ hx')
  have d_x'y : x' ≠ y := fun e => hyS (e ▸ hx')
  have d_yu : y ≠ u := fun e => hcy (by rw [← hfu, ← e])
  have d_yv : y ≠ v := fun e => hcy (by rw [← hfv, ← e])
  have d_yw : y ≠ w := fun e => hcy (by rw [← hfw, ← e])
  let Yk : V → Prop := fun n => n ∉ S ∧ f n = f y ∧ n ≠ y
  let Zk : V → Prop := fun n => n ∉ S ∧ f n = c ∧ n ≠ u ∧ n ≠ v ∧ n ≠ w
  let Rk : V → Prop := fun n => n ∉ S ∧ f n ≠ c ∧ f n ≠ f y
  let hY : V → ℕ := fun a => if ¬ G.Adj a u then c else if ¬ G.Adj a v then f y else T
  let hZ : V → ℕ := fun a =>
    if (∀ n, Yk n → G.Adj a n → hY n ≠ c) then c
    else if (∀ n, Yk n → G.Adj a n → hY n ≠ f y) then f y else T
  let col : V → ℕ := fun a =>
    if a = x' ∨ a = u then c else if a = x ∨ a = v then f y
    else if a = w ∨ a = y then T else if f a = f y then hY a else if f a = c then hZ a else f a
  have e_x' : col x' = c := by simp [col]
  have e_u : col u = c := by simp [col]
  have e_x : col x = f y := by simp [col, hxx', d_xu]
  have e_v : col v = f y := by simp [col, d_x'v.symm, huv.symm]
  have e_w : col w = T := by simp [col, d_x'w.symm, huw.symm, d_xw.symm, hvw.symm]
  have e_y : col y = T := by simp [col, d_x'y.symm, d_yu, d_xy.symm, d_yv]
  have e_Y : ∀ a, Yk a → col a = hY a := by
    rintro a ⟨haS, haf, hay⟩
    have h1 : a ≠ x' := fun e => haS (e ▸ hx')
    have h2 : a ≠ x := fun e => haS (e ▸ hx)
    have h3 : a ≠ u := fun e => hcy (by rw [← hfu, ← e, haf])
    have h4 : a ≠ v := fun e => hcy (by rw [← hfv, ← e, haf])
    have h5 : a ≠ w := fun e => hcy (by rw [← hfw, ← e, haf])
    simp only [col]
    rw [if_neg (by rintro (e|e) <;> contradiction), if_neg (by rintro (e|e) <;> contradiction),
      if_neg (by rintro (e|e) <;> contradiction), if_pos haf]
  have e_Z : ∀ a, Zk a → col a = hZ a := by
    rintro a ⟨haS, haf, h3, h4, h5⟩
    have h1 : a ≠ x' := fun e => haS (e ▸ hx')
    have h2 : a ≠ x := fun e => haS (e ▸ hx)
    have h6 : a ≠ y := fun e => hcy (by rw [← haf, e])
    have h7 : f a ≠ f y := by rw [haf]; exact hcy
    simp only [col]
    rw [if_neg (by rintro (e|e) <;> contradiction), if_neg (by rintro (e|e) <;> contradiction),
      if_neg (by rintro (e|e) <;> contradiction), if_neg h7, if_pos haf]
  have e_R : ∀ a, Rk a → col a = f a := by
    rintro a ⟨haS, h7, h8⟩
    have h1 : a ≠ x' := fun e => haS (e ▸ hx')
    have h2 : a ≠ x := fun e => haS (e ▸ hx)
    have h3 : a ≠ u := fun e => h7 (by rw [e, hfu])
    have h4 : a ≠ v := fun e => h7 (by rw [e, hfv])
    have h5 : a ≠ w := fun e => h7 (by rw [e, hfw])
    have h6 : a ≠ y := fun e => h8 (by rw [e])
    simp [col, h1, h2, h3, h4, h5, h6, h7, h8]
  have vY : ∀ a, hY a = c ∨ hY a = f y ∨ hY a = T := by
    intro a; simp only [hY]; split_ifs <;> simp
  have vZ : ∀ a, hZ a = c ∨ hZ a = f y ∨ hZ a = T := by
    intro a; simp only [hZ]; split_ifs <;> simp
  have cls : ∀ b, b = x ∨ b = x' ∨ b = y ∨ b = u ∨ b = v ∨ b = w ∨ Yk b ∨ Zk b ∨ Rk b := by
    intro b
    by_cases hb : b ∈ S
    · rcases hS2 b hb with e | e
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
    by_cases hby : b = y
    · exact Or.inr (Or.inr (Or.inl hby))
    by_cases hbf : f b = f y
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hb, hbf, hby⟩))))))
    by_cases hbc : f b = c
    · by_cases hbu : b = u
      · exact Or.inr (Or.inr (Or.inr (Or.inl hbu)))
      by_cases hbv : b = v
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hbv))))
      by_cases hbw : b = w
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hbw)))))
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨hb, hbc, hbu, hbv, hbw⟩)))))))
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hb, hbc, hbf⟩)))))))
  have hZp : ∀ z n, Yk n → G.Adj z n → hY n ≠ hZ z := by
    intro z n hn hzn
    simp only [hZ]
    split_ifs with h1 h2
    · exact h1 n hn hzn
    · exact h2 n hn hzn
    · push Not at h1 h2
      obtain ⟨n1, hn1, hz1, e1⟩ := h1
      obtain ⟨n2, hn2, hz2, e2⟩ := h2
      intro e3
      have d12 : n1 ≠ n2 := fun e => hcy (by rw [← e1, ← e2, e])
      have d13 : n1 ≠ n := fun e => by rw [e, e3] at e1; omega
      have d23 : n2 ≠ n := fun e => by rw [e, e3] at e2; omega
      exact three h hg hz1 hz2 hzn hn1.1 hn2.1 hn.1 (hn1.2.1.trans hn2.2.1.symm)
        (hn1.2.1.trans hn.2.1.symm) d12 d13 d23
  have Px : ∀ b, G.Adj x b → col x ≠ col b := by
    intro b hb
    rw [e_x]
    rcases cls b with h1|h1|h1|h1|h1|h1|h1|h1|h1
    · rw [h1] at hb; exact absurd hb (G.irrefl)
    · rw [h1, e_x']; exact hcy.symm
    · rw [h1, e_y]; omega
    · rw [h1, e_u]; exact hcy.symm
    · rw [h1] at hb; exact absurd hb nxv
    · rw [h1, e_w]; omega
    · exact absurd (hxy.2.2 b h1.1 hb h1.2.1) h1.2.2
    · exact (three h hg axw axu hb hwS huS h1.1 (hfw.trans hfu.symm) (hfw.trans h1.2.1.symm)
        huw.symm (Ne.symm h1.2.2.2.2) (Ne.symm h1.2.2.1)).elim
    · rw [e_R b h1]; exact Ne.symm h1.2.2
  have Px' : ∀ b, G.Adj x' b → col x' ≠ col b := by
    intro b hb
    rw [e_x']
    rcases cls b with h1|h1|h1|h1|h1|h1|h1|h1|h1
    · rw [h1, e_x]; exact hcy
    · rw [h1] at hb; exact absurd hb (G.irrefl)
    · rw [h1, e_y]; omega
    · rw [h1] at hb; exact absurd hb nx'u
    · rw [h1, e_v]; exact hcy
    · rw [h1, e_w]; omega
    · exact absurd (hx'y.2.2 b h1.1 hb h1.2.1) h1.2.2
    · exact (three h hg ax'w ax'v hb hwS hvS h1.1 (hfw.trans hfv.symm) (hfw.trans h1.2.1.symm)
        hvw.symm (Ne.symm h1.2.2.2.2) (Ne.symm h1.2.2.2.1)).elim
    · rw [e_R b h1]; exact Ne.symm h1.2.1
  have Py : ∀ b, G.Adj y b → col y ≠ col b := by
    intro b hb
    rw [e_y]
    rcases cls b with h1|h1|h1|h1|h1|h1|h1|h1|h1
    · rw [h1, e_x]; omega
    · rw [h1, e_x']; omega
    · rw [h1] at hb; exact absurd hb (G.irrefl)
    · rw [h1, e_u]; omega
    · rw [h1, e_v]; omega
    · rw [h1] at hb; exact absurd hb nyw
    · exact absurd hb (nadj hg hyS h1.1 h1.2.1.symm)
    · exact (three h hg ayu ayv hb huS hvS h1.1 (hfu.trans hfv.symm) (hfu.trans h1.2.1.symm)
        huv (Ne.symm h1.2.2.1) (Ne.symm h1.2.2.2.1)).elim
    · rw [e_R b h1]; have := hlt b h1.1; omega
  have Pu : ∀ b, G.Adj u b → col u ≠ col b := by
    intro b hb
    rw [e_u]
    rcases cls b with h1|h1|h1|h1|h1|h1|h1|h1|h1
    · rw [h1, e_x]; exact hcy
    · rw [h1] at hb; exact absurd hb.symm nx'u
    · rw [h1, e_y]; omega
    · rw [h1] at hb; exact absurd hb (G.irrefl)
    · rw [h1] at hb; exact absurd hb (nadj hg huS hvS (hfu.trans hfv.symm))
    · rw [h1] at hb; exact absurd hb (nadj hg huS hwS (hfu.trans hfw.symm))
    · rw [e_Y b h1]
      have hbu : ¬ ¬ G.Adj b u := not_not.2 hb.symm
      simp only [hY, if_neg hbu]
      split_ifs <;> omega
    · exact absurd hb (nadj hg huS h1.1 (hfu.trans h1.2.1.symm))
    · rw [e_R b h1]; exact Ne.symm h1.2.1
  have Pv : ∀ b, G.Adj v b → col v ≠ col b := by
    intro b hb
    rw [e_v]
    rcases cls b with h1|h1|h1|h1|h1|h1|h1|h1|h1
    · rw [h1] at hb; exact absurd hb.symm nxv
    · rw [h1, e_x']; exact hcy.symm
    · rw [h1, e_y]; omega
    · rw [h1] at hb; exact absurd hb (nadj hg hvS huS (hfv.trans hfu.symm))
    · rw [h1] at hb; exact absurd hb (G.irrefl)
    · rw [h1] at hb; exact absurd hb (nadj hg hvS hwS (hfv.trans hfw.symm))
    · rw [e_Y b h1]
      have hbv : ¬ ¬ G.Adj b v := not_not.2 hb.symm
      simp only [hY, if_neg hbv]
      split_ifs <;> omega
    · exact absurd hb (nadj hg hvS h1.1 (hfv.trans h1.2.1.symm))
    · rw [e_R b h1]; exact Ne.symm h1.2.2
  have Pw : ∀ b, G.Adj w b → col w ≠ col b := by
    intro b hb
    rw [e_w]
    rcases cls b with h1|h1|h1|h1|h1|h1|h1|h1|h1
    · rw [h1, e_x]; omega
    · rw [h1, e_x']; omega
    · rw [h1] at hb; exact absurd hb.symm nyw
    · rw [h1] at hb; exact absurd hb (nadj hg hwS huS (hfw.trans hfu.symm))
    · rw [h1] at hb; exact absurd hb (nadj hg hwS hvS (hfw.trans hfv.symm))
    · rw [h1] at hb; exact absurd hb (G.irrefl)
    · rw [e_Y b h1]
      by_cases q1 : G.Adj b u
      · by_cases q2 : G.Adj b v
        · exact fun _ => three h hg q1 q2 hb.symm huS hvS hwS (hfu.trans hfv.symm)
            (hfu.trans hfw.symm) huv huw hvw
        · simp only [hY, q1, q2, not_true_eq_false, not_false_eq_true, if_true, if_false]; omega
      · simp only [hY, q1, not_false_eq_true, if_true]; omega
    · exact absurd hb (nadj hg hwS h1.1 (hfw.trans h1.2.1.symm))
    · rw [e_R b h1]; have := hlt b h1.1; omega
  have Pcore : ∀ a b, G.Adj a b → (b = x ∨ b = x' ∨ b = y ∨ b = u ∨ b = v ∨ b = w) →
      col a ≠ col b := by
    intro a b hab hb
    rcases hb with e|e|e|e|e|e <;> rw [e] at hab ⊢
    · exact fun q => Px a hab.symm q.symm
    · exact fun q => Px' a hab.symm q.symm
    · exact fun q => Py a hab.symm q.symm
    · exact fun q => Pu a hab.symm q.symm
    · exact fun q => Pv a hab.symm q.symm
    · exact fun q => Pw a hab.symm q.symm
  have P : ∀ a b, G.Adj a b → col a ≠ col b := by
    intro a b hab
    rcases cls a with h1|h1|h1|h1|h1|h1|h1|h1|h1
    · rw [h1] at hab ⊢; exact Px b hab
    · rw [h1] at hab ⊢; exact Px' b hab
    · rw [h1] at hab ⊢; exact Py b hab
    · rw [h1] at hab ⊢; exact Pu b hab
    · rw [h1] at hab ⊢; exact Pv b hab
    · rw [h1] at hab ⊢; exact Pw b hab
    all_goals rcases cls b with h2|h2|h2|h2|h2|h2|h2|h2|h2
    all_goals first
      | exact Pcore a b hab (Or.inl h2)
      | exact Pcore a b hab (Or.inr (Or.inl h2))
      | exact Pcore a b hab (Or.inr (Or.inr (Or.inl h2)))
      | exact Pcore a b hab (Or.inr (Or.inr (Or.inr (Or.inl h2))))
      | exact Pcore a b hab (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h2)))))
      | exact Pcore a b hab (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h2)))))
      | skip
    · exact absurd hab (nadj hg h1.1 h2.1 (h1.2.1.trans h2.2.1.symm))
    · rw [e_Y a h1, e_Z b h2]; exact hZp b a h1 hab.symm
    · rw [e_Y a h1, e_R b h2]; have := vY a; have := h2.2.1; have := h2.2.2
      have := hlt b h2.1; omega
    · rw [e_Z a h1, e_Y b h2]; exact fun q => hZp a b h2 hab q.symm
    · exact absurd hab (nadj hg h1.1 h2.1 (h1.2.1.trans h2.2.1.symm))
    · rw [e_Z a h1, e_R b h2]; have := vZ a; have := h2.2.1; have := h2.2.2
      have := hlt b h2.1; omega
    · rw [e_R a h1, e_Y b h2]; have := vY b; have := h1.2.1; have := h1.2.2
      have := hlt a h1.1; omega
    · rw [e_R a h1, e_Z b h2]; have := vZ b; have := h1.2.1; have := h1.2.2
      have := hlt a h1.1; omega
    · rw [e_R a h1, e_R b h2]; exact hg.2.2.2 a b h1.1 h2.1 hab
  have two := h.two_le
  obtain ⟨a, b, hab, he⟩ := h.nocol col (by
    intro a
    rcases cls a with h1|h1|h1|h1|h1|h1|h1|h1|h1
    · rw [h1, e_x]; omega
    · rw [h1, e_x']; omega
    · rw [h1, e_y]; omega
    · rw [h1, e_u]; omega
    · rw [h1, e_v]; omega
    · rw [h1, e_w]; omega
    · rw [e_Y a h1]; have := vY a; omega
    · rw [e_Z a h1]; have := vZ a; omega
    · rw [e_R a h1]; have := hlt a h1.1; omega)
  exact P a b hab he

/-- Lemma 3.3. -/
lemma l33 (h : Hyp G s T) (hg : Good G s T S f) {x y : V} (hx : x ∈ S) (hxy : Arc G S f x y)
    {c : ℕ} (hc : c < T) (hcy : c ≠ f y) :
    ∃ z, z ∉ S ∧ f z = c ∧ (∀ u ∈ S, G.Adj u z) ∧ G.Adj y z := by
  by_contra H
  push Not at H
  obtain ⟨hyc, hg'⟩ := l32 h hg hx hxy
  have hyS := hxy.2.1
  obtain ⟨w, hwS, hfw, hwc⟩ := l25 h hg hc
  have nyw : ¬ G.Adj y w := H w hwS hfw hwc
  obtain ⟨v, hvS', hfv', hvc'⟩ := l25 h hg' hc
  have hvx : v ≠ x := by
    intro e; rw [e, fw_self] at hfv'; exact hcy hfv'.symm
  rw [fw_ne hvx] at hfv'
  have hvS : v ∉ S := fun e => hvS' (mem_sw.2 (Or.inr ⟨hvx, e⟩))
  have ayv : G.Adj y v := hvc' y (mem_sw.2 (Or.inl rfl))
  have hvc : ∀ a ∈ S, a ≠ x → G.Adj a v := fun a ha hax =>
    hvc' a (mem_sw.2 (Or.inr ⟨hax, ha⟩))
  have nxv : ¬ G.Adj x v := by
    intro e
    exact H v hvS hfv' (fun a ha => if hax : a = x then hax ▸ e else hvc a ha hax) ayv
  have hvw : v ≠ w := fun e => nxv (e ▸ hwc x hx)
  obtain ⟨x', hx', hx'x⟩ := Finset.exists_mem_ne
    (by rw [hg.2.1]; have := h.two_le; omega : 1 < S.card) x
  have hyw : y ≠ w := fun e => hcy (by rw [← hfw, e])
  have harc' : Arc G S f x' y := by
    refine ⟨hyc x' hx', hyS, ?_⟩
    intro y' hy'S hx'y' hfy'
    by_contra hne
    have nxy' : ¬ G.Adj x y' := fun e => hne (hxy.2.2 y' hy'S e hfy')
    have ny'y : ¬ G.Adj y' y := nadj hg hy'S hyS hfy'
    have hxy'ne : x ≠ y' := fun e => hy'S (e ▸ hx)
    obtain ⟨A, B, hAB, hA, hB⟩ := h.ql x'
    have ax'x : G.Adj x' x := cl_adj hg hx' hx hx'x
    have e1 := opp hAB hA hB ax'x hx'y' hxy'ne nxy'
    have e2 := opp hAB hA hB hx'y' (hyc x' hx') hne ny'y
    have e3 := opp hAB hA hB (hyc x' hx') (hwc x' hx') hyw nyw
    have e4 := opp hAB hA hB (hwc x' hx') (hvc x' hx' hx'x) hvw.symm
      (nadj hg hwS hvS (hfw.trans hfv'.symm))
    have e5 := opp hAB hA hB (hvc x' hx' hx'x) ax'x (fun e => hvS (e ▸ hx)) (fun e => nxv e.symm)
    tauto
  obtain ⟨-, hg''⟩ := l32 h hg hx' harc'
  obtain ⟨u, huS', hfu', huc'⟩ := l25 h hg'' hc
  have hux' : u ≠ x' := by
    intro e; rw [e, fw_self] at hfu'; exact hcy hfu'.symm
  rw [fw_ne hux'] at hfu'
  have huS : u ∉ S := fun e => huS' (mem_sw.2 (Or.inr ⟨hux', e⟩))
  have ayu : G.Adj y u := huc' y (mem_sw.2 (Or.inl rfl))
  have huc : ∀ a ∈ S, a ≠ x' → G.Adj a u := fun a ha hax =>
    huc' a (mem_sw.2 (Or.inr ⟨hax, ha⟩))
  have nx'u : ¬ G.Adj x' u := by
    intro e
    exact H u huS hfu' (fun a ha => if hax : a = x' then hax ▸ e else huc a ha hax) ayu
  have huw : u ≠ w := fun e => nyw (e ▸ ayu)
  have huv : u ≠ v := fun e => nxv (e ▸ huc x hx (Ne.symm hx'x))
  by_cases h3 : ∃ x'' ∈ S, x'' ≠ x ∧ x'' ≠ x'
  · obtain ⟨x'', hx'', h1, h2⟩ := h3
    exact three h hg (huc x'' hx'' h2) (hvc x'' hx'' h1) (hwc x'' hx'') huS hvS hwS
      (hfu'.trans hfv'.symm) (hfu'.trans hfw.symm) huv huw hvw
  · push Not at h3
    have hS2 : ∀ a ∈ S, a = x ∨ a = x' := fun a ha =>
      if hax : a = x then Or.inl hax else Or.inr (h3 a ha hax)
    exact s2col h hg hx hx' (Ne.symm hx'x) hS2 hxy harc' huS hvS hwS hfu' hfv' hfw hc hcy
      huv huw hvw (hwc x hx) (huc x hx (Ne.symm hx'x)) (hwc x' hx') (hvc x' hx' hx'x)
      ayv ayu nyw nxv nx'u

/-- Lemma 3.5. -/
lemma l35 (h : Hyp G s T) : ∀ p (S : Finset V) (f : V → ℕ) (g : ℕ → V),
    Good G s T S f → IsPath G S f p g → PC G S p g := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p IH =>
  intro S f g hg hP
  have hnS : ∀ i, 1 ≤ i → i ≤ p → g i ∉ S := fun i h1 h2 => path_notin hP h1 h2
  rcases Nat.lt_or_ge p 1 with hp | hp
  · refine ⟨fun i hi u hu hne => ?_, fun i hi j hj hij => by omega⟩
    have : i = 0 := by omega
    subst this
    exact cl_adj hg hu hP.1 hne
  have hpre : PC G S (p - 1) g := IH (p - 1) (by omega) S f g hg (path_le hP (by omega))
  have harc0 : Arc G S f (g 0) (g 1) := hP.2.1 0 (by omega)
  obtain ⟨hyc, hg'⟩ := l32 h hg hP.1 harc0
  rcases Nat.lt_or_ge p 2 with hp2 | hp2
  · have hp1 : p = 1 := by omega
    subst hp1
    refine ⟨fun i hi u hu hne => ?_, fun i hi j hj hij => ?_⟩
    · rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
      · exact cl_adj hg hu hP.1 hne
      · exact hyc u hu
    · rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;>
        rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
      · exact absurd rfl hij
      · exact harc0.1
      · exact harc0.1.symm
      · exact absurd rfl hij
  have htail := tail hg hP (by omega) (fun i h2 h3 => hpre.2 i (by omega) 1 (by omega) (by omega))
  have IHt := IH (p - 1) (by omega) _ _ _ hg' htail
  have hppS := hnS p (by omega) le_rfl
  have hp1S := hnS 1 le_rfl (by omega)
  have hgp1 : ∀ i, 1 ≤ i → i < p → G.Adj (g i) (g p) := fun i h1 h2 => by
    have := IHt.2 (i - 1) (by omega) (p - 1) le_rfl (by omega)
    simp only [show i - 1 + 1 = i by omega, show p - 1 + 1 = p by omega] at this
    exact this
  have hgp2 : ∀ u ∈ S, u ≠ g 0 → G.Adj u (g p) := fun u hu hne => by
    have := IHt.1 (p - 1) le_rfl u (mem_sw.2 (Or.inr ⟨hne, hu⟩))
    simp only [show p - 1 + 1 = p by omega] at this
    exact this (fun e => hppS (e ▸ hu))
  have harcp : Arc G S f (g (p - 1)) (g p) := by
    have := hP.2.1 (p - 1) (by omega); rwa [show p - 1 + 1 = p by omega] at this
  have key : G.Adj (g 0) (g p) := by
    by_contra hn
    have hg1p : G.Adj (g 1) (g p) := hgp1 1 le_rfl (by omega)
    obtain ⟨yp, hypS, hfyp, hypc, hyp1⟩ := l33 h hg hP.1 harc0 (c := f (g p))
      (hg.2.2.1 _ hppS) (fun e => hg.2.2.2 _ _ hp1S hppS hg1p e.symm)
    have hyp_ne : yp ≠ g p := fun e => hn (e ▸ hypc (g 0) hP.1)
    have hnadj : ¬ G.Adj (g (p - 1)) yp := fun e => hyp_ne (harcp.2.2 yp hypS e hfyp)
    rcases Nat.lt_or_ge p 3 with hp3 | hp3
    · rw [show p - 1 = 1 by omega] at hnadj; exact hnadj hyp1
    obtain ⟨x, hx, hx0⟩ := Finset.exists_mem_ne
      (by rw [hg.2.1]; have := h.two_le; omega : 1 < S.card) (g 0)
    have hxg : ∀ i ≤ p, G.Adj x (g i) := by
      intro i hi
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · exact cl_adj hg hx hP.1 hx0
      rcases lt_or_eq_of_le hi with hi' | rfl
      · exact hpre.1 i (by omega) x hx (fun e => hnS i hi0 hi (e ▸ hx))
      · exact hgp2 x hx hx0
    have claim : ∀ j, 1 ≤ j → j ≤ p - 1 →
        ∃ yj, yj ∉ S ∧ f yj = f (g j) ∧ yj ≠ g j ∧ G.Adj x yj := by
      intro j hj1 hj2
      by_contra H
      push Not at H
      have harc : Arc G S f x (g j) := ⟨hxg j (by omega), hnS j hj1 (by omega),
        fun z hz hxz hfz => by by_contra hne; exact H z hz hfz hne hxz⟩
      rcases Nat.lt_or_ge j 2 with hj | hj
      · have hj1' : j = 1 := by omega
        subst hj1'
        have ht := tail' hg hP (by omega) hx harc
          (fun i h2 h3 => hpre.2 i (by omega) 1 (by omega) (by omega))
        have := (IH (p - 1) (by omega) _ _ _ (l32 h hg hx harc).2 ht).1 (p - 1) le_rfl (g 0)
          (mem_sw.2 (Or.inr ⟨Ne.symm hx0, hP.1⟩))
        simp only [show p - 1 + 1 = p by omega] at this
        exact hn (this (fun e => hppS (e ▸ hP.1)))
      · have hJ := jump hP hx hj1 (by omega) harc
        have := (IH (p - j + 1) (by omega) _ _ _ hg hJ).1 (p - j + 1) le_rfl (g 0) hP.1
        simp only [show p - j + 1 ≠ 0 by omega, if_false, show p - j + 1 + j - 1 = p by omega]
          at this
        exact hn (this (fun e => hppS (e ▸ hP.1)))
    have claim' : ∀ j, ∃ yj, 1 ≤ j → j ≤ p →
        yj ∉ S ∧ f yj = f (g j) ∧ yj ≠ g j ∧ G.Adj x yj := by
      intro j
      by_cases hj : 1 ≤ j ∧ j ≤ p - 1
      · obtain ⟨yj, hh⟩ := claim j hj.1 hj.2; exact ⟨yj, fun _ _ => hh⟩
      · refine ⟨yp, fun h1 h2 => ?_⟩
        have : j = p := by omega
        subst this
        exact ⟨hypS, hfyp, hyp_ne, hypc x hx⟩
    choose Y hY using claim'
    have hY3 : ∀ j, 1 ≤ j → j ≤ p → Y j ∉ S ∧ f (Y j) = f (g j) ∧ Y j ≠ g j :=
      fun j h1 h2 => ⟨(hY j h1 h2).1, (hY j h1 h2).2.1, (hY j h1 h2).2.2.1⟩
    obtain ⟨A, hA⟩ := sep_exists h.ql x
    have hpar := alt hA g Y p hxg (fun j h1 h2 => (hY j h1 h2).2.2.2) (seqk1 hg hP hY3)
      (seqk2 hg hP hY3) p le_rfl
    have e := hA (g p) (g 0) (hxg p le_rfl) (hxg 0 (by omega)) (fun e => hppS (e ▸ hP.1))
      (fun e => hn e.symm)
    tauto
  refine ⟨fun i hi u hu hne => ?_, fun i hi j hj hij => ?_⟩
  · rcases (lt_or_eq_of_le hi) with hi' | rfl
    · exact hpre.1 i (by omega) u hu hne
    · by_cases hu0 : u = g 0
      · rw [hu0]; exact key
      · exact hgp2 u hu hu0
  · wlog hij' : i < j generalizing i j
    · exact (this j hj i hi (Ne.symm hij) (by omega)).symm
    rcases (lt_or_eq_of_le hj) with hj' | rfl
    · exact hpre.2 i (by omega) j (by omega) hij
    · rcases Nat.eq_zero_or_pos i with rfl | hi0
      · exact key
      · exact hgp1 i hi0 hij'

/-- Lemma 3.7. -/
lemma l37 (h : Hyp G s T) : ∀ p (S : Finset V) (f : V → ℕ) (g : ℕ → V),
    Good G s T S f → IsPath G S f p g → ∀ c, c < T → (∀ i, 1 ≤ i → i ≤ p → f (g i) ≠ c) →
    ∃ z, z ∉ S ∧ f z = c ∧ (∀ u ∈ S, G.Adj u z) ∧ ∀ i ≤ p, G.Adj (g i) z := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p IH =>
  intro S f g hg hP c hc hcol
  have hnS : ∀ i, 1 ≤ i → i ≤ p → g i ∉ S := fun i h1 h2 => path_notin hP h1 h2
  rcases Nat.lt_or_ge p 1 with hp | hp
  · obtain ⟨z, hzS, hfz, hzc⟩ := l25 h hg hc
    refine ⟨z, hzS, hfz, hzc, fun i hi => ?_⟩
    have : i = 0 := by omega
    subst this; exact hzc _ hP.1
  have harc0 : Arc G S f (g 0) (g 1) := hP.2.1 0 (by omega)
  rcases Nat.lt_or_ge p 2 with hp2 | hp2
  · have hp1 : p = 1 := by omega
    subst hp1
    obtain ⟨z, hzS, hfz, hzc, hz1⟩ := l33 h hg hP.1 harc0 hc (fun e => hcol 1 le_rfl le_rfl e.symm)
    refine ⟨z, hzS, hfz, hzc, fun i hi => ?_⟩
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · exact hzc _ hP.1
    · exact hz1
  have hpc := l35 h p S f g hg hP
  obtain ⟨y', hy'S, hfy', hy'c, hy'g⟩ := IH (p - 1) (by omega) S f g hg (path_le hP (by omega)) c hc
    (fun i h1 h2 => hcol i h1 (by omega))
  by_cases n1 : G.Adj (g p) y'
  · refine ⟨y', hy'S, hfy', hy'c, fun i hi => ?_⟩
    rcases lt_or_eq_of_le hi with hi' | rfl
    · exact hy'g i (by omega)
    · exact n1
  obtain ⟨hyc1, hg'⟩ := l32 h hg hP.1 harc0
  have htail := tail hg hP (by omega) (fun i h2 h3 => hpc.2 i (by omega) 1 (by omega) (by omega))
  have hg1c : f (g 1) ≠ c := hcol 1 le_rfl (by omega)
  obtain ⟨z', hz'S', hfz', hz'c, hz'g⟩ := IH (p - 1) (by omega) _ _ _ hg' htail c hc (by
    intro i h1 h2
    show fw f (g 0) (g 1) (g (i + 1)) ≠ c
    rw [fw_ne (fun (e : g (i + 1) = g 0) => hnS (i + 1) (by omega) (by omega) (e ▸ hP.1))]
    exact hcol (i + 1) (by omega) (by omega))
  have hz'0 : z' ≠ g 0 := by intro e; rw [e, fw_self] at hfz'; exact hg1c hfz'
  rw [fw_ne hz'0] at hfz'
  have hz'S : z' ∉ S := fun e => hz'S' (mem_sw.2 (Or.inr ⟨hz'0, e⟩))
  by_cases n2 : G.Adj (g 0) z'
  · refine ⟨z', hz'S, hfz', fun u hu => ?_, fun i hi => ?_⟩
    · by_cases hu0 : u = g 0
      · rw [hu0]; exact n2
      · exact hz'c u (mem_sw.2 (Or.inr ⟨hu0, hu⟩))
    · rcases Nat.eq_zero_or_pos i with rfl | hi0
      · exact n2
      · have := hz'g (i - 1) (by omega)
        simp only [show i - 1 + 1 = i by omega] at this; exact this
  exfalso
  have hz'y' : z' ≠ y' := fun e => n2 (e ▸ hy'c _ hP.1)
  obtain ⟨x, hx, hx0⟩ := Finset.exists_mem_ne
    (by rw [hg.2.1]; have := h.two_le; omega : 1 < S.card) (g 0)
  have hxz' : G.Adj x z' := hz'c x (mem_sw.2 (Or.inr ⟨hx0, hx⟩))
  have hxy' : G.Adj x y' := hy'c x hx
  have hxg : ∀ i ≤ p, G.Adj x (g i) := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact cl_adj hg hx hP.1 hx0
    · exact hpc.1 i hi x hx (fun e => hnS i hi0 hi (e ▸ hx))
  have claim : ∀ j, 1 ≤ j → j ≤ p →
      ∃ vj, vj ∉ S ∧ f vj = f (g j) ∧ vj ≠ g j ∧ G.Adj x vj := by
    intro j hj1 hj2
    by_contra H
    push Not at H
    have harc : Arc G S f x (g j) := ⟨hxg j hj2, hnS j hj1 hj2,
      fun z hz hxz hfz => by by_contra hne; exact H z hz hfz hne hxz⟩
    rcases Nat.lt_or_ge j 2 with hj | hj
    · have hj1' : j = 1 := by omega
      subst hj1'
      have ht := tail' hg hP (by omega) hx harc
        (fun i h2 h3 => hpc.2 i (by omega) 1 (by omega) (by omega))
      obtain ⟨u, huS', hfu', huc', hug⟩ := IH (p - 1) (by omega) _ _ _ (l32 h hg hx harc).2 ht
        c hc (by
          intro i h1 h2
          show fw f x (g 1) (g (i + 1)) ≠ c
          rw [fw_ne (fun (e : g (i + 1) = x) => hnS (i + 1) (by omega) (by omega) (e ▸ hx))]
          exact hcol (i + 1) (by omega) (by omega))
      have hux : u ≠ x := by intro e; rw [e, fw_self] at hfu'; exact hg1c hfu'
      rw [fw_ne hux] at hfu'
      have huS : u ∉ S := fun e => huS' (mem_sw.2 (Or.inr ⟨hux, e⟩))
      have hug0 : G.Adj (g 0) u := huc' (g 0) (mem_sw.2 (Or.inr ⟨Ne.symm hx0, hP.1⟩))
      have hugp : G.Adj (g p) u := by
        have := hug (p - 1) le_rfl; simp only [show p - 1 + 1 = p by omega] at this; exact this
      have hu1 : G.Adj (g 1) u := huc' (g 1) (mem_sw.2 (Or.inl rfl))
      have hy1 : G.Adj (g 1) y' := hy'g 1 (by omega)
      have hz1 : G.Adj (g 1) z' := hz'c (g 1) (mem_sw.2 (Or.inl rfl))
      exact three h hg hu1 hy1 hz1 huS hy'S hz'S (hfu'.trans hfy'.symm) (hfu'.trans hfz'.symm)
        (fun e => n1 (e ▸ hugp)) (fun e => n2 (e ▸ hug0)) (Ne.symm hz'y')
    · have hJ := jump hP hx hj1 hj2 harc
      obtain ⟨u, huS, hfu, huc, hug⟩ := IH (p - j + 1) (by omega) S f _ hg hJ c hc (by
        intro i h1 h2
        simp only [show i ≠ 0 by omega, if_false]
        exact hcol _ (by omega) (by omega))
      have hugp : G.Adj (g p) u := by
        have := hug (p - j + 1) le_rfl
        simp only [show p - j + 1 ≠ 0 by omega, if_false, show p - j + 1 + j - 1 = p by omega]
          at this
        exact this
      have hug0 : G.Adj (g 0) u := huc (g 0) hP.1
      exact three h hg (huc x hx) hxy' hxz' huS hy'S hz'S (hfu.trans hfy'.symm)
        (hfu.trans hfz'.symm) (fun e => n1 (e ▸ hugp)) (fun e => n2 (e ▸ hug0)) (Ne.symm hz'y')
  have claim' : ∀ j, ∃ vj, 1 ≤ j → j ≤ p →
      vj ∉ S ∧ f vj = f (g j) ∧ vj ≠ g j ∧ G.Adj x vj := by
    intro j
    by_cases hj : 1 ≤ j ∧ j ≤ p
    · obtain ⟨vj, hh⟩ := claim j hj.1 hj.2; exact ⟨vj, fun _ _ => hh⟩
    · exact ⟨x, fun h1 h2 => absurd ⟨h1, h2⟩ hj⟩
  choose Y hY using claim'
  have hY3 : ∀ j, 1 ≤ j → j ≤ p → Y j ∉ S ∧ f (Y j) = f (g j) ∧ Y j ≠ g j :=
    fun j h1 h2 => ⟨(hY j h1 h2).1, (hY j h1 h2).2.1, (hY j h1 h2).2.2.1⟩
  obtain ⟨A, hA⟩ := sep_exists h.ql x
  have hpar := alt hA g Y p hxg (fun j h1 h2 => (hY j h1 h2).2.2.2) (seqk1 hg hP hY3)
    (seqk2 hg hP hY3) p le_rfl
  have hgpy' : g p ≠ y' := fun e => hcol p (by omega) le_rfl (by rw [e, hfy'])
  have e1 := hA (g p) y' (hxg p le_rfl) hxy' hgpy' n1
  have e2 := hA y' z' hxy' hxz' (Ne.symm hz'y') (nadj hg hy'S hz'S (hfy'.trans hfz'.symm))
  have e3 := hA z' (g 0) hxz' (hxg 0 (by omega)) hz'0 (fun e => n2 e.symm)
  tauto

lemma arc_back (hg : Good G s T S f) {x y : V} (hx : x ∈ S) (hxy : Arc G S f x y) :
    Arc G (sw S x y) (fw f x y) y x := by
  have hyS := hxy.2.1
  have hxy' : x ≠ y := fun e => hyS (e ▸ hx)
  refine ⟨hxy.1.symm, ?_, ?_⟩
  · rw [mem_sw]; rintro (e | ⟨e, -⟩)
    · exact hxy' e
    · exact e rfl
  · intro w hw hyw hfw
    rw [mem_sw] at hw; push Not at hw
    rw [fw_self] at hfw
    by_contra hwx
    rw [fw_ne hwx] at hfw
    exact hg.2.2.2 y w hyS (hw.2 hwx) hyw hfw.symm

lemma keep (hg : Good G s T S f) {x y : V} (hx : x ∈ S) (hxy : Arc G S f x y) {p : ℕ}
    {g : ℕ → V} (hP : IsPath G S f p g) (hy : ∀ k ≤ p, g k ≠ y) (h0 : g 0 ≠ x)
    (hadj : ∀ i < p, G.Adj (g i) y) : IsPath G (sw S x y) (fw f x y) p g :=
  ⟨mem_sw.2 (Or.inr ⟨h0, hP.1⟩), fun i hi => arc_swap hg hx hxy (hP.2.1 i hi) (hy (i + 1) hi)
    (Or.inr (Or.inl (hadj i hi))), hP.2.2⟩

lemma cons2 (hg : Good G s T S f) {p : ℕ} {g : ℕ → V} (hP : IsPath G S f p g) {y : V}
    (hxy : Arc G S f (g 0) y) (hy : ∀ k ≤ p, g k ≠ y)
    (hadj : ∀ i, 1 ≤ i → i < p → G.Adj (g i) y) :
    IsPath G (sw S (g 0) y) (fw f (g 0) y) (p + 1) (fun i => if i = 0 then y else g (i - 1)) := by
  refine ⟨by simp [mem_sw], ?_, ?_⟩
  · intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · show Arc G _ _ (if 0 = 0 then y else g (0 - 1)) (if 0 + 1 = 0 then y else g (0 + 1 - 1))
      rw [if_pos rfl, if_neg (by omega), show 0 + 1 - 1 = 0 by omega]
      exact arc_back hg hP.1 hxy
    · show Arc G _ _ (if i = 0 then y else g (i - 1)) (if i + 1 = 0 then y else g (i + 1 - 1))
      rw [if_neg (by omega), if_neg (by omega), show i + 1 - 1 = i - 1 + 1 by omega]
      apply arc_swap hg hP.1 hxy (hP.2.1 (i - 1) (by omega)) (hy _ (by omega))
      rcases Nat.eq_zero_or_pos (i - 1) with h0 | h0
      · right; left; rw [h0]; exact hxy.1
      · right; left; exact hadj (i - 1) h0 (by omega)
  · intro i i' hi hi' e
    have e' : (if i = 0 then y else g (i - 1)) = (if i' = 0 then y else g (i' - 1)) := e
    by_cases h0 : i = 0 <;> by_cases h0' : i' = 0
    · omega
    · rw [if_pos h0, if_neg h0'] at e'; exact absurd e'.symm (hy _ (by omega))
    · rw [if_neg h0, if_pos h0'] at e'; exact absurd e' (hy _ (by omega))
    · rw [if_neg h0, if_neg h0'] at e'; have := hP.2.2 _ _ (by omega) (by omega) e'; omega

/-- Lemma 3.6, for two paths. -/
lemma l36 (h : Hyp G s T) : ∀ n m (S : Finset V) (f : V → ℕ), Good G s T S f →
    ∀ p q (g g' : ℕ → V), IsPath G S f p g → IsPath G S f q g' → p + q = n → min p q = m →
    g p ≠ g' q → G.Adj (g p) (g' q) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IHn =>
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IHm =>
  have main : ∀ (S : Finset V) (f : V → ℕ), Good G s T S f →
      ∀ p q (g g' : ℕ → V), IsPath G S f p g → IsPath G S f q g' → p + q = n →
      min p q = m → q ≤ p → g p ≠ g' q → G.Adj (g p) (g' q) := by
    intro S f hg p q g g' hP hQ hn hm hqp hne
    have pcP := l35 h p S f g hg hP
    have pcQ := l35 h q S f g' hg hQ
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · exact (pcP.1 p le_rfl (g' 0) hQ.1 (Ne.symm hne)).symm
    have arcQ : Arc G S f (g' 0) (g' 1) := hQ.2.1 0 (by omega)
    obtain ⟨hy1c, hg'⟩ := l32 h hg hQ.1 arcQ
    rcases Nat.lt_or_ge p 2 with hp2 | hp2
    · have hp1 : p = 1 := by omega
      have hq1 : q = 1 := by omega
      subst hp1
      subst hq1
      have arcP : Arc G S f (g 0) (g 1) := hP.2.1 0 (by omega)
      by_cases hf : f (g 1) = f (g' 1)
      · exact absurd (arcQ.2.2 (g 1) (path_notin hP le_rfl le_rfl)
          ((l32 h hg hP.1 arcP).1 (g' 0) hQ.1) hf) hne
      · obtain ⟨z, hzS, hfz, hzc, hz1⟩ := l33 h hg hP.1 arcP (c := f (g' 1))
          (hg.2.2.1 _ (path_notin hQ le_rfl le_rfl)) (Ne.symm hf)
        have := arcQ.2.2 z hzS (hzc (g' 0) hQ.1) hfz
        rw [← this]; exact hz1
    have one : ∀ a ≤ p - 1, ∀ b ≤ q, g a ≠ g' b → G.Adj (g a) (g' b) := by
      intro a ha b hb hab
      exact IHn (a + b) (by omega) (min a b) S f hg a b g g' (path_le hP (by omega))
        (path_le hQ hb) rfl rfl hab
    have htQ := tail hg hQ (by omega) (fun i h2 h3 => pcQ.2 i (by omega) 1 (by omega) (by omega))
    by_cases c3 : ∃ k ≤ p, g k = g' 1
    · obtain ⟨k, hk, hgk⟩ := c3
      have hk1 : 1 ≤ k := by
        by_contra hk0
        have hk0' : k = 0 := by omega
        rw [hk0'] at hgk
        exact path_notin hQ le_rfl (by omega) (hgk ▸ hP.1)
      have arcK : Arc G S f (g' 0) (g k) := hgk ▸ arcQ
      rcases Nat.lt_or_ge k 2 with hk2 | hk2
      · have hk1' : k = 1 := by omega
        subst hk1'
        have htP := tail' hg hP (by omega) hQ.1 arcK
          (fun i h2 h3 => pcP.2 i (by omega) 1 (by omega) (by omega))
        rw [hgk] at htP
        have := IHn (p - 1 + (q - 1)) (by omega) _ _ _ hg' (p - 1) (q - 1) _ _ htP htQ rfl rfl
          (by simp only [show p - 1 + 1 = p by omega, show q - 1 + 1 = q by omega]; exact hne)
        simpa only [show p - 1 + 1 = p by omega, show q - 1 + 1 = q by omega] using this
      · have hJ := jump hP hQ.1 hk1 hk arcK
        have := IHn (p - k + 1 + q) (by omega) _ _ _ hg (p - k + 1) q _ g' hJ hQ rfl rfl
          (by simp only [show p - k + 1 ≠ 0 by omega, if_false,
                show p - k + 1 + k - 1 = p by omega]
              exact hne)
        simpa only [show p - k + 1 ≠ 0 by omega, if_false, show p - k + 1 + k - 1 = p by omega]
          using this
    push Not at c3
    have hadjP : ∀ i, i < p → G.Adj (g i) (g' 1) := fun i hi =>
      one i (by omega) 1 hq (c3 i (by omega))
    by_cases c2 : g' 0 = g 0
    · have arc0 : Arc G S f (g 0) (g' 1) := c2 ▸ arcQ
      have hP' := cons2 hg hP arc0 c3 (fun i h1 h2 => hadjP i h2)
      rw [← c2] at hP'
      have := IHm (q - 1) (by omega) _ _ hg' (p + 1) (q - 1) _ _ hP' htQ (by omega) (by omega)
        (by simp only [show p + 1 ≠ 0 by omega, if_false, Nat.add_sub_cancel,
              show q - 1 + 1 = q by omega]
            exact hne)
      simpa only [show p + 1 ≠ 0 by omega, if_false, Nat.add_sub_cancel,
        show q - 1 + 1 = q by omega] using this
    · have hP1 := keep hg hQ.1 arcQ hP c3 (Ne.symm c2) hadjP
      have := IHn (p + (q - 1)) (by omega) _ _ _ hg' p (q - 1) g _ hP1 htQ rfl rfl
        (by simp only [show q - 1 + 1 = q by omega]; exact hne)
      simpa only [show q - 1 + 1 = q by omega] using this
  intro S f hg p q g g' hP hQ hn hm hne
  rcases le_total q p with hqp | hpq
  · exact main S f hg p q g g' hP hQ hn hm hqp hne
  · exact (main S f hg q p g' g hQ hP (by omega) (by rw [min_comm]; exact hm) hpq
      (Ne.symm hne)).symm

variable (G) in
def InR (S : Finset V) (f : V → ℕ) (v : V) : Prop := ∃ p g, IsPath G S f p g ∧ g p = v

lemma inR_of_mem {v : V} (hv : v ∈ S) : InR G S f v :=
  ⟨0, fun _ => v, ⟨hv, fun i hi => by omega, fun i j hi hj _ => by omega⟩, rfl⟩

lemma inR_arc {v y : V} (hv : InR G S f v) (hvy : Arc G S f v y) : InR G S f y := by
  classical
  obtain ⟨p, g, hP, rfl⟩ := hv
  by_cases hk : ∃ k ≤ p, g k = y
  · obtain ⟨k, hk, rfl⟩ := hk
    exact ⟨k, g, path_le hP hk, rfl⟩
  · push Not at hk
    refine ⟨p + 1, fun i => if i ≤ p then g i else y, ⟨by simp [hP.1], ?_, ?_⟩, by simp⟩
    · intro i hi
      by_cases hip : i + 1 ≤ p
      · show Arc G S f (if i ≤ p then g i else y) (if i + 1 ≤ p then g (i + 1) else y)
        rw [if_pos (by omega), if_pos hip]; exact hP.2.1 i (by omega)
      · have hi' : i = p := by omega
        show Arc G S f (if i ≤ p then g i else y) (if i + 1 ≤ p then g (i + 1) else y)
        rw [if_pos (by omega), if_neg hip, hi']; exact hvy
    · intro i j hi hj e
      have e' : (if i ≤ p then g i else y) = (if j ≤ p then g j else y) := e
      by_cases h1 : i ≤ p <;> by_cases h2 : j ≤ p
      · rw [if_pos h1, if_pos h2] at e'; exact hP.2.2 i j h1 h2 e'
      · rw [if_pos h1, if_neg h2] at e'; exact absurd e' (hk i h1)
      · rw [if_neg h1, if_pos h2] at e'; exact absurd e'.symm (hk j h2)
      · omega

lemma inR_pre {p : ℕ} {g : ℕ → V} (hP : IsPath G S f p g) {i : ℕ} (hi : i ≤ p) :
    InR G S f (g i) := ⟨i, g, path_le hP hi, rfl⟩

lemma R_clique (h : Hyp G s T) (hg : Good G s T S f) {a b : V} (ha : InR G S f a)
    (hb : InR G S f b) (hne : a ≠ b) : G.Adj a b := by
  obtain ⟨p, g, hP, rfl⟩ := ha
  obtain ⟨q, g', hQ, rfl⟩ := hb
  exact l36 h _ _ S f hg p q g g' hP hQ rfl rfl hne

lemma path_sub {P : V → Prop} (h0 : ∀ v ∈ S, P v) (hstep : ∀ u v, P u → Arc G S f u v → P v)
    {p : ℕ} {g : ℕ → V} (hP : IsPath G S f p g) : ∀ i ≤ p, P (g i) := by
  intro i
  induction i with
  | zero => intro _; exact h0 _ hP.1
  | succ i ih => intro hi; exact hstep _ _ (ih (by omega)) (hP.2.1 i (by omega))

lemma R_mono (h : Hyp G s T) (hg : Good G s T S f) {x y : V} (hx : x ∈ S)
    (hxy : Arc G S f x y) {v : V} (hv : InR G S f v) : InR G (sw S x y) (fw f x y) v := by
  have hyR : InR G S f y := inR_arc (inR_of_mem hx) hxy
  have hyS' : y ∈ sw S x y := mem_sw.2 (Or.inl rfl)
  obtain ⟨p, g, hP, rfl⟩ := hv
  have key := path_sub (P := fun w => InR G S f w ∧ InR G (sw S x y) (fw f x y) w)
    (fun w hw => ⟨inR_of_mem hw, by
      by_cases hwx : w = x
      · rw [hwx]; exact inR_arc (inR_of_mem hyS') (arc_back hg hx hxy)
      · exact inR_of_mem (mem_sw.2 (Or.inr ⟨hwx, hw⟩))⟩)
    (fun u w hu huw => ⟨inR_arc hu.1 huw, by
      by_cases hwy : w = y
      · rw [hwy]; exact inR_of_mem hyS'
      · refine inR_arc hu.2 (arc_swap hg hx hxy huw hwy ?_)
        by_cases huy : u = y
        · exact Or.inl huy
        · exact Or.inr (Or.inl (R_clique h hg hu.1 hyR huy))⟩) hP p le_rfl
  exact key.2

lemma arc_congr {f1 f2 : V → ℕ} (hff : ∀ v ∉ S, f1 v = f2 v) {a b : V} :
    Arc G S f1 a b → Arc G S f2 a b := by
  rintro ⟨h1, h2, h3⟩
  refine ⟨h1, h2, fun z hz hz' hf => h3 z hz hz' ?_⟩
  rw [hff z hz, hff b h2]; exact hf

lemma inR_congr {f1 f2 : V → ℕ} (hff : ∀ v ∉ S, f1 v = f2 v) {v : V} :
    InR G S f1 v → InR G S f2 v := fun ⟨p, g, hP, he⟩ =>
  ⟨p, g, ⟨hP.1, fun i hi => arc_congr hff (hP.2.1 i hi), hP.2.2⟩, he⟩

lemma sw_sw {x y : V} (hx : x ∈ S) (hy : y ∉ S) : sw (sw S x y) y x = S := by
  ext v
  simp only [mem_sw]
  constructor
  · rintro (rfl | ⟨h1, rfl | ⟨h2, h3⟩⟩)
    · exact hx
    · exact absurd rfl h1
    · exact h3
  · intro hv
    by_cases hvx : v = x
    · exact Or.inl hvx
    · exact Or.inr ⟨fun e => hy (e ▸ hv), Or.inr ⟨hvx, hv⟩⟩

lemma fw_fw {x y : V} (hx : x ∈ S) : ∀ v ∉ S, fw (fw f x y) y x v = f v := by
  intro v hv
  have hvx : v ≠ x := fun e => hv (e ▸ hx)
  by_cases hvy : v = y
  · rw [hvy, fw_self, fw_self]
  · rw [fw_ne hvy, fw_ne hvx]

lemma R_rev (h : Hyp G s T) (hg : Good G s T S f) {x y : V} (hx : x ∈ S)
    (hxy : Arc G S f x y) {v : V} (hv : InR G (sw S x y) (fw f x y) v) : InR G S f v := by
  have hg' := (l32 h hg hx hxy).2
  have := R_mono h hg' (mem_sw.2 (Or.inl rfl)) (arc_back hg hx hxy) hv
  rw [sw_sw hx hxy.2.1] at this
  exact inR_congr (fw_fw hx) this

variable (G) in
def Inv (S : Finset V) (f : V → ℕ) (c : ℕ) : Prop := ∀ v, InR G S f v → v ∉ S → f v ≠ c

lemma swap_inv (h : Hyp G s T) (hg : Good G s T S f) {x y : V} (hx : x ∈ S)
    (hxy : Arc G S f x y) {c : ℕ} (hinv : Inv G S f c) :
    Inv G (sw S x y) (fw f x y) c ∧
      ∀ v, (v ∉ sw S x y ∧ fw f x y v = c) ↔ (v ∉ S ∧ f v = c) := by
  have hyc : f y ≠ c := hinv y (inR_arc (inR_of_mem hx) hxy) hxy.2.1
  refine ⟨fun v hv hvS => ?_, fun v => ?_⟩
  · have hvR := R_rev h hg hx hxy hv
    rw [mem_sw] at hvS; push Not at hvS
    by_cases hvx : v = x
    · rw [hvx, fw_self]; exact hyc
    · rw [fw_ne hvx]; exact hinv v hvR (hvS.2 hvx)
  · rw [mem_sw]
    constructor
    · rintro ⟨h1, h2⟩
      push Not at h1
      by_cases hvx : v = x
      · rw [hvx, fw_self] at h2; exact absurd h2 hyc
      · rw [fw_ne hvx] at h2; exact ⟨h1.2 hvx, h2⟩
    · rintro ⟨h1, h2⟩
      have hvx : v ≠ x := fun e => h1 (e ▸ hx)
      refine ⟨?_, by rw [fw_ne hvx]; exact h2⟩
      rintro (e | ⟨-, e⟩)
      · exact hyc (e ▸ h2)
      · exact h1 e

lemma move (h : Hyp G s T) {c : ℕ} : ∀ p (S : Finset V) (f : V → ℕ) (g : ℕ → V),
    Good G s T S f → Inv G S f c → IsPath G S f p g →
    ∃ S' f', Good G s T S' f' ∧ Inv G S' f' c ∧ g p ∈ S' ∧ (∀ u ∈ S, u ≠ g 0 → u ∈ S') ∧
      (∀ v, InR G S f v → InR G S' f' v) ∧ ∀ v, (v ∉ S' ∧ f' v = c) ↔ (v ∉ S ∧ f v = c) := by
  intro p
  induction p with
  | zero =>
    intro S f g hg hinv hP
    exact ⟨S, f, hg, hinv, hP.1, fun u hu _ => hu, fun v hv => hv, fun v => Iff.rfl⟩
  | succ p ih =>
    intro S f g hg hinv hP
    have harc0 : Arc G S f (g 0) (g 1) := hP.2.1 0 (by omega)
    have hg1 := (l32 h hg hP.1 harc0).2
    obtain ⟨hinv1, hcl1⟩ := swap_inv h hg hP.1 harc0 hinv
    have pc := l35 h _ S f g hg hP
    have ht := tail hg hP (by omega) (fun i h2 h3 => pc.2 i (by omega) 1 (by omega) (by omega))
    obtain ⟨S', f', hg', hinv', hp', hsub, hR, hcl⟩ := ih _ _ _ hg1 hinv1 ht
    refine ⟨S', f', hg', hinv', hp', fun u hu hu0 => hsub u (mem_sw.2 (Or.inr ⟨hu0, hu⟩)) ?_,
      fun v hv => hR v (R_mono h hg hP.1 harc0 hv), fun v => (hcl v).trans (hcl1 v)⟩
    exact fun e => path_notin hP le_rfl (by omega) (e ▸ hu)

lemma zR (h : Hyp G s T) (hg : Good G s T S f) {c : ℕ} (hc : c < T) (hinv : Inv G S f c)
    {v : V} (hv : InR G S f v) :
    ∃ z, z ∉ S ∧ f z = c ∧ (∀ u ∈ S, G.Adj u z) ∧ G.Adj v z := by
  obtain ⟨p, g, hP, rfl⟩ := hv
  obtain ⟨z, hzS, hfz, hzc, hzg⟩ := l37 h p S f g hg hP c hc
    (fun i h1 h2 => hinv _ (inR_pre hP h2) (path_notin hP h1 h2))
  exact ⟨z, hzS, hfz, hzc, hzg p le_rfl⟩

/-- Lemma 3.8. -/
lemma l38 (h : Hyp G s T) (hg : Good G s T S f) {c : ℕ} (hc : c < T) (hinv : Inv G S f c) :
    ∃ z, z ∉ S ∧ f z = c ∧ ∀ v, InR G S f v → G.Adj v z := by
  by_contra H
  push Not at H
  obtain ⟨z1, hz1S, hfz1, hz1c⟩ := l25 h hg hc
  obtain ⟨v1, hv1, n1⟩ := H z1 hz1S hfz1
  obtain ⟨z2, hz2S, hfz2, hz2c, a12⟩ := zR h hg hc hinv hv1
  obtain ⟨v2, hv2, n2⟩ := H z2 hz2S hfz2
  obtain ⟨p, g, hP, rfl⟩ := hv2
  obtain ⟨S', f', hg', hinv', hp', hsub, hR, hcl⟩ := move h p S f g hg hinv hP
  obtain ⟨z3, hz3S', hfz3', hz3c, a13⟩ := zR h hg' hc hinv' (hR v1 hv1)
  obtain ⟨hz3S, hfz3⟩ := (hcl z3).1 ⟨hz3S', hfz3'⟩
  obtain ⟨x, hx, hx0⟩ := Finset.exists_mem_ne
    (by rw [hg.2.1]; have := h.two_le; omega : 1 < S.card) (g 0)
  have d12 : z1 ≠ z2 := fun e => n1 (e ▸ a12)
  have d13 : z1 ≠ z3 := fun e => n1 (e ▸ a13)
  have d23 : z2 ≠ z3 := fun e => n2 (e ▸ hz3c _ hp')
  exact three h hg (hz1c x hx) (hz2c x hx) (hz3c x (hsub x hx hx0)) hz1S hz2S hz3S
    (hfz1.trans hfz2.symm) (hfz1.trans hfz3.symm) d12 d13 d23

lemma same_side {x : V} {A : Set V} (hA : Sep G x A) {u v : V} (hu : G.Adj x u)
    (hv : G.Adj x v) (hne : u ≠ v) (hs : u ∈ A ↔ v ∈ A) : G.Adj u v := by
  by_contra hn
  have := hA u v hu hv hne hn
  tauto

/-- The final contradiction: a clique of order `s + T`. -/
theorem core [Fintype V] (h : Hyp G s T) {S : Finset V} {f : V → ℕ} (hg : Good G s T S f) :
    False := by
  classical
  obtain ⟨x, hx⟩ : S.Nonempty := Finset.card_pos.mp (by rw [hg.2.1]; have := h.two_le; omega)
  haveI : Nonempty V := ⟨x⟩
  let Rf : Finset V := Finset.univ.filter (fun v => InR G S f v)
  let C1 : Finset ℕ := (Rf.filter (fun v => v ∉ S)).image f
  have hC1 : ∀ c, c ∈ C1 ↔ ∃ v, InR G S f v ∧ v ∉ S ∧ f v = c := by
    intro c
    simp only [C1, Rf, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun ⟨v, ⟨h1, h2⟩, h3⟩ => ⟨v, h1, h2, h3⟩, fun ⟨v, h1, h2, h3⟩ => ⟨v, ⟨h1, h2⟩, h3⟩⟩
  let C2 : ℕ → Prop := fun c => c < T ∧ c ∉ C1
  have hinvc : ∀ c, C2 c → Inv G S f c := by
    intro c hc v hv hvS hfv
    exact hc.2 ((hC1 c).2 ⟨v, hv, hvS, hfv⟩)
  choose! zc hzc using (fun c (hc : C2 c) => l38 h hg hc.1 (hinvc c hc))
  have hzR : ∀ c, C2 c → ¬ InR G S f (zc c) := fun c hc hR =>
    hinvc c hc _ hR (hzc c hc).1 (hzc c hc).2.1
  have hd : ∀ c, C2 c → ∀ v, InR G S f v → ∃ d, d ∉ S ∧ f d = c ∧ G.Adj v d ∧ d ≠ zc c := by
    intro c hc v hv
    by_contra H
    push Not at H
    obtain ⟨hzS, hfz, hzadj⟩ := hzc c hc
    have harc : Arc G S f v (zc c) :=
      ⟨hzadj v hv, hzS, fun w hw hvw hfw => H w hw (hfw.trans hfz) hvw⟩
    exact hzR c hc (inR_arc hv harc)
  obtain ⟨A, hA⟩ := sep_exists h.ql x
  have hxR : ∀ v, InR G S f v → v ≠ x → G.Adj x v := fun v hv hvx =>
    R_clique h hg (inR_of_mem hx) hv (Ne.symm hvx)
  have hpair : ∀ c, C2 c → ∃ a b, a ∉ S ∧ b ∉ S ∧ f a = c ∧ f b = c ∧ G.Adj x a ∧ G.Adj x b ∧
      a ≠ b ∧ a ∈ A ∧ b ∉ A ∧ ∀ w, w ∉ S → f w = c → G.Adj x w → w = a ∨ w = b := by
    intro c hc
    obtain ⟨hzS, hfz, hzadj⟩ := hzc c hc
    obtain ⟨d, hdS, hfd, hxd, hdz⟩ := hd c hc x (inR_of_mem hx)
    have hxz := hzadj x (inR_of_mem hx)
    have hall : ∀ w, w ∉ S → f w = c → G.Adj x w → w = zc c ∨ w = d := by
      intro w hw hfw hxw
      by_contra hn
      push Not at hn
      exact three h hg hxz hxd hxw hzS hdS hw (hfz.trans hfd.symm) (hfz.trans hfw.symm)
        (Ne.symm hdz) (Ne.symm hn.1) (Ne.symm hn.2)
    have e := hA (zc c) d hxz hxd (Ne.symm hdz) (nadj hg hzS hdS (hfz.trans hfd.symm))
    by_cases hzA : zc c ∈ A
    · exact ⟨zc c, d, hzS, hdS, hfz, hfd, hxz, hxd, Ne.symm hdz, hzA, e.1 hzA, hall⟩
    · have hdA : d ∈ A := by tauto
      exact ⟨d, zc c, hdS, hzS, hfd, hfz, hxd, hxz, hdz, hdA, hzA,
        fun w h1 h2 h3 => (hall w h1 h2 h3).symm⟩
  choose! pa pb hpab using hpair
  have paR : ∀ c, C2 c → ¬ InR G S f (pa c) := fun c hc hR =>
    hinvc c hc _ hR (hpab c hc).1 (hpab c hc).2.2.1
  have pbR : ∀ c, C2 c → ¬ InR G S f (pb c) := fun c hc hR =>
    hinvc c hc _ hR (hpab c hc).2.1 (hpab c hc).2.2.2.1
  have noaug : ∀ p (r : V) (cs : ℕ → ℕ), InR G S f r → r ≠ x → r ∈ A → 1 ≤ p →
      (∀ i < p, C2 (cs i)) → ¬ G.Adj r (pb (cs 0)) →
      (∀ i, i + 1 < p → ¬ G.Adj (pa (cs i)) (pb (cs (i + 1)))) →
      ∀ z, InR G S f z → z ≠ x → z ∉ A → G.Adj (pa (cs (p - 1))) z := by
    intro p
    induction p using Nat.strong_induction_on with
    | _ p IH =>
    intro r cs hr hrx hrA hp hcs h0 hstep z hz hzx hzA
    by_contra hn
    have hmin : ∀ i, 1 ≤ i → i < p → G.Adj r (pb (cs i)) := by
      intro i h1 h2
      by_contra hn'
      have := IH (p - i) (by omega) r (fun j => cs (j + i)) hr hrx hrA (by omega)
        (fun j hj => hcs _ (by omega)) (by simpa using hn')
        (fun j hj => by
          have := hstep (j + i) (by omega)
          rwa [show j + i + 1 = j + 1 + i by omega] at this) z hz hzx hzA
      simp only [show p - i - 1 + i = p - 1 by omega] at this
      exact hn this
    have hc0 := hcs 0 (by omega)
    obtain ⟨paS, pbS, fpa, fpb, xpa, xpb, papb, paA, pbA, hall⟩ := hpab _ hc0
    obtain ⟨hzS', hfz', hzadj'⟩ := hzc _ hc0
    have hw : zc (cs 0) = pa (cs 0) := by
      rcases hall _ hzS' hfz' (hzadj' x (inR_of_mem hx)) with e | e
      · exact e
      · exact absurd (e ▸ hzadj' r hr) h0
    have zpa : G.Adj z (pa (cs 0)) := hw ▸ hzadj' z hz
    obtain ⟨d, hdS, hfd, hrd, hdz⟩ := hd _ hc0 r hr
    rw [hw] at hdz
    have hdpb : d ≠ pb (cs 0) := fun e => h0 (e ▸ hrd)
    have hxz := hxR z hz hzx
    have zpb : G.Adj z (pb (cs 0)) :=
      same_side hA hxz xpb (fun e => pbR _ hc0 (e ▸ hz)) (by tauto)
    have nzd : ¬ G.Adj z d := fun e => three h hg zpa zpb e paS pbS hdS (fpa.trans fpb.symm)
      (fpa.trans hfd.symm) papb (Ne.symm hdz) (Ne.symm hdpb)
    have hzd : z ≠ d := fun e => hinvc _ hc0 d (e ▸ hz) hdS hfd
    obtain ⟨B, hB⟩ := sep_exists h.ql r
    have hxr := hxR r hr hrx
    have hra : ∀ j, j ≤ p - 1 → G.Adj r (pa (cs j)) := by
      intro j hj
      obtain ⟨-, -, -, -, xa, -, -, aA, -, -⟩ := hpab _ (hcs j (by omega))
      exact same_side hA hxr xa (fun e => paR _ (hcs j (by omega)) (e ▸ hr)) (by tauto)
    have hpar := alt hB (fun j => pa (cs j)) (fun j => pb (cs j)) (p - 1) hra
      (fun j h1 h2 => hmin j h1 (by omega))
      (fun j h1 h2 => by
        obtain ⟨-, -, -, -, -, -, -, -, bA, -⟩ := hpab _ (hcs j (by omega))
        obtain ⟨-, -, -, -, -, -, -, aA', -, -⟩ := hpab _ (hcs (j - 1) (by omega))
        have := hstep (j - 1) (by omega)
        rw [show j - 1 + 1 = j by omega] at this
        exact ⟨fun e => bA (e ▸ aA'), this⟩)
      (fun j h1 h2 => by
        obtain ⟨aS, bS, fa, fb, -, -, ab, -, -, -⟩ := hpab _ (hcs j (by omega))
        exact ⟨Ne.symm ab, nadj hg bS aS (fb.trans fa.symm)⟩)
      (p - 1) le_rfl
    have hrz : G.Adj r z := R_clique h hg hr hz (fun e => hzA (e ▸ hrA))
    have e1 := hB d (pa (cs 0)) hrd (hra 0 (by omega)) hdz
      (nadj hg hdS paS (hfd.trans fpa.symm))
    have e2 := hB (pa (cs (p - 1))) z (hra (p - 1) le_rfl) hrz
      (fun e => paR _ (hcs _ (by omega)) (e ▸ hz)) hn
    have e3 := hB z d hrz hrd hzd nzd
    tauto
  let Reach : ℕ → Prop := fun c => ∃ (r : V) (cs : ℕ → ℕ) (p : ℕ), InR G S f r ∧ r ≠ x ∧ r ∈ A ∧ 1 ≤ p ∧
    (∀ i < p, C2 (cs i)) ∧ ¬ G.Adj r (pb (cs 0)) ∧
    (∀ i, i + 1 < p → ¬ G.Adj (pa (cs i)) (pb (cs (i + 1)))) ∧ cs (p - 1) = c
  have reach_aug : ∀ c, Reach c → ∀ z, InR G S f z → z ≠ x → z ∉ A → G.Adj (pa c) z := by
    rintro c ⟨r, cs, p, hr, hrx, hrA, hp, hcs, h0, hstep, rfl⟩ z hz hzx hzA
    exact noaug p r cs hr hrx hrA hp hcs h0 hstep z hz hzx hzA
  have reach_one : ∀ r c, InR G S f r → r ≠ x → r ∈ A → C2 c → ¬ G.Adj r (pb c) → Reach c :=
    fun r c hr hrx hrA hc hn => ⟨r, fun _ => c, 1, hr, hrx, hrA, le_rfl, fun _ _ => hc, hn,
      fun i hi => by omega, rfl⟩
  have reach_ext : ∀ c c', Reach c → C2 c' → ¬ G.Adj (pa c) (pb c') → Reach c' := by
    rintro c c' ⟨r, cs, p, hr, hrx, hrA, hp, hcs, h0, hstep, rfl⟩ hc' hn
    refine ⟨r, fun i => if i < p then cs i else c', p + 1, hr, hrx, hrA, by omega, ?_, ?_, ?_, ?_⟩
    · intro i hi
      by_cases hip : i < p
      · simp only [if_pos hip]; exact hcs i hip
      · simp only [if_neg hip]; exact hc'
    · simp only [if_pos (show 0 < p by omega)]; exact h0
    · intro i hi
      by_cases hip : i + 1 < p
      · simp only [if_pos hip, if_pos (show i < p by omega)]; exact hstep i hip
      · have hi' : i = p - 1 := by omega
        subst hi'
        show ¬ G.Adj (pa (if p - 1 < p then cs (p - 1) else c'))
          (pb (if p - 1 + 1 < p then cs (p - 1 + 1) else c'))
        rw [if_pos (show p - 1 < p by omega), if_neg (show ¬ (p - 1 + 1 < p) by omega)]
        exact hn
    · simp
  let e : ℕ → V := fun c => if Reach c then pa c else pb c
  have he : ∀ c, C2 c → e c ∉ S ∧ f (e c) = c ∧ G.Adj x (e c) ∧ ¬ InR G S f (e c) := by
    intro c hc
    obtain ⟨aS, bS, fa, fb, xa, xb, -, -, -, -⟩ := hpab c hc
    by_cases hr : Reach c
    · simp only [e, if_pos hr]; exact ⟨aS, fa, xa, paR c hc⟩
    · simp only [e, if_neg hr]; exact ⟨bS, fb, xb, pbR c hc⟩
  have adjRe : ∀ r c, InR G S f r → C2 c → r ≠ e c → G.Adj r (e c) := by
    intro r c hr hc hne
    by_cases hrx : r = x
    · rw [hrx]; exact (he c hc).2.2.1
    have hxr := hxR r hr hrx
    obtain ⟨-, -, -, -, xa, xb, -, aA, bA, -⟩ := hpab c hc
    by_cases hR : Reach c
    · have hec : e c = pa c := by simp only [e, if_pos hR]
      rw [hec] at hne ⊢
      by_cases hrA : r ∈ A
      · exact same_side hA hxr xa hne (by tauto)
      · exact (reach_aug c hR r hr hrx hrA).symm
    · have hec : e c = pb c := by simp only [e, if_neg hR]
      rw [hec] at hne ⊢
      by_cases hrA : r ∈ A
      · by_contra hn; exact hR (reach_one r c hr hrx hrA hc hn)
      · exact same_side hA hxr xb hne (by tauto)
  have adjee : ∀ c c', C2 c → C2 c' → c ≠ c' → G.Adj (e c) (e c') := by
    intro c c' hc hc' hcc
    have hne : e c ≠ e c' := fun q => hcc (by rw [← (he c hc).2.1, ← (he c' hc').2.1, q])
    obtain ⟨-, -, -, -, xa, xb, -, aA, bA, -⟩ := hpab c hc
    obtain ⟨-, -, -, -, xa', xb', -, aA', bA', -⟩ := hpab c' hc'
    by_cases hR : Reach c <;> by_cases hR' : Reach c'
    · have h1 : e c = pa c := by simp only [e, if_pos hR]
      have h2 : e c' = pa c' := by simp only [e, if_pos hR']
      rw [h1, h2] at hne ⊢
      exact same_side hA xa xa' hne (by tauto)
    · have h1 : e c = pa c := by simp only [e, if_pos hR]
      have h2 : e c' = pb c' := by simp only [e, if_neg hR']
      rw [h1, h2]
      by_contra hn; exact hR' (reach_ext c c' hR hc' hn)
    · have h1 : e c = pb c := by simp only [e, if_neg hR]
      have h2 : e c' = pa c' := by simp only [e, if_pos hR']
      rw [h1, h2]
      by_contra hn; exact hR (reach_ext c' c hR' hc (fun q => hn q.symm))
    · have h1 : e c = pb c := by simp only [e, if_neg hR]
      have h2 : e c' = pb c' := by simp only [e, if_neg hR']
      rw [h1, h2] at hne ⊢
      exact same_side hA xb xb' hne (by tauto)
  let C2s : Finset ℕ := (Finset.range T).filter (fun c => c ∉ C1)
  have hC2s : ∀ c, c ∈ C2s ↔ C2 c := fun c => by simp [C2s, C2]
  let K : Finset V := Rf ∪ C2s.image e
  have hK : G.IsClique (K : Set V) := by
    intro u hu v hv huv
    simp only [K, Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image,
      Finset.mem_coe] at hu hv
    rcases hu with hu | ⟨c, hc, rfl⟩ <;> rcases hv with hv | ⟨c', hc', rfl⟩
    · exact R_clique h hg (by simpa [Rf] using hu) (by simpa [Rf] using hv) huv
    · exact adjRe u c' (by simpa [Rf] using hu) ((hC2s c').1 hc') huv
    · exact (adjRe v c (by simpa [Rf] using hv) ((hC2s c).1 hc) (Ne.symm huv)).symm
    · exact adjee c c' ((hC2s c).1 hc) ((hC2s c').1 hc') (fun q => huv (q ▸ rfl))
  have hdisj : Disjoint Rf (C2s.image e) := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hv'
    exact (he c ((hC2s c).1 hc)).2.2.2 (by simpa [Rf] using hv)
  have hcard1 : (C2s.image e).card = C2s.card := Finset.card_image_of_injOn (by
    intro c hc c' hc' q
    rw [← (he c ((hC2s c).1 hc)).2.1, ← (he c' ((hC2s c').1 hc')).2.1]
    exact congrArg f q)
  have hcard2 : (Rf.filter (fun v => v ∉ S)).card = C1.card := (Finset.card_image_of_injOn (by
    intro u hu v hv q
    by_contra hne
    simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and, Rf,
      Set.mem_ofPred_eq] at hu hv
    exact hg.2.2.2 u v hu.2 hv.2 (R_clique h hg hu.1 hv.1 hne) q)).symm
  have hcard3 : (Rf.filter (fun v => v ∈ S)).card = s := by
    rw [← hg.2.1]
    congr 1
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Rf]
    exact ⟨fun hv => hv.2, fun hv => ⟨inR_of_mem hv, hv⟩⟩
  have hcard4 : ((Finset.range T).filter (fun c => c ∈ C1)) = C1 := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨fun hc => hc.2, fun hc => ⟨?_, hc⟩⟩
    obtain ⟨v, -, hvS, rfl⟩ := (hC1 c).1 hc
    exact hg.2.2.1 v hvS
  have hR := Finset.card_filter_add_card_filter_not (s := Rf) (fun v => v ∈ S)
  have hT := Finset.card_filter_add_card_filter_not (s := Finset.range T) (fun c => c ∈ C1)
  rw [hcard4, Finset.card_range] at hT
  have hKc : K.card = s + T := by
    rw [Finset.card_union_of_disjoint hdisj, hcard1, ← hR, hcard3, hcard2]
    simp only [C2s]
    omega
  exact h.cf K ⟨hK, hKc⟩

lemma cl_lt {n : ℕ} (hcf : G.CliqueFree n) {t : Finset V} (ht : G.IsClique (t : Set V)) :
    t.card < n := by
  by_contra hn
  push Not at hn
  obtain ⟨u, hut, hu⟩ := Finset.exists_subset_card_eq hn
  exact hcf u ⟨IsClique.subset (Finset.coe_subset.2 hut) ht, hu⟩

lemma nbr_bound (hql : QL G) (hcf : G.CliqueFree s) (v : V) (t : Finset V)
    (ht : ∀ u ∈ t, G.Adj v u) : t.card ≤ 2 * (s - 2) := by
  classical
  obtain ⟨A, B, hAB, hA, hB⟩ := hql v
  have key : ∀ C : Set V, G.IsClique C → ∀ t' : Finset V, (∀ u ∈ t', G.Adj v u ∧ u ∈ C) →
      t'.card ≤ s - 2 := by
    intro C hC t' ht'
    have hvt : v ∉ t' := fun hv => G.irrefl (ht' v hv).1
    have hcl : G.IsClique ((insert v t' : Finset V) : Set V) := by
      rw [Finset.coe_insert]
      exact IsClique.insert (hC.subset (fun u hu => (ht' u (Finset.mem_coe.1 hu)).2))
        (fun u hu _ => (ht' u (Finset.mem_coe.1 hu)).1)
    have := cl_lt hcf hcl
    rw [Finset.card_insert_of_notMem hvt] at this
    omega
  have h1 := key A hA (t.filter (fun u => u ∈ A)) (fun u hu => by
    rw [Finset.mem_filter] at hu
    exact ⟨ht u hu.1, hu.2⟩)
  have h2 := key B hB (t.filter (fun u => u ∉ A)) (fun u hu => by
    rw [Finset.mem_filter] at hu
    refine ⟨ht u hu.1, ?_⟩
    have : u ∈ A ∪ B := by rw [hAB]; exact ht u hu.1
    rcases this with h | h
    · exact absurd h hu.2
    · exact h)
  have := Finset.card_filter_add_card_filter_not (s := t) (fun u => u ∈ A)
  omega

lemma greedy (D : ℕ) (hD : ∀ v (t : Finset V), (∀ u ∈ t, G.Adj v u) → t.card ≤ D)
    (W : Finset V) :
    ∃ c : V → ℕ, (∀ v, c v ≤ D) ∧ ∀ u ∈ W, ∀ v ∈ W, G.Adj u v → c u ≠ c v := by
  classical
  induction W using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, fun _ => Nat.zero_le _, fun u hu => absurd hu (Finset.notMem_empty u)⟩
  | @insert a W haW ih =>
    obtain ⟨c, hcD, hc⟩ := ih
    have hlt : ((W.filter (fun u => G.Adj a u)).image c).card < (Finset.range (D + 1)).card := by
      rw [Finset.card_range]
      have := hD a (W.filter (fun u => G.Adj a u)) (fun u hu => (Finset.mem_filter.1 hu).2)
      have := Finset.card_image_le (s := W.filter (fun u => G.Adj a u)) (f := c)
      omega
    obtain ⟨m, hm, hmn⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    have key : ∀ u ∈ W, G.Adj a u → m ≠ c u := fun u hu hau e =>
      hmn (Finset.mem_image.2 ⟨u, Finset.mem_filter.2 ⟨hu, hau⟩, e.symm⟩)
    have hne : ∀ w ∈ W, w ≠ a := fun w hw e => haW (e ▸ hw)
    refine ⟨Function.update c a m, fun v => ?_, ?_⟩
    · by_cases hv : v = a
      · rw [hv, Function.update_self]; exact Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
      · rw [Function.update_of_ne hv]; exact hcD v
    · intro u hu v hv huv
      rw [Finset.mem_insert] at hu hv
      rcases hu with hu | hu <;> rcases hv with hv | hv
      · exact absurd (hu.trans hv.symm) huv.ne
      · rw [hu, Function.update_self, Function.update_of_ne (hne v hv)]
        exact key v hv (hu ▸ huv)
      · rw [hv, Function.update_self, Function.update_of_ne (hne u hu)]
        exact (key u hu (hv ▸ huv.symm)).symm
      · rw [Function.update_of_ne (hne u hu), Function.update_of_ne (hne v hv)]
        exact hc u hu v hv huv

lemma clique_chrom [Fintype V] (S : Finset V) (hS : G.IsClique (S : Set V)) :
    (S.card : ℕ∞) ≤ (G.induce (S : Set V)).chromaticNumber := by
  have hcl : (G.induce (S : Set V)).IsClique
      ((Finset.univ : Finset (S : Set V)) : Set (S : Set V)) := by
    intro u _ v _ huv
    exact hS u.2 v.2 (fun e => huv (Subtype.ext e))
  have := hcl.card_le_chromaticNumber
  simpa using this

lemma main_le [Fintype V] (hq : IsQuasiLineGraph G) {k : ℕ}
    (hχ : G.chromaticNumber = (k : ℕ∞)) (hcf : G.CliqueFree k) {a b : ℕ} (ha : 2 ≤ a)
    (hle : a ≤ b) (hab : a + b = k + 1) :
    ∃ s : Set V, (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞) := by
  classical
  by_contra hne
  push Not at hne
  have hql : QL G := hq
  have nocol : ∀ c : V → ℕ, (∀ v, c v < a + (b - 1) - 1) → ∃ u v, G.Adj u v ∧ c u = c v := by
    intro c hc
    by_contra hn
    push Not at hn
    have hcol : G.Colorable (k - 1) :=
      ⟨Coloring.mk (fun v => (⟨c v, by have := hc v; omega⟩ : Fin (k - 1)))
        (fun {u v} huv e => hn u v huv (congrArg Fin.val e))⟩
    have := hcol.chromaticNumber_le
    rw [hχ] at this
    have : k ≤ k - 1 := by exact_mod_cast this
    omega
  have hns : ∀ S : Finset V, G.IsClique (S : Set V) → S.card = a →
      ∃ f, Good G a (b - 1) S f := by
    intro S hS hSc
    have h1 := hne (S : Set V) (by rw [← hSc]; exact clique_chrom S hS)
    have h2 : (G.induce (S : Set V)ᶜ).Colorable (b - 1) := by
      rw [← chromaticNumber_le_iff_colorable]
      have hb' : (b : ℕ∞) = ((b - 1 : ℕ) : ℕ∞) + 1 := by norm_cast; omega
      rw [hb'] at h1
      exact Order.le_of_lt_add_one h1
    obtain ⟨C⟩ := h2
    refine ⟨fun v => if hv : v ∈ (S : Set V)ᶜ then ((C ⟨v, hv⟩ : Fin (b - 1)) : ℕ) else 0,
      hS, hSc, ?_, ?_⟩
    · intro v hv
      simp [hv]
    · intro u v hu hv huv e
      simp [hu, hv] at e
      exact C.valid (show (G.induce (S : Set V)ᶜ).Adj ⟨u, hu⟩ ⟨v, hv⟩ from huv) (Fin.ext e)
  have hcf' : G.CliqueFree (a + (b - 1)) := by rwa [show a + (b - 1) = k by omega]
  have hH : Hyp G a (b - 1) := ⟨ha, hql, nocol, hcf', hns⟩
  have hS0 : ∃ S : Finset V, G.IsClique (S : Set V) ∧ S.card = a := by
    by_contra hn
    push Not at hn
    have hcfa : G.CliqueFree a := fun t ht => hn t ht.isClique ht.card_eq
    obtain ⟨c, hcD, hc⟩ := greedy (2 * (a - 2)) (nbr_bound hql hcfa) Finset.univ
    obtain ⟨u, v, huv, e⟩ := nocol c (fun v => by have := hcD v; omega)
    exact hc u (Finset.mem_univ _) v (Finset.mem_univ _) huv e
  obtain ⟨S0, hS0, hS0c⟩ := hS0
  obtain ⟨f, hf⟩ := hns S0 hS0 hS0c
  exact core hH hf

end OMA.Erdos628QL

theorem OMA.solution : type_of% @Erdos628.erdos_628.variants.quasi_line := by
  classical
  intro V _ G _ hq k hχ hcf a b ha hb hab
  rcases le_total a b with h | h
  · exact OMA.Erdos628QL.main_le hq hχ hcf ha h hab
  · obtain ⟨s, hs1, hs2⟩ := OMA.Erdos628QL.main_le hq hχ hcf hb h (by omega)
    exact ⟨sᶜ, hs2, by rw [compl_compl]; exact hs1⟩
