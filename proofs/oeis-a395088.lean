import OMAStatements.S_oeis_a395088

namespace OMA.S_oeis_a395088

lemma expand_append (u v : List Bool) : expand (u++v) = expand u ++ expand v := by
  simp [expand]

lemma growth (t : ℕ) : ∃ c cs, stage (t+1) = stage t ++ c :: cs := by
  induction t with
  | zero => exact ⟨true, [true], rfl⟩
  | succ t ih =>
    obtain ⟨c, cs, h⟩ := ih
    change ∃ b bs, expand (stage (t+1)) = expand (stage t) ++ b :: bs
    rw [h, expand_append]
    cases c
    · exact ⟨false, true :: true :: expand cs, rfl⟩
    · exact ⟨false, expand cs, rfl⟩

lemma extend {u : List Bool} (hu : LimitPrefix u) :
    ∃ b, LimitPrefix (u ++ [b]) := by
  obtain ⟨t, v, hv⟩ := hu
  obtain ⟨b, bs, hb⟩ := growth t
  cases v with
  | nil =>
    simp at hv
    exact ⟨b, t+1, bs, by simp [hb, ← hv]⟩
  | cons c cs => exact ⟨c, t, cs, by simpa [List.append_assoc] using hv⟩

lemma double_expand (u : List Bool) :
    expand (expand u) ++ [false, true, true] = predicted u := by
  induction u with
  | nil => rfl
  | cons b bs ih =>
    rw [show b :: bs = [b] ++ bs from rfl, expand_append]
    rw [expand_append, List.append_assoc, ih]
    cases b <;> rfl

lemma predicted_prefix {u : List Bool} (hu : LimitPrefix u) :
    LimitPrefix (predicted u) := by
  obtain ⟨b, t, v, hv⟩ := extend hu
  refine ⟨t+2, ?_⟩
  change predicted u <+: expand (expand (stage t))
  rw [← hv, expand_append, expand_append, expand_append, expand_append, ← double_expand]
  cases b
  · exact ⟨[false, false] ++ expand (expand v), by simp [expand, List.append_assoc]⟩
  · exact ⟨expand (expand v), by simp [expand, List.append_assoc]⟩

theorem solution :
    (∀ n : ℕ, ∃ u : List Bool, u.length = n ∧ LimitPrefix u) ∧
    (∀ u : List Bool, LimitPrefix u → LimitPrefix (predicted u)) := by
  refine ⟨?_, fun _ => predicted_prefix⟩
  intro n
  induction n with
  | zero => exact ⟨[], rfl, 0, [false], rfl⟩
  | succ n ih =>
    obtain ⟨u, hl, hu⟩ := ih
    obtain ⟨b, hb⟩ := extend hu
    exact ⟨u++[b], by simp [hl], hb⟩

lemma stage_prefix {i j : ℕ} (h : i≤j) : stage i <+: stage j := by
  induction h with
  | refl => exact List.prefix_rfl
  | @step j _ ih =>
    obtain ⟨b,bs,hb⟩ := growth j
    exact ih.trans ⟨b::bs,hb.symm⟩

lemma stage_long (i : ℕ) : i < (stage i).length := by
  induction i with
  | zero => decide
  | succ i ih =>
    obtain ⟨b,bs,h⟩ := growth i
    rw [h,List.length_append,List.length_cons]
    omega

def bit (i : ℕ) : Bool := (stage i)[i]'(stage_long i)

lemma bit_of_prefix {u : List Bool} (h : LimitPrefix u) {i : ℕ} (hi : i<u.length) :
    bit i = u[i] := by
  obtain ⟨t,ht⟩ := h
  let k := max i t
  have h1 : stage i <+: stage k := stage_prefix (le_max_left _ _)
  have h2 : u <+: stage k := ht.trans (stage_prefix (le_max_right _ _))
  exact (h1.getElem (stage_long i)).trans (h2.getElem hi).symm

def firstBits (n : ℕ) : List Bool := List.ofFn fun i : Fin n => bit i

lemma firstBits_limit (n : ℕ) : LimitPrefix (firstBits n) := by
  obtain ⟨u,hl,hu⟩ := solution.1 n
  have he : firstBits n = u := by
    apply List.ext_getElem
    · simp [firstBits,hl]
    · intro i hi hj
      simpa [firstBits] using bit_of_prefix hu hj
  exact he ▸ hu

def zeroLength (i : ℕ) : ℕ := if bit i then 1 else 3

def zeroStart (i : ℕ) : ℕ := (predicted (firstBits i)).length

lemma next_prefix (i : ℕ) : predicted (firstBits (i+1)) =
    predicted (firstBits i) ++ (List.replicate (zeroLength i) false ++ [true,true]) := by
  have h : firstBits (i+1) = firstBits i ++ [bit i] := List.ofFn_succ_last
  rw [h]
  simp [predicted,zeroLength]

lemma appended_bits {u v : List Bool} (hu : LimitPrefix (u++v)) {i : ℕ} (hi : i<v.length) :
    bit (u.length+i) = v[i] := by
  have hb := bit_of_prefix hu (show u.length+i<(u++v).length by simp;omega)
  rw [List.getElem_append_right (by omega)] at hb
  simpa using hb

theorem all_runs :
    bit 0=false ∧ bit 1=true ∧ bit 2=true ∧ zeroStart 0=3 ∧
    ∀ i, zeroStart (i+1)=zeroStart i+zeroLength i+2 ∧
      (∀ j<zeroLength i, bit (zeroStart i+j)=false) ∧
      bit (zeroStart i+zeroLength i)=true ∧ bit (zeroStart i+zeroLength i+1)=true := by
  refine ⟨by decide,by decide,by decide,by decide,?_⟩
  intro i
  have hp := predicted_prefix (firstBits_limit (i+1))
  rw [next_prefix] at hp
  have atBit {k : ℕ} (hk : k < ((List.replicate (zeroLength i) false)++[true,true]).length) :
      bit (zeroStart i+k) = ((List.replicate (zeroLength i) false)++[true,true])[k] :=
    appended_bits hp hk
  refine ⟨?_,?_,?_,?_⟩
  · simp [zeroStart,next_prefix,Nat.add_assoc]
  · intro j hj
    rw [atBit (by simp;omega),List.getElem_append_left (by simpa using hj)]
    simp
  · rw [atBit (by simp),List.getElem_append_right (by simp)]
    simp
  · rw [Nat.add_assoc,atBit (by simp),List.getElem_append_right (by simp)]
    simp

end OMA.S_oeis_a395088

theorem OMA.solution : type_of% @OMA.S_oeis_a395088.main :=
  OMA.S_oeis_a395088.solution
