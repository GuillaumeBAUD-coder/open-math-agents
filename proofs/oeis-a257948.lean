import OMAStatements.S_oeis_a257948
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a257948

/-- Sum of squares of the last `f` base-100 digits. -/
def a257sqf (f : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0)
    (fun _ ih n => n % 100 * (n % 100) + ih (n / 100)) f

/-- The map on numbers below 10^6. -/
def a257t (n : ℕ) : ℕ := a257sqf 3 n

theorem a257_s2_zero : s2 0 = 0 := by simp [s2]

theorem a257_s2_step (n : ℕ) : s2 n = n % 100 * (n % 100) + s2 (n / 100) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [a257_s2_zero]
  · unfold s2
    rw [Nat.digits_def' (by norm_num) hn, List.map_cons, List.sum_cons, pow_two]

theorem a257_s2_eq_sqf : ∀ f n, n < 100 ^ f → s2 n = a257sqf f n := by
  intro f
  induction f with
  | zero =>
    intro n h
    have : n = 0 := by simpa using h
    subst this
    rw [a257_s2_zero]
    rfl
  | succ f ih =>
    intro n h
    rw [a257_s2_step, ih (n / 100) (by rw [pow_succ] at h; omega)]
    rfl

theorem a257_t_lt (n : ℕ) : a257t n < 1000000 := by
  show n % 100 * (n % 100) + (n / 100 % 100 * (n / 100 % 100) +
    (n / 100 / 100 % 100 * (n / 100 / 100 % 100) + 0)) < 1000000
  have h1 : n % 100 < 100 := Nat.mod_lt _ (by norm_num)
  have h2 : n / 100 % 100 < 100 := Nat.mod_lt _ (by norm_num)
  have h3 : n / 100 / 100 % 100 < 100 := Nat.mod_lt _ (by norm_num)
  have e1 : n % 100 * (n % 100) ≤ 99 * 99 := Nat.mul_le_mul (by omega) (by omega)
  have e2 : n / 100 % 100 * (n / 100 % 100) ≤ 99 * 99 := Nat.mul_le_mul (by omega) (by omega)
  have e3 : n / 100 / 100 % 100 * (n / 100 / 100 % 100) ≤ 99 * 99 :=
    Nat.mul_le_mul (by omega) (by omega)
  omega

theorem a257_s2_eq_t (n : ℕ) (h : n < 1000000) : s2 n = a257t n :=
  a257_s2_eq_sqf 3 n (lt_of_lt_of_eq h (by norm_num))

theorem a257_iter_eq : ∀ k x, x < 1000000 → s2^[k] x = a257t^[k] x := by
  intro k
  induction k with
  | zero => intro x _; rfl
  | succ k ih =>
    intro x hx
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, a257_s2_eq_t x hx]
    exact ih _ (a257_t_lt x)

/-- Kernel-friendly iteration of `a257t`. -/
def a257it (k x : ℕ) : ℕ := Nat.rec (motive := fun _ => ℕ) x (fun _ ih => a257t ih) k

theorem a257_it_eq (k x : ℕ) : a257it k x = a257t^[k] x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    show a257t (a257it k x) = _
    rw [ih]

/-- Bitmask of all periodic points of `s2` (fixed points and cycle members). -/
def a257cm : ℕ := 1412147001678587962629955708286847482488618757493653153952065858139975435168374256582702133676827803425007429919460805394293182001769983828114700886931176081199454804949870017675701784904809951761374188893610476417804473056674245275405950170594606781628928263287872362748708262456101640569920469025721632656642320334920996837358515341459358345275788228482333617888149293803704786002231883786925888067461617712318156753296817829746016341445026934515087075389421211157570062721559911901198905749281518502482007858290606473228457830108569856284789599768573377333461656232174765188423863659534313987255605687310649249525397720232799353890001273358021265036413476180133532028269906140560898800235706112864392801515885256853070956477857638956991278806016101186104069873643377804070855210796070853930955541779720079878365359115161707989768089806314465138476437976635142945328602224576622871780165636623855618953327736747869397652847882251479066572913809230167600755357062162892292946697058004496210542712510518174457688904081044968787219696291621096017883231842638538459956699936872971506291864211046234813624391854189910005196533376976343868641830981707892654039931518511206166537656061998906504293504772531097358365995670742677621662969856443826502878484865296466734412832703760300930868804143214459142979841142287971649049161931015067556386831557126533259027986812587410537833346414864477105707533345903322807537222922771081414988501144452197055338980000389499205969127106446561752294292084285714296498639976663675159540031129323612995336561603884047976314229701333131667136983190166374776151625502957068224698795378827862487065697052110613088623458551610902563756246558507669603195852521800654889389896095323962016687941425870250140784681039930264360306418040602622726526871334304596801965998158515552817147533124931461765492594319523804406207901897077017742863799684166134989273627544263910206575720490930381178021915990861496595650649166054408172394782177832616204987193764352935631683186064021359374083286781824744615794281543246721271680076695568283843150188642359059228266713491178819263662998272591776256752923770061381540482214465790993589074781826185418544724587467838001418019138060473368537692152826145164607806131837370751706730326693726108339290316452777879473640574262242673642330064193129354819840443207971128798605006633076091213412595859803901540507148329349621733883704313158755408012240464127517249288768751934323711830008314170076712461797739064686542048118529338758836125509843928600155274709155862176818587015975663201842163763470110829254182537064551982555057685285210420202879929343841280290059486411624043625517203871496703697083032033460456925864738743565219993256133766225772698882804582455132188209391395649617589345633187725694920018324488313060444899563427271067578926718956086977837902559410482248176833441188836140245760059831099355455441742336425113197082797677367290040955531535244654917857180914748396139221193834432828644982176143071115521918830693867427293131611499169310841101498139003850954085823325861631168666181468880814653473912094034691978114980808888931590866335752720853275721061630351385404510685692791273403318903209497228777694718807146388576386742737521110221472110941885238797554052592936219186360712750703955085716415607441716358894326859773756614322287501288692845742887748520270909672733295126491060860896927072019072119959989960666656860460596986383535942107650316973415026759128230565032417828236120531865993292127261041442142917956976885142807445967778952615139349032695889134956695179301022198311736060104166499773302531651107874478128132968362666353189300171362590299770354726758439340445200655585835486452513458568218158759893818811878009608878097215504941809946360737052238352522456805554968130624296181249909534375190784918386500404182697825180994823777896861978099573763256748352748403372647236404822157204316989884473409264519841917399441065394646819975310574043582568845037233249982556877534552044028154507777777247226704350103037982815722538628882658057569622165042134898772686698974003827811941050307130399112944603549160084805862008815560873448722062390484620390697732443071971156517175374495790537264280576975888973707029847643943278786619477100221414251091422705465564963896636712707949907500440358726760541257557276835571599152347581935080596916461673307310757626605353952491301459975355714529132231432660980511385077900296863473717740091858636737841453915400541789862601873064614695808651469833001035412533995594619443989499762548608393250891783649167337750812722939848783731229027544635189166144380280738011504977684100124298144805352876129383844688858680267738146018755577992460649328925890861031572838375623149068843652724278743465795166694070449611040142990537644892745865571782580961766591179582892621520674197913463162198576103495525878554566146863681777646483071359729851189496662509639172099

def a257good (x : ℕ) : Bool := Nat.beq (Nat.shiftRight a257cm x % 2) 1

theorem a257_good_lt (x : ℕ) (h : a257good x = true) : x < 16384 := by
  by_contra hx'
  have hx : 16384 ≤ x := by omega
  have hc : a257cm < 2 ^ 16384 := by decide +kernel
  have h0 : Nat.shiftRight a257cm x = 0 := by
    show a257cm >>> x = 0
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt (lt_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num) hx))
  unfold a257good at h
  rw [h0] at h
  exact absurd h (by decide)

def a257csL : List (List ℕ) := [
  [3869, 6205],
  [5965, 7706],
  [3460, 4756, 5345, 4834],
  [1781, 6850, 7124, 5617, 3425],
  [3770, 6269, 8605, 7421, 5917],
  [4973, 7730, 6829, 5465, 7141, 6722],
  [1268, 4768, 6833, 5713, 3418, 1480, 6596, 13441, 2838, 2228],
  [1946, 2477, 6505, 4250, 4264, 5860, 6964, 8857, 10993, 8731, 8530, 8125, 7186, 12437],
  [37, 1369, 4930, 3301, 1090, 8200, 6724, 5065, 6725, 5114, 2797, 10138, 1446, 2312, 673, 5365, 7034, 6056, 6736, 5785, 10474, 5493, 11565, 4451, 4537, 3394, 9925, 10426, 693, 8685, 14621, 2558, 3989, 9442, 10600],
  [41, 1681, 6817, 4913, 2570, 5525, 3650, 3796, 10585, 7251, 7785, 13154, 3878, 7528, 6409, 4177, 7610, 5876, 9140, 9881, 16165, 7947, 8450, 9556, 12161, 4163, 5650, 5636, 4432, 2960, 4441, 3617, 1585, 7450, 7976, 12017, 690, 8136, 7857, 9333, 9738, 10853, 2874, 6260, 7444, 7412, 5620, 3536, 2521, 1066, 4456, 5072, 7684, 12832, 1809, 405]]
/-- Membership test in a list. -/
def a257mem (l : List ℕ) (x : ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ ih => Nat.beq a x || ih) l

theorem a257_mem_sound (x : ℕ) : ∀ l, a257mem l x = true → x ∈ l := by
  intro l
  induction l with
  | nil => intro h; exact absurd h Bool.false_ne_true
  | cons a l ih =>
    intro h
    have h' : (Nat.beq a x || a257mem l x) = true := h
    rw [Bool.or_eq_true] at h'
    rcases h' with h' | h'
    · rw [Nat.eq_of_beq_eq_true h']
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h')

/-- Range checker: `p` holds on `[lo, lo + 2^d)`. -/
def a257chk (p : ℕ → Bool) (d : ℕ) : ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → Bool) (fun lo => p lo)
    (fun d ih lo => ih lo && ih (lo + 2 ^ d)) d

theorem a257_chk_sound (p : ℕ → Bool) : ∀ d lo, a257chk p d lo = true →
    ∀ x, lo ≤ x → x < lo + 2 ^ d → p x = true := by
  intro d
  induction d with
  | zero =>
    intro lo h x h1 h2
    have : x = lo := by simp at h2; omega
    subst this
    exact h
  | succ d ih =>
    intro lo h x h1 h2
    have h' : (a257chk p d lo && a257chk p d (lo + 2 ^ d)) = true := h
    rw [Bool.and_eq_true] at h'
    rw [pow_succ] at h2
    by_cases hx : x < lo + 2 ^ d
    · exact ih lo h'.1 x h1 hx
    · exact ih (lo + 2 ^ d) h'.2 x (by omega) (by omega)

/-- The properties of each periodic point. -/
def a257pC (x : ℕ) : Bool :=
  !a257good x || (a257good (a257t x) && Nat.beq (a257it 840 x) x &&
    (Nat.beq (a257t x) x || a257mem a257csL.flatten x))

theorem a257_K1 : a257chk a257pC 14 0 = true := by decide +kernel

/-- From `x`, a periodic point is reached within `f` steps. -/
def a257reach (f : ℕ) : ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → Bool) (fun x => a257good x)
    (fun _ ih x => a257good x || ih (a257t x)) f

theorem a257_reach_sound : ∀ f x, a257reach f x = true → ∃ k, a257good (a257t^[k] x) = true := by
  intro f
  induction f with
  | zero => intro x h; exact ⟨0, h⟩
  | succ f ih =>
    intro x h
    have h' : (a257good x || a257reach f (a257t x)) = true := h
    rw [Bool.or_eq_true] at h'
    rcases h' with h' | h'
    · exact ⟨0, h'⟩
    · obtain ⟨k, hk⟩ := ih _ h'
      exact ⟨k + 1, by rw [Function.iterate_succ_apply]; exact hk⟩

theorem a257_K2a : a257chk (a257reach 70) 12 0 = true := by decide +kernel
theorem a257_K2b : a257chk (a257reach 70) 12 4096 = true := by decide +kernel
theorem a257_K2c : a257chk (a257reach 70) 12 8192 = true := by decide +kernel

end OMA.Helpers

namespace OMA.Helpers

open OMA.S_oeis_a257948

theorem a257_s2_small (b : ℕ) (hb : b < 100) : s2 b = b * b := by
  rw [a257_s2_step, Nat.mod_eq_of_lt hb, Nat.div_eq_of_lt hb, a257_s2_zero, add_zero]

theorem a257_s2_lt (n : ℕ) (hn : 10000 ≤ n) : s2 n < n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [a257_s2_step n]
    have hr : n % 100 < 100 := Nat.mod_lt _ (by norm_num)
    have hq := Nat.div_add_mod n 100
    have hrr : n % 100 * (n % 100) ≤ 99 * (n % 100) := Nat.mul_le_mul_right _ (by omega)
    by_cases hq1 : 10000 ≤ n / 100
    · have := ih (n / 100) (by omega) hq1
      omega
    · rw [a257_s2_step (n / 100), a257_s2_small (n / 100 / 100) (by omega)]
      have hc : n / 100 % 100 < 100 := Nat.mod_lt _ (by norm_num)
      have hcc : n / 100 % 100 * (n / 100 % 100) ≤ 99 * (n / 100 % 100) :=
        Nat.mul_le_mul_right _ (by omega)
      have hbb : n / 100 / 100 * (n / 100 / 100) ≤ 99 * (n / 100 / 100) :=
        Nat.mul_le_mul_right _ (by omega)
      have hq2 := Nat.div_add_mod (n / 100) 100
      omega

theorem a257_descend (n : ℕ) : ∃ j, s2^[j] n < 10000 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n < 10000
    · exact ⟨0, h⟩
    · obtain ⟨j, hj⟩ := ih (s2 n) (a257_s2_lt n (by omega))
      exact ⟨j + 1, by rw [Function.iterate_succ_apply]; exact hj⟩

theorem a257_reach_small (y : ℕ) (hy : y < 12288) : a257reach 70 y = true := by
  by_cases h1 : y < 4096
  · exact a257_chk_sound _ 12 0 a257_K2a y (Nat.zero_le _) (by norm_num; omega)
  · by_cases h2 : y < 8192
    · exact a257_chk_sound _ 12 4096 a257_K2b y (by omega) (by norm_num; omega)
    · exact a257_chk_sound _ 12 8192 a257_K2c y (by omega) (by norm_num; omega)

theorem a257_ent (n : ℕ) : ∃ k, a257good (s2^[k] n) = true := by
  obtain ⟨j, hj⟩ := a257_descend n
  obtain ⟨k, hk⟩ := a257_reach_sound 70 (s2^[j] n) (a257_reach_small (s2^[j] n) (by omega))
  refine ⟨k + j, ?_⟩
  rw [Function.iterate_add_apply, a257_iter_eq k _ (by omega)]
  exact hk

theorem a257_goodC (x : ℕ) (h : a257good x = true) :
    a257good (s2 x) = true ∧ s2^[840] x = x ∧ (s2 x = x ∨ x ∈ a257csL.flatten) := by
  have hx := a257_good_lt x h
  have hp := a257_chk_sound a257pC 14 0 a257_K1 x (Nat.zero_le _) (by norm_num; omega)
  have hx6 : x < 1000000 := by omega
  rw [a257_s2_eq_t x hx6, a257_iter_eq 840 x hx6, ← a257_it_eq]
  unfold a257pC at hp
  rw [h] at hp
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true] at hp
  obtain ⟨⟨h1, h2⟩, h3⟩ := hp
  refine ⟨h1, Nat.eq_of_beq_eq_true h2, ?_⟩
  rcases h3 with h3 | h3
  · exact Or.inl (Nat.eq_of_beq_eq_true h3)
  · exact Or.inr (a257_mem_sound x _ h3)

theorem a257_goodIter : ∀ k x, a257good x = true → a257good (s2^[k] x) = true := by
  intro k
  induction k with
  | zero => intro x h; exact h
  | succ k ih =>
    intro x h
    rw [Function.iterate_succ_apply]
    exact ih _ (a257_goodC x h).1

theorem a257_cyc_t : ∀ c ∈ a257csL, c ≠ [] ∧ c.Nodup ∧ c.map a257t = c.rotate 1 ∧
    ∀ x ∈ c, x < 1000000 := by decide +kernel

theorem a257_nodup : a257csL.flatten.Nodup := by decide +kernel

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a257948.main := by
  refine ⟨fun n => ?_, OMA.Helpers.a257csL, rfl, ?_, OMA.Helpers.a257_nodup, ?_⟩
  · obtain ⟨k, hk⟩ := OMA.Helpers.a257_ent n
    refine ⟨k, 840, by norm_num, ?_⟩
    rw [add_comm, Function.iterate_add_apply]
    exact (OMA.Helpers.a257_goodC _ hk).2.1
  · intro c hc
    obtain ⟨h1, h2, h3, h4⟩ := OMA.Helpers.a257_cyc_t c hc
    refine ⟨h1, h2, ?_⟩
    rw [← h3]
    apply List.map_congr_left
    intro x hx
    exact OMA.Helpers.a257_s2_eq_t x (h4 x hx)
  · rintro n ⟨m, hm, hper⟩ hne
    obtain ⟨k, hk⟩ := OMA.Helpers.a257_ent n
    have hp : Function.IsPeriodicPt OMA.S_oeis_a257948.s2 (m * k) n :=
      (show Function.IsPeriodicPt OMA.S_oeis_a257948.s2 m n from hper).mul_const k
    have hle : k ≤ m * k := Nat.le_mul_of_pos_left k hm
    have e : OMA.S_oeis_a257948.s2^[m * k] n =
        OMA.S_oeis_a257948.s2^[m * k - k] (OMA.S_oeis_a257948.s2^[k] n) := by
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel hle]
    have hg : OMA.Helpers.a257good n = true := by
      have := OMA.Helpers.a257_goodIter (m * k - k) _ hk
      rw [← e, show OMA.S_oeis_a257948.s2^[m * k] n = n from hp] at this
      exact this
    rcases (OMA.Helpers.a257_goodC n hg).2.2 with h | h
    · exact absurd h hne
    · exact h
