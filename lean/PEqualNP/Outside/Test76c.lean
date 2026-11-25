import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Test76c

open PEqualNP.CircuitLowerBounds

/-! ## Bit-parallel truth tables (from `PEqualNP.MetaComplexity.Helpers.TableSearch`) -/

/-- The table of one gate, from the tables of the wires it reads. -/
def gt (M : ℕ) : GateOp → List ℕ → ℕ
  | GateOp.and, [] => M
  | GateOp.and, [a] => a
  | GateOp.and, a :: b :: _ => a &&& b
  | GateOp.or, [] => 0
  | GateOp.or, [a] => a
  | GateOp.or, a :: b :: _ => a ||| b
  | GateOp.not, [] => M
  | GateOp.not, a :: _ => M ^^^ a
  | _, _ => 0

/-- One step of `tabs`. -/
def tstep (M : ℕ) (T : List ℕ) (g : Gate) : List ℕ :=
  T ++ [gt M g.op (g.inputs.map fun i => T.getD i 0)]

/-- The tables of all wires: the input tables `T0`, then one table per gate. -/
def tabs (M : ℕ) (T0 : List ℕ) (gs : List Gate) : List ℕ :=
  gs.foldl (tstep M) T0

/-- The gate is AND, OR or NOT and reads at most two wires. -/
def GOk (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

theorem gt_testBit (M p : ℕ) (hM : M.testBit p = true) (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (l : List ℕ)
    (hl : l.length ≤ 2) :
    (gt M op l).testBit p = op.eval (l.map fun t => t.testBit p) := by
  match l, hl with
  | [], _ => rcases hop with h | h | h <;> subst h <;> simp [gt, GateOp.eval, hM]
  | [a], _ => rcases hop with h | h | h <;> subst h <;> simp [gt, GateOp.eval, Nat.testBit_xor, hM]
  | [a, b], _ =>
    rcases hop with h | h | h <;> subst h <;>
      simp [gt, GateOp.eval, Nat.testBit_xor, Nat.testBit_land, Nat.testBit_lor, hM]

theorem getD_map_testBit (T : List ℕ) (p i : ℕ) :
    (T.map fun t => t.testBit p).getD i false = (T.getD i 0).testBit p := by
  rw [show false = (0 : ℕ).testBit p by simp, List.getD_map]

/-- The abstraction lemma: wire values at the point `p` are bits of the wire tables. -/
theorem wires_tabs (M p : ℕ) (hM : M.testBit p = true) :
    ∀ (gs : List Gate) (T0 : List ℕ), (∀ g ∈ gs, GOk g) →
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (T0.map fun t => t.testBit p)
        = (tabs M T0 gs).map fun t => t.testBit p := by
  intro gs
  induction gs with
  | nil => intro T0 _; rfl
  | cons g gs ih =>
    intro T0 hok
    have hg := hok g (by simp)
    have e : (T0.map fun t => t.testBit p) ++
        [g.op.eval (g.inputs.map fun i => (T0.map fun t => t.testBit p).getD i false)]
        = (tstep M T0 g).map fun t => t.testBit p := by
      simp only [tstep, List.map_append, List.map_cons, List.map_nil]
      congr 2
      rw [gt_testBit M p hM g.op hg.1 _ (by simpa using hg.2), List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact getD_map_testBit T0 p i
    simp only [List.foldl_cons]
    rw [e]
    exact ih _ (fun g' hg' => hok g' (by simp [hg']))

/-! ## The input tables: bit `33 u + v` is the input with left `u` and right `v` on -/

/-- Left input `i`: the bits `33 i .. 33 i + 32`. -/
def lmask (i : ℕ) : ℕ := (2 ^ 33 - 1) <<< (33 * i)

/-- Right input `j`: the bits `33 u + j` for `u < 33`. -/
def rmask (j : ℕ) : ℕ := (List.range 33).foldr (fun u acc => acc ||| 1 <<< (33 * u + j)) 0

theorem lmask_bit (i u v : ℕ) (hv : v < 33) :
    (lmask i).testBit (33 * u + v) = decide (i = u) := by
  unfold lmask
  rw [Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq, ge_iff_le]
  omega

theorem rfold_bit (j q : ℕ) (l : List ℕ) :
    (l.foldr (fun u acc => acc ||| 1 <<< (33 * u + j)) 0).testBit q = true ↔
      ∃ u ∈ l, q = 33 * u + j := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.foldr_cons, Nat.testBit_lor, Bool.or_eq_true, ih, Nat.one_shiftLeft, Nat.testBit_two_pow,
      decide_eq_true_eq]
    simp only [List.mem_cons, exists_eq_or_imp]
    constructor
    · rintro (h | h)
      · exact Or.inr h
      · exact Or.inl h.symm
    · rintro (h | h)
      · exact Or.inr h.symm
      · exact Or.inl h

theorem rmask_bit (j u v : ℕ) (hu : u < 33) (hj : j < 33) (hv : v < 33) :
    (rmask j).testBit (33 * u + v) = decide (j = v) := by
  rw [Bool.eq_iff_iff, decide_eq_true_eq]
  unfold rmask
  rw [rfold_bit]
  constructor
  · rintro ⟨w, -, h⟩
    omega
  · intro h
    exact ⟨u, List.mem_range.2 hu, by omega⟩

/-- All input tables. -/
def T0 : List ℕ := List.ofFn (fun i : Fin 33 => lmask i) ++ List.ofFn (fun j : Fin 33 => rmask j)

theorem oneEach_eq (u v : Fin 33) :
    PEqualNP.Represents.oneEach u v = T0.map (fun t => t.testBit (33 * u.val + v.val)) := by
  simp only [PEqualNP.Represents.oneEach, T0, List.map_append, List.map_ofFn]
  congr 1
  · congr 1
    funext i
    simp only [Function.comp_apply]
    rw [lmask_bit _ _ _ v.isLt]
    exact decide_eq_decide.mpr Fin.ext_iff
  · congr 1
    funext j
    simp only [Function.comp_apply]
    rw [rmask_bit _ _ _ u.isLt j.isLt v.isLt]
    exact decide_eq_decide.mpr Fin.ext_iff

/-- Every bit of the 1089 points. -/
def M : ℕ := 2 ^ 1089 - 1

/-! ## The circuit -/

/-- 76 gates: `w_u = x_u ∨ y_u` for the 33 vertices, then 43 gates on the `w`'s. -/
def C : Circuit := ⟨[
    ⟨GateOp.or, [0, 33]⟩,
    ⟨GateOp.or, [1, 34]⟩,
    ⟨GateOp.or, [2, 35]⟩,
    ⟨GateOp.or, [3, 36]⟩,
    ⟨GateOp.or, [4, 37]⟩,
    ⟨GateOp.or, [5, 38]⟩,
    ⟨GateOp.or, [6, 39]⟩,
    ⟨GateOp.or, [7, 40]⟩,
    ⟨GateOp.or, [8, 41]⟩,
    ⟨GateOp.or, [9, 42]⟩,
    ⟨GateOp.or, [10, 43]⟩,
    ⟨GateOp.or, [11, 44]⟩,
    ⟨GateOp.or, [12, 45]⟩,
    ⟨GateOp.or, [13, 46]⟩,
    ⟨GateOp.or, [14, 47]⟩,
    ⟨GateOp.or, [15, 48]⟩,
    ⟨GateOp.or, [16, 49]⟩,
    ⟨GateOp.or, [17, 50]⟩,
    ⟨GateOp.or, [18, 51]⟩,
    ⟨GateOp.or, [19, 52]⟩,
    ⟨GateOp.or, [20, 53]⟩,
    ⟨GateOp.or, [21, 54]⟩,
    ⟨GateOp.or, [22, 55]⟩,
    ⟨GateOp.or, [23, 56]⟩,
    ⟨GateOp.or, [24, 57]⟩,
    ⟨GateOp.or, [25, 58]⟩,
    ⟨GateOp.or, [26, 59]⟩,
    ⟨GateOp.or, [27, 60]⟩,
    ⟨GateOp.or, [28, 61]⟩,
    ⟨GateOp.or, [29, 62]⟩,
    ⟨GateOp.or, [30, 63]⟩,
    ⟨GateOp.or, [31, 64]⟩,
    ⟨GateOp.or, [32, 65]⟩,
    ⟨GateOp.or, [66, 77]⟩,
    ⟨GateOp.or, [67, 88]⟩,
    ⟨GateOp.and, [99, 100]⟩,
    ⟨GateOp.or, [67, 78]⟩,
    ⟨GateOp.or, [68, 89]⟩,
    ⟨GateOp.and, [102, 103]⟩,
    ⟨GateOp.or, [68, 79]⟩,
    ⟨GateOp.or, [69, 90]⟩,
    ⟨GateOp.and, [105, 106]⟩,
    ⟨GateOp.or, [69, 80]⟩,
    ⟨GateOp.or, [70, 91]⟩,
    ⟨GateOp.and, [108, 109]⟩,
    ⟨GateOp.or, [70, 81]⟩,
    ⟨GateOp.or, [71, 92]⟩,
    ⟨GateOp.and, [111, 112]⟩,
    ⟨GateOp.or, [71, 82]⟩,
    ⟨GateOp.or, [72, 93]⟩,
    ⟨GateOp.and, [114, 115]⟩,
    ⟨GateOp.or, [72, 83]⟩,
    ⟨GateOp.or, [73, 94]⟩,
    ⟨GateOp.and, [117, 118]⟩,
    ⟨GateOp.or, [73, 84]⟩,
    ⟨GateOp.or, [74, 95]⟩,
    ⟨GateOp.and, [120, 121]⟩,
    ⟨GateOp.or, [74, 85]⟩,
    ⟨GateOp.or, [75, 96]⟩,
    ⟨GateOp.and, [123, 124]⟩,
    ⟨GateOp.or, [75, 86]⟩,
    ⟨GateOp.or, [76, 97]⟩,
    ⟨GateOp.and, [126, 127]⟩,
    ⟨GateOp.or, [76, 87]⟩,
    ⟨GateOp.or, [66, 98]⟩,
    ⟨GateOp.and, [129, 130]⟩,
    ⟨GateOp.or, [101, 104]⟩,
    ⟨GateOp.or, [132, 107]⟩,
    ⟨GateOp.or, [133, 110]⟩,
    ⟨GateOp.or, [134, 113]⟩,
    ⟨GateOp.or, [135, 116]⟩,
    ⟨GateOp.or, [136, 119]⟩,
    ⟨GateOp.or, [137, 122]⟩,
    ⟨GateOp.or, [138, 125]⟩,
    ⟨GateOp.or, [139, 128]⟩,
    ⟨GateOp.or, [140, 131]⟩], 141⟩

/-- `true` for AND and OR. -/
def isAO : GateOp → Bool
  | GateOp.and => true
  | GateOp.or => true
  | _ => false

theorem ops : ∀ g ∈ C.gates, isAO g.op = true ∧ g.inputs.length ≤ 2 := by
  decide

theorem op_cases (o : GateOp) (h : isAO o = true) : o = GateOp.and ∨ o = GateOp.or := by
  cases o <;> simp_all [isAO]

theorem mono : PEqualNP.MetaComplexity.Monotone2 C := by
  intro g hg
  obtain ⟨h1, h2⟩ := ops g hg
  refine ⟨?_, h2⟩
  rcases op_cases _ h1 with h | h <;> simp [h]

theorem gok : ∀ g ∈ C.gates, GOk g := by
  intro g hg
  obtain ⟨h1, h2⟩ := ops g hg
  refine ⟨?_, h2⟩
  rcases op_cases _ h1 with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

theorem size_le : C.size ≤ 76 := by decide

theorem eval_eq (u v : Fin 33) :
    C.eval (PEqualNP.Represents.oneEach u v)
      = ((tabs M T0 C.gates).getD C.output 0).testBit (33 * u.val + v.val) := by
  have hp : 33 * u.val + v.val < 1089 := by omega
  have hM : M.testBit (33 * u.val + v.val) = true := by
    unfold M
    rw [Nat.testBit_two_pow_sub_one]
    simpa using hp
  unfold Circuit.eval Circuit.wires
  rw [oneEach_eq, wires_tabs M _ hM C.gates T0 gok]
  exact getD_map_testBit _ _ _

/-- The output table, computed once. -/
def TGT : ℕ := 1620008660354763543701712875090486438052965989434417093509201957275630686653897059553870083650467087122975905668955856506936765737084772582034024445182427770914717785076778205246288317534007769753392955724796787651395321773361764029030606474675607228596596296169031301553371958527579659108555055290591788036513073760712000514

theorem tab_eq : (tabs M T0 C.gates).getD C.output 0 = TGT := by
  decide +kernel

theorem tgt_bits : ∀ u v : Fin 33, TGT.testBit (33 * u.val + v.val) = (fun a b : Fin 33 => decide (∃ i : Fin 11, ((a.val = i.val ∨ a.val = 11 + i.val) ∧ (b.val = (i.val + 1) % 11 ∨ b.val = 22 + i.val)) ∨ ((b.val = i.val ∨ b.val = 11 + i.val) ∧ (a.val = (i.val + 1) % 11 ∨ a.val = 22 + i.val)))) u v := by
  decide +kernel

theorem rep : PEqualNP.Represents.Represents (fun a b : Fin 33 => decide (∃ i : Fin 11, ((a.val = i.val ∨ a.val = 11 + i.val) ∧ (b.val = (i.val + 1) % 11 ∨ b.val = 22 + i.val)) ∨ ((b.val = i.val ∨ b.val = 11 + i.val) ∧ (a.val = (i.val + 1) % 11 ∨ a.val = 22 + i.val)))) C := by
  intro u v
  rw [eval_eq, tab_eq]
  exact tgt_bits u v

end PEqualNP.Outside.Test76c

theorem PEqualNP.Outside.Test76c : PEqualNP.Represents.RepSizeAtMost (fun a b : Fin 33 => decide (∃ i : Fin 11, ((a.val = i.val ∨ a.val = 11 + i.val) ∧ (b.val = (i.val + 1) % 11 ∨ b.val = 22 + i.val)) ∨ ((b.val = i.val ∨ b.val = 11 + i.val) ∧ (a.val = (i.val + 1) % 11 ∨ a.val = 22 + i.val)))) 76 :=
  ⟨PEqualNP.Outside.Test76c.C, PEqualNP.Outside.Test76c.mono, PEqualNP.Outside.Test76c.size_le,
    PEqualNP.Outside.Test76c.rep⟩
