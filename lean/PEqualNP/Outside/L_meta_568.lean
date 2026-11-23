import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L568

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ)
    (h : j ≠ L.length) : (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) :
    (L ++ [S]).getD L.length d = S := by
  simp

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ)
    (h : L.length = k) : (L ++ [S]).getD k d = S := by
  subst h; simp

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom_input (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length →
      (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i h
    have h' : i < (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length := by
      simp; omega
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i h'
    exact this.trans (List.getD_append _ _ _ _ h)

theorem mem_take_one {α : Type} {a : α} (l : List α) :
    a ∈ l.take 1 ↔ l.head? = some a := by
  rw [List.take_one]
  cases l <;> simp [eq_comm]

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

theorem mem_normGate_inputs_iff (n : ℕ) (g : Gate) :
    n ∈ (normGate g).inputs ↔
      (g.op = GateOp.not ∧ g.inputs.head? = some n) ∨
      (g.op ≠ GateOp.not ∧ n ∈ g.inputs) := by
  obtain ⟨op, inputs⟩ := g
  cases op with
  | not =>
    simp only [normGate]
    rw [mem_take_one inputs]
    simp
  | and => simp [normGate]
  | or => simp [normGate]
  | mod m => simp [normGate]
  | maj => simp [normGate]

abbrev Stat := Sum Bool ℕ

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

theorem elim_len_add_count_le (n k : ℕ) (gs : List Gate) :
    ∀ acc : List Stat × List Gate,
      (∀ g ∈ gs, NOk g) → k < acc.1.length →
      (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
      (elim n gs acc).2.length + gs.countP (fun g => decide (k ∈ g.inputs))
        ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _; simp [elim]
  | cons g gs ih =>
    intro acc hok hk hc
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3]
    have hok' : ∀ g' ∈ gs, NOk g' := fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')
    have hk' : k < (elimStep n acc g).1.length := by simp [elimStep]; omega
    have hc' : ∃ c, (elimStep n acc g).1.getD k (Sum.inl false) = Sum.inl c := by
      obtain ⟨c, hc⟩ := hc
      refine ⟨c, ?_⟩
      simp only [elimStep]
      rw [getD_snoc_ne _ _ _ _ (by omega)]
      exact hc
    have hih := ih (elimStep n acc g) hok' hk' hc'
    by_cases hkg : k ∈ g.inputs
    · have hcnt : (g :: gs).countP (fun g => decide (k ∈ g.inputs))
          = gs.countP (fun g => decide (k ∈ g.inputs)) + 1 := by
        rw [List.countP_cons]
        simp [hkg]
      have hsim : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact (hok g List.mem_cons_self).1.1
        · simpa using (hok g List.mem_cons_self).1.2
        · intro h; simpa using (hok g List.mem_cons_self).2 h
        · obtain ⟨c, hc⟩ := hc
          exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        simp only [elimStep, List.length_append]
        rw [hsim]; simp
      rw [hcnt, List.length_cons]
      omega
    · have hcnt : (g :: gs).countP (fun g => decide (k ∈ g.inputs))
          = gs.countP (fun g => decide (k ∈ g.inputs)) := by
        rw [List.countP_cons]
        simp [hkg]
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      rw [hcnt, List.length_cons]
      omega

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Sum.inr (i : ℕ)) ++ [Sum.inl b]

theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Stat))).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, Stat.Valid, Stat.val, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

theorem wiresFrom_agree_off {n : ℕ} (gs : List Gate)
    (hno : ∀ g ∈ gs, n ∉ g.inputs) :
    ∀ w w' : List Bool, w.length = w'.length →
      (∀ i, i ≠ n → w.getD i false = w'.getD i false) →
      ∀ j, j ≠ n → (wiresFrom gs w).getD j false = (wiresFrom gs w').getD j false := by
  induction gs with
  | nil =>
    intro w w' _ hagree j hj
    exact hagree j hj
  | cons g gs ih =>
    intro w w' hlen hagree j hj
    have hno' : ∀ g' ∈ gs, n ∉ g'.inputs :=
      fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')
    have hgn : n ∉ g.inputs := hno g List.mem_cons_self
    have hlen1 : (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length
        = (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)]).length := by
      simp [hlen]
    have hagree1 : ∀ i, i ≠ n →
        (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).getD i false
        = (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)]).getD i false := by
      intro i hi
      by_cases hlt : i < w.length
      · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (by omega)]
        exact hagree i hi
      · by_cases heq : i = w.length
        · subst heq
          rw [getD_snoc_len w _ _ w.length rfl, getD_snoc_len w' _ _ w.length hlen.symm]
          congr 1
          apply List.map_congr_left
          intro a ha
          exact hagree a (fun e => hgn (e ▸ ha))
        · have hwl : i ≠ w'.length := by omega
          rw [getD_snoc_ne _ _ _ _ heq, getD_snoc_ne _ _ _ _ hwl]
          exact hagree i hi
    exact ih hno'
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
      hlen1 hagree1 j hj

theorem two_le_countP_of_two_getElem {α : Type} (p : α → Bool) (l : List α)
    (i j : ℕ) (hi : i < l.length) (hj : j < l.length) (hij : i ≠ j)
    (hpi : p l[i] = true) (hpj : p l[j] = true) : 2 ≤ l.countP p := by
  induction l generalizing i j with
  | nil => simp at hi
  | cons a l ih =>
    match i, j with
    | 0, 0 => exact absurd rfl hij
    | 0, j + 1 =>
      have ha : p a = true := by simpa using hpi
      have hj' : j < l.length := by simpa using hj
      have hpj' : p l[j] = true := by simpa using hpj
      rw [List.countP_cons, if_pos ha]
      have hpos : 1 ≤ l.countP p := by
        rw [List.one_le_countP_iff]
        exact ⟨l[j], List.getElem_mem hj', hpj'⟩
      omega
    | i + 1, 0 =>
      have ha : p a = true := by simpa using hpj
      have hi' : i < l.length := by simpa using hi
      have hpi' : p l[i] = true := by simpa using hpi
      rw [List.countP_cons, if_pos ha]
      have hpos : 1 ≤ l.countP p := by
        rw [List.one_le_countP_iff]
        exact ⟨l[i], List.getElem_mem hi', hpi'⟩
      omega
    | i + 1, j + 1 =>
      have hi' : i < l.length := by simpa using hi
      have hj' : j < l.length := by simpa using hj
      have hij' : i ≠ j := by omega
      have hpi' : p l[i] = true := by simpa using hpi
      have hpj' : p l[j] = true := by simpa using hpj
      have hrec := ih i j hi' hj' hij' hpi' hpj'
      rw [List.countP_cons]
      have hle : l.countP p ≤ l.countP p + (if p a then 1 else 0) := Nat.le_add_right _ _
      omega

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem foldl_step_length (G : List Gate) (w : List Bool) :
    (G.foldl step w).length = w.length + G.length := by
  induction G generalizing w with
  | nil => simp
  | cons g G ih => rw [List.foldl_cons, ih]; simp [step]; omega

theorem getD_append_lt (l l' : List Bool) (i : ℕ) (hi : i < l.length) :
    (l ++ l').getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_of_length_le (l : List Bool) (i : ℕ) (hi : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

theorem foldl_step_getD (G : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (G.foldl step w).getD i false = w.getD i false := by
  induction G generalizing w with
  | nil => rfl
  | cons g G ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    exact getD_append_lt _ _ _ hi

theorem foldl_step_getD_gate (G : List Gate) (w : List Bool) (t : ℕ) (ht : t < G.length) :
    (G.foldl step w).getD (w.length + t) false =
      (G[t]).op.eval ((G[t]).inputs.map fun i => ((G.take t).foldl step w).getD i false) := by
  have hsplit : G = G.take t ++ G[t] :: G.drop (t + 1) := by
    simp [List.take_append_drop]
  conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  rw [foldl_step_getD _ _ _ (by simp only [step, List.length_append, List.length_singleton, foldl_step_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp only [step]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp only [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp [foldl_step_length, Nat.min_eq_left ht.le]

def deps (g : Gate) : List ℕ :=
  match g.op with
  | GateOp.not => g.inputs.head?.toList
  | _ => g.inputs

theorem eval_congr (g : Gate) (f f' : ℕ → Bool) (h : ∀ i ∈ deps g, f i = f' i) :
    g.op.eval (g.inputs.map f) = g.op.eval (g.inputs.map f') := by
  obtain ⟨op, l⟩ := g
  cases op with
  | not =>
    cases l with
    | nil => rfl
    | cons a l =>
      simp only [deps, List.head?_cons, Option.toList_some, List.mem_singleton, forall_eq] at h
      simp [GateOp.eval, h]
  | _ =>
    simp only [deps] at h
    rw [List.map_congr_left h]

theorem getD_eraseIdx_lt (l : List Bool) (p i : ℕ) (hi : i < p) :
    (l.eraseIdx p).getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eraseIdx_of_lt hi]

theorem getD_eraseIdx_ge (l : List Bool) (p i : ℕ) (hi : p ≤ i) :
    (l.eraseIdx p).getD i false = l.getD (i + 1) false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eraseIdx_of_ge hi]

def ren (p r i : ℕ) : ℕ := if i < p then i else if i = p then r else i - 1

def renG (p r : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (ren p r)⟩

def del (G : List Gate) (t p r : ℕ) : List Gate := G.take t ++ (G.drop (t + 1)).map (renG p r)

theorem deps_renG (p r : ℕ) (g : Gate) : deps (renG p r g) = (deps g).map (ren p r) := by
  obtain ⟨op, l⟩ := g
  cases op <;> cases l <;> simp [deps, renG]

theorem del_foldl_aux (W : List Bool) (p r : ℕ) (hr : r < p ∨ W.length ≤ r) :
    ∀ (L : List Gate) (v : List Bool), L.foldl step v = W → p < v.length →
      (∀ g ∈ L, p ∈ deps g → W.getD p false = W.getD r false) →
      (L.map (renG p r)).foldl step (v.eraseIdx p) = W.eraseIdx p := by
  intro L
  induction L with
  | nil =>
    intro v hW _ _
    simp only [List.foldl_nil] at hW
    subst hW
    rfl
  | cons g L ih =>
    intro v hW hp hv
    rw [List.foldl_cons] at hW
    rw [List.map_cons, List.foldl_cons]
    have hvW : ∀ i, i < v.length → v.getD i false = W.getD i false := fun i hi => by
      rw [← hW, foldl_step_getD _ _ _ (by simp only [step, List.length_append, List.length_singleton]; omega)]
      exact (getD_append_lt _ _ _ hi).symm
    have hWlen : v.length + 1 + L.length = W.length := by
      have := congrArg List.length hW
      rw [foldl_step_length] at this
      simp only [step, List.length_append, List.length_singleton] at this
      omega
    have hstep : step (v.eraseIdx p) (renG p r g) = (step v g).eraseIdx p := by
      simp only [step, renG, List.map_map]
      rw [List.eraseIdx_append_of_lt_length hp]
      congr 2
      apply eval_congr
      intro i hi
      simp only [Function.comp, ren]
      split_ifs with h1 h2
      · exact getD_eraseIdx_lt _ _ _ h1
      · subst h2
        rcases hr with hr | hr
        · rw [getD_eraseIdx_lt _ _ _ hr, hvW _ (by omega), hvW _ hp]
          exact (hv g (by simp) hi).symm
        · rw [getD_of_length_le _ _ (by rw [List.length_eraseIdx_of_lt hp]; omega), hvW _ hp,
            hv g (by simp) hi, getD_of_length_le _ _ hr]
      · rw [getD_eraseIdx_ge _ _ _ (by omega), Nat.sub_add_cancel (by omega)]
    rw [hstep]
    exact ih _ hW (by simp only [step, List.length_append, List.length_singleton]; omega)
      (fun g' hg' => hv g' (List.mem_cons_of_mem _ hg'))

theorem del_foldl (G : List Gate) (x : List Bool) (t r : ℕ) (ht : t < G.length)
    (hr : r < x.length + t ∨ x.length + G.length ≤ r)
    (hv : ∀ g ∈ G.drop (t + 1), x.length + t ∈ deps g →
      (G.foldl step x).getD (x.length + t) false = (G.foldl step x).getD r false) :
    (del G t (x.length + t) r).foldl step x = (G.foldl step x).eraseIdx (x.length + t) := by
  have hsplit : G = G.take t ++ G[t] :: G.drop (t + 1) := by simp
  have hWlen : (G.foldl step x).length = x.length + G.length := foldl_step_length _ _
  have hW' : (G.drop (t + 1)).foldl step (step ((G.take t).foldl step x) G[t]) = G.foldl step x := by
    conv_rhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have hlen : ((G.take t).foldl step x).length = x.length + t := by
    rw [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]
  have hv0 : (G.take t).foldl step x = (step ((G.take t).foldl step x) G[t]).eraseIdx (x.length + t) := by
    simp only [step]
    rw [List.eraseIdx_append_of_length_le (by omega)]
    simp [hlen]
  unfold del
  rw [List.foldl_append, hv0]
  exact del_foldl_aux _ (x.length + t) r (by rwa [hWlen]) _ _ hW'
    (by simp only [step, List.length_append, List.length_singleton, hlen]; omega) hv

theorem del_eval (G : List Gate) (o : ℕ) (x : List Bool) (t r : ℕ) (ht : t < G.length)
    (hr : r < x.length + t ∨ x.length + G.length ≤ r)
    (hv : ∀ g ∈ G.drop (t + 1), x.length + t ∈ deps g →
      (G.foldl step x).getD (x.length + t) false = (G.foldl step x).getD r false)
    (ho : o = x.length + t → (G.foldl step x).getD (x.length + t) false = (G.foldl step x).getD r false) :
    Circuit.eval ⟨del G t (x.length + t) r, ren (x.length + t) r o⟩ x = Circuit.eval ⟨G, o⟩ x := by
  simp only [Circuit.eval, wires_eq]
  rw [del_foldl G x t r ht hr hv]
  unfold ren
  split_ifs with h1 h2
  · exact getD_eraseIdx_lt _ _ _ h1
  · subst h2
    rcases hr with hr | hr
    · rw [getD_eraseIdx_lt _ _ _ hr]
      exact (ho rfl).symm
    · rw [getD_of_length_le _ _ (by rw [List.length_eraseIdx_of_lt (by rw [foldl_step_length]; omega), foldl_step_length]; omega),
        ho rfl, getD_of_length_le _ _ (by rw [foldl_step_length]; exact hr)]
  · rw [getD_eraseIdx_ge _ _ _ (by omega), Nat.sub_add_cancel (by omega)]

theorem del_length (G : List Gate) (t p r : ℕ) (ht : t < G.length) :
    (del G t p r).length = G.length - 1 := by
  simp only [del, List.length_append, List.length_take, List.length_map, List.length_drop]
  omega

theorem fanInTwo_del (G : List Gate) (o : ℕ) (t p r o' : ℕ) (h : FanInTwo ⟨G, o⟩) :
    FanInTwo ⟨del G t p r, o'⟩ := by
  simp only [FanInTwo] at h ⊢
  intro g hg
  simp only [del, List.mem_append, List.mem_map] at hg
  rcases hg with hg | ⟨g', hg', rfl⟩
  · exact h g (List.mem_of_mem_take hg)
  · obtain ⟨h1, h2⟩ := h g' (List.mem_of_mem_drop hg')
    exact ⟨h1, by simpa [renG] using h2⟩

theorem foldl_take_getD (G : List Gate) (w : List Bool) (t i : ℕ)
    (hi : i < ((G.take t).foldl step w).length) :
    (G.foldl step w).getD i false = ((G.take t).foldl step w).getD i false := by
  conv_lhs => rw [← List.take_append_drop t G, List.foldl_append]
  exact foldl_step_getD _ _ _ hi

theorem gate_value (G : List Gate) (w : List Bool) (t : ℕ) (ht : t < G.length) :
    (G.foldl step w).getD (w.length + t) false =
      (G[t]).op.eval ((G[t]).inputs.map fun i =>
        if i < w.length + t then (G.foldl step w).getD i false else false) := by
  rw [foldl_step_getD_gate G w t ht]
  congr 1
  apply List.map_congr_left
  intro i _
  have hlen : ((G.take t).foldl step w).length = w.length + t := by
    rw [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]
  split_ifs with h
  · exact (foldl_take_getD G w t i (by rw [hlen]; exact h)).symm
  · exact getD_of_length_le _ _ (by rw [hlen]; omega)

theorem del_getElem_lt (G : List Gate) (t p r t' : ℕ) (h : t' < t) (ht : t < G.length) :
    (del G t p r)[t']'(by rw [del_length G t p r ht]; omega) = G[t']'(by omega) := by
  simp only [del]
  rw [List.getElem_append_left (by simp [List.length_take]; omega), List.getElem_take]

theorem del_getElem_ge (G : List Gate) (t p r t' : ℕ) (h : t ≤ t') (ht : t' + 1 < G.length) :
    (del G t p r)[t']'(by rw [del_length G t p r (by omega)]; omega) = renG p r (G[t' + 1]'ht) := by
  simp only [del]
  rw [List.getElem_append_right (by simp [List.length_take]; omega), List.getElem_map, List.getElem_drop]
  congr 2
  simp [List.length_take]
  omega

theorem mem_deps_iff (a : ℕ) (g : Gate) : a ∈ deps g ↔
    (g.op = GateOp.not ∧ g.inputs.head? = some a) ∨ (g.op ≠ GateOp.not ∧ a ∈ g.inputs) := by
  obtain ⟨op, l⟩ := g
  cases op <;> cases l <;> simp [deps, eq_comm]

theorem mem_inputs_of_mem_deps {a : ℕ} {g : Gate} (h : a ∈ deps g) : a ∈ g.inputs := by
  obtain ⟨op, l⟩ := g
  cases op <;> cases l <;> simp_all [deps]

theorem normGate_inputs (g : Gate) : (normGate g).inputs = deps g := by
  obtain ⟨op, l⟩ := g
  cases op <;> cases l <;> simp [normGate, deps]

theorem wiresFrom_eq (gs : List Gate) (w : List Bool) : wiresFrom gs w = gs.foldl step w := rfl

def isConst : Stat → Bool
  | Sum.inl _ => true
  | Sum.inr _ => false

def hits (acc : List Stat × List Gate) (g : Gate) : Bool :=
  g.inputs.any (fun i => isConst (acc.1.getD i (Sum.inl false)))

def dropCount (n : ℕ) : List Gate → List Stat × List Gate → ℕ
  | [], _ => 0
  | g :: gs, acc => (if hits acc g then 1 else 0) + dropCount n gs (elimStep n acc g)

theorem elim_len_add_drop (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → (elim n gs acc).2.length + dropCount n gs acc ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _; simp [elim, dropCount]
  | cons g gs ih =>
    intro acc hok
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    have hih := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    simp only [dropCount]
    rw [h3]
    by_cases hh : hits acc g = true
    · have hsim : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact (hok g List.mem_cons_self).1.1
        · simpa using (hok g List.mem_cons_self).1.2
        · intro h; simpa using (hok g List.mem_cons_self).2 h
        · simp only [hits, List.any_eq_true] at hh
          obtain ⟨i, hi, hc⟩ := hh
          revert hc
          cases hs : acc.1.getD i (Sum.inl false) with
          | inl c => intro _; exact ⟨c, List.mem_map.2 ⟨i, hi, hs⟩⟩
          | inr j => simp [isConst]
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        simp only [elimStep, List.length_append]
        rw [hsim]; simp
      rw [if_pos hh, List.length_cons]
      omega
    · have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      rw [if_neg hh, List.length_cons]
      omega

def dflt : Gate := ⟨GateOp.and, []⟩

theorem dropCount_eq_sum (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    dropCount n gs acc = ∑ t ∈ Finset.range gs.length,
      (if hits (elim n (gs.take t) acc) (gs.getD t dflt) then 1 else 0) := by
  induction gs with
  | nil => intro acc; simp [dropCount]
  | cons g gs ih =>
    intro acc
    rw [List.length_cons, Finset.sum_range_succ', dropCount, ih (elimStep n acc g)]
    have h0 : elim n ((g :: gs).take 0) acc = acc := rfl
    rw [h0]
    simp only [List.getD_cons_zero, List.getD_cons_succ, List.take_succ_cons]
    rw [Nat.add_comm]
    rfl

theorem card_le_dropCount (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate)
    (T : Finset ℕ) (hT : ∀ t ∈ T, ∃ h : t < gs.length, hits (elim n (gs.take t) acc) gs[t] = true) :
    T.card ≤ dropCount n gs acc := by
  rw [dropCount_eq_sum, Finset.card_eq_sum_ones]
  have hsub : T ⊆ Finset.range gs.length := by
    intro t ht; obtain ⟨h, _⟩ := hT t ht; exact Finset.mem_range.2 h
  calc ∑ t ∈ T, 1 = ∑ t ∈ T, (if hits (elim n (gs.take t) acc) (gs.getD t dflt) then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro t ht
        obtain ⟨h, hh⟩ := hT t ht
        rw [List.getD_eq_getElem _ _ h, if_pos hh]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)

theorem elim_fst (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    ∃ l, (elim n gs acc).1 = acc.1 ++ l ∧ l.length = gs.length := by
  induction gs with
  | nil => intro acc; exact ⟨[], by simp [elim], rfl⟩
  | cons g gs ih =>
    intro acc
    obtain ⟨l, hl, hll⟩ := ih (elimStep n acc g)
    refine ⟨(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2 :: l, ?_, by simp [hll]⟩
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, hl]
    simp [elimStep]

theorem elim_fst_length (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) :
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  obtain ⟨l, hl, hll⟩ := elim_fst n gs acc
  rw [hl]; simp [hll]

theorem elim_take_getD (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) (t i : ℕ)
    (hi : i < acc.1.length + t) (ht : t ≤ gs.length) :
    (elim n (gs.take t) acc).1.getD i (Sum.inl false) = (elim n gs acc).1.getD i (Sum.inl false) := by
  have hsplit : elim n gs acc = elim n (gs.drop t) (elim n (gs.take t) acc) := by
    simp only [elim]
    rw [← List.foldl_append, List.take_append_drop]
  rw [hsplit]
  obtain ⟨l, hl, _⟩ := elim_fst n (gs.drop t) (elim n (gs.take t) acc)
  rw [hl, List.getD_append]
  rw [elim_fst_length, List.length_take, Nat.min_eq_left ht]
  exact hi

theorem elim_take_getD_ge (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) (t i : ℕ)
    (hi : acc.1.length + t ≤ i) (ht : t ≤ gs.length) :
    (elim n (gs.take t) acc).1.getD i (Sum.inl false) = Sum.inl false := by
  apply List.getD_eq_default
  rw [elim_fst_length, List.length_take, Nat.min_eq_left ht]
  exact hi

def sh (n i : ℕ) : ℕ := if i < n then i else i + 1

def liftG (n : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (sh n)⟩

theorem ren_sh (n r i : ℕ) : ren n r (sh n i) = i := by
  unfold ren sh; split_ifs <;> omega

theorem renG_liftG (n r : ℕ) (g : Gate) : renG n r (liftG n g) = g := by
  obtain ⟨op, l⟩ := g
  simp only [renG, liftG, List.map_map]
  congr 1
  conv_rhs => rw [← List.map_id l]
  apply List.map_congr_left
  intro i _
  exact ren_sh n r i

theorem sh_ne (n i : ℕ) : sh n i ≠ n := by
  unfold sh; split_ifs <;> omega

theorem lift_foldl (n : ℕ) (E : List Gate) (y : Fin n → Bool) (b : Bool) :
    E.foldl step (List.ofFn y) =
      ((E.map (liftG n)).foldl step (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))).eraseIdx n := by
  set W := (E.map (liftG n)).foldl step (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool)) with hW
  have h := del_foldl_aux W n W.length (Or.inr le_rfl) (E.map (liftG n))
    (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool)) hW.symm (by simp)
    (by
      intro g hg hd
      exfalso
      obtain ⟨g0, _, rfl⟩ := List.mem_map.1 hg
      have := mem_inputs_of_mem_deps hd
      simp only [liftG, List.mem_map] at this
      obtain ⟨i, _, hi⟩ := this
      exact sh_ne n i hi)
  rw [← h, List.map_map]
  have hc : (renG n W.length ∘ liftG n) = id := by
    funext g; exact renG_liftG n W.length g
  rw [hc, List.map_id, ofFn_snoc]
  congr 1
  rw [List.eraseIdx_append_of_length_le (by simp)]
  simp

def liftC (n : ℕ) (E : Circuit) : Circuit :=
  ⟨E.gates.map (liftG n) ++ [⟨GateOp.or, [n, sh n E.output]⟩], n + 1 + E.gates.length⟩

theorem liftC_eval (n : ℕ) (E : Circuit) (y : Fin n → Bool) (b : Bool) :
    circuitFun (n + 1) (liftC n E) (Fin.snoc y b) = (b || E.eval (List.ofFn y)) := by
  set W := (E.gates.map (liftG n)).foldl step (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool)) with hW
  have hWlen : W.length = n + 1 + E.gates.length := by
    rw [hW, foldl_step_length]; simp
  have hb : W.getD n false = b := by
    rw [hW, foldl_step_getD _ _ _ (by simp), ofFn_snoc]
    exact getD_snoc_len _ _ _ _ (by simp)
  have he : E.eval (List.ofFn y) = W.getD (sh n E.output) false := by
    simp only [Circuit.eval, wires_eq]
    rw [lift_foldl n E.gates y b, ← hW]
    unfold sh
    split_ifs with h
    · exact getD_eraseIdx_lt _ _ _ h
    · exact getD_eraseIdx_ge _ _ _ (by omega)
  rw [he]
  simp only [circuitFun, Circuit.eval, liftC, wires_eq, List.foldl_append, List.foldl_cons,
    List.foldl_nil]
  rw [← hW]
  simp only [step]
  rw [getD_snoc_len _ _ _ _ hWlen]
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, hb, id,
    Bool.or_false]

theorem size_le_lift {n : ℕ} {C E : Circuit} (hmin : IsMinimalCircuit (n + 1) C) (hE : FanInTwo E)
    (hC : ∀ (y : Fin n → Bool) (b : Bool),
      circuitFun (n + 1) C (Fin.snoc y b) = (b || E.eval (List.ofFn y))) :
    C.size ≤ E.size + 1 := by
  have hD : FanInTwo (liftC n E) := by
    intro g hg
    simp only [liftC, List.mem_append, List.mem_map, List.mem_singleton] at hg
    rcases hg with ⟨g0, hg0, rfl⟩ | rfl
    · obtain ⟨h1, h2⟩ := hE g0 hg0
      exact ⟨h1, by simpa [liftG] using h2⟩
    · exact ⟨by simp, by simp⟩
  have hf : circuitFun (n + 1) (liftC n E) = circuitFun (n + 1) C := by
    funext X
    rw [← Fin.snoc_init_self X, liftC_eval, hC]
  have := hmin.2 (liftC n E) hD hf
  simpa [Circuit.size, liftC] using this

theorem not_dead {N : ℕ} {C : Circuit} (hmin : IsMinimalCircuit N C) (hN : 0 < N) (t : ℕ)
    (ht : t < C.gates.length)
    (hno : ∀ t' (h : t' < C.gates.length), t < t' → N + t ∉ deps (C.gates[t']))
    (hout : C.output ≠ N + t) : False := by
  set D : Circuit := ⟨del C.gates t (N + t) 0, ren (N + t) 0 C.output⟩ with hD
  have hDok : FanInTwo D := fanInTwo_del C.gates C.output t (N + t) 0 _ hmin.1
  have hf : circuitFun N D = circuitFun N C := by
    funext X
    have hl : (List.ofFn X).length = N := by simp
    have := del_eval C.gates C.output (List.ofFn X) t 0 ht (Or.inl (by omega))
      (by
        intro g hg hd
        exfalso
        rw [List.mem_iff_getElem] at hg
        obtain ⟨j, hj, rfl⟩ := hg
        rw [List.getElem_drop] at hd
        rw [hl] at hd
        exact hno _ _ (by omega) hd)
      (by intro h; rw [hl] at h; exact absurd h hout)
    simp only [circuitFun, hD]
    rw [hl] at this
    exact this
  have := hmin.2 D hDok hf
  simp only [Circuit.size, hD, del_length C.gates t (N + t) 0 ht] at this
  omega

def rd (P M i : ℕ) : ℕ := if i = P then M else i

def rdG (P M : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (rd P M)⟩

theorem deps_rdG (P M : ℕ) (g : Gate) : deps (rdG P M g) = (deps g).map (rd P M) := by
  obtain ⟨op, l⟩ := g
  cases op <;> cases l <;> simp [deps, rdG]

theorem rd_foldl_aux (W : List Bool) (P M : ℕ) (hM : W.length ≤ M) (hP : W.getD P false = false) :
    ∀ (L : List Gate) (v : List Bool), L.foldl step v = W →
      (L.map (rdG P M)).foldl step v = W := by
  intro L
  induction L with
  | nil => intro v h; exact h
  | cons g L ih =>
    intro v hW
    rw [List.foldl_cons] at hW
    rw [List.map_cons, List.foldl_cons]
    have hvl : (step v g).length ≤ W.length := by
      rw [← hW, foldl_step_length]; omega
    have hstep : step v (rdG P M g) = step v g := by
      simp only [step, rdG, List.map_map]
      congr 2
      apply eval_congr
      intro i _
      simp only [Function.comp, rd]
      split_ifs with h
      · have hvM : v.length ≤ M := by
          simp only [step, List.length_append, List.length_singleton] at hvl; omega
        rw [getD_of_length_le v M hvM, h]
        by_cases hlt : P < v.length
        · have hWv : W.getD P false = v.getD P false := by
            rw [← hW, foldl_step_getD _ _ _ (by simp [step]; omega)]
            exact getD_append_lt _ _ _ hlt
          rw [← hWv, hP]
        · exact (getD_of_length_le _ _ (by omega)).symm
      · rfl
    rw [hstep]
    exact ih _ hW

theorem agree (G : List Gate) (v v' : List Bool) (hlen : v.length = v'.length) (B : ℕ → Prop)
    (hin : ∀ i, ¬ B i → v.getD i false = v'.getD i false)
    (hg : ∀ t (ht : t < G.length), ¬ B (v.length + t) →
      (∀ i ∈ deps G[t], ¬ B i) ∨
        (G.foldl step v).getD (v.length + t) false = (G.foldl step v').getD (v.length + t) false) :
    ∀ i, ¬ B i → (G.foldl step v).getD i false = (G.foldl step v').getD i false := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hBi
    by_cases h1 : i < v.length
    · rw [foldl_step_getD _ _ _ h1, foldl_step_getD _ _ _ (by omega)]
      exact hin i hBi
    · by_cases h2 : v.length + G.length ≤ i
      · rw [getD_of_length_le _ _ (by rw [foldl_step_length]; omega),
          getD_of_length_le _ _ (by rw [foldl_step_length]; omega)]
      · obtain ⟨t, rfl⟩ : ∃ t, i = v.length + t := ⟨i - v.length, by omega⟩
        have ht : t < G.length := by omega
        rcases hg t ht hBi with hd | hv
        · rw [gate_value G v t ht]
          have := gate_value G v' t ht
          rw [← hlen] at this
          rw [this]
          apply eval_congr
          intro j hj
          split_ifs with hjl
          · exact ih j hjl (hd j hj)
          · rfl
        · exact hv

def acc0 (n : ℕ) : List Stat × List Gate := (initStats n false, [])

theorem acc0_len (n : ℕ) : (acc0 n).1.length = n + 1 := by simp [acc0, initStats]

theorem normGate_op (g : Gate) : (normGate g).op = g.op := by
  obtain ⟨op, l⟩ := g
  cases op <;> rfl

theorem st_x (n : ℕ) (Gs : List Gate) :
    (elim n (Gs.map normGate) (acc0 n)).1.getD n (Sum.inl false) = Sum.inl false := by
  obtain ⟨l, hl, _⟩ := elim_fst n (Gs.map normGate) (acc0 n)
  rw [hl, List.getD_append _ _ _ _ (by rw [acc0_len]; omega)]
  simp only [acc0, initStats]
  exact getD_snoc_len _ _ _ _ (by simp)

theorem elim_inv (n : ℕ) (Gs : List Gate) (hok : ∀ g ∈ Gs, Ok g) (y : Fin n → Bool) (i : ℕ) :
    ((elim n (Gs.map normGate) (acc0 n)).1.getD i (Sum.inl false)).val
      (wiresFrom (elim n (Gs.map normGate) (acc0 n)).2 (List.ofFn y))
      = (Gs.foldl step (List.ofFn (Fin.snoc y false : Fin (n + 1) → Bool))).getD i false := by
  have h := inv_elim n (List.ofFn y) (by simp) (Gs.map normGate) _ _
    (by
      intro g hg
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
      exact (normGate_nok g0 (hok g0 hg0)).1)
    (inv_init n false y)
  rw [show acc0 n = (initStats n false, []) from rfl, (h.2 i).2, wiresFrom_norm, ofFn_snoc]
  rfl

theorem elim_ok' (n : ℕ) (Gs : List Gate) :
    ∀ g ∈ (elim n (Gs.map normGate) (acc0 n)).2, Ok g :=
  elim_ok n _ _ (by simp [acc0])

theorem elim_count (n : ℕ) (Gs : List Gate) (hok : ∀ g ∈ Gs, Ok g) :
    (elim n (Gs.map normGate) (acc0 n)).2.length + dropCount n (Gs.map normGate) (acc0 n)
      ≤ Gs.length := by
  have := elim_len_add_drop n (Gs.map normGate) (acc0 n)
    (by
      intro g hg
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
      exact normGate_nok g0 (hok g0 hg0))
  simpa [acc0] using this

theorem hit_of (n : ℕ) (Gs : List Gate) (t : ℕ) (ht : t < Gs.length) (i : ℕ)
    (hi : i ∈ deps Gs[t])
    (hc : n + 1 + t ≤ i ∨
      isConst ((elim n (Gs.map normGate) (acc0 n)).1.getD i (Sum.inl false)) = true) :
    ∃ h : t < (Gs.map normGate).length,
      hits (elim n ((Gs.map normGate).take t) (acc0 n)) (Gs.map normGate)[t] = true := by
  refine ⟨by simpa using ht, ?_⟩
  simp only [hits, List.any_eq_true, List.getElem_map, normGate_inputs]
  refine ⟨i, hi, ?_⟩
  have hlen : t ≤ (Gs.map normGate).length := by simp; omega
  by_cases hlt : i < n + 1 + t
  · rcases hc with hc | hc
    · omega
    · rw [elim_take_getD n _ _ t i (by rw [acc0_len]; exact hlt) hlen]
      exact hc
  · rw [elim_take_getD_ge n _ _ t i (by rw [acc0_len]; omega) hlen]
    rfl

theorem st_gate (n : ℕ) (Gs : List Gate) (r : ℕ) (hr : r < Gs.length) :
    (elim n (Gs.map normGate) (acc0 n)).1.getD (n + 1 + r) (Sum.inl false) =
      (simplify Gs[r].op (n + (elim n ((Gs.map normGate).take r) (acc0 n)).2.length)
        ((deps Gs[r]).map fun i =>
          (elim n ((Gs.map normGate).take r) (acc0 n)).1.getD i (Sum.inl false))).2 := by
  have hlen : r + 1 ≤ (Gs.map normGate).length := by simp; omega
  rw [← elim_take_getD n _ _ (r + 1) (n + 1 + r) (by rw [acc0_len]; omega) hlen]
  have htake : (Gs.map normGate).take (r + 1) =
      (Gs.map normGate).take r ++ [normGate Gs[r]] := by
    rw [List.take_succ, List.getElem?_eq_getElem (by simpa using hr)]
    simp
  rw [htake]
  have he : elim n ((Gs.map normGate).take r ++ [normGate Gs[r]]) (acc0 n) =
      elimStep n (elim n ((Gs.map normGate).take r) (acc0 n)) (normGate Gs[r]) := by
    simp [elim, List.foldl_append]
  rw [he]
  simp only [elimStep]
  rw [getD_snoc_len _ _ _ _ (by
    rw [elim_fst_length, acc0_len, List.length_take, Nat.min_eq_left (by omega)])]
  rw [normGate_op, normGate_inputs]

theorem simplify_inr {op : GateOp} {m : ℕ} {ins : List Stat}
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hf : Sum.inl false ∈ ins) {j : ℕ}
    (hj : (simplify op m ins).2 = Sum.inr j) :
    op = GateOp.or ∧ ∃ j', ins = [Sum.inl false, Sum.inr j'] ∨ ins = [Sum.inr j', Sum.inl false] := by
  rcases hop with rfl | rfl | rfl
  · exfalso
    obtain _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ := ins
    · simp at hf
    · rcases a with ((_ | _) | j1) <;> simp_all [simplify, simpAnd]
    · rcases a with ((_ | _) | j1) <;> rcases b with ((_ | _) | j2) <;>
        simp_all [simplify, simpAnd]
    · simp at hlen
  · refine ⟨rfl, ?_⟩
    obtain _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ := ins
    · simp at hf
    · rcases a with ((_ | _) | j1) <;> simp_all [simplify, simpOr]
    · rcases a with ((_ | _) | j1) <;> rcases b with ((_ | _) | j2) <;>
        simp_all [simplify, simpOr]
    · simp at hlen
  · exfalso
    have := hnot rfl
    obtain _ | ⟨a, _ | ⟨b, l⟩⟩ := ins
    · simp at hf
    · rcases a with ((_ | _) | j1) <;> simp_all [simplify, simpNot]
    · simp at this

theorem ofFn_getD {m : ℕ} (X : Fin m → Bool) (i : ℕ) (hi : i < m) :
    (List.ofFn X).getD i false = X ⟨i, hi⟩ := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem snoc_getD_n (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool)).getD n false = b := by
  rw [ofFn_snoc]; exact getD_snoc_len _ _ _ _ (by simp)

theorem snoc_getD_lt (n : ℕ) (y : Fin n → Bool) (b : Bool) (i : ℕ) (hi : i < n) :
    (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool)).getD i false = y ⟨i, hi⟩ := by
  rw [ofFn_snoc, List.getD_append _ _ _ _ (by simpa using hi), ofFn_getD]

theorem two_hits {n : ℕ} {gs : List Gate} {acc : List Stat × List Gate} (hd : dropCount n gs acc ≤ 1)
    {t1 t2 : ℕ} (h1 : ∃ h : t1 < gs.length, hits (elim n (gs.take t1) acc) gs[t1] = true)
    (h2 : ∃ h : t2 < gs.length, hits (elim n (gs.take t2) acc) gs[t2] = true) : t1 = t2 := by
  by_contra hne
  have := card_le_dropCount n gs acc {t1, t2} (by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact h1
    · exact h2)
  rw [Finset.card_pair hne] at this
  omega

theorem base {n : ℕ} {C : Circuit} {H : (Fin n → Bool) → Bool}
    (hmin : IsMinimalCircuit (n + 1) C) (hH : ∃ y y', H y ≠ H y')
    (hF : ∀ y b, circuitFun (n + 1) C (Fin.snoc y b) = (b || H y)) :
    ∃ c0 : ℕ, ∃ hc0 : c0 < C.gates.length,
      (∀ t (ht : t < C.gates.length), n ∈ deps C.gates[t] → t = c0) ∧
      C.gates[c0].op = GateOp.or ∧
      (∃ b, b ≠ n ∧ b < n + 1 + c0 ∧ (deps C.gates[c0] = [n, b] ∨ deps C.gates[c0] = [b, n])) ∧
      (∀ t (ht : t < C.gates.length), ∀ i ∈ deps C.gates[t], i < n + 1 + t) := by
  classical
  have hok : ∀ g ∈ C.gates, Ok g := hmin.1
  set G := C.gates with hG
  set gs := G.map normGate with hgs
  set acc := elim n gs (acc0 n) with hacc
  have hval : ∀ y i, (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn y)) =
      (G.foldl step (List.ofFn (Fin.snoc y false : Fin (n + 1) → Bool))).getD i false :=
    fun y i => elim_inv n G hok y i
  have hHy : ∀ y, H y =
      (G.foldl step (List.ofFn (Fin.snoc y false : Fin (n + 1) → Bool))).getD C.output false := by
    intro y
    have := hF y false
    rw [Bool.false_or] at this
    exact this.symm
  have hTy : ∀ y,
      (G.foldl step (List.ofFn (Fin.snoc y true : Fin (n + 1) → Bool))).getD C.output false
        = true := by
    intro y
    have := hF y true
    rw [Bool.true_or] at this
    exact this
  obtain ⟨o, ho⟩ : ∃ o, acc.1.getD C.output (Sum.inl false) = Sum.inr o := by
    cases h : acc.1.getD C.output (Sum.inl false) with
    | inr o => exact ⟨o, rfl⟩
    | inl c =>
      exfalso
      obtain ⟨y, y', hne⟩ := hH
      apply hne
      rw [hHy y, hHy y', ← hval y, ← hval y', h]
      rfl
  have hsize : G.length ≤ acc.2.length + 1 := by
    have := size_le_lift (E := ⟨acc.2, o⟩) hmin (elim_ok' n G) (by
      intro y b
      rw [hF y b]
      congr 1
      rw [hHy y, ← hval y, ho]
      rfl)
    simpa [Circuit.size] using this
  have hcnt := elim_count n G hok
  have hd : dropCount n gs (acc0 n) ≤ 1 := by
    rw [← hgs] at hcnt
    rw [← hacc] at hcnt
    omega
  have hxst : isConst (acc.1.getD n (Sum.inl false)) = true := by
    rw [hacc, hgs, st_x]
    rfl
  have hout_ne : C.output ≠ n := by
    intro h
    obtain ⟨y, y', hne⟩ := hH
    apply hne
    rw [hHy y, hHy y', h, foldl_step_getD _ _ _ (by simp), foldl_step_getD _ _ _ (by simp),
      snoc_getD_n, snoc_getD_n]
  have hex : ∃ c0, ∃ _ : c0 < G.length, n ∈ deps G[c0] := by
    by_contra hnone
    push_neg at hnone
    have hno : ∀ g ∈ gs, n ∉ g.inputs := by
      intro g hg
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg0
      rw [normGate_inputs]
      exact hnone i hi
    obtain ⟨y, y', hne⟩ := hH
    have hall : ∀ z, H z = true := by
      intro z
      have e1 : G.foldl step (List.ofFn (Fin.snoc z false : Fin (n + 1) → Bool)) =
          wiresFrom gs (List.ofFn (Fin.snoc z false : Fin (n + 1) → Bool)) := by
        rw [hgs, wiresFrom_norm]; rfl
      have e2 : G.foldl step (List.ofFn (Fin.snoc z true : Fin (n + 1) → Bool)) =
          wiresFrom gs (List.ofFn (Fin.snoc z true : Fin (n + 1) → Bool)) := by
        rw [hgs, wiresFrom_norm]; rfl
      rw [hHy z, ← hTy z, e1, e2]
      apply wiresFrom_agree_off gs hno _ _ (by simp)
      · intro i hi
        rw [ofFn_snoc, ofFn_snoc]
        by_cases hlt : i < n
        · rw [List.getD_append _ _ _ _ (by simpa using hlt),
            List.getD_append _ _ _ _ (by simpa using hlt)]
        · rw [getD_snoc_ne _ _ _ _ (by simp; omega), getD_snoc_ne _ _ _ _ (by simp; omega)]
      · exact hout_ne
    exact hne (by rw [hall y, hall y'])
  obtain ⟨c0, hc0, hxc0⟩ := hex
  have hit_c0 := hit_of n G c0 hc0 n hxc0 (Or.inr hxst)
  have huniq : ∀ t (ht : t < G.length), n ∈ deps G[t] → t = c0 := by
    intro t ht hxt
    exact two_hits hd (hit_of n G t ht n hxt (Or.inr hxst)) hit_c0
  obtain ⟨j0, hj0⟩ : ∃ j0, acc.1.getD (n + 1 + c0) (Sum.inl false) = Sum.inr j0 := by
    cases h : acc.1.getD (n + 1 + c0) (Sum.inl false) with
    | inr j => exact ⟨j, rfl⟩
    | inl c =>
      exfalso
      have hc : isConst (acc.1.getD (n + 1 + c0) (Sum.inl false)) = true := by rw [h]; rfl
      by_cases hout : C.output = n + 1 + c0
      · rw [hout, h] at ho
        cases ho
      · apply not_dead hmin (by omega) c0 hc0 _ hout
        intro t' ht' _ hdep
        have := two_hits hd (hit_of n G t' ht' _ hdep (Or.inr hc)) hit_c0
        omega
  have hsg := st_gate n G c0 hc0
  rw [← hgs, ← hacc, hj0] at hsg
  set f := fun i => (elim n (gs.take c0) (acc0 n)).1.getD i (Sum.inl false) with hf
  have hfn : f n = Sum.inl false := by
    simp only [hf]
    rw [elim_take_getD n _ _ c0 n (by rw [acc0_len]; omega) (by simp [hgs]; omega), ← hacc]
    rw [hacc, hgs, st_x]
  have hop := (hok _ (List.getElem_mem hc0)).1
  have hlen2 : (deps G[c0]).length ≤ 2 := by
    have := (hok _ (List.getElem_mem hc0)).2
    have hsub : (deps G[c0]).length ≤ G[c0].inputs.length := by
      obtain ⟨op, l⟩ := G[c0]
      cases op <;> cases l <;> simp [deps]
    omega
  have hor := simplify_inr (op := G[c0].op) (m := n + (elim n (gs.take c0) (acc0 n)).2.length)
    (ins := (deps G[c0]).map f)
    (by rcases hop with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h))
    (by simpa using hlen2)
    (by
      intro hn
      have := (normGate_nok G[c0] (hok _ (List.getElem_mem hc0))).2 (by rw [normGate_op]; exact hn)
      rw [normGate_inputs] at this
      simpa using this)
    (List.mem_map.2 ⟨n, hxc0, hfn⟩) hsg.symm
  obtain ⟨hor, j', hins⟩ := hor
  have hform : ∃ b, b ≠ n ∧ b < n + 1 + c0 ∧ (deps G[c0] = [n, b] ∨ deps G[c0] = [b, n]) := by
    have hfb : ∀ b, f b = Sum.inr j' → b ≠ n ∧ b < n + 1 + c0 := by
      intro b hb
      constructor
      · intro h
        rw [h, hfn] at hb
        cases hb
      · by_contra hge
        push_neg at hge
        simp only [hf] at hb
        rw [elim_take_getD_ge n _ _ c0 b (by rw [acc0_len]; omega) (by simp [hgs]; omega)] at hb
        cases hb
    rcases hins with h | h
    · obtain ⟨d1, d2, hd12⟩ : ∃ d1 d2, deps G[c0] = [d1, d2] := by
        have hl := congrArg List.length h
        simp only [List.length_map, List.length_cons, List.length_nil] at hl
        match hdl : deps G[c0], hl with
        | [d1, d2], _ => exact ⟨d1, d2, rfl⟩
      rw [hd12] at h hxc0
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
      obtain ⟨hb1, hb2⟩ := hfb d2 h.2
      have : d1 = n := by
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hxc0
        rcases hxc0 with h' | h'
        · exact h'.symm
        · exact absurd h'.symm hb1
      exact ⟨d2, hb1, hb2, Or.inl (by rw [hd12, this])⟩
    · obtain ⟨d1, d2, hd12⟩ : ∃ d1 d2, deps G[c0] = [d1, d2] := by
        have hl := congrArg List.length h
        simp only [List.length_map, List.length_cons, List.length_nil] at hl
        match hdl : deps G[c0], hl with
        | [d1, d2], _ => exact ⟨d1, d2, rfl⟩
      rw [hd12] at h hxc0
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
      obtain ⟨hb1, hb2⟩ := hfb d1 h.1
      have : d2 = n := by
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hxc0
        rcases hxc0 with h' | h'
        · exact absurd h'.symm hb1
        · exact h'.symm
      exact ⟨d1, hb1, hb2, Or.inr (by rw [hd12, this])⟩
  refine ⟨c0, hc0, huniq, hor, hform, ?_⟩
  intro t ht i hi
  by_contra hge
  push_neg at hge
  have := two_hits hd (hit_of n G t ht i hi (Or.inl hge)) hit_c0
  subst this
  obtain ⟨b, hb, hbl, hdc⟩ := hform
  rcases hdc with h | h <;> rw [h] at hi <;> simp at hi <;> omega

theorem output_last {n : ℕ} {C : Circuit} {H : (Fin n → Bool) → Bool}
    (hmin : IsMinimalCircuit (n + 1) C) (hH : ∃ y y', H y ≠ H y')
    (hF : ∀ y b, circuitFun (n + 1) C (Fin.snoc y b) = (b || H y))
    (hfut : ∀ t (ht : t < C.gates.length), ∀ i ∈ deps C.gates[t], i < n + 1 + t) :
    0 < C.gates.length ∧ C.output = n + 1 + (C.gates.length - 1) := by
  have hHy : ∀ y, H y =
      (C.gates.foldl step (List.ofFn (Fin.snoc y false : Fin (n + 1) → Bool))).getD C.output false := by
    intro y
    have := hF y false
    rw [Bool.false_or] at this
    exact this.symm
  have hTy : ∀ y,
      (C.gates.foldl step (List.ofFn (Fin.snoc y true : Fin (n + 1) → Bool))).getD C.output false
        = true := by
    intro y
    have := hF y true
    rw [Bool.true_or] at this
    exact this
  set y0 : Fin n → Bool := fun _ => false
  have h1 : C.output < n + 1 + C.gates.length := by
    by_contra hge
    push_neg at hge
    have := hTy y0
    rw [getD_of_length_le _ _ (by rw [foldl_step_length]; simpa using hge)] at this
    cases this
  have h2 : n + 1 ≤ C.output := by
    by_contra hlt
    push_neg at hlt
    by_cases hn : C.output = n
    · obtain ⟨y, y', hne⟩ := hH
      apply hne
      rw [hHy y, hHy y', hn, foldl_step_getD _ _ _ (by simp), foldl_step_getD _ _ _ (by simp),
        snoc_getD_n, snoc_getD_n]
    · have := hTy y0
      rw [foldl_step_getD _ _ _ (by simp; omega), snoc_getD_lt _ _ _ _ (by omega)] at this
      cases this
  refine ⟨by omega, ?_⟩
  by_contra hne
  apply not_dead hmin (by omega) (C.gates.length - 1) (by omega) _ (by omega)
  intro t' ht' hlt
  omega

def redir (G : List Gate) (p0 P M : ℕ) : List Gate :=
  G.take (p0 + 1) ++ (G.drop (p0 + 1)).map (rdG P M)

theorem redir_length (G : List Gate) (p0 P M : ℕ) (hp : p0 < G.length) :
    (redir G p0 P M).length = G.length := by
  simp only [redir, List.length_append, List.length_take, List.length_map, List.length_drop]
  omega

theorem redir_get_le (G : List Gate) (p0 P M t : ℕ) (hp : p0 < G.length) (ht : t ≤ p0) :
    (redir G p0 P M)[t]'(by rw [redir_length G p0 P M hp]; omega) = G[t]'(by omega) := by
  simp only [redir]
  rw [List.getElem_append_left (by simp [List.length_take]; omega), List.getElem_take]

theorem redir_get_gt (G : List Gate) (p0 P M t : ℕ) (hp : p0 < t) (ht : t < G.length) :
    (redir G p0 P M)[t]'(by rw [redir_length G p0 P M (by omega)]; omega) = rdG P M (G[t]) := by
  simp only [redir]
  rw [List.getElem_append_right (by simp [List.length_take]; omega), List.getElem_map,
    List.getElem_drop]
  congr 2
  simp [List.length_take]
  omega

theorem redir_ok (G : List Gate) (p0 P M : ℕ) (hok : ∀ g ∈ G, Ok g) :
    ∀ g ∈ redir G p0 P M, Ok g := by
  intro g hg
  simp only [redir, List.mem_append, List.mem_map] at hg
  rcases hg with hg | ⟨g', hg', rfl⟩
  · exact hok g (List.mem_of_mem_take hg)
  · obtain ⟨h1, h2⟩ := hok g' (List.mem_of_mem_drop hg')
    exact ⟨h1, by simpa [rdG] using h2⟩

theorem redir_take (G : List Gate) (p0 P M : ℕ) (hp : p0 < G.length) :
    (redir G p0 P M).take (p0 + 1) = G.take (p0 + 1) := by
  simp only [redir]
  rw [List.take_append_of_le_length (by simp; omega)]
  simp

theorem redir_getD_P (G : List Gate) (p0 P M : ℕ) (v : List Bool) (hp : p0 < G.length)
    (hP : P = v.length + p0) :
    ((redir G p0 P M).foldl step v).getD P false = (G.foldl step v).getD P false := by
  have hl1 : P < ((G.take (p0 + 1)).foldl step v).length := by
    rw [foldl_step_length, List.length_take]; omega
  rw [foldl_take_getD (redir G p0 P M) v (p0 + 1) P (by rw [redir_take G p0 P M hp]; exact hl1),
    foldl_take_getD G v (p0 + 1) P hl1, redir_take G p0 P M hp]

theorem redir_foldl_eq (G : List Gate) (p0 P M : ℕ) (v : List Bool)
    (hM : v.length + G.length ≤ M) (hfalse : (G.foldl step v).getD P false = false) :
    (redir G p0 P M).foldl step v = G.foldl step v := by
  have hsplit : G.foldl step v = (G.drop (p0 + 1)).foldl step ((G.take (p0 + 1)).foldl step v) := by
    rw [← List.foldl_append, List.take_append_drop]
  simp only [redir]
  rw [List.foldl_append]
  exact rd_foldl_aux (G.foldl step v) P M (by rw [foldl_step_length]; exact hM) hfalse
    (G.drop (p0 + 1)) _ hsplit.symm

theorem or_deps {g : Gate} (h : g.op = GateOp.or) : deps g = g.inputs := by
  obtain ⟨op, l⟩ := g
  simp only at h
  subst h
  rfl

theorem gate_true_of_or (G : List Gate) (v : List Bool) (t : ℕ) (ht : t < G.length)
    (hor : G[t].op = GateOp.or) (i : ℕ) (hi : i ∈ G[t].inputs) (hlt : i < v.length + t)
    (hv : (G.foldl step v).getD i false = true) :
    (G.foldl step v).getD (v.length + t) false = true := by
  rw [gate_value G v t ht, hor]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp]
  exact ⟨i, hi, by rw [if_pos hlt]; exact hv⟩

theorem rd_mem_deps (P M i : ℕ) (g : Gate) (hi : i ∈ deps g) : rd P M i ∈ deps (rdG P M g) := by
  rw [deps_rdG]
  exact List.mem_map.2 ⟨i, hi, rfl⟩

theorem getD_dflt (G : List Gate) (t : ℕ) (ht : t < G.length) : G.getD t dflt = G[t] := by
  simp [List.getD_eq_getElem?_getD, ht]

def ChainInv (n : ℕ) (G : List Gate) (k : ℕ) (c : ℕ → ℕ) : Prop :=
  (∀ j ≤ k, c j < G.length) ∧
  (∀ j < k, c j < c (j + 1)) ∧
  (∀ j ≤ k, (G.getD (c j) dflt).op = GateOp.or ∧ (G.getD (c j) dflt).inputs.length = 2) ∧
  (n ∈ (G.getD (c 0) dflt).inputs ∧ ∀ j < k, n + 1 + c j ∈ (G.getD (c (j + 1)) dflt).inputs) ∧
  (∀ t (ht : t < G.length), n ∈ deps G[t] → t = c 0) ∧
  (∀ j < k, ∀ t (ht : t < G.length), n + 1 + c j ∈ deps G[t] → t = c (j + 1)) ∧
  ((∃ w ∈ (G.getD (c 0) dflt).inputs, w ≠ n ∧ w < n + 1 + c 0) ∧
    ∀ j < k, ∃ w ∈ (G.getD (c (j + 1)) dflt).inputs,
      w ≠ n + 1 + c j ∧ w ≠ n ∧ w < n + 1 + c (j + 1))

theorem chain_lt {n : ℕ} {G : List Gate} {k : ℕ} {c : ℕ → ℕ} (hc : ChainInv n G k c) :
    ∀ i j, i < j → j ≤ k → c i < c j := by
  intro i j hij hjk
  induction j with
  | zero => omega
  | succ j ih =>
    have h1 := hc.2.1 j (by omega)
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | h
    · have := ih h (by omega); omega
    · subst h; exact h1

theorem chain_true {n : ℕ} {G : List Gate} {k : ℕ} {c : ℕ → ℕ} (hc : ChainInv n G k c)
    (y : Fin n → Bool) : ∀ j ≤ k,
    (G.foldl step (List.ofFn (Fin.snoc y true : Fin (n + 1) → Bool))).getD (n + 1 + c j) false
      = true := by
  intro j hj
  have hv : (List.ofFn (Fin.snoc y true : Fin (n + 1) → Bool)).length = n + 1 := by simp
  induction j with
  | zero =>
    have hc0 := hc.1 0 (by omega)
    have := gate_true_of_or G (List.ofFn (Fin.snoc y true : Fin (n + 1) → Bool)) (c 0) hc0
      (by rw [← getD_dflt G _ hc0]; exact (hc.2.2.1 0 (by omega)).1) n
      (by rw [← getD_dflt G _ hc0]; exact hc.2.2.2.1.1) (by rw [hv]; omega)
      (by rw [foldl_step_getD _ _ _ (by rw [hv]; omega), snoc_getD_n])
    rwa [hv] at this
  | succ j ih =>
    have hcj := hc.1 (j + 1) hj
    have hlt := hc.2.1 j (by omega)
    have := gate_true_of_or G (List.ofFn (Fin.snoc y true : Fin (n + 1) → Bool)) (c (j + 1)) hcj
      (by rw [← getD_dflt G _ hcj]; exact (hc.2.2.1 (j + 1) hj).1) (n + 1 + c j)
      (by rw [← getD_dflt G _ hcj]; exact hc.2.2.2.1.2 j (by omega))
      (by rw [hv]; omega) (ih (by omega))
    rwa [hv] at this

theorem three_hits {n : ℕ} {gs : List Gate} {acc : List Stat × List Gate}
    (hd : dropCount n gs acc ≤ 2) {t1 t2 t3 : ℕ}
    (h1 : ∃ h : t1 < gs.length, hits (elim n (gs.take t1) acc) gs[t1] = true)
    (h2 : ∃ h : t2 < gs.length, hits (elim n (gs.take t2) acc) gs[t2] = true)
    (h3 : ∃ h : t3 < gs.length, hits (elim n (gs.take t3) acc) gs[t3] = true)
    (h12 : t1 ≠ t2) (h13 : t1 ≠ t3) (h23 : t2 ≠ t3) : False := by
  have := card_le_dropCount n gs acc {t1, t2, t3} (by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3)
  rw [Finset.card_insert_of_notMem (by simp [h12, h13]), Finset.card_pair h23] at this
  omega

theorem extend_inv {n : ℕ} {G : List Gate} {k : ℕ} {c : ℕ → ℕ} (hc : ChainInv n G k c)
    {r b : ℕ} (hpr : c k < r) (hrs : r < G.length) (hor : G[r].op = GateOp.or)
    (hin : G[r].inputs = [n + 1 + c k, b] ∨ G[r].inputs = [b, n + 1 + c k])
    (hb1 : b ≠ n + 1 + c k) (hb2 : b ≠ n) (hb3 : b < n + 1 + r)
    (huniq : ∀ t (ht : t < G.length), n + 1 + c k ∈ deps G[t] → t = r) :
    ChainInv n G (k + 1) (fun j => if j ≤ k then c j else r) := by
  obtain ⟨hA, hB, hC, ⟨hD1, hD2⟩, hE, hF, ⟨hG1, hG2⟩⟩ := hc
  have hlen : G[r].inputs.length = 2 := by rcases hin with h | h <;> rw [h] <;> rfl
  have hmemP : n + 1 + c k ∈ G[r].inputs := by rcases hin with h | h <;> rw [h] <;> simp
  have hmemb : b ∈ G[r].inputs := by rcases hin with h | h <;> rw [h] <;> simp
  have hr' : G.getD r dflt = G[r] := getD_dflt G r hrs
  refine ⟨?_, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_, ⟨?_, ?_⟩⟩
  all_goals beta_reduce
  · intro j hj
    by_cases h : j ≤ k
    · rw [if_pos h]; exact hA j h
    · rw [if_neg h]; exact hrs
  · intro j hj
    by_cases h : j < k
    · rw [if_pos (by omega), if_pos (by omega)]; exact hB j h
    · have : j = k := by omega
      subst this
      rw [if_pos le_rfl, if_neg (by omega)]
      exact hpr
  · intro j hj
    by_cases h : j ≤ k
    · rw [if_pos h]; exact hC j h
    · rw [if_neg h, hr']; exact ⟨hor, hlen⟩
  · rw [if_pos (Nat.zero_le k)]; exact hD1
  · intro j hj
    by_cases h : j < k
    · rw [if_pos (by omega), if_pos (by omega)]; exact hD2 j h
    · have : j = k := by omega
      subst this
      rw [if_pos le_rfl, if_neg (by omega), hr']
      exact hmemP
  · intro t ht hd
    rw [if_pos (Nat.zero_le k)]; exact hE t ht hd
  · intro j hj t ht hd
    by_cases h : j < k
    · rw [if_pos (by omega)] at hd
      rw [if_pos (by omega)]
      exact hF j h t ht hd
    · have : j = k := by omega
      subst this
      rw [if_pos le_rfl] at hd
      rw [if_neg (by omega)]
      exact huniq t ht hd
  · rw [if_pos (Nat.zero_le k)]; exact hG1
  · intro j hj
    by_cases h : j < k
    · rw [if_pos (by omega), if_pos (by omega)]; exact hG2 j h
    · have : j = k := by omega
      subst this
      rw [if_pos le_rfl, if_neg (by omega), hr']
      exact ⟨b, hmemb, hb1, hb2, hb3⟩

theorem step_ext {n : ℕ} {C : Circuit} {H : (Fin n → Bool) → Bool}
    (hmin : IsMinimalCircuit (n + 1) C) (hH : ∃ y y', H y ≠ H y')
    (hF : ∀ y b, circuitFun (n + 1) C (Fin.snoc y b) = (b || H y))
    (hfut : ∀ t (ht : t < C.gates.length), ∀ i ∈ deps C.gates[t], i < n + 1 + t)
    (hlast : C.output = n + 1 + (C.gates.length - 1))
    (k : ℕ) (c : ℕ → ℕ) (hc : ChainInv n C.gates k c) (hk : c k ≠ C.gates.length - 1) :
    ∃ r, c k < r ∧ ChainInv n C.gates (k + 1) (fun j => if j ≤ k then c j else r) := by
  classical
  have hok : ∀ g ∈ C.gates, Ok g := hmin.1
  set G := C.gates with hG
  set s := G.length with hs
  have hp : c k < s := hc.1 k le_rfl
  set p0 := c k with hp0
  set P := n + 1 + p0 with hP
  set M := n + 1 + s with hM
  set Ga := redir G p0 P M with hGa
  have hGal : Ga.length = s := redir_length G p0 P M hp
  have hokA : ∀ g ∈ Ga, Ok g := redir_ok G p0 P M hok
  set gsA := Ga.map normGate with hgsA
  set accA := elim n gsA (acc0 n) with haccA
  have hvalA : ∀ y i, (accA.1.getD i (Sum.inl false)).val (wiresFrom accA.2 (List.ofFn y)) =
      (Ga.foldl step (List.ofFn (Fin.snoc y false : Fin (n + 1) → Bool))).getD i false :=
    fun y i => elim_inv n Ga hokA y i
  have hcntA := elim_count n Ga hokA
  rw [← hgsA] at hcntA
  rw [← haccA, hGal] at hcntA
  have hHy : ∀ y, H y =
      (G.foldl step (List.ofFn (Fin.snoc y false : Fin (n + 1) → Bool))).getD C.output false := by
    intro y
    have := hF y false
    rw [Bool.false_or] at this
    exact this.symm
  have hTy : ∀ y,
      (G.foldl step (List.ofFn (Fin.snoc y true : Fin (n + 1) → Bool))).getD C.output false
        = true := by
    intro y
    have := hF y true
    rw [Bool.true_or] at this
    exact this
  have hvlen : ∀ (y : Fin n → Bool) b,
      (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool)).length = n + 1 := by simp
  set A := fun y : Fin n → Bool =>
    (G.foldl step (List.ofFn (Fin.snoc y false : Fin (n + 1) → Bool))).getD P false with hA
  have hAa : ∀ y, (Ga.foldl step (List.ofFn (Fin.snoc y false : Fin (n + 1) → Bool))).getD P false
      = A y := by
    intro y
    exact redir_getD_P G p0 P M _ hp (by rw [hvlen])
  have hAtrue : ∀ y, A y = true → H y = true := by
    intro y hAy
    have hBout : ¬ (C.output = n ∨ ∃ j < k, C.output = n + 1 + c j) := by
      rintro (h | ⟨j, hj, h⟩)
      · omega
      · have := chain_lt hc j k hj le_rfl
        omega
    have hag := agree G (List.ofFn (Fin.snoc y false : Fin (n + 1) → Bool))
      (List.ofFn (Fin.snoc y true : Fin (n + 1) → Bool)) (by simp)
      (fun i => i = n ∨ ∃ j < k, i = n + 1 + c j)
      (by
        intro i hi
        simp only [not_or, not_exists, not_and] at hi
        by_cases hlt : i < n
        · rw [snoc_getD_lt _ _ _ _ hlt, snoc_getD_lt _ _ _ _ hlt]
        · rw [getD_of_length_le _ _ (by rw [hvlen]; omega),
            getD_of_length_le _ _ (by rw [hvlen]; omega)])
      (by
        intro t ht hBt
        simp only [hvlen] at hBt ⊢
        by_cases htp : t = p0
        · right
          rw [htp]
          have h1 : (G.foldl step (List.ofFn (Fin.snoc y false : Fin (n + 1) → Bool))).getD
              (n + 1 + p0) false = A y := rfl
          rw [h1, hAy]
          exact (chain_true hc y k le_rfl).symm
        · left
          intro i hi hBi
          apply hBt
          rcases hBi with rfl | ⟨j, hj, rfl⟩
          · have h0 := hc.2.2.2.2.1 t ht hi
            rcases Nat.eq_zero_or_pos k with hk0 | hk0
            · exfalso
              apply htp
              rw [h0, hp0, hk0]
            · right
              exact ⟨0, hk0, by rw [h0]⟩
          · have h1 := hc.2.2.2.2.2.1 j hj t ht hi
            by_cases hj1 : j + 1 < k
            · right
              exact ⟨j + 1, hj1, by rw [h1]⟩
            · exfalso
              apply htp
              rw [h1, hp0]
              congr 1
              omega)
      C.output hBout
    rw [hHy y, hag, hTy y]
  have hHA : ∀ y, H y = (A y ||
      (Ga.foldl step (List.ofFn (Fin.snoc y false : Fin (n + 1) → Bool))).getD C.output false) := by
    intro y
    cases hAy : A y with
    | true => rw [hAtrue y hAy]; rfl
    | false =>
      rw [Bool.false_or, redir_foldl_eq G p0 P M _ (by rw [hvlen]) hAy, hHy y]
  have hE : ∀ (E : Circuit), FanInTwo E → (∀ y, E.eval (List.ofFn y) = H y) → s ≤ E.size + 1 := by
    intro E hEok hEval
    have := size_le_lift (E := E) hmin hEok (by intro y b; rw [hF y b, hEval y])
    simpa [Circuit.size] using this
  have hPst : ∀ y, (accA.1.getD P (Sum.inl false)).val (wiresFrom accA.2 (List.ofFn y)) = A y := by
    intro y
    rw [hvalA y P, hAa y]
  have hOst : ∀ y, (accA.1.getD C.output (Sum.inl false)).val (wiresFrom accA.2 (List.ofFn y)) =
      (Ga.foldl step (List.ofFn (Fin.snoc y false : Fin (n + 1) → Bool))).getD C.output false :=
    fun y => hvalA y C.output
  have hbound : dropCount n gsA (acc0 n) ≤ 2 ∧
      (isConst (accA.1.getD C.output (Sum.inl false)) = true →
        dropCount n gsA (acc0 n) ≤ 1) := by
    obtain ⟨y1, y2, hne⟩ := hH
    cases hsp : accA.1.getD P (Sum.inl false) with
    | inl cp =>
      have hAc : ∀ y, A y = cp := fun y => by rw [← hPst y, hsp]; rfl
      cases cp with
      | true =>
        exfalso
        apply hne
        rw [hHA y1, hHA y2, hAc, hAc]
        rfl
      | false =>
        cases hso : accA.1.getD C.output (Sum.inl false) with
        | inl co =>
          exfalso
          apply hne
          rw [hHA y1, hHA y2, hAc, hAc, ← hOst, ← hOst, hso]
          rfl
        | inr o =>
          have := hE ⟨accA.2, o⟩ (elim_ok' n Ga) (by
            intro y
            rw [hHA y, hAc, Bool.false_or, ← hOst y, hso]
            rfl)
          simp only [Circuit.size] at this
          exact ⟨by omega, fun _ => by omega⟩
    | inr m =>
      cases hso : accA.1.getD C.output (Sum.inl false) with
      | inl co =>
        cases co with
        | true =>
          exfalso
          apply hne
          rw [hHA y1, hHA y2, ← hOst, ← hOst, hso]
          simp [Stat.val]
        | false =>
          have := hE ⟨accA.2, m⟩ (elim_ok' n Ga) (by
            intro y
            rw [hHA y, ← hOst y, hso, ← hPst y, hsp]
            simp [Stat.val]
            rfl)
          simp only [Circuit.size] at this
          exact ⟨by omega, fun _ => by omega⟩
      | inr o =>
        have hEok : FanInTwo ⟨accA.2 ++ [⟨GateOp.or, [m, o]⟩], n + accA.2.length⟩ := by
          intro g hg
          simp only [List.mem_append, List.mem_singleton] at hg
          rcases hg with hg | rfl
          · exact elim_ok' n Ga g hg
          · exact ⟨by simp, by simp⟩
        have := hE ⟨accA.2 ++ [⟨GateOp.or, [m, o]⟩], n + accA.2.length⟩ hEok (by
          intro y
          rw [hHA y, ← hOst y, hso, ← hPst y, hsp]
          simp only [Circuit.eval, wires_eq, List.foldl_append, List.foldl_cons, List.foldl_nil,
            step]
          rw [getD_snoc_len _ _ _ _ (by rw [foldl_step_length]; simp)]
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
            Bool.or_false, Stat.val]
          rfl)
        simp only [Circuit.size, List.length_append, List.length_singleton] at this
        refine ⟨by omega, fun h => ?_⟩
        simp [isConst] at h
  have hx0 : isConst (accA.1.getD n (Sum.inl false)) = true := by
    rw [haccA, hgsA, st_x]
    rfl
  have hc0s : c 0 < s := hc.1 0 (by omega)
  have hc0p : c 0 ≤ p0 := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · rw [hp0, hk0]
    · exact le_of_lt (chain_lt hc 0 k hk0 le_rfl)
  have hit0 : ∃ h : c 0 < gsA.length,
      hits (elim n (gsA.take (c 0)) (acc0 n)) gsA[c 0] = true := by
    have hxd : n ∈ deps (Ga[c 0]'(by omega)) := by
      rw [redir_get_le G p0 P M (c 0) hp hc0p]
      have := hc.2.2.2.1.1
      rw [getD_dflt G _ hc0s] at this
      rw [or_deps (by have := (hc.2.2.1 0 (by omega)).1; rwa [getD_dflt G _ hc0s] at this)]
      exact this
    exact hit_of n Ga (c 0) (by omega) n hxd (Or.inr hx0)
  have hitP : ∀ t (ht : t < s), P ∈ deps G[t] →
      p0 < t ∧ ∃ h : t < gsA.length, hits (elim n (gsA.take t) (acc0 n)) gsA[t] = true := by
    intro t ht hd
    have hpt : p0 < t := by have := hfut t ht P hd; omega
    refine ⟨hpt, ?_⟩
    have hMd : M ∈ deps (Ga[t]'(by omega)) := by
      rw [redir_get_gt G p0 P M t hpt ht]
      have := rd_mem_deps P M P G[t] hd
      simpa [rd] using this
    exact hit_of n Ga t (by omega) M hMd (Or.inl (by omega))
  have hpls : p0 < s - 1 := by omega
  obtain ⟨r, hrs, hrP⟩ : ∃ r, ∃ _ : r < s, P ∈ deps G[r] := by
    by_contra hno
    push_neg at hno
    exact not_dead hmin (by omega) p0 hp (fun t' ht' _ => hno t' ht') (by omega)
  obtain ⟨hpr, hitr⟩ := hitP r hrs hrP
  have huniq : ∀ t (ht : t < s), P ∈ deps G[t] → t = r := by
    intro t ht hd
    obtain ⟨hpt, hitt⟩ := hitP t ht hd
    by_contra htr
    exact three_hits hbound.1 hit0 hitr hitt (by omega) (by omega) (Ne.symm htr)
  have hOnc : isConst (accA.1.getD C.output (Sum.inl false)) = false := by
    by_contra h
    have h1 := hbound.2 (by simpa using h)
    have := two_hits h1 hit0 hitr
    omega
  have hrnc : isConst (accA.1.getD (n + 1 + r) (Sum.inl false)) = false := by
    by_contra h
    simp only [Bool.not_eq_false] at h
    by_cases hrl : r = s - 1
    · apply absurd hOnc
      rw [hlast, ← hrl, h]
      simp
    · obtain ⟨t', ht', hlt', hdep'⟩ : ∃ t', ∃ _ : t' < s, r < t' ∧ n + 1 + r ∈ deps G[t'] := by
        by_contra hno
        push_neg at hno
        exact not_dead hmin (by omega) r hrs (fun t' ht' hlt => hno t' ht' hlt) (by omega)
      have hdA : n + 1 + r ∈ deps (Ga[t']'(by omega)) := by
        rw [redir_get_gt G p0 P M t' (by omega) ht']
        have := rd_mem_deps P M (n + 1 + r) G[t'] hdep'
        have hne : n + 1 + r ≠ P := by omega
        simpa [rd, hne] using this
      have hitt' := hit_of n Ga t' (by omega) (n + 1 + r) hdA (Or.inr h)
      exact three_hits hbound.1 hit0 hitr hitt' (by omega) (by omega) (by omega)
  have hrA : r < Ga.length := by omega
  have hGar : Ga[r]'hrA = rdG P M G[r] := redir_get_gt G p0 P M r hpr hrs
  have hsg := st_gate n Ga r hrA
  rw [← hgsA] at hsg
  rw [← haccA] at hsg
  simp only [hGar] at hsg
  rw [deps_rdG] at hsg
  obtain ⟨jr, hjr⟩ : ∃ jr, accA.1.getD (n + 1 + r) (Sum.inl false) = Sum.inr jr := by
    cases h : accA.1.getD (n + 1 + r) (Sum.inl false) with
    | inl c => rw [h] at hrnc; simp [isConst] at hrnc
    | inr j => exact ⟨j, rfl⟩
  rw [hjr] at hsg
  set f := fun i => (elim n (gsA.take r) (acc0 n)).1.getD i (Sum.inl false) with hf
  have hgslen : r ≤ gsA.length := by simp [hgsA]; omega
  have hfge : ∀ i, n + 1 + r ≤ i → f i = Sum.inl false := by
    intro i hi
    exact elim_take_getD_ge n _ _ r i (by rw [acc0_len]; omega) hgslen
  have hfn : f n = Sum.inl false := by
    simp only [hf]
    rw [elim_take_getD n _ _ r n (by rw [acc0_len]; omega) hgslen]
    exact st_x n Ga
  have hopr := (hok _ (List.getElem_mem hrs)).1
  have hlenr : (deps G[r]).length ≤ 2 := by
    have := (hok _ (List.getElem_mem hrs)).2
    have hsub : (deps G[r]).length ≤ G[r].inputs.length := by
      obtain ⟨op, l⟩ := G[r]
      cases op <;> cases l <;> simp [deps]
    omega
  have hnotr : G[r].op = GateOp.not → (deps G[r]).length ≤ 1 := by
    obtain ⟨op, l⟩ := G[r]
    intro h
    simp only at h
    subst h
    cases l <;> simp [deps]
  have hres := simplify_inr (op := G[r].op) (ins := ((deps G[r]).map (rd P M)).map f)
    (by rcases hopr with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h))
    (by simpa using hlenr)
    (by intro h; simpa using hnotr h)
    (List.mem_map.2 ⟨M, List.mem_map.2 ⟨P, hrP, by simp [rd]⟩, hfge M (by omega)⟩)
    hsg.symm
  obtain ⟨hor, j', hins⟩ := hres
  obtain ⟨d1, d2, hd12⟩ : ∃ d1 d2, deps G[r] = [d1, d2] := by
    have hl : (((deps G[r]).map (rd P M)).map f).length = 2 := by
      rcases hins with h | h <;> rw [h] <;> rfl
    simp only [List.length_map] at hl
    match hdl : deps G[r], hl with
    | [d1, d2], _ => exact ⟨d1, d2, rfl⟩
  have hdeps_in : deps G[r] = G[r].inputs := or_deps hor
  have hgood : ∀ d, f (rd P M d) = Sum.inr j' → d ≠ P ∧ d ≠ n ∧ d < n + 1 + r := by
    intro d hd
    have hdP : d ≠ P := by
      intro h
      rw [h] at hd
      simp only [rd, if_true] at hd
      rw [hfge M (by omega)] at hd
      cases hd
    simp only [rd, hdP, if_false] at hd
    refine ⟨hdP, ?_, ?_⟩
    · intro h
      rw [h, hfn] at hd
      cases hd
    · by_contra hge
      push_neg at hge
      rw [hfge d hge] at hd
      cases hd
  rw [hd12] at hins hrP
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hins
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hrP
  refine ⟨r, hpr, ?_⟩
  rcases hins with ⟨_, h2⟩ | ⟨h1, _⟩
  · obtain ⟨hb1, hb2, hb3⟩ := hgood d2 h2
    have hd1 : d1 = P := by
      rcases hrP with h | h
      · exact h.symm
      · exact absurd h.symm hb1
    exact extend_inv hc hpr hrs hor (Or.inl (by rw [← hdeps_in, hd12, hd1])) hb1 hb2 hb3 huniq
  · obtain ⟨hb1, hb2, hb3⟩ := hgood d1 h1
    have hd2 : d2 = P := by
      rcases hrP with h | h
      · exact absurd h.symm hb1
      · exact h.symm
    exact extend_inv hc hpr hrs hor (Or.inr (by rw [← hdeps_in, hd12, hd2])) hb1 hb2 hb3 huniq

theorem chain_mono {n : ℕ} {G : List Gate} {k : ℕ} {c : ℕ → ℕ} (hc : ChainInv n G k c)
    (i j : ℕ) (hij : i ≤ j) (hjk : j ≤ k) : c i ≤ c j := by
  rcases Nat.lt_or_eq_of_le hij with h | h
  · exact le_of_lt (chain_lt hc i j h hjk)
  · rw [h]

theorem chain_inj {n : ℕ} {G : List Gate} {k : ℕ} {c : ℕ → ℕ} (hc : ChainInv n G k c)
    (i j : ℕ) (hi : i ≤ k) (hj : j ≤ k) (h : c i = c j) : i = j := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := chain_lt hc i j hlt hj; omega
  · have := chain_lt hc j i hlt hi; omega

theorem chain_full {n : ℕ} {C : Circuit} {H : (Fin n → Bool) → Bool}
    (hmin : IsMinimalCircuit (n + 1) C) (hH : ∃ y y', H y ≠ H y')
    (hF : ∀ y b, circuitFun (n + 1) C (Fin.snoc y b) = (b || H y))
    (hfut : ∀ t (ht : t < C.gates.length), ∀ i ∈ deps C.gates[t], i < n + 1 + t)
    (hlast : C.output = n + 1 + (C.gates.length - 1)) :
    ∀ m k c, ChainInv n C.gates k c → C.gates.length - 1 - c k = m →
      ∃ k' c', ChainInv n C.gates k' c' ∧ c' k' = C.gates.length - 1 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro k c hc hm
    by_cases hk : c k = C.gates.length - 1
    · exact ⟨k, c, hc, hk⟩
    · obtain ⟨r, hr, hc'⟩ := step_ext hmin hH hF hfut hlast k c hc hk
      have hrs : r < C.gates.length := by
        have := hc'.1 (k + 1) le_rfl
        simpa using this
      exact ih (C.gates.length - 1 - r) (by have := hc.1 k le_rfl; omega) (k + 1) _ hc'
        (by simp)

theorem finish {n : ℕ} {C : Circuit} (k : ℕ) (c : ℕ → ℕ) (hc : ChainInv n C.gates k c)
    (hck : c k = C.gates.length - 1) (hs : 0 < C.gates.length)
    (hfut : ∀ t (ht : t < C.gates.length), ∀ i ∈ deps C.gates[t], i < n + 1 + t)
    (hlast : C.output = n + 1 + (C.gates.length - 1)) :
    ∃ (k : ℕ) (c : Fin (k + 1) → Fin C.gates.length), StrictMono c ∧ (c (Fin.last k)).val + 1 = C.gates.length ∧ C.output = n + 1 + (c (Fin.last k)).val ∧ (∀ i : Fin (k + 1), (C.gates.get (c i)).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get (c i)).inputs.length = 2) ∧ n ∈ (C.gates.get (c 0)).inputs ∧ (∀ i : Fin k, n + 1 + (c i.castSucc).val ∈ (C.gates.get (c i.succ)).inputs) ∧ (∀ j : Fin C.gates.length, ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some n ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ n ∈ (C.gates.get j).inputs) → j = c 0) ∧ (∀ (i : Fin k) (j : Fin C.gates.length), ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some (n + 1 + (c i.castSucc).val) ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (n + 1 + (c i.castSucc).val) ∈ (C.gates.get j).inputs) → j = c i.succ) ∧ (∀ j : Fin C.gates.length, Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n (n + 1 + j.val) ↔ ∃ i : Fin (k + 1), c i = j) ∧ (∃ w ∈ (C.gates.get (c 0)).inputs, w ≠ n ∧ w < n + 1 + (c 0).val ∧ ¬ Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n w) ∧ (∀ i : Fin k, ∃ w ∈ (C.gates.get (c i.succ)).inputs, w ≠ n + 1 + (c i.castSucc).val ∧ w ≠ n ∧ w < n + 1 + (c i.succ).val ∧ ¬ Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n w) := by
  classical
  have hA := hc.1
  have hR : ∀ (a : ℕ) (j : Fin C.gates.length),
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
        (C.gates.get j).inputs.head? = some a ∨
        (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)
      ↔ a ∈ deps C.gates[j.val] := by
    intro a j
    rw [mem_deps_iff, List.get_eq_getElem]
  have hreach : ∀ w, Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length,
      b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
        (C.gates.get j).inputs.head? = some a ∨
        (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs))
      n w → ∃ i ≤ k, w = n + 1 + c i := by
    intro w h
    induction h with
    | single hab =>
      obtain ⟨j, rfl, hj⟩ := hab
      rw [hR] at hj
      exact ⟨0, Nat.zero_le _, by rw [hc.2.2.2.2.1 j j.isLt hj]⟩
    | tail _ hbc ih =>
      obtain ⟨i, hi, rfl⟩ := ih
      obtain ⟨j, rfl, hj⟩ := hbc
      rw [hR] at hj
      by_cases hik : i < k
      · exact ⟨i + 1, hik, by rw [hc.2.2.2.2.2.1 i hik j j.isLt hj]⟩
      · have hik' : i = k := by omega
        subst hik'
        have := hfut j j.isLt _ hj
        omega
  have hreach' : ∀ i ≤ k, Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length,
      b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
        (C.gates.get j).inputs.head? = some a ∨
        (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs))
      n (n + 1 + c i) := by
    intro i hi
    induction i with
    | zero =>
      apply Relation.TransGen.single
      refine ⟨⟨c 0, hA 0 hi⟩, rfl, ?_⟩
      rw [hR]
      have h1 := hc.2.2.2.1.1
      have h2 := (hc.2.2.1 0 hi).1
      rw [getD_dflt _ _ (hA 0 hi)] at h1 h2
      rw [or_deps h2]
      exact h1
    | succ i ih =>
      apply Relation.TransGen.tail (ih (by omega))
      refine ⟨⟨c (i + 1), hA (i + 1) hi⟩, rfl, ?_⟩
      rw [hR]
      have h1 := hc.2.2.2.1.2 i (by omega)
      have h2 := (hc.2.2.1 (i + 1) hi).1
      rw [getD_dflt _ _ (hA (i + 1) hi)] at h1 h2
      rw [or_deps h2]
      exact h1
  have hget : ∀ (i : ℕ) (hi : i ≤ k),
      C.gates.get ⟨c i, hA i hi⟩ = C.gates.getD (c i) dflt := by
    intro i hi
    rw [List.get_eq_getElem, getD_dflt _ _ (hA i hi)]
  refine ⟨k, fun i => ⟨c i.val, hA i.val (by omega)⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Fin.strictMono_iff_lt_succ]
    intro i
    simp only [Fin.coe_castSucc, Fin.val_succ, Fin.mk_lt_mk]
    exact hc.2.1 i i.isLt
  · simp only [Fin.val_last]
    omega
  · simp only [Fin.val_last]
    rw [hlast, hck]
  · intro i
    rw [hget i.val (by omega)]
    exact hc.2.2.1 i.val (by omega)
  · rw [hget (0 : Fin (k + 1)).val (by simp)]
    simp only [Fin.val_zero]
    exact hc.2.2.2.1.1
  · intro i
    simp only [Fin.coe_castSucc, Fin.val_succ]
    rw [hget (i.val + 1) (by omega)]
    exact hc.2.2.2.1.2 i.val i.isLt
  · intro j hj
    rw [hR] at hj
    apply Fin.ext
    simp only [Fin.val_zero]
    exact hc.2.2.2.2.1 j j.isLt hj
  · intro i j hj
    rw [hR] at hj
    apply Fin.ext
    simp only [Fin.coe_castSucc, Fin.val_succ] at hj ⊢
    exact hc.2.2.2.2.2.1 i.val i.isLt j j.isLt hj
  · intro j
    constructor
    · intro h
      obtain ⟨i, hi, hw⟩ := hreach _ h
      exact ⟨⟨i, by omega⟩, Fin.ext (by simp only; omega)⟩
    · rintro ⟨i, rfl⟩
      exact hreach' i.val (by omega)
  · obtain ⟨w, hw, hw1, hw2⟩ := hc.2.2.2.2.2.2.1
    refine ⟨w, by rw [hget (0 : Fin (k + 1)).val (by simp)]; simpa using hw, hw1,
      by simpa using hw2, ?_⟩
    intro h
    obtain ⟨i, hi, rfl⟩ := hreach w h
    have := chain_mono hc 0 i (Nat.zero_le _) hi
    omega
  · intro i
    obtain ⟨w, hw, hw1, hw2, hw3⟩ := hc.2.2.2.2.2.2.2 i.val i.isLt
    simp only [Fin.coe_castSucc, Fin.val_succ]
    refine ⟨w, by rw [hget (i.val + 1) (by omega)]; exact hw, hw1, hw2, hw3, ?_⟩
    intro h
    obtain ⟨i', hi', rfl⟩ := hreach _ h
    have hlt : i' ≤ i.val := by
      by_contra hgt
      push_neg at hgt
      have := chain_mono hc (i.val + 1) i' hgt hi'
      omega
    have hne : i' ≠ i.val := by
      intro h'
      subst h'
      exact hw1 rfl
    have hor := (hc.2.2.1 (i.val + 1) (by omega)).1
    rw [getD_dflt _ _ (hA (i.val + 1) (by omega))] at hor
    rw [getD_dflt _ _ (hA (i.val + 1) (by omega))] at hw
    rw [← or_deps hor] at hw
    have := hc.2.2.2.2.2.1 i' (by omega) (c (i.val + 1)) (hA _ (by omega)) hw
    have := chain_inj hc (i.val + 1) (i' + 1) (by omega) (by omega) this
    omega

theorem main_568 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (H : (Fin n → Bool) → Bool), PEqualNP.MetaComplexity.IsMinimalCircuit (n + 1) C → (∃ y y' : Fin n → Bool, H y ≠ H y') → (∀ x : Fin (n + 1) → Bool, PEqualNP.MetaComplexity.circuitFun (n + 1) C x = (x (Fin.last n) || H (fun i : Fin n => x i.castSucc))) → ∃ (k : ℕ) (c : Fin (k + 1) → Fin C.gates.length), StrictMono c ∧ (c (Fin.last k)).val + 1 = C.gates.length ∧ C.output = n + 1 + (c (Fin.last k)).val ∧ (∀ i : Fin (k + 1), (C.gates.get (c i)).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get (c i)).inputs.length = 2) ∧ n ∈ (C.gates.get (c 0)).inputs ∧ (∀ i : Fin k, n + 1 + (c i.castSucc).val ∈ (C.gates.get (c i.succ)).inputs) ∧ (∀ j : Fin C.gates.length, ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some n ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ n ∈ (C.gates.get j).inputs) → j = c 0) ∧ (∀ (i : Fin k) (j : Fin C.gates.length), ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some (n + 1 + (c i.castSucc).val) ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (n + 1 + (c i.castSucc).val) ∈ (C.gates.get j).inputs) → j = c i.succ) ∧ (∀ j : Fin C.gates.length, Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n (n + 1 + j.val) ↔ ∃ i : Fin (k + 1), c i = j) ∧ (∃ w ∈ (C.gates.get (c 0)).inputs, w ≠ n ∧ w < n + 1 + (c 0).val ∧ ¬ Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n w) ∧ (∀ i : Fin k, ∃ w ∈ (C.gates.get (c i.succ)).inputs, w ≠ n + 1 + (c i.castSucc).val ∧ w ≠ n ∧ w < n + 1 + (c i.succ).val ∧ ¬ Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n w) := by
  intro n C H hmin hH hF'
  have hF : ∀ (y : Fin n → Bool) (b : Bool),
      circuitFun (n + 1) C (Fin.snoc y b) = (b || H y) := by
    intro y b
    rw [hF' (Fin.snoc y b)]
    simp [Fin.snoc_last, Fin.snoc_castSucc]
  obtain ⟨c0, hc0, hxu, hor0, ⟨b, hbn, hbl, hdc⟩, hfut⟩ := base hmin hH hF
  obtain ⟨hspos, hlast⟩ := output_last hmin hH hF hfut
  have hdin : deps C.gates[c0] = C.gates[c0].inputs := or_deps hor0
  have hinit : ChainInv n C.gates 0 (fun _ => c0) := by
    have hg : C.gates.getD c0 dflt = C.gates[c0] := getD_dflt _ _ hc0
    refine ⟨fun _ _ => hc0, fun j hj => absurd hj (Nat.not_lt_zero _), ?_, ⟨?_, ?_⟩, ?_, ?_, ⟨?_, ?_⟩⟩
    · intro j _
      rw [hg]
      refine ⟨hor0, ?_⟩
      rw [← hdin]
      rcases hdc with h | h <;> rw [h] <;> rfl
    · rw [hg, ← hdin]
      rcases hdc with h | h <;> rw [h] <;> simp
    · intro j hj; exact absurd hj (Nat.not_lt_zero _)
    · intro t ht hd; exact hxu t ht hd
    · intro j hj; exact absurd hj (Nat.not_lt_zero _)
    · refine ⟨b, ?_, hbn, hbl⟩
      rw [hg, ← hdin]
      rcases hdc with h | h <;> rw [h] <;> simp
    · intro j hj; exact absurd hj (Nat.not_lt_zero _)
  obtain ⟨k, c, hc, hck⟩ := chain_full hmin hH hF hfut hlast _ 0 _ hinit rfl
  exact finish k c hc hck hspos hfut hlast

end PEqualNP.Outside.L568

theorem PEqualNP.Outside.L_meta_568 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (H : (Fin n → Bool) → Bool), PEqualNP.MetaComplexity.IsMinimalCircuit (n + 1) C → (∃ y y' : Fin n → Bool, H y ≠ H y') → (∀ x : Fin (n + 1) → Bool, PEqualNP.MetaComplexity.circuitFun (n + 1) C x = (x (Fin.last n) || H (fun i : Fin n => x i.castSucc))) → ∃ (k : ℕ) (c : Fin (k + 1) → Fin C.gates.length), StrictMono c ∧ (c (Fin.last k)).val + 1 = C.gates.length ∧ C.output = n + 1 + (c (Fin.last k)).val ∧ (∀ i : Fin (k + 1), (C.gates.get (c i)).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get (c i)).inputs.length = 2) ∧ n ∈ (C.gates.get (c 0)).inputs ∧ (∀ i : Fin k, n + 1 + (c i.castSucc).val ∈ (C.gates.get (c i.succ)).inputs) ∧ (∀ j : Fin C.gates.length, ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some n ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ n ∈ (C.gates.get j).inputs) → j = c 0) ∧ (∀ (i : Fin k) (j : Fin C.gates.length), ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some (n + 1 + (c i.castSucc).val) ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (n + 1 + (c i.castSucc).val) ∈ (C.gates.get j).inputs) → j = c i.succ) ∧ (∀ j : Fin C.gates.length, Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n (n + 1 + j.val) ↔ ∃ i : Fin (k + 1), c i = j) ∧ (∃ w ∈ (C.gates.get (c 0)).inputs, w ≠ n ∧ w < n + 1 + (c 0).val ∧ ¬ Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n w) ∧ (∀ i : Fin k, ∃ w ∈ (C.gates.get (c i.succ)).inputs, w ≠ n + 1 + (c i.castSucc).val ∧ w ≠ n ∧ w < n + 1 + (c i.succ).val ∧ ¬ Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n w) :=
  PEqualNP.Outside.L568.main_568
