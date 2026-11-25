import Mathlib
import PEqualNP.Defs

/-!
The edge function of the Petersen graph minus the edge 0-1 has an AND/OR/NOT circuit of fan-in two
with 21 gates (NOT gates counted). The circuit was found by an exact SAT search; it is checked
on all 1024 inputs by `decide +kernel` (the pattern of `PEqualNP.Outside.L_meta_1001`).
-/

namespace PEqualNP.Outside.Scratch_meta9755

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- The circuit: wires 0-9 are the inputs, gate `j` is wire `10 + j`, the output is the last gate. -/
def C0 : Circuit := ⟨[⟨GateOp.or, [1, 3]⟩, ⟨GateOp.or, [10, 7]⟩, ⟨GateOp.and, [2, 11]⟩, ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [13, 9]⟩, ⟨GateOp.and, [4, 14]⟩, ⟨GateOp.or, [0, 7]⟩, ⟨GateOp.or, [16, 8]⟩, ⟨GateOp.and, [5, 17]⟩, ⟨GateOp.or, [1, 8]⟩, ⟨GateOp.or, [19, 9]⟩, ⟨GateOp.and, [6, 20]⟩, ⟨GateOp.and, [8, 3]⟩, ⟨GateOp.and, [9, 7]⟩, ⟨GateOp.or, [12, 15]⟩, ⟨GateOp.or, [24, 18]⟩, ⟨GateOp.or, [25, 21]⟩, ⟨GateOp.or, [26, 22]⟩, ⟨GateOp.or, [27, 23]⟩, ⟨GateOp.not, [28]⟩, ⟨GateOp.not, [29]⟩], 30⟩

theorem ok0 : FanInTwo C0 := by
  intro g hg
  simp only [C0, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev0 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    C0.eval [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9] = ((b0 && b4) || (b0 && b5) || (b1 && b2) || (b1 && b6) || (b2 && b3) || (b2 && b7) || (b3 && b4) || (b3 && b8) || (b4 && b9) || (b5 && b7) || (b5 && b8) || (b6 && b8) || (b6 && b9) || (b7 && b9)) := by
  decide +kernel

theorem ofFn10 (x : Fin 10 → Bool) : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9] := by
  simp [List.ofFn_succ]

end PEqualNP.Outside.Scratch_meta9755

theorem PEqualNP.Outside.Scratch_meta9755 : PEqualNP.MetaComplexity.HasCircuitSize 10 (fun x : Fin 10 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6) || (x 2 && x 3) || (x 2 && x 7) || (x 3 && x 4) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 5 && x 8) || (x 6 && x 8) || (x 6 && x 9) || (x 7 && x 9)) 21 :=
  ⟨PEqualNP.Outside.Scratch_meta9755.C0, PEqualNP.Outside.Scratch_meta9755.ok0, by decide, fun x => by
      rw [PEqualNP.Outside.Scratch_meta9755.ofFn10]
      exact PEqualNP.Outside.Scratch_meta9755.ev0 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9)⟩
