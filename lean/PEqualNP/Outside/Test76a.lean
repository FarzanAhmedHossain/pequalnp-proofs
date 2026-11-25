import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Test76a

open PEqualNP.CircuitLowerBounds

/-- The circuit: 33 gates w_u = x_u OR y_u, then 43 gates on the w's. -/
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

theorem ops : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  decide

theorem mono : PEqualNP.MetaComplexity.Monotone2 C := by
  intro g hg
  obtain ⟨h1, h2⟩ := ops g hg
  refine ⟨?_, h2⟩
  rcases h1 with h | h <;> simp [h]

theorem size_le : C.size ≤ 76 := by decide

theorem rep : PEqualNP.Represents.Represents (fun a b : Fin 33 => decide (∃ i : Fin 11, ((a.val = i.val ∨ a.val = 11 + i.val) ∧ (b.val = (i.val + 1) % 11 ∨ b.val = 22 + i.val)) ∨ ((b.val = i.val ∨ b.val = 11 + i.val) ∧ (a.val = (i.val + 1) % 11 ∨ a.val = 22 + i.val)))) C := by
  decide

end PEqualNP.Outside.Test76a

theorem PEqualNP.Outside.Test76a : PEqualNP.Represents.RepSizeAtMost (fun a b : Fin 33 => decide (∃ i : Fin 11, ((a.val = i.val ∨ a.val = 11 + i.val) ∧ (b.val = (i.val + 1) % 11 ∨ b.val = 22 + i.val)) ∨ ((b.val = i.val ∨ b.val = 11 + i.val) ∧ (a.val = (i.val + 1) % 11 ∨ a.val = 22 + i.val)))) 76 :=
  ⟨PEqualNP.Outside.Test76a.C, PEqualNP.Outside.Test76a.mono, PEqualNP.Outside.Test76a.size_le,
    PEqualNP.Outside.Test76a.rep⟩
