module

public import Development.Core20Slim.Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.EndInt
public import Development.Core20Slim.Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.HasCMByStable
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.SecondCoeffConsistency
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.CompInv
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open PowerSeries

noncomputable section

namespace Formalism.L2.KerInert.PN


section Field

variable {K : Type} [Field K] [CharZero K] (W : WeierstrassCurve K) (C : WeierstrassCurve.VariableChange K)

theorem g_change' : Formalism.L2.Th1.A.g₂ (C • W) = ((C.u⁻¹ : Kˣ) : K) ^ 4 * Formalism.L2.Th1.A.g₂ W ∧
    Formalism.L2.Th1.A.g₃ (C • W) = ((C.u⁻¹ : Kˣ) : K) ^ 6 * Formalism.L2.Th1.A.g₃ W := by
  refine ⟨?_, ?_⟩
  · simp only [Formalism.L2.Th1.A.g₂, WeierstrassCurve.variableChange_c₄]
    ring
  · simp only [Formalism.L2.Th1.A.g₃, WeierstrassCurve.variableChange_c₆]
    ring












end Field

section Cong

open Formalism.L2.Th1.C Formalism.L2.Th1.C.Pts

variable {K : Type} [Field K] [CharZero K] {R' : Subring K}




end Cong

section Transfer

open Formalism.L2.Th1.C Formalism.L2.Th1.C.Pts Formalism.L2.Th1.C.Calc

variable {K : Type} [Field K] [CharZero K] {R' : Subring K}






end Transfer

section Main

open Formalism.BasicNotions Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric NumberField Formalism.L2.KerInert.IwahoriBlocks


end Main

end Formalism.L2.KerInert.PN

namespace Formalism.L2.KerInert


end Formalism.L2.KerInert
