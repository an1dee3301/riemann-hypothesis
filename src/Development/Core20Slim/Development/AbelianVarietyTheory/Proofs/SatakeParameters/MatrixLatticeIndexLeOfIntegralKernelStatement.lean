module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixLatticeIndexLeOfIntegralKernel
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependent
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntMat
public import Formalism.SatakeDualWeyl.StatementF
public import Init.Data.Int.Basic
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

@[expose] public section

open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixLatticeIndex_le_of_integral_kernel : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q a b : ℕ) (x y : Matrix (Fin a) (Fin b) L),
    Formalism.UG.IsUnramInv ϖ σ q →
    (∀ u : Fin b → L, (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (Matrix.mulVec x u) i ∈ Formalism.UG.intL L) → ∀ i, (Matrix.mulVec y u) i ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.HoweDuality.latIdx y ≤ GlobalTheory.Hk3.HoweDuality.latIdx x := by
  first | exact @GlobalTheory.Hk3.HoweDuality.latIdx_le_of_ker | exact GlobalTheory.Hk3.HoweDuality.latIdx_le_of_ker | (intros; apply GlobalTheory.Hk3.HoweDuality.latIdx_le_of_ker <;> assumption)
