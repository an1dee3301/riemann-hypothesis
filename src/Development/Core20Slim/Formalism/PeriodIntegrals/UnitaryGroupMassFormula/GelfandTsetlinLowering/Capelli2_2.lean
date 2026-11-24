module

public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.ZScalarVanish
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuantumDetHighestWeightHolds
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ShiftedGeneratorEqIteSmulAdd
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.GeneratorCommutatorQuantumDet
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.CapelliZ
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.IoPolDiagHw
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HwIrred
public import Formalism.LocalRingCardinality.DataCoeff
public import Init.Prelude
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

noncomputable section

namespace PI.WGL

open Formalism.BasicNotions MvPolynomial

theorem capelli_scalar_identity : CapelliZ :=
  capelliZ_of fun h lam mu φ hφ s hs u => capScalar highest_weight_irreducible h lam mu φ hφ s hs u

end PI.WGL
