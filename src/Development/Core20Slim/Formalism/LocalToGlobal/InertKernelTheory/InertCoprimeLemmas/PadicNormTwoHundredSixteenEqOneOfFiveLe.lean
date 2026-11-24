module

public import Mathlib
public import Development.Core20Slim.Formalism.LocalToGlobal.InertKernelTheory.DefsSigma
public import Development.Core20Slim.Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.FormalExponentialAgree
public import Development.Core20Slim.Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.PowerSeriesEmbedding
public import Development.Core20Slim.Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.ExistsPeriodPairOfIsLat
public import Development.Core20Slim.Formalism.LocalToGlobal.TorsionIntegrality.ComplexLatticeClosure.LamConjTheta0
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EllipticOnePole
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.IsogenyFormulaInstance
public import Development.Core20Slim.Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.HasCMByStable
public import Development.Core20Slim.Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinRecursion
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.TwoTorsionU
public import Development.Core20Slim.Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.CmAll
public import Formalism.GaussJetBounds.GaussJetProofs.NormNatCastEqPowPadicValNat
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.CompInv
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.CharP.IntermediateField
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.UniformField
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

namespace Formalism.L2.KerInert.Sigma

open NumberField Formalism.BasicNotions

theorem lamC_coe {p : ℕ} [Fact p.Prime] (lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p]) (a : Formalism.MainNotions.TaylorLogMetric.Qbar) :
    Formalism.MainNotions.TaylorLogMetric.lamC lam (a : ℂ) = lam a := by
  unfold Formalism.MainNotions.TaylorLogMetric.lamC
  rw [dite_eq_left a.2]



theorem wModel_g {p : ℕ} [Fact p.Prime] (lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ)
    (a2 a3 : Formalism.MainNotions.TaylorLogMetric.Qbar) (h2 : Formalism.MainNotions.TaylorLogMetric.g2 Λ = a2) (h3 : Formalism.MainNotions.TaylorLogMetric.g3 Λ = a3) :
    Formalism.L2.Th1.A.g₂ (Formalism.MainNotions.TaylorLogMetric.wModel lam Λ) = lam a2 ∧ Formalism.L2.Th1.A.g₃ (Formalism.MainNotions.TaylorLogMetric.wModel lam Λ) = lam a3 := by
  have e4 : Formalism.MainNotions.TaylorLogMetric.lamC lam (-(Formalism.MainNotions.TaylorLogMetric.g2 Λ) / 4) = -(lam a2) / 4 := by
    have : -(Formalism.MainNotions.TaylorLogMetric.g2 Λ) / 4 = ((-a2 / 4 : Formalism.MainNotions.TaylorLogMetric.Qbar) : ℂ) := by rw [h2]; push_cast; rfl
    rw [this, lamC_coe, map_div₀, map_neg, map_ofNat]
  have e6 : Formalism.MainNotions.TaylorLogMetric.lamC lam (-(Formalism.MainNotions.TaylorLogMetric.g3 Λ) / 4) = -(lam a3) / 4 := by
    have : -(Formalism.MainNotions.TaylorLogMetric.g3 Λ) / 4 = ((-a3 / 4 : Formalism.MainNotions.TaylorLogMetric.Qbar) : ℂ) := by rw [h3]; push_cast; rfl
    rw [this, lamC_coe, map_div₀, map_neg, map_ofNat]
  simp only [Formalism.L2.Th1.A.g₂, Formalism.L2.Th1.A.g₃, WeierstrassCurve.c₄, WeierstrassCurve.c₆, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, Formalism.MainNotions.TaylorLogMetric.wModel, e4, e6]
  constructor <;> ring



section Int

variable {p : ℕ} [Fact p.Prime]











end Int



end Formalism.L2.KerInert.Sigma
