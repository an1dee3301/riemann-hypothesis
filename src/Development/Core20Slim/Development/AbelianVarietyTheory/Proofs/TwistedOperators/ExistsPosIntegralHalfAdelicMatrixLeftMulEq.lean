module

public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceHalfAdelicMatrixAddSubgroup
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Action
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.HalfAverage
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfAverage

theorem integral_leftMul_eq_smul : ∀ (D : D7) (a : AE D) (m n : ℕ) (M M' : Matrix (Fin m) (Fin m) (AE D)),
    M * M' = 1 → M' * M = 1 → ∃ κ : ℝ, 0 < κ ∧ ∀ φ : halfMx a m n → ℂ,
      ∫ t, φ (leftMul a M t) ∂haarHalf a m n = κ * ∫ t, φ t ∂haarHalf a m n := by
  intro D a m n M M' h1 h2
  haveI : IsTopologicalRing (AE D) := (Formalism.IndefR.Eqv.ae_facts D).1
  haveI : SecondCountableTopology (AE D) := (Formalism.IndefR.Eqv.ae_facts D).2.2.2.1
  haveI : SecondCountableTopology (Mx D m n) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin n → AE D))
  haveI : SecondCountableTopology (halfMx a m n) := Topology.IsInducing.subtypeVal.secondCountableTopology
  have hc : ∀ N : Matrix (Fin m) (Fin m) (AE D), Continuous (leftMul a (n := n) N) := fun N =>
    (continuous_const.matrix_mul continuous_subtype_val).subtype_mk _
  let e : halfMx a m n ≃ₜ+ halfMx a m n :=
    { toFun := leftMul a M
      invFun := leftMul a M'
      left_inv := fun t => Subtype.ext (by
        rw [leftMul_coe, leftMul_coe, ← Matrix.mul_assoc, h2, Matrix.one_mul])
      right_inv := fun t => Subtype.ext (by
        rw [leftMul_coe, leftMul_coe, ← Matrix.mul_assoc, h1, Matrix.one_mul])
      map_add' := fun x y => Subtype.ext (by
        rw [AddSubgroup.coe_add, leftMul_coe, leftMul_coe, leftMul_coe, AddSubgroup.coe_add, Matrix.mul_add])
      continuous_toFun := hc M
      continuous_invFun := hc M' }
  haveI : ((haarHalf a m n).map e).IsAddHaarMeasure := e.isAddHaarMeasure_map _
  have heq := Measure.isAddLeftInvariant_eq_smul ((haarHalf a m n).map e) (haarHalf a m n)
  refine ⟨(Measure.addHaarScalarFactor ((haarHalf a m n).map e) (haarHalf a m n) : ℝ),
    by exact_mod_cast Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _, fun φ => ?_⟩
  let em : halfMx a m n ≃ᵐ halfMx a m n := e.toHomeomorph.toMeasurableEquiv
  have h3 : ∫ t, φ (leftMul a M t) ∂haarHalf a m n = ∫ t, φ t ∂((haarHalf a m n).map e) := by
    have := integral_map_equiv (μ := haarHalf a m n) em φ
    exact this.symm
  have h4 := congrArg (fun μ : Measure (halfMx a m n) => ∫ t, φ t ∂μ) heq
  rw [h3, h4, integral_smul_nnreal_measure]
  simp [Complex.real_smul, NNReal.smul_def]

end GlobalTheory.HalfAverage
