module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBlockNFZeroOne
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullbackSchwartzLinearIndependentStatement
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.Core20Slim.Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
public import Development.Core20Slim.Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.ProjectiveLattices.IsProbabilityMeasureAutQuotientNormalized
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Order.Real
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Deg

variable {D : D7}

def rightMulEquiv {m r : ℕ} (a : Matrix (Fin r) (Fin r) D.host.E) (ha : a.det ≠ 0) :
    Matrix (Fin m) (Fin r) D.host.E ≃ Matrix (Fin m) (Fin r) D.host.E where
  toFun ξ := ξ * a
  invFun ξ := ξ * a⁻¹
  left_inv ξ := by
    have hu : IsUnit a.det := isUnit_iff_ne_zero.mpr ha
    simp [Matrix.mul_assoc, Matrix.mul_nonsing_inv a hu]
  right_inv ξ := by
    have hu : IsUnit a.det := isUnit_iff_ne_zero.mpr ha
    simp [Matrix.mul_assoc, Matrix.nonsing_inv_mul a hu]

theorem invPt_mul (V : HSp D) {r : ℕ} (h : GA D V) (ξ : Matrix (Fin V.rank) (Fin r) D.host.E)
    (a : Matrix (Fin r) (Fin r) D.host.E) :
    GlobalTheory.SiegelFormula.invPt V h (ξ * a) =
      HMul.hMul (GlobalTheory.SiegelFormula.invPt V h ξ) (a.map (incA D)) := by
  unfold GlobalTheory.SiegelFormula.invPt
  rw [Matrix.map_mul, Matrix.mul_assoc]

theorem absTheta_pull (V : HSp D) {r : ℕ} (φ : Mx D V.rank r → ℂ)
    (a : Matrix (Fin r) (Fin r) D.host.E) (ha : a.det ≠ 0) (h : GA D V) :
    GlobalTheory.SiegelFormula.absTheta V (pull a φ) h = GlobalTheory.SiegelFormula.absTheta V φ h := by
  unfold GlobalTheory.SiegelFormula.absTheta
  rw [← (rightMulEquiv (m := V.rank) a ha).tsum_eq
    (fun ξ => ‖φ (GlobalTheory.SiegelFormula.invPt V h ξ)‖ₑ)]
  refine tsum_congr fun ξ => ?_
  show ‖φ _‖ₑ = ‖φ (GlobalTheory.SiegelFormula.invPt V h (ξ * a))‖ₑ
  rw [invPt_mul]

theorem absThetaInt_pull (V : HSp D) (ν : Measure (GA D V)) {r : ℕ} (φ : Mx D V.rank r → ℂ)
    (a : Matrix (Fin r) (Fin r) D.host.E) (ha : a.det ≠ 0) :
    GlobalTheory.SiegelFormula.absThetaInt V ν (pull a φ) = GlobalTheory.SiegelFormula.absThetaInt V ν φ := by
  unfold GlobalTheory.SiegelFormula.absThetaInt
  have : GlobalTheory.SiegelFormula.absTheta V (pull a φ) = GlobalTheory.SiegelFormula.absTheta V φ :=
    funext (absTheta_pull V φ a ha)
  rw [this]

theorem hyp_pull : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (μ : Measure (Mx D V.rank r)) (lam : Measure (hermA D r)) (ν : Measure (GA D V))
    (φ : Mx D V.rank r → ℂ) (a : Matrix (Fin r) (Fin r) D.host.E), a.det ≠ 0 →
    Hyp D r V ψ θ μ lam ν φ → Hyp D r V ψ θ μ lam ν (pull a φ) := by
  intro D r V ψ θ μ lam ν φ a ha ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hli : LinearIndependent D.host.E a :=
    Matrix.linearIndependent_rows_of_isUnit ((Matrix.isUnit_iff_isUnit_det a).mpr (isUnit_iff_ne_zero.mpr ha))
  refine ⟨h1, h2, h3, h4, h5, h6, GlobalTheory.T.pullback_schwartz_linear_independent D θ h3 _ _ _ a hli φ h7, ?_⟩
  rw [absThetaInt_pull V ν φ a ha]
  exact h8

end GlobalTheory.CompanionTheory.WeilSiegel.Deg
