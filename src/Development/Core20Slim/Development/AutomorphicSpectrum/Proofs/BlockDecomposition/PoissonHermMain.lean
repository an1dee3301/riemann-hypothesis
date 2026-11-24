module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfHermEBijective
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaIntegralContinuousStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaIntegralLocallySummableBoundStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PoissonSummationHermitianLatticeStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinCoefficientsSummableStatement
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.Core20Slim.Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Prelude
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
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
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
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.HermPoisson

theorem poissonHerm_main : PositivityTheory.GramSchwartzFunctions.BC.PoissonHerm := by
  intro D r V ψ θ μ lam ν φ hH hJ
  obtain ⟨hm, hψ, hθ, hμ, ⟨𝓖, hlam⟩, -, hφ, -⟩ := hH
  have hc := GlobalTheory.T.theta_integral_continuous D r V ψ θ μ φ hψ hθ hμ hφ
  have hu := GlobalTheory.T.theta_integral_locally_summable_bound D r V ψ θ μ φ hm hψ hθ hμ hφ
  have hW := GlobalTheory.T.siegel_eisenstein_coefficients_summable D r V ψ θ μ lam 𝓖 φ hm hψ hθ hμ hlam hφ
  obtain ⟨-, hP⟩ := GlobalTheory.T.poisson_summation_hermitian_lattice D r ψ hψ lam 𝓖 hlam _ hc hu
  have hgW : ∀ β : HermE D r, (fun t : ratHerm D r => ∫ b, Jt ψ V μ φ b *
      ψ (-halfTr (Matrix.trace (HMul.hMul t.1.1 b.1 : Mx D r r))) ∂lam) ((hermEquiv (D := D) (r := r)) β) = W ψ V μ lam φ β :=
    fun β => (W_eq ψ V μ lam φ β).symm
  have hS : Summable (fun t : ratHerm D r => ∫ b, Jt ψ V μ φ b *
      ψ (-halfTr (Matrix.trace (HMul.hMul t.1.1 b.1 : Mx D r r))) ∂lam) := by
    refine (hermEquiv (D := D) (r := r)).summable_iff.1 ?_
    exact hW.congr fun β => (hgW β).symm
  have e := hP hS
  have hsumJ : ∑' b : HermE D r, J ψ V μ φ b = ∑' c : ratHerm D r, Jt ψ V μ φ c.1 :=
    (hermEquiv (D := D) (r := r)).tsum_eq (fun c => Jt ψ V μ φ c.1)
  have hsumW : ∑' β : HermE D r, W ψ V μ lam φ β = ∑' t : ratHerm D r, ∫ b, Jt ψ V μ φ b *
      ψ (-halfTr (Matrix.trace (HMul.hMul t.1.1 b.1 : Mx D r r))) ∂lam := by
    rw [← (hermEquiv (D := D) (r := r)).tsum_eq]
    exact tsum_congr fun β => (hgW β).symm
  rw [hsumJ, e, ← hsumW]
  exact hW.hasSum

end GlobalTheory.CompanionTheory.HermPoisson
