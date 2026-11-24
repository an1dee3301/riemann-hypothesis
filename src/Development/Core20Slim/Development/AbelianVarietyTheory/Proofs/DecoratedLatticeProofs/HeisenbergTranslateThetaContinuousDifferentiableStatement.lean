module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergTranslateThetaContinuousDifferentiable
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Order.Real
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergTranslate_theta_continuous_differentiable_sobolev : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D) (k : ℕ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → Filter.Tendsto (fun u : WO S T => supSob ψ θ k (heisO ψ S T u f - f)) (nhds 0) (nhds 0) ∧ ∀ L : ℝ →+ WO S T, Continuous L → (∀ t, (L t).map (finPart D) = 0) → IsThetaFunO ψ S T (fun p => deriv (fun t : ℝ => heisO ψ S T (L t) f p) 0) ∧ Filter.Tendsto (fun t : ℝ => supSob ψ θ k ((t⁻¹ : ℂ) • (heisO ψ S T (L t) f - f) - fun p => deriv (fun t : ℝ => heisO ψ S T (L t) f p) 0)) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
  first | exact @GlobalTheory.HeisTaylor.heisO_taylor | exact GlobalTheory.HeisTaylor.heisO_taylor | (intros; apply GlobalTheory.HeisTaylor.heisO_taylor <;> assumption)
