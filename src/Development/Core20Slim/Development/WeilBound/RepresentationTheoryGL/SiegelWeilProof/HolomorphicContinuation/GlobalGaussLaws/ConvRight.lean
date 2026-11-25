module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FourierZeroN
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
public import Development.AbelianVarietyTheory.Definitions.Foundations.AnalyticOnNhdTsumNpow
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
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
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

def ConvRight : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν Φ, PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν Φ → PositivityTheory.PfSWUS.InRange V n →
    ∃ σ : ℝ, ∀ z : ℂ, σ < z.re → ∀ g, GlobalTheory.Eis.CosetConv (P D n) (GF D n) (sect ω H Φ z) g

def ThLin : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν Φ Φ', PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν Φ →
    PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν Φ' → PositivityTheory.PfSWUS.InRange V n →
    ∀ g, thetaInt ω ν (Φ + Φ') g = thetaInt ω ν Φ g + thetaInt ω ν Φ' g

def GLamBd : Prop :=
  ∀ (D : D7) (n : ℕ) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ L ∈ lamSet (n := n) ψ,
    (∀ (a : ℂ) (F F' : G D n → ℂ), Continuous F → Continuous F' → (∀ γ ∈ GF D n, ∀ g, F (γ * g) = F g) →
      (∀ γ ∈ GF D n, ∀ g, F' (γ * g) = F' g) → L (a • F + F') = a * L F + L F') ∧
    ∃ C : Set (G D n), IsCompact C ∧ ∀ (F : G D n → ℂ) (M : ℝ), Continuous F → (∀ γ ∈ GF D n, ∀ g, F (γ * g) = F g) →
      (∀ x ∈ C, ‖F x‖ ≤ M) → ‖L F‖ ≤ M

def GLsing : Prop :=
  ∀ (D : D7) (n : ℕ) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (τ : D.what₂.Tau) (ι : GR n →* G D n), IsCharAF D.host.F ψ →
    IsInfFam θ → IsPlaceEmb θ τ ι → ∀ F : G D n → ℂ, Continuous F → (∀ γ ∈ GF D n, ∀ g, F (γ * g) = F g) →
    (∀ L ∈ lamSet (n := n) ψ, L F = 0) → ∀ ψ₀, IsSingTest ψ₀ → ∀ (nb : (Fin n → Fin n → ℝ) → GR n), (∀ x, mR (nb x) = nU (herm x)) →
      ∀ (g : G D n) (a b : GR n), ∫ x, F (g * ι (a * nb x * b)) * ψ₀ x = 0

def LNZ : Prop :=
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (l : D.what₂.Tau → ℝ), IsCharAF D.host.F ψ → IsInfFam θ →
    HasRealPar ψ θ l → ∀ τ, l τ ≠ 0

def MainSt : Prop :=
  AbsThm → SFrame → SEmb → SigOK → SplitFock → TensMem → LocOpEx → LocInst → LinSec → GSplit → GIauto → GIk → GIinv →
    GIdil → EisStrong → GLamBd → GLsing → PositivityTheory.PfSWUS.CoefND → ConvRight → ThLin → LNZ →
    ∀ D n V ψ χ θ μ ω H l s ν Φ, PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν Φ → PositivityTheory.PfSWUS.InRange V n → 1 ≤ n →
      ∀ g, HolValueAt (PositivityTheory.PfSWUS.eis ω H Φ g) (s0 V n) (thetaInt ω ν Φ g)

end PositivityTheory.Rg.Sw.Glob
