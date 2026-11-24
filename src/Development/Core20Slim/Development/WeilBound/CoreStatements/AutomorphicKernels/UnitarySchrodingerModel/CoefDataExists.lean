module

public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.Core20Slim.Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinPolesStd
public import Development.Core20Slim.Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.Core20Slim.Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.Definitions.Foundations.AnalyticOnNhdTsumNpow
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.Core20Slim.Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

variable {D : D7} {n : ℕ}

def IsNMap (nb : hermA D n → G D n) : Prop := ∀ b, mat (nb b) = blk4 1 b.1 0 1

def fc (ψ : AddChar (AF D.host.F) ℂ) (lam : Measure (hermA D n)) (𝓖 : Set (hermA D n)) (nb : hermA D n → G D n)
    (f : G D n → ℂ) (β : HermE D n) (g : G D n) : ℂ :=
  ∫ b in 𝓖, f (nb b * g) * ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n))) ∂lam

def eis {θ : InfFam D} {V : HSp D} (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (H : G D n → ℝ≥0)
    (Φ : schwartzA θ V.rank n) (g : G D n) : ℂ → ℂ :=
  fun z => GlobalTheory.Eis.cosetSum (P D n) (GF D n) (sect ω H Φ z) g

structure Std (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D)
    (μ : Measure (Mx D V.rank n)) (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (H : G D n → ℝ≥0)
    (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (ν : Measure (GA D V))
    (Φ : schwartzA θ V.rank n) : Prop where
  hψ : IsCharAF D.host.F ψ
  hχ : IsHeckeChar D χ
  hη : ResEta D χ V.rank
  hθ : IsInfFam θ
  hμ : ∃ 𝓕, IsCovolOne (ratMx D V.rank n) μ 𝓕
  hω : IsWeilSch ψ χ θ V μ ω
  hH : IsHeight H
  hl : HasRealPar ψ θ l
  hs : ∀ τ, IsCartanInv (gramAt D V τ) (s τ)
  hν : ν.IsHaarMeasure
  hΦ : Φ.1 ∈ fockA θ V n l s

def InRange (V : HSp D) (n : ℕ) : Prop :=
  n < V.rank ∧ V.rank ≤ 2 * n ∧ n + Formalism.MainNotions.SchurIrreducible.wittIdx V < V.rank

def CoefData (nb : hermA D n → G D n) (lam : Measure (hermA D n)) (𝓖 : Set (hermA D n)) : Prop :=
  IsNMap nb ∧ IsCovolOneH lam 𝓖

def ThetaAuto : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν Φ, Std D n V ψ χ θ μ ω H l s ν Φ → InRange V n →
    Continuous (thetaInt ω ν Φ) ∧ LeftInv (GF D n) (thetaInt ω ν Φ)

def CoefND : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν Φ, Std D n V ψ χ θ μ ω H l s ν Φ → InRange V n →
  ∀ nb lam 𝓖, CoefData (D := D) (n := n) nb lam 𝓖 → ∀ (β : HermE D n), β.1.det ≠ 0 → ∀ g : G D n,
    HolValueAt (fun z => fc ψ lam 𝓖 nb (fun x => eis ω H Φ x z) β g) (s0 V n) (fc ψ lam 𝓖 nb (thetaInt ω ν Φ) β g)

def Unfold : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν Φ, Std D n V ψ χ θ μ ω H l s ν Φ → InRange V n →
  ∀ nb lam 𝓖, CoefData (D := D) (n := n) nb lam 𝓖 → ∀ w : G D n, mat w = blk4 0 1 (-1) 0 →
  ∀ (β : HermE D n), β.1.det ≠ 0 → ∀ (z : ℂ), (n : ℝ) / 2 < z.re → ∀ g : G D n,
    Integrable (fun b : hermA D n => sect ω H Φ z (w * nb b * g)) lam ∧
    fc ψ lam 𝓖 nb (fun x => eis ω H Φ x z) β g =
      ∫ b, sect ω H Φ z (w * nb b * g) * ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n))) ∂lam

def ThetaCoef : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν Φ, Std D n V ψ χ θ μ ω H l s ν Φ → InRange V n →
  ∀ nb lam 𝓖, CoefData (D := D) (n := n) nb lam 𝓖 → ∀ (β : HermE D n), β.1.det ≠ 0 → ∀ g : G D n,
    fc ψ lam 𝓖 nb (thetaInt ω ν Φ) β g = IfrB V ν (fun x => (ω g Φ).1 x) β

def FourierZero : Prop :=
  ∀ (D : D7) (n : ℕ) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ →
  ∀ nb lam 𝓖, CoefData (D := D) (n := n) nb lam 𝓖 → ∀ f : G D n → ℂ, Continuous f → LeftInv (GF D n) f →
    (∀ β g, fc ψ lam 𝓖 nb f β g = 0) → f = 0

def CoefDataExists : Prop :=
  ∀ (D : D7) (n : ℕ), ∃ nb lam 𝓖, CoefData (D := D) (n := n) nb lam 𝓖

end PositivityTheory.PfSWUS

end
