module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
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
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Ker (ipO)
open scoped TensorProduct ENNReal ComplexConjugate

namespace GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def hermAt (V W : HSp D) (τ : D.what₂.Tau) (z w : Matrix (Fin W.rank) (Fin V.rank) ℂ) : ℂ :=
  ((gramAt D V τ)⁻¹ * wᴴ * gramAt D W τ * z).trace

def symplAt (V W : HSp D) (τ : D.what₂.Tau) (z w : Matrix (Fin W.rank) (Fin V.rank) ℂ) : ℝ :=
  2 * (tauE D τ D.host.xi0 * hermAt V W τ z w).re


open Classical in
def commScalar (V W : HSp D) (τ τ' : D.what₂.Tau) (z w : Matrix (Fin W.rank) (Fin V.rank) ℂ) : ℂ :=
  if τ = τ' then -(2 * Real.pi * Complex.I) * (symplAt V W τ z w : ℂ) else 0

def Cocompact (V W : HSp D) : Prop := CompactSpace (WO V W ⧸ (ratL W V : AddSubgroup (WO V W)))

def SquareIntegrable (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) : Prop :=
  ∀ f, IsThetaFunO ψ V W f →
    (∀ γ ∈ ratL W V, ∀ x : WO V W, ‖f (γ + x)‖ = ‖f x‖) ∧
    (∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) ∧
    ∀ (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 μ →
      MemLp f 2 (μ.restrict 𝓕)

def HeisUnitary (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) : Prop :=
  (∀ (u v : WO V W) (f : WO V W → ℂ),
    heisO ψ V W u (heisO ψ V W v f) = ψ (symplOH V W u v) • heisO ψ V W (u + v) f) ∧
  (∀ (u : WO V W) (f : WO V W → ℂ), heisO ψ V W (-u) (heisO ψ V W u f) = f) ∧
  (∀ u f, IsThetaFunO ψ V W f → IsThetaFunO ψ V W (heisO ψ V W u f)) ∧
  (∀ (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 μ →
    ∀ u f f', IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' →
      ipO μ 𝓕 (heisO ψ V W u f) (heisO ψ V W u f') = ipO μ 𝓕 f f') ∧
  ∀ γ ∈ ratL W V, ∀ f, IsThetaFunO ψ V W f → heisO ψ V W γ f 0 = f 0

def DerSkew (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) : Prop :=
  ∀ (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ),
    (∀ f, IsThetaFunO ψ V W f → ∀ x, HasDerivAt (fun t : ℝ => heisO ψ V W (lineAt θ τ z t) f x)
      (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z f x) 0) ∧
    (∀ f, IsThetaFunO ψ V W f → IsThetaFunO ψ V W (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z f)) ∧
    ∀ (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 μ →
      ∀ f f', IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' →
        ipO μ 𝓕 (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z f) f' =
          -ipO μ 𝓕 f (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z f')

def DerComm (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) : Prop :=
  ∀ (τ τ' : D.what₂.Tau) (z w : Matrix (Fin W.rank) (Fin V.rank) ℂ),
    (∀ s t : ℝ, ψ (symplO V W (lineAt θ τ z s) (lineAt θ τ' w t)) =
      Complex.exp (s * t * commScalar V W τ τ' z w)) ∧
    ∀ f, IsThetaFunO ψ V W f →
      Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ' w f) -
        Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ' w (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z f) =
          commScalar V W τ τ' z w • f

def FinRealComm (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) : Prop :=
  ∀ u : WO V W, u.map (infPart D) = 0 →
    (∀ v : WO V W, v.map (finPart D) = 0 → ∀ f : WO V W → ℂ,
      heisO ψ V W u (heisO ψ V W v f) = heisO ψ V W v (heisO ψ V W u f)) ∧
    ∀ (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ) (f : WO V W → ℂ), IsThetaFunO ψ V W f →
      heisO ψ V W u (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z f) =
        Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z (heisO ψ V W u f)

def ThetaSquareIntegrable (D : D7) : Prop :=
  ∀ V W : HSp D, Cocompact V W ∧
    ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) →
      SquareIntegrable ψ V W ∧ HeisUnitary ψ V W ∧
        ∀ θ : InfFam D, IsInfFam θ → DerSkew ψ θ V W ∧ DerComm ψ θ V W ∧ FinRealComm ψ θ V W

end GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars

end
