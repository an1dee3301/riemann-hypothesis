module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.MeanPair
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine
public import Development.AbelianVarietyTheory.Definitions.Foundations.AnalyticOnNhdTsumNpow
public import Development.Core20Slim.Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinPolesStd
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
public import Development.Core20Slim.Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothAutomorphicFormRightTranslateFiniteAdelic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
public import Development.Core20Slim.Formalism.LocalToGlobal.IndefiniteReal.TopMult
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
public import Formalism.FormalDegreeBessel.StatementG
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.List.Basic
public import Init.Data.List.OfFn
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Notation
public import Mathlib.Order.TypeTags
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel  GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSch.CentreRight

open GlobalTheory.Mem.AutSpace GlobalTheory.Mem.RealTranslate GlobalTheory.PointAtPlaceHom
open Formalism.MainNotions.StandardLattice (infMat)

variable {D : D7} {θ : InfFam D} {V : HSp D}

theorem rTr_mem_fin {u : GA D V} (hu : u ∈ GfC V) {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) : rTr V u φ ∈ SmFun θ V := by
  intro n τs Xs hX g
  have := hφ n τs Xs hX (g * u)
  convert this using 2 with t
  unfold rTr
  rw [mul_assoc, mul_assoc, comm_of_mem V (list_prod_mem fun a ha => ?_) hu]
  obtain ⟨b, rfl⟩ := List.mem_ofFn.1 ha
  exact atTau_mem V _ _

theorem rTr_mul (u a : GA D V) (φ : GA D V → ℂ) : rTr V (u * a) φ = rTr V u (rTr V a φ) := by
  funext g
  simp only [rTr, mul_assoc]

theorem decomp (hθ : IsInfFam θ) (x : GA D V) : ∃ u ∈ GfC V, ∃ a, IsRealPt θ a ∧ x = u * a := by
  obtain ⟨u, hu, a, ha, e⟩ := Formalism.IndefR.TopMult.ga_decomp x
  exact ⟨u, hu, a, ⟨ha, GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V a⟩, e⟩

theorem rTr_mem_all (hθ : IsInfFam θ) (x : GA D V) {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) : rTr V x φ ∈ SmFun θ V := by
  obtain ⟨u, hu, a, ha, rfl⟩ := decomp hθ x
  rw [rTr_mul]
  exact rTr_mem_fin hu (rTr_mem hθ ha hφ)

theorem gelf_rTr_all (hθ : IsInfFam θ) (x : GA D V) (τ : D.what₂.Tau) (k : ℕ) {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) :
    gelf θ V τ k (rTr V x φ) = rTr V x (gelf θ V τ k φ) := by
  obtain ⟨u, hu, a, ha, rfl⟩ := decomp hθ x
  rw [rTr_mul, rTr_mul, GlobalTheory.Mem.FinTranslate.gelf_rTr hu, gelf_rTr hθ ha τ k hφ]

end GlobalTheory.RegSch.CentreRight

end
