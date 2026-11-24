module

public import Development.Core20Slim.Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
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
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.GramSchwartzFunctions.BC

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions

variable {D : D7}

def hermA (D : D7) (r : ℕ) : AddSubgroup (Mx D r r) where
  carrier := {b | adj b = b}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, GlobalTheory.MixModel.adj] at *
    rw [Matrix.map_add _ (map_add _), Matrix.transpose_add, ha, hb]
  zero_mem' := by
    simp only [Set.mem_setOf_eq, GlobalTheory.MixModel.adj]
    rw [Matrix.map_zero _ (map_zero _), Matrix.transpose_zero]
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, GlobalTheory.MixModel.adj] at *
    rw [Matrix.map_neg _ (map_neg _), Matrix.transpose_neg, ha]

def ratHerm (D : D7) (r : ℕ) : AddSubgroup (hermA D r) := (ratMx D r r).comap (hermA D r).subtype

def IsCovolOneH {r : ℕ} (lam : Measure (hermA D r)) (𝓕 : Set (hermA D r)) : Prop :=
  lam.IsAddHaarMeasure ∧ IsAddFundamentalDomain (ratHerm D r) 𝓕 lam ∧ lam 𝓕 = 1

def Jt (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) {r : ℕ} (μ : Measure (Mx D V.rank r)) (φ : Mx D V.rank r → ℂ)
    (b : hermA D r) : ℂ :=
  ∫ y, φ y * ψ (halfTr (Matrix.trace (HMul.hMul b.1 (inner V y y) : Mx D r r))) ∂μ

def W (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) {r : ℕ} (μ : Measure (Mx D V.rank r)) (lam : Measure (hermA D r))
    (φ : Mx D V.rank r → ℂ) (β : HermE D r) : ℂ :=
  ∫ b, Jt ψ V μ φ b * ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D r r))) ∂lam

def gramQ (V : HSp D) {r : ℕ} (x : Matrix (Fin V.rank) (Fin r) D.host.E) : Matrix (Fin r) (Fin r) D.host.E :=
  (x.map (D.sp.cm.sig : D.host.E → D.host.E)).transpose * (HSpace.gram V * x)

def IfrB (V : HSp D) (ν : Measure (GA D V)) {r : ℕ} (φ : Mx D V.rank r → ℂ) (β : HermE D r) : ℂ :=
  ⨍ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (fun h => ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = β.1},
    φ (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) (x.1.map (incA D)))) q ∂autMeasure V ν

def Hyp (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (μ : Measure (Mx D V.rank r))
    (lam : Measure (hermA D r)) (ν : Measure (GA D V)) (φ : Mx D V.rank r → ℂ) : Prop :=
  2 * r < V.rank ∧ IsCharAF D.host.F ψ ∧ IsInfFam θ ∧ (∃ 𝓕, IsCovolOne (ratMx D V.rank r) μ 𝓕) ∧
    (∃ 𝓖, IsCovolOneH lam 𝓖) ∧ ν.IsHaarMeasure ∧ φ ∈ schwartzA θ V.rank r ∧
    GlobalTheory.SiegelFormula.absThetaInt V ν φ < ⊤

def PoissonHerm : Prop :=
  ∀ (D : D7) (r : ℕ) (V : HSp D) ψ θ μ lam ν φ, Hyp D r V ψ θ μ lam ν φ →
    Summable (fun b : HermE D r => J ψ V μ φ b) →
    HasSum (fun β : HermE D r => W ψ V μ lam φ β) (∑' b : HermE D r, J ψ V μ φ b)

def SiegelND : Prop :=
  ∀ (D : D7) (r : ℕ) (V : HSp D) ψ θ μ lam ν φ, Hyp D r V ψ θ μ lam ν φ →
    ∀ β : HermE D r, β.1.det ≠ 0 → IfrB V ν φ β = W ψ V μ lam φ β

def SiegelDeg : Prop :=
  ∀ (D : D7) (r : ℕ) (V : HSp D) ψ θ μ lam ν φ, Hyp D r V ψ θ μ lam ν φ →
    ∀ β : HermE D r, β.1.det = 0 → IfrB V ν φ β = W ψ V μ lam φ β

end PositivityTheory.GramSchwartzFunctions.BC
