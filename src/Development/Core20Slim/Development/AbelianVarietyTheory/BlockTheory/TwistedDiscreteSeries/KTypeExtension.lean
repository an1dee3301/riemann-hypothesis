module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsGrowthSobNeTopOfIsAutFunSm
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsKStableOnKFiniteVectors
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
public import Formalism.FormalDegreeBessel.StatementDS
public import Formalism.FormalDegreeBessel.StatementG
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedType
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.RealPlaceAnalysis.Complexify
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ExistsUnique
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Nontrivial.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Logic.Function.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix

namespace GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

def kFin (M : DSModel V S) (τ : D.what₂.Tau) : Submodule ℂ (M.H τ) :=
  GlobalTheory.KFiniteVectors.kFiniteVectors (M.ε τ) (M.σ τ)

abbrev KVec (M : DSModel V S) : Type := ∀ τ : D.what₂.Tau, kFin M τ

abbrev KMap (M : DSModel V S) : Type := (∀ τ : D.what₂.Tau, kFin M τ) →ₘₗ[ℂ] (GA D V → ℂ)

def maxCpt (M : DSModel V S) (τ : D.what₂.Tau) : Set (Matrix (Fin V.rank) (Fin V.rank) ℂ) :=
  {g | M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ)}


open Classical in
def IsGKMap (θ : InfFam D) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (μ : Measure (GA D V))
    (𝓕 : Set (GA D V)) (T₀ : KMap M) : Prop :=
  (∀ u, IsAutFun V (T₀ u)) ∧
  (∀ u, T₀ u ∈ GlobalTheory.Mem.AutSpace.SmFun θ V) ∧
  (∀ u, IsCuspFun V (T₀ u)) ∧
  (∀ u, MemLp (T₀ u) 2 (μ.restrict 𝓕)) ∧
  (∀ u, GlobalTheory.Grow.UnifModGrowth V θ (T₀ u)) ∧
  (∀ u, ∀ k ∈ J, ∀ g, T₀ u (g * k) = χ k * T₀ u g) ∧
  (∀ τ, ∀ k ∈ maxCpt M τ, ∀ (u : KVec M) (w : kFin M τ), (w : M.H τ) = M.rep τ k (u τ) →
    T₀ (Function.update u τ w) = rTr V (atTau θ V τ k) (T₀ u)) ∧
  (∀ τ, ∀ X ∈ lieAt V τ, ∀ (u : KVec M) (w : kFin M τ), (w : M.H τ) = dRep (M.rep τ) X (u τ) →
    T₀ (Function.update u τ w) = Rder θ V τ X (T₀ u))

def Extends {M : DSModel V S} (T : MMap M) (T₀ : KMap M) : Prop :=
  ∀ (v : M.Vec) (u : KVec M), (∀ τ, (v τ : M.H τ) = u τ) → T v = T₀ u

def ExtExists (D : D7) : Prop :=
  ∀ (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V))
    (χ : GA D V → ℂ) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ →
    ∀ T₀ : KMap M, IsGKMap θ M J χ μ 𝓕 T₀ → ∃! T : MMap M, IsMultMap θ M J χ T ∧ Extends T T₀

def RestrInj (D : D7) : Prop :=
  ∀ (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V))
    (χ : GA D V → ℂ), ∀ T ∈ Mult θ M J χ, (∀ v : M.Vec, (∀ τ, (v τ : M.H τ) ∈ kFin M τ) → T v = 0) → T = 0

def GKExtension (D : D7) : Prop := ExtExists D ∧ RestrInj D

theorem maxCpt_subset (M : DSModel V S) (τ : D.what₂.Tau) : maxCpt M τ ⊆ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
  intro g hg
  have h1 : (M.fr τ * g * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * g * (M.fr τ)⁻¹) = Formalism.REAL.Jm (M.ε τ) := by
    rw [Matrix.mul_assoc _ (Formalism.REAL.Jm (M.ε τ)), ← hg.2, ← Matrix.mul_assoc]
    have := (Matrix.mem_unitaryGroup_iff').1 hg.1
    rw [Matrix.star_eq_conjTranspose] at this
    rw [this, Matrix.one_mul]
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have e : M.fr τ * g * (M.fr τ)⁻¹ * M.fr τ = M.fr τ * g := Matrix.nonsing_inv_mul_cancel_right _ _ hd
  show gᴴ * gramAt D V τ * g = gramAt D V τ
  rw [← M.fr_gram τ]
  calc gᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * g
      = (M.fr τ * g)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * g) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (M.fr τ)ᴴ * ((M.fr τ * g * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * g * (M.fr τ)⁻¹)) * M.fr τ := by
        conv_lhs => rw [← e]
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [h1]

theorem rep_mem_kFin (M : DSModel V S) (τ : D.what₂.Tau) {k : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hk : k ∈ maxCpt M τ)
    {v : M.H τ} (hv : v ∈ kFin M τ) : M.rep τ k v ∈ kFin M τ := by
  obtain ⟨A, hA, ha, hs⟩ := hv
  exact ⟨A, hA, hs _ hk v ha, hs⟩

theorem kFin_ne_bot (M : DSModel V S) (τ : D.what₂.Tau) : kFin M τ ≠ ⊥ := by
  obtain ⟨A, hA, hs, -, ⟨v, hv, h0, -⟩, -⟩ := (M.ds τ).2.2.2.2.2.1
  exact fun h => h0 ((Submodule.mem_bot ℂ).1 (h ▸ (show v ∈ kFin M τ from ⟨A, hA, hv, hs⟩)))

end GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension

end
