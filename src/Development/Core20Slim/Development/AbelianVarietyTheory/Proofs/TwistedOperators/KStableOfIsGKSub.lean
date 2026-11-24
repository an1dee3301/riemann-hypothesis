module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.HeightProofs.AutomorphicFormUniformLimitDiscreteSeriesSeriesStatement
public import Development.Core20Slim.Formalism.LocalToGlobal.IndefiniteReal.MultLemmas
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSumOfMemMultSpan
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.KTypeProj

section Gen

variable {M ι : Type} [AddCommGroup M] [Module ℂ M]

def typeSpan (ρ : ι → M →ₗ[ℂ] M) (Y₀ G : Submodule ℂ M) : Submodule ℂ M :=
  ⨆ (T : M →ₗ[ℂ] M) (_ : Y₀.map T ≤ G ∧ ∀ i, ∀ w ∈ Y₀, T (ρ i w) = ρ i (T w)), Y₀.map T

theorem typeSpan_le (ρ : ι → M →ₗ[ℂ] M) (Y₀ G : Submodule ℂ M) : typeSpan ρ Y₀ G ≤ G :=
  iSup₂_le fun _ h => h.1

theorem le_typeSpan (ρ : ι → M →ₗ[ℂ] M) {Y₀ G : Submodule ℂ M} (h : Y₀ ≤ G) : Y₀ ≤ typeSpan ρ Y₀ G := by
  have h1 : Y₀.map LinearMap.id ≤ typeSpan ρ Y₀ G :=
    le_iSup₂_of_le (f := fun (T : M →ₗ[ℂ] M) (_ : Y₀.map T ≤ G ∧ ∀ i, ∀ w ∈ Y₀, T (ρ i w) = ρ i (T w)) => Y₀.map T)
      LinearMap.id ⟨by rwa [Submodule.map_id], fun _ _ _ => rfl⟩ le_rfl
  rwa [Submodule.map_id] at h1

theorem map_le_typeSpan (ρ : ι → M →ₗ[ℂ] M) {Y₀ G : Submodule ℂ M} (T : M →ₗ[ℂ] M) (hT : Y₀.map T ≤ G)
    (hc : ∀ i, ∀ w ∈ Y₀, T (ρ i w) = ρ i (T w)) : Y₀.map T ≤ typeSpan ρ Y₀ G :=
  le_iSup₂_of_le (f := fun (T : M →ₗ[ℂ] M) (_ : Y₀.map T ≤ G ∧ ∀ i, ∀ w ∈ Y₀, T (ρ i w) = ρ i (T w)) => Y₀.map T)
    T ⟨hT, hc⟩ le_rfl

end Gen

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D} {S : D.what₂.Tau → SPar}
  (M : Formalism.IndefR.Mult.DSModel V S)

def rTrL (k : GA D V) : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ) where
  toFun := rTr V k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem rTrL_apply (k : GA D V) (f : GA D V → ℂ) : rTrL k f = rTr V k f := rfl

def KIdx : Type := {p : D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ // GlobalTheory.CuspGK.InK M p.1 p.2}

def rhoK (i : KIdx M) : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ) := rTrL (atTau θ V i.1.1 i.1.2)

def KStable (Y : Submodule ℂ (GA D V → ℂ)) : Prop :=
  ∀ τ g, GlobalTheory.CuspGK.InK M τ g → ∀ f ∈ Y, rTr V (atTau θ V τ g) f ∈ Y

theorem kStable_iff (Y : Submodule ℂ (GA D V → ℂ)) : KStable θ M Y ↔ ∀ i, ∀ y ∈ Y, rhoK θ M i y ∈ Y :=
  ⟨fun h i y hy => h i.1.1 i.1.2 i.2 y hy, fun h τ g hg y hy => h ⟨(τ, g), hg⟩ y hy⟩

theorem kStable_inf {Y Y' : Submodule ℂ (GA D V → ℂ)} (h : KStable θ M Y) (h' : KStable θ M Y') :
    KStable θ M (Y ⊓ Y') :=
  fun τ g hg f hf => ⟨h τ g hg f hf.1, h' τ g hg f hf.2⟩

theorem kStable_gkGen (ψ : GA D V → ℂ) : KStable θ M (GlobalTheory.CuspGK.gkGen θ M ψ) :=
  (GlobalTheory.CuspGK.isGKSub_gkGen θ M ψ).k

theorem kStable_of_isGKSub {A : Submodule ℂ (GA D V → ℂ)} (h : GlobalTheory.CuspGK.IsGKSub θ M A) : KStable θ M A := h.k

end GlobalTheory.KTypeProj

end
