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
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.KStableOfIsGKSub
public import Init.Classical
public import Init.Core
public import Init.Data.Function
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.Order.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

namespace GlobalTheory

theorem exists_proj_sesq_posDef_finiteDim : ∀ {M : Type} [AddCommGroup M] [Module ℂ M] (b : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) (F : Submodule ℂ M), FiniteDimensional ℂ F →
    (∀ x ∈ F, x ≠ 0 → 0 < (b x x).re) → (∀ x ∈ F, ∀ y ∈ F, star (b x y) = b y x) →
    ∃ e : M →ₗ[ℂ] M, (∀ x, e x ∈ F) ∧ ∀ x, ∀ f ∈ F, b (e x) f = b x f := by
  intro M _ _ b F hF hpos hherm
  classical
  set n := Module.finrank ℂ F
  let v : Module.Basis (Fin n) ℂ F := Module.finBasis ℂ F
  let A : F →ₗ[ℂ] (Fin n → ℂ) := LinearMap.pi (fun i => (b (v i : M)).comp F.subtype)
  let B : M →ₗ[ℂ] (Fin n → ℂ) :=
    { toFun := fun x i => star (b x (v i : M))
      map_add' := by intro x y; funext i; simp [map_add (f := _)]
      map_smul' := by intro c x; funext i; simp [mul_comm] }
  have key : ∀ (y : F) (x : M), (∀ i, b (v i : M) (y : M) = star (b x (v i : M))) →
      ∀ f ∈ F, b (y : M) f = b x f := by
    intro y x h f hf
    have hc : (b (y : M)).comp F.subtype = (b x).comp F.subtype := by
      refine v.ext (fun i => ?_)
      simp only [LinearMap.comp_apply, Submodule.coe_subtype]
      rw [← hherm _ (v i).2 _ y.2, h i, star_star]
    have := LinearMap.congr_fun hc ⟨f, hf⟩
    simpa using this
  have hinj : Function.Injective A := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have h0 : ∀ i, b (v i : M) (y : M) = star (b (0 : M) (v i : M)) := by
      intro i
      have := congrFun hy i
      simpa [A] using this
    have hyy := key y 0 h0 y y.2
    by_contra hne
    have hne' : (y : M) ≠ 0 := by simpa using hne
    have := hpos y y.2 hne'
    rw [hyy] at this
    simp at this
  have hdim : Module.finrank ℂ F = Module.finrank ℂ (Fin n → ℂ) := by simp [n]
  let Aeq := LinearMap.linearEquivOfInjective A hinj hdim
  refine ⟨F.subtype.comp (Aeq.symm.toLinearMap.comp B), fun x => (Aeq.symm (B x)).2, ?_⟩
  intro x f hf
  show b ((Aeq.symm (B x) : F) : M) f = b x f
  refine key (Aeq.symm (B x)) x ?_ f hf
  intro i
  have h1 : A (Aeq.symm (B x)) = B x := by
    exact Aeq.apply_symm_apply (B x)
  have := congrFun h1 i
  simpa [A, B] using this

end GlobalTheory
