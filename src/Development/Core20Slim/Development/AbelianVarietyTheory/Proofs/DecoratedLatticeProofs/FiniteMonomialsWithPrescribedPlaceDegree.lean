module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsBiSmooth
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationCommFockPolynomialVectorsStatement
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.Interval
public import Mathlib.Data.Finsupp.Order
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Operations
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.Preorder.Finsupp

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

namespace GlobalTheory

theorem finite_monomials_of_placeDegree : ∀ (D : D7) (m n : ℕ) (d : D.what₂.Tau → ℕ), {α : FVar D m n →₀ ℕ | ∀ τ, (∑ v ∈ α.support with v.1 = τ, α v) = d τ}.Finite := by
  intro D m n d
  classical
  refine (Set.finite_Iic (Finsupp.equivFunOnFinite.symm (fun v : FVar D m n => d v.1))).subset ?_
  intro α hα
  simp only [Set.mem_setOf_eq] at hα
  rw [Set.mem_Iic, Finsupp.le_def]
  intro v
  rw [Finsupp.coe_equivFunOnFinite_symm]
  by_cases hv : v ∈ α.support
  · rw [← hα v.1]
    exact Finset.single_le_sum (f := fun w => α w) (fun _ _ => Nat.zero_le _)
      (Finset.mem_filter.2 ⟨hv, rfl⟩)
  · rw [Finsupp.notMem_support_iff.1 hv]
    exact Nat.zero_le _

end GlobalTheory
