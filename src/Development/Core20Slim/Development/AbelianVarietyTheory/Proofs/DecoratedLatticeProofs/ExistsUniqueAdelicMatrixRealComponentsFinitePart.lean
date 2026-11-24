module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtensionAdeleRealComponentsCmTypeStatement
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
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
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Ring.WithAbs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ExistsUnique
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.StdUnn

theorem exists_unique_of_comp_finPart : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ) (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) (x₀ : Mx D m n), ∃! x : Mx D m n, (∀ τ, compAt θ τ x = z τ) ∧ x.map (finPart D) = x₀.map (finPart D) := by
  intro D θ hθ m n z x₀
  have hL : ∀ τ (w : Matrix (Fin m) (Fin n) ℂ), IsLineAt θ τ w (lineAt θ τ w) := fun τ w =>
    Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ m n τ w)
  let C : D.what₂.Tau → Mx D m n →+ Matrix (Fin m) (Fin n) ℂ := fun τ =>
    (((θ τ).comp (infPart D)).toAddMonoidHom).mapMatrix
  have hC : ∀ τ w, compAt θ τ w = C τ w := fun τ w => rfl
  let P : Mx D m n →+ Matrix (Fin m) (Fin n) _ := ((finPart D).toAddMonoidHom).mapMatrix
  have hP : ∀ w : Mx D m n, w.map (finPart D) = P w := fun w => rfl
  have key : ∀ x y : Mx D m n, (∀ τ, compAt θ τ x = compAt θ τ y) → x.map (finPart D) = y.map (finPart D) → x = y := by
    intro x y h1 h2
    refine Matrix.ext fun i j => ?_
    rw [← sub_eq_zero]
    refine (GlobalTheory.T.extensionAdele_realComponents_cmType D θ hθ).2.2.2 (x i j - y i j) (fun τ => ?_) ?_
    · have := congrFun (congrFun (h1 τ) i) j
      simp only [compAt, Matrix.map_apply] at this
      rw [(infPart D).map_sub, (θ τ).map_sub, this, sub_self]
    · have := congrFun (congrFun h2 i) j
      simp only [Matrix.map_apply] at this
      rw [(finPart D).map_sub, this, sub_self]
  refine ⟨x₀ + ∑ σ, lineAt θ σ (z σ - compAt θ σ x₀) 1, ⟨fun τ => ?_, ?_⟩, ?_⟩
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [hC, map_add (f := _), map_sum, ← hC]
    simp_rw [← hC, (hL _ _).2.2 1 τ]
    rw [Finset.sum_eq_single τ (fun b _ hb => if_neg (Ne.symm hb)) (by simp), if_pos rfl, Complex.ofReal_one, one_smul]
    abel
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [hP, hP, map_add (f := _), map_sum]
    simp_rw [← hP, (hL _ _).2.1 1]
    simp
  · rintro y ⟨hy1, hy2⟩
    apply key
    · intro τ
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hy1, hC, map_add (f := _), map_sum, ← hC]
      simp_rw [← hC, (hL _ _).2.2 1 τ]
      rw [Finset.sum_eq_single τ (fun b _ hb => if_neg (Ne.symm hb)) (by simp), if_pos rfl, Complex.ofReal_one, one_smul]
      abel
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [hy2, hP, hP, map_add (f := _), map_sum]
      simp_rw [← hP, (hL _ _).2.1 1]
      simp

end GlobalTheory.StdUnn
