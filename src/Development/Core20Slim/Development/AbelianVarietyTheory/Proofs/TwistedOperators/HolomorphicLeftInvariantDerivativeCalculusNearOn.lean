module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunJetApply
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Analytic.ChangeOrigin
public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Notation
public import Mathlib.Order.TypeTags
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.UniformMulAction
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

noncomputable section

namespace GlobalTheory.SphJetCalc

section General

variable {A B : Type} [NormedAddCommGroup A] [NormedSpace ℂ A] [NormedAddCommGroup B] [NormedSpace ℂ B]
  [CompleteSpace B]

theorem analyticAt_linField {f : A → B} {z : A} (hf : AnalyticAt ℂ f z) (L : A →L[ℂ] A) :
    AnalyticAt ℂ (fun w => fderiv ℂ f w (L w)) z := by

  have hd : AnalyticAt ℂ (fderiv ℂ f) z := hf.fderiv
  have hp : AnalyticAt ℂ (fun w => (fderiv ℂ f w, L w)) z := hd.prod (L.analyticAt z)
  have hev : AnalyticAt ℂ (fun q : (A →L[ℂ] B) × A => q.1 q.2) (fderiv ℂ f z, L z) :=
    (ContinuousLinearMap.id ℂ (A →L[ℂ] B)).analyticAt_bilinear _
  exact AnalyticAt.comp (g := fun q : (A →L[ℂ] B) × A => q.1 q.2)
    (f := fun w => (fderiv ℂ f w, L w)) hev hp

theorem fderiv_linField {f : A → B} {z : A} (hf : AnalyticAt ℂ f z) (L : A →L[ℂ] A) (M : A) :
    fderiv ℂ (fun w => fderiv ℂ f w (L w)) z M
      = fderiv ℂ (fderiv ℂ f) z M (L z) + fderiv ℂ f z (L M) := by

  have hD : HasFDerivAt (fderiv ℂ f) (fderiv ℂ (fderiv ℂ f) z) z :=
    hf.fderiv.differentiableAt.hasFDerivAt
  have hP := hD.clm_apply L.hasFDerivAt
  rw [hP.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  exact add_comm _ _

theorem snd_symm {f : A → B} {z : A} (hf : AnalyticAt ℂ f z) (M N : A) :
    fderiv ℂ (fderiv ℂ f) z M N = fderiv ℂ (fderiv ℂ f) z N M := by

  have hS : IsSymmSndFDerivAt ℂ f z := hf.contDiffAt.isSymmSndFDerivAt_of_omega
  exact hS M N

theorem comm_linField {f : A → B} {z : A} (hf : AnalyticAt ℂ f z) (L K : A →L[ℂ] A) :
    fderiv ℂ (fun w => fderiv ℂ f w (L w)) z (K z) - fderiv ℂ (fun w => fderiv ℂ f w (K w)) z (L z)
      = fderiv ℂ f z (L (K z) - K (L z)) := by

  rw [fderiv_linField hf L, fderiv_linField hf K, snd_symm hf (K z) (L z), map_sub]
  abel

end General

theorem leftInvariant_calculus (n : ℕ) (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
    (f : Matrix (Fin n) (Fin n) ℂ → B) (hf : AnalyticAt ℂ f 1) :
    (∀ Z, AnalyticAt ℂ (Rz Z f) 1) ∧
    (∀ A Z, (fun z => Rz A (Rz Z f) z - Rz Z (Rz A f) z) =ᶠ[𝓝 1] Rz (A * Z - Z * A) f) ∧
    ∀ Y Z : Matrix (Fin n) (Fin n) ℂ, (fun z => fderiv ℂ (Rz Z f) z (Y * z)) =ᶠ[𝓝 1]
      Rz Z (fun z => fderiv ℂ f z (Y * z)) := by

  let RM : Matrix (Fin n) (Fin n) ℂ → (Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ) :=
    fun Z => LinearMap.toContinuousLinearMap (LinearMap.mulRight ℂ Z)
  let LM : Matrix (Fin n) (Fin n) ℂ → (Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ) :=
    fun Y => LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℂ Y)
  have hRz : ∀ (Z : Matrix (Fin n) (Fin n) ℂ) (g : Matrix (Fin n) (Fin n) ℂ → B),
      Rz Z g = fun w => fderiv ℂ g w (RM Z w) := fun Z g => rfl
  have hev : ∀ᶠ z in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), AnalyticAt ℂ f z :=
    hf.eventually_analyticAt
  refine ⟨fun Z => ?_, fun A Z => ?_, fun Y Z => ?_⟩
  · rw [hRz]
    exact analyticAt_linField hf (RM Z)
  · filter_upwards [hev] with z hz
    have hc := comm_linField hz (RM Z) (RM A)
    have hb : (RM Z) ((RM A) z) - (RM A) ((RM Z) z) = z * (A * Z - Z * A) := by
      show z * A * Z - z * Z * A = z * (A * Z - Z * A)
      rw [mul_sub, mul_assoc, mul_assoc]
    rw [hb] at hc
    exact hc
  · filter_upwards [hev] with z hz
    have hc := comm_linField hz (RM Z) (LM Y)
    have hb : (RM Z) ((LM Y) z) - (LM Y) ((RM Z) z) = 0 := by
      show Y * z * Z - Y * (z * Z) = 0
      rw [mul_assoc, sub_self]
    rw [hb, map_zero, sub_eq_zero] at hc
    exact hc

end GlobalTheory.SphJetCalc
