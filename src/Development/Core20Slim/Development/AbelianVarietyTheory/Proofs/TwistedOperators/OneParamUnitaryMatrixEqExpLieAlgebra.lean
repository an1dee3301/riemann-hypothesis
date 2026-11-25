module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.WordDerivatives
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffOfContinuousOneParameter
public import Formalism.FormalDegreeBessel.StatementG
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Commute.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Lie.Subalgebra
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
public import Mathlib.Algebra.Ring.Commute
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Order.Notation
public import Mathlib.Order.TypeTags
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.Real

@[expose] public section

open Matrix

namespace GlobalTheory.OneParamUnitary

open scoped ContDiff

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem oneParam_eq_exp_lieU {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (u : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (hc : Continuous u) (h0 : u 0 = 1) (hadd : ∀ s t, u (s + t) = u s * u t)
    (hU : ∀ t, u t ∈ Formalism.QuantumDeterminants.UH G) :
    ∃ Y ∈ GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU G, ∀ t : ℝ, u t = NormedSpace.exp (t • Y) := by
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  have hsm : ContDiff ℝ ∞ u :=
    GlobalTheory.contDiff_of_continuous_oneParameter (Matrix (Fin n) (Fin n) ℂ) u hc h0 hadd
  have hdiff : Differentiable ℝ u := hsm.differentiable (by simp)
  set Y := deriv u 0 with hY
  have hY0 : HasDerivAt u Y 0 := (hdiff 0).hasDerivAt
  have hder : ∀ t, HasDerivAt u (u t * Y) t := by
    intro t
    have h1 : HasDerivAt (fun s => u (s - t)) Y t :=
      (show HasDerivAt u Y (t - t) by simpa using hY0).comp_sub_const t t
    have h2 := h1.const_mul (u t)
    have h3 : (fun s => u t * u (s - t)) = u := by
      funext s
      rw [← hadd]; congr 1; ring
    rwa [h3] at h2

  have hexp : ∀ t : ℝ, u t = NormedSpace.exp (t • Y) := by
    set v : ℝ → Matrix (Fin n) (Fin n) ℂ := fun t => u t * NormedSpace.exp (t • (-Y)) with hv
    have hvd : ∀ t, HasDerivAt v 0 t := by
      intro t
      have hE := hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-Y) t
      have := (hder t).mul hE
      rw [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, add_neg_cancel] at this
      exact this
    have hvc : ∀ t, v t = v 0 := fun t =>
      is_const_of_deriv_eq_zero (fun s => (hvd s).differentiableAt) (fun s => (hvd s).deriv) t 0
    have hv0 : v 0 = 1 := by simp [hv, h0]
    intro t
    have hcomm : Commute (t • (-Y)) (t • Y) :=
      ((Commute.refl Y).neg_left.smul_left t).smul_right t
    have hinv : NormedSpace.exp (t • (-Y)) * NormedSpace.exp (t • Y) = 1 := by
      rw [← Matrix.exp_add_of_commute _ _ hcomm, smul_neg, neg_add_cancel, NormedSpace.exp_zero]
    calc u t = u t * (NormedSpace.exp (t • (-Y)) * NormedSpace.exp (t • Y)) := by rw [hinv, Matrix.mul_one]
      _ = v t * NormedSpace.exp (t • Y) := by rw [hv, Matrix.mul_assoc]
      _ = NormedSpace.exp (t • Y) := by rw [hvc t, hv0, Matrix.one_mul]
  refine ⟨Y, ?_, hexp⟩

  show Yᴴ * G + G * Y = 0
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun A => star A
      map_add' := fun A B => star_add A B
      map_smul' := fun c A => by simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_smul] }
  have hst : HasDerivAt (fun t => star (u t)) (star Y) 0 :=
    (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt 0 hY0
  have hw := (hst.mul_const G).mul hY0
  have hconst : ((fun t => star (u t) * G) * u) = fun _ => G := by
    funext t; exact hU t
  rw [hconst] at hw
  have := (hasDerivAt_const (0 : ℝ) G).unique hw
  rw [h0, star_one, Matrix.one_mul, Matrix.mul_one, ← Matrix.star_eq_conjTranspose] at *
  exact this.symm

end GlobalTheory.OneParamUnitary
