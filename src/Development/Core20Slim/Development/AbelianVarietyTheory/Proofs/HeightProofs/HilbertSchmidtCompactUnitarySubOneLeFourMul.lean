module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddHsConjLe
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.HeightProofs.ContDiffMatrixRightInvariantDerivative
public import Formalism.RealPlaceAnalysis.Complexify
public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
public import Formalism.RealPlaceAnalysis.SmoothVectorGrowthBound
public import Init.ByCases
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Logic.Function.Defs
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

namespace GlobalTheory.HsLe

theorem hs_toMK_sub_one_le {n : ℕ} (ε : Fin n → Bool) (k : KG ε) :
    Formalism.REAL.hs (toMK k - 1) ≤ 4 * (n : ℝ) := by
  have hu : toMK k ∈ unitary (Matrix (Fin n) (Fin n) ℂ) := k.2.1
  have hcol : ∀ j : Fin n, ∑ i, ‖toMK k i j‖ ^ 2 = 1 := by
    intro j
    have hm : star (toMK k) * toMK k = 1 := Matrix.mem_unitaryGroup_iff'.1 hu
    have h1 : (star (toMK k) * toMK k) j j = (1 : Matrix (Fin n) (Fin n) ℂ) j j := by rw [hm]
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
    have h2 : ((∑ i, ‖toMK k i j‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [← h1]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.star_apply, ← Complex.conj_mul']
      rfl
    exact_mod_cast h2
  have hsum : ∑ i, ∑ j, ‖toMK k i j‖ ^ 2 = (n : ℝ) := by
    rw [Finset.sum_comm]
    simp [hcol]
  have hone : ∑ i : Fin n, ∑ j : Fin n, ‖(1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2 = (n : ℝ) := by
    have : ∀ i j : Fin n, ‖(1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2 = if i = j then 1 else 0 := by
      intro i j
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
    simp only [this, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
  have key : ∀ a b : ℂ, ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
    intro a b
    have h := norm_sub_le a b
    nlinarith [norm_nonneg (a - b), norm_nonneg a, norm_nonneg b, sq_nonneg (‖a‖ - ‖b‖)]
  unfold Formalism.REAL.hs
  calc ∑ i, ∑ j, ‖(toMK k - 1) i j‖ ^ 2
      ≤ ∑ i, ∑ j, (2 * ‖toMK k i j‖ ^ 2 + 2 * ‖(1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        rw [Matrix.sub_apply]
        exact key _ _
    _ = 2 * ∑ i, ∑ j, ‖toMK k i j‖ ^ 2 + 2 * ∑ i : Fin n, ∑ j : Fin n, ‖(1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2 := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ = 4 * (n : ℝ) := by rw [hsum, hone]; ring

end GlobalTheory.HsLe
