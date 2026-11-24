module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.Core20Slim.Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TheoremOfCubeOfAdditionFormulas
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorSeriesInParameterRescaleOfAlgebraic
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarSquareQuotientInModelParameter
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.ColA
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EllipticOnePole
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaZeroPeriodLatticeEq
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarCubeColumnsModelParameterSeries
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.SemiChar
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.ThetaLine
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.List.Basic
public import Init.Data.List.FinRange
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Notation
public import Mathlib.Order.TypeTags
public import Mathlib.Order.WithBot
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.NhdsWithin
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries

noncomputable section

namespace GlobalTheory.FrobStick

theorem sgStar_cube_det_cplx : ∀ (Λ : AddSubgroup ℂ), IsLat Λ → ∀ v : ℂ, v ∉ Λ → ∀ z : Fin 3 → ℂ, Matrix.det (Matrix.of fun i j => ![GlobalTheory.FrobStick.colA Λ, GlobalTheory.FrobStick.colB Λ v, GlobalTheory.FrobStick.colC Λ v] j (z i)) = 2 * sgStar Λ (z 0 + z 1 + z 2) * sgStar Λ (z 0 - z 1) * sgStar Λ (z 1 - z 2) * sgStar Λ (z 2 - z 0) := by
  intro Λ hΛ v hv z
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ hΛ
  have hΛL : Λ = L.lattice.toAddSubgroup := AddSubgroup.ext hL
  have hσ : sgStar Λ = Formalism.L2.Th1.F.sgStar L := by rw [hΛL]; exact GlobalTheory.JetsGenusOne.sgStar_eq L
  have hwp : wpF Λ = L.weierstrassP := funext (GlobalTheory.OddTheta.wpF_eq L Λ hL)
  have hsd : Differentiable ℂ (sgStar Λ) := hΛ.differentiable
  have hopen : IsOpen ((Λ : Set ℂ)ᶜ) := by
    have : (Λ : Set ℂ) = (L.lattice : Set ℂ) := Set.ext fun w => hL w
    rw [this]; exact L.isClosed_lattice.isOpen_compl
  have hB : ∀ w, w ∉ Λ → colB Λ v w = sgStar Λ w ^ 3 * L.weierstrassP w := by
    intro w hw
    rw [colB, hΛ.sqTh_eq hv hw, ← hwp]
    ring
  have hC : ∀ w, w ∉ Λ → colC Λ v w = sgStar Λ w ^ 3 * L.derivWeierstrassP w := by
    intro w hw
    have hwL : w ∉ L.lattice := fun h => hw ((hL w).2 h)
    have hpd : HasDerivAt L.weierstrassP (L.derivWeierstrassP w) w := by
      have h1 : DifferentiableAt ℂ L.weierstrassP w :=
        L.differentiableOn_weierstrassP.differentiableAt (L.isClosed_lattice.isOpen_compl.mem_nhds hwL)
      have h2 := h1.hasDerivAt
      rwa [L.deriv_weierstrassP] at h2
    have hev : sqTh Λ v =ᶠ[nhds w] fun u => sgStar Λ u ^ 2 * (L.weierstrassP u - wpF Λ v) := by
      filter_upwards [hopen.mem_nhds hw] with u hu
      rw [hΛ.sqTh_eq hv hu, hwp]
    have hd : HasDerivAt (fun u => sgStar Λ u ^ 2 * (L.weierstrassP u - wpF Λ v))
        ((2 : ℕ) * sgStar Λ w ^ (2 - 1) * deriv (sgStar Λ) w * (L.weierstrassP w - wpF Λ v) +
          sgStar Λ w ^ 2 * L.derivWeierstrassP w) w :=
      ((hsd w).hasDerivAt.pow 2).mul (hpd.sub_const _)
    rw [colC, hev.deriv_eq, hd.deriv, hΛ.sqTh_eq hv hw, hwp]
    push_cast
    ring
  have hoff : ∀ y : Fin 3 → ℂ, (∀ i, y i ∉ Λ) →
      Matrix.det (Matrix.of fun i j => ![colA Λ, colB Λ v, colC Λ v] j (y i)) =
        2 * sgStar Λ (y 0 + y 1 + y 2) * sgStar Λ (y 0 - y 1) * sgStar Λ (y 1 - y 2) * sgStar Λ (y 2 - y 0) := by
    intro y hy
    have h := Formalism.L2.Th1.F.sgStarThree L (y 0) (y 1) (y 2)
      (fun h => hy 0 ((hL _).2 h)) (fun h => hy 1 ((hL _).2 h)) (fun h => hy 2 ((hL _).2 h))
    rw [← hσ] at h
    rw [Matrix.det_fin_three] at h ⊢
    simp [Matrix.vecHead, Matrix.vecTail] at h ⊢
    rw [hB _ (hy 0), hB _ (hy 1), hB _ (hy 2), hC _ (hy 0), hC _ (hy 1), hC _ (hy 2)]
    simp only [colA]
    linear_combination h
  have hcA : Continuous (colA Λ) := by
    have := hsd.continuous
    unfold colA; fun_prop
  have hcB : Continuous (colB Λ v) := by
    have := (hΛ.differentiable_sqTh v).continuous
    have := hsd.continuous
    unfold colB; fun_prop
  have hcC : Continuous (colC Λ v) := by
    have h1 : Continuous (deriv (sqTh Λ v)) :=
      ((hΛ.differentiable_sqTh v).contDiff (n := 1)).continuous_deriv le_rfl
    have h2 : Continuous (deriv (sgStar Λ)) := (hsd.contDiff (n := 1)).continuous_deriv le_rfl
    have := (hΛ.differentiable_sqTh v).continuous
    have := hsd.continuous
    unfold colC; fun_prop
  have hcL : Continuous fun y : Fin 3 → ℂ =>
      Matrix.det (Matrix.of fun i j => ![colA Λ, colB Λ v, colC Λ v] j (y i)) := by
    refine Continuous.matrix_det ?_
    refine continuous_matrix fun i j => ?_
    simp only [Matrix.of_apply]
    fin_cases j
    · exact hcA.comp (continuous_apply i)
    · exact hcB.comp (continuous_apply i)
    · exact hcC.comp (continuous_apply i)
  have hcR : Continuous fun y : Fin 3 → ℂ =>
      2 * sgStar Λ (y 0 + y 1 + y 2) * sgStar Λ (y 0 - y 1) * sgStar Λ (y 1 - y 2) * sgStar Λ (y 2 - y 0) := by
    have := hsd.continuous
    fun_prop
  have hdense : Dense {y : Fin 3 → ℂ | ∀ i, y i ∉ Λ} := by
    have := dense_pi (Set.univ : Set (Fin 3)) (s := fun _ => ((Λ : Set ℂ)ᶜ)) fun _ _ => hΛ.dense_compl
    convert this using 1
    ext y; simp
  exact congrFun (Continuous.ext_on hdense hcL hcR fun y hy => hoff y hy) z

end GlobalTheory.FrobStick
