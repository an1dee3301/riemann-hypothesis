module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralSiegelConeInvModulusLtTopWeilStatement
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
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Fin
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
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Basic.Unique
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Order.Real
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.ColProd

theorem tsum_pow_fin {α : Type*} (f : α → ℝ≥0∞) (n : ℕ) :
    ∑' g : Fin n → α, ∏ j, f (g j) = (∑' v, f v) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← Equiv.tsum_eq (Fin.consEquiv (fun _ : Fin (n + 1) => α))]
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [ENNReal.tsum_prod (f := fun a (g : Fin n → α) => f a * ∏ i, f (g i))]
    simp_rw [ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_mul_right, ih, pow_succ']

theorem absTheta_le_pow_of_colProd : ∀ (D : D7) (V : HSp D) {n : ℕ} (φ : Mx D V.rank n → ℂ) (ρ : Mx D V.rank 1 → ℝ≥0∞) (C : ℝ≥0∞) (y : GA D V), (∀ x : Mx D V.rank n, ‖φ (HMul.hMul (mt V y⁻¹) x : Matrix (Fin V.rank) (Fin n) (AE D))‖ₑ ≤ C * ∏ j : Fin n, ρ (fun i (_ : Fin 1) => x i j)) → ∀ a : GA D V, absTheta V φ (a * y) ≤ C * (∑' ξ : Matrix (Fin V.rank) (Fin 1) D.host.E, ρ (invPt V a ξ)) ^ n := by
  intro D V n φ ρ C y hφ a
  have hstep : ∀ ξ : Matrix (Fin V.rank) (Fin n) D.host.E,
      ‖φ (invPt V (a * y) ξ)‖ₑ ≤ C * ∏ j : Fin n, ρ (invPt V a (fun i (_ : Fin 1) => ξ i j)) := by
    intro ξ
    have h1 : invPt V (a * y) ξ =
        (HMul.hMul (mt V y⁻¹) (invPt V a ξ) : Matrix (Fin V.rank) (Fin n) (AE D)) := by
      simp only [invPt, mul_inv_rev, Formalism.L2.Theta.mt, map_mul, Units.val_mul, Matrix.mul_assoc]
    rw [h1]
    refine (hφ (invPt V a ξ)).trans (le_of_eq ?_)
    congr 1
  let e : (Fin n → Matrix (Fin V.rank) (Fin 1) D.host.E) ≃ Matrix (Fin V.rank) (Fin n) D.host.E :=
    { toFun := fun g i j => g j i 0
      invFun := fun ξ j i _ => ξ i j
      left_inv := fun g => by
        funext j i u
        show g j i 0 = g j i u
        rw [Fin.fin_one_eq_zero u]
      right_inv := fun ξ => by rfl }
  calc absTheta V φ (a * y)
      = ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, ‖φ (invPt V (a * y) ξ)‖ₑ := by rfl
    _ ≤ ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E,
          C * ∏ j : Fin n, ρ (invPt V a (fun i (_ : Fin 1) => ξ i j)) := ENNReal.tsum_le_tsum hstep
    _ = C * ∑' g : Fin n → Matrix (Fin V.rank) (Fin 1) D.host.E, ∏ j : Fin n, ρ (invPt V a (g j)) := by
        rw [ENNReal.tsum_mul_left, ← Equiv.tsum_eq e]
        congr 1
        refine tsum_congr (fun g => Finset.prod_congr rfl (fun j _ => ?_))
        congr 2
        funext i u
        show g j i 0 = g j i u
        rw [Fin.fin_one_eq_zero u]
    _ = C * (∑' ξ : Matrix (Fin V.rank) (Fin 1) D.host.E, ρ (invPt V a ξ)) ^ n := by
        rw [tsum_pow_fin (fun v => ρ (invPt V a v)) n]

end GlobalTheory.CompanionTheory.ColProd
