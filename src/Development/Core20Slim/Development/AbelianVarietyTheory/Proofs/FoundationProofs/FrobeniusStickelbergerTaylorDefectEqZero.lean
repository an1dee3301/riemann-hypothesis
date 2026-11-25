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
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.List.Basic
public import Init.Data.List.FinRange
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Antidiag.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.NatAntidiagonal
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries

noncomputable section

namespace GlobalTheory.FrobStick

def entireRing : Subring (ℂ → ℂ) where
  carrier := {F | Differentiable ℂ F}
  mul_mem' := fun {F G} hF hG => by
    exact (hF.mul hG : Differentiable ℂ (fun z => F z * G z))
  one_mem' := by simpa using (differentiable_const (1 : ℂ) : Differentiable ℂ fun _ : ℂ => (1 : ℂ))
  add_mem' := fun {F G} hF hG => by
    exact (hF.add hG : Differentiable ℂ (fun z => F z + G z))
  zero_mem' := by simpa using (differentiable_const (0 : ℂ) : Differentiable ℂ fun _ : ℂ => (0 : ℂ))
  neg_mem' := fun {F} hF => by
    exact (hF.neg : Differentiable ℂ (fun z => -F z))

theorem tay_coeff (F : ℂ → ℂ) (n : ℕ) : PowerSeries.coeff n (tay F) = coef1 F n := by
  simp [tay, PowerSeries.coeff_mk]

def tayHom : entireRing →+* PowerSeries ℂ where
  toFun F := tay F
  map_one' := by
    ext n
    rw [tay_coeff, PowerSeries.coeff_one]
    exact GlobalTheory.SerTransport.taylorCoeff_const_function 1 n
  map_mul' F G := by
    ext n
    rw [tay_coeff, PowerSeries.coeff_mul]
    have := GlobalTheory.SerTransport.taylorCoeff_mul_entire F.2 G.2 n
    simp only [tay_coeff]
    exact this
  map_zero' := by
    ext n
    rw [tay_coeff, map_zero]
    have := GlobalTheory.SerTransport.taylorCoeff_const_function 0 n
    simp only [ite_self] at this
    exact this
  map_add' F G := by
    ext n
    rw [map_add (f := _), tay_coeff, tay_coeff, tay_coeff]
    exact GlobalTheory.SerTransport.taylorCoeff_add_entire F.2 G.2 n

def scaleE (β : ℂ) (F : entireRing) : entireRing :=
  ⟨fun z => F.1 (β * z), F.2.comp (differentiable_id.const_mul β)⟩

theorem rescale_tayHom (β : ℂ) (F : entireRing) :
    PowerSeries.rescale β (tayHom F) = tayHom (scaleE β F) := by
  ext n
  rw [PowerSeries.coeff_rescale]
  show β ^ n * PowerSeries.coeff n (tay F.1) = PowerSeries.coeff n (tay (fun z => F.1 (β * z)))
  rw [tay_coeff, tay_coeff, GlobalTheory.SerTransport.taylorCoeff_scale_entire F.2]

end GlobalTheory.FrobStick

namespace GlobalTheory.FrobStick

theorem tay_defect_eq_zero : (∀ (K : Type) [Field K] [Infinite K] (Φ : MvPowerSeries (Fin 3) K), (∀ t : Fin 3 → K, (MvPowerSeries.subst (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries K)) Φ : PowerSeries K) = 0) → Φ = 0) → (∀ (R : Type) [CommRing R] (f : Fin 3 → PowerSeries R) (s : PowerSeries R) (t : Fin 3 → R), (MvPowerSeries.subst (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries R)) (GlobalTheory.FrobStick.defect f s) : PowerSeries R) = Matrix.det (Matrix.of fun i j => PowerSeries.rescale (t i) (f j)) - 2 * PowerSeries.rescale (t 0 + t 1 + t 2) s * PowerSeries.rescale (t 0 - t 1) s * PowerSeries.rescale (t 1 - t 2) s * PowerSeries.rescale (t 2 - t 0) s) → (∀ (Λ : AddSubgroup ℂ), IsLat Λ → ∀ v : ℂ, v ∉ Λ → ∀ z : Fin 3 → ℂ, Matrix.det (Matrix.of fun i j => ![GlobalTheory.FrobStick.colA Λ, GlobalTheory.FrobStick.colB Λ v, GlobalTheory.FrobStick.colC Λ v] j (z i)) = 2 * sgStar Λ (z 0 + z 1 + z 2) * sgStar Λ (z 0 - z 1) * sgStar Λ (z 1 - z 2) * sgStar Λ (z 2 - z 0)) → ∀ (Λ : AddSubgroup ℂ), IsLat Λ → ∀ v : ℂ, v ∉ Λ → GlobalTheory.FrobStick.defect (fun j => GlobalTheory.FrobStick.tay (![GlobalTheory.FrobStick.colA Λ, GlobalTheory.FrobStick.colB Λ v, GlobalTheory.FrobStick.colC Λ v] j)) (GlobalTheory.FrobStick.tay (sgStar Λ)) = 0 := by
  intro hLine hRestr hId Λ hL v hv
  have hS : Differentiable ℂ (sgStar Λ) := hL.differentiable
  have hQ : Differentiable ℂ (sqTh Λ v) := hL.differentiable_sqTh v
  have hdS : Differentiable ℂ (deriv (sgStar Λ)) := fun z => ((hS.analyticAt z).deriv).differentiableAt
  have hdQ : Differentiable ℂ (deriv (sqTh Λ v)) := fun z => ((hQ.analyticAt z).deriv).differentiableAt
  have hA : Differentiable ℂ (colA Λ) :=
    (hS.pow 3 : Differentiable ℂ (fun z => sgStar Λ z ^ 3))
  have hB : Differentiable ℂ (colB Λ v) :=
    (hS.mul (hQ.add ((hS.pow 2).const_mul (wpF Λ v))) :
      Differentiable ℂ (fun z => sgStar Λ z * (sqTh Λ v z + wpF Λ v * sgStar Λ z ^ 2)))
  have hC : Differentiable ℂ (colC Λ v) :=
    ((hS.mul hdQ).sub ((hdS.const_mul 2).mul hQ) :
      Differentiable ℂ (fun z => sgStar Λ z * deriv (sqTh Λ v) z - 2 * deriv (sgStar Λ) z * sqTh Λ v z))
  let a : Fin 3 → entireRing := ![⟨colA Λ, hA⟩, ⟨colB Λ v, hB⟩, ⟨colC Λ v, hC⟩]
  let s : entireRing := ⟨sgStar Λ, hS⟩
  have ha : ∀ j, tay (![colA Λ, colB Λ v, colC Λ v] j) = tayHom (a j) := by
    intro j; fin_cases j <;> rfl
  apply hLine ℂ
  intro t
  rw [hRestr]
  have e1 : (Matrix.of fun i j => PowerSeries.rescale (t i) (tay (![colA Λ, colB Λ v, colC Λ v] j))) =
      tayHom.mapMatrix (Matrix.of fun i j => scaleE (t i) (a j)) := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, ha, rescale_tayHom]
  have es : tay (sgStar Λ) = tayHom s := rfl
  rw [e1, ← RingHom.map_det, es, rescale_tayHom, rescale_tayHom, rescale_tayHom, rescale_tayHom,
    show (2 : PowerSeries ℂ) = tayHom 2 from (map_ofNat tayHom 2).symm,
    ← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_sub]
  convert map_zero tayHom
  refine Subtype.ext (funext fun z => ?_)
  let φ : entireRing →+* ℂ := (Pi.evalRingHom (fun _ : ℂ => ℂ) z).comp entireRing.subtype
  rw [ZeroMemClass.coe_zero, Pi.zero_apply]
  have hφ : ∀ x : entireRing, (x : ℂ → ℂ) z = φ x := fun x => rfl
  rw [hφ]
  rw [map_sub, RingHom.map_det, map_mul, map_mul, map_mul, map_mul, map_ofNat]
  have hm : φ.mapMatrix (Matrix.of fun i j => scaleE (t i) (a j)) =
      Matrix.of fun i j => ![colA Λ, colB Λ v, colC Λ v] j ((fun i => t i * z) i) := by
    ext i j; fin_cases j <;> rfl
  rw [hm, hId Λ hL v hv (fun i => t i * z)]
  change _ - 2 * sgStar Λ ((t 0 + t 1 + t 2) * z) * sgStar Λ ((t 0 - t 1) * z) * sgStar Λ ((t 1 - t 2) * z) *
    sgStar Λ ((t 2 - t 0) * z) = 0
  simp only [add_mul, sub_mul, sub_self]

end GlobalTheory.FrobStick
