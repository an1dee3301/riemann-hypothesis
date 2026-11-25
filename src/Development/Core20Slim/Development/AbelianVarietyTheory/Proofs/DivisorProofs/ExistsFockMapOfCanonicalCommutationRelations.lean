module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEval
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutingOperatorsPolynomialEvalPderivStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveOfMapPderivEqAndMapOneNeZeroStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorPolynomialsToProductVariablesInjectiveStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorPolynomialsToProductVariablesCompMulLeftXStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorPolynomialsToProductVariablesCompPderivStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergCreationOperatorsCommuteOfCcrStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergAnnihilationCreationCommutatorEqDeltaStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergFamilyExpandCreationAnnihilationStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHeisenbergOperatorOfCoordsEqSumMulLeftPderivStatement
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Classical
public import Init.Core
public import Init.Data.Function
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.IsApply
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.Logic.Function.Basic
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.PiTensorProduct

@[expose] public section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

noncomputable section

namespace GlobalTheory.CCRFock
open MvPolynomial

theorem polEval_X {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} (m : ι → Module.End ℂ V)
    (hm : ∀ i j, m i * m j = m j * m i) (f₀ : V) (i : ι) (p : MvPolynomial ι ℂ) :
    polEval m hm f₀ (X i * p) = m i (polEval m hm f₀ p) := by
  simp [polEval, Module.End.mul_apply]

theorem polEval_one {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} (m : ι → Module.End ℂ V)
    (hm : ∀ i j, m i * m j = m j * m i) (f₀ : V) : polEval m hm f₀ 1 = f₀ := by
  simp [polEval]

theorem atPl_linear {W Λ : Type} [Fintype W] [DecidableEq W] (w : W) :
    ∃ L : Module.End ℂ (MvPolynomial Λ ℂ) →ₗ[ℂ] Module.End ℂ (⨂[ℂ] _ : W, MvPolynomial Λ ℂ),
      ∀ A, L A = GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial Λ ℂ) w A := ⟨(PiTensorProduct.mapMultilinear ℂ (fun _ : W => MvPolynomial Λ ℂ) (fun _ : W => MvPolynomial Λ ℂ)).toLinearMap
      (fun _ => LinearMap.id) w, fun A => by
    simp [GlobalTheory.RealLift.atPl]⟩

theorem fock_map_of_ccr : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] {W : Type} [Fintype W] [DecidableEq W] {P Q R S : ℕ}
    (H : (W → Matrix (Ix P Q) (Ix R S) ℂ) → Module.End ℂ V),
    (∀ c c', H (c + c') = H c + H c') → (∀ (r : ℝ) c, H ((r : ℂ) • c) = (r : ℂ) • H c) →
    (∀ c c', H c * H c' - H c' * H c =
      ((4 * Real.pi : ℂ) * Complex.I * ((∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im : ℂ)) • 1) →
    ∀ f₀ : V, f₀ ≠ 0 →
    (∀ w a b, H (Pi.single w (Matrix.single a b 1)) f₀ +
      (lineSign a b * Complex.I) • H (Pi.single w (Matrix.single a b Complex.I)) f₀ = 0) →
    ∃ Φ : (⨂[ℂ] _ : W, Pol P Q R S) →ₗ[ℂ] V, Function.Injective Φ ∧
      ∀ c T, Φ (sumPl (fun w => heisOp (c w)) T) = H c (Φ T) := by
  intro V _ _ W _ _ P Q R S H hadd hsmul hccr f₀ hf₀ hvac

  have hm : ∀ i j, fockM H i * fockM H j = fockM H j * fockM H i := GlobalTheory.T.heisenberg_creation_operators_commute_of_ccr H hadd hsmul hccr
  have hcr := GlobalTheory.T.heisenberg_annihilation_creation_commutator_eq_delta H hadd hsmul hccr

  have hd0 : ∀ j, fockD H j f₀ = 0 := by
    rintro ⟨w, a, b⟩
    have h := hvac w a b
    simp only [fockD, unitAt, LinearMap.neg_apply, LinearMap.smul_apply, LinearMap.add_apply]
    rw [h, smul_zero, neg_zero]
  have hpd := GlobalTheory.T.commutingOperatorsPolynomialEval_pderiv (fockM H) (fockD H) hm f₀ hcr hd0
  have hinj0 : Function.Injective (polEval (fockM H) hm f₀) :=
    GlobalTheory.T.injective_of_map_pderiv_eq_and_map_one_ne_zero _ (fockD H) hpd (by rw [polEval_one]; exact hf₀)
  refine ⟨polEval (fockM H) hm f₀ ∘ₗ polMap W (Ix P Q × Ix R S), hinj0.comp (GlobalTheory.T.tensorPolynomialsToProductVariables_injective W _), ?_⟩

  have hX : ∀ (w : W) (l : Ix P Q × Ix R S) T, polEval (fockM H) hm f₀ (polMap W (Ix P Q × Ix R S)
      (GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial (Ix P Q × Ix R S) ℂ) w
        (LinearMap.mulLeft ℂ (MvPolynomial.X l)) T)) =
      fockM H (w, l) (polEval (fockM H) hm f₀ (polMap W (Ix P Q × Ix R S) T)) := by
    intro w l T
    have h := LinearMap.congr_fun (GlobalTheory.T.tensorPolynomialsToProductVariables_comp_mulLeft_X W (Ix P Q × Ix R S) w l) T
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply] at h
    rw [h, polEval_X]
  have hD : ∀ (w : W) (l : Ix P Q × Ix R S) T, polEval (fockM H) hm f₀ (polMap W (Ix P Q × Ix R S)
      (GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial (Ix P Q × Ix R S) ℂ) w
        (MvPolynomial.pderiv l).toLinearMap T)) =
      fockD H (w, l) (polEval (fockM H) hm f₀ (polMap W (Ix P Q × Ix R S) T)) := by
    intro w l T
    have h := LinearMap.congr_fun (GlobalTheory.T.tensorPolynomialsToProductVariables_comp_pderiv W (Ix P Q × Ix R S) w l) T
    simp only [LinearMap.comp_apply, Derivation.coeFn_coe] at h
    rw [h, hpd]

  choose L hL using fun w : W => atPl_linear (Λ := Ix P Q × Ix R S) w
  intro c T
  have hsum : ∀ w, GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial (Ix P Q × Ix R S) ℂ) w (heisOp (c w)) =
      ∑ l : Ix P Q × Ix R S, ((((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * coefM (c w l.1 l.2) (lineSign l.1 l.2)) •
          GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial (Ix P Q × Ix R S) ℂ) w
            (LinearMap.mulLeft ℂ (MvPolynomial.X l)) +
        (((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * coefD (c w l.1 l.2) (lineSign l.1 l.2)) •
          GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial (Ix P Q × Ix R S) ℂ) w
            (MvPolynomial.pderiv l).toLinearMap) := by
    intro w
    clear hX hD hpd hinj0 hcr hm hd0 hvac hccr hsmul hadd hf₀
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hL w (heisOp (c w)), GlobalTheory.T.fockHeisenbergOperatorOfCoords_eq_sum_mulLeft_pderiv (c w), map_sum]
    simp only [map_add (f := _), map_smul]
    simp only [hL]
  rw [GlobalTheory.T.heisenberg_family_expand_creation_annihilation H hadd hsmul c]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [GlobalTheory.RealLift.sumPl, hsum, LinearMap.comp_apply, LinearMap.sum_apply,
    LinearMap.add_apply, LinearMap.smul_apply, map_sum, map_add, map_smul, hX, hD]
  conv_rhs => rw [Fintype.sum_prod_type]

end GlobalTheory.CCRFock
