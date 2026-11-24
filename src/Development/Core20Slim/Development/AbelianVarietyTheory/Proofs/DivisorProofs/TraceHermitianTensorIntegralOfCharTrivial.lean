module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqAdeleSupportedAtFinitePlaceOfSupportedAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuum
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLagrAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordsAndSymplecticIntegralOnPlaceLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.RingTheory.Valuation.ValuationSubring

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny

namespace GlobalTheory.KFinLoc

theorem symp_incM_mat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n d : ℕ} (JA : Matrix (Fin n) (Fin n) E) (JB : Matrix (Fin d) (Fin d) E)
    (θ : E) (x y : Matrix (Fin n) (Fin d) E) :
    GlobalTheory.WeilM.symp (R := AF F) (cA σ) (inclR (F := F) (AF F) θ) (incM F JA) (incM F JB)
      (incM F x) (incM F y) =
      algebraMap F (AF F) (Algebra.trace F E (θ * GlobalTheory.WeilM.hTens σ JA JB x y)) := by
  have ht : ∀ e : E, Algebra.trace (AF F) (AF F ⊗[F] E) (inclR (F := F) (AF F) e) =
      algebraMap F (AF F) (Algebra.trace F E e) := fun e => by
    show Algebra.trace (AF F) (AF F ⊗[F] E) ((1 : AF F) ⊗ₜ[F] e) = _
    rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]
  have hc : ∀ e : E, cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := fun e => rfl
  rw [← ht, GlobalTheory.WeilM.symp]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [GlobalTheory.WeilM.hTens, incM, Matrix.map_apply, hc, map_mul, map_sum]

theorem trace_hTens_integral_of_char : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (ψ : AddChar (AF F) ℂ) {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (v : Pl (F := F)), PsiUnr ψ v →
    ∀ X₀ : Matrix (Fin n) (Fin d) E, (∀ γ ∈ latAtV X Y v,
      ψ (symp (cA σ) (-1) (incM F X.J) (incM F Y.J) (GlobalTheory.EmbChart.atPlace v 1 • incM F X₀) γ) = 1) →
    ∀ x ∈ X.L, ∀ y ∈ Y.L, algebraMap F (Fv F v) (Algebra.trace F E (-GlobalTheory.WeilM.hTens σ X.J Y.J X₀ (Matrix.vecMulVec x y)))
      ∈ v.adicCompletionIntegers F := by
  intro F E _ _ _ _ _ σ ψ n d X Y v hψ X₀ h x hx y hy
  refine (hψ _).1 fun t ht => ?_
  have hat : At (evFin F v) (GlobalTheory.EmbChart.atPlace v t) := fun u hu => by
    rw [smul_eq_mul, mul_comm, GlobalTheory.EmbChart.atPlace_mul_right, hu, mul_zero, map_zero]
  have hmem : GlobalTheory.EmbChart.atPlace v t • incM F (Matrix.vecMulVec x y) ∈ latAtV X Y v :=
    AddSubgroup.subset_closure ⟨GlobalTheory.EmbChart.atPlace v t, hat, by rw [GlobalTheory.EmbChart.evFin_atPlace]; exact ht,
      x, hx, y, hy, rfl⟩
  have h1 := h _ hmem
  have hm : (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = inclR (F := F) (AF F) (-1 : E) := by rw [map_neg, map_one]
  rw [GlobalTheory.LatVac.symp_smul_smul, hm, symp_incM_mat, GlobalTheory.EmbChart.atPlace_mul_right,
    GlobalTheory.EmbChart.atPlace_mul_right, GlobalTheory.EmbChart.evFin_atPlace, one_mul, AlgHom.commutes, neg_one_mul,
    mul_comm] at h1
  exact h1

end GlobalTheory.KFinLoc
