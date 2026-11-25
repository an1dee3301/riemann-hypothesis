module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameValuesPolynomialDetStableHomogeneous
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
public import Formalism.LocalToGlobal.Columns.PolyFnLemmas
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockSubstitutionIdentities
public import Formalism.GradedWeylDivisibility.StatementD
public import Formalism.LocalRingCardinality.DataCoeff
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Init.Core
public import Init.Data.Sum.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Function
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.Sum.Basic
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open GlobalTheory.KJInf Formalism.L2.Forms Formalism.BasicNotions MvPolynomial

noncomputable section
namespace GlobalTheory.KJInf.ClsVal
variable {ι : Type} [Fintype ι] {a b : ℕ}

theorem evalAt_jetLin (y' : ι → Matrix (Fin b) (Fin b) ℂ) (Λ : FP ι a b →ₗ[ℂ] ℂ)
    (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ Formalism.L2.Ker.DVar ι a b) ℂ) :
    evalAt y' (Formalism.L2.Ker.jetLin (fun m => Λ (monomial m 1)) Q) =
      Λ (aeval (Sum.elim (fun x : ι × Fin b × Fin b => (C (y' x.1 x.2.1 x.2.2) : FP ι a b)) X) Q) := by
  induction Q using MvPolynomial.induction_on' with
  | monomial m c =>
    have hm : (monomial m c : MvPolynomial ((ι × Fin b × Fin b) ⊕ Formalism.L2.Ker.DVar ι a b) ℂ) = c • monomial m 1 := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    have h1 : Formalism.L2.Ker.jetLin (fun m => Λ (monomial m 1)) (monomial m c) =
        c • monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn)
          (Λ (monomial (m.comapDomain Sum.inr Sum.inr_injective.injOn) 1)) := by
      rw [hm, map_smul]
      congr 1
      unfold Formalism.L2.Ker.jetLin
      have := (basisMonomials ((ι × Fin b × Fin b) ⊕ Formalism.L2.Ker.DVar ι a b) ℂ).constr_basis ℂ
        (fun m : ((ι × Fin b × Fin b) ⊕ Formalism.L2.Ker.DVar ι a b) →₀ ℕ => (monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn)
          (Λ (monomial (m.comapDomain Sum.inr Sum.inr_injective.injOn) 1)) : MvPolynomial (ι × Fin b × Fin b) ℂ)) m
      simpa using this
    rw [h1, evalAt, smul_eval, eval_monomial, aeval_monomial, Finsupp.prod_fintype _ _ (by simp),
      Finsupp.prod_fintype _ _ (by simp), Fintype.prod_sum_type]
    have h2 : (∏ i : ι × Fin b × Fin a, (X i : FP ι a b) ^ m (Sum.inr i)) =
        monomial (m.comapDomain Sum.inr Sum.inr_injective.injOn) 1 := by
      rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp)]
      rfl
    simp only [Sum.elim_inl, Sum.elim_inr, h2, ← map_pow, ← map_prod, algebraMap_eq]
    rw [show ∀ (u v : ℂ) (q : FP ι a b), C u * (C v * q) = (u * v) • q from fun u v q => by rw [smul_eq_C_mul, C_mul, mul_assoc], map_smul, smul_eq_mul]
    simp only [Finsupp.comapDomain_apply]
    ring
  | add p q hp hq => rw [map_add (f := _), evalAt, map_add (f := _), ← evalAt, ← evalAt, hp, hq, map_add (f := _), map_add (f := _)]

theorem evalAt_jetMap (hab : a ≤ b) (y' : ι → Matrix (Fin b) (Fin b) ℂ) (Λ : FP ι a b →ₗ[ℂ] ℂ) (k : ι → ℕ) (P : PY ι a) :
    evalAt y' (Formalism.L2.Ker.jetMap (fun m => Λ (monomial m 1)) k P) =
      Λ (subY hab y' (P * ∏ τ, Formalism.L2.Ker.frDet ℂ a τ ^ k τ)) := by
  rw [subY_eq_subD]
  exact evalAt_jetLin y' Λ _

theorem cSpan_eq_VV' {m : ℕ} (lam : ι → DomWeight m) : CSpan lam = Formalism.L2.DIV.VV ℂ lam := by
  unfold CSpan Formalism.L2.DIV.VV Formalism.GradedWeylDivisibility.tensorLat
  congr 1
  ext p
  simp only [Set.mem_ofPred_eq, Formalism.L2.Col.nablaSq_eq_delSq]
  rfl

end GlobalTheory.KJInf.ClsVal
