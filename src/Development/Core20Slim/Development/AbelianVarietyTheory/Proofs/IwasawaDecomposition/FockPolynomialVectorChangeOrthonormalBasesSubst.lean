module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
public import Formalism.LocalRingCardinality.DataExtra
public import Formalism.LocalRingCardinality.DataTies
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolRepOfIsTau
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.APlusComm
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockBasis

section Mat

variable {m n : ℕ}

theorem unitMap_mul (B u : Matrix (Fin n) (Fin n) ℂ) (B' k : Matrix (Fin m) (Fin m) ℂ) (i : Fin m) (j : Fin n) :
    Formalism.IndefR.Datum.unitMap (B * u) (B' * k) i j =
      ∑ a, ∑ b, (k a i * u⁻¹ j b) • Formalism.IndefR.Datum.unitMap B B' a b := by
  have e : k * Matrix.single i j (1 : ℂ) * u⁻¹ = ∑ a, ∑ b, (k a i * u⁻¹ j b) • Matrix.single a b (1 : ℂ) := by
    rw [Matrix.matrix_eq_sum_single (k * Matrix.single i j (1 : ℂ) * u⁻¹)]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
    congr 1
    rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · simp
    · intro c _ hc
      simp [Matrix.mul_single_apply_of_ne _ _ _ _ _ hc]
    · simp
  unfold Formalism.IndefR.Datum.unitMap
  rw [Matrix.mul_inv_rev]
  calc B' * k * Matrix.single i j (1 : ℂ) * (u⁻¹ * B⁻¹) = B' * (k * Matrix.single i j (1 : ℂ) * u⁻¹) * B⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [e]
        simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]



end Mat

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
  (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (τ : D.what₂.Tau) (s : Matrix (Fin T.rank) (Fin T.rank) ℂ)
  {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
include hψ hθ hf






omit hψ hθ hf

section Generic

variable {ι κ μ X : Type} [Fintype κ] [Fintype μ] {A A' : ι → (X → ℂ) → (X → ℂ)} {P : (X → ℂ) → Prop}


end Generic


end GlobalTheory.FockBasis
