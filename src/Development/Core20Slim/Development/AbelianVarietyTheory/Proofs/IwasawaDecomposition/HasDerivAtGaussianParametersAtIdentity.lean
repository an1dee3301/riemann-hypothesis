module

public import Mathlib
public import Formalism.LocalRingCardinality.DataTheta
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegBaseY
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDerivAtInvDetAndInvAtIdentityStatement
public import Init.Core
public import Init.Data.Sum.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder

namespace GlobalTheory.OscGauss.ParDer

variable {l m n : Type} [Fintype m]

theorem der_mul {M : ℝ → Matrix l m ℂ} {N : ℝ → Matrix m n ℂ} {M' : Matrix l m ℂ} {N' : Matrix m n ℂ} {s : ℝ}
    (hM : ∀ i j, HasDerivAt (fun t => M t i j) (M' i j) s) (hN : ∀ i j, HasDerivAt (fun t => N t i j) (N' i j) s)
    (i : l) (j : n) : HasDerivAt (fun t => (M t * N t) i j) ((M' * N s + M s * N') i j) s := by
  simp only [Matrix.mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
  exact HasDerivAt.fun_sum fun k _ => (hM i k).fun_mul (hN k j)

theorem der_dot {u v : ℝ → m → ℂ} {u' v' : m → ℂ} {s : ℝ}
    (hu : ∀ i, HasDerivAt (fun t => u t i) (u' i) s) (hv : ∀ i, HasDerivAt (fun t => v t i) (v' i) s) :
    HasDerivAt (fun t => u t ⬝ᵥ v t) (u' ⬝ᵥ v s + u s ⬝ᵥ v') s := by
  simp only [dotProduct, ← Finset.sum_add_distrib]
  exact HasDerivAt.fun_sum fun k _ => (hu k).fun_mul (hv k)

theorem der_mulVec {M : ℝ → Matrix l m ℂ} {v : ℝ → m → ℂ} {M' : Matrix l m ℂ} {v' : m → ℂ} {s : ℝ}
    (hM : ∀ i j, HasDerivAt (fun t => M t i j) (M' i j) s) (hv : ∀ i, HasDerivAt (fun t => v t i) (v' i) s)
    (i : l) : HasDerivAt (fun t => (M t *ᵥ v t) i) ((M' *ᵥ v s + M s *ᵥ v') i) s :=
  der_dot (u := fun t => M t i) (u' := M' i) (hM i) hv

theorem der_vecMul {M : ℝ → Matrix m n ℂ} {v : ℝ → m → ℂ} {M' : Matrix m n ℂ} {v' : m → ℂ} {s : ℝ}
    (hv : ∀ i, HasDerivAt (fun t => v t i) (v' i) s) (hM : ∀ i j, HasDerivAt (fun t => M t i j) (M' i j) s)
    (j : n) : HasDerivAt (fun t => (v t ᵥ* M t) j) ((v' ᵥ* M s + v s ᵥ* M') j) s :=
  der_dot (v := fun t i => M t i j) (v' := fun i => M' i j) hv fun i => hM i j

theorem par_deriv : ∀ (P Q : ℕ) (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) (Z : Mat P Q) (g g' : ℝ → Mat P Q), g 0 = 1 → g' 0 = 1 → (∀ a b, HasDerivAt (fun t => g t a b) (Z a b) 0) → (∀ a b, HasDerivAt (fun t => g' t a b) (-Z a b) 0) → (∀ i j, HasDerivAt (fun t => matA (g t * baseY A) i j) (dA Z A i j) 0) ∧ (∀ l, HasDerivAt (fun t => linX (g t * baseY A) (g t *ᵥ baseV x) (baseF x ᵥ* g' t) l) (dX Z A x l) 0) ∧ HasDerivAt (fun t => scal (g t * baseY A) (g t *ᵥ baseV x) (baseF x ᵥ* g' t)) (dS Z A x) 0 := by
  intro P Q A x Z g g' h0 h0' hg hg'
  have hY : ∀ i j, HasDerivAt (fun t => (g t * baseY A) i j) ((Z * baseY A) i j) 0 := fun i j => by
    simpa using der_mul (N := fun _ => baseY A) (N' := 0) hg (fun _ _ => hasDerivAt_const _ _) i j
  have hZ : Z * baseY A = Matrix.fromRows (Z.toBlocks₁₁ * A + Z.toBlocks₁₂) (Z.toBlocks₂₁ * A + Z.toBlocks₂₂) := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks Z, baseY, Matrix.fromBlocks_mul_fromRows]
    simp
  have hY1 : ∀ i j, HasDerivAt (fun t => (g t * baseY A).toRows₁ i j) ((Z.toBlocks₁₁ * A + Z.toBlocks₁₂) i j) 0 :=
    fun i j => by have := hY (.inl i) j; rw [hZ] at this; exact this
  have hY2 : ∀ i j, HasDerivAt (fun t => (g t * baseY A).toRows₂ i j) ((Z.toBlocks₂₁ * A + Z.toBlocks₂₂) i j) 0 :=
    fun i j => by have := hY (.inr i) j; rw [hZ] at this; exact this
  have e2 : (g 0 * baseY A).toRows₂ = 1 := by rw [h0, Matrix.one_mul]; rfl
  have e1 : (g 0 * baseY A).toRows₁ = A := by rw [h0, Matrix.one_mul]; rfl
  obtain ⟨hdet, hinv⟩ := GlobalTheory.T.hasDerivAt_inv_det_and_inv_at_identity Q (fun t => (g t * baseY A).toRows₂) _ e2 hY2
  have hA : ∀ i j, HasDerivAt (fun t => matA (g t * baseY A) i j) (dA Z A i j) 0 := fun i j => by
    have := der_mul (N' := -(Z.toBlocks₂₁ * A + Z.toBlocks₂₂)) hY1 hinv i j
    rw [e1, e2, inv_one, Matrix.mul_one, Matrix.mul_neg, ← sub_eq_add_neg] at this
    exact this
  have eA : matA (g 0 * baseY A) = A := by rw [h0, Matrix.one_mul, matA_baseY]
  have hv : ∀ i, HasDerivAt (fun t => (g t *ᵥ baseV x) i) ((Z *ᵥ baseV x) i) 0 := fun i => by
    simpa using der_mulVec (v := fun _ => baseV x) (v' := 0) hg (fun _ => hasDerivAt_const _ _) i
  have hf : ∀ i, HasDerivAt (fun t => (baseF x ᵥ* g' t) i) ((baseF x ᵥ* (-Z)) i) 0 := fun i => by
    simpa using der_vecMul (v := fun _ => baseF x) (v' := 0) (M' := -Z) (fun _ => hasDerivAt_const _ _) hg' i
  have hv1 : ∀ i, HasDerivAt (fun t => ((g t *ᵥ baseV x) ∘ Sum.inl) i) ((Z.toBlocks₁₁ *ᵥ (x ∘ Sum.inl)) i) 0 :=
    fun i => (hv (.inl i)).congr_deriv (by
      simp [mulVec, dotProduct, baseV, Fintype.sum_sum_type, Matrix.toBlocks₁₁])
  have hv2 : ∀ i, HasDerivAt (fun t => ((g t *ᵥ baseV x) ∘ Sum.inr) i) ((Z.toBlocks₂₁ *ᵥ (x ∘ Sum.inl)) i) 0 :=
    fun i => (hv (.inr i)).congr_deriv (by
      simp [mulVec, dotProduct, baseV, Fintype.sum_sum_type, Matrix.toBlocks₂₁])
  have hf1 : ∀ i, HasDerivAt (fun t => ((baseF x ᵥ* g' t) ∘ Sum.inl) i) ((-((x ∘ Sum.inr) ᵥ* Z.toBlocks₂₁)) i) 0 :=
    fun i => (hf (.inl i)).congr_deriv (by
      simp [vecMul, dotProduct, baseF, Fintype.sum_sum_type, Matrix.toBlocks₂₁])
  have hf2 : ∀ i, HasDerivAt (fun t => ((baseF x ᵥ* g' t) ∘ Sum.inr) i) ((-((x ∘ Sum.inr) ᵥ* Z.toBlocks₂₂)) i) 0 :=
    fun i => (hf (.inr i)).congr_deriv (by
      simp [vecMul, dotProduct, baseF, Fintype.sum_sum_type, Matrix.toBlocks₂₂])
  have ev : (g 0 *ᵥ baseV x) ∘ Sum.inr = 0 := by rw [h0, Matrix.one_mulVec]; rfl
  have ef : (baseF x ᵥ* g' 0) ∘ Sum.inl = 0 := by rw [h0', Matrix.vecMul_one]; rfl
  have hX : ∀ l, HasDerivAt (fun t => linX (g t * baseY A) (g t *ᵥ baseV x) (baseF x ᵥ* g' t) l) (dX Z A x l) 0 := by
    rintro (i | j)
    · refine ((hv1 i).fun_sub (der_mulVec hA hv2 i)).congr_deriv ?_
      rw [ev, eA]
      simp [dX, Matrix.sub_mulVec, Matrix.mulVec_mulVec]
    · refine ((der_vecMul hf1 hA j).fun_add (hf2 j)).congr_deriv ?_
      rw [ef, eA]
      simp [dX, Matrix.vecMul_add, Matrix.neg_vecMul, Matrix.vecMul_vecMul, add_comm]
  refine ⟨hA, hX, ?_⟩
  have hd := der_dot (u := fun t => linX (g t * baseY A) (g t *ᵥ baseV x) (baseF x ᵥ* g' t) ∘ Sum.inr)
    (u' := dX Z A x ∘ Sum.inr) (fun j => hX (.inr j)) hv2
  refine (hdet.fun_mul hd.fun_neg.cexp).congr_deriv ?_
  simp only [ev, e2]
  rw [h0, h0', Matrix.one_mul, Matrix.one_mulVec, Matrix.vecMul_one, linX_base]
  simp [dS, sub_eq_add_neg]

end GlobalTheory.OscGauss.ParDer
