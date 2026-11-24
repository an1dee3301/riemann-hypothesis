module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagOneNegOneConjAntidiagonalStabilizerMem
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagonalFixingDoublingMatrix
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTwoSmulMemAdelicLatticeAtFinitePlace
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.SplitDblPar

section Gen
variable {A : Type} [CommRing A] {ι : Type} [Fintype ι] [DecidableEq ι]

def shear (ι : Type) [DecidableEq ι] (s : A) : Matrix (ι ⊕ ι) (ι ⊕ ι) A :=
  Matrix.fromBlocks ((1 + s) • 1) ((-s) • 1) (s • 1) ((1 - s) • 1)

theorem shear_mul (s t : A) : shear ι s * shear ι t = shear ι (s + t) := by
  simp only [shear, Matrix.fromBlocks_multiply, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, ← add_smul]
  congr 2 <;> ring

omit [Fintype ι] in
theorem shear_zero : shear ι (0 : A) = 1 := by
  simp [shear, Matrix.fromBlocks_one]

omit [Fintype ι] in
theorem shear_map (f : A →+* A) (s : A) : (shear ι s).map f = shear ι (f s) := by
  ext (i | i) (j | j) <;> by_cases h : i = j <;> simp [shear, Matrix.one_apply, h]

theorem shear_unitary (J : Matrix ι ι A) (s : A) : (shear ι s)ᵀ * dbl J * shear ι (-s) = dbl J := by
  simp only [shear, dbl, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.transpose_smul,
    Matrix.transpose_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, add_zero,
    zero_add, smul_smul, smul_neg, Matrix.neg_mul, smul_zero]
  congr 1 <;> module

theorem shear_mulVec_inl (s : A) (z : ι ⊕ ι → A) :
    (fun i => (shear ι s *ᵥ z) (Sum.inl i)) =
      (fun i => z (Sum.inl i)) + s • (fun i => z (Sum.inl i)) - s • (fun i => z (Sum.inr i)) := by
  funext i
  simp [shear, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply]
  ring

theorem shear_mulVec_inr (s : A) (z : ι ⊕ ι → A) :
    (fun i => (shear ι s *ᵥ z) (Sum.inr i)) =
      (fun i => z (Sum.inr i)) + s • (fun i => z (Sum.inl i)) - s • (fun i => z (Sum.inr i)) := by
  funext i
  simp [shear, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply]
  ring

theorem shear_diagCols (s : A) : shear ι s * (diagCols ι : Matrix (ι ⊕ ι) ι A) = (diagCols ι : Matrix (ι ⊕ ι) ι A) * (1 : Matrix ι ι A) := by
  rw [Matrix.mul_one]
  ext (i | i) j <;> by_cases h : i = j <;>
    simp [shear, diagCols, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, h]

theorem shear_eq (s : A) : shear ι s = 1 + s • ((diagCols ι : Matrix (ι ⊕ ι) ι A) * (Matrix.fromRows (1 : Matrix ι ι A) (-1))ᵀ) := by
  ext (i | i) (j | j) <;> by_cases h : i = j <;>
    simp [shear, diagCols, Matrix.mul_apply, Matrix.one_apply, h, sub_eq_add_neg]
  all_goals (intro h'; exact absurd h'.symm h)

end Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem diagonalFixingDoublingMatrix_eq_shear (c : AE F E) (d : ℕ) : GlobalTheory.SplitDblGen.diagonalFixingDoublingMatrix c d = shear (Fin d) (GlobalTheory.SplitDblGen.half * c) :=
  (shear_eq _).symm

theorem shear_mem_latAtD {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) (s : AE F E)
    (hs : ∀ z ∈ GlobalTheory.InertSph.latAt W v, s • z ∈ GlobalTheory.InertSph.latAt W v) {z : Fin d ⊕ Fin d → AE F E}
    (hz : z ∈ GlobalTheory.InertDbl.latAtD W v) : shear (Fin d) s *ᵥ z ∈ GlobalTheory.InertDbl.latAtD W v := by
  refine ⟨?_, ?_⟩
  · rw [shear_mulVec_inl]; exact sub_mem (add_mem hz.1 (hs _ hz.1)) (hs _ hz.2)
  · rw [shear_mulVec_inr]; exact sub_mem (add_mem hz.2 (hs _ hz.1)) (hs _ hz.2)

theorem diagonalFixingDoublingMatrix_mem_integralSiegelParabolic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ) (W : Spc F E d) (v : Pl (F := F)), (2 : 𝓞 F) ∉ v.asIdeal →
    ∀ c : AE F E, cA σ c = -c → At (evFin F v) c → (∀ z ∈ GlobalTheory.InertSph.latAt W v, c • z ∈ GlobalTheory.InertSph.latAt W v) →
    ∃ p ∈ GlobalTheory.InertDbl.ParD σ W v, GlobalTheory.InertDbl.matD p = GlobalTheory.SplitDblGen.diagonalFixingDoublingMatrix c d := by
  intro F E _ _ _ _ _ σ d W v h2 c hc hat hlat
  set s : AE F E := GlobalTheory.SplitDblGen.half * c with hsdef
  have hσ : cA σ s = -s := by
    rw [hsdef, map_mul, hc, GlobalTheory.SplitDblGen.half, AlgHom.commutes, mul_neg]
  have hs : ∀ z ∈ GlobalTheory.InertSph.latAt W v, s • z ∈ GlobalTheory.InertSph.latAt W v := by
    intro z hz
    rw [hsdef, mul_smul, GlobalTheory.SplitDblGen.half, algebraMap_smul]
    exact GlobalTheory.InertSph.invTwo_smul_mem_latAt F E d W v h2 _ (hlat z hz)
  have hs' : ∀ z ∈ GlobalTheory.InertSph.latAt W v, (-s) • z ∈ GlobalTheory.InertSph.latAt W v := by
    intro z hz
    rw [neg_smul]; exact neg_mem (hs z hz)
  have hu : (shear (Fin d) s)ᵀ * dbl (incM F W.J) * (shear (Fin d) s).map (cA σ) = dbl (incM F W.J) := by
    have h := shear_map (ι := Fin d) (cA σ : AE F E →+* AE F E) s
    have h' : (shear (Fin d) s).map (cA σ) = shear (Fin d) (-s) := by rw [← hσ]; exact h
    rw [h', shear_unitary]
  let p : GlobalTheory.InertDbl.UD σ W :=
    ⟨⟨shear (Fin d) s, shear (Fin d) (-s), by rw [shear_mul, add_neg_cancel, shear_zero],
      by rw [shear_mul, neg_add_cancel, shear_zero]⟩, hu⟩
  have hp : GlobalTheory.InertDbl.matD p = shear (Fin d) s := rfl
  have hpi : GlobalTheory.InertDbl.matD p⁻¹ = shear (Fin d) (-s) := rfl
  refine ⟨p, ⟨⟨fun u hu => ?_, fun z hz => ?_⟩, 1, ?_⟩, (diagonalFixingDoublingMatrix_eq_shear c d).symm⟩
  · have h0 : u • s = 0 := by rw [hsdef, ← mul_smul_comm, hat u hu, mul_zero]
    rw [hp, shear_eq, add_sub_cancel_left, ← smul_assoc, h0, zero_smul]
  · rw [hp, hpi]
    exact ⟨shear_mem_latAtD W v s hs hz, shear_mem_latAtD W v (-s) hs' hz⟩
  · exact shear_diagCols s

end GlobalTheory.SplitDblPar
end
