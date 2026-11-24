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
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.SplitDblGen

theorem tMat_mul_tMat_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (c : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (K K' : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
    K * K' = 1 → (c * c) • (K - 1) = K - 1 →
    GlobalTheory.SplitDblGen.tMat c K * GlobalTheory.SplitDblGen.tMat c K' = 1 := by
  intro F E _ _ _ _ _ d c K K' hKK hc
  have h2 : (half : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) * 2 = 1 := by
    unfold half
    rw [show (2 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) 2 from (map_ofNat _ 2).symm, ← map_mul, invOf_mul_self, map_one]
  have hP : (c * c) • ((K - 1) * (K' - 1)) = (K - 1) * (K' - 1) := by rw [← smul_mul_assoc, hc]
  have hsum : (K - 1) + (K' - 1) + (K - 1) * (K' - 1) = 0 := by
    rw [sub_mul, mul_sub, mul_sub, hKK]; noncomm_ring
  have hff : ((half * (1 + c)) * (half * (1 + c))) • ((K - 1) * (K' - 1))
      = (half * (1 + c)) • ((K - 1) * (K' - 1)) := by
    rw [show (half * (1 + c)) * (half * (1 + c)) = half * half * (1 + 2 * c) + half * half * (c * c) by ring,
      add_smul, ← smul_smul (half * half) (c * c), hP, ← add_smul]
    congr 1
    linear_combination (half * (1 + c)) * h2
  unfold tMat
  generalize half * (1 + c) = f at hff ⊢
  have e : (1 + f • (K - 1)) * (1 + f • (K' - 1))
      = 1 + f • ((K - 1) + (K' - 1)) + (f * f) • ((K - 1) * (K' - 1)) := by
    rw [add_mul, one_mul, mul_add, mul_one, smul_mul_smul_comm, smul_add]; abel
  rw [e, hff, add_assoc, ← smul_add, hsum, smul_zero, add_zero]

end GlobalTheory.SplitDblGen
