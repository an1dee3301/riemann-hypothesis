module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsBlockOrd
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SignatureConjugationInvariant
public import Formalism.SatakeDualWeyl.Statement
public import Init.Core
public import Init.Data.Bool
public import Init.Data.Sum.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

noncomputable section
namespace GlobalTheory.HeisTwist

theorem jm_eq_diagonal (p q : ℕ) :
    Jm p q = Matrix.diagonal (Sum.elim (fun _ : Fin p => (1 : ℂ)) (fun _ : Fin q => (-1 : ℂ))) := by
  rw [Jm, Formalism.UG.Jpq, ← Matrix.fromBlocks_diagonal]
  simp [Matrix.diagonal_neg]
  ext i j
  by_cases h : i = j <;> simp [Matrix.diagonal_apply, h]

theorem jm_mul_mul_jm_apply {P Q R S : ℕ} (c : Matrix (Ix P Q) (Ix R S) ℂ) (a : Ix P Q) (b : Ix R S) :
    (Jm P Q * c * Jm R S) a b = lineSign a b * c a b := by
  rw [jm_eq_diagonal, jm_eq_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases a with a | a <;> rcases b with b | b <;> simp [lineSign]

theorem term_one {P Q R S : ℕ} (c : Matrix (Ix P Q) (Ix R S) ℂ) (l : Ln P Q R S) :
    (Complex.I * lineSign l.1 l.2 * c l.1 l.2) • raiB l (1 : Pol P Q R S)
      - (lineSign l.1 l.2 * star (Complex.I * lineSign l.1 l.2 * c l.1 l.2)) • lowB l 1
      = Complex.I • (c l.1 l.2 • raiB l (1 : Pol P Q R S) - (lineSign l.1 l.2 * star (c l.1 l.2)) • lowB l 1) := by
  rcases l with ⟨a | a, b | b⟩ <;>
    simp [raiB, lowB, linePos, lineSign, smul_sub, smul_smul] <;> ring_nf <;> simp [Complex.conj_I] <;> module

end GlobalTheory.HeisTwist

namespace GlobalTheory.RealLift

theorem heisOp_twist_one {P Q R S : ℕ} (c : Matrix (Ix P Q) (Ix R S) ℂ) :
    heisOp (Complex.I • (Jm P Q * c * Jm R S)) 1 = Complex.I • heisOp c 1 := by
  simp only [heisOp, LinearMap.smul_apply, LinearMap.sum_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [smul_comm Complex.I]
  congr 1
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Matrix.smul_apply,
    GlobalTheory.HeisTwist.jm_mul_mul_jm_apply, smul_eq_mul]
  rw [← GlobalTheory.HeisTwist.term_one c l, mul_assoc]

end GlobalTheory.RealLift
