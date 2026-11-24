module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiTensorMvPolynomialSubmoduleEqTopOfOneMulX
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.piTensorMvPolynomial_submodule_eq_top_of_one_mul_X : ∀ {ι σ : Type} [Fintype ι] [DecidableEq ι] (N : Submodule ℂ (⨂[ℂ] _ : ι, MvPolynomial σ ℂ)), PiTensorProduct.tprod ℂ (fun _ => (1 : MvPolynomial σ ℂ)) ∈ N → (∀ (w : ι) (l : σ), ∀ T ∈ N, atPl w (LinearMap.mulLeft ℂ (MvPolynomial.X l : MvPolynomial σ ℂ)) T ∈ N) → N = ⊤ := by
  first | exact @GlobalTheory.RealLift.tensor_submodule_eq_top | exact GlobalTheory.RealLift.tensor_submodule_eq_top | (intros; apply GlobalTheory.RealLift.tensor_submodule_eq_top <;> assumption)
