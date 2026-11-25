module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.OuterIrrIsoWeylRep
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunEquiv
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MinorOrderedEntries
public import Formalism.LocalRingCardinality.DataCoeff
public import Init.Data.Int.Basic
public import Init.Prelude
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.outer_irr_iso_weylRep_of_pos : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ), 0 < n → ∀ (lam : ι → ℕ → ℤ) (μ : ι → DomWeight n), (∀ τ (i : Fin n), (μ τ).w i = lam τ i) → Iso (outer fun τ => irr n (μ τ)) (weylRep n lam) := by
  first | exact @GlobalTheory.OneFunctional.WeylTensor.outer_irr_iso_weylRep | exact GlobalTheory.OneFunctional.WeylTensor.outer_irr_iso_weylRep | (intros; apply GlobalTheory.OneFunctional.WeylTensor.outer_irr_iso_weylRep <;> assumption)
