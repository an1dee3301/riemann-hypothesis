module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryIrrepCompConjIsoDual
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunEquiv
public import Formalism.LocalRingCardinality.DataCoeff
public import Init.Prelude
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryIrrep_comp_conj_iso_dual : ∀ (n : ℕ), 0 < n → ∀ lam : DomWeight n, Iso ((irr n lam).comp (conjU n) : Representation ℂ (U n) (nablaSq ℂ n lam)) (irr n lam.dual) := by
  first | exact @GlobalTheory.OneFunctional.iso_irr_comp_conjU | exact GlobalTheory.OneFunctional.iso_irr_comp_conjU | (intros; apply GlobalTheory.OneFunctional.iso_irr_comp_conjU <;> assumption)
