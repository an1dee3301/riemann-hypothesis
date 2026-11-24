module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockOnePlaceIsoDirectSumPartitions
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunEquiv
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MinorOrderedEntries
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IrreducibleDistinctUnitary
public import Formalism.LocalRingCardinality.DataCoeff
public import Init.Data.Int.Basic
public import Init.Prelude
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
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
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockOnePlace_iso_directSum_partitions : ∀ (a b : ℕ) (α β : ℤ), Iso (Representation.directSum fun i : GlobalTheory.GLDuality.Part (min a b) => Representation.tprod ((twist (detU a ^ α) ((irr a (GlobalTheory.GLDuality.pad a i)).comp (conjU a))).comp (MonoidHom.fst (U a) (U b))) ((twist (detU b ^ β) (irr b (GlobalTheory.GLDuality.pad b i))).comp (MonoidHom.snd (U a) (U b)))) (fockOne a b α β) := by
  first | exact @GlobalTheory.OneFunctional.iso_directSum_fockOne | exact GlobalTheory.OneFunctional.iso_directSum_fockOne | (intros; apply GlobalTheory.OneFunctional.iso_directSum_fockOne <;> assumption)
