module

public import Development.Core20Slim.Formalism.LocalToGlobal.InertKernelTheory.StatementIota
public import Development.Core20Slim.ReciprocityTheory.ReductiveGroups.LatticeEmbeddings.IotaPlaceB
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Init.Classical
public import Init.Core
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.CharP.IntermediateField
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Cardinality
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Rat.Encodable
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Logic.Encodable.Basic
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Order.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.Algebraic.Cardinality
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.SetTheory.Cardinal.Basic
public import Mathlib.SetTheory.Cardinal.Continuum
public import Mathlib.SetTheory.Cardinal.Defs
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.UniformField
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.ValuedField

@[expose] public section

noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions

theorem lattice_extension : LamExt := by
  intro p _ lam
  have : Algebra.IsAlgebraic ℚ Formalism.MainNotions.TaylorLogMetric.Qbar := algebraicClosure.isAlgebraic ℚ ℂ
  have hR : Cardinal.mk Formalism.MainNotions.TaylorLogMetric.Qbar ≤ Cardinal.aleph0 :=
    (Algebra.IsAlgebraic.cardinalMk_le_max ℚ Formalism.MainNotions.TaylorLogMetric.Qbar).trans
      (max_le Cardinal.mk_le_aleph0 le_rfl)
  obtain ⟨σ, hσ⟩ := ReciprocityTheory.ChartRestriction.B3.iop_extEmb (algebraMap Formalism.MainNotions.TaylorLogMetric.Qbar ℂ) lam hR
    (by simp [Cardinal.mk_complex, Cardinal.aleph0_lt_continuum])
    (Cardinal.mk_complex.trans (ReciprocityTheory.ChartRestriction.T1.lat_mk_Cp p).symm)
  exact ⟨σ, fun x => hσ x⟩

theorem lattice_embedding : LamCIota := by
  intro p _ lam ι h
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · unfold Formalism.MainNotions.TaylorLogMetric.lamC
    rw [dite_eq_left hx]
    exact (h ⟨x, hx⟩).symm
  · unfold Formalism.MainNotions.TaylorLogMetric.lamC
    rw [dite_eq_right hx]


theorem lamExt : LamExt := lattice_extension
theorem lamCIota : LamCIota := lattice_embedding

end Formalism.L2.KerInert
