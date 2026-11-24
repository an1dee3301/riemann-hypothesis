module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Init.Core
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.Algebra.UniformField
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions

def IotaExt {p : ℕ} [Fact p.Prime] (lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : ℂ ≃+* ℂ_[p]) : Prop :=
  ∀ x : Formalism.MainNotions.TaylorLogMetric.Qbar, ι (x : ℂ) = lam x



def LamExt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p]), ∃ ι : ℂ ≃+* ℂ_[p], IotaExt lam ι

def LamCIota : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : ℂ ≃+* ℂ_[p]), IotaExt lam ι →
    (∀ x : ℂ, x ∈ Formalism.MainNotions.TaylorLogMetric.Qbar → Formalism.MainNotions.TaylorLogMetric.lamC lam x = ι x) ∧
    (∀ x : ℂ, x ∉ Formalism.MainNotions.TaylorLogMetric.Qbar → Formalism.MainNotions.TaylorLogMetric.lamC lam x = 0)


end Formalism.L2.KerInert
