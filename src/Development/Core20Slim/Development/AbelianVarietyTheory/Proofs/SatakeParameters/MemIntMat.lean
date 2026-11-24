module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Formalism.SatakeDualWeyl.StatementF
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

@[expose] public section

noncomputable section

namespace GlobalTheory.Hk3.HoweDuality

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def intMat (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (a b : ℕ) :
    AddSubgroup (Matrix (Fin a) (Fin b) L) where
  carrier := {u | ∀ i j, u i j ∈ Formalism.UG.intL L}
  zero_mem' := fun _ _ => (Formalism.UG.intL L).zero_mem
  add_mem' := fun ha hb i j => (Formalism.UG.intL L).add_mem (ha i j) (hb i j)
  neg_mem' := fun ha i j => (Formalism.UG.intL L).neg_mem (ha i j)

def intVec (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (a : ℕ) : AddSubgroup (Fin a → L) where
  carrier := {u | ∀ i, u i ∈ Formalism.UG.intL L}
  zero_mem' := fun _ => (Formalism.UG.intL L).zero_mem
  add_mem' := fun ha hb i => (Formalism.UG.intL L).add_mem (ha i) (hb i)
  neg_mem' := fun ha i => (Formalism.UG.intL L).neg_mem (ha i)

theorem mem_intMat {a b : ℕ} (u : Matrix (Fin a) (Fin b) L) : u ∈ intMat L a b ↔ ∀ i j, u i j ∈ Formalism.UG.intL L := Iff.rfl

theorem mem_intVec {a : ℕ} (u : Fin a → L) : u ∈ intVec L a ↔ ∀ i, u i ∈ Formalism.UG.intL L := Iff.rfl

def latIdx {a b : ℕ} (x : Matrix (Fin a) (Fin b) L) : ℕ :=
  Nat.card (Set.range fun u : intVec L b => (QuotientAddGroup.mk (Matrix.mulVec x (u : Fin b → L)) : (Fin a → L) ⧸ intVec L a))

end GlobalTheory.Hk3.HoweDuality

end
