module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.VacuumPhaseSubTraceMemIntegers
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependent
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.Gam0
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SatakeDualWeyl.StatementF
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

@[expose] public section

open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuumPhase_sub_trace_mem_integers : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (δ : L), (∀ x, Valued.v (σ x) = Valued.v x) → δ ∈ Formalism.UG.intL L →
  ∀ (n n' : ℕ) (JS a k : GL (Fin n) L) (JT : GL (Fin n') L) (E : Matrix (Fin n) (Fin n) L) (y : Matrix (Fin n') (Fin n) L),
  (∀ i j, (JS : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L) → (∀ i j, ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L) →
  (∀ i j, (JT : Matrix (Fin n') (Fin n') L) i j ∈ Formalism.UG.intL L) → GlobalTheory.Hk3.HoweG.SelfDual σ JS a →
  Formalism.UG.cT σ E * (JS : Matrix (Fin n) (Fin n) L) = -((JS : Matrix (Fin n) (Fin n) L) * E) →
  (∀ i j, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * E) i j ∈ Formalism.UG.intL L) → (∀ i j, (E * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) →
  (k : Matrix (Fin n) (Fin n) L) = 1 + E → (∀ i j, ((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L) →
  (∀ i j, (y * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) →
  GlobalTheory.Hk3.locH σ δ JS JT y (y * (((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - 1)) -
    δ * Matrix.trace (E * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Formalism.UG.cT σ y * (JT : Matrix (Fin n') (Fin n') L) * y) ∈ Formalism.UG.intL L := by
  first | exact @GlobalTheory.Hk3.VacPhase.locH_sub_trace_mem | exact GlobalTheory.Hk3.VacPhase.locH_sub_trace_mem | (intros; apply GlobalTheory.Hk3.VacPhase.locH_sub_trace_mem <;> assumption)
