module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.VacuumTranslateSumSelfDualLatticeFixed
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependent
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntMat
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SatakeDualWeyl.StatementF
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.UniformSpace.Cauchy

@[expose] public section

open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuumTranslateSum_selfDualLattice_fixed : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M)
    (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M),
    GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ s : M, GlobalTheory.Hk3.LocVac ρ s →
    ∀ a : GL (Fin n) L, GlobalTheory.Hk3.HoweG.SelfDual σ JS a → ∀ Z : Finset (Matrix (Fin n') (Fin n) L),
    (∀ z ∈ Z, ∃ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) ∧
      z = u * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) →
    (∀ z ∈ Z, ∀ z' ∈ Z, z - z' ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n → z = z') →
    (∀ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) →
      ∃ z ∈ Z, u * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - z ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n) →
    ∀ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) →
      ρ (u * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) (∑ z ∈ Z, ρ z s) = ∑ z ∈ Z, ρ z s := by
  first | exact @GlobalTheory.Hk3.HoweG.vacuum_sum_selfDual_fixed | exact GlobalTheory.Hk3.HoweG.vacuum_sum_selfDual_fixed | (intros; apply GlobalTheory.Hk3.HoweG.vacuum_sum_selfDual_fixed <;> assumption)
