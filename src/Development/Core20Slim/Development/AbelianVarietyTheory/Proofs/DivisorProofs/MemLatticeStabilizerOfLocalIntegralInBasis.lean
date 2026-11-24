module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCO
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemGLintOfEntries
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlacesApart
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ChainMatrices
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SatakeDualWeyl.StatementE
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Subtype
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Tactic.Group

@[expose] public section

namespace StabilizerBasis
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.CompanionTheory.StabBasis

theorem exists_bc_eq_of_entries {R : Type} [CommRing R] (S : Subring R) {n : ℕ} (g : GL (Fin n) R)
    (h1 : ∀ i j, g.1 i j ∈ S) (h2 : ∀ i j, g⁻¹.1 i j ∈ S) :
    ∃ y : GL (Fin n) S, Formalism.UG.bc S.subtype y = g := by
  have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) S => A.map S.subtype :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.mul_inv
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.inv_mul

theorem mem_St_of_inBasis_mem_KO : ∀ {D : D7} {n : ℕ} (β x : GL (Fin n) (Lev.EAf D)),
    (∀ w : Pl D.host.E, inBasis rfl β w x ∈ KO (Kw w) (Fin n)) → x ∈ St β := by
  intro D n β x h
  have hent : ∀ (w : Pl D.host.E) (g : GL (Fin n) (Kw w)), g ∈ KO (Kw w) (Fin n) →
      ∀ i j, g.1 i j ∈ Formalism.UG.Ov D.host.E w := by
    intro w g hg i j
    rw [GlobalTheory.SmGL.SphCompletion.KO_completion w n] at hg
    obtain ⟨u, rfl⟩ := hg
    exact (u.1 i j).2
  have e2 : (β⁻¹ * x * β)⁻¹ = β⁻¹ * x⁻¹ * β := by group
  have a1 : ∀ i j, (β⁻¹ * x * β).1 i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun i j =>
    (mem_OA_iff _).2 fun w => by
      have := hent w _ (h w) i j
      rwa [inBasis_apply] at this
  have a2 : ∀ i j, (β⁻¹ * x * β)⁻¹.1 i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun i j =>
    (mem_OA_iff _).2 fun w => by
      have := hent w _ ((KO (Kw w) (Fin n)).inv_mem (h w)) i j
      rw [← map_inv, inBasis_apply] at this
      rwa [e2]
  obtain ⟨y, hy⟩ := exists_bc_eq_of_entries _ _ a1 a2
  refine ⟨y, ?_⟩
  have e : Formalism.L2.DIV.intGL D.host.F D.host.E n y = β⁻¹ * x * β := hy
  show β * Formalism.L2.DIV.intGL D.host.F D.host.E n y * β⁻¹ = x
  rw [e]; group

end GlobalTheory.CompanionTheory.StabBasis

end
end

end StabilizerBasis
section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

theorem _root_.GlobalTheory.Adopt.mem_latticeStabilizer_of_local_integral_inBasis : ∀ {D : D7} {n : ℕ} (β x : GL (Fin n) (Lev.EAf D)), (∀ w : Pl D.host.E, inBasis rfl β w x ∈ KO (Kw w) (Fin n)) → x ∈ St β := by
  first | exact @StabilizerBasis.GlobalTheory.CompanionTheory.StabBasis.mem_St_of_inBasis_mem_KO | exact StabilizerBasis.GlobalTheory.CompanionTheory.StabBasis.mem_St_of_inBasis_mem_KO | (intros; apply StabilizerBasis.GlobalTheory.CompanionTheory.StabBasis.mem_St_of_inBasis_mem_KO <;> assumption)

end
end
