module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCO
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemGLintOfEntries
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlacesApart
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridBlockCongruenceTypePrimeDescription
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Fin.Lemmas
public import Init.Data.Nat.Basic
public import Init.Data.Sum.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.SuccPred
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Order.SuccPred.Nat
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

namespace IwahoriGroupOffset
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.CompanionTheory.StepGroupOff

theorem symm_mem_KO_iff {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (e : a ≃ b) (g : GL b k) :
    (reGL e).symm g ∈ KO k a ↔ g ∈ KO k b := by
  rw [mem_KO, mem_KO, ← map_inv, reGL_symm_val, reGL_symm_val]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j => by simpa using h1 (e.symm i) (e.symm j), fun i j => by simpa using h2 (e.symm i) (e.symm j)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j => h1 _ _, fun i j => h2 _ _⟩

theorem twoBlock_gridIndex {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E)
    (j : ℕ) (x : Ix (Fin D.R.r) (Fin D.R.t) j) :
    Formalism.L2.DIV.blk2 D.R.r (ixFin G t w j x) = Sum.elim (fun _ => 0) (fun _ => 1) x := by
  rcases x with a | ⟨c, b⟩
  · simp [Formalism.L2.DIV.blk2, (ixFin_val G t w j).1 a]
  · simp [Formalism.L2.DIV.blk2, (ixFin_val G t w j).2 c b]

theorem mem_map_stepGroup_iff : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E), w ∉ L.Pg → ∀ (j : ℕ) (g : GL (Fin ((locGrid G t w).rank (0, j))) (Kw w)), g ∈ (stepGroup L t w j).map (reGL (ixFin G t w j)).toMonoidHom ↔ g ∈ KO (Kw w) (Fin ((locGrid G t w).rank (0, j))) ∧ (w ∈ L.Q t → ∀ a b, Formalism.L2.DIV.blk2 D.R.r b < Formalism.L2.DIV.blk2 D.R.r a → valuation (Kw w) (g.1 a b) < 1) := by
  intro D T L sc G t w hP j g
  rw [Subgroup.mem_map_equiv, stepGroup, if_neg hP]
  by_cases hQ : w ∈ L.Q t
  · rw [if_pos hQ]
    refine (mem_parahoric (k := Kw w) (r := Fin D.R.r) (s := Fin j × Fin D.R.t) (δ := 1) (hδ := fun _ _ => rfl)).trans ?_
    rw [symm_mem_KO_iff]
    refine and_congr_right fun _ => ?_
    constructor
    · intro h _ a b hab
      obtain ⟨x, rfl⟩ := (ixFin G t w j).surjective a
      obtain ⟨y, rfl⟩ := (ixFin G t w j).surjective b
      rw [twoBlock_gridIndex, twoBlock_gridIndex] at hab
      rcases x with x | x <;> rcases y with y | y
      · simp at hab
      · simp at hab
      · simpa [reGL_symm_val, Matrix.toBlocks₂₁] using h x y
      · simp at hab
    · intro h i l
      have := h hQ (ixFin G t w j (.inr i)) (ixFin G t w j (.inl l)) (by simp [twoBlock_gridIndex])
      simpa [reGL_symm_val, Matrix.toBlocks₂₁] using this
  · rw [if_neg hQ, symm_mem_KO_iff]
    exact ⟨fun h => ⟨h, fun h' => absurd h' hQ⟩, fun h => h.1⟩

end GlobalTheory.CompanionTheory.StepGroupOff

end
end

end IwahoriGroupOffset
section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

theorem _root_.GlobalTheory.Adopt.thetaGridBlockCongruence_offTypePrime_description : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E), w ∉ L.Pg → ∀ (j : ℕ) (g : GL (Fin ((locGrid G t w).rank (0, j))) (Kw w)), g ∈ (stepGroup L t w j).map (reGL (ixFin G t w j)).toMonoidHom ↔ g ∈ KO (Kw w) (Fin ((locGrid G t w).rank (0, j))) ∧ (w ∈ L.Q t → ∀ a b, Formalism.L2.DIV.blk2 D.R.r b < Formalism.L2.DIV.blk2 D.R.r a → valuation (Kw w) (g.1 a b) < 1) := by
  first | exact @IwahoriGroupOffset.GlobalTheory.CompanionTheory.StepGroupOff.mem_map_stepGroup_iff | exact IwahoriGroupOffset.GlobalTheory.CompanionTheory.StepGroupOff.mem_map_stepGroup_iff | (intros; apply IwahoriGroupOffset.GlobalTheory.CompanionTheory.StepGroupOff.mem_map_stepGroup_iff <;> assumption)

end
end
