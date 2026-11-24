module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVacuumMovedThetaVacuum
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsPowPrincipalFractionalIdeal
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Init.Core
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.FieldTheory.IntermediateField.Basic

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.FamilyTieProof




theorem mod1All_mul' {a b : ℂ} (ha : StandardLatticesGL3.Mod1All a) (hb : StandardLatticesGL3.Mod1All b) : StandardLatticesGL3.Mod1All (a * b) := by
  obtain ⟨h1, h1'⟩ := ha
  obtain ⟨h2, h2'⟩ := hb
  refine ⟨mul_mem h1 h2, fun σ => ?_⟩
  have e : (⟨a * b, mul_mem h1 h2⟩ : TaylorLogMetric.Qbar) = ⟨a, h1⟩ * ⟨b, h2⟩ := rfl
  rw [e, map_mul, norm_mul, h1' σ, h2' σ, one_mul]

theorem mod1All_inv {a : ℂ} (ha : StandardLatticesGL3.Mod1All a) : StandardLatticesGL3.Mod1All a⁻¹ := by
  obtain ⟨h1, h1'⟩ := ha
  refine ⟨inv_mem h1, fun σ => ?_⟩
  have e : (⟨a⁻¹, inv_mem h1⟩ : TaylorLogMetric.Qbar) = (⟨a, h1⟩ : TaylorLogMetric.Qbar)⁻¹ := rfl
  rw [e, map_inv₀, norm_inv, h1' σ, inv_one]







end GlobalTheory.FamilyTieProof
