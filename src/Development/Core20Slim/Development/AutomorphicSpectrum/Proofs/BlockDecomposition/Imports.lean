module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsAdmissibleDegenerate
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactOpenSubgroupsBasis
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitarisableDegenerateSeries
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NontrivialSubrepresentation
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleUnitarySemisimpleStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetInducedTwoCharactersStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedTwoCharactersNotScalarStatement
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Init.Classical
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Bool.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Order.Atoms
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Disjoint
public import Mathlib.Order.Notation
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Tactic.Push
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.SmGL.Bernstein

theorem prod₂_detRep_isIrreducible :
    (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
      JacquetOfInducedFiltration k) →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → IsUnitaryChar χ₁ →
      IsUnitaryChar χ₂ → (a ≠ b ∨ χ₁ ≠ χ₂) →
      (prod₂ (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).IsIrreducible := by
  intro hJ k _ _ _ _ a b χ₁ χ₂ s₁ s₂ u₁ u₂ hne
  haveI := GlobalTheory.CompanionTheory.DegPrinSeries.nontrivial_subrepresentation k a b χ₁ χ₂ s₁ s₂
  show IsSimpleOrder (Subrepresentation (parInd (two (stdSum (rfl : a + b = a + b)))
    ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)))
  refine ⟨fun W => ?_⟩
  obtain ⟨W', hc⟩ := GlobalTheory.T.admissible_unitary_semisimple _ (GlobalTheory.CompanionTheory.SmGL.exists_compact_open_subgroup_subset k (a + b))
    (GlobalTheory.CompanionTheory.DegenSeries.isAdmissible_degenerate k a b χ₁ χ₂ s₁ s₂)
    (GlobalTheory.CompanionTheory.DegenerateSeries.isUnitarisable_degenerateSeries k a b χ₁ χ₂ s₁ s₂ u₁ u₂) W
  by_contra h
  push_neg at h
  have hW' : W' ≠ ⊥ := by
    rintro rfl
    exact h.2 (eq_top_of_isCompl_bot hc)
  exact GlobalTheory.T.induced_two_characters_not_scalar k a b χ₁ χ₂ W W' hc h.1 hW'
    (GlobalTheory.T.jacquet_induced_two_characters k a b χ₁ χ₂ (hJ k) s₁ s₂ u₁ u₂ hne)

end GlobalTheory.CompanionTheory.SmGL.Bernstein
