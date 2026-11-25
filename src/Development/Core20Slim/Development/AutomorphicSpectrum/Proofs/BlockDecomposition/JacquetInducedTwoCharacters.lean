module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiltrationUniqueSubquotientStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CellFunctorNonscalarOffdiagStatement
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CellFunctorScalarDiagonalStatement
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Init.Core
public import Init.Data.Bool
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Nonempty
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Bool.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Order.Notation
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.SmGL.Bernstein

theorem proportional_of_equiv {G V V' W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W] [Module ℂ W]
    {τ : Representation ℂ G V} {τ' : Representation ℂ G V'} {σ : Representation ℂ G W}
    (E : τ.Equiv τ')
    (h : ∀ φ ψ : τ'.IntertwiningMap σ, φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap)
    (φ ψ : τ.IntertwiningMap σ) :
    φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap := by
  rcases h (φ.comp E.symm.toIntertwiningMap) (ψ.comp E.symm.toIntertwiningMap) with h0 | ⟨c, hc⟩
  · left
    ext v
    have := LinearMap.congr_fun h0 (E v)
    simpa using this
  · right
    refine ⟨c, ?_⟩
    ext v
    have := LinearMap.congr_fun hc (E v)
    simpa using this

theorem eq_zero_of_equiv {G V V' W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W] [Module ℂ W]
    {τ : Representation ℂ G V} {τ' : Representation ℂ G V'} {σ : Representation ℂ G W}
    (E : τ.Equiv τ') (h : ∀ φ : τ'.IntertwiningMap σ, φ.toLinearMap = 0)
    (φ : τ.IntertwiningMap σ) : φ.toLinearMap = 0 := by
  ext v
  have := LinearMap.congr_fun (h (φ.comp E.symm.toIntertwiningMap)) (E v)
  simpa using this

theorem exists_diagonal_sizeMatrix (a b : ℕ) :
    ∃ D : SizeMatrix (Two (Fin a) (Fin b)) (Two (Fin a) (Fin b)),
      ∀ B : SizeMatrix (Two (Fin a) (Fin b)) (Two (Fin a) (Fin b)), B = D ↔ B.1 false true = 0 := by
  have card_f : Fintype.card (Two (Fin a) (Fin b) false) = a := Fintype.card_fin a
  have card_t : Fintype.card (Two (Fin a) (Fin b) true) = b := Fintype.card_fin b
  refine ⟨⟨fun i j => if i = j then (if i then b else a) else 0, ?_, ?_⟩, fun B => ⟨?_, ?_⟩⟩
  · intro i; cases i <;> simp [card_f, card_t]
  · intro j; cases j <;> simp [card_f, card_t]
  · rintro rfl; simp
  · intro hB
    have r0 := B.2.1 false
    have r1 := B.2.1 true
    have c0 := B.2.2 false
    have c1 := B.2.2 true
    simp only [Fintype.sum_bool, card_f, card_t] at r0 r1 c0 c1
    apply Subtype.ext
    funext i j
    cases i <;> cases j <;> simp <;> omega


set_option maxHeartbeats 600000 in
theorem mackey_maps_proportional : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ), JacquetOfInducedFiltration k → IsSmoothChar χ₁ → IsSmoothChar χ₂ → IsUnitaryChar χ₁ → IsUnitaryChar χ₂ → (a ≠ b ∨ χ₁ ≠ χ₂) → (∀ φ ψ : (jac (two (stdSum (rfl : a + b = a + b))) (parInd (two (stdSum (rfl : a + b = a + b))) ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom))).IntertwiningMap (((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)), φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap) := by
  intro k _ _ _ _ a b χ₁ χ₂ hJ h₁ h₂ u₁ u₂ hne
  have hc : Continuous (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom :=
    continuous_prodMk.2 ⟨continuous_apply _, continuous_apply _⟩
  have hsm : IsSmooth ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp
      (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom) :=
    isSmooth_comp (isSmooth_extTensor ((isSmooth_ofChar_iff _).2 h₁.detChar)
      ((isSmooth_ofChar_iff _).2 h₂.detChar)) _ hc
  obtain ⟨N, bb, hb⟩ := hJ Bool Bool (Fin (a + b)) (Two (Fin a) (Fin b)) (Two (Fin a) (Fin b))
    (two (stdSum (rfl : a + b = a + b))) (two (stdSum (rfl : a + b = a + b)))
  obtain ⟨S, hm, hbot, htop, hE⟩ := hb (TensorProduct ℂ ℂ ℂ) _ hsm
  obtain ⟨D, hD⟩ := exists_diagonal_sizeMatrix a b
  obtain ⟨t₀, ht₀⟩ := bb.surjective D
  refine GlobalTheory.T.filtration_unique_subquotient _ ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom) N S hm hbot htop t₀ ?_ ?_
  · exact proportional_of_equiv (hE t₀ (SizeMatrix.nonempty_rows (bb t₀)).some (SizeMatrix.nonempty_cols (bb t₀)).some).some
      (GlobalTheory.T.cell_functor_scalar_diagonal k a b χ₁ χ₂ (bb t₀) _ _ ((hD _).1 ht₀))
  · intro t ht
    exact eq_zero_of_equiv (hE t (SizeMatrix.nonempty_rows (bb t)).some (SizeMatrix.nonempty_cols (bb t)).some).some
      (GlobalTheory.T.cell_functor_nonscalar_offdiag k a b χ₁ χ₂ h₁ h₂ u₁ u₂ hne (bb t) _ _ fun h0 =>
        ht (bb.injective (((hD _).2 h0).trans ht₀.symm)))

end GlobalTheory.CompanionTheory.SmGL.Bernstein
