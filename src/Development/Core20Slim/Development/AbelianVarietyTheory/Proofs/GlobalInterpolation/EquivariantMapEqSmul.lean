module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InterlacingEquivariance
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitLastBlockActX
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.BranchesAlongOfIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
public import Formalism.LocalRingCardinality.DataCoeff
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open MvPolynomial NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance GlobalTheory.BranchFormula

namespace GlobalTheory.Branching

theorem equivariant_map_eq_smul : ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n), Formalism.MainNotions.PrimeDegreeVariant.Interlace h lam sg → ∀ (φ φ' : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ), (∀ ψ, ψ = φ ∨ ψ = φ' → (∀ f ∈ nablaSq ℂ N lam, ψ f ∈ nablaSq ℂ n sg) ∧ ∀ (g : GL (Fin n) ℂ), ∀ f ∈ nablaSq ℂ N lam, ψ (sqAct ℂ N lam (Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N h g) f) = sqAct ℂ n sg g (ψ f)) → (∃ f ∈ nablaSq ℂ N lam, φ' f ≠ 0) → ∃ c : ℂ, ∀ f ∈ nablaSq ℂ N lam, φ f = c • φ' f := by
  intro n N h lam sg hI φ φ' H hne
  let mk : ∀ ψ, (ψ = φ ∨ ψ = φ') → (resRep (MonoidHom.id (GL (Fin n) ℂ)) h lam).IntertwiningMap
      (smallRep (MonoidHom.id (GL (Fin n) ℂ)) sg) := fun ψ hψ =>
    ⟨ψ.restrict (H ψ hψ).1, fun g => LinearMap.ext fun f => Subtype.ext ((H ψ hψ).2 g f.1 f.2)⟩
  have h1 := (comult_id n N h lam sg).1 hI
  have hz : mk φ' (Or.inr rfl) ≠ 0 := by
    obtain ⟨f, hf, hf0⟩ := hne
    intro e
    apply hf0
    have := congrArg (fun F => ((F.toLinearMap ⟨f, hf⟩ : nablaSq ℂ n sg) : MvPolynomial (Fin n × Fin n) ℂ)) e
    exact this
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hz).1 h1 (mk φ (Or.inl rfl))
  refine ⟨c, fun f hf => ?_⟩
  have := congrArg (fun F => ((F.toLinearMap ⟨f, hf⟩ : nablaSq ℂ n sg) : MvPolynomial (Fin n × Fin n) ℂ)) hc
  exact this.symm

end GlobalTheory.Branching
