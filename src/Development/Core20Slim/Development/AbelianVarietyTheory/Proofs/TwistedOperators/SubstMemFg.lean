module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpDiv
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsPairReading
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactSubgroupsActOnFockVectorsAllSignatures
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignedUnitaryGroupCompat
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHermitianLogUnitaryBlockDiagonal
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmTypeRestrictRealSubfieldInfinitePlaceBijective
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasArchimedeanCharExponentsConjOfHasInfExp
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLines
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicRapidDecayOfMemAdelicSchwartzSpace
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CtxExists
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqOfThetaHeisenbergTranslates
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RaisingLoweringOperators
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Init.Classical
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Set.Insert
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Finiteness.Subalgebra
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

namespace GlobalTheory.SubstitutionFinitelyGenerated

theorem fg_of_vars {σ ι : Type*} (φ : ι → MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ)
    (h : ∀ v, ∃ U : Submodule ℂ (MvPolynomial σ ℂ), U.FG ∧ ∀ i, φ i (MvPolynomial.X v) ∈ U)
    (P : MvPolynomial σ ℂ) : ∃ V : Submodule ℂ (MvPolynomial σ ℂ), V.FG ∧ ∀ i, φ i P ∈ V := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    refine ⟨Submodule.span ℂ {MvPolynomial.C c}, Submodule.fg_span_singleton _, fun i => ?_⟩
    have : φ i (MvPolynomial.C c) = MvPolynomial.C c := (φ i).commutes c
    rw [this]
    exact Submodule.mem_span_singleton_self _
  | add p q hp hq =>
    obtain ⟨V₁, h₁, h₁'⟩ := hp
    obtain ⟨V₂, h₂, h₂'⟩ := hq
    refine ⟨V₁ ⊔ V₂, h₁.sup h₂, fun i => ?_⟩
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (h₁' i) (h₂' i)
  | mul_X p v hp =>
    obtain ⟨V₁, h₁, h₁'⟩ := hp
    obtain ⟨V₂, h₂, h₂'⟩ := h v
    refine ⟨V₁ * V₂, h₁.mul h₂, fun i => ?_⟩
    rw [map_mul]
    exact Submodule.mul_mem_mul (h₁' i) (h₂' i)

theorem subst_mem_fg : ∀ {D : Formalism.BasicNotions.D7} {a b : ℕ} (τ : Formalism.BasicNotions.Rows.Data.Tau (Formalism.BasicNotions.D7.what₂ D)) (ε : Fin a → Bool) (ε' : Fin b → Bool) (P : Formalism.IndefR.Links.PolF D b a), ∃ (V : Submodule ℂ (Formalism.IndefR.Links.PolF D b a)), Submodule.FG V ∧ ∀ (g : Matrix (Fin a) (Fin a) ℂ) (k : Matrix (Fin b) (Fin b) ℂ), (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.subst τ ε ε' g k : Formalism.IndefR.Links.PolF D b a → Formalism.IndefR.Links.PolF D b a) P ∈ V := by
  intro D a b τ ε ε' P
  obtain ⟨V, hV, hV'⟩ := fg_of_vars
    (fun gk : Matrix (Fin a) (Fin a) ℂ × Matrix (Fin b) (Fin b) ℂ => GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.subst τ ε ε' gk.1 gk.2) (by
      intro v
      refine ⟨Submodule.span ℂ (insert (MvPolynomial.X v)
        (Set.range fun lm : Fin b × Fin a => MvPolynomial.X (τ, lm.1, lm.2))),
        Submodule.fg_span ((Set.finite_range _).insert _), fun gk => ?_⟩
      unfold GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.subst
      rw [MvPolynomial.aeval_X]
      by_cases hv : v.1 = τ
      · rw [if_pos hv]
        refine Submodule.sum_mem _ fun l _ => Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ ?_
        exact Submodule.subset_span (Set.mem_insert_of_mem _ ⟨(l, m), rfl⟩)
      · rw [if_neg hv]
        exact Submodule.subset_span (Set.mem_insert _ _)) P
  exact ⟨V, hV, fun g k => hV' (g, k)⟩

end GlobalTheory.SubstitutionFinitelyGenerated
