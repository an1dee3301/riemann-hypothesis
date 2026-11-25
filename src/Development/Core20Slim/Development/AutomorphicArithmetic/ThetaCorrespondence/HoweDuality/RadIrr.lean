module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.FactorApply
public import Development.Core20Slim.Development.WeilBound.ThetaLifts.SphericalLattices.ThetaSubSup
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelInfAlt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsGaussianTransform
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsOrbitKernel
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubGAlgDOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalAtFinitePlaceUnitaryGroupStatement
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.Core20Slim.Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.InertDef
public import Development.Core20Slim.Development.WeilBound.ThetaLifts.SphericalLattices.HoweInert
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.BinderNameHint
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.IsApply
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
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
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.Push
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open UpperTheory.Lit.HoweDuality GlobalTheory.HoweGlobalPair

theorem UpperTheory.Lit.HoweDuality.radIrr :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ} {om : Rep σ X W} {v : Pl (F := F)} {ω : UA σ X.J × UA σ W.J → Module.End ℂ (PositivityTheory.ThK.Fn F n d v)} {ρ : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Module.End ℂ (PositivityTheory.ThK.Fn F n d v)}, PositivityTheory.ThK.IsLocRep M ψ om v ω ρ → PositivityTheory.Sph.IrrAt om v → ∀ K : Submodule ℂ ↥(SB (Fin n × Fin d → Fv F v)), relFin om v ≤ K → Stable (opFin om v) K → K ≠ ⊤ → Rad (opFin om v) (relFin om v) K := by
  intro F E _ _ _ _ _ σ n d X W M ψ om v ω ρ hL hI K hrel hst hne
  have one_mem : (1 : UA σ X.J) ∈ UAt σ X (evFin F v) := by
    show At _ (mat 1 - 1)
    have h1 : mat (1 : UA σ X.J) = 1 := Matrix.ext fun i => congrFun rfl
    rw [h1, sub_self]
    intro _ _
    simp
  have aug_le : augAt om v ≤ SB (Fin n × Fin d → Fv F v) := by
    refine Submodule.span_le.mpr ?_
    rintro z ⟨g, -, φ, hφ, φ₁, hφ₁, -, rfl⟩
    exact Submodule.sub_mem _ hφ₁ hφ
  have key : ∀ P : Submodule ℂ ↥(SB (Fin n × Fin d → Fv F v)), relFin om v ≤ P →
      Stable (opFin om v) P → P = relFin om v ∨ P = ⊤ := by
    intro P hP hPs
    have hT : GlobalTheory.Published.ThetaSub om v (P.map (SB (Fin n × Fin d → Fv F v)).subtype) := by
      refine ⟨?_, ?_, ?_⟩
      · intro z hz
        have hzS := aug_le hz
        refine ⟨⟨z, hzS⟩, hP ?_, rfl⟩
        simpa [relFin] using hz
      · rintro _ ⟨k, -, rfl⟩
        exact k.2
      · rintro h hh _ ⟨k, hk, rfl⟩ φ₁ hφ₁ hA
        have hφ₁eq : φ₁ = ω (1, h) k := (hL.acts 1 one_mem h hh k k.2 φ₁).mp hA
        let g : Module.End ℂ ↥(SB (Fin n × Fin d → Fv F v)) :=
          { toFun := fun x => ⟨ω (1, h) x, hL.pres 1 one_mem h hh x x.2⟩
            map_add' := fun x y => by ext1; simp
            map_smul' := fun c x => by ext1; simp }
        have hg : g ∈ opFin om v := by
          refine ⟨h, hh, fun φ => ?_⟩
          exact (hL.acts 1 one_mem h hh φ φ.2 _).mpr rfl
        refine ⟨g k, hPs g hg k hk, ?_⟩
        simp [g, hφ₁eq]
    rcases hI _ hT with h1 | h1
    · left
      ext x
      constructor
      · intro hx
        have hx' : (x : (Fin n × Fin d → Fv F v) → ℂ) ∈ augAt om v := by
          rw [← h1]
          exact ⟨x, hx, rfl⟩
        simpa [relFin] using hx'
      · intro hx
        exact hP hx
    · right
      rw [eq_top_iff]
      intro x _
      have hx' : (x : (Fin n × Fin d → Fv F v) → ℂ) ∈ P.map (SB (Fin n × Fin d → Fv F v)).subtype := by
        rw [h1]
        exact x.2
      obtain ⟨y, hy, hyx⟩ := hx'
      have hyx' : y = x := Subtype.ext hyx
      rw [← hyx']
      exact hy
  have hK : K = relFin om v := by
    rcases key K hrel hst with h | h
    · exact h
    · exact absurd h hne
  obtain ⟨s, hs⟩ : ∃ s, s ∉ relFin om v := by
    by_contra hc
    push_neg at hc
    apply hne
    rw [hK, eq_top_iff]
    intro x _
    exact hc x
  refine ⟨s, ?_, ?_⟩
  · intro P hP hPs hsP
    rcases key P hP hPs with h | h
    · rw [h] at hsP
      exact absurd hsP hs
    · exact h
  · intro k hk
    refine ⟨1, Subalgebra.one_mem _, rfl, ?_⟩
    rw [hK] at hk
    simpa using hk
