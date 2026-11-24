module

public import Development.Core20Slim.Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.InertDef
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

namespace PositivityTheory.KCo

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ}

def aug (n d : ℕ) (ν α : kˣ →* ℂˣ) : Submodule ℂ (Matrix (Fin n) (Fin d) k → ℂ) :=
  Submodule.span ℂ {z | ∃ g : GL (Fin n) k, ∃ Φ ∈ SB (Matrix (Fin n) (Fin d) k), z = omB ν α g 1 Φ - Φ}

def Full (Φ : Matrix (Fin n) (Fin d) k → ℂ) : Prop := Φ ∈ SB (Matrix (Fin n) (Fin d) k) ∧ ∀ Y, Y.rank ≠ n → Φ Y = 0

def USm (χ : kˣ →* ℂˣ) : Prop := (∀ x, ‖(χ x : ℂ)‖ = 1) ∧ IsOpen (χ.ker : Set kˣ)

end Local

def SurjSt : Prop := ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ)
  (ν α : kˣ →* ℂˣ), USm ν → ν ≠ 1 → ∀ Φ ∈ SB (Matrix (Fin n) (Fin d) k), ∃ Φ₀, Full Φ₀ ∧ Φ - Φ₀ ∈ aug n d ν α

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Dict

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d}

def Reads (v : Pl F) (ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ))
    (T : ((Fin n × Fin d → AF F) → ℂ) → (Fin n × Fin d → AF F) → ℂ)
    (S : (Matrix (Fin n) (Fin d) (Fv F v) → ℂ) → Matrix (Fin n) (Fin d) (Fv F v) → ℂ) : Prop :=
  ∀ φ ∈ SB _, ∃ φ₁ ∈ SB _, Acts (evFin F v) T φ φ₁ ∧ ι φ₁ = S (ι φ)

structure IsDict (om : Rep σ X W) (v : Pl F) (ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ))
    (ν α : (Fv F v)ˣ →* ℂˣ) : Prop where
  left : ∀ g ∈ UAt σ X (evFin F v), ∃ g₀, Reads v ι (om (g, 1)) (omB ν α g₀ 1)
  leftOnto : ∀ g₀, ∃ g ∈ UAt σ X (evFin F v), Reads v ι (om (g, 1)) (omB ν α g₀ 1)
  right : ∀ h ∈ UAt σ W (evFin F v), ∃ h₀, Reads v ι (om (1, h)) (omB ν α 1 h₀)
  rightOnto : ∀ h₀, ∃ h ∈ UAt σ W (evFin F v), Reads v ι (om (1, h)) (omB ν α 1 h₀)

end Dict


def ActsUniq : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (v : Pl F) (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ),
    ∀ φ ∈ SB (κ → Fv F v), ∀ φ₁ φ₂, Acts (evFin F v) T φ φ₁ → Acts (evFin F v) T φ φ₂ → φ₁ = φ₂



end PositivityTheory.KCo
