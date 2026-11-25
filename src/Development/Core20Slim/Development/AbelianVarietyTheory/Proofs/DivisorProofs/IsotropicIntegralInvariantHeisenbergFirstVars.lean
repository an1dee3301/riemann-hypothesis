module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagWZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPlaneSeesaw
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Sum.Basic
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.LagIntTransl

def liftFst {R : Type} [CommRing R] {κ : Type} (a : (κ → R) × (κ → R)) : (κ ⊕ κ → R) × (κ ⊕ κ → R) :=
  (Sum.elim a.1 0, Sum.elim a.2 0)

theorem liftFst_add {R : Type} [CommRing R] {κ : Type} (a b : (κ → R) × (κ → R)) :
    liftFst (a + b) = liftFst a + liftFst b := by
  simp only [liftFst, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]
  refine Prod.ext ?_ ?_ <;> funext i <;> cases i <;> simp

theorem liftFst_dot {R : Type} [CommRing R] {κ : Type} [Fintype κ] (a b : (κ → R) × (κ → R)) :
    (liftFst a).1 ⬝ᵥ (liftFst b).2 = a.1 ⬝ᵥ b.2 := by
  simp [liftFst, dotProduct, Fintype.sum_sum_type]

theorem boxFun_schr {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (a : (κ → R) × (κ → R)) (φ₁ φ₂ : (κ → R) → ℂ) :
    boxFun (schr ψ a φ₁) φ₂ = schr ψ (liftFst a) (boxFun φ₁ φ₂) := by
  funext z
  simp only [boxFun, schr, liftFst, dotProduct, Fintype.sum_sum_type, Function.comp_apply, Sum.elim_inl, Sum.elim_inr,
    Pi.add_apply, Pi.zero_apply, mul_zero, add_zero, mul_assoc]
  have e1 : (z + Sum.elim a.1 0) ∘ Sum.inl = z ∘ Sum.inl + a.1 := by funext i; simp
  have e2 : (z + Sum.elim a.1 0) ∘ Sum.inr = z ∘ Sum.inr := by funext i; simp
  rw [e1, e2]
  simp

theorem diagW_schr (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ : Type) [Fintype κ] (ψ : AddChar (Fv F v) ℂ)
    (μ : @Measure (κ → Fv F v) (borel _)) (a w : (κ → Fv F v) × (κ → Fv F v)) (h : w.1 ⬝ᵥ a.2 = a.1 ⬝ᵥ w.2)
    (φ₁ φ₂ : (κ → Fv F v) → ℂ) :
    diagW ψ μ (boxFun (schr ψ a φ₁) φ₂) w = diagW ψ μ (boxFun φ₁ φ₂) (w + a) := by
  unfold diagW
  rw [boxFun_schr]
  congr 1
  funext x
  have h' : (liftFst w).1 ⬝ᵥ (liftFst a).2 = (liftFst a).1 ⬝ᵥ (liftFst w).2 := by
    rw [liftFst_dot, liftFst_dot, h]
  have := GlobalTheory.MixXEvUniq.schr_add ψ (liftFst w) (liftFst a) h' (boxFun φ₁ φ₂)
  rw [← liftFst_add] at this
  rw [show ((Sum.elim (w + a).1 0, Sum.elim (w + a).2 0) : (κ ⊕ κ → Fv F v) × (κ ⊕ κ → Fv F v)) = liftFst (w + a) from rfl,
    this]
  rfl

theorem main : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ : Type) [Fintype κ] (ψ : AddChar (Fv F v) ℂ) (μ : @Measure (κ → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (N : ℕ) (ν : @Measure (Fin N → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
    ∀ j : (Fin N → Fv F v) →ₗ[Fv F v] (κ → Fv F v) × (κ → Fv F v), (∀ y y', (j y).1 ⬝ᵥ (j y').2 = (j y').1 ⬝ᵥ (j y).2) →
    ∀ (y₀ : Fin N → Fv F v) (φ₁ φ₂ : (κ → Fv F v) → ℂ),
      lagInt ψ μ ν j (boxFun (schr ψ (j y₀) φ₁) φ₂) = lagInt ψ μ ν j (boxFun φ₁ φ₂) := by
  intro F _ _ v κ _ ψ μ _ N ν hν j hj y₀ φ₁ φ₂
  unfold lagInt
  have h1 : ∀ y, diagW ψ μ (boxFun (schr ψ (j y₀) φ₁) φ₂) (j y) = diagW ψ μ (boxFun φ₁ φ₂) (j (y + y₀)) := fun y => by
    rw [diagW_schr F v κ ψ μ _ _ (hj y y₀), map_add (f := _)]
  simp only [h1]
  letI : MeasurableSpace (Fin N → Fv F v) := borel _
  haveI : BorelSpace (Fin N → Fv F v) := ⟨rfl⟩
  exact integral_add_right_eq_self (μ := ν) (fun y => diagW ψ μ (boxFun φ₁ φ₂) (j y)) y₀

end GlobalTheory.LagIntTransl
end
