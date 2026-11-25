module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyReal
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsUnipotentInvariantCompactlySupportedWeight
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Init.Tactics
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Action
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Basic.Unique
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.SdAny

theorem selfDual_map {V W : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] [AddCommGroup W] [TopologicalSpace W]
    [IsTopologicalAddGroup W] [MeasurableSpace W] [BorelSpace W] (e : V ≃ₜ+ W) (μ : Measure V)
    (χ : V → V → ℂ) (h : SelfDual μ χ) :
    SelfDual (μ.map e) (fun x y => χ (e.symm x) (e.symm y)) := by
  obtain ⟨hH, hinv⟩ := h
  have hemb : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  refine ⟨e.isAddHaarMeasure_map μ, ?_⟩
  intro Φ hc hs hint z
  let H : V → ℂ := fun y => ∫ x, Φ (e x) * χ x y ∂μ
  have h1 : ∀ y, ∫ x, Φ x * χ (e.symm x) (e.symm y) ∂(μ.map e) = H (e.symm y) := fun y => by
    rw [hemb.integral_map]
    simp [H]
  simp only [h1] at hint ⊢
  have hint2 : Integrable H μ := by
    have h2 := (hemb.integrable_map_iff).1 hint
    simpa [Function.comp_def] using h2
  have h3 := hinv (Φ ∘ e) (hc.comp e.continuous) (hs.comp_homeomorph e.toHomeomorph) hint2 (e.symm z)
  rw [hemb.integral_map]
  simp only [ContinuousAddEquiv.symm_apply_apply]
  refine h3.trans ?_
  simp

section Unit

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

def evalE : (Unit → R) ≃ₜ+ R where
  toFun x := x ()
  invFun s := fun _ => s
  left_inv x := rfl
  right_inv s := rfl
  map_add' x y := rfl
  continuous_toFun := continuous_apply ()
  continuous_invFun := continuous_pi fun _ => continuous_id

variable [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R]

theorem iff_of_unit (ψR : R → ℂ) (lam : Measure R) [SigmaFinite lam] (c : ℝ≥0)
    (B : Matrix Unit Unit R) (hB : B = 1)
    (h : ∀ μ : Measure (Unit → R), SelfDual μ (fun x y => ψR (x ⬝ᵥ (B *ᵥ y))) ↔
      μ = c • Measure.pi fun _ => lam) (ν : Measure R) :
    SelfDual ν (fun s t => ψR (s * t)) ↔ ν = c • lam := by
  subst hB
  have hχ : (fun x y : Unit → R => ψR (x ⬝ᵥ ((1 : Matrix Unit Unit R) *ᵥ y))) =
      fun x y => ψR (evalE x * evalE y) := by
    funext x y
    simp [evalE, dotProduct]
  rw [hχ] at h
  have hm : Measurable (evalE : (Unit → R) ≃ₜ+ R) := evalE.continuous.measurable
  have hms : Measurable (evalE.symm : R ≃ₜ+ (Unit → R)) := evalE.symm.continuous.measurable
  have hp : (Measure.pi fun _ : Unit => lam).map evalE = lam :=
    (measurePreserving_funUnique lam Unit).map_eq
  have hmm : ∀ μ : Measure R, (μ.map evalE.symm).map evalE = μ := fun μ => by
    rw [Measure.map_map hm hms]
    convert Measure.map_id
    ext x
    simp
  constructor
  · intro hν
    have h1 := selfDual_map evalE.symm ν _ hν
    have h2 := (h _).1 h1
    have h3 := congrArg (Measure.map evalE) h2
    rw [hmm, Measure.map_smul, hp] at h3 <;> try exact hm.aemeasurable
    exact h3
  · rintro rfl
    have h1 := selfDual_map evalE _ _ ((h _).2 rfl)
    rw [Measure.map_smul, hp] at h1 <;> try exact hm.aemeasurable
    simpa using h1

end Unit


end GlobalTheory.CompanionTheory.SW.SdAny
