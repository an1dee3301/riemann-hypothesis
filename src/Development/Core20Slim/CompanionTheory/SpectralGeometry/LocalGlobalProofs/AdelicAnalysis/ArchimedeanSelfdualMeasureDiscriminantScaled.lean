module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdeleHaarMapEqScaledVolume
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LebesgueSelfdualForDotCharacter
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SelfdualMeasureTransportEquiv
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.AdelicChar
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Action
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.DenseEmbedding
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.SW

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem real_coord_eq_re {F : Type} [Field F] [NumberField F]
    (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) (hh : IsHomeomorph e)
    (he : ∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) (x : Ainf F) (w : InfinitePlace F) :
    e x w = (InfinitePlace.Completion.extensionEmbedding w (x w)).re := by
  have hf : Continuous fun y : Ainf F => e y w := (continuous_apply w).comp hh.continuous
  have hg : Continuous fun y : Ainf F =>
      (InfinitePlace.Completion.extensionEmbedding w (y w)).re :=
    Complex.continuous_re.comp
      ((InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply w))
  have key := (InfiniteAdeleRing.denseRange_algebraMap (K := F)).equalizer hf hg (by
    funext k
    simp only [Function.comp_apply]
    rw [he, GroundTheory.Global.extensionEmbedding_algebraMap_apply, ← hρ, Complex.ofReal_re])
  exact congrFun key x

theorem psiInf_std_mul {F : Type} [Field F] [NumberField F] (hF : IsTotallyReal F)
    (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) (hh : IsHomeomorph e)
    (he : ∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) (s t : Ainf F) :
    psiInf F (Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar F)) (s * t) =
      Complex.exp (2 * Real.pi * Complex.I * (((-1 : ℝ) * (e s ⬝ᵥ e t) : ℝ) : ℂ)) := by
  have htr : GroundTheory.Global.infiniteTrace F (s * t) = e s ⬝ᵥ e t := by
    rw [GroundTheory.Global.infiniteTrace_apply]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [(hF.isReal w).mult_eq_one, Nat.cast_one, one_mul,
      ← real_coord_eq_re ρ e hρ hh he, map_mul, Pi.mul_apply]
  have h1 : GroundTheory.Global.adelicChar F (pairA F (s * t) 0) =
      Real.fourierChar (-GroundTheory.Global.infiniteTrace F (s * t)) :=
    GroundTheory.Global.adelicChar_infinite (K := F) (s * t)
  show ((GroundTheory.Global.adelicChar F (pairA F (s * t) 0) : Circle) : ℂ) = _
  rw [h1, htr, Real.fourierChar_apply]
  congr 1
  push_cast
  ring

theorem selfDual_psiInf_std (F : Type) [Field F] [NumberField F] (hF : IsTotallyReal F)
    (laminf : Measure (Ainf F)) (hl : IsStdInf laminf) :
    SelfDual (Real.toNNReal (Real.sqrt |(discr F : ℝ)|) • laminf)
      (fun s t => psiInf F (Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar F)) (s * t)) := by
  obtain ⟨ρ, e, hρ, hh, he, -, hm⟩ := real_iso F hF
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  let e' : Ainf F ≃ₜ+ (InfinitePlace F → ℝ) :=
    { e.toAddEquiv with
      continuous_toFun := hh.continuous
      continuous_invFun :=
        (e.toEquiv.toHomeomorphOfContinuousOpen hh.continuous hh.isOpenMap).symm.continuous }
  have hcoe : ∀ x, e' x = e x := fun _ => rfl
  set c : ℝ := Real.sqrt |(discr F : ℝ)| with hc
  have hc0 : 0 < c := by
    have : (discr F : ℝ) ≠ 0 := by exact_mod_cast discr_ne_zero F
    exact Real.sqrt_pos.mpr (abs_pos.mpr this)
  have hmap : (Real.toNNReal c • laminf).map e' = (volume : Measure (InfinitePlace F → ℝ)) := by
    have h1 : laminf.map e' = ENNReal.ofReal c⁻¹ • (volume : Measure (InfinitePlace F → ℝ)) := hm laminf hl
    have h2 : ((Real.toNNReal c : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal c⁻¹ = 1 := by
      rw [ENNReal.coe_nnreal_eq, Real.coe_toNNReal _ hc0.le,
        ← ENNReal.ofReal_mul hc0.le, mul_inv_cancel₀ hc0.ne', ENNReal.ofReal_one]
    rw [Measure.map_smul, h1, ENNReal.smul_def, smul_smul, h2, one_smul]
    exact e'.continuous.measurable.aemeasurable
  have hsd := selfDual_real_coord (InfinitePlace F) (-1) (Or.inr rfl)
  rw [← hmap] at hsd
  have := (selfDual_transport (Ainf F) (InfinitePlace F → ℝ) e' (Real.toNNReal c • laminf)
    (fun x y => Complex.exp (2 * Real.pi * Complex.I * (((-1 : ℝ) * (x ⬝ᵥ y) : ℝ) : ℂ)))).mpr hsd
  convert this using 3 with s t
  exact psiInf_std_mul hF ρ e hρ hh he s t

end GlobalTheory.CompanionTheory.SW
