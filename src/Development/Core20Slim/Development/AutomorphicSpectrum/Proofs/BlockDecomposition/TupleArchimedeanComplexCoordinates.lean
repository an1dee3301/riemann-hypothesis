module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermInf
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatC
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch NumberField

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.TupHaar

theorem tup_coord_haar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (e : Ainf F ≃+* (InfinitePlace F → ℝ)) (τ : InfinitePlace F → (E →+* ℂ))
  (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)), IsCoord σ e τ Θ →
  ∀ n M : ℕ, ∃ Φ : (Fin n → Fin M → Ainf F ⊗[F] E) ≃+ (InfinitePlace F → Fin n → Fin M → ℂ),
    (∀ X, Φ X = tupC Θ X) ∧ Continuous Φ ∧ Continuous Φ.symm ∧
    ∀ μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E), μ.IsAddHaarMeasure →
      (μ.map Φ).IsAddHaarMeasure ∧ ∀ g : (InfinitePlace F → Fin n → Fin M → ℂ) → ℂ, ∫ X, g (Φ X) ∂μ = ∫ Y, g Y ∂(μ.map Φ) := by
  intro F E _ _ _ _ _ σ _ e τ Θ hco n M
  have hΘ : IsHomeomorph Θ := hco.1
  have hΘc : Continuous Θ := hΘ.continuous
  have hs : Continuous (Θ.symm : (InfinitePlace F → ℂ) → Ainf F ⊗[F] E) := by
    have h := (IsHomeomorph.homeomorph (⇑Θ) hΘ).symm.continuous
    convert h using 1
    funext y
    apply Θ.injective
    rw [RingEquiv.apply_symm_apply]
    exact ((IsHomeomorph.homeomorph (⇑Θ) hΘ).apply_symm_apply y).symm
  let Φ : (Fin n → Fin M → Ainf F ⊗[F] E) ≃+ (InfinitePlace F → Fin n → Fin M → ℂ) :=
    { toFun := fun X w a i => Θ (X a i) w
      invFun := fun Y a i => Θ.symm (fun w => Y w a i)
      left_inv := fun X => by funext a i; simp
      right_inv := fun Y => by funext w a i; simp
      map_add' := fun X X' => by funext w a i; simp }
  have hc' : Continuous (fun (X : Fin n → Fin M → Ainf F ⊗[F] E) (w : InfinitePlace F) (a : Fin n)
      (i : Fin M) => Θ (X a i) w) := by fun_prop
  have hcs' : Continuous (fun (Y : InfinitePlace F → Fin n → Fin M → ℂ) (a : Fin n) (i : Fin M) =>
      Θ.symm (fun w => Y w a i)) := by fun_prop
  have hc : Continuous Φ := hc'
  have hcs : Continuous Φ.symm := hcs'
  refine ⟨Φ, fun X => rfl, hc, hcs, fun μ hμ => ?_⟩
  haveI := hμ
  refine ⟨AddEquiv.isAddHaarMeasure_map μ Φ hc hcs, fun g => ?_⟩
  let h : (Fin n → Fin M → Ainf F ⊗[F] E) ≃ₜ (InfinitePlace F → Fin n → Fin M → ℂ) :=
    ⟨Φ.toEquiv, hc, hcs⟩
  exact (h.measurableEmbedding.integral_map g).symm

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.TupHaar
