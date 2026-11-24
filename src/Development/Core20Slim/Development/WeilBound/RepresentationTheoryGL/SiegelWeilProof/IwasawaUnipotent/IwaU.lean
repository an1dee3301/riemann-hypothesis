module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinResidues.AnisotropicGlobalForms.SectionTrace.SecOf
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FourierZeroN
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Foundations.AnalyticOnNhdTsumNpow
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Ring.Units
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SProd
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open scoped NNReal Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open PositivityTheory.RgEis ResidueKilled.Tr
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.SwEis

def IwaU : Prop := ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (n : ℕ),
  Iwa ((adCM D.sp.cm.sig χ).uQ (-1) (Set.univ : Set (Fin n))) ((adCM D.sp.cm.sig χ).uK (-1) (Fin n))

def EIwa : Prop := Chart → IwaU

def Far : Prop :=
  ∀ (G G' : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
    [T2Space G'] [LocallyCompactSpace G'] (Φ : G ≃ₜ* G') (Γ P : Subgroup G) (Γ' K' P' : Subgroup G') (c : G' → ℂ) (η : G' → ℝ)
    (R : ℝ), IsCompact (K' : Set G') → IsPar Γ' K' P' c → IsHt Γ' K' P' η → (∀ g, g ∈ Γ ↔ Φ g ∈ Γ') → (∀ g, g ∈ P ↔ Φ g ∈ P') →
    (∀ x : ℝ, R < x → Conv Γ' P' fun g => x * η g) →
    ∀ f : G → ℂ, Continuous f → (∀ q ∈ P, ∀ g, f (q * g) = c (Φ q) * f g) →
      (∀ z : ℂ, R < z.re → ∀ C : Set G, IsCompact C → ∃ u : GlobalTheory.Eis.Cosets P Γ → ℝ, Summable u ∧
        ∀ g ∈ C, ∀ q, ‖GlobalTheory.Eis.term P Γ (fun x => Complex.exp (z * η (Φ x)) * f x) g q‖ ≤ u q) ∧
      (∀ g, DifferentiableOn ℂ (fun z => GlobalTheory.Eis.cosetSum P Γ (fun x => Complex.exp (z * η (Φ x)) * f x) g) {z | R < z.re}) ∧
      ContinuousOn (fun y : ℂ × G => GlobalTheory.Eis.cosetSum P Γ (fun x => Complex.exp (y.1 * η (Φ x)) * f x) y.2)
        ({z | R < z.re} ×ˢ Set.univ) ∧
      ∀ z : ℂ, ∀ γ ∈ Γ, ∀ g, GlobalTheory.Eis.cosetSum P Γ (fun x => Complex.exp (z * η (Φ x)) * f x) (γ * g) =
        GlobalTheory.Eis.cosetSum P Γ (fun x => Complex.exp (z * η (Φ x)) * f x) g

def EFar : Prop := HtLip → Far

def Glue : Prop :=
  ∀ (X I : Type) [TopologicalSpace X] (T : I → X → X) (e H : ℂ → X → ℂ) (A : ℂ → ℂ) (R : ℝ), Differentiable ℂ A → (∃ z, A z ≠ 0) →
    (∀ x, Differentiable ℂ (H · x)) → Continuous (fun y : ℂ × X => H y.1 y.2) →
    (∀ z : ℂ, R < z.re → ∀ x, H z x = A z * e z x) → (∀ x, DifferentiableOn ℂ (e · x) {z | R < z.re}) →
    ContinuousOn (fun y : ℂ × X => e y.1 y.2) ({z | R < z.re} ×ˢ Set.univ) → (∀ z i x, e z (T i x) = e z x) → ∀ s₀ : ℂ,
    ∃ (U : Set ℂ) (d : Polynomial ℂ) (E : ℂ → X → ℂ), IsOpen U ∧ IsRightDomain U ∧ s₀ ∈ U ∧ d ≠ 0 ∧
      (∀ x, DifferentiableOn ℂ (E · x) U) ∧ ContinuousOn (fun y : ℂ × X => E y.1 y.2) (U ×ˢ Set.univ) ∧
      (∀ z ∈ U, ∀ i x, E z (T i x) = E z x) ∧ ∀ z : ℂ, R < z.re → ∀ x, E z x = d.eval z * e z x

def ETop : Prop := Dict → DictInf → CMGood → GrpTop → BdetLaw → ExtLaw → ParLaw → SgAll → TStd → IwaU → Scal → Far → Glue →
  PositivityTheory.Rg.Sw.Glob.EisStrong

end PositivityTheory.Rg.SwEis

end
