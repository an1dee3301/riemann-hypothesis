module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddHsConjLe
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
public import Formalism.RealPlaceAnalysis.Complexify
public import Formalism.RealPlaceAnalysis.InstMeasurableSpaceUJ
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactHaarRightInvariantInst
public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
public import Init.Core
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Star
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory GlobalTheory.KFourier

noncomputable section
namespace GlobalTheory.KFourier

theorem pairing_convolution_swap {n : ℕ} (ε : Fin n → Bool) (e q g : KG ε → ℂ)
    (he : Continuous e) (hq : Continuous q) (hg : Continuous g) :
    ∫ k', star (q k') * ∫ k, e k * g (k' * k) ∂(muK ε) ∂(muK ε) =
      ∫ y, g y * ∫ x, e x * star (q (y * x⁻¹)) ∂(muK ε) ∂(muK ε) := by
  haveI : IsProbabilityMeasure (muK ε) := (compact_haar_holds n ε).1
  haveI : (muK ε).IsInvInvariant := ⟨(compact_haar_holds n ε).2.2.2⟩
  haveI : SecondCountableTopology (KG ε) :=
    TopologicalSpace.Subtype.secondCountableTopology (KG ε : Set (UJ ε))

  have h1 : ∀ k' : KG ε, ∫ k, e k * g (k' * k) ∂(muK ε) = ∫ y, e (k'⁻¹ * y) * g y ∂(muK ε) := by
    intro k'
    have := integral_mul_left_eq_self (μ := muK ε) (fun y => e (k'⁻¹ * y) * g y) k'
    rw [← this]; simp [← mul_assoc]

  have h2 : ∀ y : KG ε, ∫ k', star (q k') * e (k'⁻¹ * y) ∂(muK ε) =
      ∫ x, e x * star (q (y * x⁻¹)) ∂(muK ε) := by
    intro y
    have a := integral_inv_eq_self (fun x => star (q (y * x)) * e ((y * x)⁻¹ * y)) (muK ε)
    have b := integral_mul_left_eq_self (μ := muK ε) (fun k' => star (q k') * e (k'⁻¹ * y)) y
    rw [← b, ← a]
    congr 1; funext x
    rw [mul_comm]; congr 2; group
  have hcont : Continuous (fun p : KG ε × KG ε => star (q p.1) * e (p.1⁻¹ * p.2) * g p.2) := by
    fun_prop
  have hint : Integrable (Function.uncurry fun (k' y : KG ε) => star (q k') * e (k'⁻¹ * y) * g y)
      ((muK ε).prod (muK ε)) :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc ∫ k', star (q k') * ∫ k, e k * g (k' * k) ∂(muK ε) ∂(muK ε)
      = ∫ k', ∫ y, star (q k') * e (k'⁻¹ * y) * g y ∂(muK ε) ∂(muK ε) := by
        congr 1; funext k'
        rw [h1, ← integral_const_mul]
        congr 1; funext y; ring
    _ = ∫ y, ∫ k', star (q k') * e (k'⁻¹ * y) * g y ∂(muK ε) ∂(muK ε) :=
        integral_integral_swap hint
    _ = ∫ y, g y * ∫ x, e x * star (q (y * x⁻¹)) ∂(muK ε) ∂(muK ε) := by
        congr 1; funext y
        rw [← h2, ← integral_const_mul]
        congr 1; funext k'; ring

end GlobalTheory.KFourier
