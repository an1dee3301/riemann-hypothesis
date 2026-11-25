module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormFiniteDimCompactStable
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.HeightProofs.AutomorphicFormUniformLimitDiscreteSeriesSeriesStatement
public import Development.Core20Slim.Formalism.LocalToGlobal.IndefiniteReal.MultLemmas
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSumOfMemMultSpan
public import Formalism.FormalDegreeBessel.StatementG
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.RealPlaceAnalysis.Complexify
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
noncomputable section
namespace GlobalTheory.CuspGKPet
open Matrix GlobalTheory.PointAtPlaceHom GlobalTheory.Mem.RealTranslate GlobalTheory.CuspGK GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}
theorem exists_petersson_pairing_gelfandKirillov_generator : FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ ψ : GA D V → ℂ, IsAutFunSm θ V ψ → IsCuspFun V ψ →
    (∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ ψ ∈ W ∧ ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) → ∀ f ∈ W, rTr V (atTau θ V τ g) f ∈ W) →
    ∃ b : (GA D V → ℂ) →ₗ⋆[ℂ] (GA D V → ℂ) →ₗ[ℂ] ℂ,
      (∀ x ∈ CuspGK.gkGen θ M ψ, x ≠ 0 → 0 < (b x x).re) ∧
      (∀ x ∈ CuspGK.gkGen θ M ψ, ∀ y ∈ CuspGK.gkGen θ M ψ, star (b x y) = b y x) ∧
      (∀ τ g, CuspGK.InK M τ g → ∀ x ∈ CuspGK.gkGen θ M ψ, ∀ y ∈ CuspGK.gkGen θ M ψ,
        b x (rTr V (atTau θ V τ g) y) = b (rTr V (atTau θ V τ g⁻¹) x) y) ∧
      (∀ τ, ∀ X ∈ lieAt V τ, ∀ x ∈ CuspGK.gkGen θ M ψ, ∀ y ∈ CuspGK.gkGen θ M ψ,
        b x (Rder θ V τ X y) = -b (Rder θ V τ X x) y) := by
  intro hP D θ V S M hθ ψ h1 h2 _
  obtain ⟨b, b1, b2, b3, b4⟩ := exists_form_cuspSub (V := V) hP.cuspRapidDecay hθ
  have hle : gkGen θ M ψ ≤ cuspSub θ V := gkGen_le θ M (A := cuspSub θ V) ⟨h1, h2⟩
    ⟨fun _ _ hg _ hf => rTr_mem_cuspSub hθ hg.1 hf, fun _ _ hX _ hf => Rder_mem_cuspSub hθ hX hf⟩
  exact ⟨b, fun x hx => b1 x (hle hx), fun x hx y hy => b2 x (hle hx) y (hle hy),
    fun τ g hg x hx y hy => b3 τ g hg.1 x (hle hx) y (hle hy),
    fun τ X hX x hx y hy => b4 τ X hX x (hle hx) y (hle hy)⟩
end GlobalTheory.CuspGKPet
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_form_petersson_nonvanishing_gelfandKirillov : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ ψ : GA D V → ℂ, IsAutFunSm θ V ψ → IsCuspFun V ψ →
    (∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ ψ ∈ W ∧ ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) → ∀ f ∈ W, rTr V (atTau θ V τ g) f ∈ W) →
    ∃ b : (GA D V → ℂ) →ₗ⋆[ℂ] (GA D V → ℂ) →ₗ[ℂ] ℂ,
      (∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, x ≠ 0 → 0 < (b x x).re) ∧
      (∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ, star (b x y) = b y x) ∧
      (∀ τ g, GlobalTheory.CuspGK.InK M τ g → ∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ,
        b x (rTr V (atTau θ V τ g) y) = b (rTr V (atTau θ V τ g⁻¹) x) y) ∧
      (∀ τ, ∀ X ∈ lieAt V τ, ∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ,
        b x (Rder θ V τ X y) = -b (Rder θ V τ X x) y) := by
  first | exact @_root_.GlobalTheory.CuspGKPet.exists_petersson_pairing_gelfandKirillov_generator | exact _root_.GlobalTheory.CuspGKPet.exists_petersson_pairing_gelfandKirillov_generator | (intros; apply _root_.GlobalTheory.CuspGKPet.exists_petersson_pairing_gelfandKirillov_generator <;> assumption)
end
