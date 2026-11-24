module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.GaussianThetaImagesAlgebraic
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsReading
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTransformGaussianVacuumIsFiniteDatumStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.ByCases
public import Init.Core
public import Init.Data.Bool
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.ThetaGaussAlg
variable {D : D7}
theorem theta_pure_tensor_gaussian_mem_fockAlgebraic : Published.HoweDualityReal → FunPr.ThetaLocalInputs →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Γ : IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
      (om : IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
      (h : TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc),
      TripleRead.IsTransp ψ true Γ.M om ωA e (IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW) (TripleRead.toUX X e h.JX) →
      TripleRead.IsTransp ψ false Γ.M' om' ωB e (IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁) (TripleRead.toUX X e h.JX) →
      ∀ R Rf, IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
        ∀ (f₀ : IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin W₁.rank × Fin (W.rank + W₁.rank)))
          (φ : ∀ v : IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin W₁.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ),
          Γ.M'.IsGauss Bs.ψ Bs.emb f₀ → (∀ v, φ v ∈ WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = Γ.M'.vac v) →
          TripleRead.thO Γ.M' ψ (sgn false W₁).gram e (IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ φ) ∈ algF ψ θ false A₁ B := by
  intro _ _ D ψ θ _ hθ W W₁ X A A₁ B α β _ ωA ωB _ _ e Bs Γ Xc om om' h _ _ R Rf hM f₀ φ hg hφ hvac
  obtain ⟨f, hf, hD⟩ := T.thetaTransform_gaussianVacuum_isFiniteDatum D ψ θ hθ false W₁ X A₁ B e.symm Bs hM.triple.base h.ψ Γ.V' Γ.W _ _ _ _
    (by simpa using h.JW₁) h.JX hM.triple.geo.hV' hM.triple.geo.hW
    (fun w => by
      obtain ⟨τ, h1, -, h3, h4⟩ := h.cart w
      exact ⟨τ, h1, by simpa using h3, h4⟩)
    Γ.M' hM.triple.geo.hM' (crd W₁ X e) (fun u => by simp only [Bool.false_eq_true, if_false, one_smul]; rfl)
    f₀ φ hg hφ hvac
  have e1 : TripleRead.thO Γ.M' ψ (sgn false W₁).gram e (IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ φ) = f := by
    funext x
    exact (hD.2 ((crd W₁ X e).symm x)).trans (congrArg f ((crd W₁ X e).apply_symm_apply x))
  rw [e1]
  exact Submodule.subset_span ⟨f, 1, hf, (fockF_one ψ θ false A₁ B f).symm⟩
end GlobalTheory.ThetaGaussAlg
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pure_gaussian_theta_lift_algebraic : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
      (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
      (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc),
      GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW) (GlobalTheory.TripleRead.toUX X e h.JX) →
      GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁) (GlobalTheory.TripleRead.toUX X e h.JX) →
      ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
        ∀ (f₀ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin W₁.rank × Fin (W.rank + W₁.rank)))
          (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin W₁.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ),
          Γ.M'.IsGauss Bs.ψ Bs.emb f₀ → (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = Γ.M'.vac v) →
          GlobalTheory.TripleRead.thO Γ.M' ψ (sgn false W₁).gram e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ φ) ∈ algF ψ θ false A₁ B := by
  first | exact @_root_.GlobalTheory.ThetaGaussAlg.theta_pure_tensor_gaussian_mem_fockAlgebraic | exact _root_.GlobalTheory.ThetaGaussAlg.theta_pure_tensor_gaussian_mem_fockAlgebraic | (intros; apply _root_.GlobalTheory.ThetaGaussAlg.theta_pure_tensor_gaussian_mem_fockAlgebraic <;> assumption)
end
