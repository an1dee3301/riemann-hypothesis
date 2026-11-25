module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDblCoordDblD
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerOperatorMemAdelicSchwartzStdChar
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Sum.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

namespace DoublingThetaSums
section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.DblTheta

section Gen

variable {R : Type} [CommRing R] [Invertible (2 : R)]

theorem schr_boxFun_elim (ψ : AddChar R ℂ) {κ κ' : Type} [Fintype κ] [Fintype κ'] (x₁ y₁ : κ → R) (x₂ y₂ : κ' → R)
    (φ₁ : (κ → R) → ℂ) (φ₂ : (κ' → R) → ℂ) :
    GlobalTheory.WeilM.schr ψ (Sum.elim x₁ x₂, Sum.elim y₁ y₂) (GlobalTheory.WeilM.boxFun φ₁ φ₂) =
      GlobalTheory.WeilM.boxFun (GlobalTheory.WeilM.schr ψ (x₁, y₁) φ₁) (GlobalTheory.WeilM.schr ψ (x₂, y₂) φ₂) := by
  funext z
  have e₁ : (z + Sum.elim x₁ x₂) ∘ Sum.inl = z ∘ Sum.inl + x₁ := rfl
  have e₂ : (z + Sum.elim x₁ x₂) ∘ Sum.inr = z ∘ Sum.inr + x₂ := rfl
  have e₃ : z ⬝ᵥ Sum.elim y₁ y₂ + ⅟(2 : R) * (Sum.elim x₁ x₂ ⬝ᵥ Sum.elim y₁ y₂) =
      ((z ∘ Sum.inl) ⬝ᵥ y₁ + ⅟(2 : R) * (x₁ ⬝ᵥ y₁)) + ((z ∘ Sum.inr) ⬝ᵥ y₂ + ⅟(2 : R) * (x₂ ⬝ᵥ y₂)) := by
    simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Function.comp_apply]
    ring
  simp only [GlobalTheory.WeilM.schr, GlobalTheory.WeilM.boxFun, e₁, e₂, e₃]
  rw [AddChar.map_add_eq_mul]
  ring

end Gen

section Sums

variable (F : Type) [Field F] [NumberField F]

theorem thetaSum_boxFun {κ κ' : Type} [Fintype κ] [Fintype κ'] {A : (κ → AdeleRing (𝓞 F) F) → ℂ}
    {B : (κ' → AdeleRing (𝓞 F) F) → ℂ} (hA : A ∈ GlobalTheory.WeilM.schA F κ) (hB : B ∈ GlobalTheory.WeilM.schA F κ') :
    GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.boxFun A B) = GlobalTheory.WeilM.thetaSum F A * GlobalTheory.WeilM.thetaSum F B := by
  unfold GlobalTheory.WeilM.thetaSum
  rw [tsum_mul_tsum_of_summable_norm (GlobalTheory.WeilM.summable_norm_of_mem_schA F hA)
    (GlobalTheory.WeilM.summable_norm_of_mem_schA F hB), ← (Equiv.sumArrowEquivProdArrow κ κ' F).tsum_eq]
  exact tsum_congr fun ξ => rfl

theorem thetaSum_schr_neg [Invertible (2 : AdeleRing (𝓞 F) F)] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (hu : ∀ a, ‖ψ a‖ = 1) {κ : Type} [Fintype κ] (x y : κ → AdeleRing (𝓞 F) F)
    (φ : (κ → AdeleRing (𝓞 F) F) → ℂ) :
    GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (x, -y) φ) =
      starRingEnd ℂ (GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (-x, -y) (fun u => starRingEnd ℂ (φ (-u))))) := by
  have hc : ∀ t, starRingEnd ℂ (ψ t) = ψ (-t) := fun t => by
    rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hu t)]
  have key : ∀ ξ : κ → F,
      GlobalTheory.WeilM.schr ψ (x, -y) φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) ((-ξ) i)) =
        starRingEnd ℂ (GlobalTheory.WeilM.schr ψ (-x, -y) (fun u => starRingEnd ℂ (φ (-u)))
          (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))) := by
    intro ξ
    have ha : (fun i => algebraMap F (AdeleRing (𝓞 F) F) ((-ξ) i)) =
        -(fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) := by
      funext i; simp
    rw [ha]
    generalize (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) = a
    simp only [GlobalTheory.WeilM.schr, map_mul, Complex.conj_conj, hc]
    have h1 : -a + x = -(a + -x) := by abel
    have h2 : -a ⬝ᵥ -y + ⅟(2 : AdeleRing (𝓞 F) F) * (x ⬝ᵥ -y) =
        -(a ⬝ᵥ -y + ⅟(2 : AdeleRing (𝓞 F) F) * (-x ⬝ᵥ -y)) := by
      simp only [neg_dotProduct, dotProduct_neg]
      ring
    rw [h1, h2]
  unfold GlobalTheory.WeilM.thetaSum
  calc _ = ∑' ξ : κ → F, GlobalTheory.WeilM.schr ψ (x, -y) φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) ((-ξ) i)) :=
        ((Equiv.neg (κ → F)).tsum_eq
          (fun ξ : κ → F => GlobalTheory.WeilM.schr ψ (x, -y) φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)))).symm
    _ = _ := tsum_congr key
    _ = _ := (Complex.conj_tsum _).symm

end Sums

theorem thetaTr_ddr_boxFun : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (κ : Type) [Fintype κ]
      (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
      ∀ φ₁ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ φ₂ ∈ GlobalTheory.WeilM.schA D.host.F κ,
        GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.DblSchr.ddr co) ψ (GlobalTheory.WeilM.boxFun φ₁ φ₂) =
          GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta S T (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ φ₁)
            (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ (fun x => starRingEnd ℂ (φ₂ (-x)))) := by
  intro D ψ hψ S T JA JB ξ κ _ co φ₁ h₁ φ₂ h₂
  funext x
  have he : (GlobalTheory.DblSchr.ddr co).e x =
      (Sum.elim (co.e (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resL S T x)).1 (co.e (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resR S T x)).1,
        Sum.elim (co.e (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resL S T x)).2 (-(co.e (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resR S T x)).2)) := rfl
  have hn : co.e (-GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resR S T x) =
      (-(co.e (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resR S T x)).1, -(co.e (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resR S T x)).2) := by
    rw [map_neg]; rfl
  have hs : ∀ (w : (κ → AF D.host.F) × (κ → AF D.host.F)) (φ : (κ → AF D.host.F) → ℂ),
      φ ∈ GlobalTheory.WeilM.schA D.host.F κ → GlobalTheory.WeilM.schr ψ w φ ∈ GlobalTheory.WeilM.schA D.host.F κ :=
    fun w φ hφ => GlobalTheory.SchrSchA.schr_mem_schA_of_isStdChar D ψ hψ κ w φ hφ
  simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta]
  rw [he, hn, schr_boxFun_elim, thetaSum_boxFun _ (hs _ _ h₁) (hs _ _ h₂),
    thetaSum_schr_neg _ ψ hψ.1.2.1]

end GlobalTheory.CompanionTheory.DblTheta

end

end

end DoublingThetaSums
section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.Adopt.doubledCoordsThetaTransform_product_eq_tensor_conj : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (κ : Type) [Fintype κ]
      (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
      ∀ φ₁ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ φ₂ ∈ GlobalTheory.WeilM.schA D.host.F κ,
        GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.DblSchr.ddr co) ψ (GlobalTheory.WeilM.boxFun φ₁ φ₂) =
          GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta S T (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ φ₁)
            (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ (fun x => starRingEnd ℂ (φ₂ (-x)))) := by
  first | exact @DoublingThetaSums.GlobalTheory.CompanionTheory.DblTheta.thetaTr_ddr_boxFun | exact DoublingThetaSums.GlobalTheory.CompanionTheory.DblTheta.thetaTr_ddr_boxFun | (intros; apply DoublingThetaSums.GlobalTheory.CompanionTheory.DblTheta.thetaTr_ddr_boxFun <;> assumption)

end
