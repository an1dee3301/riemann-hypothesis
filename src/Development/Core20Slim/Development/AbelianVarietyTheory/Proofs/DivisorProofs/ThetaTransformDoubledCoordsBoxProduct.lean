module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUgReindex
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerOperatorMemAdelicSchwartzStdChar
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledCoordsThetaTransformProductEqTensorConj
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsGLSubmatrix
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
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
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
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilSchrodinger.DblTarget.ThetaBox

variable {F : Type} [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)]

theorem thetaSum_schr_negY (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hu : ∀ a, ‖ψ a‖ = 1) {κ : Type} [Fintype κ]
    (x y : κ → AdeleRing (𝓞 F) F) (φ : (κ → AdeleRing (𝓞 F) F) → ℂ) :
    GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (x, -y) φ) =
      star (GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (x, y) (fun u => star (φ u)))) := by
  have hc : ∀ t, starRingEnd ℂ (ψ t) = ψ (-t) := fun t => by
    rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hu t)]
  unfold GlobalTheory.WeilM.thetaSum
  rw [Complex.star_def, Complex.conj_tsum]
  refine tsum_congr fun ξ => ?_
  generalize (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) = a
  simp only [GlobalTheory.WeilM.schr, map_mul, Complex.star_def, Complex.conj_conj, hc, dotProduct_neg, neg_add, mul_neg]

end GlobalTheory.WeilSchrodinger.DblTarget.ThetaBox


open GlobalTheory.WeilSchrodinger.DblTarget.ThetaBox in
theorem GlobalTheory.WeilSchrodinger.DblTarget.thetaTr_coDbl_boxFun : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (hA : JA = T.gramᵀ) (κ : Type) [Fintype κ]
      (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
      ∀ φ₁ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ φ₂ ∈ GlobalTheory.WeilM.schA D.host.F κ,
        GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.WeilSchrodinger.DblTarget.coDbl hA co) ψ (GlobalTheory.WeilM.boxFun φ₁ φ₂) =
          fun w : Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) =>
            GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ φ₁ (w.submatrix (finSumFinEquiv ∘ Sum.inl) id) *
              star (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ (fun x => star (φ₂ x)) (w.submatrix (finSumFinEquiv ∘ Sum.inr) id)) := by
  intro D ψ hψ S T JA JB ξ hA κ _ co φ₁ h₁ φ₂ h₂
  funext w
  have he : (GlobalTheory.WeilSchrodinger.DblTarget.coDbl hA co).e w =
      (Sum.elim (co.e (w.submatrix (finSumFinEquiv ∘ Sum.inl) id)).1 (co.e (w.submatrix (finSumFinEquiv ∘ Sum.inr) id)).1,
        Sum.elim (co.e (w.submatrix (finSumFinEquiv ∘ Sum.inl) id)).2
          (-(co.e (w.submatrix (finSumFinEquiv ∘ Sum.inr) id)).2)) := rfl
  have hs : ∀ (v : (κ → AF D.host.F) × (κ → AF D.host.F)) (φ : (κ → AF D.host.F) → ℂ),
      φ ∈ GlobalTheory.WeilM.schA D.host.F κ → GlobalTheory.WeilM.schr ψ v φ ∈ GlobalTheory.WeilM.schA D.host.F κ :=
    fun v φ hφ => GlobalTheory.SchrSchA.schr_mem_schA_of_isStdChar D ψ hψ κ v φ hφ
  simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.Darboux.rho]
  rw [he, DoublingThetaSums.GlobalTheory.CompanionTheory.DblTheta.schr_boxFun_elim,
    DoublingThetaSums.GlobalTheory.CompanionTheory.DblTheta.thetaSum_boxFun _ (hs _ _ h₁) (hs _ _ h₂), thetaSum_schr_negY ψ hψ.1.2.1]

end
