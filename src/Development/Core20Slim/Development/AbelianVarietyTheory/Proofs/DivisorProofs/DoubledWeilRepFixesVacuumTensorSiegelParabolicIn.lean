module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.AdelicAdmissibleSmul
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMemAdelicSchwartzSpaceNumberFieldOfMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceDoubledUnitaryVacuumTensorEigenStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslationInvariantDoubledFormConjProductStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledSiegelParabolicDiagonalActionIntegralStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComparisonCharacterDetEqOneInertPlaceStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalThetaIntegralAtInertPlaceStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuum
public import Formalism.SatakeDualWeyl.StatementG
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.BinderNameHint
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Sum.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Tactic.Push
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertDblPar

theorem parD_fix : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T → ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')))
      (omd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) →* Module.End ℂ ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → AF F) → ℂ)),
      IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) G.M'.co dd →
      IsUWeilSplit (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) dd X.α (diagCols (Fin (a + a'))) omd →
    ∀ R : (Fin a' × Fin (a + a') → AF F) → ℂ, R 0 ≠ 0 → Rest (evFin F v) (G.M'.vac v) R →
    ∀ p ∈ GlobalTheory.InertDbl.ParD σ G.W v, omd p (GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R)) =
      GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w hin hT dd omd hdc hws R hR0 hRv p hp
  set Ψ := tens (evFin F v) (G.M'.vac v) R with hΨdef
  have hΨ : Ψ ∈ schA F _ := hRv.2
  have hΦ : GlobalTheory.InertDbl.dblFun Ψ ∈ schA F _ :=
    GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ Ψ hΨ _ (GlobalTheory.star_mem_schA_main _ Ψ hΨ)
  have hV := hTr.geo.hM'.vac v
  obtain ⟨y, hy⟩ : ∃ y, G.M'.vac v y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hV.2.1 (funext h)
  have hΨne : Ψ ≠ 0 := by
    intro h0
    let x : Fin a' × Fin (a + a') → AF F := fun i => GlobalTheory.LatVac.liftV v (y i)
    have hRx : R x = R 0 := by
      have := hRv.1 0 x (fun u hu => by funext i; exact GlobalTheory.LatVac.at_liftV v _ u hu)
      simpa using this
    have h1 := congrFun h0 x
    simp only [hΨdef, tens, x, GlobalTheory.LatVac.evFin_liftV, hRx, Pi.zero_apply] at h1
    exact mul_ne_zero hy hR0 h1
  obtain ⟨c, hc⟩ := GlobalTheory.T.inertPlace_doubledUnitary_vacuumTensor_eigen F E σ B a a' G X om om' hTr v w hin dd omd hdc hws R hRv p hp.1
  obtain ⟨l, hl, hinv, hl0⟩ := GlobalTheory.T.exists_translationInvariant_doubledForm_conjProduct_ne_zero F _ Ψ hΨ hΨne
  obtain ⟨t, ht⟩ := hp.2
  have hS := hws.2.2 l hl (fun z φ hφ => hinv φ hφ _ _ (GlobalTheory.WeilM.SiegelModel.rho_diag B.ψ hdc z φ)) p t ht _ hΦ
  have htp := GlobalTheory.T.doubledSiegelParabolic_diagonal_action_integral F E σ G.W v p hp t ht
  have ha := GlobalTheory.T.comparisonCharacter_det_eq_one_inertPlace F E σ B a a' G X om om' hTr v w hin hT t htp
  have hb := GlobalTheory.T.local_theta_integral_at_inert_place F E σ B a a' G X om om' hTr v w hin hT t htp
  rw [ha, hb] at hS
  rw [hc, map_smul, smul_eq_mul] at hS
  simp only [Circle.coe_one, NNReal.coe_one, Real.one_rpow, Complex.ofReal_one, one_mul] at hS
  have h1 : c = 1 := (mul_eq_right₀ hl0).mp hS
  rw [hc, h1, one_smul]

end GlobalTheory.InertDblPar

end
