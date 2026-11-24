module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepSourceLineEqOppositeTargetLineStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaTensorRuleOrthogonalSumSourceStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaTensorRuleTargetOrthogonalSumStatement
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConjugateAdjointDagger
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Formalism.LocalRingCardinality.DataHost
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
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.SeeLastPf

theorem ofAdj_zero (D : D7) (L S : HSp D) : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S 0 = 0 := by
  simp [GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj]

theorem seeLast : ∀ D : D7, SeeLast D := by
  intro D ψ V₀ A L S X T L'' o o'' τ hL hL'' hτ χA χz χS χS' χT om₁ oma omz omX omT omz'' h₁ ha hz hX hT hz'' Ξ Φ₂ hΞ hΦ₂
  have hψ : IsStdChar D ψ (-1) := h₁.std
  have hsrc := GlobalTheory.T.thetaTensorRule_orthogonalSum_source D ψ hψ V₀ A L o S
  have htgt := GlobalTheory.T.thetaTensorRule_targetOrthogonalSum D ψ hψ X T L'' o'' S
  have hτ' : τᴴ ⬝ (L.gram ⬝ τ) = (((-1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L''.gram := by
    rw [hτ]; simp
  have hrk : L.rank = L''.rank := hL.trans hL''.symm
  have hline := fun u => GlobalTheory.T.weilRep_sourceLine_eq_opposite_targetLine D ψ L L'' S τ hrk hτ' χz χS χS' omz omz'' hz hz''
    (fun v => Ξ ((o.resS S).symm (u, v))) ((hsrc.slice_theta Ξ hΞ).2 u)
  refine ⟨fun u => (hline u).1, ?_⟩
  intro h₀ h h'
  have e1 : ∀ u, omX (h, o''.emb (h', 1)) (o''.boxT S Φ₂ fun w => Ξ ((o.resS S).symm
      (u, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L''.rank) ⬝ w)))) 0 =
      omT (h, h') Φ₂ 0 * omz (1, h) (fun v => Ξ ((o.resS S).symm (u, v))) 0 := by
    intro u
    rw [htgt.om_box χS' χT χz⁻¹ omX omT omz'' hX hT hz'' h h' 1 Φ₂ _ hΦ₂ (hline u).1, htgt.box_zero,
      (hline u).2 h]
    beta_reduce
    congr 1
    exact congrArg (omz (1, h) (fun v => Ξ ((o.resS S).symm (u, v))))
      ((congrArg (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S) (Matrix.mul_zero _)).trans (ofAdj_zero D L S))
  have e2 := (hsrc.om_slice χA χz χS om₁ oma omz h₁ ha hz h₀ 1 h Ξ hΞ 0).2 0
  have e0 : (o.resS S).symm (0, 0) = 0 := by
    rw [← Prod.zero_eq_mk, map_zero]
  rw [e0] at e2
  simp only [e1]
  rw [e2]
  have : (fun u => omT (h, h') Φ₂ 0 * omz (1, h) (fun v => Ξ ((o.resS S).symm (u, v))) 0) =
      omT (h, h') Φ₂ 0 • (fun u' => omz (1, h) (fun v' => Ξ ((o.resS S).symm (u', v'))) 0) := by
    funext u; simp
  rw [this, map_smul]
  simp

end GlobalTheory.SeeLastPf

end
