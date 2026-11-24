module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaussianDatumFlippedFiniteTensorBigRoute
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenPtSubset
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLagrModelOfIsLin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finsupp.Single
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

noncomputable section

namespace GlobalTheory.FlipVac

theorem exists_gauss_vac : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G) (hst : SquareStanding G t) (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X), IsTriple Bs Γ X om om' → IsTied t i j e Bs Γ X →
    ∃ f₀, f₀ ≠ 0 ∧ Γ.M.IsGauss Bs.ψ Bs.emb f₀ ∧
      IsDatumA (t := t) W e Γ (Finsupp.single (((), ρ.vX i (j + 1)), ρ.vT (i + 1) j) 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ Γ.M.vac) := by
  intro D T L sc G μ₀ hL W ρ t i j M _ e Bs Γ X om om' h hT hti
  have h₁ := ρ.vX_is i (j + 1) i.2 j.2
  have h₂ := ρ.vT_is t (i + 1) j i.2 j.2
  have hG : Γ.M.IsGood W.ψ := h.ψ ▸ hT.geo.hM
  obtain ⟨f, hf⟩ := GlobalTheory.BigDat.exists_vac hL h hT hti h₁ h₂
  refine ⟨f, fun h0 => ?_, GlobalTheory.BigDat.isGauss (c := 1) h hT h₁ h₂ (by rw [hf, one_smul]),
    (isFinPart_vac hG ∅).fam.mem hG f, fun u => ?_⟩
  · obtain ⟨x, hx⟩ := Function.ne_iff.1 (GlobalTheory.BigDat.vac_ne_zero h₁)
    obtain ⟨y, hy⟩ := Function.ne_iff.1 (GlobalTheory.BigDat.vac_ne_zero h₂)
    have := congrFun hf (GlobalTheory.BigDat.ofMaps e (x, y))
    rw [h0, show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (0 : SInf D.host.F (GlobalTheory.BigDat.Ix G i j)) Γ.M.vac =
        (0 : ℂ) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure 0 Γ.M.vac from funext fun _ => (zero_mul _).trans (zero_mul _).symm,
      GlobalTheory.BigDat.thetaPt_smul, zero_mul, GlobalTheory.BigDat.box, GlobalTheory.BigDat.mapV_ofMaps, GlobalTheory.BigDat.mapW_ofMaps] at this
    exact mul_ne_zero hx hy this.symm
  · refine (congrFun hf u).trans ?_
    first
    | exact (one_mul _).symm.trans (Finsupp.sum_single_index (h := fun d (c : ℂ) => c * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.boxA e d u) (zero_mul _)).symm
    | (erw [Finsupp.sum_single_index (by exact zero_mul _), one_mul]; rfl)
    | (simp only [Finsupp.sum_single_index, zero_mul, one_mul]; rfl)

end GlobalTheory.FlipVac

end
