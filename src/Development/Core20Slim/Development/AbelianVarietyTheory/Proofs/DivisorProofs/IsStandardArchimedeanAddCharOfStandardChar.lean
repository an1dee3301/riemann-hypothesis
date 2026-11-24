module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryPartnerDiagStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnOfLocal
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleJoinZero
public import Development.Core20Slim.Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCB
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.WeilL2Words.StdTheta

def negSum (F : Type) [Field F] [NumberField F] : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ :=
  -(∑ w : {w : InfinitePlace F // w.IsReal}, (LinearMap.proj w).comp (LinearMap.fst ℝ _ _))

theorem negSum_apply (F : Type) [Field F] [NumberField F] (z : mixedEmbedding.mixedSpace F) :
    negSum F z = -∑ w, z.1 w := by
  simp [negSum]

theorem negSum_nondeg (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (z : mixedEmbedding.mixedSpace F)
    (hz : z ≠ 0) : ∃ u, negSum F (z * u) ≠ 0 := by
  have h1 : z.1 ≠ 0 := by
    intro h0
    apply hz
    refine Prod.ext h0 (funext fun w => absurd (IsTotallyReal.isReal w.1) ?_)
    exact InfinitePlace.not_isReal_iff_isComplex.2 w.2
  obtain ⟨w, hw⟩ := Function.ne_iff.1 h1
  refine ⟨(Pi.single w 1, 0), ?_⟩
  rw [negSum_apply]
  simpa [Pi.single_apply] using hw

theorem cmTypeComponents_sum_eq_realCoordinates_sum (D : D7) (x : Ainf D.host.F) :
    ∑ ρ, Formalism.L2.Fam.ThC.th0 D ρ (x ⊗ₜ[D.host.F] (1 : D.host.E)) =
      ((∑ w, (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F x).1 w : ℝ) : ℂ) := by
  haveI := D.sp.cm.totReal
  have e1 : ∀ ρ, Formalism.L2.Fam.ThC.th0 D ρ (x ⊗ₜ[D.host.F] (1 : D.host.E)) =
      InfinitePlace.Completion.extensionEmbedding (GlobalTheory.AdelicU.placeOf D ρ) (x (GlobalTheory.AdelicU.placeOf D ρ)) := by
    intro ρ
    show Formalism.L2.Fam.ThC.projAt (tauE D ρ) (x ⊗ₜ[D.host.F] (1 : D.host.E)) = _
    rw [Formalism.L2.Fam.ThC.projAt_tmul, map_one, mul_one]
    rfl
  rw [Finset.sum_congr rfl fun ρ _ => e1 ρ,
    (GlobalTheory.AdelicU.placeOf_bijective D).sum_comp (fun w => InfinitePlace.Completion.extensionEmbedding w (x w)),
    Complex.ofReal_sum]
  refine (Fintype.sum_equiv (Equiv.subtypeUnivEquiv fun w : InfinitePlace D.host.F => IsTotallyReal.isReal w) _ _
    fun w => ?_).symm
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  exact InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply w.2 (x w.1)

theorem isStdInf_of_isStdChar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    GlobalTheory.WeilL2Words.IsStdInf D.host.F ψ := by
  intro D ψ hψ
  haveI := D.sp.cm.totReal
  have h := Formalism.L2.Fam.ThC.allSome_fam.1 hψ.2
  refine ⟨negSum D.host.F, negSum_nondeg D.host.F, fun z => ?_⟩
  have hx := h ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm z)
  rw [cmTypeComponents_sum_eq_realCoordinates_sum, RingEquiv.apply_symm_apply] at hx
  show psiInf D.host.F ψ ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm z) = _
  rw [hx, negSum_apply]
  congr 1
  push_cast
  ring

end GlobalTheory.WeilL2Words.StdTheta
