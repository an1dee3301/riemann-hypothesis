module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpDiv
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsPairReading
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffOfContinuousOneParameter
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sets
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.ArchCancel

theorem eq_of_tens_eq : ∀ (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] (r : (κ → AF F) → ℂ),
    (∀ x z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) z → r (x + z) = r x) → (∃ x, r x ≠ 0) →
    ∀ f₁ f₂ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f₁ r = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f₂ r → f₁ = f₂ := by
  intro F _ _ κ _ r hr hne f₁ f₂ h
  obtain ⟨x₀, hx₀⟩ := hne
  refine DFunLike.ext f₁ f₂ fun y => ?_
  let z : κ → AF F := fun i =>
    ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i - GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (x₀ i)), 0)
  have hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) z := by
    intro u hu
    funext i
    have hu1 : u.1 = 0 := by
      have : InfiniteAdeleRing.ringEquiv_mixedSpace F u.1 = 0 := hu
      exact (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).mp this
    show u * z i = 0
    refine Prod.ext ?_ ?_
    · show u.1 * (z i).1 = 0
      rw [hu1, zero_mul]
    · show u.2 * (z i).2 = 0
      show u.2 * 0 = 0
      rw [mul_zero]
  have hev : (fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F ((x₀ + z) i)) = y := by
    funext i
    show InfiniteAdeleRing.ringEquiv_mixedSpace F ((x₀ i).1 +
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i - GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (x₀ i))) = y i
    rw [map_add (f := _), RingEquiv.apply_symm_apply]
    show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (x₀ i) + (y i - GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (x₀ i)) = y i
    exact add_sub_cancel _ _
  have h2 := congrFun h (x₀ + z)
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens] at h2
  rw [hev, hr x₀ z hz] at h2
  exact mul_right_cancel₀ hx₀ h2

end GlobalTheory.ArchCancel
