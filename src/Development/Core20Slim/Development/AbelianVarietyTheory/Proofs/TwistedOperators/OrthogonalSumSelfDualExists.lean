module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsGLSubmatrix
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAHEqOfMemRatPts
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemSiegelOfIffRightAct
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Action.Prod
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.Lattice.Basic
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio
open GlobalTheory.Doubling GlobalTheory.AdelicU

namespace GlobalTheory.Twist.OrthSum

variable {D : D7}

theorem pair_hsum (V W : HSp D) (x y : Fin (hsum V W).rank → D.host.E) :
    ∑ i, ∑ j, star (x i) * (hsum V W).gram i j * y j =
      (∑ i, ∑ j, star (x (finSumFinEquiv (Sum.inl i))) * V.gram i j * y (finSumFinEquiv (Sum.inl j))) +
      ∑ i, ∑ j, star (x (finSumFinEquiv (Sum.inr i))) * W.gram i j * y (finSumFinEquiv (Sum.inr j)) := by
  rw [gram_hsum]
  simp only [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, Doubling.blkMat, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero,
    add_zero, zero_add]

theorem selfDual_hsum {V W : HSp D} {L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)} (hL : IsSelfDualC V L) (hL' : IsSelfDualC W L') :
    IsSelfDualC (hsum V W) (sumLat finSumFinEquiv L L') := by
  have hsumLat : Submodule.IsLattice D.host.E (sumLat finSumFinEquiv L L') := by
    let φ : ((Fin V.rank → D.host.E) × (Fin W.rank → D.host.E)) ≃ₗ[D.host.E]
        (Fin (V.rank + W.rank) → D.host.E) :=
      (LinearEquiv.sumArrowLequivProdArrow _ _ _ _).symm.trans
        (LinearEquiv.funCongrLeft _ _ finSumFinEquiv.symm)
    have e : sumLat finSumFinEquiv L L' =
        (L.prod L').map (φ.toLinearMap.restrictScalars (𝓞 D.host.E)) := by
      ext w
      refine ⟨fun hw => ⟨(_, _), hw, pairVec_eta _ w⟩, ?_⟩
      rintro ⟨x, hx, rfl⟩
      exact (pairVec_mem_sumLat _).2 hx
    exact Submodule.IsLattice.of_fg D.host.E (e ▸ (hL.1.fg.prod hL'.1.fg).map _)
  refine ⟨hsumLat, fun y => ⟨fun hy x hx => ?_, fun H => ?_⟩⟩
  · obtain ⟨b₁, hb₁⟩ := (hL.2 (fun i => y (finSumFinEquiv (Sum.inl i)))).1 hy.1
      (fun i => x (finSumFinEquiv (Sum.inl i))) hx.1
    obtain ⟨b₂, hb₂⟩ := (hL'.2 (fun i => y (finSumFinEquiv (Sum.inr i)))).1 hy.2
      (fun i => x (finSumFinEquiv (Sum.inr i))) hx.2
    refine ⟨b₁ + b₂, ?_⟩
    rw [pair_hsum]
    push_cast
    linear_combination hb₁ + hb₂
  · refine ⟨(hL.2 _).2 fun x hx => ?_, (hL'.2 _).2 fun x hx => ?_⟩
    · obtain ⟨b, hb⟩ := H (pairVec finSumFinEquiv x 0) ((pairVec_mem_sumLat _).2 ⟨hx, zero_mem _⟩)
      rw [pair_hsum] at hb
      simp only [pairVec_inl, pairVec_inr, Pi.zero_apply, star_zero, zero_mul, Finset.sum_const_zero, add_zero] at hb
      exact ⟨b, hb⟩
    · obtain ⟨b, hb⟩ := H (pairVec finSumFinEquiv 0 x) ((pairVec_mem_sumLat _).2 ⟨zero_mem _, hx⟩)
      rw [pair_hsum] at hb
      simp only [pairVec_inl, pairVec_inr, Pi.zero_apply, star_zero, zero_mul, Finset.sum_const_zero, zero_add] at hb
      exact ⟨b, hb⟩

end GlobalTheory.Twist.OrthSum

end
