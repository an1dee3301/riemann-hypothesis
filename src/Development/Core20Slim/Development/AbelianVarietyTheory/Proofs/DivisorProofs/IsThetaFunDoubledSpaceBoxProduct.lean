module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActOOneOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsGLSubmatrix
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
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
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
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
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Notation
public import Mathlib.Order.TypeTags
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Star
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)
open Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasMat GlobalTheory.SplitWeil.matrixMeasurableSpace

namespace GlobalTheory.DblBoxTheta

open GlobalTheory.DblBox

theorem isThetaFunO_box : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (f₁ f₂ : Formalism.IndefR.Datum.WO S T → ℂ),
    Formalism.IndefR.Datum.IsThetaFunO ψ S T f₁ → Formalism.IndefR.Datum.IsThetaFunO ψ S T f₂ →
      Formalism.IndefR.Datum.IsThetaFunO ψ S (GlobalTheory.Doubling.dblSp T) (GlobalTheory.DblBox.box f₁ f₂) := by
  intro D ψ hψ S T f₁ f₂ h₁ h₂
  have ctop : Continuous (top : WO S (GlobalTheory.Doubling.dblSp T) → WO S T) :=
    continuous_id.matrix_submatrix _ _
  have cbot : Continuous (bot : WO S (GlobalTheory.Doubling.dblSp T) → WO S T) :=
    continuous_id.matrix_submatrix _ _
  let topH : WO S (GlobalTheory.Doubling.dblSp T) →+ WO S T := AddMonoidHom.mk' top top_add
  let botH : WO S (GlobalTheory.Doubling.dblSp T) →+ WO S T := AddMonoidHom.mk' bot bot_add
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro γ w
    have e₁ : top (ratW (GlobalTheory.Doubling.dblSp T) S γ) = ratW T S (γ.submatrix (finSumFinEquiv ∘ Sum.inl) id) := rfl
    have e₂ : bot (ratW (GlobalTheory.Doubling.dblSp T) S γ) = ratW T S (γ.submatrix (finSumFinEquiv ∘ Sum.inr) id) := rfl
    simp only [box, top_add, bot_add, symplOH_dbl]
    rw [e₁, e₂, h₁.quasi, h₂.quasi]
    rw [sub_eq_add_neg, neg_add, AddChar.map_add_eq_mul, neg_neg]
    simp only [psi_neg hψ, star_mul', star_star]
    ring
  · obtain ⟨U₁, hU₁o, hU₁⟩ := h₁.level
    obtain ⟨U₂, hU₂o, hU₂⟩ := h₂.level
    refine ⟨U₁.comap topH ⊓ U₂.comap botH, ?_, ?_⟩
    · exact (hU₁o.preimage ctop).inter (hU₂o.preimage cbot)
    · intro u hu hinf
      have hu₁ : top u ∈ U₁ := hu.1
      have hu₂ : bot u ∈ U₂ := hu.2
      have ht : (top u).map (infPart D) = 0 := by
        ext i j
        exact congrFun (congrFun hinf (finSumFinEquiv (Sum.inl i))) j
      have hb : (bot u).map (infPart D) = 0 := by
        ext i j
        exact congrFun (congrFun hinf (finSumFinEquiv (Sum.inr i))) j
      rw [heisO_box hψ, hU₁ _ hu₁ ht, hU₂ _ hu₂ hb]
  · exact (h₁.cont.comp ctop).mul ((h₂.cont.comp cbot).star)
  · intro k L hL hfin w
    have hf₁ :=
      h₁.smooth k (topH.comp L) (ctop.comp hL) (fun t => by
        ext i j
        exact congrFun (congrFun (hfin t) (finSumFinEquiv (Sum.inl i))) j) (top w)
    have hf₂ :=
      h₂.smooth k (botH.comp L) (cbot.comp hL) (fun t => by
        ext i j
        exact congrFun (congrFun (hfin t) (finSumFinEquiv (Sum.inr i))) j) (bot w)
    exact ContDiff.mul hf₁ (Complex.conjCLE.contDiff.comp hf₂)

end GlobalTheory.DblBoxTheta
