module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSobolevBoundThetaPointwise
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.SobContId
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
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
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Lattice.Nat
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.UniformConvergence

@[expose] public section

open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

noncomputable section

namespace GlobalTheory.ThetaDensCauchy

open GlobalTheory.Size

section

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem word_add (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool))
    {f f' : WO S T → ℂ} (h : IsThetaFunO ψ S T f) (h' : IsThetaFunO ψ S T f') :
    GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (f + f') =
      GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l f + GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l f' := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [GlobalTheory.Size.wordAct_cons, ih]
    exact GlobalTheory.Size.dRho_add hψ hθ a.1 _ (GlobalTheory.Size.theta_word hψ hθ l h) (GlobalTheory.Size.theta_word hψ hθ l h')

theorem word_mem (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool))
    {U : AddSubgroup (WO S T)} {f : WO S T → ℂ} (h : f ∈ thetaLevel ψ S T U) :
    GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l f ∈ thetaLevel ψ S T U := by
  induction l with
  | nil => exact h
  | cons a l ih =>
    rw [GlobalTheory.Size.wordAct_cons]
    exact GlobalTheory.Size.dRho_mem_thetaLevel hψ hθ ih a.1 _

theorem sobO_word_le (μ : Measure (WO S T)) (𝓕 : Set (WO S T))
    (l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool)) (f : WO S T → ℂ) (d : ℕ) :
    sobO ψ θ μ 𝓕 d (GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l f) ≤ sobO ψ θ μ 𝓕 (d + l.length) f := by
  induction l generalizing d with
  | nil => exact le_rfl
  | cons a l ih =>
    rw [GlobalTheory.Size.wordAct_cons]
    refine (GlobalTheory.Size.sobO_heisDer_le d a).trans ((ih (d + 1)).trans (le_of_eq ?_))
    congr 1
    simp only [List.length_cons]
    omega

end

theorem uniformCauchySeqOn_word : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ S T : HSp D, ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∀ u : ℕ → WO S T → ℂ, (∀ j, u j ∈ thetaLevel ψ S T U) → (∀ d, ∀ ε : ℝ≥0∞, 0 < ε → ∃ J, ∀ i ≥ J, ∀ j ≥ J, sobO ψ θ μ 𝓕 d (u i - u j) < ε) → ∀ l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool), UniformCauchySeqOn (fun j => GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (u j)) Filter.atTop Set.univ := by
  intro D ψ hψ θ hθ S T μ 𝓕 hm U hU u hu hC l
  obtain ⟨d₀, C, hb⟩ := GlobalTheory.ThetaDensSup.sup_le_sobO D ψ hψ θ hθ S T μ 𝓕 hm U hU
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  have hη : (0 : ℝ) < ε / (C + 1) := by positivity
  obtain ⟨J, hJ⟩ := hC (d₀ + l.length) (ENNReal.ofReal (ε / (C + 1))) (ENNReal.ofReal_pos.2 hη)
  refine ⟨J, fun i hi j hj w _ => ?_⟩
  have hd : u i - u j ∈ thetaLevel ψ S T U := Submodule.sub_mem _ (hu i) (hu j)
  have he := word_add hψ hθ l hd.1 (hu j).1
  rw [sub_add_cancel] at he
  have h1 := (hb _ (word_mem hψ hθ l hd) w).trans
    (mul_le_mul_right ((sobO_word_le μ 𝓕 l _ d₀).trans (hJ i hi j hj).le) _)
  rw [dist_eq_norm, he, Pi.add_apply, add_sub_cancel_right]
  rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul C.coe_nonneg,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
  refine h1.trans_lt ?_
  rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
  nlinarith

end GlobalTheory.ThetaDensCauchy
