module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.WhitKAOfGenLt
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
public import Development.Core20Slim.Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.SiegelWeilUnitarySchrodingerLit
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionUnitary
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine
public import Development.AbelianVarietyTheory.Definitions.Foundations.AnalyticOnNhdTsumNpow
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.LinearMap
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
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.Lattice.Nat
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.CompanionTheory.AnisoRange

theorem bddAbove_isotropic_dims {D : D7} (V : HSp D) :
    BddAbove {k | ∃ W : Submodule D.host.E V.V, Module.finrank D.host.E W = k ∧ ∀ x ∈ W, ∀ y ∈ W, V.hT x y = 0} := by
  haveI := V.fd
  refine ⟨Module.finrank D.host.E V.V, ?_⟩
  rintro k ⟨W, rfl, -⟩
  exact Submodule.finrank_le W

theorem one_le_wittIdx {D : D7} (V : HSp D) {v : V.V} (hv : v ≠ 0) (h : V.hT v v = 0) :
    1 ≤ Formalism.MainNotions.SchurIrreducible.wittIdx V := by
  refine le_csSup (bddAbove_isotropic_dims V) ⟨Submodule.span D.host.E {v}, finrank_span_singleton hv, ?_⟩
  intro x hx y hy
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hy
  simp [h]

theorem hT_coord {D : D7} (V : HSp D) (x : Fin V.rank → D.host.E) :
    V.hT (V.frame.equivFun.symm x) (V.frame.equivFun.symm x) =
      HeckeCharacterZeroLocus.SiegelWeilU.hE D.sp.cm.sig (HSpace.gram V) x x := by
  have hσ : ∀ a : D.host.E, ((D.sp.cm.sig : D.host.E →ₐ[D.host.F] D.host.E) : D.host.E →+* D.host.E) a = star a :=
    fun _ => rfl
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Module.Basis.equivFun_symm_apply, HeckeCharacterZeroLocus.SiegelWeilU.hE, HeckeCharacterZeroLocus.SiegelWeilU.hform, map_sum, LinearMap.sum_apply,
    map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hσ, HSpace.gram]
  simp only [starRingEnd_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RingHom.id_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem anisoOfRange : PositivityTheory.PfSWUS.AnisoOfRange := by
  rintro D n V ⟨h1, -, h3⟩
  by_cases h : n + 2 ≤ V.rank
  · exact Or.inl h
  refine Or.inr fun x hx => ?_
  by_contra hne
  have hv : V.frame.equivFun.symm x ≠ 0 := fun h0 => hne ((map_eq_zero_iff _ V.frame.equivFun.symm.injective).1 h0)
  have := one_le_wittIdx V hv ((hT_coord V x).trans hx)
  omega

end GlobalTheory.CompanionTheory.AnisoRange
