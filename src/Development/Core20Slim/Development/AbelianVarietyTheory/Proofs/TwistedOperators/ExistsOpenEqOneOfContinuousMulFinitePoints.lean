module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepLatticeStabilizerVacuumEqDetCharSmul
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HomSymplecticHalfFormAlgebraicLawsContinuous
public import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonarchimedeanGroupOfIsCompactIsOpen
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OpenKer

open GlobalTheory.AdelicU Filter Topology

theorem eq_one_on_finite_of_mul : ∀ {D : D7} (T : HSp D) (K : Subgroup (GA D T)), IsOpen (K : Set (GA D T)) → ∀ F : GA D T → ℂ, Continuous F → F 1 = 1 → (∀ a ∈ K, a ∈ GfC T → ∀ b ∈ K, b ∈ GfC T → F (a * b) = F a * F b) → ∃ U : Subgroup (GA D T), IsOpen (U : Set (GA D T)) ∧ ∀ k ∈ U, k ∈ GfC T → F k = 1 := by
  intro D T K hK F hF h1 hmul
  haveI := GlobalTheory.Doubling.nonarchimedeanGroup_GFin D.sp.cm.sig T.gram
  have hc := continuous_ofFin D.sp.cm.sig T.gram
  have hN : {y | ‖F (ofFin D.sp.cm.sig T.gram y) - 1‖ < 1 / 2} ∈ 𝓝 (1 : GFin D.sp.cm.sig T.gram) :=
    (isOpen_lt (continuous_norm.comp ((hF.comp hc).sub continuous_const)) continuous_const).mem_nhds
      (by simp [h1])
  have hK' : {y | ofFin D.sp.cm.sig T.gram y ∈ K} ∈ 𝓝 (1 : GFin D.sp.cm.sig T.gram) :=
    (hK.preimage hc).mem_nhds (by simp [one_mem])
  obtain ⟨W, hW⟩ := NonarchimedeanGroup.is_nonarchimedean _ (inter_mem hN hK')
  refine ⟨W.toSubgroup.comap (projFin D.sp.cm.sig T.gram),
    W.isOpen.preimage (continuous_projFin D.sp.cm.sig T.gram), ?_⟩
  intro k hk hkf
  have hkk : ∀ n : ℕ, ofFin D.sp.cm.sig T.gram (projFin D.sp.cm.sig T.gram (k ^ n)) = k ^ n := fun n => by
    have h := ofInf_projInf_mul_ofFin_projFin D.sp.cm.sig T.gram (k ^ n)
    rwa [mem_finPts.1 (pow_mem hkf n), map_one, one_mul] at h
  have hW' : ∀ n : ℕ, ‖F (k ^ n) - 1‖ < 1 / 2 ∧ k ^ n ∈ K := fun n => by
    have : projFin D.sp.cm.sig T.gram (k ^ n) ∈ W := by
      rw [map_pow]; exact pow_mem (show projFin D.sp.cm.sig T.gram k ∈ W from hk) n
    have h := hW this
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, hkk n] at h
    exact h
  have hpow : ∀ n : ℕ, F (k ^ n) = F k ^ n := fun n => by
    induction n with
    | zero => simp [h1]
    | succ n ih =>
      rw [pow_succ, hmul _ (hW' n).2 (pow_mem hkf n) _ (by simpa using (hW' 1).2) hkf, ih, pow_succ]
  exact GlobalTheory.Doubling.eq_one_of_forall_norm_pow_sub_one_le fun m => by
    rw [← hpow]; exact (hW' m).1.le

end GlobalTheory.OpenKer
