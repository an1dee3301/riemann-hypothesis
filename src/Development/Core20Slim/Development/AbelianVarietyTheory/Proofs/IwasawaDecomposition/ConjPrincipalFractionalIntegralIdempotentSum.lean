module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalRingCardinality.DataExtra
public import Formalism.LocalRingCardinality.DataTies
public import Development.Core20Slim.ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatA
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimeDvdAbsNormHalfDifferent
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.IdemIntegral

theorem toEAf_mem_of_finPart {D : D7} {w : AE D} (hw : finPart D w ∈ intAE D) :
    toEAf D w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  have key : ∀ z ∈ intAE D, Algebra.TensorProduct.comm D.host.F (Formalism.L2.Herm.Af D.host.F) D.host.E z ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, rfl⟩ := hz
      have h1 : (1 : D.host.E) ⊗ₜ[D.host.F] a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
        Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)
      have h2 : (x : D.host.E) ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
        Subring.subset_closure (Or.inl ⟨⟨_, x, rfl⟩, rfl⟩)
      have h3 := mul_mem h2 h1
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one] at h3
      exact h3
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | neg x _ hx => rw [map_neg]; exact neg_mem hx
  exact key _ hw

theorem toEAf_incA (D : D7) (x : D.host.E) : toEAf D (incA D x) = eToEAf D x := rfl

theorem eToEAf_int (D : D7) (x : 𝓞 D.host.E) :
    eToEAf D (x : D.host.E) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
  Subring.subset_closure (Or.inl ⟨⟨_, x, rfl⟩, rfl⟩)



end GlobalTheory.IdemIntegral
