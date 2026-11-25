module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitProjAdeleComponentChartProperties
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
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
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SplitFrameColumn




theorem latHat_iff_hatL {D : D7} {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (z : Fin n → Af D.host.F ⊗[D.host.F] D.host.E) :
    z ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (Λ : Set (Fin n → D.host.E)) ↔
      (fun i => Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (z i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hz
      exact GlobalTheory.AdelicLatMove.pure_mem_hatL Λ a (fun w => ha w) x hx
    | zero => simp only [Pi.zero_apply, map_zero]; exact zero_mem _
    | add x y _ _ hx hy => simp only [Pi.add_apply, map_add (f := _)]; exact add_mem hx hy
    | neg x _ hx => simp only [Pi.neg_apply, map_neg]; exact neg_mem hx
  · intro hz
    have key : ∀ w ∈ AddSubgroup.closure (GlobalTheory.AdelicLatMove.pureSet (D := D) Λ),
        (fun i => (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm (w i)) ∈
          Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (Λ : Set (Fin n → D.host.E)) := by
      intro w hw
      induction hw using AddSubgroup.closure_induction with
      | mem w hw =>
        obtain ⟨α, hα, x, hx, rfl⟩ := hw
        exact AddSubgroup.subset_closure ⟨α, fun u => hα u, x, hx, rfl⟩
      | zero => simp only [Pi.zero_apply, map_zero]; exact zero_mem _
      | add x y _ _ hx hy => simp only [Pi.add_apply, map_add (f := _)]; exact add_mem hx hy
      | neg x _ hx => simp only [Pi.neg_apply, map_neg]; exact neg_mem hx
    have := key _ (GlobalTheory.AdelicLatMove.mem_closure_of_mem_hatL Λ _ hz)
    simpa only [AlgEquiv.symm_apply_apply] using this


end GlobalTheory.SplitFrameColumn
