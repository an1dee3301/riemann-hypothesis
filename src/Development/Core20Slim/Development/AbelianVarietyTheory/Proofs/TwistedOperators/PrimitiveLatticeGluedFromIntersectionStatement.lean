module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrimitiveLatticeGluedFromIntersection
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FlatSpaceComponents
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.Lattice.Basic
public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Finiteness.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_lattice_glued_from_intersection : ∀ (D : D7) (u : D.what₂.Word) (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V), IsLine Y X ι z u → ∀ L, IsSDIn Y (flatSp Y X ι z) L → IsPrim Y z L → Submodule.IsFullLattice D.host.E (capX Y X ι L) ∧ ∃ x₀ : X.V, L = glueLat Y X ι z u (capX Y X ι L) x₀ := by
  intro D u Y X ι z hl L hL hp
  obtain ⟨hlat, hglue⟩ := GlobalTheory.AdIsom.Unglue.isLattice_capX_and_exists_glue D u Y X ι z hl L hL hp
  refine ⟨{ toIsLattice := by first | exact hlat | exact hlat.toIsLattice, span_eq_top := ?_ }, hglue⟩
  apply Submodule.eq_top_iff'.2
  intro y
  let x := (Formalism.L2.Herm.crd X).symm y
  have hx : ι x ∈ Submodule.span D.host.E (L : Set Y.V) := by
    rw [hL.2.1]
    exact Submodule.mem_sup_left (LinearMap.mem_range_self ι x)
  obtain ⟨c, hc, hcx⟩ := GlobalTheory.AdIsom.Unglue.exists_smul_mem L hx
  have hcy : c • y ∈ capX Y X ι L := by
    change c • y ∈ Formalism.L2.Herm.crdLat X (L.comap (ι.restrictScalars (𝓞 D.host.E)))
    refine ⟨c • x, ?_, ?_⟩
    · change ι (c • x) ∈ L
      simpa using hcx
    · simp [x]
  have hcy' : c • y ∈ Submodule.span D.host.E (capX Y X ι L : Set (Fin X.rank → D.host.E)) :=
    Submodule.subset_span hcy
  rw [← algebraMap_smul D.host.E c] at hcy'
  have h := (Submodule.span D.host.E (capX Y X ι L : Set (Fin X.rank → D.host.E))).smul_mem
    (c : D.host.E)⁻¹ hcy'
  simpa only [smul_smul, inv_mul_cancel₀ (RingOfIntegers.coe_ne_zero_iff.2 hc), one_smul] using h
