module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsNhdsZeroPrincipalEqZero
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Rat
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Map
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.IndefR.DatumF

namespace GlobalTheory.AdelicMatrixLatticeF

theorem lattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (nS nT : ℕ),
    IsTopologicalAddGroup (WOF F E nS nT) ∧ LocallyCompactSpace (WOF F E nS nT) ∧
    SecondCountableTopology (WOF F E nS nT) ∧ T2Space (WOF F E nS nT) ∧ DiscreteTopology (ratLF F E nS nT) ∧
    ∃ K : Set (WOF F E nS nT), IsCompact K ∧ ∀ x : WOF F E nS nT, ∃ γ ∈ ratLF F E nS nT, γ + x ∈ K := by
  intro F E _ _ _ _ _ nS nT
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele _
  have : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele _
  have : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField _
  have : IsModuleTopology (AF F) (AEF F E) := ⟨rfl⟩
  have : IsTopologicalRing (AEF F E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  have : LocallyCompactSpace (AEF F E) := e.isClosedEmbedding.locallyCompactSpace
  have : SecondCountableTopology (AEF F E) := e.secondCountableTopology
  have : T2Space (AEF F E) := e.isEmbedding.t2Space
  have hg : IsTopologicalAddGroup (WOF F E nS nT) :=
    inferInstanceAs (IsTopologicalAddGroup (Fin nT → Fin nS → AEF F E))
  refine ⟨hg, inferInstanceAs (LocallyCompactSpace (Fin nT → Fin nS → AEF F E)),
    inferInstanceAs (SecondCountableTopology (Fin nT → Fin nS → AEF F E)),
    inferInstanceAs (T2Space (Fin nT → Fin nS → AEF F E)), ?_, ?_⟩
  · obtain ⟨U, hU, hx⟩ := GlobalTheory.AdelicMatrixLattice.discrete_tensor (F := F) (E := E) (AF F)
      (GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F)
    have hN : (Set.univ.pi fun _ : Fin nT => Set.univ.pi fun _ : Fin nS => U) ∈
        nhds (0 : WOF F E nS nT) :=
      set_pi_mem_nhds Set.finite_univ fun _ _ => set_pi_mem_nhds Set.finite_univ fun _ _ => hU
    refine discreteTopology_of_isOpen_singleton_zero ?_
    rw [isOpen_singleton_iff_nhds_eq_pure]
    refine le_antisymm (Filter.le_pure_iff.2 ?_) (pure_le_nhds _)
    have hc : ContinuousAt (fun x : ratLF F E nS nT => (x : WOF F E nS nT)) 0 :=
      continuous_subtype_val.continuousAt
    refine Filter.mem_of_superset (hc.preimage_mem_nhds hN) ?_
    rintro ⟨_, y, rfl⟩ hy
    have hy0 : y = 0 := by
      funext i j
      exact hx _ (hy i (Set.mem_univ i) j (Set.mem_univ j))
    subst hy0
    exact Subtype.ext (map_zero _)
  · obtain ⟨K, hK, hx⟩ := GlobalTheory.AdelicMatrixLattice.cocompact_tensor (F := F) (E := E) (AF F)
      (GlobalTheory.AdeleCocompact.exists_compact_adele F)
    choose c hc using hx
    refine ⟨Set.univ.pi fun _ : Fin nT => Set.univ.pi fun _ : Fin nS => K,
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hK, fun x => ?_⟩
    exact ⟨_, ⟨Matrix.of fun i j => c (x i j), rfl⟩, fun i _ j _ => hc (x i j)⟩

end GlobalTheory.AdelicMatrixLatticeF
