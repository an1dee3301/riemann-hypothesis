module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjInvariantCharacterMem
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter

@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK 

namespace GlobalTheory.AdeleCocompactExt

theorem exists_compact_adele_ext : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∃ C : Set (AE F E), IsCompact C ∧ ∀ a : AE F E, ∃ α : E, a - inclR (F := F) (AF F) α ∈ C := by
  intro F E _ _ _ _ _
  classical
  haveI : IsModuleTopology (AF F) (AE F E) := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.modTop
  haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) (AE F E)
  haveI : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul (AF F) (AE F E)
  obtain ⟨K, hK, hK'⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele F
  let b := Module.finBasis F E
  let B : Module.Basis (Fin (Module.finrank F E)) (AF F) (AE F E) := Algebra.TensorProduct.basis (AF F) b
  let φ : (Fin (Module.finrank F E) → AF F) → AE F E := fun c => ∑ i, c i • B i
  have hφ : Continuous φ := continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const
  refine ⟨φ '' Set.univ.pi (fun _ => K), (isCompact_univ_pi fun _ => hK).image hφ, fun a => ?_⟩
  choose x hx using fun i => hK' (B.repr a i)
  refine ⟨∑ i, x i • b i, fun i => B.repr a i - algebraMap F (AF F) (x i), fun i _ => hx i, ?_⟩
  have hB : ∀ i, B i = (1 : AF F) ⊗ₜ[F] b i := fun i => Algebra.TensorProduct.basis_apply _ _
  have hincl : inclR (F := F) (AF F) (∑ i, x i • b i) = ∑ i, algebraMap F (AF F) (x i) • B i := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sum, map_smul,
      Algebra.TensorProduct.includeRight_apply, hB, algebraMap_smul]
  simp only [φ, sub_smul, Finset.sum_sub_distrib, hincl]
  rw [B.sum_repr a]

end GlobalTheory.AdeleCocompactExt
