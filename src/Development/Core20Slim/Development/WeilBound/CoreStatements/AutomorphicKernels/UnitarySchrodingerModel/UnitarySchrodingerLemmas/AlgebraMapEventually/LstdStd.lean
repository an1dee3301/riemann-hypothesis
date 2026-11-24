module

public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.FockLatticeHeights.HWDefs
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenOf
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.NDDefs
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Development.Core20Slim.GroundTheory.GlobalFields.CompletionAtPlace.Integers
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Finsupp.SMulWithZero
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Operations
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Finite
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open NumberField IsDedekindDomain GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

namespace PositivityTheory.PfSWUS.SwsLstd

open PositivityTheory.PfSWUS.SwFockk

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem isCO_lstd (n : ℕ) (v : HeightOneSpectrum (𝓞 F)) : PositivityTheory.SiegelWeilFormula.Gen.IsCO (lstd F E n v) := by
  obtain ⟨hc, ho⟩ := GlobalTheory.ThK.isCompact_isOpen_intLoc (F := F) (E := E) v
  have e : (lstd F E n v : Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) =
      Set.univ.pi fun _ => (GlobalTheory.AdelicU.intLoc F E v : Set (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) := by
    ext y
    simp only [Set.mem_univ_pi]
    rfl
  refine ⟨?_, ?_⟩
  · rw [e]; exact isOpen_set_pi Set.finite_univ fun _ _ => ho
  · rw [e]; exact isCompact_univ_pi fun _ => hc

theorem eventually_algebraMap_mem (c : F) :
    ∀ᶠ v in Filter.cofinite, algebraMap F (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) c ∈ v.adicCompletionIntegers F :=
  (FiniteAdeleRing.algebraMap (𝓞 F) F c).2

theorem eventually_mem_intLoc_iff {d : ℕ} (bs : Module.Basis (Fin d) F E) :
    ∀ᶠ v in Filter.cofinite, ∀ z : HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E, z ∈ GlobalTheory.AdelicU.intLoc F E v ↔
      ∀ k, (Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) bs).repr z k ∈ v.adicCompletionIntegers F := by
  classical
  have hint : ∀ y : E, ∃ m : ℤ, m ≠ 0 ∧ IsIntegral ℤ ((m : F) • y) := fun y => by
    obtain ⟨m, hm, hi⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2
      (Algebra.IsAlgebraic.isAlgebraic y)).exists_integral_multiple
    exact ⟨m, hm, by rwa [Int.cast_smul_eq_zsmul]⟩
  choose m hm hmi using hint
  let b := RingOfIntegers.basis E
  have h1 : ∀ᶠ v in Filter.cofinite, ∀ i k, algebraMap F (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v)
      (bs.repr ((b i : 𝓞 E) : E) k) ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun k => eventually_algebraMap_mem _
  have h2 : ∀ᶠ v in Filter.cofinite, ∀ k, algebraMap F (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) ((m (bs k) : F))⁻¹ ∈
      v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun k => eventually_algebraMap_mem _
  filter_upwards [h1, h2] with v hv1 hv2 z
  set B := Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) bs
  constructor
  · intro hz
    refine GlobalTheory.AdelicU.intLoc_induction (p := fun y => ∀ k, B.repr y k ∈ v.adicCompletionIntegers F)
      ?_ ?_ ?_ ?_ hz
    · intro a ha x k
      rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]
      refine mul_mem ha ?_
      have hx : (x : E) = ∑ i, (b.repr x i) • ((b i : 𝓞 E) : E) := by
        conv_lhs => rw [← b.sum_repr x]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_zsmul, RingOfIntegers.coe_eq_algebraMap]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hx, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply, map_sum]
      refine Subring.sum_mem _ fun i _ => ?_
      rw [map_zsmul, Finsupp.smul_apply, map_zsmul]
      exact zsmul_mem (hv1 i k) _
    · intro k; simp
    · intro y z hy hz k; rw [map_add (f := _), Finsupp.add_apply]; exact add_mem (hy k) (hz k)
    · intro y hy k; rw [map_neg, Finsupp.neg_apply]; exact neg_mem (hy k)
  · intro hz
    rw [← B.sum_repr z]
    refine Subring.sum_mem _ fun k _ => ?_
    have hm0 : ((m (bs k) : ℤ) : F) ≠ 0 := by exact_mod_cast hm (bs k)
    have e : B.repr z k • B k = (algebraMap F (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) ((m (bs k) : F))⁻¹ * B.repr z k) ⊗ₜ[F]
        ((⟨(m (bs k) : F) • bs k, hmi (bs k)⟩ : 𝓞 E) : E) := by
      rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← Algebra.smul_def,
        TensorProduct.smul_tmul]
      congr 1
      change bs k = ((m (bs k) : F))⁻¹ • ((m (bs k) : F) • bs k)
      rw [smul_smul, inv_mul_cancel₀ hm0, one_smul]
    rw [e]
    exact GlobalTheory.AdelicU.tmul_mem_intLoc (E := E) (mul_mem (hv2 k) (hz k)) (⟨(m (bs k) : F) • bs k, hmi (bs k)⟩ : 𝓞 E)

theorem lstdStd : LstdStd := by
  intro F E _ _ _ _ _ n
  refine ⟨fun v => isCO_lstd n v, fun d bs => ?_⟩
  filter_upwards [eventually_mem_intLoc_iff bs] with v hv
  ext y
  change (∀ i, y i ∈ GlobalTheory.AdelicU.intLoc F E v) ↔ _
  simp only [PositivityTheory.PfSWUS.Loc.latO, Set.mem_ofPred_eq]
  exact forall_congr' fun a => hv (y a)

end PositivityTheory.PfSWUS.SwsLstd

end
