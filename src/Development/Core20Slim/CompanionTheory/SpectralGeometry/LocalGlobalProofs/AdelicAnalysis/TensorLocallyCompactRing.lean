module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Rat.Basic
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Rat
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Defs
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
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.TopK

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

section

variable {F E : Type} [Field F] [Field E] [Algebra F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]


omit [IsTopologicalRing R] in
theorem isModTop : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩

def coordHomeo {d : ℕ} (b : Module.Basis (Fin d) F E) : (R ⊗[F] E) ≃ₜ (Fin d → R) :=
  haveI : IsModuleTopology R (R ⊗[F] E) := isModTop R
  haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R _
  { (Algebra.TensorProduct.basis R b).equivFun.toEquiv with
    continuous_toFun :=
      IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.basis R b).equivFun.toLinearMap
    continuous_invFun :=
      IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.basis R b).equivFun.symm.toLinearMap }

theorem isHomeomorph_coord {d : ℕ} (b : Module.Basis (Fin d) F E) :
    IsHomeomorph fun (y : R ⊗[F] E) (k : Fin d) => (Algebra.TensorProduct.basis R b).repr y k :=
  (coordHomeo R b).isHomeomorph

theorem isTopRing [Module.Finite F E] : IsTopologicalRing (R ⊗[F] E) :=
  haveI : IsModuleTopology R (R ⊗[F] E) := isModTop R
  IsModuleTopology.isTopologicalRing R (R ⊗[F] E)

omit [IsTopologicalRing R] in
theorem continuous_sigR (σ : E →ₐ[F] E) : Continuous (sigR R σ) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R _
  exact IsModuleTopology.continuous_of_linearMap
    (Algebra.TensorProduct.map (AlgHom.id R R) σ).toLinearMap

theorem continuous_trace [Module.Finite F E] : Continuous (Algebra.trace R (R ⊗[F] E)) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := isModTop R
  exact IsModuleTopology.continuous_of_linearMap _

end

theorem topTens_props : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R], IsTopologicalRing (R ⊗[F] E) ∧ LocallyCompactSpace (R ⊗[F] E) ∧ SecondCountableTopology (R ⊗[F] E) ∧ T2Space (R ⊗[F] E) ∧ Continuous (sigR R σ) ∧ Continuous (Algebra.trace R (R ⊗[F] E)) ∧ (∀ (d : ℕ) (b : Module.Basis (Fin d) F E), IsHomeomorph fun (y : R ⊗[F] E) (k : Fin d) => (Algebra.TensorProduct.basis R b).repr y k) ∧ (∀ n M : ℕ, BorelSpace (Fin n → Fin M → R ⊗[F] E)) ∧ (∀ n : ℕ, IsClosed (HermR R σ n : Set (Matrix (Fin n) (Fin n) (R ⊗[F] E)))) ∧ (∀ (n M : ℕ) (J : Matrix (Fin M) (Fin M) E), Continuous (gramR R σ J : (Fin n → Fin M → R ⊗[F] E) → _)) := by
  intro F E _ _ _ _ _ σ _ R _ _ _ _ _ _ _
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have e := coordHomeo R (Module.finBasis F E)
  haveI h1 : IsTopologicalRing (R ⊗[F] E) := isTopRing R
  haveI h2 : LocallyCompactSpace (R ⊗[F] E) := e.isOpenEmbedding.locallyCompactSpace
  haveI h3 : SecondCountableTopology (R ⊗[F] E) := e.secondCountableTopology
  haveI h4 : T2Space (R ⊗[F] E) := e.isEmbedding.t2Space
  haveI h5 : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  have hs := continuous_sigR R σ
  refine ⟨h1, h2, h3, h4, hs, continuous_trace R, fun d b => isHomeomorph_coord R b,
    fun n M => inferInstance, fun n => ?_, fun n M J => ?_⟩
  · have : (HermR R σ n : Set (Matrix (Fin n) (Fin n) (R ⊗[F] E))) =
        ⋂ a, ⋂ b, {S | sigR R σ (S b a) = S a b} := by
      ext S
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      rfl
    rw [this]
    refine isClosed_iInter fun a => isClosed_iInter fun b => isClosed_eq ?_ ?_
    · exact hs.comp (continuous_id.matrix_elem b a)
    · exact continuous_id.matrix_elem a b
  · refine continuous_pi fun a => continuous_pi fun b => ?_
    unfold gramR hR hform
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact ((hs.comp ((continuous_apply i).comp (continuous_apply a))).mul continuous_const).mul
      ((continuous_apply j).comp (continuous_apply b))

end GlobalTheory.CompanionTheory.SW.TopK
