module

public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.RingHom
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.WithAbs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.UniformMulAction
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.ContMapReal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem continuous_evInf (w : InfinitePlace F) : Continuous (evInf F w) := by
  show Continuous (fun a : AF F => a.1 w)
  exact (continuous_apply w).comp continuous_fst

def phiW (w : InfinitePlace F) : AF F →+* ℂ :=
  (InfinitePlace.Completion.extensionEmbedding w).comp (evInf F w).toRingHom

theorem continuous_phiW (w : InfinitePlace F) : Continuous (phiW (F := F) w) :=
  (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp (continuous_evInf w)

theorem piInf_smul {w : InfinitePlace F} (τ : EmbOver E w) (a : AF F) (x : AE F E) :
    piInf τ (a • x) = phiW w a * piInf τ x := by
  rw [Algebra.smul_def, map_mul]
  congr 1
  simp [piInf, compInf, infEmb, phiW, Algebra.TensorProduct.algebraMap_apply]

theorem continuous_piInf {w : InfinitePlace F} (τ : EmbOver E w) : Continuous (piInf (E := E) τ) := by
  letI : Module (AF F) ℂ := Module.compHom ℂ (phiW (F := F) w)
  haveI : ContinuousSMul (AF F) ℂ := ⟨by
    show Continuous (fun p : AF F × ℂ => phiW w p.1 * p.2)
    exact ((continuous_phiW w).comp continuous_fst).mul continuous_snd⟩
  let L : AE F E →ₗ[AF F] ℂ :=
    { toFun := piInf τ
      map_add' := map_add _
      map_smul' := fun a x => by rw [piInf_smul]; rfl }
  exact IsModuleTopology.continuous_of_linearMap L

theorem contmap {σ : E →ₐ[F] E} {β : Type} [Fintype β] [DecidableEq β] {J : Matrix β β (AE F E)}
    (γ : Multiplicative ℝ →* UG (cA σ) J) (hγ : Continuous γ) (w : InfinitePlace F) (τ : EmbOver E w) :
    Continuous (fun t : ℝ => ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (piInf τ)) := by
  have h1 : Continuous (fun t : ℝ => ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E))) :=
    Units.continuous_val.comp (continuous_subtype_val.comp (hγ.comp continuous_ofAdd))
  exact h1.matrix_map (continuous_piInf τ)

end GlobalTheory.ContMapReal

end
