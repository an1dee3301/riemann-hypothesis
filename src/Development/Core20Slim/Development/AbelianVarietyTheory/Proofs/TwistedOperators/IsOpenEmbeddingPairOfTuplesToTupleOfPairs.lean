module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecCEApply
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Init.Prelude
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Homeomorph.Defs

@[expose] public section

open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct

namespace GlobalTheory.ModuLR

theorem zipHom_isOpenEmbedding : ∀ (κ X Y : Type) [Fintype κ] [AddCommGroup X] [TopologicalSpace X]
    [AddCommGroup Y] [TopologicalSpace Y], IsOpenEmbedding (zipHom κ X Y) := by
  intro κ X Y _ _ _ _ _
  let e : ((κ → X) × (κ → Y)) ≃ₜ (κ → X × Y) :=
    { toFun := fun p i => (p.1 i, p.2 i)
      invFun := fun q => (fun i => (q i).1, fun i => (q i).2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := continuous_pi fun i =>
        ((continuous_apply i).comp continuous_fst).prodMk ((continuous_apply i).comp continuous_snd)
      continuous_invFun :=
        (continuous_pi fun i => continuous_fst.comp (continuous_apply i)).prodMk
          (continuous_pi fun i => continuous_snd.comp (continuous_apply i)) }
  exact e.isOpenEmbedding

end GlobalTheory.ModuLR
