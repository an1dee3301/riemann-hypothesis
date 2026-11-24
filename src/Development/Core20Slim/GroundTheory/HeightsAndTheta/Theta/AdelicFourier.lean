module

public import Mathlib
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Theta.AdelicFourierCoord
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.GaussianSchwartz
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Defs.Basic

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Theta

open GroundTheory.Global GroundTheory.Automorphic.GJMatrix NumberField NumberField.mixedEmbedding
  IsDedekindDomain MeasureTheory Measure Matrix Module TensorProduct
open scoped NumberField.AdeleRing ENNReal NNReal SchwartzMap Classical nonZeroDivisors

noncomputable section

set_option synthInstance.maxSize 1000
set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [NumberField K]
variable {X : Type*} [AddCommGroup X] [Module K X] [FiniteDimensional K X]


variable (K X) in
abbrev AdelicPoints : Type _ := 𝔸[K] ⊗[K] X

instance : TopologicalSpace (AdelicPoints K X) := moduleTopology 𝔸[K] (AdelicPoints K X)

instance : IsModuleTopology 𝔸[K] (AdelicPoints K X) := ⟨rfl⟩

instance : IsTopologicalAddGroup (AdelicPoints K X) := IsModuleTopology.topologicalAddGroup 𝔸[K] _

instance : MeasurableSpace (AdelicPoints K X) := borel _

instance : BorelSpace (AdelicPoints K X) := ⟨rfl⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ] [DecidableEq κ]



variable (B : LinearMap.BilinForm K X)




end

end GroundTheory.Heights₂.Theta
