module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
public import Formalism.RealPlaceAnalysis.FinalF
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactHaarRightInvariantInst
public import Formalism.RealPlaceAnalysis.Complexify
public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
public import Init.Core
public import Init.Data.Function
public import Init.Prelude
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.ContinuousMap.Defs
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.KHolExt

variable {n : ℕ} {ε : Fin n → Bool}














lemma isEmb (ε : Fin n → Bool) : Topology.IsEmbedding (fun k : KG ε => toMK k) := by
  have hc : Continuous (fun k : KG ε => toMK k) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hi : Function.Injective (fun k : KG ε => toMK k) := fun a b h =>
    Subtype.ext (Subtype.ext (Units.ext h))
  exact (hc.isClosedEmbedding hi).isEmbedding

def ent (ε : Fin n → Bool) (i j : Fin n) : C(KG ε, ℂ) :=
  ⟨fun k => toMK k i j, (continuous_apply_apply i j).comp (isEmb ε).continuous⟩







end GlobalTheory.KHolExt
