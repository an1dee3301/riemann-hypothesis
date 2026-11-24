module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteSupport
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProdUpdateSelf
public import Init.Prelude
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.IoLift

theorem mem_range_map_subtype_of_contr (ι : Type) [Fintype ι] (K : ι → Type) [∀ i, AddCommGroup (K i)]
    [∀ i, Module ℂ (K i)] (N : ∀ i, Submodule ℂ (K i)) (x : ⨂[ℂ] i, K i)
    (h : ∀ i (L : (⨂[ℂ] j, K j) →ₗ[ℂ] K i), (∀ f : Module.End ℂ (K i), L ∘ₗ intersection_update_fsHerm_neg_one i f = f ∘ₗ L) → L x ∈ N i) :
    x ∈ LinearMap.range (PiTensorProduct.map fun i => (N i).subtype) := by
  first
  | exact @_root_.GlobalTheory.TensorContraction.mem_range_map
  | exact _root_.GlobalTheory.TensorContraction.mem_range_map
  | (apply _root_.GlobalTheory.TensorContraction.mem_range_map <;> assumption)
  | (intros; apply _root_.GlobalTheory.TensorContraction.mem_range_map <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TensorContraction.mem_range_map <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TensorContraction.mem_range_map ..)

end GlobalTheory.Chain.IoLift
