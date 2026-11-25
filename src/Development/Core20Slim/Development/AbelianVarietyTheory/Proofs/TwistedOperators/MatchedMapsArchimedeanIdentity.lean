module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleGlobalProductFormula
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.IsApply
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.Order.Notation
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

namespace GlobalTheory.KStableLie

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mem_of_isExp {V : Type} [AddCommGroup V] [Module ℂ V] {L U : Module.End ℂ V} (hU : IsExp L U)
    (N : Submodule ℂ V) (hL : ∀ y ∈ N, L y ∈ N) {v : V} (hv : v ∈ N) : U v ∈ N := by
  have hpow : ∀ m : ℕ, (L ^ m) v ∈ N := by
    intro m
    induction m with
    | zero => simpa using hv
    | succ m ih => rw [pow_succ', Module.End.mul_apply]; exact hL _ ih
  by_contra hn
  obtain ⟨l, hl, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hn inferInstance
  have hz : ∀ y ∈ N, l y = 0 := fun y hy => by
    have h' := Submodule.mem_map_of_mem (f := l) hy
    rw [hmap, Submodule.mem_bot] at h'
    exact h'
  have h0 : (fun m : ℕ => ((m.factorial : ℂ))⁻¹ * l ((L ^ m) v)) = fun _ => 0 := by
    funext m; rw [hz _ (hpow m), mul_zero]
  have hs := hU v l
  rw [h0] at hs
  exact hl (hs.unique hasSum_zero)


end GlobalTheory.KStableLie

end
