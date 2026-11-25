module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ConvRight
public import Development.AbelianVarietyTheory.Definitions.Foundations.AnalyticOnNhdTsumNpow
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Quot
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

namespace PositivityTheory.Rg.Sw.Glob

theorem holValueAt_finsum {ι : Type} (T : Finset ι) {f : ι → ℂ → ℂ} {c : ι → ℂ} {s₀ : ℂ}
    (h : ∀ i ∈ T, GlobalTheory.Cont.HolValueAt (f i) s₀ (c i)) :
    GlobalTheory.Cont.HolValueAt (fun s => ∑ i ∈ T, f i s) s₀ (∑ i ∈ T, c i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using GlobalTheory.Cont.holValueAt_const 0 s₀
  | insert a T ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem cosetSum_finsum {G : Type} [Group G] (Pp Γ : Subgroup G) {ι : Type} (T : Finset ι) (f : ι → G → ℂ) (g : G)
    (h : ∀ i ∈ T, GlobalTheory.Eis.CosetConv Pp Γ (f i) g) :
    GlobalTheory.Eis.cosetSum Pp Γ (fun x => ∑ i ∈ T, f i x) g = ∑ i ∈ T, GlobalTheory.Eis.cosetSum Pp Γ (f i) g := by
  unfold GlobalTheory.Eis.cosetSum GlobalTheory.Eis.term
  exact Summable.tsum_finsetSum fun i hi => (h i hi).of_norm

end PositivityTheory.Rg.Sw.Glob
