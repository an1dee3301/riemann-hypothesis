module

public import Mathlib
public import Development.Core20Slim.GroundTheory.AutomorphicForms.AdelicGLn
public import GroundTheory.GlobalFields.Adele.Approximation
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.AdelicCharDual
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.ClusterPt
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter

@[expose] public section

open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped RestrictedProduct

namespace GroundTheory.Automorphic

noncomputable section

namespace AdelicGLn

variable (K : Type*) [Field K] [NumberField K]

theorem denseRange_algebraMap_finiteAdeleRing :
    DenseRange (algebraMap K (FiniteAdeleRing (𝓞 K) K)) := by
  intro a
  refine mem_closure_iff_nhds.2 fun U hU => ?_
  have hW : (fun y => a + y) ⁻¹' U ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 K) K) :=
    (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (by simpa using hU)
  obtain ⟨d, hd0, hd⟩ := GroundTheory.Global.exists_forall_mul_mem_of_mem_nhds hW
  set c : K := algebraMap (𝓞 K) K d
  have hc : c ≠ 0 := by
    simpa [c] using hd0
  set x := algebraMap K (FiniteAdeleRing (𝓞 K) K)
  obtain ⟨k, hk⟩ := GroundTheory.Global.exists_sub_mem_integralFiniteAdeles (R := 𝓞 K) (K := K)
    (x c⁻¹ * a)
  have hmem := hd _ (neg_mem hk)
  have hcc : x c * x c⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hc, map_one]
  refine ⟨x (c * k), ?_, c * k, rfl⟩
  have heq : a + x c * -(x c⁻¹ * a - x k) = x (c * k) := by
    rw [map_mul]
    linear_combination (-a) * hcc
  rw [← heq]
  exact hmem

variable (n : ℕ)

def finiteDiagonal : GL (Fin n) K →* FiniteAdelicGL K n :=
  Matrix.GeneralLinearGroup.map (algebraMap K (FiniteAdeleRing (𝓞 K) K))

@[simp]
theorem finiteDiagonal_apply (γ : GL (Fin n) K) (a b : Fin n) :
    finiteDiagonal K n γ a b = algebraMap K (FiniteAdeleRing (𝓞 K) K) (γ a b) :=
  rfl








variable {K n}






















variable (K n)



end AdelicGLn

end

end GroundTheory.Automorphic
