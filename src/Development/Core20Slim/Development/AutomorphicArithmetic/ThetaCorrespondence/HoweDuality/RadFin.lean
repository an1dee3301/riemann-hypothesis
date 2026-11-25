module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.FactorApply
public import Development.Core20Slim.Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RadFinAdjoinStable
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.IsApply
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs

@[expose] public section

open scoped TensorProduct
open UpperTheory.Lit.HoweDuality

private theorem UpperTheory.Lit.HoweDuality.radFin_adjoin_stable {M : Type} [AddCommGroup M] [Module ℂ M]
    (Op : Set (Module.End ℂ M)) (P : Submodule ℂ M) (hP : Stable Op P)
    (e : Module.End ℂ M) (he : e ∈ Algebra.adjoin ℂ Op) : ∀ x ∈ P, e x ∈ P :=
  _root_.UpperTheory.Reformulated.B.Qj9.radFin_adjoin_stable Op P hP e he

theorem UpperTheory.Lit.HoweDuality.radFin :
    ∀ {M : Type} [AddCommGroup M] [Module ℂ M] (Op : Set (Module.End ℂ M)) (Rel K : Submodule ℂ M), Stable Op Rel → Stable Op K → Rad Op Rel K → RadFin Op Rel K := by
  intro M _ _ Op Rel K hRel hK hRad
  classical
  obtain ⟨s, hs, h⟩ := hRad
  refine ⟨s, hs, fun S => ?_⟩
  induction S using Finset.induction_on with
  | empty => exact fun _ => ⟨1, one_mem _, rfl, by simp⟩
  | insert k S _ ih =>
    intro hS
    obtain ⟨e', he', hs', hk'⟩ := ih (fun x hx => hS x (Finset.mem_insert_of_mem hx))
    have hkK : e' k ∈ K :=
      radFin_adjoin_stable Op K hK e' he' k (hS k (Finset.mem_insert_self _ _))
    obtain ⟨e'', he'', hs'', hk''⟩ := h _ hkK
    refine ⟨e'' * e', mul_mem he'' he', by simp [hs', hs''], fun x hx => ?_⟩
    rcases Finset.mem_insert.1 hx with rfl | hx
    · simpa using hk''
    · simpa using radFin_adjoin_stable Op Rel hRel e'' he'' _ (hk' x hx)
