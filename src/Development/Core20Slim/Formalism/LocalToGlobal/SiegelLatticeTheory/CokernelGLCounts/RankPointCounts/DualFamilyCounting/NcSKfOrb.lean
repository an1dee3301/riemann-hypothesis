module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.LatHat
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.RPGlue
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.PosNear
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Submonoid.MulAction
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Finsupp.SMulWithZero
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Finite
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.Valuation.ValuationSubring

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.Pf.NcS.KfOrbPf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.LocVol NumberField IsDedekindDomain
  MeasureTheory Topology Filter
open scoped TensorProduct

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem ev_int (x : F) : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, (algebraMap F (Fv F v) x) ∈ v.adicCompletionIntegers F :=
  (algebraMap F (Af F) x).2





variable [FiniteDimensional F E]

theorem ev_crd_oev {d : ℕ} (b : Module.Basis (Fin d) F E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ z ∈ OEv (E := E) v, ∀ l,
      PI.VolStabS.PositiveNearLattice.crd b (Fv F v) z l ∈ v.adicCompletionIntegers F := by
  classical
  let B := NumberField.RingOfIntegers.basis E
  filter_upwards [eventually_all.2 fun t => eventually_all.2 fun l =>
    ev_int (F := F) (b.repr ((B t : 𝓞 E) : E) l)] with v hv
  have hgen : ∀ (o : 𝓞 E) (l : Fin d),
      PI.VolStabS.PositiveNearLattice.crd b (Fv F v) (inclR (F := F) (Fv F v) (o : E)) l ∈
        v.adicCompletionIntegers F := by
    intro o l
    have hcrd : ∀ e : E, PI.VolStabS.PositiveNearLattice.crd b (Fv F v) (inclR (F := F) (Fv F v) e) l =
        algebraMap F (Fv F v) (b.repr e l) := by
      intro e
      simp [PI.VolStabS.PositiveNearLattice.crd, inclR, Algebra.TensorProduct.basis_repr_tmul]
    rw [hcrd]
    have ho : (o : E) = ∑ t, (B.repr o t) • ((B t : 𝓞 E) : E) := by
      have := congrArg (algebraMap (𝓞 E) E) (B.sum_repr o)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at this
      simpa [map_zsmul] using this.symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [ho, map_sum, Finsupp.finsetSum_apply, map_sum]
    refine Subring.sum_mem _ fun t _ => ?_
    rw [map_zsmul, Finsupp.smul_apply, map_zsmul]
    exact Subring.zsmul_mem _ (hv t l) _
  intro z hz l
  change z ∈ Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ) at hz
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨o, -, rfl⟩ := hy
    exact hgen o l
  | zero => simp [PI.VolStabS.PositiveNearLattice.crd]
  | add a c _ _ ha hc =>
    simp only [PI.VolStabS.PositiveNearLattice.crd, map_add (f := _), Finsupp.add_apply] at *
    exact Subring.add_mem _ ha hc
  | smul c a _ ha =>
    have e : PI.VolStabS.PositiveNearLattice.crd b (Fv F v) (c • a) l =
        (c : Fv F v) * PI.VolStabS.PositiveNearLattice.crd b (Fv F v) a l := by
      show (Algebra.TensorProduct.basis (Fv F v) b).repr ((c : Fv F v) • a) l = _
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
      rfl
    rw [e]
    exact Subring.mul_mem _ c.2 ha


end SlopeTestRemainingChoices


end Formalism.L2.SG.Pf.NcS.KfOrbPf
