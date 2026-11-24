module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrandPeriodic
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteAdeleVectorAnnihilatorsCompactOpenBasisStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.Order.Filter.Defs
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

namespace GlobalTheory.ThetaTransform

noncomputable def finEmbSnd (F : Type) [Field F] [NumberField F] (N : ℕ) : (Fin N → Af F) →+ VA F N where
  toFun v := (0, fun i => pairA F 0 (v i))
  map_zero' := rfl
  map_add' v w := by
    refine Prod.ext (add_zero _).symm ?_
    funext i
    exact Prod.ext (add_zero _).symm rfl

theorem continuous_finEmbSnd (F : Type) [Field F] [NumberField F] (N : ℕ) : Continuous (finEmbSnd F N) :=
  continuous_const.prodMk (continuous_pi fun i => continuous_const.prodMk (continuous_apply i))

theorem dotProduct_finEmbSnd {F : Type} [Field F] [NumberField F] {N : ℕ} (x : Fin N → AF F) (v : Fin N → Af F) :
    x ⬝ᵥ (finEmbSnd F N v).2 = pairA F 0 (Bd (Af F) (half F N) (fin x) v) := by
  have h : Bd (Af F) (half F N) (fin x) v = ∑ i, fin x i * v i := by
    simp [Bd, half]
  rw [h]
  refine Prod.ext ?_ ?_
  · change fstA F (∑ i, x i * pairA F 0 (v i)) = 0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_eq_zero fun i _ => by rw [map_mul]; exact mul_zero _
  · change sndA F (∑ i, x i * pairA F 0 (v i)) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    rfl

theorem invV_level_support : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)), Ctx ψ lam ν (half F N) → ∀ 𝓓 : Set (Fin N → AF F), IsAddFundamentalDomain (ratSub F N) 𝓓 (muV N ν) → muV N ν 𝓓 = 1 → ∀ f : VA F N → ℂ, QuasiV ψ f → LevelV ψ f → (∃ U : AddSubgroup (Fin N → AF F), IsOpen (U : Set (Fin N → AF F)) ∧ ∀ u ∈ U, inf u = 0 → ∀ x, invV ψ ν 𝓓 f (x + u) = invV ψ ν 𝓓 f x) ∧ ∃ K : Set (Fin N → Af F), IsCompact K ∧ ∀ x, invV ψ ν 𝓓 f x ≠ 0 → fin x ∈ K := by
  intro F _ _ N _ ψ lam ν hc 𝓓 hD _ f hq hl
  obtain ⟨U, hU, hf⟩ := hl
  have h0 : inf (0 : Fin N → AF F) = 0 := rfl
  refine ⟨⟨U.comap (AddMonoidHom.inl (Fin N → AF F) (Fin N → AF F)),
    hU.preimage (f := fun u : Fin N → AF F => ((u, 0) : VA F N)) (continuous_id.prodMk continuous_const), ?_⟩, ?_⟩
  · intro u hu hi x
    rw [← invV_heisV_fst, hf (u, 0) hu hi h0]
  · refine ⟨_, (GlobalTheory.T.finiteAdeleVector_annihilators_compact_open_basis F N ψ lam ν (half F N) hc).1 (U.comap (finEmbSnd F N))
      (hU.preimage (continuous_finEmbSnd F N)), fun x hx v hv => ?_⟩
    have h1 := invV_heisV_snd hc.2.2.2.1 hD hq (finEmbSnd F N v).2 x
    rw [show ((0 : Fin N → AF F), (finEmbSnd F N v).2) = finEmbSnd F N v from rfl, hf _ hv h0 rfl,
      dotProduct_finEmbSnd] at h1
    exact mul_right_cancel₀ hx (h1.symm.trans (one_mul _).symm)

end GlobalTheory.ThetaTransform
