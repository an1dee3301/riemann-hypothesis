module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Invertible
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ
open scoped Matrix

namespace GlobalTheory.ThetaTransform

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

abbrev VA (F : Type) [Field F] [NumberField F] (N : ℕ) : Type := (Fin N → AF F) × (Fin N → AF F)

def symV (w w' : VA F N) : AF F := w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2

def embR {κ : Type} (t : κ → mixedEmbedding.mixedSpace F) : κ → AF F :=
  fun i => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t i)) 0

def IsRealLine (M : ℝ →+ VA F N) : Prop := Continuous M ∧ ∀ t, fin (M t).1 = 0 ∧ fin (M t).2 = 0

def half (F : Type) [Field F] (N : ℕ) : Fin N → F := fun _ => 1 / 2

variable [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ)

def heisV (u : VA F N) (f : VA F N → ℂ) : VA F N → ℂ := fun w => ψ (⅟(2 : AF F) * symV w u) * f (w + u)

def thV (Φ : (Fin N → AF F) → ℂ) : VA F N → ℂ := fun w => GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ w Φ)

def invV (ν : Measure (AF F)) (𝓓 : Set (Fin N → AF F)) (f : VA F N → ℂ) : (Fin N → AF F) → ℂ :=
  fun x => ∫ y in 𝓓, f (x, y) * ψ (-(⅟(2 : AF F) * (x ⬝ᵥ y))) ∂(muV N ν)

def QuasiV (f : VA F N → ℂ) : Prop :=
  ∀ (a b : Fin N → F) (w : VA F N), f ((rat a, rat b) + w) = ψ (-(⅟(2 : AF F) * symV (rat a, rat b) w)) * f w

def LevelV (f : VA F N → ℂ) : Prop :=
  ∃ U : AddSubgroup (VA F N), IsOpen (U : Set (VA F N)) ∧ ∀ u ∈ U, inf u.1 = 0 → inf u.2 = 0 → heisV ψ u f = f

abbrev ratSub (F : Type) [Field F] [NumberField F] (N : ℕ) : AddSubgroup (Fin N → AF F) :=
  AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F)))

theorem invOf_two_eq : ⅟(2 : AF F) = algebraMap F (AF F) (1 / 2) := by
  refine invOf_eq_right_inv ?_
  rw [← map_ofNat (algebraMap F (AF F)) 2, ← map_mul]
  simp

omit [Invertible (2 : AF F)] in
theorem Bd_half (u u' : Fin N → AF F) : Bd (AF F) (half F N) u u' = u ⬝ᵥ u' := by
  simp [Bd, half, dotProduct]

omit [NumberField F] [Invertible (2 : AF F)] in
theorem half_ne_zero [CharZero F] (l : Fin N) : half F N l ≠ 0 := by
  simp [half]

theorem schr_eq_rho (w : VA F N) (Φ : (Fin N → AF F) → ℂ) :
    GlobalTheory.WeilM.schr ψ w Φ = rho ψ (half F N) w.1 w.2 Φ := by
  funext x
  rw [GlobalTheory.WeilM.schr, rho, Bd_half, Bd_half, invOf_two_eq]

theorem thV_eq_th (Φ : (Fin N → AF F) → ℂ) (w : VA F N) : thV ψ Φ w = th (rho ψ (half F N) w.1 w.2 Φ) := by
  rw [thV, schr_eq_rho]
  rfl

theorem two_mul_invOf (a : AF F) : ⅟(2 : AF F) * a + ⅟(2 : AF F) * a = a := by
  rw [← add_mul, invOf_two_add_invOf_two, one_mul]

theorem schr_schr (w u : VA F N) (Φ : (Fin N → AF F) → ℂ) :
    GlobalTheory.WeilM.schr ψ w (GlobalTheory.WeilM.schr ψ u Φ) = ψ (⅟(2 : AF F) * symV w u) • GlobalTheory.WeilM.schr ψ (w + u) Φ := by
  funext x
  simp only [GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add, ← mul_assoc,
    ← AddChar.map_add_eq_mul, add_assoc]
  congr 2
  simp only [symV, add_dotProduct, dotProduct_add]
  linear_combination (-1 : AF F) * two_mul_invOf (w.1 ⬝ᵥ u.2)

theorem thV_schr (u : VA F N) (Φ : (Fin N → AF F) → ℂ) : thV ψ (GlobalTheory.WeilM.schr ψ u Φ) = heisV ψ u (thV ψ Φ) := by
  funext w
  rw [thV, schr_schr, heisV, thV]
  exact tsum_mul_left

theorem quasiV_thV (hψ : ∀ a : F, ψ (algebraMap F (AF F) a) = 1) (Φ : (Fin N → AF F) → ℂ) : QuasiV ψ (thV ψ Φ) := by
  intro a b w
  simp only [thV, GlobalTheory.WeilM.thetaSum]
  rw [← tsum_mul_left, ← (Equiv.addRight a).tsum_eq (fun ξ : Fin N → F => ψ (-(⅟(2 : AF F) * symV (rat a, rat b) w)) *
    GlobalTheory.WeilM.schr ψ w Φ fun i => algebraMap F (AF F) (ξ i))]
  refine tsum_congr fun ξ => ?_
  have e1 : (fun i => algebraMap F (AF F) ((Equiv.addRight a ξ) i)) = rat ξ + rat a := by
    funext i; simp [rat]
  have e2 : (fun i => algebraMap F (AF F) (ξ i)) = rat ξ := rfl
  have e3 : ∀ c d : Fin N → F, rat c ⬝ᵥ rat d = algebraMap F (AF F) (c ⬝ᵥ d) := fun c d => by
    simp [rat, dotProduct]
  rw [e1, e2]
  simp only [GlobalTheory.WeilM.schr, Prod.fst_add, Prod.snd_add, ← mul_assoc, ← AddChar.map_add_eq_mul, add_assoc]
  congr 1
  have h1 := hψ (ξ ⬝ᵥ b + 1 / 2 * (a ⬝ᵥ b))
  rw [← mul_one (ψ (-(⅟(2 : AF F) * symV (rat a, rat b) w) + _)), ← h1, ← AddChar.map_add_eq_mul]
  congr 1
  rw [map_add (f := _), map_mul, ← invOf_two_eq, ← e3, ← e3]
  simp only [symV, add_dotProduct, dotProduct_add]
  linear_combination two_mul_invOf (rat a ⬝ᵥ w.2)

end GlobalTheory.ThetaTransform

end
