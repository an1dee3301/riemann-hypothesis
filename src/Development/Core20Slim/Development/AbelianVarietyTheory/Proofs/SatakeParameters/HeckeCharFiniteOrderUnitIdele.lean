module

public import Mathlib
public import Formalism.LocalToGlobal.UnitaryNorms.CharTied
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfDiagMulFinPartI
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousCharacterFiniteOrderIntegralUnits
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.ContinuousMap.Defs
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import ReciprocityTheory.NeutralLocalFields.Reciprocity

@[expose] public section

noncomputable section

namespace GlobalTheory.HeckeFin

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

variable {L : Type} [Field L] [NumberField L]

theorem circle_pow (ψ : Ideles L →* Circle) (hψ : Continuous ψ) :
    ∃ m : ℕ, 0 < m ∧ ∀ u : Ideles L, IsFinIdele u → u ∈ unitIdl L → ψ u ^ m = 1 := by
  obtain ⟨-, -, -, m, hm, h⟩ := GlobalTheory.CharFin.finite_order_of_small (R := AdeleRing (𝓞 L) L)
    (RingHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)) (RingHom.snd _ _) id continuous_id (fun _ => rfl)
    (GlobalTheory.UnUnitCmp.Val.intFin L) (fun W hW => GlobalTheory.AdLat.OpenLat.exists_nsmul_adele L W hW)
    GlobalTheory.UnUnitCmp.Val.finite_quot ψ hψ
  exact ⟨m, hm, fun u h1 h2 => h u ⟨funext h1, fun v => (h2 v).le, fun v => ((unitIdl L).inv_mem h2 v).le⟩⟩

theorem norm_ne (χ : HChar L) (x : Ideles L) : ‖((χ.1 x : ℂˣ) : ℂ)‖ ≠ 0 :=
  norm_ne_zero_iff.2 (Units.ne_zero _)

theorem continuous_norm_val (χ : HChar L) : Continuous fun x : Ideles L => ‖((χ.1 x : ℂˣ) : ℂ)‖ :=
  (Units.continuous_val.comp χ.2.1).norm

def twist (χ : HChar L) (c : ℝ) : Ideles L →* Circle where
  toFun x := Circle.exp (c * Real.log ‖((χ.1 x : ℂˣ) : ℂ)‖)
  map_one' := by simp
  map_mul' x y := by
    rw [χ.1.map_mul, Units.val_mul, norm_mul, Real.log_mul (norm_ne χ x) (norm_ne χ y), mul_add, Circle.exp_add]

theorem continuous_twist (χ : HChar L) (c : ℝ) : Continuous (twist χ c) :=
  Circle.exp.continuous.comp (continuous_const.mul ((continuous_norm_val χ).log (norm_ne χ)))

theorem norm_eq_one (χ : HChar L) (a : Ideles L) (h1 : IsFinIdele a) (h2 : a ∈ unitIdl L) :
    ‖((χ.1 a : ℂˣ) : ℂ)‖ = 1 := by
  by_contra hne
  have ht : Real.log ‖((χ.1 a : ℂˣ) : ℂ)‖ ≠ 0 := by
    intro h0
    rcases Real.log_eq_zero.1 h0 with h | h | h
    · exact norm_ne χ a h
    · exact hne h
    · linarith [norm_nonneg ((χ.1 a : ℂˣ) : ℂ)]
  set t := Real.log ‖((χ.1 a : ℂˣ) : ℂ)‖ with htdef
  obtain ⟨m, hm, h⟩ := circle_pow (twist χ (2 * Real.pi * √2 / t)) (continuous_twist χ _)
  have e := h a h1 h2
  have e1 : twist χ (2 * Real.pi * √2 / t) a = Circle.exp (2 * Real.pi * √2) := by
    change Circle.exp (2 * Real.pi * √2 / t * Real.log ‖((χ.1 a : ℂˣ) : ℂ)‖) = _
    rw [← htdef, div_mul_cancel₀ _ ht]
  rw [e1, ← Circle.exp_nsmul] at e
  have e2 := congrArg (fun z : Circle => (z : ℂ)) e
  simp only [Circle.coe_exp, Circle.coe_one] at e2
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 e2
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have e3 : (m : ℂ) * (√2 : ℝ) = n := by
    have : ((m : ℂ) * (√2 : ℝ)) * (2 * Real.pi * Complex.I) = n * (2 * Real.pi * Complex.I) := by
      rw [← hn]; push_cast; simp only [nsmul_eq_mul]; push_cast; ring
    exact mul_right_cancel₀ (by simp [hpi, Complex.I_ne_zero]) this
  have e4 : (m : ℝ) * √2 = n := by exact_mod_cast e3
  exact (irrational_sqrt_two.natCast_mul hm.ne').ne_int n e4

def unitPart (χ : HChar L) : Ideles L →* Circle where
  toFun x := ⟨((χ.1 x : ℂˣ) : ℂ) / ‖((χ.1 x : ℂˣ) : ℂ)‖, by
    simp [Submonoid.unitSphere, norm_ne χ x]⟩
  map_one' := by ext; simp
  map_mul' x y := by
    ext
    change ((χ.1 (x * y) : ℂˣ) : ℂ) / ‖((χ.1 (x * y) : ℂˣ) : ℂ)‖ =
      (((χ.1 x : ℂˣ) : ℂ) / ‖((χ.1 x : ℂˣ) : ℂ)‖) * (((χ.1 y : ℂˣ) : ℂ) / ‖((χ.1 y : ℂˣ) : ℂ)‖)
    rw [χ.1.map_mul, Units.val_mul, norm_mul]
    push_cast
    rw [mul_div_mul_comm]

theorem continuous_unitPart (χ : HChar L) : Continuous (unitPart χ) := by
  refine Continuous.subtype_mk ?_ _
  exact (Units.continuous_val.comp χ.2.1).div (Complex.continuous_ofReal.comp (continuous_norm_val χ))
    (fun x => by simpa using norm_ne χ x)

theorem finite_order : ∀ (L : Type) [Field L] [NumberField L] (χ : HChar L) (a : Ideles L), IsFinIdele a →
    (∀ v, Valued.v ((a : AdeleRing (𝓞 L) L).2 v) = 1) → ∃ n : ℕ, 0 < n ∧ χ.1 a ^ n = 1 := by
  intro L _ _ χ a h1 h2
  have h2' : a ∈ unitIdl L := h2
  obtain ⟨m, hm, h⟩ := circle_pow (unitPart χ) (continuous_unitPart χ)
  refine ⟨m, hm, Units.ext ?_⟩
  have e := congrArg (fun z : Circle => (z : ℂ)) (h a h1 h2')
  have e1 : ((unitPart χ a : Circle) : ℂ) = ((χ.1 a : ℂˣ) : ℂ) := by
    change ((χ.1 a : ℂˣ) : ℂ) / ‖((χ.1 a : ℂˣ) : ℂ)‖ = _
    rw [norm_eq_one χ a h1 h2']; simp
  simpa [e1] using e

end GlobalTheory.HeckeFin
