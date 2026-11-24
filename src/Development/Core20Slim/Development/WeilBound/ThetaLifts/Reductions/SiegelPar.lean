module

public import Development.Core20Slim.Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import Development.Core20Slim.Development.WeilBound.ThetaLifts.Reductions.SiegelAbs
public import Development.Core20Slim.Development.WeilBound.ThetaLifts.Reductions.SiegelParMod
public import Development.Core20Slim.Development.WeilBound.ThetaLifts.Reductions.SiegelGood
public import Development.Core20Slim.Development.WeilBound.ThetaLifts.FrameEstimates.LintegralLeOfCover
public import Development.Core20Slim.Development.WeilBound.ThetaLifts.FrameEstimates.LeHeightOfIsTorusElt
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.Core20Slim.Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Nat.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Ring.WithAbs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.SiegelSet GlobalTheory.Orb Matrix
open Formalism.UG (cT)
open PositivityTheory.ThKEst PositivityTheory.ThKEst.Sieg

namespace PositivityTheory.ThKR

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n r : ℕ} {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E}


variable (σ J X Y) in
structure IsTorus (a : (Fin r → ℝ) → GAd σ J) : Prop where
  add : ∀ s t, a (s + t) = a s * a t
  cont : Continuous a
  tor : ∀ t, IsTorusElt σ J X Y (fun i => Real.exp (t i)) (a t)
  onX : ∀ t, (matHom _ σ J (a t)).1 * adMat F X = adMat F X * diagonal (fun i => algebraMap (AF F) (AE F E) (rId F (t i)))
  onY : ∀ t, (matHom _ σ J (a t)).1 * adMat F Y = adMat F Y * diagonal (fun i => algebraMap (AF F) (AE F E) (rId F (-t i)))
  onV : ∀ t, ∀ z : Fin n → E, (cT (σ : E →+* E) X * J) *ᵥ z = 0 → (cT (σ : E →+* E) Y * J) *ᵥ z = 0 →
    (matHom _ σ J (a t)).1 *ᵥ incV F z = incV F z

theorem exists_isTorus (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) :
    ∃ a, IsTorus σ J X Y a := by
  obtain ⟨a, h1, h2, h3, h4⟩ := exists_torus h hJ hW
  exact ⟨a, ⟨h1, h2, h3, fun t => (h4 t).1, fun t => (h4 t).2.1, fun t => (h4 t).2.2⟩⟩

theorem mul_mem_minPar {p q : GAd σ J} (hp : p ∈ minPar σ J X) (hq : q ∈ minPar σ J X) : p * q ∈ minPar σ J X :=
  mul_mem_minimal_parabolic hp hq

theorem inv_mem_minPar (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {p : GAd σ J}
    (hp : p ∈ minPar σ J X) : p⁻¹ ∈ minPar σ J X :=
  inv_mem_minimal_parabolic h hJ hW hp


variable (X) in
def minParSub (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) : Subgroup (GAd σ J) where
  carrier := minPar σ J X
  one_mem' := one_mem_minPar σ J X
  mul_mem' := mul_mem_minPar
  inv_mem' := inv_mem_minPar h hJ hW

theorem isClosed_minPar (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) :
    IsClosed (minPar σ J X) :=
  isClosed_minimal_parabolic h hJ hW

theorem minParOne_subset : minParOne σ J X ⊆ minPar σ J X := fun _ ⟨B, hB, e, _⟩ => ⟨B, hB, e⟩

theorem IsTorus.mem {a : (Fin r → ℝ) → GAd σ J} (ha : IsTorus σ J X Y a) (t : Fin r → ℝ) : a t ∈ minPar σ J X :=
  ⟨_, Matrix.blockTriangular_diagonal _, ha.onX t⟩

def IsTorus.sub {a : (Fin r → ℝ) → GAd σ J} (ha : IsTorus σ J X Y a) (h : IsCMExt F E σ) (hJ : IsHermND σ J)
    (hW : IsWittFrame σ J X Y) (t : Fin r → ℝ) : minParSub X h hJ hW :=
  ⟨a t, ha.mem t⟩

theorem exists_tau (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {a : (Fin r → ℝ) → GAd σ J}
    (ha : IsTorus σ J X Y a) :
    ∃ τ : minParSub X h hJ hW → Fin r → ℝ, Continuous τ ∧ (∀ p q, τ (p * q) = τ p + τ q) ∧
      (∀ t, τ (ha.sub h hJ hW t) = t) ∧ (∀ p (hp : p ∈ minParOne σ J X), τ ⟨p, minParOne_subset hp⟩ = 0) ∧
      ∀ p : minParSub X h hJ hW, p.1 * (a (τ p))⁻¹ ∈ minParOne σ J X :=
  exists_torus_section h hJ hW (minParSub X h hJ hW) (fun _ => Iff.rfl) ha.add ha.onX (ha.sub h hJ hW) (fun _ => rfl)

theorem map_mul_torus (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {a : (Fin r → ℝ) → GAd σ J}
    (ha : IsTorus σ J X Y a) (ν : Measure (minParSub X h hJ hW)) [ν.IsHaarMeasure] (s : Fin r → ℝ) :
    ν.map (· * ha.sub h hJ hW s) = ENNReal.ofReal (Real.exp (2 * (Module.finrank ℚ F : ℝ) * rho2 n s)) • ν :=
  PMod.map_mul_torus_of h hJ hW (minParSub X h hJ hW) (isClosed_minPar h hJ hW) (fun _ hp => hp) (fun _ hp => hp)
    ha.add ha.onX ha.onY ha.onV ha.mem ν s

theorem commute_of_goodPosition (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y)
    {a : (Fin r → ℝ) → GAd σ J} (ha : IsTorus σ J X Y a) {K : Subgroup (GAd σ J)} (hK : IsCompact (K : Set (GAd σ J)))
    (hG : GoodPosition σ J X Y K) {m : GAd σ J} (hm : m ∈ minPar σ J X) (hmK : m ∈ K) (t : Fin r → ℝ) :
    a t * m = m * a t :=
  commute_of_good_position h hJ hW (ha.tor t).1 (ha.onX t) (ha.onY t) (ha.onV t) hK hG hm hmK

end PositivityTheory.ThKR

end
