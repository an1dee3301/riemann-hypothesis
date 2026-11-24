module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharOfTrace
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharFinitePartRationalEqExpTrace
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RationalHermitianRankOneLatticeSelfDual
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SmulMemOfIsIntegral
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsInvariantNatLengthLattice
public import Development.Core20Slim.ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatA
public import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasSign
public import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.FramesExistOfDiagonalTypePlaces
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Basis.Submodule
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate

namespace GlobalTheory.Ker.Inhab

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA

variable {D : D7}















theorem selfDual_diag {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ} (neg : Fin N → Bool)
    (G : Matrix (Fin N) (Fin N) E) (hG : ∀ i j, G i j = if i = j then (Examples₂.sgn (neg i) : E) else 0)
    (y : Fin N → E) : y ∈ Examples₂.stdLat N ↔
      ∀ x ∈ Examples₂.stdLat (E := E) N, ∃ b : 𝓞 E, (b : E) = ∑ i, ∑ j, star (x i) * G i j * y j := by
  have hm : ∀ x : Fin N → E, x ∈ Examples₂.stdLat N ↔ ∀ i, IsIntegral ℤ (x i) := fun x => by
    rw [Examples₂.stdLat, Module.Basis.mem_span_iff_repr_mem]
    exact forall_congr' fun i => ⟨fun ⟨b, hb⟩ => by rw [← show _ = x i from hb]; exact b.2, fun h => ⟨⟨_, h⟩, rfl⟩⟩
  have hs : ∀ b, IsIntegral ℤ (Examples₂.sgn b : E) := fun b => by
    cases b
    · exact isIntegral_one
    · exact isIntegral_one.neg
  have hf : ∀ x : Fin N → E, ∑ i, ∑ j, star (x i) * G i j * y j = ∑ i, star (x i) * Examples₂.sgn (neg i) * y i := by
    intro x
    simp [hG]
  simp only [hf]
  refine (hm y).trans ⟨fun h x hx => ?_, fun h i => ?_⟩
  · have : IsIntegral ℤ (∑ i, star (x i) * Examples₂.sgn (neg i) * y i) :=
      IsIntegral.sum _ fun i _ => ((Examples₂.star_isIntegral _ ((hm x).1 hx i)).mul (hs _)).mul (h i)
    exact ⟨⟨_, this⟩, rfl⟩
  · obtain ⟨b, hb⟩ := h (Pi.single i 1) (Submodule.subset_span ⟨i, by simp⟩)
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)] at hb
    have : y i = Examples₂.sgn (neg i) * (b : E) := by
      rw [hb, Pi.single_eq_same, star_one, one_mul, ← mul_assoc, Examples₂.sgn_mul_self, one_mul]
    rw [this]
    exact (hs _).mul b.2






end GlobalTheory.Ker.Inhab

end
