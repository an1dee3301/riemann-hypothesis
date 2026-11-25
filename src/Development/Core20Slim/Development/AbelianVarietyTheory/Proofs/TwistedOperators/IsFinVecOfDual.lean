module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.OppositeColumnLifts
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainStepsAreGridArrows
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EquivariantOfWave
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Lattice.Basic
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.IwahoriMembership
open scoped Pointwise TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FlipPath

variable {D : D7}

section Local

variable (e : AE D) (I : Ideal (𝓞 D.host.E)) (ν : (AE D)ˣ →* Circle)

variable {e I}

end Local

theorem isSelfDualC_sgn (ε : Bool) {S : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} (h : IsSelfDualC S Λ) :
    IsSelfDualC (sgn ε S) Λ := by
  cases ε
  · exact h
  · refine ⟨h.1, fun y => (h.2 y).trans (forall₂_congr fun x _ => ?_)⟩
    have e : ∑ i, ∑ j, star (x i) * (neg S).gram i j * y j = -∑ i, ∑ j, star (x i) * S.gram i j * y j := by
      simp [neg_gram, Finset.sum_neg_distrib]
    refine ⟨fun ⟨b, hb⟩ => ⟨-b, ?_⟩, fun ⟨b, hb⟩ => ⟨-b, ?_⟩⟩
    · refine Eq.trans ?_ e.symm
      rw [← hb]; simp
    · have := hb.trans e
      rw [← neg_eq_iff_eq_neg] at this
      rw [← this]; simp

section Fin

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : Node D} {e : AE D} {P : Finset (Pl D.host.E)} {f₀ f : WO S.V T.V → ℂ}

theorem isFinVec_of_own {ε : Bool} (hv : IsVac ψ θ ε S T f₀) (hS : IsSelfDualC S.V S.Λ) (hT : IsSelfDualC T.V T.Λ) (he : IsIdemSum e P)
    {φ : Matrix (Fin T.V.rank) (Fin S.V.rank) (Datum.EAf D) → ℂ} (h : IsDatOwn ψ ε S T e f₀ φ f) : IsFinVec ψ θ ε S T f := by
  obtain ⟨hSB, ⟨Tm, hTm⟩, hall⟩ := h
  rw [hall Tm hTm]
  exact finVec_of_mem_span (S := sgn ε S.V) hv (GlobalTheory.Chain.StepVac.placeModel_span_ne hv.1 (isSelfDualC_sgn ε hS) hT
    (GlobalTheory.PlaceDatum.idemSum_mul_self he) he.2 (GlobalTheory.PlaceDatum.infPart_idemSum he) hTm hSB).1

end Fin

variable {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (G : GridDat R)

end GlobalTheory.FlipPath

end
