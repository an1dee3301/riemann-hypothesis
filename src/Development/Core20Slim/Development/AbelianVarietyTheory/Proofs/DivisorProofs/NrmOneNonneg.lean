module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjPlInvolutive
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbLLMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Formalism.LocalRingCardinality.DataCoeff
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.Divisibility.LiftLat
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Order.Lemmas
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.CharP.IntermediateField
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.RelClasses
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

namespace GlobalTheory.KerConjMean

open scoped ComplexOrder

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem nrm_one_nonneg {D : D7} {n : ℕ} (lam : D.what₂.Tau → DomWeight n) (v : VV ℂ lam) :
    0 ≤ nrm lam (fun _ => 1) v := by
  by_cases hv : v = 0
  · simp [nrm, hv]
  · exact (Complex.le_def.1 (GlobalTheory.CoefModel.pairK_pos lam (fun _ => Matrix.PosDef.one) v hv).le).1

section Claims

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (C b C1 : ℝ)

def RatRowAt : Prop := ∀ Φ β d, Occurs ch.S.toGridChoice A.μ0 Φ β d → ∀ (c : ch.S.Classes A.μ0 Φ β) (i : Fin D.R.m),
  ∃ f : VV D.what₂.LL (wt ch.G (.grid i D.R.m)) →ₗ[D.what₂.LL] VV D.what₂.LL (wt ch.G (.grid (i + 1) D.R.m)), ∀ u,
    ch.S.Z.kkMap 1 (d.2 i) (ch.S.ptRow c i) (ch.S.ptRow c (i + 1)) (GlobalTheory.CoefModel.mapVV D.what₂.embLL _ u) =
      GlobalTheory.CoefModel.mapVV D.what₂.embLL _ (f u)

def ConjRowAt : Prop := ∃ a0 nD Gd : ℝ, 0 ≤ a0 ∧ 0 ≤ nD ∧ 0 ≤ Gd ∧ 2 * a0 + (nD + Gd) * C1 * Real.log b ≤ aOne ch.G C b ∧
  ∀ Φ β d, Occurs ch.S.toGridChoice A.μ0 Φ β d → ∀ (c : ch.S.Classes A.μ0 Φ β) (i : Fin D.R.m)
    (f : VV D.what₂.LL (wt ch.G (.grid i D.R.m)) →ₗ[D.what₂.LL] VV D.what₂.LL (wt ch.G (.grid (i + 1) D.R.m))),
    (∀ u, ch.S.Z.kkMap 1 (d.2 i) (ch.S.ptRow c i) (ch.S.ptRow c (i + 1)) (GlobalTheory.CoefModel.mapVV D.what₂.embLL _ u) =
      GlobalTheory.CoefModel.mapVV D.what₂.embLL _ (f u)) →
    ∀ (σ : D.what₂.LL →+* ℂ), ∀ ρ ∈ ext D ch.S.Z.δ ch.S.Z.t0 σ, ∀ u (B : ℝ),
      nrm _ (fun _ => 1) (GlobalTheory.CoefModel.mapVV (σ.comp (starRingEnd D.what₂.LL)) _ u) ≤ B →
      nrm _ (fun _ => 1) (GlobalTheory.CoefModel.mapVV (σ.comp (starRingEnd D.what₂.LL)) _ (f u)) ≤
        Real.exp (a0 + nD * hArea D ch.S.Z.δ ch.S.Z.t0 ρ + Gd * hTh D ch.S.Z.δ ch.S.Z.t0 ρ) * B

end Claims

end GlobalTheory.KerConjMean

end
