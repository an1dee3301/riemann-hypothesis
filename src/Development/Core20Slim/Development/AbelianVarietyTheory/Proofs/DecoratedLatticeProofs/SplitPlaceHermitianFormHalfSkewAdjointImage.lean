module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFrameCol
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianLinkMapAdditiveRationalEquivariant
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontrivia
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergFrameHalfInverse
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialFourierInversion
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Basic.Unique
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Defs.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KappaSplitPairing

theorem hO_ofAdj_right {D : D7} (L S : HSp D) (X : WO L S) (z : Mx D L.rank S.rank) :
    hO L S X (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S z) = incA D (D.host.xi0⁻¹) * (z ⬝ X).trace := by
  rw [hO_eq_trace, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj]
  simp only [adj_smul, adj_mul, adj_adj, adj_gA, adj_giA, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc,
    giA_gA_cancel, gA_giA_cancel, trace_smul, smul_eq_mul]
  rw [GlobalTheory.DualPairCheck.cA_incA, star_neg, star_inv₀, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, inv_neg, neg_neg]

theorem map_trace {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {m : ℕ} (M : Mx D m m) : p.π M.trace = (M.map p.π).trace := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, Matrix.diag, map_sum, Matrix.map_apply]

theorem key : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (L S L'' : HSp D) (ζ : Fin L.rank → D.host.E) (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (s : k) (z₀ : Fin L''.rank → k), s ≠ 0 → τ.map p.pr *ᵥ z₀ = (-(p.xi * s)) • (fun i => p.pr (ζ i)) → ∀ (n : Type) [Fintype n] [DecidableEq n] (FS : Frame k S.rank n) (FL : Frame k L.rank Unit) (FL'' : Frame k L''.rank Unit), (∀ r, FL.β r () = s * p.pr (ζ r)) → (∀ r, FL''.β r () = z₀ r) → ∀ (x : Matrix Unit n k) (a : Matrix n Unit k), p.π (hO L S (p.up FL FS a) (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L''.rank) * p.up FS FL'' x))) = -(∑ r, x () r * a r ()) := by
  intro D k _ _ _ _ p L S L'' ζ τ s z₀ hs hτ n _ _ FS FL FL'' hFL hFL'' x a
  rw [hO_ofAdj_right, map_mul, map_trace]
  have hxi : p.π (incA D D.host.xi0⁻¹) = p.xi⁻¹ := by
    change (p.π.comp (incA D)) D.host.xi0⁻¹ = ((p.π.comp (incA D)) D.host.xi0)⁻¹
    exact map_inv₀ _ _
  have hr : (rat τ : Mx D L.rank L''.rank).map p.π = τ.map p.pr := rfl
  have hu : ∀ {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D}
      (F₁ : Frame k S.rank Y') (F₂ : Frame k T.rank Y) (m : Matrix Y Y' k),
      (p.up F₁ F₂ m : Mx D T.rank S.rank).map p.π = F₂.β * m * F₁.γ := by
    intro Y Y' _ _ _ _ S T F₁ F₂ m
    ext i j
    exact p.π_ι _
  have hcol : τ.map p.pr * FL''.β = (-p.xi) • FL.β := by
    ext r u
    have h1 := congrFun hτ r
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h1
    simp only [Matrix.mul_apply, hFL'', Matrix.smul_apply, smul_eq_mul, hFL, h1]
    ring
  have hγ : FL.γ * (τ.map p.pr * FL''.β) = (-p.xi) • (1 : Matrix Unit Unit k) := by
    rw [hcol, Matrix.mul_smul, FL.γβ]
  rw [hxi, Matrix.map_mul, Matrix.map_mul, hr, hu, hu]
  have e1 : τ.map p.pr * (FL''.β * x * FS.γ) * (FS.β * a * FL.γ) = (τ.map p.pr * FL''.β) * x * a * FL.γ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc FS.γ, FS.γβ, Matrix.one_mul]
  rw [e1, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hγ]
  have hx := Witness.xi_ne p
  simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, smul_eq_mul, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Finset.univ_unique, Finset.sum_singleton]
  simp only [Matrix.smul_apply, smul_eq_mul, neg_mul, Finset.sum_neg_distrib, mul_assoc, ← Finset.mul_sum, mul_neg,
    inv_mul_cancel_left₀ hx]

end GlobalTheory.KappaSplitPairing
