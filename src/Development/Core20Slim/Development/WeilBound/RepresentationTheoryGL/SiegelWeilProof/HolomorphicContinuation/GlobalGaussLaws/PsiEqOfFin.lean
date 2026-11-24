module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocalL2IsometryAlt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicTraceSupportedAtSplitPlace
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTraceEqAddStar
public import Development.Core20Slim.Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ContinuousSplitInv
public import Development.Core20Slim.Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ContinuousPsiT
public import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AtTauExUniqueHolds
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.StdUnn
open Formalism.IndefR.Eqv (psiT psiT_sigR thetaC eq_thetaC)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.FTP

variable {D : D7}


set_option synthInstance.maxHeartbeats 400000 in
theorem incl_trA (z : AE D) : algebraMap (AF D.host.F) (AE D) (trA z) = z + cA D z := by
  induction z using TensorProduct.induction_on with
  | zero => simp [trA]
  | tmul a e =>
    simp only [trA]
    rw [GlobalTheory.SplitAdeleTrace.trace_baseChange_tmul (AF D.host.F) a e]
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    have h : (Algebra.trace D.host.F D.host.E e : D.host.E) = e + star e := GlobalTheory.TraceAddStar.trace_eq_add_star e
    calc (a * algebraMap D.host.F (AF D.host.F) (Algebra.trace D.host.F D.host.E e)) ⊗ₜ[D.host.F] (1 : D.host.E)
        = a ⊗ₜ[D.host.F] ((Algebra.trace D.host.F D.host.E e : D.host.F) : D.host.E) := by
          rw [mul_comm, ← Algebra.smul_def, TensorProduct.smul_tmul, Algebra.smul_def, mul_one]; rfl
      _ = a ⊗ₜ[D.host.F] e + cA D (a ⊗ₜ[D.host.F] e) := by
          rw [h, TensorProduct.tmul_add]; rfl
  | add x y hx hy =>
    simp only [trA, map_add (f := _)] at hx hy ⊢
    rw [hx, hy]; abel


set_option synthInstance.maxHeartbeats 400000 in
theorem psi_eq_of_fin {θ : InfFam D} (hθ : IsInfFam θ) {ψ : AddChar (AF D.host.F) ℂ} {l : D.what₂.Tau → ℝ}
    (hl : HasRealPar ψ θ l) (a : AF D.host.F) (ha : finPart D (algebraMap (AF D.host.F) (AE D) a) = 0) :
    ψ a = Complex.exp (2 * Real.pi * Complex.I * ∑ τ, (l τ : ℂ) * psiT D τ (algebraMap (AF D.host.F) (AE D) a)) := by
  have hsnd : sndA D.host.F a = 0 := by
    apply Algebra.TensorProduct.includeLeft_injective (S := Af D.host.F) (algebraMap D.host.F D.host.E).injective
    rw [map_zero]
    exact ha
  have ha' : a = pairA D.host.F (fstA D.host.F a) 0 := Prod.ext rfl hsnd
  have h1 : ψ a = psiInf D.host.F ψ (fstA D.host.F a) := by
    conv_lhs => rw [ha']
    rfl
  rw [h1, hl, eq_thetaC D hθ]
  rfl


set_option synthInstance.maxHeartbeats 400000 in
theorem psi_trA_tau {θ : InfFam D} (hθ : IsInfFam θ) {ψ : AddChar (AF D.host.F) ℂ} {l : D.what₂.Tau → ℝ}
    (hl : HasRealPar ψ θ l) (τ : D.what₂.Tau) (z : AE D) (hz : ∀ τ', τ' ≠ τ → psiT D τ' z = 0)
    (hzf : finPart D z = 0) :
    ψ (trA z) = Complex.exp (Complex.I * ((4 * Real.pi * l τ : ℝ) : ℂ) * ((psiT D τ z).re : ℂ)) := by
  have hfin : finPart D (algebraMap (AF D.host.F) (AE D) (trA z)) = 0 := by
    rw [incl_trA, RingHom.map_add (f := _), hzf, cA, Formalism.IndefR.Eqv.finPart_sigR, hzf, RingHom.map_zero, add_zero]
  rw [psi_eq_of_fin hθ hl _ hfin, incl_trA]
  have hs : ∑ τ', (l τ' : ℂ) * psiT D τ' (z + cA D z) = (l τ : ℂ) * (2 * ((psiT D τ z).re : ℂ)) := by
    rw [Finset.sum_eq_single τ]
    · rw [RingHom.map_add (f := _), cA, psiT_sigR, Complex.add_conj]; push_cast; ring
    · intro τ' _ hne
      rw [RingHom.map_add (f := _), cA, psiT_sigR, hz τ' hne, map_zero, add_zero, mul_zero]
    · intro h; exact absurd (Finset.mem_univ τ) h
  rw [hs]
  congr 1
  push_cast
  ring

end PositivityTheory.Rg.Sw.Glob.FTP
