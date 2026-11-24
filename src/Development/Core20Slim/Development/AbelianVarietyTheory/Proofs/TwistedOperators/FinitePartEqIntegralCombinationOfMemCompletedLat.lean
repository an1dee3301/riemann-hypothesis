module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrT
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SrcLat
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsApprox
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryPairMapsCompletedHomLatticeOntoTranslate
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StrongApproximationDecomposition
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SatakeDualWeyl.StatementC
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Submonoid.MulAction
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open Matrix

noncomputable section
namespace GlobalTheory.LatExpand

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

variable {D : D7}

theorem finPart_liftFin (y : Af D.host.F ⊗[D.host.F] D.host.E) :
    finPart D (GlobalTheory.LatticeStable.liftFin D y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  | tmul a m => rfl

theorem toEAf_apply (w : Formalism.L2.Theta.AE D) :
    Formalism.IndefR.Datum.toEAf D w = Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (finPart D w) := rfl

theorem toEAf_liftFin (y : Af D.host.F ⊗[D.host.F] D.host.E) :
    Formalism.IndefR.Datum.toEAf D (GlobalTheory.LatticeStable.liftFin D y) =
      Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E y := by
  rw [toEAf_apply, finPart_liftFin]

theorem toEAf_incA' (e : D.host.E) :
    Formalism.IndefR.Datum.toEAf D (incA D e) = Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) e := rfl

theorem exists_integralCombination_of_mem_completedLattice {n : ℕ} (B : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (z : Fin n → Formalism.IndefR.Datum.EAf D) (hz : z ∈ Formalism.L2.Herm.hatL (F := D.host.F) B) :
    ∃ (m : ℕ) (β : Fin m → Formalism.L2.Theta.AE D) (b : Fin m → Fin n → D.host.E),
      (∀ p, finPart D (β p) ∈ intAE D) ∧ (∀ p, b p ∈ B) ∧
      ∀ i, z i = Formalism.IndefR.Datum.toEAf D (∑ p, β p * incA D (b p i)) := by
  unfold Formalism.L2.Herm.hatL Formalism.UG.latS at hz
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    refine ⟨1, fun _ => 1, fun _ => c, fun _ => ?_, fun _ => hc, fun i => ?_⟩
    · exact (GlobalTheory.SplitDec.int_iff 1).2 (by rw [map_one]; exact one_mem _)
    · rw [Fin.sum_univ_one, one_mul, toEAf_incA']
  | zero =>
    refine ⟨0, Fin.elim0, Fin.elim0, fun p => p.elim0, fun p => p.elim0, fun i => ?_⟩
    rw [Finset.univ_eq_empty, Finset.sum_empty, map_zero]; rfl
  | add x y _ _ hx hy =>
    obtain ⟨m, β, b, hβ, hb, he⟩ := hx
    obtain ⟨m', β', b', hβ', hb', he'⟩ := hy
    refine ⟨m + m', Fin.append β β', Fin.append b b', fun p => ?_, fun p => ?_, fun i => ?_⟩
    · refine Fin.addCases (fun q => ?_) (fun q => ?_) p
      · rw [Fin.append_left]; exact hβ q
      · rw [Fin.append_right]; exact hβ' q
    · refine Fin.addCases (fun q => ?_) (fun q => ?_) p
      · rw [Fin.append_left]; exact hb q
      · rw [Fin.append_right]; exact hb' q
    · rw [Fin.sum_univ_add, map_add (f := _), Pi.add_apply, he i, he' i]
      simp only [Fin.append_left, Fin.append_right]
  | smul r x _ hx =>
    obtain ⟨m, β, b, hβ, hb, he⟩ := hx
    set y := (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm (r : Formalism.IndefR.Datum.EAf D)
    have hy : Formalism.IndefR.Datum.toEAf D (GlobalTheory.LatticeStable.liftFin D y) = r := by
      rw [toEAf_liftFin, AlgEquiv.apply_symm_apply]
    have hyi : finPart D (GlobalTheory.LatticeStable.liftFin D y) ∈ intAE D :=
      (GlobalTheory.SplitDec.int_iff _).2 (by rw [hy]; exact r.2)
    refine ⟨m, fun p => GlobalTheory.LatticeStable.liftFin D y * β p, b, fun p => ?_, hb, fun i => ?_⟩
    · rw [map_mul]; exact GlobalTheory.FinPl.FrameLat.mul_mem_intAE hyi (hβ p)
    · simp only [mul_assoc, ← Finset.mul_sum, map_mul, hy]
      rw [Pi.smul_apply, he i, Subring.smul_def, smul_eq_mul]

theorem expand {n : ℕ} (B : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (Y : Fin n → Formalism.L2.Theta.AE D)
    (hY : (fun i => Formalism.IndefR.Datum.toEAf D (Y i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) B) :
    ∃ (m : ℕ) (β : Fin m → Formalism.L2.Theta.AE D) (b : Fin m → Fin n → D.host.E),
      (∀ p, finPart D (β p) ∈ intAE D) ∧ (∀ p, b p ∈ B) ∧
      ∀ i, finPart D (Y i) = finPart D (∑ p, β p * incA D (b p i)) := by
  obtain ⟨m, β, b, hβ, hb, he⟩ := exists_integralCombination_of_mem_completedLattice B _ hY
  refine ⟨m, β, b, hβ, hb, fun i => ?_⟩
  have h := he i
  rw [toEAf_apply, toEAf_apply] at h
  exact (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective h

theorem finPart_eq_int_comb_of_mem_hatL : ∀ {D : D7} {n : ℕ} (B : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (Y : Fin n → Formalism.L2.Theta.AE D),
    (fun i => Formalism.IndefR.Datum.toEAf D (Y i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) B →
    ∃ (m : ℕ) (β : Fin m → Formalism.L2.Theta.AE D) (b : Fin m → Fin n → D.host.E),
      (∀ p, finPart D (β p) ∈ intAE D) ∧ (∀ p, b p ∈ B) ∧
      ∀ i, finPart D (Y i) = finPart D (∑ p, β p * incA D (b p i)) := fun B Y hY => expand B Y hY

end GlobalTheory.LatExpand
