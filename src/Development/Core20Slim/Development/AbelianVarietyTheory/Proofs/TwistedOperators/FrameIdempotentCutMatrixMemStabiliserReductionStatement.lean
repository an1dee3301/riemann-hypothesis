module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameIdempotentCutMatrixMemStabiliserReduction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameIdempotentCutMatrix_mem_stabiliser_reduction : ∀ {D : D7} (n : ℕ) (β γ y : GL (Fin n) (EAf D)) (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z → IsIntM (toEAf D e • γ.1) → IsIntM (toEAf D e • (γ⁻¹ : GL (Fin n) (EAf D)).1) → IsIntM (toEAf D (cA D e) • γ.1) → IsIntM (toEAf D (cA D e) • (γ⁻¹ : GL (Fin n) (EAf D)).1) → y.1 = β.1 * (toEAf D (e + cA D e) • γ.1 + (1 - toEAf D (e + cA D e)) • (1 : Matrix (Fin n) (Fin n) (EAf D))) * (β⁻¹ : GL (Fin n) (EAf D)).1 → y ∈ St β ∧ ∀ PP ∈ Z, ((redFn β PP y : GL (Fin n) (kP PP)) : Matrix (Fin n) (Fin n) (kP PP)) = redM PP (toEAf D e • γ.1) := by
  first | exact @GlobalTheory.FrameIdem.cut_mem_St_red | exact GlobalTheory.FrameIdem.cut_mem_St_red | (intros; apply GlobalTheory.FrameIdem.cut_mem_St_red <;> assumption)
