module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicIsometryTransportUniqueModStabilizer
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FlatSpaceComponents
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicIsometry_transport_unique_mod_stabilizer : ∀ (D : D7) (W Y : HSp D) (L : Lat W) (Λ : Lat Y) (S : Finset (Pl D.host.E)), IsSplitSet S → ∀ (n : ℕ) (be : Pl D.host.E → Matrix (Fin W.rank) (Fin n) (EAf D)) (be' : Pl D.host.E → Matrix (Fin Y.rank) (Fin n) (EAf D)), Submodule.IsFullLattice D.host.E L → (∀ w ∈ S, IsBasisAt W w L (be w)) → ∀ x, IsTransport W Y L Λ S be be' x → ∀ x', IsTransport W Y L Λ S be be' x' ↔ ∃ k, InStabAway W L S k ∧ x' = HMul.hMul x (k.1 : Matrix (Fin W.rank) (Fin W.rank) (EAf D)) := by
  intro D W Y L Λ S hS n be be' hL hbe x hx x'
  first
  | exact GlobalTheory.TransportUnique.transport_unique D W Y L Λ S hS n be be' hL hbe x hx x'
  | exact GlobalTheory.TransportUnique.transport_unique D W Y L Λ S hS n be be' hL.toIsLattice hbe x hx x' 
