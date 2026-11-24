module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenSubgroupHalfCharactersSeparate
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfSymplZeroRight
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceHalfAdelicMatrixAddSubgroup
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.HalfAverage
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_subgroup_half_characters_separate : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (W : HSp D) (r : ℕ) (e : AE D), IsSplitIdem D e → ∀ U : AddSubgroup (halfMx (cA D e) W.rank r), IsOpen (U : Set (halfMx (cA D e) W.rank r)) → ∃ L : AddSubgroup (halfMx (cA D e) W.rank r), IsOpen (L : Set (halfMx (cA D e) W.rank r)) ∧ L ≤ U ∧ ∀ x, x ∉ L → ∃ a : halfMx e W.rank r, (∀ l ∈ L, ψ (halfSympl W (a : Mx D W.rank r) (l : Mx D W.rank r)) = 1) ∧ ψ (halfSympl W (a : Mx D W.rank r) (x : Mx D W.rank r)) ≠ 1 := by
  first | exact @GlobalTheory.HalfSeparate.exists_open_separated | exact GlobalTheory.HalfSeparate.exists_open_separated | (intros; apply GlobalTheory.HalfSeparate.exists_open_separated <;> assumption)
