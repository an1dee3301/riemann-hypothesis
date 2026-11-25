module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPlaceStabilizerPartialProductsFiniteSet
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
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
public import Init.Data.List.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_placeStabilizer_partialProducts_finiteSet : ∀ (D : D7) (S : HSp D) (L : Lat S) (P : Pl D → Prop) (κ : GA D S), IsSelfDualC S L → InK S L P κ → ∀ Fs : Finset (Pl D), ∃ l : List (GA D S), (∀ y ∈ l, ∃ v, P v ∧ InK S L (· = v) y) ∧ (∀ i j, infPart D (Formalism.L2.Theta.mt S l.prod i j) = infPart D (Formalism.L2.Theta.mt S κ i j)) ∧ (∀ w ∈ Fs, ∀ i j, GlobalTheory.FinPl.compAt D w (Formalism.L2.Theta.mt S l.prod i j) = GlobalTheory.FinPl.compAt D w (Formalism.L2.Theta.mt S κ i j)) ∧ ∀ w, w ∉ Fs → ∀ i j, GlobalTheory.FinPl.compAt D w (Formalism.L2.Theta.mt S l.prod i j) = GlobalTheory.FinPl.compAt D w ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) := by
  first | exact @GlobalTheory.PlaceProducts.finite_place_products | exact GlobalTheory.PlaceProducts.finite_place_products | (intros; apply GlobalTheory.PlaceProducts.finite_place_products <;> assumption)
