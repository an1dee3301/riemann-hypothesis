module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotropicPartRationalCharactersAdelicMatrices
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
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
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropic_part_rational_characters_adelic_matrices : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → (∀ (a : Matrix (Fin W.rank) (Fin r) D.host.E), Continuous fun t : Mx D W.rank r => ψ (symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D))))) ∧ (∀ (a : Matrix (Fin W.rank) (Fin r) D.host.E) t s, ψ (symplO V W (isoPart V W C' (t + s)) (isoPart V W C (a.map (incA D)))) = ψ (symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D)))) * ψ (symplO V W (isoPart V W C' s) (isoPart V W C (a.map (incA D))))) ∧ (∀ (a b : Matrix (Fin W.rank) (Fin r) D.host.E) t, ψ (symplO V W (isoPart V W C' t) (isoPart V W C ((a + b).map (incA D)))) = ψ (symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D)))) * ψ (symplO V W (isoPart V W C' t) (isoPart V W C (b.map (incA D))))) ∧ (∀ t, (∀ a : Matrix (Fin W.rank) (Fin r) D.host.E, ψ (symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D)))) = 1) ↔ t ∈ ratMx D W.rank r) ∧ ∀ a : Matrix (Fin W.rank) (Fin r) D.host.E, (∀ t, ψ (symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D)))) = 1) → a = 0 := by
  first | exact @GlobalTheory.IsoDualChars.chars | exact GlobalTheory.IsoDualChars.chars | (intros; apply GlobalTheory.IsoDualChars.chars <;> assumption)
