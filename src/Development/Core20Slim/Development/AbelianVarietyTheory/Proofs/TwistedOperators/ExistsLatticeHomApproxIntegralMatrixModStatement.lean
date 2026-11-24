module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLatticeHomApproxIntegralMatrixMod
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.NodeAgree
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHatMxHomLatIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_latticeHom_approx_integralMatrix_mod : ∀ {D : D7} {m n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)) (β : GL (Fin n) (EAf D)) (β' : GL (Fin m) (EAf D)), Formalism.L2.DIV.IsFrame β Λ → Formalism.L2.DIV.IsFrame β' Λ' → ∀ (I : Ideal (𝓞 D.host.E)), I ≠ ⊥ → ∀ (N : Matrix (Fin m) (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E)), ∃ x₀ ∈ GlobalTheory.ChiGrid.homLat Λ Λ', ∀ i j, ∃ s ∈ Formalism.L2.DIV.idS D.host.F I, (s : EAf D) = HMul.hMul (HMul.hMul (β'⁻¹).val (x₀.map (eToEAf D))) β.val i j - (N i j : EAf D) := by
  first | exact @GlobalTheory.FunObj.HatFrame.homLat_approx_mod | exact GlobalTheory.FunObj.HatFrame.homLat_approx_mod | (intros; apply GlobalTheory.FunObj.HatFrame.homLat_approx_mod <;> assumption)
