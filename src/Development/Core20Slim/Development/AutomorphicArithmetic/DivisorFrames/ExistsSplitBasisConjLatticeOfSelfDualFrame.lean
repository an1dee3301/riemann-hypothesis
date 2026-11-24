module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicArithmetic.LocalEmbeddings.StageGeoDefs
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.Core20Slim.Development.AutomorphicArithmetic.DivisorFrames.ExistsMaxCompactEqFrameGramSplitBasis
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianLatticeLocalBases
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.Core20Slim.Development.AutomorphicArithmetic.LocalEmbeddings.ComplEquivEvW
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ExistsNatSmulSingle
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Ring.Units
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Geo piW chrW unifAt latAtV At SInf)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime IsSplitBasis)
open GlobalTheory.BotMatch (evW)
open GlobalTheory.StageGeo
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.exists_splitBasis_conj_lattice_of_selfDual_frame :
    ∀ (D : D7) (S : HSp D) (Λ L : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (β : GL (Fin S.rank) (EAf D)),
        IsSelfDualC S Λ → Formalism.L2.DIV.IsFrame β Λ → (∀ y, y ∈ L ↔ star y ∈ Λ) →
        ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (t : D.host.E →ₐ[D.host.F] Fv D.host.F v), ∃ b : GL (Fin S.rank) (Fv D.host.F v),
          IsSplitBasis t L b ∧ IsSplitBasis t L (-b) ∧ (b⁻¹).1 = (S.gram.map t * β.1.map (evW t))ᵀ := by
  intro D S Λ L β hΛ hβ hL v t
  obtain rfl : L = GlobalTheory.TripleSpaceW.conjSub Λ := by
    ext y
    rw [hL, GlobalTheory.TripleSpaceW.mem_conjSub]
  haveI := GlobalTheory.TripleSpaceW.conjSub_isFullLattice
    (Formalism.IndefR.Fin.PDA.selfDual_isFullLattice S Λ hΛ)
  obtain ⟨b₀, hb₀⟩ : ∃ b : GL (Fin S.rank) (Fv D.host.F v),
      IsSplitBasis t (GlobalTheory.TripleSpaceW.conjSub Λ) b :=
    GlobalTheory.AdelicU.exists_isSplitBasis t (GlobalTheory.TripleSpaceW.conjSub Λ) (GlobalTheory.AdelicU.isCMExt_host D)
  obtain ⟨g, hg, hgv⟩ := UpperTheory.exists_maxCompact_eq_frame_gram_splitBasis D S Λ β hΛ hβ v t b₀ hb₀
  rw [← (GlobalTheory.AdelicU.GLint_eq_KO_and_princ_eq_KOne v S.rank).1] at hg
  have h1 : IsSplitBasis t (GlobalTheory.TripleSpaceW.conjSub Λ) (b₀ * g⁻¹) := by
    rw [hb₀.iff_mem_GLint, inv_mul_cancel_left]
    exact inv_mem hg
  refine ⟨b₀ * g⁻¹, h1, fun u => ?_, ?_⟩
  · have := h1 (-u)
    simp only [Pi.neg_apply, neg_mem_iff, Matrix.mulVec_neg] at this
    rw [Units.val_neg, Matrix.neg_mulVec, neg_mem_iff]
    exact this
  · rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, hgv, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one,
      Matrix.transpose_mul]
