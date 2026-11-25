module

public import Mathlib
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.OfUnfolding
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PArchUnimodular
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PMajorantStabCompact
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PLineStabHaar
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PSemidirectCovering
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PStabilizerLevi
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulus
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentCocompact
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PCongruenceLift
public import Development.Core20Slim.GroundTheory.AutomorphicForms.HermitianSpaces
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Assembly
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Objects
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StUnipotentCentral
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StUnipotentCoordProper
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StUnipotentHorizontal
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Statements
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsComplementForm
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsLineEigenvalue
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsSemidirectHaar
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsStabilizerLevi
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsTorusEmbedding
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsTorusModulus
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsUnitsInvHaar
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsVecFixGroup
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Separation.GDelta
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped Pointwise ComplexOrder ENNReal NumberField.AdeleRing

noncomputable section

universe u

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]

variable
    (hTE : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), TorusEmbedding.Statement h v)
    (hLE : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), LineEigenvalue.Statement h v)
    (hTM : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), TorusModulus.Statement h v)
    (hSH : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), SemidirectHaar.Statement (archUnitary h v) (InfinitePlace E → ℂˣ))
    (hUI : UnitsInvHaar.Statement (InfinitePlace E))
    (hCP : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), UnipotentCoordProper.Statement h v)
    (hUH : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), UnipotentHorizontal.Statement h v)
    (hUZ : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), UnipotentCentral.Statement h v)

variable {W : Type u} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (h : HermitianForm F E W) (v : Basis ι E W)
variable (hTE' : TorusEmbedding.Statement h v) (hLE' : LineEigenvalue.Statement h v)
    (hTM' : TorusModulus.Statement h v)
    (hSH' : SemidirectHaar.Statement (archUnitary h v) (InfinitePlace E → ℂˣ))
    (hCP' : UnipotentCoordProper.Statement h v) (hUH' : UnipotentHorizontal.Statement h v)
    (hUZ' : UnipotentCentral.Statement h v)

include hTE hLE hTM hSH hUI hCP hUH hUZ hTE' hLE' hTM' hSH' hCP' hUH' hUZ'

theorem ScalingLaw.of_remaining : ScalingLaw.Statement h v :=
  ScalingLaw.of_open
    (fun _ _ _ _ h _ v => ArchUnimodular.proof h v)
    (fun _ _ _ _ h _ v => MajorantStabCompact.proof h v)
    (fun W _ _ _ h n v => LineStabHaar.proof h v (WittPartner.full h) (VecAtNeZero.full v)
      (hTE W h n v) (hLE W h n v) (hTM W h n v) (hSH W h n v) hUI)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ => SemidirectCovering.proof _ _ _)
    (fun _ _ _ _ h _ v => StabilizerLevi.proof h v)
    (fun _ _ _ _ h _ v => UnipotentModulus.proof h v)
    (fun W _ _ _ h n v => UnipotentCocompact.proof h v (hCP W h n v) (hUH W h n v) (hUZ W h n v))
    (fun _ _ _ _ h => CongruenceLift.proof h)
    h v (fun _ _ _ _ _ => SemidirectCovering.proof _ _ _) (StabilizerLevi.proof h v)
    (UnipotentModulus.proof h v) (UnipotentCocompact.proof h v hCP' hUH' hUZ')
    (ArchUnimodular.proof h v) (MajorantStabCompact.proof h v)
    (LineStabHaar.proof h v (WittPartner.full h) (VecAtNeZero.full v) hTE' hLE' hTM' hSH' hUI)

theorem ArithmeticCovolumeFinite.of_remaining : ArithmeticCovolumeFinite.Statement h v :=
  ArithmeticCovolumeFinite.of_open
    (fun _ _ _ _ h _ v => ArchUnimodular.proof h v)
    (fun _ _ _ _ h _ v => MajorantStabCompact.proof h v)
    (fun W _ _ _ h n v => LineStabHaar.proof h v (WittPartner.full h) (VecAtNeZero.full v)
      (hTE W h n v) (hLE W h n v) (hTM W h n v) (hSH W h n v) hUI)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ => SemidirectCovering.proof _ _ _)
    (fun _ _ _ _ h _ v => StabilizerLevi.proof h v)
    (fun _ _ _ _ h _ v => UnipotentModulus.proof h v)
    (fun W _ _ _ h n v => UnipotentCocompact.proof h v (hCP W h n v) (hUH W h n v) (hUZ W h n v))
    (fun _ _ _ _ h => CongruenceLift.proof h)
    h v (fun _ _ _ _ _ => SemidirectCovering.proof _ _ _) (StabilizerLevi.proof h v)
    (UnipotentModulus.proof h v) (UnipotentCocompact.proof h v hCP' hUH' hUZ')
    (ArchUnimodular.proof h v) (MajorantStabCompact.proof h v)
    (LineStabHaar.proof h v (WittPartner.full h) (VecAtNeZero.full v) hTE' hLE' hTM' hSH' hUI)

theorem AdelicCovolumeFinite.of_remaining : AdelicCovolumeFinite.Statement h v :=
  AdelicCovolumeFinite.of_open
    (fun _ _ _ _ h _ v => ArchUnimodular.proof h v)
    (fun _ _ _ _ h _ v => MajorantStabCompact.proof h v)
    (fun W _ _ _ h n v => LineStabHaar.proof h v (WittPartner.full h) (VecAtNeZero.full v)
      (hTE W h n v) (hLE W h n v) (hTM W h n v) (hSH W h n v) hUI)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ => SemidirectCovering.proof _ _ _)
    (fun _ _ _ _ h _ v => StabilizerLevi.proof h v)
    (fun _ _ _ _ h _ v => UnipotentModulus.proof h v)
    (fun W _ _ _ h n v => UnipotentCocompact.proof h v (hCP W h n v) (hUH W h n v) (hUZ W h n v))
    (fun _ _ _ _ h => CongruenceLift.proof h)
    h v (fun _ _ _ _ _ => SemidirectCovering.proof _ _ _) (StabilizerLevi.proof h v)
    (UnipotentModulus.proof h v) (UnipotentCocompact.proof h v hCP' hUH' hUZ')
    (ArchUnimodular.proof h v) (MajorantStabCompact.proof h v)
    (LineStabHaar.proof h v (WittPartner.full h) (VecAtNeZero.full v) hTE' hLE' hTM' hSH' hUI)

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
