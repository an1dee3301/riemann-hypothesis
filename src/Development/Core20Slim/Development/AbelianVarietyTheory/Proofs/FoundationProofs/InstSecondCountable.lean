module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.BlockOrderedSquareIntegrable
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Opposite
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Opposites
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Homeomorph.Lemmas
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.HolDS

variable {p q : ℕ}

instance t2Space_cuspAdeles (T : GrpData p q) : T2Space T.G := T.emb.t2Space

instance instSecondCountable (T : GrpData p q) : SecondCountableTopology T.G := by
  haveI : SecondCountableTopology (Mat p q) := inferInstanceAs (SecondCountableTopology (Ix p q → Ix p q → ℂ))
  haveI : SecondCountableTopology (Mat p q)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : SecondCountableTopology (GL (Ix p q) ℂ) := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : SecondCountableTopology ℂˣ := Units.isEmbedding_val₀.secondCountableTopology
  exact T.emb.secondCountableTopology

instance instLocallyCompact (T : GrpData p q) : LocallyCompactSpace T.G := by
  haveI : LocallyCompactSpace (Mat p q) := inferInstanceAs (LocallyCompactSpace (Ix p q → Ix p q → ℂ))
  exact (GlobalTheory.RealPar.SqInt.isClosedEmbedding_emb T).locallyCompactSpace

end GlobalTheory.HolDS

end
