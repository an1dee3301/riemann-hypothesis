module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteSupport
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.BarMatrix
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.KTypeExtension
public import Formalism.FormalDegreeBessel.StatementDS
public import Formalism.FormalDegreeBessel.StatementG
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedType
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.Subspace
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Submodule
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Nontrivial.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift

namespace GlobalTheory.Chain.IoLift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_isKAct_of_stable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    (hs : ∀ x ∈ kFin M τ, x ∈ GlobalTheory.SmVec.smSub (gramAt D V τ) (M.rep τ))
    (hd : ∀ X ∈ lieAt V τ, ∀ x ∈ kFin M τ, dRep (M.rep τ) X x ∈ kFin M τ) :
    ∃ a : Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (kFin M τ), IsKAct M τ a := by
  have hU : IsUnit (M.fr τ) := M.fr_unit τ
  have hG : IsUnit (gramAt D V τ) := GlobalTheory.SmVec.gram_unit hU (M.fr_gram τ)
  have hπ := GlobalTheory.SmVec.isURepOn_trRep hU (M.fr_gram τ) (M.ds τ).2.2.1
  refine ⟨fun X => if hX : X ∈ lieAt V τ then
    { toFun := fun v => ⟨dRep (M.rep τ) X v, hd X hX v v.2⟩
      map_add' := fun v w => Subtype.ext (GlobalTheory.SmVec.dRep_add (hs v v.2) (hs w w.2) hX)
      map_smul' := fun c v => Subtype.ext (GlobalTheory.SmVec.dRep_smul c (hs v v.2) hX) } else 0, ⟨?_, ?_⟩⟩
  · intro X hX v
    rw [dite_eq_left hX]
    exact GlobalTheory.SmVec.hasDerivAt_dRep (hs v v.2) hX
  · intro X hX v w
    rw [dite_eq_left hX, Submodule.coe_inner, Submodule.coe_inner]
    have key : ⟪(v : M.H τ), dRep (M.rep τ) X w⟫_ℂ = -⟪dRep (M.rep τ) X v, (w : M.H τ)⟫_ℂ :=
      GlobalTheory.SmVec.inner_dRep hG hπ (hs v v.2) (hs w w.2) hX
    change ⟪dRep (M.rep τ) X v, (w : M.H τ)⟫_ℂ + ⟪(v : M.H τ), dRep (M.rep τ) X w⟫_ℂ = 0
    linear_combination key

theorem kFin_smooth_isKAct : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) (p q : ℕ) (T : GrpData p q) (R : DSRep T) (φ : Mat p q → Matrix (Fin V.rank) (Fin V.rank) ℂ) (m : ℤ) (U : M.H τ → R.U.H), GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.Matches R M τ φ m U → kFin M τ ≤ M.sm τ ∧ ∃ a : Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (kFin M τ), IsKAct M τ a := by
  intro D V S M τ p q T R φ m U hM
  have hk : ∀ y : M.H τ, y ∈ kFin M τ ↔ U y ∈ Set.range R.ι := fun y => hM.kfin y
  have hsm : ∀ y ∈ kFin M τ, y ∈ GlobalTheory.SmVec.smSub (gramAt D V τ) (M.rep τ) := fun y hy =>
    GlobalTheory.SmVec.mem_smSub.2 (hM.smooth y ((hk y).1 hy))
  refine ⟨fun y hy => Submodule.subset_span (hM.smooth y ((hk y).1 hy)), exists_isKAct_of_stable M τ hsm ?_⟩
  intro X hX y hy
  rw [← hM.lie] at hX
  obtain ⟨Z, hZ, rfl⟩ := hX
  obtain ⟨v, hv⟩ := (hk y).1 hy
  exact (hk _).2 ⟨_, (hM.der Z hZ v y hv.symm).symm⟩

end GlobalTheory.Chain.IoLift

end
