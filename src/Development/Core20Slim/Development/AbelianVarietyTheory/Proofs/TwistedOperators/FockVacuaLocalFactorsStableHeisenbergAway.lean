module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.CmAdeleIdempotentOfPlacePropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FockOrthogonalDecomposition
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.DifferentiableOfChar
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ContinuousOfHeisenbergLevelAndSmooth
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IntegrableOnOfPeriodic
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceStable

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem symplO_of_place {p : Place D} {x y : WO S T} (hx : wAt p x = x) (hy : wAt p y = 0) : symplO S T x y = 0 := by
  rw [← hx, wAt_eq_smul, GlobalTheory.SplitScalar.symplO_smul, (GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).2.2.1 p, ← wAt_eq_smul, hy,
    GlobalTheory.SplitScalar.symplO_zero_right]


theorem wAt_wAt_ne {p q : Place D} (h : q ≠ p) (w : WO S T) : wAt q (wAt p w) = 0 := by
  rw [wAt_eq_smul, wAt_eq_smul, smul_smul, (GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).2.1 q p h, zero_smul]

theorem heisO_swap {u w : WO S T} (h : symplO S T u w = 0) (f : WO S T → ℂ) :
    heisO ψ S T u (heisO ψ S T w f) = heisO ψ S T w (heisO ψ S T u f) := by
  rw [GlobalTheory.SplitScalar.heisO_comm, h, AddChar.map_zero_eq_one, one_smul]



theorem wAt_lineAt (hθ : IsInfFam θ) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (t : ℝ) :
    wAt (.inr τ) (lineAt θ τ z t : WO S T) = lineAt θ τ z t := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨-, h1, h2⟩ := GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ z
  obtain ⟨-, -, -, -, h3, -, h4⟩ := GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D
  refine funext fun i => funext fun j => ?_
  show idem D (.inr τ) * lineAt θ τ z t i j = lineAt θ τ z t i j
  refine GlobalTheory.SplitScalar.adele_ext ?_ ?_
  · rw [← sub_eq_zero, ← RingHom.map_sub]
    refine GlobalTheory.FockCompare.ThetaCont.infPart_eq_zero hσ _ fun τ' => ?_
    rw [RingHom.map_sub, RingHom.map_sub, RingHom.map_mul, RingHom.map_mul]
    by_cases h : τ' = τ
    · subst h
      rw [(h4 θ hθ τ').1, one_mul, sub_self]
    · have h5 : θ τ' (infPart D (lineAt θ τ z t i j)) = 0 := by
        have := h2 t τ'
        rw [if_neg h] at this
        exact congrFun (congrFun this i) j
      rw [h5, mul_zero, sub_self]
  · have h5 : finPart D (lineAt θ τ z t i j) = 0 := congrFun (congrFun (h1 t) i) j
    rw [RingHom.map_mul, h5, mul_zero]

theorem dRho_heisO (hθ : IsInfFam θ) {τ : D.what₂.Tau} {w : WO S T} (hw : wAt (.inr τ) w = 0)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (g : WO S T → ℂ) :
    Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z (heisO ψ S T w g) =
      heisO ψ S T w (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z g) := by
  funext x
  unfold Formalism.IndefR.Datum.dRho
  rw [heisO, ← deriv_const_mul_field]
  congr 1
  funext t
  rw [heisO_swap (symplO_of_place (wAt_lineAt hθ τ z t) hw)]
  rfl

theorem isFockVacAt_heisO (hθ : IsInfFam θ) {τ : D.what₂.Tau} {w : WO S T} (hw : wAt (.inr τ) w = 0)
    {J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ} {f : WO S T → ℂ}
    (hf : IsFockVacAt (heisO ψ S T) θ τ J f) : IsFockVacAt (heisO ψ S T) θ τ J (heisO ψ S T w f) := by
  intro z
  have h := congrArg (GlobalTheory.SplitScalar.heisL ψ S T w) (hf z)
  rw [annih, map_add (f := _), map_smul, map_zero] at h
  rw [annih, dRho_heisO hθ hw, dRho_heisO hθ hw]
  exact h


end GlobalTheory.PlaceStable

end
