module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
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
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3.FiniteHeis

variable {D : D7}

noncomputable def heisLin (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (u : WO S T) : Module.End ℂ (WO S T → ℂ) where
  toFun := heisO ψ S T u
  map_add' f g := by
    funext w
    simp only [heisO, Pi.add_apply, mul_add]
  map_smul' c f := by
    funext w
    simp only [heisO, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem lineAt_fin {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D} (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (t : ℝ) :
    (show WO S T from lineAt θ τ z t).map (finPart D) = 0 :=
  (Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ T.rank S.rank τ z)).2.1 t

theorem heisO_comm_real (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {u x : WO S T} (hu : u.map (infPart D) = 0)
    (hx : x.map (finPart D) = 0) (g : WO S T → ℂ) :
    heisO ψ S T u (heisO ψ S T x g) = heisO ψ S T x (heisO ψ S T u g) := by
  rw [GlobalTheory.OrientedHeis.heisO_heisO, GlobalTheory.OrientedHeis.heisO_heisO, (GlobalTheory.OrientedHeis.symplOH_fin_real hu hx).1,
    (GlobalTheory.OrientedHeis.symplOH_fin_real hu hx).2, add_comm]

theorem heisO_dRho (ψ : AddChar (AF D.host.F) ℂ) {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D} {u : WO S T}
    (hu : u.map (infPart D) = 0) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (g : WO S T → ℂ) :
    heisO ψ S T u (dRho (heisO ψ S T) θ τ z g) = dRho (heisO ψ S T) θ τ z (heisO ψ S T u g) := by
  funext x
  have e : (fun t : ℝ => heisO ψ S T (lineAt θ τ z t) (heisO ψ S T u g) x) =
      fun t : ℝ => ψ (symplOH S T x u) * heisO ψ S T (lineAt θ τ z t) g (x + u) := by
    funext t
    rw [← heisO_comm_real ψ hu (lineAt_fin hθ τ z t) g]
    rfl
  show ψ (symplOH S T x u) * deriv (fun t : ℝ => heisO ψ S T (lineAt θ τ z t) g (x + u)) 0 =
    deriv (fun t : ℝ => heisO ψ S T (lineAt θ τ z t) (heisO ψ S T u g) x) 0
  rw [e, deriv_const_mul_field]

theorem heisO_pureTensorO_of_finite : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsInfFam θ → ∀ sS sT BS BT f, (∀ φ, IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f φ)) → ∀ u : WO S T, u.map (infPart D) = 0 → heisO ψ S T u f = f → ∀ φ, heisO ψ S T u (pureTensorO ψ θ S T sS sT BS BT f φ) = pureTensorO ψ θ S T sS sT BS BT f φ := by
  intro D ψ θ S T hθ sS sT BS BT f _ u hu hf φ
  have h := (GlobalTheory.OrientedHeis.pureTensorL_intertwine (fun _ => True) trivial (fun _ _ _ _ => trivial)
    (fun _ _ _ => trivial) (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT)
    (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT) (heisLin ψ S T u)
    (fun k g _ => ⟨trivial, ?_⟩) f trivial φ).2
  · have hf' : heisLin ψ S T u f = f := hf
    rw [hf'] at h
    exact h
  · obtain ⟨τ, i, j⟩ := k
    simp only [aPlusAll, aPlus, crea]
    rw [map_smul, map_sub, map_smul]
    show _ • (heisO ψ S T u (Datum.dRho _ _ _ _ _) - _ • heisO ψ S T u (Datum.dRho _ _ _ _ _)) = _
    rw [heisO_dRho ψ hθ hu, heisO_dRho ψ hθ hu]
    rfl

end GlobalTheory.Hk3.FiniteHeis
