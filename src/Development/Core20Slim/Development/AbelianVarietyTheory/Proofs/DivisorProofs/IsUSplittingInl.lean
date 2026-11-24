module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramHspOf
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
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
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (incM)

namespace GlobalTheory.WeilSchrodinger

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem symp_transpose (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α β E) :
    GlobalTheory.WeilM.symp c ξ JB JA xᵀ yᵀ = GlobalTheory.WeilM.symp c ξ JA JB x y := by
  unfold GlobalTheory.WeilM.symp GlobalTheory.WeilM.hTens
  congr 2
  simp only [Matrix.transpose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

variable [Invertible (2 : R)]

def transD {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {κ : Type} [Fintype κ]
    (d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA JB) κ) : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JB JA) κ where
  e := (Matrix.transposeLinearEquiv β α R E).trans d.e
  form w w' := by
    rw [← symp_transpose c ξ JB JA w w', d.form]
    rfl

variable {c}

theorem transD_e {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {κ : Type} [Fintype κ]
    (d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA JB) κ) (x : Matrix α β E) : (transD c d).e xᵀ = d.e x := by
  simp [transD]

theorem transD_rho {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {κ : Type} [Fintype κ]
    (d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA JB) κ) (ψ : AddChar R ℂ) (w : Matrix β α E) :
    (transD c d).rho ψ w = d.rho ψ wᵀ := by
  simp [GlobalTheory.WeilM.Darboux.rho, transD]

variable [TopologicalSpace R] [TopologicalSpace E] {C : GlobalTheory.WeilM.TestClass R} {ψ : AddChar R ℂ} {ξ : E}
  {JA : Matrix α α E} {JB : Matrix β β E} {κ : Type} [Fintype κ] {d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA JB) κ}
  {om : GlobalTheory.WeilM.UG c JA × GlobalTheory.WeilM.UG c JB →* Module.End ℂ ((κ → R) → ℂ)}

theorem isUSplitting_inr (h : GlobalTheory.WeilM.IsUSplitting C ψ d (GlobalTheory.WeilM.actAB c) om) :
    GlobalTheory.WeilM.IsUSplitting C ψ d (GlobalTheory.WeilM.actB c) (om.comp (MonoidHom.inr _ _)) := by
  refine ⟨⟨fun g φ hφ => h.pres _ φ hφ, fun g w φ hφ => ?_, fun g l hl => h.adm _ l hl⟩, h.unit.comp _,
    h.cont.comp (f := MonoidHom.inr _ _) (continuous_const.prodMk continuous_id)⟩
  have := h.impl (1, g) w φ hφ
  simpa [GlobalTheory.WeilM.actAB, GlobalTheory.WeilM.actB] using this

theorem isUSplitting_inl (h : GlobalTheory.WeilM.IsUSplitting C ψ d (GlobalTheory.WeilM.actAB c) om) :
    GlobalTheory.WeilM.IsUSplitting C ψ (transD c d) (GlobalTheory.WeilM.actB c) (om.comp (MonoidHom.inl _ _)) := by
  refine ⟨⟨fun g φ hφ => h.pres _ φ hφ, fun g w φ hφ => ?_, fun g l hl => h.adm _ l hl⟩, h.unit.comp _,
    h.cont.comp (f := MonoidHom.inl _ _) (continuous_id.prodMk continuous_const)⟩
  have := h.impl (g, 1) wᵀ φ hφ
  simp only [MonoidHom.comp_apply, MonoidHom.inl_apply, transD_rho]
  convert this using 2
  simp [GlobalTheory.WeilM.actAB, GlobalTheory.WeilM.actB, Matrix.transpose_mul]

end Gen

section Theta

variable (F : Type) [Field F] [NumberField F] [Invertible (2 : AF F)]

def thetaTr {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ]
    (d : GlobalTheory.WeilM.Darboux B κ) (ψ : AddChar (AF F) ℂ) (Φ : (κ → AF F) → ℂ) : W → ℂ :=
  fun w => GlobalTheory.WeilM.thetaSum F (d.rho ψ w Φ)

end Theta

section Transport

def IsTransport {D : D7} (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {ξ : AE D}
    {JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E} {JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E}
    {κ : Type} [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ)
    (ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ))
    (om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ)) :
    Prop :=
  ∀ (a : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA))
    (b : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB)) (g : GA D S) (h : GA D T),
    mt T h = a.1.1 → mt S g = (b⁻¹).1.1ᵀ →
    ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, om (a, b) Φ ∈ GlobalTheory.WeilM.schA D.host.F κ ∧
      thetaTr D.host.F co ψ (om (a, b) Φ) = ω (g, h) (thetaTr D.host.F co ψ Φ)

end Transport

end GlobalTheory.WeilSchrodinger

end
