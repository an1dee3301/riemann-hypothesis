module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowShiftEq
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ApplyAddInfRat
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitVacuumStandardLatticesDefinitePair
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsThetaAtOfVac
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilFinitePointPreservesFockVacuum
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowShiftTheta
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv GlobalTheory.LastVertexMove
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section
namespace GlobalTheory.LastVertexVac
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem colPt_mem_GfC (S : GridChoice W U) (t : T) (g : FinPt G (.top D.R.m)) :
    (colPt S t g).1 ∈ GfC _ ∧ (colPt S t g).2 ∈ GfC _ := by
  refine ⟨?_, ?_⟩
  · show (1 : GA D _) ∈ GfC _
    exact one_mem _
  · exact (topLast ((S.N.u (.top D.R.m))⁻¹ * g * S.N.u (.top D.R.m))).2

theorem latMove (S : GridChoice W U) (t : T) (g : FinPt G (.top D.R.m))
    (hlat : ∀ x, actO _ _ (colPt S t g).1⁻¹ (colPt S t g).2⁻¹ x ∈ stdLat S (.top t (lastIx D)) ↔ x ∈ stdLat S (.top t (lastIx D))) :
    ∀ u, u ∈ stdLat S (.top t (lastIx D)) ↔ ∃ u₀ ∈ stdLat S (.top t (lastIx D)), u = actO _ _ (colPt S t g).1 (colPt S t g).2 u₀ := by
  intro u
  constructor
  · intro hu
    refine ⟨actO _ _ (colPt S t g).1⁻¹ (colPt S t g).2⁻¹ u, (hlat u).2 hu, ?_⟩
    have := GlobalTheory.WeilVacMove.actO_inv_actO (colPt S t g).1⁻¹ (colPt S t g).2⁻¹ u
    rw [inv_inv, inv_inv] at this
    exact this.symm
  · rintro ⟨u₀, hu₀, rfl⟩
    refine (hlat _).1 ?_
    rw [GlobalTheory.WeilVacMove.actO_inv_actO]
    exact hu₀

theorem om_vac_top (S : GridChoice W U) (t : T) (j : Fin D.R.m)
    (q : GA D (G.V (.top (j : ℕ))) × GA D (G.V (.top ((j : ℕ) + 1)))) (hq1 : q.1 ∈ GfC _) (hq2 : q.2 ∈ GfC _)
    (hΛ : ∀ u, u ∈ stdLat S (.top t (j : ℕ)) ↔ ∃ u₀ ∈ stdLat S (.top t (j : ℕ)), u = actO _ _ q.1 q.2 u₀) :
    ∃ c : ℂ, W.om (.top t (j : ℕ)) q (S.Z.vac (.top t (j : ℕ))) = c • S.Z.vac (.top t (j : ℕ)) := by
  have hp : DefPair D.R.m (Pair.top t (j : ℕ)) := defPair_top t j
  have hIn : (Pair.top t (j : ℕ) : Pair T).InRange D.R.m := inRange_top t j
  have hn := hp.nodes
  have hvac : IsVacO W.ψ W.θ (G.V (.top (j : ℕ))) (G.V (.top ((j : ℕ) + 1))) (W.cart (.top (j : ℕ))) (W.cart (.top ((j : ℕ) + 1)))
      (colLat (S.N.fr (.top (j : ℕ))) : Set _) (colLat (S.N.fr (.top ((j : ℕ) + 1))) : Set _) (S.Z.vac (.top t (j : ℕ))) :=
    S.Z.vac_is _ hp
  have hW : IsWeilDatumO W.ψ (G.V (.top (j : ℕ))) (G.V (.top ((j : ℕ) + 1))) (G.chrS (.top t (j : ℕ))) (G.chrT (.top t (j : ℕ)))
      (W.om (.top t (j : ℕ))) := W.om_is _ hIn
  have hmove : IsVacO W.ψ W.θ (G.V (.top (j : ℕ))) (G.V (.top ((j : ℕ) + 1))) (W.cart (.top (j : ℕ))) (W.cart (.top ((j : ℕ) + 1)))
      (colLat (S.N.fr (.top (j : ℕ))) : Set _) (colLat (S.N.fr (.top ((j : ℕ) + 1))) : Set _)
      (W.om (.top t (j : ℕ)) (q.1, q.2) (S.Z.vac (.top t (j : ℕ)))) :=
    GlobalTheory.WeilVacMove.isVacO_om D W.ψ W.θ _ _ _ _ _ hW W.θ_is _ _ _ _ _ _ _ _ q.1 q.2
      (fun τ => by rw [GlobalTheory.FockRealMove.compAt_mt_of_mem_GfC _ _ _ hq1, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FockRealMove.compAt_mt_of_mem_GfC _ _ _ hq2, Matrix.mul_one, Matrix.one_mul])
      hΛ _ hvac
  have hS1 : (G.V (.top (j : ℕ))).SigOK := hn.1.sigOK G
  have hS2 : (G.V (.top ((j : ℕ) + 1))).SigOK := hn.2.sigOK G
  have hC1 : ∀ τ, IsCartanInv (gramAt D (G.V (.top (j : ℕ))) τ) (W.cart (.top (j : ℕ)) τ) := fun τ => W.cart_is _ hn.1.inRange τ
  have hC2 : ∀ τ, IsCartanInv (gramAt D (G.V (.top ((j : ℕ) + 1))) τ) (W.cart (.top ((j : ℕ) + 1)) τ) :=
    fun τ => W.cart_is _ hn.2.inRange τ
  have hD1 : IsSelfDualC (G.V (.top (j : ℕ))) (colLat (S.N.fr (.top (j : ℕ)))) := S.N.selfDual hn.1
  have hD2 : IsSelfDualC (G.V (.top ((j : ℕ) + 1))) (colLat (S.N.fr (.top ((j : ℕ) + 1)))) := S.N.selfDual hn.2
  obtain ⟨c, -, hc⟩ := GlobalTheory.VacUnique.vacUniqueO D W.ψ W.θ hvac.1 W.θ_is _ _ _ _ hS1 hS2 hC1 hC2 _ _ hD1 hD2 _ _ hvac hmove
  exact ⟨c, hc⟩

theorem colShift_vac_eq_smul : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) (t : T) (g : FinPt G (.top D.R.m)),
    (∀ x, actO _ _ (colPt S t g).1⁻¹ (colPt S t g).2⁻¹ x ∈ stdLat S (.top t (lastIx D)) ↔ x ∈ stdLat S (.top t (lastIx D))) →
    ∃ c : ℂ, colShift S t g (S.Z.vac (.top t (lastIx D))) = c • S.Z.vac (.top t (lastIx D)) := by
  intro D T L sc G W U S t g hlat
  obtain ⟨hx, hy⟩ := colPt_mem_GfC S t g
  rw [colShift_eq]
  exact om_vac_top S t (lastIx D) (colPt S t g) hx hy (latMove S t g hlat)

end GlobalTheory.LastVertexVac
