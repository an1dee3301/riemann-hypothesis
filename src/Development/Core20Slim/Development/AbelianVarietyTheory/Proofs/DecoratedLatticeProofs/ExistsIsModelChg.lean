module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.LocallyConstant.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod

noncomputable section

namespace GlobalTheory.LocMod.FrameChange

variable {k : Type} [Field k]
variable {N M : ℕ} {Y Y' Z Z' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
  [Fintype Z] [DecidableEq Z] [Fintype Z'] [DecidableEq Z']

def chg (FS : Frame k M Y') (FT : Frame k N Y) (GS : Frame k M Z') (GT : Frame k N Z)
    (x : Matrix Y Y' k) : Matrix Z Z' k :=
  GT.γ * FT.β * x * (FS.γ * GS.β)

theorem chg_inv (FS : Frame k M Y') (FT : Frame k N Y) (GS : Frame k M Z') (GT : Frame k N Z)
    (x : Matrix Y Y' k) : chg GS GT FS FT (chg FS FT GS GT x) = x := by
  simp only [chg, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc GT.β GT.γ, GT.βγ, Matrix.one_mul, ← Matrix.mul_assoc FT.γ FT.β, FT.γβ, Matrix.one_mul,
    ← Matrix.mul_assoc GS.β GS.γ, GS.βγ, Matrix.one_mul, FS.γβ, Matrix.mul_one]

theorem frame_sandwich (FS : Frame k M Y') (FT : Frame k N Y) (GS : Frame k M Z') (GT : Frame k N Z)
    (x : Matrix Y Y' k) : GT.β * chg FS FT GS GT x * GS.γ = FT.β * x * FS.γ := by
  simp only [chg, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc GT.β GT.γ, GT.βγ, Matrix.one_mul, GS.βγ, Matrix.mul_one]

theorem chg_add (FS : Frame k M Y') (FT : Frame k N Y) (GS : Frame k M Z') (GT : Frame k N Z)
    (x y : Matrix Y Y' k) : chg FS FT GS GT (x + y) = chg FS FT GS GT x + chg FS FT GS GT y := by
  simp only [chg, Matrix.mul_add, Matrix.add_mul]

variable [TopologicalSpace k] [IsTopologicalRing k]

theorem continuous_chg (FS : Frame k M Y') (FT : Frame k N Y) (GS : Frame k M Z') (GT : Frame k N Z) :
    Continuous (chg FS FT GS GT) := by
  unfold chg
  exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

def chgH (FS : Frame k M Y') (FT : Frame k N Y) (GS : Frame k M Z') (GT : Frame k N Z) :
    Matrix Y Y' k ≃ₜ Matrix Z Z' k where
  toFun := chg FS FT GS GT
  invFun := chg GS GT FS FT
  left_inv := chg_inv FS FT GS GT
  right_inv := chg_inv GS GT FS FT
  continuous_toFun := continuous_chg FS FT GS GT
  continuous_invFun := continuous_chg GS GT FS FT

def pull (FS : Frame k M Y') (FT : Frame k N Y) (GS : Frame k M Z') (GT : Frame k N Z) :
    SB (Matrix Z Z' k) →ₗ[ℂ] SB (Matrix Y Y' k) where
  toFun Φ := ⟨fun x => Φ.1 (chg FS FT GS GT x),
    ⟨Φ.2.1.comp_continuous (continuous_chg FS FT GS GT),
     Φ.2.2.comp_homeomorph (chgH FS FT GS GT)⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end GlobalTheory.LocMod.FrameChange

namespace GlobalTheory.LocMod.Place

open GlobalTheory.LocMod.FrameChange

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (p : Place D k)

theorem up_chg {Y Y' Z Z' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
    [Fintype Z] [DecidableEq Z] [Fintype Z'] [DecidableEq Z'] {S T : HSp D}
    (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (GS : Frame k S.rank Z') (GT : Frame k T.rank Z)
    (x : Matrix Y Y' k) : p.up GS GT (chg FS FT GS GT x) = p.up FS FT x := by
  unfold up
  rw [frame_sandwich]

theorem exists_isModel_chg (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (p : Place D k) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y']
    [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (Z Z' : Type) [Fintype Z]
    [DecidableEq Z] [Fintype Z'] [DecidableEq Z'] (GS : Frame k S.rank Z') (GT : Frame k T.rank Z)
    (ψ : AddChar (AF D.host.F) ℂ) :
    ∀ Tm, p.IsModel ψ FS FT Tm → ∃ Tm', p.IsModel ψ GS GT Tm' ∧
      ∀ (Φ : SB (Matrix Y Y' k)) (Φ' : SB (Matrix Z Z' k)),
        (∀ x, Φ.1 x = Φ'.1 (GT.γ * FT.β * x * (FS.γ * GS.β))) → Tm' Φ' = Tm Φ := by
  intro Tm hTm
  refine ⟨Tm.comp (pull FS FT GS GT), ⟨?_, ?_, ?_⟩, ?_⟩
  · intro Φ'
    exact hTm.theta _
  · intro x Φ' Φ'' h
    have := hTm.trans (chg GS GT FS FT x) (pull FS FT GS GT Φ') (pull FS FT GS GT Φ'') (by
      intro t
      change Φ''.1 (chg FS FT GS GT t) = Φ'.1 (chg FS FT GS GT (t + chg GS GT FS FT x))
      rw [h, chg_add, chg_inv])
    simpa [LinearMap.comp_apply, up_chg, chg_inv] using this
  · intro y hy Φ' Φ'' h
    have := hTm.modul y hy (pull FS FT GS GT Φ') (pull FS FT GS GT Φ'') (by
      intro t
      change Φ''.1 (chg FS FT GS GT t) = ψ (symplO S T (p.up FS FT t) y) * Φ'.1 (chg FS FT GS GT t)
      rw [h, up_chg])
    simpa [LinearMap.comp_apply] using this
  · intro Φ Φ' h
    change Tm (pull FS FT GS GT Φ') = Tm Φ
    congr 1
    exact Subtype.ext (funext fun x => (h x).symm)

end GlobalTheory.LocMod.Place
