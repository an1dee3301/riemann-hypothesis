module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPairingCoordinatesSchrodingerFolland
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairingStdP
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Lp.WithLp
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped SchwartzMap Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pairing_coordinates_schrodinger_folland : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (P : V → V → ℝ), GlobalTheory.ArchUniq.IsPairing P → ∀ n : ℕ, Module.finrank ℝ V = n →
    ∃ (C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (φ : (V × V) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ)),
      (∀ v v', GlobalTheory.RealWeil.sympl (φ v) (φ v') = -GlobalTheory.ArchUniq.omega P v v') ∧
      ∀ v (f : EuclideanSpace ℝ (Fin n) → ℂ),
        GlobalTheory.ArchUniq.schrF P v (f ∘ C) = GlobalTheory.RealWeil.rhoFun (φ v) f ∘ C := by
  first | exact @GlobalTheory.ArchUniq.exists_pairing_coords | exact GlobalTheory.ArchUniq.exists_pairing_coords | (intros; apply GlobalTheory.ArchUniq.exists_pairing_coords <;> assumption)
