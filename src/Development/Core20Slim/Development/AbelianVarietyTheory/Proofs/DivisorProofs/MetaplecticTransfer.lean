module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairingStdP
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPairingCoordinatesSchrodingerFollandStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticGroupMatrixOfPreservesPhaseSpaceStatement
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
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
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.SymplecticGroup
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped SchwartzMap Matrix

noncomputable section

namespace GlobalTheory.ArchUniq

open GlobalTheory.RealWeil

theorem pairingCoords : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (P : V → V → ℝ), GlobalTheory.ArchUniq.IsPairing P → ∀ n : ℕ, Module.finrank ℝ V = n →
    ∃ (C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (φ : (V × V) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ)),
      (∀ v v', GlobalTheory.RealWeil.sympl (φ v) (φ v') = -GlobalTheory.ArchUniq.omega P v v') ∧
      ∀ v (f : EuclideanSpace ℝ (Fin n) → ℂ),
        GlobalTheory.ArchUniq.schrF P v (f ∘ C) = GlobalTheory.RealWeil.rhoFun (φ v) f ∘ C := GlobalTheory.T.exists_pairing_coordinates_schrodinger_folland

theorem symplMatrix : ∀ (l : Type) [Fintype l] [DecidableEq l] (ψ : (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ w w', GlobalTheory.RealWeil.sympl (ψ w) (ψ w') = GlobalTheory.RealWeil.sympl w w') →
    ∃ M : Matrix.symplecticGroup l ℝ, ∀ w, (M : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w = ψ w := GlobalTheory.T.exists_symplecticGroup_matrix_of_preserves_phaseSpaceForm

end GlobalTheory.ArchUniq

open scoped SchwartzMap Matrix TensorProduct Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchUniq

namespace GlobalTheory.ArchUniq

end GlobalTheory.ArchUniq
