module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.AdelicCharDual
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace
public import Development.Core20Slim.Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FactorialTendstoZero
public import Development.Core20Slim.Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.UnitaryAnnihilator
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Matrix NumberField IsDedekindDomain GlobalTheory.WeilM MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.AdeleAnn

open GroundTheory.Global

variable {F : Type} [Field F] [NumberField F]



theorem norm_eq_one (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hc : Continuous ψ)
    (hF : ∀ a : F, ψ (algebraMap F (AdeleRing (𝓞 F) F) a) = 1) (x : AdeleRing (𝓞 F) F) :
    ‖ψ x‖ = 1 :=
  _root_.UpperTheory.Reformulated.B.AdelicCharacterNormOne.norm_eq_one ψ hc hF x

theorem unitary_and_annihilator_eq : ∀ (F : Type) [Field F] [NumberField F] [LocallyCompactSpace (AdeleRing (𝓞 F) F)] [Invertible (2 : AdeleRing (𝓞 F) F)] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), Continuous ψ → ψ ≠ 1 → (∀ a : F, ψ (algebraMap F (AdeleRing (𝓞 F) F) a) = 1) → (∀ x, ‖ψ x‖ = 1) ∧ ∀ x : AdeleRing (𝓞 F) F, (∀ a : F, ψ (x * algebraMap F (AdeleRing (𝓞 F) F) a) = 1) → ∃ b : F, x = algebraMap F (AdeleRing (𝓞 F) F) b :=
  _root_.UpperTheory.Reformulated.B.UnitaryAnnihilator.unitary_and_annihilator_eq

end GlobalTheory.CompanionTheory.AdeleAnn
