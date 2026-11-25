module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLiftHermitianIsometryModLevelSelfDual
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.JetGauges.ThetaSpanAdjoint
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermForm
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Init.Core
public import Init.Data.Cast
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Unramified.Basic

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence
open GlobalTheory.AdLat GlobalTheory.UnRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_hermitianIsometryModLevel_selfDual : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n m : ℕ), Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) → 0 < m → ∀ (Λ : GenLat E n) (io : Λ.La →ₗ[𝓞 E] StdMod E n m), Λ.Unimod → IsIsomMod Λ m io → ∀ k : ℕ, 0 < k → ∃ io' : Λ.La →ₗ[𝓞 E] StdMod E n (m * k), IsIsomMod Λ (m * k) io' ∧ ∀ (v : Λ.La) (x : Fin n → 𝓞 E), (∀ j, io' v j = Ideal.Quotient.mk _ (x j)) → ∀ j, io v j = Ideal.Quotient.mk _ (x j) := by
  first | exact @GlobalTheory.IsomLift.exists_lift | exact GlobalTheory.IsomLift.exists_lift | (intros; apply GlobalTheory.IsomLift.exists_lift <;> assumption)
