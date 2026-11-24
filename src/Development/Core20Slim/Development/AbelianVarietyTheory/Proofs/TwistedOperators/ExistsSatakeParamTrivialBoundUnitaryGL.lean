module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SphericalEigenvectorGeneratesIrreducibleSubrepreStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSatakeLeOfUnitarySphericalGLStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.PowDvdOfHermMatEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeParameterGLStarEqInvOfUnitarisable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeParameterOfSpherical
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SatakeDualWeyl.StatementE
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Multiset.Defs
public import Mathlib.Data.Multiset.MapFold
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Subtype
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Notation
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinZeta.ParGL

theorem exists_isSatVecGL_bound : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V), IsUnitarisable ρ → ∀ x : V, x ≠ 0 → x ∈ fixed ρ (KGL w (n := n)) → (∀ h ∈ Hecke ℂ (KGL w (n := n)), ∃ c : ℂ, heckeVec ρ (KGL w (n := n)) h x = c • x) → ∃ B, IsSatVecGL w ρ x B ∧ ∀ β ∈ B, ‖(β : ℂ)‖ ≤ (qV E w : ℝ) ^ (((n : ℝ) - 1) / 2) ∧ ‖((β⁻¹ : ℂˣ) : ℂ)‖ ≤ (qV E w : ℝ) ^ (((n : ℝ) - 1) / 2) := by
  intro E _ _ w n V _ _ ρ hun x hx0 hxf hs
  have hK : IsCommensurated (KGL w (n := n)) := Formalism.UG.Final.GLintComm E w n
  obtain ⟨U, hU, hxU, hirr, hunU, hline⟩ :=
    GlobalTheory.T.spherical_eigenvector_generates_irreducible_subrepresentation ρ (KGL w (n := n)) (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).1 hK hun x hx0 hxf hs
  set π := GlobalTheory.PRep.sub ρ U hU with hπ
  let x' : U := ⟨x, hxU⟩
  have hx'0 : x' ≠ 0 := fun e => hx0 (congrArg Subtype.val e)
  have hx'f : x' ∈ fixed π (KGL w (n := n)) :=
    GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (GlobalTheory.LGrp.mem_fixed.1 hxf k hk)
  have hsub : ∀ g (y : U), U.subtype (π g y) = ρ g (U.subtype y) := fun _ _ => rfl
  have heig : ∀ h ∈ Hecke ℂ (KGL w (n := n)), ∃ c : ℂ, ∀ y ∈ fixed π (KGL w (n := n)), heckeVec π (KGL w (n := n)) h y = c • y := by
    intro h hh
    obtain ⟨c, hc⟩ := hs h hh
    have e1 : heckeVec π (KGL w (n := n)) h x' = c • x' := Subtype.val_injective (by
      have := map_heckeVec hK hh U.subtype hsub (x := x')
      exact this.trans hc)
    refine ⟨c, fun y hy => ?_⟩
    obtain ⟨a, rfl⟩ := hline y hy
    have := map_heckeVec hK hh (ρ := π) (ρ' := π) (a • LinearMap.id) (fun g y => by simp) (x := x')
    simp only [LinearMap.smul_apply, LinearMap.id_apply] at this
    rw [← this, e1, smul_comm]
  obtain ⟨B, hB⟩ := GlobalTheory.LFun.ExSatGL.exists_hasSatGL E w n U π
    ((Submodule.ne_bot_iff _).2 ⟨x', hx'f, hx'0⟩) heig
  have hx' : IsSatVecGL w π x' B := hB.2 x' hx'f hx'0
  have hup := GlobalTheory.T.norm_satake_le_of_unitary_spherical_GL GlobalTheory.SatakeBound.satakeTrivialBound E w n _ π B hirr hunU hB
  refine ⟨B, hx'.map U.subtype hsub hx0, fun β hβ => ⟨hup β hβ, ?_⟩⟩
  have hst := GlobalTheory.LFun.UnitaryParam.map_star_eq_map_inv E w n _ π x' B hunU hx'
  have h1 : β⁻¹ ∈ B.map star := hst ▸ Multiset.mem_map_of_mem _ hβ
  obtain ⟨β', hβ', e⟩ := Multiset.mem_map.1 h1
  have h2 : ‖((β⁻¹ : ℂˣ) : ℂ)‖ = ‖(β' : ℂ)‖ := by
    rw [← e]
    simp
  rw [h2]
  exact hup β' hβ'

end GlobalTheory.FinZeta.ParGL

end
