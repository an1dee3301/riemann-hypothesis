module

public import Development.Core20Slim.Development.WeilBound.ThetaLifts.SphericalLattices.HoweDefs
public import Development.Core20Slim.Development.WeilBound.ThetaLifts.DoubleEigenvalues.DblEigenW
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.Core20Slim.Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.InertDef
public import Development.Core20Slim.Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Inertof
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Formalism.SatakeDualWeyl.StatementG
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

namespace PositivityTheory.Sph

open scoped Matrix
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

theorem inert_ctx {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
    (hT : IsTriple B G X om om') {v : Pl F} (he : IsEmpty (E →ₐ[F] Fv F v)) :
    (∃ w, Formalism.UG.IsInertAt F E v w) ∧ v ∉ X.T :=
  ⟨inert_of_local F E σ B hT.base v he, fun hv => he.false (B.τ ⟨v, hT.chars.sub hv⟩)⟩

theorem unrAt_div {χ χ' : Chr F E} {u : HeightOneSpectrum (𝓞 E)} (h : UnrAt χ u) (h' : UnrAt χ' u) :
    UnrAt (χ / χ') u := fun x hx => by
  have e : χ / χ' * χ' = χ := div_mul_cancel χ χ'
  have e2 : locChar (χ / χ' * χ') u x = locChar (χ / χ') u x * locChar χ' u x := by simp [locChar]
  rw [e, h x hx, h' x hx, mul_one] at e2
  exact e2.symm

theorem fix_of {B : Base F E} (hB : B.IsGood σ) {X : Spc F E n} {W : Spc F E d} {r s r' s' : ℕ} (hX : X.IsHerm σ B r s)
    (hW : W.IsSkew σ B r' s') {M : Model σ X W} (hM : M.IsGood B.ψ) {χX χW : Chr F E} {om : Rep σ X W}
    (hw : M.IsWeil B.ψ χX χW om) {v : Pl F} (hX' : ∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 F) = v → UnrAt χX u)
    (hW' : ∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 F) = v → UnrAt χW u)
    {ω : UA σ X.J × UA σ W.J → Module.End ℂ (Fn F n d v)} {ρ : Matrix (Fin n) (Fin d) (AE F E) → Module.End ℂ (Fn F n d v)}
    (hL : IsLocRep M B.ψ om v ω ρ) :
    (∀ g ∈ KAt σ X v, ω (g, 1) (M.vac v) = M.vac v) ∧ (∀ k ∈ KAt σ W v, ω (1, k) (M.vac v) = M.vac v) := by
  have hSB := (hM.vac v).1
  refine ⟨fun g hg => ?_, fun k hk => ?_⟩
  · have hA := PositivityTheory.ThKU.Vac.vacFixX hB hX hW hM hw hW' (k := g) hg
    exact ((hL.acts g hg.1 1 (GlobalTheory.InertSph.one_mem_KAt σ W v).1 _ hSB _).1 hA).symm
  · have hA := PositivityTheory.ThKU.Vac.vacFixW hB hX hW hM hw hX' (k := k) hk
    exact ((hL.acts 1 (GlobalTheory.InertSph.one_mem_KAt σ X v).1 k hk.1 _ hSB _).1 hA).symm

end PositivityTheory.Sph

end
