module

public import Development.Core20Slim.Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementW
public import Development.Core20Slim.Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.AnaSysW
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.AnalyticTransOfAdd
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.IsTransSys
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.Taylor0ConstMul
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Group.Completion
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.UniformField
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open PowerSeries

noncomputable section

namespace Formalism.L2.Th1.E

open Formalism.L2.Th1.F (opU sgStar th0 taylor0)
open Formalism.L2.Th1.B (fExp)

namespace TransW

section Sim

variable {K : Type} [NormedField K]

def Sim (f g : K⟦X⟧) : Prop := ∃ ρ : K, ‖ρ‖ = 1 ∧ f = C ρ * g

theorem Sim.symm {f g : K⟦X⟧} (h : Sim f g) : Sim g f := by
  obtain ⟨ρ, hρ, rfl⟩ := h
  have hne : ρ ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hρ
    exact zero_ne_one hρ
  refine ⟨ρ⁻¹, by rw [norm_inv, hρ, inv_one], ?_⟩
  rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hne, map_one, one_mul]








end Sim

section An

variable (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (W : WeierstrassCurve ℂ_[l])





open Classical in
def piW (hA : PtWAdd) (hU : Unif l L ι W) : ℂ →+ W.toAffine.Point :=
  AddMonoidHom.mk' (ptW l L ι W) (hA l L ι W hU)

variable {l L ι W}

open Classical in
theorem nsmul_ptW (hA : PtWAdd) (hU : Unif l L ι W) (t : ℂ) (N : ℕ) :
    N • ptW l L ι W t = ptW l L ι W ((N : ℂ) * t) := by
  have h := map_nsmul (piW l L ι W hA hU) N t
  simpa [piW, nsmul_eq_mul] using h.symm




open Classical in
theorem ptW_int (hA : PtWAdd) (hZ : PtWZero) (hU : Unif l L ι W) (hW : IntCurve W) (t : ℂ) (N : ℕ)
    (hlN : ¬ l ∣ N) (hNt : (N : ℂ) * t ∈ L.lattice) (ht : t ∉ L.lattice) :
    ‖px W (ptW l L ι W t)‖ ≤ 1 ∧ ‖py W (ptW l L ι W t)‖ ≤ 1 :=
  torsionIntegral ℂ_[l] W hW _ N (Tor.norm_natCast l hlN)
    (by rw [nsmul_ptW hA hU]; exact (hZ l L ι W hU _).2 hNt)
    (fun h => ht ((hZ l L ι W hU t).1 h))




variable (l L ι W)


def hW (t₀ t : ℂ) : PowerSeries ℂ_[l] := inW l ι W (opU L t (th0 L t₀))







variable {l L ι W}





end An

end TransW

open TransW



namespace TransW

section Cases

variable {l : ℕ} [Fact l.Prime] {L : PeriodPair} {ι : ℂ ≃+* ℂ_[l]} {W : WeierstrassCurve ℂ_[l]}







end Cases

end TransW




end Formalism.L2.Th1.E
