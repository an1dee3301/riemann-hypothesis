module
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.Core20Slim.Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.InertDef
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
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
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.UniformSpace.Defs


@[expose] public section

noncomputable section

namespace PositivityTheory.ThK

open scoped Matrix
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

theorem one_mem_UAt (X : Spc F E n) (v : Pl F) : (1 : UA σ X.J) ∈ UAt σ X (evFin F v) := fun u _ => by
  have : mat (1 : UA σ X.J) = 1 := rfl
  rw [this, sub_self, smul_zero]

theorem mul_mem_UAt {X : Spc F E n} {v : Pl F} {g h : UA σ X.J} (hg : g ∈ UAt σ X (evFin F v)) (hh : h ∈ UAt σ X (evFin F v)) :
    g * h ∈ UAt σ X (evFin F v) := fun u hu => by
  have e : mat (g * h) - 1 = (mat g - 1) * mat h + (mat h - 1) := by
    have : mat (g * h) = mat g * mat h := rfl
    rw [this, sub_mul, one_mul]; abel
  rw [e, smul_add, ← Matrix.smul_mul, hg u hu, hh u hu, Matrix.zero_mul, add_zero]

theorem mat_inv_mul {X : Spc F E n} (g : UA σ X.J) : mat g⁻¹ * mat g = 1 := by
  have : mat (g⁻¹ * g) = mat g⁻¹ * mat g := rfl
  rw [← this, inv_mul_cancel]; rfl

theorem inv_mem_UAt {X : Spc F E n} {v : Pl F} {g : UA σ X.J} (hg : g ∈ UAt σ X (evFin F v)) :
    g⁻¹ ∈ UAt σ X (evFin F v) := fun u hu => by
  have e : mat g⁻¹ - 1 = -(mat g⁻¹ * (mat g - 1)) := by rw [mul_sub, mat_inv_mul, mul_one, neg_sub]
  rw [e, smul_neg, ← Matrix.mul_smul, hg u hu, Matrix.mul_zero, neg_zero]


variable (σ) in
def KSub (W : Spc F E d) (v : Pl F) : Subgroup (UA σ W.J) where
  carrier := KAt σ W v
  one_mem' := ⟨one_mem_UAt W v, fun y hy => by
    have : mat (1 : UA σ W.J) = 1 := rfl
    rw [inv_one, this, Matrix.one_mulVec]; exact ⟨hy, hy⟩⟩
  mul_mem' := fun {g h} hg hh => ⟨mul_mem_UAt hg.1 hh.1, fun y hy => by
    have e1 : mat (g * h) = mat g * mat h := rfl
    have e2 : mat (h⁻¹ * g⁻¹) = mat h⁻¹ * mat g⁻¹ := rfl
    rw [mul_inv_rev, e1, e2, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact ⟨(hg.2 _ (hh.2 y hy).1).1, (hh.2 _ (hg.2 y hy).2).2⟩⟩
  inv_mem' := fun {g} hg => ⟨inv_mem_UAt hg.1, fun y hy => by
    rw [inv_inv]; exact ⟨(hg.2 y hy).2, (hg.2 y hy).1⟩⟩



section Loc

variable {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ} {om : Rep σ X W} {v : Pl F}
  {ω : UA σ X.J × UA σ W.J → Module.End ℂ (Fn F n d v)} {ρ : Matrix (Fin n) (Fin d) (AE F E) → Module.End ℂ (Fn F n d v)}

theorem IsLocRep.mulW (L : IsLocRep M ψ om v ω ρ) {h h' : UA σ W.J} (hh : h ∈ UAt σ W (evFin F v)) (hh' : h' ∈ UAt σ W (evFin F v))
    {φ} (hφ : φ ∈ SB _) : ω (1, h * h') φ = ω (1, h) (ω (1, h') φ) := by
  simpa using L.mul 1 (one_mem_UAt X v) h hh 1 (one_mem_UAt X v) h' hh' φ hφ



def IsLocRep.onK (L : IsLocRep M ψ om v ω ρ) : KSub σ W v →* Module.End ℂ (SB (Fin n × Fin d → Fv F v)) where
  toFun k := (ω (1, k.1)).restrict fun φ hφ => L.pres 1 (one_mem_UAt X v) k.1 k.2.1 φ hφ
  map_one' := LinearMap.ext fun φ => Subtype.ext (L.one φ φ.2)
  map_mul' a b := LinearMap.ext fun φ => Subtype.ext (L.mulW a.2.1 b.2.1 φ.2)

end Loc

section Main

variable {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} {v : Pl F}


end Main


end PositivityTheory.ThK
