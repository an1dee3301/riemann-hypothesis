module

public import Formalism.LocalToGlobal.InertKernelTheory.DefsInt
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.RingTheory.Ideal.Defs

@[expose] public section

noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

section Comb

variable {D : D7} {N N' r : ℕ} {p : ℕ} [Fact p.Prime]




end Comb


section Lin

variable {D : D7} {N N' : ℕ}



variable {p : ℕ} [Fact p.Prime]




end Lin


section Pull

variable {D : D7}

theorem ie_emb_star (φ : D.host.E →+* ℂ) (x : D.host.E) :
    φ (@star D.host.E (@InvolutiveStar.toStar _ (@StarMul.toInvolutiveStar _ _
      (@StarRing.toStarMul _ _ D.host.cmStar))) x) = (starRingEnd ℂ) (φ x) := by
  haveI := D.host.isCMField_hostE
  exact NumberField.IsCMField.complexEmbedding_complexConj D.host.E φ x

theorem ie_mem_smulLat {n : ℕ} (γ : Matrix (Fin n) (Fin n) D.host.E) (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (x : Fin n → D.host.E) : x ∈ SDLat.smulLat γ L ↔ ∃ w ∈ L, γ.mulVec w = x := by
  simp [SDLat.smulLat, Submodule.mem_map, Matrix.toLin'_apply]

variable {N N' : ℕ}

theorem ie_homL_pull (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)
    (h1' : (letI := D.host.cmStar; star γ' * γ') = 1) {M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {A : Matrix (Fin N') (Fin N) D.host.E}
    (hA : A ∈ homL D (SDLat.smulLat γ M) (SDLat.smulLat γ' M')) :
    (letI := D.host.cmStar; star γ' * A * γ) ∈ homL D M M' := by
  letI := D.host.cmStar
  induction hA using Submodule.span_induction with
  | mem A hA =>
    refine Submodule.subset_span fun x hx => ?_
    obtain ⟨y, hy, hxy⟩ := (ie_mem_smulLat γ' M' _).1 (hA _ ((ie_mem_smulLat γ M _).2 ⟨x, hx, rfl⟩))
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hxy, Matrix.mulVec_mulVec, h1', Matrix.one_mulVec]
    exact hy
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.mul_add, Matrix.add_mul]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [Matrix.mul_smul, Matrix.smul_mul]; exact Submodule.smul_mem _ c hx

theorem ie_yy_pull (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)
    (h1' : (letI := D.host.cmStar; star γ' * γ') = 1) {M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {A : Matrix (Fin N') (Fin N) D.host.E}
    (hA : A ∈ YYl D (SDLat.smulLat γ M) (SDLat.smulLat γ' M')) :
    (letI := D.host.cmStar; star γ' * A * γ) ∈ YYl D M M' := by
  letI := D.host.cmStar
  induction hA using Submodule.span_induction with
  | mem B hB =>
    obtain ⟨a, ha, A₀, hA₀, rfl⟩ := hB
    refine Submodule.subset_span ⟨a, ha, _, ie_homL_pull γ γ' h1' hA₀, ?_⟩
    rw [Matrix.mul_smul, Matrix.smul_mul]
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.mul_add, Matrix.add_mul]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [Matrix.mul_smul, Matrix.smul_mul]; exact Submodule.smul_mem _ c hx

variable (cc : Ideal (𝓞 D.host.K)) (δ : ℂ)

theorem ie_tPull_add (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) (x y : VC D N N') :
    tPull D (tor0 D cc δ) γ γ' (x + y) = tPull D (tor0 D cc δ) γ γ' x + tPull D (tor0 D cc δ) γ γ' y := by
  funext τ
  show _ * (Matrix.of (x τ) + Matrix.of (y τ)) * _ = _
  rw [Matrix.mul_add, Matrix.add_mul]
  rfl

theorem ie_tPull_smul (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) (c : ℂ)
    (x : VC D N N') : tPull D (tor0 D cc δ) γ γ' (c • x) = c • tPull D (tor0 D cc δ) γ γ' x := by
  funext τ
  simp only [tPull, Pi.smul_apply]
  rw [show (Matrix.of (c • x τ) : Matrix (Fin N') (Fin N) ℂ) = c • Matrix.of (x τ) from rfl, Matrix.mul_smul,
    Matrix.smul_mul]
  rfl

def ieTPullHom (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) :
    VC D N N' →+ VC D N N' :=
  AddMonoidHom.mk' (tPull D (tor0 D cc δ) γ γ') (ie_tPull_add cc δ γ γ')

theorem ie_tPull_embV (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)
    (A : Matrix (Fin N') (Fin N) D.host.E) :
    tPull D (tor0 D cc δ) γ γ' (embV D (tor0 D cc δ) A) =
      embV D (tor0 D cc δ) (letI := D.host.cmStar; star γ' * A * γ) := by
  letI := D.host.cmStar
  funext τ
  have e1 : (star γ').map (embT D τ) = Matrix.conjTranspose (γ'.map (embT D τ)) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.star_apply, Matrix.conjTranspose_apply]
    exact ie_emb_star (embT D τ) (γ' j i)
  have e2 : (star γ' * A * γ).map (embT D τ) =
      Matrix.conjTranspose (γ'.map (embT D τ)) * A.map (embT D τ) * γ.map (embT D τ) := by
    rw [Matrix.map_mul, Matrix.map_mul, e1]
  exact e2.symm

theorem ie_La_pull (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)
    (h1' : (letI := D.host.cmStar; star γ' * γ') = 1) (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) :
    La D (tor0 D cc δ) (SDLat.smulLat γ M) (SDLat.smulLat γ' M') ≤
      (La D (tor0 D cc δ) M M').comap (ieTPullHom cc δ γ γ') := by
  unfold La
  rw [AddSubgroup.closure_le]
  rintro z ⟨w, hw, A, hA, rfl⟩
  simp only [SetLike.mem_coe, AddSubgroup.mem_comap, ieTPullHom, AddMonoidHom.mk'_apply]
  rw [ie_tPull_smul, ie_tPull_embV]
  exact AddSubgroup.subset_closure ⟨w, hw, _, ie_yy_pull γ γ' h1' hA, rfl⟩

end Pull


section Pair

variable {D : D7} {N N' : ℕ}





end Pair


end Formalism.L2.KerInert
