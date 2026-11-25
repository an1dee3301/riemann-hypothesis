module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.CProps
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.PsiFEqOne
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.TraceDual
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.GunrClassLev

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen PositivityTheory.SiegelWeilFormula.Gunr
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M n d : ℕ} {J : Matrix (Fin M) (Fin M) E} {T : Matrix (Fin n) (Fin n) E}
  {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)} {ψv : Fv F v → ℂ} {S : Subring (Fv F v ⊗[F] E)}
  {σS : S →+* S} {ϖ : Fv F v} {ε : ℤ}

theorem coe_mul_pS_pow (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (k : ℕ) (t : S) :
    ((t * hG.pS ^ k : S) : Fv F v ⊗[F] E) = (ϖ ^ k) • (t : Fv F v ⊗[F] E) := by
  rw [Subring.coe_mul, Subring.coe_pow, Algebra.smul_def, map_pow, mul_comm]
  rfl

theorem smul_sub_mem_iff (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (k : ℕ) (s s' : S) :
    (ϖ ^ k)⁻¹ • (s : Fv F v ⊗[F] E) - (ϖ ^ k)⁻¹ • (s' : Fv F v ⊗[F] E) ∈ S ↔ s - s' ∈ lev hG.pS k := by
  have hne : ϖ ^ k ≠ 0 := pow_ne_zero _ hG.unif_ne
  constructor
  · intro h
    refine Ideal.mem_span_singleton'.2 ⟨⟨_, h⟩, Subtype.ext ?_⟩
    rw [coe_mul_pS_pow hG]
    show (ϖ ^ k) • ((ϖ ^ k)⁻¹ • (s : Fv F v ⊗[F] E) - (ϖ ^ k)⁻¹ • (s' : Fv F v ⊗[F] E)) = (s : Fv F v ⊗[F] E) - s'
    rw [← smul_sub, smul_smul, mul_inv_cancel₀ hne, one_smul]
  · intro h
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h
    have e : (s : Fv F v ⊗[F] E) - (s' : Fv F v ⊗[F] E) = (ϖ ^ k) • (c : Fv F v ⊗[F] E) := by
      rw [← coe_mul_pS_pow hG, hc, AddSubgroupClass.coe_sub]
    rw [← smul_sub, e, smul_smul, inv_mul_cancel₀ hne, one_smul]
    exact c.2

theorem classLev : ClassLev := by
  intro F E _ _ _ _ _ σ M n d J T bs v ψv S σS ϖ ε hG k X X' hX hX'
  constructor
  · intro h
    refine Matrix.ext fun a b => ?_
    exact Ideal.Quotient.eq.2 ((smul_sub_mem_iff hG k (X a b) (X' a b)).1 (h a b))
  · intro h a b
    exact (smul_sub_mem_iff hG k (X a b) (X' a b)).2 (Ideal.Quotient.eq.1 (congrFun (congrFun h a) b))

end GlobalTheory.CompanionTheory.GunrClassLev

end
