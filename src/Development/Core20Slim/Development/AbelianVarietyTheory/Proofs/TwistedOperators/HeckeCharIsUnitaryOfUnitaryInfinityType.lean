module

public import Mathlib
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerOfInfConn
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharFiniteOrderUnitIdele
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfDiagMulFinPartI
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenConnectedComponentOfOneInf
public import Formalism.LocalToGlobal.UnitaryNorms.CharTied
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Order.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.DenseEmbedding
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.UniformSpace.Defs
public import ReciprocityTheory.NeutralLocalFields.Reciprocity

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.HeckeUnitaryInf

theorem isUnitary_of_hasInf : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) {I : Type} [Fintype I]
    (φ : I → L →+* ℂ) (n : I → ℤ), χ.HasInf φ n → χ.IsUnitary := by
  intro L _ _ χ I _ φ n h
  have hinf : ∀ k : Lˣ, ‖((χ.1 (infDiag k) : ℂˣ) : ℂ)‖ = 1 := by
    intro k
    have e : ((χ.1 (infDiag k) : ℂˣ) : ℂ) = _ := h k
    rw [e, norm_prod]
    refine Finset.prod_eq_one fun i _ => ?_
    have h0 : φ i (k : L) ≠ 0 := (map_ne_zero _).2 k.ne_zero
    rw [norm_zpow, norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 h0), one_zpow]
  have hI : ∀ y : (InfiniteAdeleRing L)ˣ, ‖((χ.1 (GlobalTheory.HeckeGal.inlInf L y) : ℂˣ) : ℂ)‖ = 1 := by
    have := (GlobalTheory.HeckeGal.denseRange_units_inf L).equalizer
      (g := fun y => ‖((χ.1 (GlobalTheory.HeckeGal.inlInf L y) : ℂˣ) : ℂ)‖) (h := fun _ => (1 : ℝ))
      ((Units.continuous_val.comp (χ.2.1.comp GlobalTheory.HeckeGal.continuous_inlInf)).norm) continuous_const
      (funext fun k => by
        simp only [Function.comp_apply]
        rw [← GlobalTheory.HeckeGal.infDiag_eq]
        exact hinf k)
    exact fun y => congrFun this y
  have hF : ∀ x : Ideles L, IsFinIdele x → ‖((χ.1 x : ℂˣ) : ℂ)‖ = 1 := by
    intro x hx
    obtain ⟨m, hm, u, k, u1, u2, e⟩ := GlobalTheory.UnUnitCmp.Val.exists_pow_eq x hx
    have e1 := congrArg (fun a => ‖((χ.1 a : ℂˣ) : ℂ)‖) e
    simp only [map_mul, map_pow, Units.val_mul, Units.val_pow_eq_pow_val, norm_mul, norm_pow, hinf k,
      GlobalTheory.HeckeFin.norm_eq_one χ u u1 u2, χ.2.2 k, Units.val_one, norm_one, mul_one] at e1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 e1
  intro z
  have hz : z = GlobalTheory.HeckeGal.inlInf L (Units.map (MonoidHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)) z) *
      finPartI L z := Units.ext (Prod.ext (mul_one _).symm (one_mul _).symm)
  rw [hz, map_mul, Units.val_mul, norm_mul, hI, hF _ (fun _ => rfl), one_mul]

end GlobalTheory.HeckeUnitaryInf
