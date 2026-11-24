module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.TwistedScalarSection
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.DerivativeVacuumDilationsAlt
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SProd
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open MeasureTheory Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

theorem cont_KR_mul (n : ℕ) (y k1 : GR n) : Continuous (fun k : KR n => y * (k : GR n) * k1) :=
  (continuous_const.mul continuous_subtype_val).mul continuous_const

theorem cont_KR_mul' (n : ℕ) (k1 : GR n) : Continuous (fun k : KR n => (k : GR n) * k1) :=
  continuous_subtype_val.mul continuous_const

theorem mR_mul {n : ℕ} (a b : GR n) : mR (a * b) = mR a * mR b := rfl

theorem spherical_section_eq_extension {n : ℕ} (p q : ℕ) (e : ℤ) (g : GR n) : F0 p q e g = twistedScalarSection p q e (mR g) := by
  simp only [F0, twistedScalarSection]

theorem inK_mul {n : ℕ} (k : KR n) (k1 : GR n) (hk1 : k1 ∈ KR n) : InK (mR ((k : GR n) * k1)) :=
  (KR n).mul_mem k.2 hk1

theorem continuousOn_twisted_section_compact {n : ℕ} (p q : ℕ) (e : ℤ) (X : Fin n → ℝ) (y k1 : GR n) (U : Set ℂ) (κ : KR n → ℂ)
    (hκ : Continuous κ) (C : Set (GR n)) (hC : ∀ k : KR n, y * (k : GR n) * k1 ∈ C)
    (hU2c : ContinuousOn (fun yz : GR n × ℂ => twistedScalarSection p q e (mR yz.1 * aZ X yz.2)) (C ×ˢ U)) :
    ContinuousOn (fun yz : KR n × ℂ => κ yz.1 * twistedScalarSection p q e (mR (y * (yz.1 : GR n) * k1) * aZ X yz.2)) (univ ×ˢ U) := by
  refine (hκ.comp continuous_fst).continuousOn.mul ?_
  have hφ : Continuous (fun yz : KR n × ℂ => (y * (yz.1 : GR n) * k1, yz.2)) :=
    ((cont_KR_mul n y k1).comp continuous_fst).prodMk continuous_snd
  have hcmp : (fun yz : KR n × ℂ => twistedScalarSection p q e (mR (y * (yz.1 : GR n) * k1) * aZ X yz.2)) =
      (fun yz : GR n × ℂ => twistedScalarSection p q e (mR yz.1 * aZ X yz.2)) ∘ (fun yz : KR n × ℂ => (y * (yz.1 : GR n) * k1, yz.2)) :=
    funext fun _ => rfl
  rw [hcmp]
  exact ContinuousOn.comp (g := fun yz : GR n × ℂ => twistedScalarSection p q e (mR yz.1 * aZ X yz.2)) hU2c hφ.continuousOn
    (fun yz hyz => ⟨hC yz.1, hyz.2⟩)

theorem contOn_Fid {n : ℕ} (k1 : GR n) (U U1 : Set ℂ) (hUU : U ⊆ U1) (κ : KR n → ℂ) (hκ : Continuous κ)
    (Fid : GR n → ℂ → ℂ) (hFidc : ContinuousOn (fun y : GR n × ℂ => Fid y.1 y.2) (univ ×ˢ U1)) :
    ContinuousOn (fun yz : KR n × ℂ => κ yz.1 * Fid ((yz.1 : GR n) * k1) yz.2) (univ ×ˢ U) := by
  refine (hκ.comp continuous_fst).continuousOn.mul ?_
  have hφ : Continuous (fun yz : KR n × ℂ => ((yz.1 : GR n) * k1, yz.2)) :=
    ((cont_KR_mul' n k1).comp continuous_fst).prodMk continuous_snd
  have hcmp : (fun yz : KR n × ℂ => Fid ((yz.1 : GR n) * k1) yz.2) =
      (fun y : GR n × ℂ => Fid y.1 y.2) ∘ (fun yz : KR n × ℂ => ((yz.1 : GR n) * k1, yz.2)) :=
    funext fun _ => rfl
  rw [hcmp]
  exact ContinuousOn.comp (g := fun y : GR n × ℂ => Fid y.1 y.2) hFidc hφ.continuousOn
    (fun yz hyz => ⟨mem_univ _, hUU hyz.2⟩)

end PositivityTheory.Rg.Sw.AbsSt
