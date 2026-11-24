module

public import Development.Core20Slim.Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.RightOnto
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Sum.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Invertible
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

namespace PositivityTheory.KCo

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def ModelEx : Prop := ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)]
  (κ μ : Type) [Fintype κ] [Fintype μ] (ψ : AddChar k ℂ), Continuous ψ → ψ ≠ 1 →
  ∀ e : ((μ → k) × (μ → k)) ≃ₗ[k] ((κ → k) × (κ → k)),
    (∀ w w', (e w).1 ⬝ᵥ (e w').2 - (e w').1 ⬝ᵥ (e w).2 = w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2) →
    ∃ ι : ((κ → k) → ℂ) →ₗ[ℂ] ((μ → k) → ℂ), Set.BijOn ι (SB (κ → k) : Set _) (SB (μ → k) : Set _) ∧
      ∀ w, ∀ φ ∈ SB (κ → k), ι (schr ψ (e w) φ) = schr ψ w (ι φ)

def Cyc : Prop := ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)]
  (κ : Type) [Fintype κ] (ψ : AddChar k ℂ), Continuous ψ → ψ ≠ 1 → ∀ φ₀ ∈ SB (κ → k), φ₀ ≠ 0 →
  ∀ l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ, (∀ w, l (schr ψ w φ₀) = 0) → ∀ φ ∈ SB (κ → k), l φ = 0

section Ad

variable {F : Type} [Field F] [NumberField F]

def sgl (v : Pl F) : Fv F v →ₗ[F] AF F := (LinearMap.inr F (Ainf F) (Af F)).comp (singleFin v)

def psiV (ψ : AddChar (AF F) ℂ) (v : Pl F) : AddChar (Fv F v) ℂ := ψ.compAddMonoidHom (sgl v).toAddMonoidHom

def locW {κ : Type} (v : Pl F) (w : (κ → AF F) × (κ → AF F)) : (κ → Fv F v) × (κ → Fv F v) :=
  (fun i => evFin F v (w.1 i), fun i => evFin F v (w.2 i))

instance invTwo (v : Pl F) : Invertible (2 : Fv F v) := invertibleOfNonzero (by
  have : CharZero (Fv F v) := algebraRat.charZero _
  exact two_ne_zero)

end Ad

structure AdSt : Prop where
  psi : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ψ ≠ 1 ∧ ∀ v : Pl F,
    Continuous (psiV ψ v) ∧ psiV ψ v ≠ 1
  Heisenberg₂ : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ) (v : Pl F)
    (w : (κ → AF F) × (κ → AF F)), At (evFin F v) w → ∀ φ, Acts (evFin F v) (schr ψ w) φ (schr (psiV ψ v) (locW v w) φ)
  rest : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (v : Pl F) (r : (κ → AF F) → ℂ),
    ∀ φ₀ ∈ SB (κ → Fv F v), φ₀ ≠ 0 → Rest (evFin F v) φ₀ r → ∀ φ ∈ SB (κ → Fv F v), Rest (evFin F v) φ r
  act : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (v : Pl F)
    (T : Module.End ℂ ((κ → AF F) → ℂ)) (s : (κ → AF F) × (κ → AF F) → (κ → AF F) × (κ → AF F))
    (L L' : Module.End ℂ ((κ → Fv F v) → ℂ)) (sv : (κ → Fv F v) × (κ → Fv F v) → (κ → Fv F v) × (κ → Fv F v)),
    (∀ Φ ∈ schA F κ, T Φ ∈ schA F κ) → (∀ l ∈ (adeleClass F).adm κ, l ∘ₗ T ∈ (adeleClass F).adm κ) →
    (∀ w, ∀ Φ ∈ schA F κ, T (schr ψ w Φ) = schr ψ (s w) (T Φ)) →
    (∀ φ ∈ SB (κ → Fv F v), L φ ∈ SB (κ → Fv F v) ∧ L' φ ∈ SB (κ → Fv F v) ∧ L' (L φ) = φ ∧ L (L' φ) = φ) →
    (∀ w, ∀ φ ∈ SB (κ → Fv F v), L (schr (psiV ψ v) w φ) = schr (psiV ψ v) (sv w) (L φ)) →
    (∀ w, locW v (s w) = sv (locW v w) ∧ At (evFin F v) (s w - w)) →
    ∃ c : ℂ, ∀ φ ∈ SB (κ → Fv F v), Acts (evFin F v) T φ (c • L φ)
  diag : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ) (v : Pl F),
    ∃ l ∈ (adeleClass F).adm (κ ⊕ κ),
      (∀ (x y : κ → AF F), ∀ Φ ∈ schA F (κ ⊕ κ), l (schr ψ (Sum.elim x x, Sum.elim y (-y)) Φ) = l Φ) ∧
      ∃ φ ∈ SB (κ → Fv F v), ∃ r, Rest (evFin F v) φ r ∧ Rest (evFin F v) (boxFun φ φ) (boxFun r r) ∧
        l (boxFun (tens (evFin F v) φ r) (tens (evFin F v) φ r)) ≠ 0

section Sec

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {v : Pl F}
  (t : E →ₐ[F] Fv F v)

structure IsSec (sec : Fv F v × Fv F v → AE F E) : Prop where
  at' : ∀ x, At (evFin F v) (sec x)
  fst : ∀ x, piW t (sec x) = x.1
  snd : ∀ x, piW (t.comp σ) (sec x) = x.2
  ext : ∀ z : AE F E, At (evFin F v) z → piW t z = 0 → piW (t.comp σ) z = 0 → z = 0
  conj : ∀ z : AE F E, piW t (cA σ z) = piW (t.comp σ) z ∧ piW (t.comp σ) (cA σ z) = piW t z
  atConj : ∀ z : AE F E, At (evFin F v) z → At (evFin F v) (cA σ z)
  smul : ∀ (a : AF F) (z : AE F E), piW t (a • z) = evFin F v a * piW t z ∧
    piW (t.comp σ) (a • z) = evFin F v a * piW (t.comp σ) z
  inc : ∀ x : E, piW t (inclR (F := F) (AF F) x) = t x ∧ piW (t.comp σ) (inclR (F := F) (AF F) x) = t (σ x)
  trace : ∀ z : AE F E, At (evFin F v) z → Algebra.trace (AF F) (AE F E) z = sgl v (piW t z + piW (t.comp σ) z)
  idele : ∀ (z : (AE F E)ˣ) (x : (Fv F v)ˣ), At (evFin F v) ((z : AE F E) - 1) → piW t z = x → piW (t.comp σ) z = 1 →
    (∀ χ : Chr F E, (χ z : ℂ) = (chrW χ t x : ℂ)) ∧
      ((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) z) : ℝ) = GlobalTheory.SplitWeil.nabs (Fv F v) x

end Sec

def SecSt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v), (∃ sec, IsSec σ t sec) ∧ ∀ χ : Chr F E, IsHecke F E χ → USm (chrW χ t)

end PositivityTheory.KCo
