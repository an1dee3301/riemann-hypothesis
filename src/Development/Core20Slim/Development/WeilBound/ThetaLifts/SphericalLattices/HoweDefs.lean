module

public import Development.Core20Slim.Development.WeilBound.ThetaLifts.SphericalLattices.HoweInert
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Development.Core20Slim.Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.InertDef
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SatakeDualWeyl.StatementF
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

namespace PositivityTheory.Sph

open scoped Matrix
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

def LocData {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (om : Rep σ X W) (v : Pl F) : Prop :=
  ∃ (L : Type) (_ : Field L) (_ : CharZero L) (_ : Valued L (WithZero (Multiplicative ℤ))) (_ : CompleteSpace L)
    (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L) (JS : GL (Fin n) L) (JT : GL (Fin d) L) (ψL : AddChar L ℂ)
    (ρL : Matrix (Fin d) (Fin n) L → Module.End ℂ (SB (Fin n × Fin d → Fv F v)))
    (ωL : Formalism.UG.UJ σL (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σL (JT : Matrix (Fin d) (Fin d) L) →*
      Module.End ℂ (SB (Fin n × Fin d → Fv F v)))
    (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin n) (Fin n) L) →* UA σ X.J)
    (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin d) (Fin d) L) →* UA σ W.J) (s : SB (Fin n × Fin d → Fv F v)),
    GlobalTheory.Hk3.LocPair ϖ σL q δ JS JT ψL ρL ωL ∧ s ≠ 0 ∧ GlobalTheory.Hk3.LocVac ρL s ∧
    Submodule.span ℂ (Set.range fun x => ρL x s) = ⊤ ∧ (s : (Fin n × Fin d → Fv F v) → ℂ) = M.vac v ∧
    (∀ g, ιS g ∈ UAt σ X (evFin F v)) ∧ (∀ h, ιT h ∈ UAt σ W (evFin F v)) ∧
    (∀ g : Formalism.UG.UJ σL (JS : Matrix (Fin n) (Fin n) L),
      (g : GL (Fin n) L) ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → ιS g ∈ GlobalTheory.InertSph.KAt σ X v) ∧
    (∀ h : Formalism.UG.UJ σL (JT : Matrix (Fin d) (Fin d) L),
      (h : GL (Fin d) L) ∈ Formalism.UG.GLint (Fin d) (Formalism.UG.intL L) → ιT h ∈ GlobalTheory.InertSph.KAt σ W v) ∧
    ∀ g h (m : SB (Fin n × Fin d → Fv F v)) (φ₁ : (Fin n × Fin d → Fv F v) → ℂ), φ₁ ∈ SB (Fin n × Fin d → Fv F v) →
      (Acts (evFin F v) (om (ιS g, ιT h)) (m : (Fin n × Fin d → Fv F v) → ℂ) φ₁ ↔
        ((ωL (g, h) m : SB (Fin n × Fin d → Fv F v)) : (Fin n × Fin d → Fv F v) → ℂ) = φ₁)

theorem kAt_eq (X : Spc F E n) (v : Pl F) : KAt σ X v = GlobalTheory.InertSph.KAt σ X v := rfl

end PositivityTheory.Sph

end
