module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SatakeDualWeyl.StatementF
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.InertBridge

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def Chart (σ : E →ₐ[F] E) (B : Base F E) {a a' : ℕ} (G : Geo σ a a') (v : Pl (F := F)) {L : Type} [Field L]
    [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L) (JS : GL (Fin a') L)
    (JT : GL (Fin (a + a')) L) (ψL : AddChar L ℂ)
    (κ : Matrix (Fin (a + a')) (Fin a') L →+ Matrix (Fin a') (Fin (a + a')) (AE F E))
    (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) →* UA σ G.V'.J)
    (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →* UA σ G.W.J) : Prop :=
  Formalism.UG.IsUnramInv ϖ σL q ∧ Odd q ∧
  JS ∈ Formalism.UG.GLint (Fin a') (Formalism.UG.intL L) ∧ JT ∈ Formalism.UG.GLint (Fin (a + a')) (Formalism.UG.intL L) ∧
  (∀ i j, σL ((JS : Matrix (Fin a') (Fin a') L) i j) = (JS : Matrix (Fin a') (Fin a') L) j i) ∧
  (∀ i j, σL ((JT : Matrix (Fin (a + a')) (Fin (a + a')) L) i j) = (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) j i) ∧
  (Valued.v δ = 1 ∧ σL δ = -δ) ∧
  (∀ z ∈ Formalism.UG.intL L, σL z = z → ψL z = 1) ∧
  (∃ z ∈ Formalism.UG.intL L, σL z = z ∧ ψL (ϖ⁻¹ * z) ≠ 1) ∧
  (∀ x, At (evFin F v) (κ x)) ∧
  (∀ γ : Matrix (Fin a') (Fin (a + a')) (AE F E), At (evFin F v) γ → ∃ x, κ x = γ) ∧
  (∀ x, (∀ i j, x i j ∈ Formalism.UG.intL L) ↔ κ x ∈ latAtV G.V' G.W v) ∧
  (∀ x y, ψL ((GlobalTheory.Hk3.locH σL δ JS JT x y + σL (GlobalTheory.Hk3.locH σL δ JS JT x y)) / 2) =
    B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (κ x) (κ y))) ∧
  (∀ g h x, actAB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (ιS g, ιT h) (κ x) =
    κ (((h : GL (Fin (a + a')) L) : Matrix (Fin (a + a')) (Fin (a + a')) L) * x *
      (((g : GL (Fin a') L)⁻¹ : GL (Fin a') L) : Matrix (Fin a') (Fin a') L))) ∧
  (∀ g, ιS g ∈ UAt σ G.V' (evFin F v)) ∧ (∀ h, ιT h ∈ UAt σ G.W (evFin F v)) ∧
  (∀ g : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L),
    (g : GL (Fin a') L) ∈ Formalism.UG.GLint (Fin a') (Formalism.UG.intL L) → ιS g ∈ GlobalTheory.InertSph.KAt σ G.V' v) ∧
  (∀ h : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L),
    (h : GL (Fin (a + a')) L) ∈ Formalism.UG.GLint (Fin (a + a')) (Formalism.UG.intL L) → ιT h ∈ GlobalTheory.InertSph.KAt σ G.W v)

end GlobalTheory.InertBridge

end
