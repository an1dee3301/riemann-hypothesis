module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticOrderPrincipal
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Span

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_quadratic_order_principal : ∀ (R O : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R] [CommRing O] (ι : R →+* O) (δ : O) (D : R), δ * δ = ι D → (∀ y : O, ∃ p q : R, y = ι p + ι q * δ) → (∀ p q : R, ι p + ι q * δ = 0 → p = 0 ∧ q = 0) → IsUnit D → IsUnit (2 : R) → (¬ ∃ e : R, D = e * e) → IsPrincipalIdealRing O := by
  first | exact @GlobalTheory.CompanionTheory.QuadraticUnit.isPrincipalIdealRing_of_nonsquare_unit | exact GlobalTheory.CompanionTheory.QuadraticUnit.isPrincipalIdealRing_of_nonsquare_unit | (intros; apply GlobalTheory.CompanionTheory.QuadraticUnit.isPrincipalIdealRing_of_nonsquare_unit <;> assumption)
