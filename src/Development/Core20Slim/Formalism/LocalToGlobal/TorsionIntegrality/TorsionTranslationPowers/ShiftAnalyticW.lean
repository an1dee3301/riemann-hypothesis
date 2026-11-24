module

public import Development.Core20Slim.Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.AnaSysW
public import Development.Core20Slim.Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.TransW
public import Development.Core20Slim.Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementW

@[expose] public section

namespace Formalism.L2.Th1.E

theorem ptWZero : PtWZero := analytic_point_eq_zero_iff
theorem ptWAdd : PtWAdd := analytic_point_map_add

end Formalism.L2.Th1.E
