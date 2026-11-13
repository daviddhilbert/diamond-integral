import IntegrationSection6.KernelEquivalence
import IntegrationSection6.FiniteIntegrationEquivalence
import IntegrationSection6.GlobalIntegrationCharacterization
import IntegrationSection6.GammaNonzeroPrincipalIdeal

/-! Exact later [18] proof exports at 7d4acc730496b3bd05a22c268ffd89540ca694f9.
The section 5.8 input, the definably closed generated base and every native
category/presentation remain visible in their full types. These exports do
not by themselves construct the legacy Yin lift-input records. Measured
section 7 is not supplied by the unmeasured section 6 results. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section3

abbrev integration_lemma_6_17 := @IntegrationInACVF.Section6.FiniteRV.lemma_6_17
abbrev integration_proposition_6_18 := @IntegrationInACVF.Section6.FiniteRV.proposition_6_18
abbrev integration_proposition_6_18_lift := @IntegrationInACVF.Section6.FiniteRV.proposition_6_18_lift
abbrev integration_theorem_6_19 := @IntegrationInACVF.Section6.FiniteRV.theorem_6_19
abbrev integration_theorem_6_19_lift := @IntegrationInACVF.Section6.FiniteRV.theorem_6_19_lift_finite
abbrev integration_theorem_6_19_characterization :=
  @IntegrationInACVF.Section6.FiniteRV.theorem_6_19_characterization
abbrev integration_nonzero_basic_congruence :=
  @IntegrationInACVF.Section6.FiniteRV.gammaNonzeroIsp_eq_resolved_basic
abbrev integration_nonzero_principal_ideal :=
  @IntegrationInACVF.Section6.FiniteRV.gammaNonzeroIsp_relationIdeal_j
abbrev integration_nonzero_completion_quotient :=
  @IntegrationInACVF.Section6.FiniteRV.gammaNonzeroCompletionQuotientEquiv
abbrev integration_nonzero_completion_quotient_of :=
  @IntegrationInACVF.Section6.FiniteRV.gammaNonzeroCompletionQuotientEquiv_of

end DiamondIntegral.Section3
