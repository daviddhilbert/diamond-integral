import «section 3».CompletionSurjectivity
import Mathlib.RingTheory.Ideal.Quotient.Operations
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section3
open Algebra.GrothendieckAddGroup
universe u v w
variable {R : Type u} {T : Type v} [CommSemiring R] [CommSemiring T]

/-- A proved positive presentation gives the ring presentation by the
differences of exactly its positive generators. -/
def completedKernelQuotientEquiv (F : R →+* T) (hF : Function.Surjective F)
    (r : R → R → Prop) (hr : ringConGen r = RingCon.ker F) :
    RingCompletion R ⧸ relationIdeal r ≃+* RingCompletion T :=
  (completedCongruenceEquiv r).symm.trans
    (ringCompletionCongr (semiringIntegralFromKernel F hF (ringConGen r) hr).symm)

@[simp] theorem completedKernelQuotientEquiv_of (F : R →+* T) (hF : Function.Surjective F)
    (r : R → R → Prop) (hr : ringConGen r = RingCon.ker F) (a : R) :
    completedKernelQuotientEquiv F hF r hr (Ideal.Quotient.mk (relationIdeal r) (of a)) = of (F a) := by
  let E := semiringIntegralFromKernel F hF (ringConGen r) hr
  have ha : E (F a) = (ringConGen r).mk' a :=
    (semiringIntegralFromKernel_characterization F hF (ringConGen r) hr (F a) a).mpr rfl
  change ringCompletionCongr E.symm ((completedCongruenceEquiv r).symm
    (Ideal.Quotient.mk (relationIdeal r) (of a))) = of (F a)
  rw [← completedCongruenceEquiv_generator r a, RingEquiv.symm_apply_apply,
    ringCompletionCongr_of, ← ha, E.symm_apply_apply]

theorem completedKernelQuotientEquiv_comp (F : R →+* T) (hF : Function.Surjective F)
    (r : R → R → Prop) (hr : ringConGen r = RingCon.ker F) :
    (completedKernelQuotientEquiv F hF r hr).toRingHom.comp (Ideal.Quotient.mk (relationIdeal r)) =
      ringCompletionMap F := by
  apply ringHom_ext
  intro a
  exact (completedKernelQuotientEquiv_of F hF r hr a).trans (ringCompletionMap_of F a).symm

theorem relationIdeal_eq_completed_kernel (F : R →+* T) (hF : Function.Surjective F)
    (r : R → R → Prop) (hr : ringConGen r = RingCon.ker F) :
    relationIdeal r = RingHom.ker (ringCompletionMap F) := by
  ext x
  have hx := RingHom.congr_fun (completedKernelQuotientEquiv_comp F hF r hr) x
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] at hx
  change x ∈ relationIdeal r ↔ ringCompletionMap F x = 0
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← hx]
  exact ⟨fun h => by rw [h,map_zero], fun h =>
    (completedKernelQuotientEquiv F hF r hr).injective (h.trans (map_zero _).symm)⟩

variable {S : Type w} [CommRing S]

/-- Presentation in an explicitly identified ring, such as the tensor of
the three ring completions, retains the actual generator differences. -/
def transportedRelationIdeal (e : RingCompletion R ≃+* S) (r : R → R → Prop) : Ideal S :=
  Ideal.span {z | ∃ a b, r a b ∧ z = e (of a) - e (of b)}

theorem transportedRelationIdeal_eq_map (e : RingCompletion R ≃+* S) (r : R → R → Prop) :
    transportedRelationIdeal e r = Ideal.map e.toRingHom (relationIdeal r) := by
  unfold transportedRelationIdeal relationIdeal
  rw [Ideal.map_span]
  apply congrArg Ideal.span
  ext z
  constructor
  · rintro ⟨a,b,hab,rfl⟩
    exact ⟨of a-of b,⟨a,b,hab,rfl⟩,map_sub e _ _⟩
  · rintro ⟨x,⟨a,b,hab,rfl⟩,rfl⟩
    exact ⟨a,b,hab,map_sub e _ _⟩

theorem transportedRelationIdeal_eq_kernel (F : R →+* T) (hF : Function.Surjective F)
    (r : R → R → Prop) (hr : ringConGen r = RingCon.ker F)
    (e : RingCompletion R ≃+* S) :
    transportedRelationIdeal e r = RingHom.ker ((ringCompletionMap F).comp e.symm.toRingHom) := by
  rw [transportedRelationIdeal_eq_map,relationIdeal_eq_completed_kernel F hF r hr]
  ext z
  rw [Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective]
  change (∃ x, ringCompletionMap F x = 0 ∧ e x = z) ↔ ringCompletionMap F (e.symm z) = 0
  constructor
  · rintro ⟨x,hx,rfl⟩
    simpa only [e.symm_apply_apply] using hx
  · intro hz
    exact ⟨e.symm z,hz,e.apply_symm_apply z⟩

end DiamondIntegral.Section3
