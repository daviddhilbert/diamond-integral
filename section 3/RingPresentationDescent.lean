import «section 3».CompletedKernelPresentation
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section3
open Algebra.GrothendieckAddGroup
universe u v w x
variable {R : Type u} [CommSemiring R]
variable {S : Type v} {T : Type w} {V : Type x}
variable [CommRing S] [CommRing T] [CommRing V]

/-- Testing the displayed positive pairs is exactly testing the whole
ideal after passage to the explicitly identified ring. -/
theorem transportedRelationIdeal_le_kernel_iff
    (e : RingCompletion R ≃+* S) (r : R → R → Prop) (H : S →+* V) :
    transportedRelationIdeal e r ≤ RingHom.ker H ↔
      ∀ a b, r a b → H (e (of a)) = H (e (of b)) := by
  constructor
  · intro h a b hab
    have hz := h (Ideal.subset_span (show e (of a) - e (of b) ∈
      {z | ∃ a b, r a b ∧ z = e (of a) - e (of b)} from ⟨a,b,hab,rfl⟩))
    change H (e (of a) - e (of b)) = 0 at hz
    exact sub_eq_zero.mp ((map_sub H _ _).symm.trans hz)
  · intro h
    apply Ideal.span_le.mpr
    rintro z ⟨a,b,hab,rfl⟩
    change H (e (of a) - e (of b)) = 0
    rw [map_sub,h a b hab,sub_self]

def ringPresentationQuotientEquiv (F : S →+* T) (hF : Function.Surjective F)
    (I : Ideal S) (hI : RingHom.ker F = I) : S ⧸ I ≃+* T :=
  (Ideal.quotEquivOfEq hI.symm).trans (RingHom.quotientKerEquivOfSurjective hF)

@[simp] theorem ringPresentationQuotientEquiv_mk
    (F : S →+* T) (hF : Function.Surjective F) (I : Ideal S) (hI : RingHom.ker F = I) (a : S) :
    ringPresentationQuotientEquiv F hF I hI (Ideal.Quotient.mk I a) = F a := by
  change F.quotientKerEquivOfSurjective hF (Ideal.quotEquivOfEq hI.symm (Ideal.Quotient.mk I a)) = F a
  rw [Ideal.quotEquivOfEq_mk,RingHom.quotientKerEquivOfSurjective_apply_mk]

/-- Descent uses the complete kernel ideal and never cancels a class. -/
def ringPresentationDescend (F : S →+* T) (hF : Function.Surjective F)
    (I : Ideal S) (hI : RingHom.ker F = I) (H : S →+* V) (hH : I ≤ RingHom.ker H) : T →+* V :=
  (Ideal.Quotient.lift I H hH).comp (ringPresentationQuotientEquiv F hF I hI).symm.toRingHom

@[simp] theorem ringPresentationDescend_image (F : S →+* T) (hF : Function.Surjective F)
    (I : Ideal S) (hI : RingHom.ker F = I) (H : S →+* V) (hH : I ≤ RingHom.ker H) (a : S) :
    ringPresentationDescend F hF I hI H hH (F a) = H a := by
  let E := ringPresentationQuotientEquiv F hF I hI
  change Ideal.Quotient.lift I H hH (E.symm (F a)) = H a
  rw [← ringPresentationQuotientEquiv_mk F hF I hI a,E.symm_apply_apply]
  rfl

theorem ringPresentationDescend_unique (F : S →+* T) (hF : Function.Surjective F)
    (I : Ideal S) (hI : RingHom.ker F = I) (H : S →+* V) (hH : I ≤ RingHom.ker H)
    (D : T →+* V) (hD : D.comp F = H) : D = ringPresentationDescend F hF I hI H hH := by
  apply RingHom.ext
  intro z
  obtain ⟨a,rfl⟩ := hF z
  exact (RingHom.congr_fun hD a).trans (ringPresentationDescend_image F hF I hI H hH a).symm

theorem ringPresentation_descends_iff (F : S →+* T) (hF : Function.Surjective F)
    (I : Ideal S) (hI : RingHom.ker F = I) (H : S →+* V) :
    (∃ D : T →+* V, D.comp F = H) ↔ I ≤ RingHom.ker H := by
  constructor
  · rintro ⟨D,hD⟩ a ha
    rw [← hI] at ha
    change H a = 0
    rw [← RingHom.congr_fun hD a]
    change D (F a) = 0
    rw [show F a = 0 from ha,map_zero]
  · intro hH
    exact ⟨ringPresentationDescend F hF I hI H hH,
      RingHom.ext (ringPresentationDescend_image F hF I hI H hH)⟩

end DiamondIntegral.Section3
