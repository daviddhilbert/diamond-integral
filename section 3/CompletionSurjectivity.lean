import «section 3».CompletionTensor
set_option autoImplicit false
namespace DiamondIntegral.Section3
open Algebra.GrothendieckAddGroup
universe u v
variable {R : Type u} {T : Type v} [CommSemiring R] [CommSemiring T]

theorem ringCompletionMap_surjective (F : R →+* T) (hF : Function.Surjective F) :
    Function.Surjective (ringCompletionMap F) := by
  intro z
  obtain ⟨a,b,rfl⟩ := exists_eq_sub_of z
  obtain ⟨r,hr⟩ := hF a
  obtain ⟨s,hs⟩ := hF b
  exact ⟨of r - of s,by rw [map_sub,ringCompletionMap_of,ringCompletionMap_of,hr,hs]⟩
end DiamondIntegral.Section3
