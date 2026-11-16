import «section 6».SpecialCovariantChains

/-! On a regularized source every RV-pullback locus is represented by
an original-base definable set of existing RV tags. This justifies the
old-tag active-locus presentation in CentripetalData without new names. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}

theorem rvValues_decode (z : (rawRVSpace (M := M) r).domain) :
    rvValues ((rawRVSpace (M := M) r).decode z) = z.val := Classical.choose_spec z.property

theorem rv_definable_iff_values_image (S : Set M) (U : Set (Fin r → RVInfinity M)) :
    (rawRVSpace (M := M) r).Definable S U ↔ S.Definable LRV (rvValues '' U) := by
  have he : (rawRVSpace (M := M) r).preimage U = rvValues '' U := by
    ext z
    constructor
    · rintro ⟨hz,hU⟩
      exact ⟨(rawRVSpace r).decode ⟨z,hz⟩,hU,rvValues_decode _⟩
    · rintro ⟨u,hu,rfl⟩
      refine ⟨Set.mem_range_self u,?_⟩
      have he : (rawRVSpace r).decode ⟨rvValues u,Set.mem_range_self u⟩ = u :=
        rvValues_injective (rvValues_decode _)
      exact he.symm ▸ hu
  change S.Definable LRV _ ↔ _
  rw [he]

def locusTags (A C : DefSet (rawMixedSpace (M := M) n r) S) :
    DefSet (rawRVSpace (M := M) r) S := by
  let H := A.carrier ∩ C.carrier
  have hH : (rawMixedSpace n r).Definable S H := A.definable.inter _ C.definable
  have h := ((mixed_definable_iff_values_image S H).mp hH).image_comp (Sum.inr : Fin r → Fin n ⊕ Fin r)
  refine ⟨Prod.snd '' H,(rv_definable_iff_values_image S _).mpr ?_⟩
  convert h using 1
  ext z
  constructor
  · rintro ⟨_,⟨p,hp,rfl⟩,rfl⟩
    exact ⟨mixedValues p,⟨p,hp,rfl⟩,rfl⟩
  · rintro ⟨_,⟨p,hp,rfl⟩,he⟩
    exact ⟨p.2,⟨p,hp,rfl⟩,he⟩

theorem locus_iff_tags (A C : DefSet (rawMixedSpace (M := M) n r) S)
    (hC : IsRVPullback C.carrier)
    (htag : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1)
    {p : Mixed M n r} (hp : p ∈ A.carrier) : p ∈ C.carrier ↔ p.2 ∈ (locusTags A C).carrier := by
  constructor
  · intro hpc
    exact ⟨p,⟨hp,hpc⟩,rfl⟩
  · rintro ⟨q,⟨hq,hqc⟩,he⟩
    have hh : p ∈ rvHull C.carrier :=
      (mem_rvHull_iff C.carrier p).mpr ⟨q,hqc,htag q hq p hp he,he⟩
    rwa [hC] at hh

theorem focusActive_locus (A C : DefSet (rawMixedSpace (M := M) n r) S)
    (hC : IsRVPullback C.carrier)
    (htag : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1) :
    (focusActive A (locusTags A C)).carrier = A.carrier ∩ C.carrier := by
  ext p
  exact and_congr_right (fun hp => (locus_iff_tags A C hC htag hp).symm)

theorem regularized_tagged (A : Set (Mixed M n r)) :
    ∀ p ∈ regularize '' A, ∀ q ∈ regularize '' A, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1 := by
  rintro _ ⟨p,hp,rfl⟩ _ ⟨q,hq,rfl⟩ he
  funext i
  simpa only [regularize,Fin.append_left] using congrFun he (Fin.castAdd r i)

end DiamondIntegral.Section6
