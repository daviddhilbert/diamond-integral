import «section 6».InitialPreparation
import Section5.VerticalConstruction

/-! Same-base presentation adapters to the checked ordinary special
bijections. Canonicality transports the normalized language structure;
all VF/RV coordinates and their original parameter names are retained. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}

theorem ordinary_point_preimage (H : Set (Mixed M n r)) :
    @Space.preimage LRV M (CanonicalStructure.normalize (M := M))
      (SpecialTransformations.Section5.pointSpace n r) H = mixedValues '' H := by
  ext z
  constructor
  · rintro ⟨hz,hH⟩
    refine ⟨@Space.decode LRV M (CanonicalStructure.normalize (M := M))
      (SpecialTransformations.Section5.pointSpace n r) ⟨z,hz⟩,hH,?_⟩
    funext i
    cases i <;> rfl
  · rintro ⟨p,hp,rfl⟩
    refine ⟨⟨fun i => (p.1 i).property,fun i => (p.2 i).property⟩,?_⟩
    let q : Mixed M n r := @Space.decode LRV M (CanonicalStructure.normalize (M := M))
      (SpecialTransformations.Section5.pointSpace n r)
      ⟨mixedValues p,⟨fun i => (p.1 i).property,fun i => (p.2 i).property⟩⟩
    have hq : mixedValues q = mixedValues p := by
      funext i
      cases i <;> rfl
    exact (mixedValues_injective hq).symm ▸ hp

theorem ordinary_point_definable_iff
    (hc : CanonicalStructure.IsCanonical (M := M)) (H : Set (Mixed M n r)) :
    SpecialTransformations.Section5.SetDefinable (SpecialTransformations.Section5.pointSpace n r) S H ↔
      (rawMixedSpace (M := M) n r).Definable S H := by
  rw [mixed_definable_iff_values_image]
  change (@Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) _
    (@Space.preimage LRV M (CanonicalStructure.normalize (M := M))
      (SpecialTransformations.Section5.pointSpace n r) H)) ↔ _
  rw [ordinary_point_preimage]
  change (@Set.Definable M S LRV (CanonicalStructure.normalize (M := M))
    (Fin n ⊕ Fin r) (mixedValues '' H)) ↔ S.Definable LRV (mixedValues '' H)
  rw [normalize_eq_of_isCanonical hc]

def toOrdinarySet (hc : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (rawMixedSpace (M := M) n r) S) : SpecialTransformations.Section5.DefSet S n r :=
  SpecialTransformations.Section5.PresentedSet.mk A.carrier
    ((ordinary_point_definable_iff hc A.carrier).mpr A.definable)

def fromOrdinarySet (hc : CanonicalStructure.IsCanonical (M := M))
    (A : SpecialTransformations.Section5.DefSet (M := M) S n r) : DefSet (rawMixedSpace (M := M) n r) S :=
  ⟨SpecialTransformations.Section5.carrier A,
    (ordinary_point_definable_iff hc (SpecialTransformations.Section5.carrier A)).mp
      (SpecialTransformations.Section5.setDefinable A)⟩

theorem ordinary_sameRV_iff (p q : Mixed M n r) :
    SpecialTransformations.Section5.SameRV p q ↔ tupleRV M p.1 = tupleRV M q.1 ∧ p.2 = q.2 := by
  rw [SpecialTransformations.Section5.sameRV_iff]
  exact and_congr (by simp only [funext_iff,Section2.tupleRV,Section2.rv,SpecialTransformations.Section5.rv,
    CanonicalRV.encodedRv]) Iff.rfl

theorem ordinary_pullback_iff (H : Set (Mixed M n r)) :
    SpecialTransformations.Section5.IsRVPullback H ↔ IsRVPullback H := by
  have he : SpecialTransformations.Section5.hull H = rvHull H := by
    ext p
    simp only [SpecialTransformations.Section5.hull,Set.mem_setOf_eq,mem_rvHull_iff,
      ordinary_sameRV_iff]
  change (SpecialTransformations.Section5.hull H = H) ↔ rvHull H = H
  rw [he]

end DiamondIntegral.Section6
