import «section 6».OrdinaryPresentation

/-! Complete graph adapters between the ordinary special-bijection
presentation and the raw mixed spaces used in this section. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m r s : ℕ} {S : Set M}

def ordinaryPointCode (p : Mixed M n r) :
    @Space.domain LRV M (CanonicalStructure.normalize (M := M)) (SpecialTransformations.Section5.pointSpace n r) :=
  ⟨mixedValues p,⟨fun i => (p.1 i).property,fun i => (p.2 i).property⟩⟩

theorem ordinary_values_decode
    (z : @Space.domain LRV M (CanonicalStructure.normalize (M := M)) (SpecialTransformations.Section5.pointSpace n r)) :
    mixedValues (@Space.decode LRV M (CanonicalStructure.normalize (M := M))
      (SpecialTransformations.Section5.pointSpace n r) z) = z.val := by
  funext i
  cases i <;> rfl

theorem ordinary_decode_values (p : Mixed M n r) :
    @Space.decode LRV M (CanonicalStructure.normalize (M := M))
      (SpecialTransformations.Section5.pointSpace n r) (ordinaryPointCode p) = p :=
  mixedValues_injective (ordinary_values_decode _)

theorem ordinary_relation_eq_raw (R : Mixed M n r → Mixed M m s → Prop) :
    @Space.relation LRV M (CanonicalStructure.normalize (M := M))
      (SpecialTransformations.Section5.pointSpace n r) (SpecialTransformations.Section5.pointSpace m s) R =
      (rawMixedSpace n r).relation (rawMixedSpace m s) R := by
  ext z
  constructor
  · rintro ⟨hx,hy,hR⟩
    let p := @Space.decode LRV M (CanonicalStructure.normalize (M := M))
      (SpecialTransformations.Section5.pointSpace n r) ⟨z ∘ Sum.inl,hx⟩
    let q := @Space.decode LRV M (CanonicalStructure.normalize (M := M))
      (SpecialTransformations.Section5.pointSpace m s) ⟨z ∘ Sum.inr,hy⟩
    have hp : mixedValues p = z ∘ Sum.inl := ordinary_values_decode _
    have hq : mixedValues q = z ∘ Sum.inr := ordinary_values_decode _
    have hd : Sum.elim (mixedValues p) (mixedValues q) = z := by
      funext i
      cases i with
      | inl i => exact congrFun hp i
      | inr i => exact congrFun hq i
    rw [← hd]
    have h := (rawMixedSpace n r).relation_decode (rawMixedSpace m s) R
      ⟨mixedValues p,mixedValues_mem_domain p⟩ ⟨mixedValues q,mixedValues_mem_domain q⟩
    rw [decode_mixedValues,decode_mixedValues] at h
    exact h.mpr hR
  · rintro ⟨hx,hy,hR⟩
    let p := (rawMixedSpace n r).decode ⟨z ∘ Sum.inl,hx⟩
    let q := (rawMixedSpace m s).decode ⟨z ∘ Sum.inr,hy⟩
    have hp : mixedValues p = z ∘ Sum.inl := mixedValues_decode _
    have hq : mixedValues q = z ∘ Sum.inr := mixedValues_decode _
    have hd : Sum.elim (mixedValues p) (mixedValues q) = z := by
      funext i
      cases i with
      | inl i => exact congrFun hp i
      | inr i => exact congrFun hq i
    rw [← hd]
    have h := @Space.relation_decode LRV M (CanonicalStructure.normalize (M := M))
      (SpecialTransformations.Section5.pointSpace n r) (SpecialTransformations.Section5.pointSpace m s) R
      (ordinaryPointCode p) (ordinaryPointCode q)
    simpa only [ordinary_decode_values,ordinaryPointCode] using h.mpr hR

theorem ordinary_relation_definable_iff
    (hc : CanonicalStructure.IsCanonical (M := M)) (R : Mixed M n r → Mixed M m s → Prop) :
    SpecialTransformations.Section5.RelationDefinable
      (SpecialTransformations.Section5.pointSpace n r) (SpecialTransformations.Section5.pointSpace m s) S R ↔
      (rawMixedSpace n r).RelationDefinable (rawMixedSpace m s) S R := by
  change (@Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) _ _) ↔ _
  rw [ordinary_relation_eq_raw]
  change (@Set.Definable M S LRV (CanonicalStructure.normalize (M := M))
    ((Fin n ⊕ Fin r) ⊕ (Fin m ⊕ Fin s)) _) ↔ S.Definable LRV _
  rw [normalize_eq_of_isCanonical hc]

def fromOrdinaryMap (hc : CanonicalStructure.IsCanonical (M := M))
    {A : SpecialTransformations.Section5.DefSet (M := M) S n r}
    {B : SpecialTransformations.Section5.DefSet (M := M) S m s}
    (f : SpecialTransformations.Section5.Map A B) : Map (fromOrdinarySet hc A) (fromOrdinarySet hc B) :=
  ⟨f,(ordinary_relation_definable_iff hc _).mp (SpecialTransformations.Section5.Map.graph_definable f)⟩

def toOrdinaryMap (hc : CanonicalStructure.IsCanonical (M := M))
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) m s) S}
    (f : Map A B) : SpecialTransformations.Section5.Map (toOrdinarySet hc A) (toOrdinarySet hc B) :=
  SpecialTransformations.Section5.Map.mk f ((ordinary_relation_definable_iff hc _).mpr f.graph_definable)

end DiamondIntegral.Section6
