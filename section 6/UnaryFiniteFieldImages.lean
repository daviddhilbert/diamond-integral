import «section 6».OriginalBaseOrdinaryMatching
import IntegrationSection5.UnaryVFFibreFinite

/-! Finite field projections remain finite under an actual definable
unary map, even when the retained RV fibres are infinite. This controls
images and inverse images of the ordinary matching's exceptional points. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r s : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S} {B : DefSet (rawMixedSpace (M := M) 1 s) S}

def unaryFixedFieldImage (f : Map A B) (x : VF M) : Set (Fin 1 → VF M) :=
  {y | ∃ p : A,p.val.1 0=x ∧ (f p).val.1=y}

theorem unaryFixedFieldImage_finite
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (f : Map A B) (x : VF M) : (unaryFixedFieldImage f x).Finite := by
  let P := ordinaryNamedGammaBase S
  have h := IntegrationInACVF.Section5.unary_vf_fibre_image_finite hκ hs hsmall (toOrdinaryMap hc f)
    ((SpecialTransformations.Section5.gammaLogicInput P).real_map_graph (toOrdinaryMap hc f)) x
  have hVF := h.preimage (f := fun y : VF M => y.val) Subtype.val_injective.injOn
  apply (hVF.image (fun y => fun _ : Fin 1 => y)).subset
  rintro y ⟨p,hx,rfl⟩
  refine ⟨(f p).val.1 0,⟨p,hx,rfl⟩,?_⟩
  funext i
  fin_cases i
  rfl

def unaryFieldImage (f : Map A B) (E : Set (Mixed M 1 r)) : Set (Fin 1 → VF M) :=
  {y | ∃ p : A,p.val ∈ E ∧ (f p).val.1=y}

theorem unaryFieldImage_finite
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (f : Map A B) (E : Set (Mixed M 1 r)) (hE : (Prod.fst '' E).Finite) :
    (unaryFieldImage f E).Finite := by
  apply (hE.biUnion (fun x _ => unaryFixedFieldImage_finite hc hκ hs hsmall f (x 0))).subset
  rintro y ⟨p,hp,he⟩
  simp only [Set.mem_iUnion]
  exact ⟨p.val.1,⟨p.val,hp,rfl⟩,p,rfl,he⟩

theorem unary_bijection_zero_preimage_finite_vfProjection
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (f : Map A B) (hf : Function.Bijective f) :
    (Prod.fst '' {p : Mixed M 1 r | ∃ a : A,a.val=p ∧ (f a).val.1 0=0}).Finite := by
  let E : Set (Mixed M 1 s) := {q | q.1 0=0}
  have hE : (Prod.fst '' E).Finite := by
    apply (Set.finite_singleton (0 : Fin 1 → VF M)).subset
    rintro x ⟨q,hq,rfl⟩
    apply Set.mem_singleton_iff.mpr
    funext i
    fin_cases i
    exact hq
  apply (unaryFieldImage_finite hc hκ hs hsmall (f.inverse hf) E hE).subset
  rintro x ⟨p,⟨a,rfl,ha⟩,rfl⟩
  refine ⟨f a,ha,?_⟩
  rw [Map.inverse_apply]

end DiamondIntegral.Section6
