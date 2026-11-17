import «section 3».GammaGroundRVProducts
import «section 3».GammaGroundPointIsomorphisms
import «section 5».NativeMixedKeyMaps

/-! Appending an actual RV-valued map to a mixed point is an original
base bijection onto its graph, fixing VF and retaining all old labels.
Finite RV fibres are preserved by an explicit finite-image argument. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}
variable {n r l : ℕ} (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r))
variable {R : GammaGroundDefSet hc B (rawRVSpace (M := M) l)} (K : GammaGroundMap A R)

def gammaMixedAttachRV : GammaGroundMap A (GammaGroundDefSet.univ hc B (rawMixedSpace (M := M) n (r+l))) :=
  ((GammaGroundMap.ofGlobal A (GammaGroundDefSet.univ hc B (rawVFSpace (M := M) n))
    (universalProductFst (rawVFSpace n) (rawRVSpace r) B.real)
    (fun _ => Set.mem_univ _)).pair
    (gammaGroundRVAppendTargets.comp ((Section5.nativeMixedRVProjection A).pair K.toUniv))).toUniv

theorem gammaMixedAttachRV_value (p : A) :
    (gammaMixedAttachRV A K p).val = (p.val.1,Fin.append p.val.2 (K p).val) := rfl

theorem gammaMixedAttachRV_injective : Function.Injective (gammaMixedAttachRV A K) := by
  intro p q hpq
  have he := congrArg Subtype.val hpq
  have hPair : (p.val.1,Fin.append p.val.2 (K p).val) = (q.val.1,Fin.append q.val.2 (K q).val) := he
  have hVF := congrArg Prod.fst hPair
  have hr := congrArg Prod.snd hPair
  apply Subtype.ext
  refine Prod.ext hVF ?_
  funext i
  exact (Fin.append_left _ _ i).symm.trans ((congrFun hr (Fin.castAdd l i)).trans (Fin.append_left _ _ i))

def gammaMixedAttachRVBijection : GammaGroundBijection A (gammaMixedAttachRV A K).image :=
  ⟨(gammaMixedAttachRV A K).toImage,(gammaMixedAttachRV A K).toImage_bijective (gammaMixedAttachRV_injective A K)⟩

theorem gammaMixedAttachRV_inverse_new_labels (p : (gammaMixedAttachRV A K).image) :
    (K ((gammaMixedAttachRVBijection A K).symm.map p)).val = p.val.2 ∘ Fin.natAdd r := by
  let e := gammaMixedAttachRVBijection A K
  let q := e.symm.map p
  have he : e.map q = p := e.map.apply_inverse e.bijective p
  have hPair : (q.val.1,Fin.append q.val.2 (K q).val) = p.val := congrArg Subtype.val he
  have hRV := congrArg Prod.snd hPair
  funext j
  exact (Fin.append_right _ _ j).symm.trans (congrFun hRV (Fin.natAdd r j))

theorem gammaMixedAttachRV_finite (hfin : ∀ x, {r | (x,r) ∈ A.carrier}.Finite) :
    ∀ x, {r | (x,r) ∈ (gammaMixedAttachRV A K).image.carrier}.Finite := by
  intro x
  let k : (Fin r → CanonicalRV.RVSort M) → Fin l → CanonicalRV.RVSort M := fun u =>
    if h : (x,u) ∈ A.carrier then (K ⟨(x,u),h⟩).val else fun _ => 0
  apply ((hfin x).image (fun u => Fin.append u (k u))).subset
  rintro u ⟨p,hp⟩
  have hPair : (p.val.1,Fin.append p.val.2 (K p).val) = (x,u) := hp
  have hx := congrArg Prod.fst hPair
  have hR := congrArg Prod.snd hPair
  have hm : (x,p.val.2) ∈ A.carrier := by
    exact Eq.mp (congrArg (fun z => (z,p.val.2) ∈ A.carrier) hx) p.property
  have he : (⟨(x,p.val.2),hm⟩ : A) = p := Subtype.ext (Prod.ext hx.symm rfl)
  refine ⟨p.val.2,hm,?_⟩
  have hk : k p.val.2 = (K p).val := by
    dsimp [k]
    rw [dite_eq_left hm,he]
  exact (congrArg (Fin.append p.val.2) hk).trans hR

end DiamondIntegral.Section3
