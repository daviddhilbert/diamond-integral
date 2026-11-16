import «section 6».RVTagProjection
import Section5.UnaryMaps

/-! Grafting invariant RV data retains every VF coordinate. The actual
same-base map is constructed through the checked tuple concatenation;
its graph fibers are exactly the label fibers with the old tags fixed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r q : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) n r) S}
variable {D : DefSet (rawMixedSpace (M := M) 0 q) S}

def graftMap (hc : CanonicalStructure.IsCanonical (M := M)) (τ : Map A D) :
    Map A (DefSet.univ (rawMixedSpace (M := M) n (r+q)) S) := by
  let A' := toOrdinarySet hc A
  let D' := toOrdinarySet hc D
  exact fromOrdinaryMap hc (SpecialTransformations.Section5.Map.comp
    (SpecialTransformations.Section5.attachRVMap A' D')
    (SpecialTransformations.Section5.Map.pair (SpecialTransformations.Section5.Map.id A') (toOrdinaryMap hc τ)))

def graft (hc : CanonicalStructure.IsCanonical (M := M)) (τ : Map A D) := (graftMap hc τ).toImage

theorem graft_apply (hc : CanonicalStructure.IsCanonical (M := M)) (τ : Map A D) (p : A) :
    (graft hc τ p).val = (p.val.1,Fin.append p.val.2 (τ p).val.2) := rfl

theorem graft_bijective (hc : CanonicalStructure.IsCanonical (M := M)) (τ : Map A D) : Function.Bijective (graft hc τ) := by
  constructor
  · intro p p' he
    have hVF : p.val.1 = p'.val.1 := congrArg (fun x => x.val.1) he
    have hRV : p.val.2 = p'.val.2 := funext (fun i => by
      simpa only [graft_apply,Fin.append_left] using
        congrArg (fun x => x.val.2 (Fin.castAdd q i)) he)
    exact Subtype.ext (Prod.ext hVF hRV)
  · rintro ⟨_,p,rfl⟩
    exact ⟨p,rfl⟩

theorem graft_source_iff (hc : CanonicalStructure.IsCanonical (M := M)) (τ : Map A D)
    (u : Fin r → RVInfinity M) (v : Fin (r+q) → RVInfinity M) (a : Fin n → VF M) :
    a ∈ graphFibreSource (graft hc τ) u v ↔
      u = v ∘ Fin.castAdd q ∧ a ∈ graphFibreSource τ u (v ∘ Fin.natAdd r) := by
  constructor
  · rintro ⟨b,p,hp,hgp⟩
    have hOld := congrArg Prod.snd hp
    rw [graft_apply] at hgp
    have htags := congrArg Prod.snd hgp
    have hu : u = v ∘ Fin.castAdd q := funext (fun i => by
      simpa only [Fin.append_left,Function.comp_apply,hOld] using congrFun htags (Fin.castAdd q i))
    have hnew : (τ p).val.2 = v ∘ Fin.natAdd r := funext (fun i => by
      simpa only [Fin.append_right,Function.comp_apply] using congrFun htags (Fin.natAdd r i))
    exact ⟨hu,(τ p).val.1,p,hp,Prod.ext rfl hnew⟩
  · rintro ⟨hu,b,p,hp,hτp⟩
    refine ⟨a,p,hp,?_⟩
    rw [graft_apply]
    apply Prod.ext
    · exact congrArg (fun x : Mixed M n r => x.1) hp
    · funext i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · have hOld := congrArg (fun x : Mixed M n r => x.2 i) hp
        simpa only [Fin.append_left,Function.comp_apply] using hOld.trans (congrFun hu i)
      · have hNew := congrArg (fun x : Mixed M 0 q => x.2 i) hτp
        simpa only [Fin.append_right,Function.comp_apply] using hNew

theorem graft_range_eq_source (hc : CanonicalStructure.IsCanonical (M := M)) (τ : Map A D)
    (u : Fin r → RVInfinity M) (v : Fin (r+q) → RVInfinity M) :
    graphFibreRange (graft hc τ) u v = graphFibreSource (graft hc τ) u v := by
  ext a
  constructor
  · rintro ⟨b,p,hp,hgp⟩
    have he : b = a := (congrArg Prod.fst hp).symm.trans (congrArg Prod.fst hgp)
    subst b
    exact ⟨a,p,hp,hgp⟩
  · rintro ⟨b,p,hp,hgp⟩
    have he : b = a := (congrArg Prod.fst hgp).symm.trans (congrArg Prod.fst hp)
    subst b
    exact ⟨a,p,hp,hgp⟩

theorem graft_image_fibre (hc : CanonicalStructure.IsCanonical (M := M)) (τ : Map A D)
    (v : Fin (r+q) → RVInfinity M) : vfFibre (graftMap hc τ).image.carrier v =
      graphFibreRange (graft hc τ) (v ∘ Fin.castAdd q) v := by
  ext a
  constructor
  · rintro ⟨p,hp⟩
    change (graft hc τ p).val = (a,v) at hp
    rw [graft_apply] at hp
    have hVF := congrArg Prod.fst hp
    have hOld : p.val.2 = v ∘ Fin.castAdd q := funext (fun i => by
      simpa only [Fin.append_left,Function.comp_apply] using
        congrArg (fun x : Mixed M n (r+q) => x.2 (Fin.castAdd q i)) hp)
    refine ⟨a,p,Prod.ext hVF hOld,?_⟩
    exact (graft_apply hc τ p).trans hp
  · rintro ⟨b,p,hp,hgp⟩
    exact ⟨p,hgp⟩

theorem graft_vfBounded (hc : CanonicalStructure.IsCanonical (M := M)) (τ : Map A D) (hA : VFBounded A.carrier) :
    VFBounded (graftMap hc τ).image.carrier := by
  obtain ⟨γ,hγ⟩ := hA
  exact ⟨γ,by rintro _ ⟨p,rfl⟩ i; exact hγ p.val p.property i⟩

theorem graft_rvBounded (hc : CanonicalStructure.IsCanonical (M := M)) (τ : Map A D)
    (hA : RVSupportDoublyBounded A.carrier) (hτ : RVSupportDoublyBounded (mixedMapRange τ)) :
    RVSupportDoublyBounded (graftMap hc τ).image.carrier := by
  obtain ⟨γ,hγ⟩ := hA
  obtain ⟨δ,hδ⟩ := hτ
  let ε := max γ δ
  have hlowγ : (ε⁻¹).val ≤ (γ⁻¹).val := show ε⁻¹ ≤ γ⁻¹ from inv_le_inv' (le_max_left _ _)
  have hlowδ : (ε⁻¹).val ≤ (δ⁻¹).val := show ε⁻¹ ≤ δ⁻¹ from inv_le_inv' (le_max_right _ _)
  have hhighγ : γ.val ≤ ε.val := le_max_left _ _
  have hhighδ : δ.val ≤ ε.val := le_max_right _ _
  refine ⟨ε,?_⟩
  rintro _ ⟨p,rfl⟩ i
  change (ε⁻¹).val ≤ Values.vrv ((Fin.append p.val.2 (τ p).val.2) i) ∧
    Values.vrv ((Fin.append p.val.2 (τ p).val.2) i) ≤ ε.val
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simpa only [Fin.append_left] using
      And.intro (hlowγ.trans (hγ p.val p.property i).1) ((hγ p.val p.property i).2.trans hhighγ)
  · simpa only [Fin.append_right] using
      And.intro (hlowδ.trans (hδ (τ p).val ⟨p,rfl⟩ i).1) ((hδ (τ p).val ⟨p,rfl⟩ i).2.trans hhighδ)

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem graft_source_clopen (hc : CanonicalStructure.IsCanonical (M := M))
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (τ : Map A D) (hτ : ProperCovariant τ) (u : Fin r → RVInfinity M) (v : Fin (r+q) → RVInfinity M) :
    IsClopen (graphFibreSource (graft hc τ) u v) := by
  classical
  by_cases hu : u = v ∘ Fin.castAdd q
  · have he : graphFibreSource (graft hc τ) u v = graphFibreSource τ u (v ∘ Fin.natAdd r) := by
      ext a
      exact (graft_source_iff hc τ u v a).trans (and_iff_right hu)
    rw [he]
    obtain ⟨α,β,_,_,hInv,_,_⟩ := hτ.radii u (v ∘ Fin.natAdd r)
    exact hInv.isClopen hv
  · have he : graphFibreSource (graft hc τ) u v = ∅ := by
      ext a
      exact ⟨fun ha => False.elim (hu ((graft_source_iff hc τ u v a).mp ha).1),False.elim⟩
    rw [he]
    exact isClopen_empty

end DiamondIntegral.Section6
