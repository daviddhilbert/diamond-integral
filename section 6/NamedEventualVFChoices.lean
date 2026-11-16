import «section 6».NamedFiniteNeighborhoods
import «section 6».NamedVFValues
import «section 2».ZeroFacesVF

/-! A definable property true at every sufficiently small nonzero VF
point admits a positive VF witness named over the original base. The
local unnamed radius is eliminated through the full neighborhood formula. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_named_vf_in_eventual_property
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (P : Set (VF M)) (hP : S.Definable₁ LRV (Subtype.val '' P))
    (hEventual : ∃ η : Gamma M,∀ x : VF M,x ≠ 0 → η.val < vfValue x → x ∈ P) :
    ∃ c : VF M,c ≠ 0 ∧ S.Definable₁ LRV {c.val} ∧ (1 : GammaInfinity M) < vfValue c ∧ c ∈ P := by
  let Q := P ∪ {(0 : VF M)}
  have hQ : S.Definable₁ LRV (Subtype.val '' Q) := by
    have hImage : Subtype.val '' Q=Subtype.val '' P ∪ {(0 : VF M).val} := by
      change Subtype.val '' (P ∪ {(0 : VF M)})=Subtype.val '' P ∪ {(0 : VF M).val}
      rw [Set.image_union,Set.image_singleton]
    rw [hImage]
    exact hP.union (vfZero_singleton_definable S)
  have hNear : Q ∈ 𝓝 (0 : VF M) := by
    obtain ⟨η,hη⟩ := hEventual
    have h0 : (0 : VF M) ∈ centeredGammaDisc 0 η := Set.mem_insert _ _
    apply Filter.mem_of_superset ((centeredGammaDisc_clopen hv (0 : VF M) η).isOpen.mem_nhds h0)
    intro x hx
    by_cases hx0 : x=0
    · exact Or.inr hx0
    · exact Or.inl (hη x hx0 (by simpa only [sub_zero] using (mem_centeredGammaDisc (0 : VF M) x η).mp hx))
  let C : Set (Fin 1 → VF M) := {fun _ => 0}
  have hC : S.Definable LRV (vfValues '' C) := by
    have hZero := vfZero_singleton_definable S
    change S.Definable LRV {z : Fin 1 → M | z 0=(0 : VF M).val} at hZero
    convert hZero using 1
    ext z
    constructor
    · rintro ⟨a,ha,he⟩
      have ha0 : a=(fun _ : Fin 1 => (0 : VF M)) := ha
      subst a
      exact (congrFun he 0).symm
    · intro hz
      change z 0=(0 : VF M).val at hz
      refine ⟨fun _ => 0,rfl,?_⟩
      funext i
      fin_cases i
      exact hz.symm
  let R : Set (Fin 1 ⊕ Fin 1 → M) := {z | z (.inr 0) ∈ Subtype.val '' Q}
  have hR : S.Definable LRV R := hQ.preimage_comp (Sum.inr : Fin 1 → Fin 1 ⊕ Fin 1)
  have hNearC (q : Fin 1 → VF M) (hq : q ∈ C) :
      {x : VF M | Sum.elim (vfValues q) (fun _ : Fin 1 => x.val) ∈ R} ∈ 𝓝 (q 0) := by
    have hq0 : q=(fun _ : Fin 1 => (0 : VF M)) := hq
    subst q
    convert hNear using 1
    ext x
    exact ⟨fun hx => by obtain ⟨y,hy,he⟩ := hx; exact (Subtype.ext he : y=x) ▸ hy,
      fun hx => ⟨x,hx,rfl⟩⟩
  obtain ⟨r,hr0,hrDef,hrPos,hrFit⟩ := exists_named_radius_for_finite_neighborhoods h00 hc hv V hV hVS hSV hnt
    C hC (Set.finite_singleton _) R hR 0 hNearC
  obtain ⟨c,hc0,hcDef,hrc⟩ := exists_named_vf_above_radius Valued.v hv hc h00 V S hV hVS hSV hnt
    (finiteValue r hr0) hrPos.le (finiteValue_named r hr0 hrDef)
  have hcDisc : c ∈ centeredGammaDisc (0 : VF M) (finiteValue r hr0) :=
    (mem_centeredGammaDisc _ _ _).mpr (by simpa only [sub_zero] using hrc)
  have hcQ : c ∈ Q := by
    obtain ⟨x,hx,he⟩ := hrFit (fun _ => 0) rfl c hcDisc
    exact (Subtype.ext he : x=c) ▸ hx
  refine ⟨c,hc0,hcDef,hrPos.trans hrc,?_⟩
  exact hcQ.resolve_right hc0

end DiamondIntegral.Section6
