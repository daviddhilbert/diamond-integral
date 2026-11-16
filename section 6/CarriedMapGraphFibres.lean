import «section 6».CarriedDefinableMaps

/-! Exact full graph fibres of a carried map. Their source and range
are the old graph fibres crossed with the same retained-label RV disc;
these identities include all original source and target labels. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
variable (f : Map A B) (k : Fin r) (l : Fin s) (hLabels : ∀ p : A,(f p).val.2 l=p.val.2 k)

include hLabels in
theorem graphFibre_retained_disc_label (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M)
    (a b : Fin n → VF M) (h : graphFibre f u v a b) : u k=v l := by
  obtain ⟨p,hp,hfp⟩ := h
  exact (congrArg (fun z : Mixed M n r => z.2 k) hp).symm.trans
    ((hLabels p).symm.trans (congrArg (fun z : Mixed M n s => z.2 l) hfp))

theorem graphFibre_carryLastMap_iff (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M)
    (a b : Fin (n+1) → VF M) :
    graphFibre (carryLastMap f k l hLabels) u v a b ↔
      graphFibre f u v (Fin.init a) (Fin.init b) ∧ a (Fin.last n)=b (Fin.last n) ∧ rv M (a (Fin.last n))=u k := by
  constructor
  · rintro ⟨p,hp,hfp⟩
    have hBase : (bundleProjection A k p).val=(Fin.init a,u) :=
      congrArg (fun z : Mixed M (n+1) r => (Fin.init z.1,z.2)) hp
    have hOut : (f (bundleProjection A k p)).val=(Fin.init b,v) := by
      have h := congrArg (fun z : Mixed M (n+1) s => (Fin.init z.1,z.2)) hfp
      rw [carryLastMap_value,Fin.init_snoc] at h
      exact h
    have hLast : a (Fin.last n)=b (Fin.last n) := by
      have h := congrArg (fun z : Mixed M (n+1) s => z.1 (Fin.last n)) hfp
      change (carryLastMap f k l hLabels p).val.1 (Fin.last n)=b (Fin.last n) at h
      rw [carryLastMap_fixed] at h
      exact (congrArg (fun z : Mixed M (n+1) r => z.1 (Fin.last n)) hp).symm.trans h
    have hRV := p.property.2
    rw [hp] at hRV
    exact ⟨⟨bundleProjection A k p,hBase,hOut⟩,hLast,hRV⟩
  · rintro ⟨⟨p,hp,hfp⟩,hLast,hRV⟩
    have hx : (a,u) ∈ (rvCoordinateBundle A k).carrier := ⟨hp ▸ p.property,hRV⟩
    let x : rvCoordinateBundle A k := ⟨(a,u),hx⟩
    have hBase : bundleProjection A k x=p := Subtype.ext hp.symm
    refine ⟨x,rfl,?_⟩
    rw [carryLastMap_value,hBase,hfp]
    change (Fin.snoc (Fin.init b) (a (Fin.last n)),v)=(b,v)
    rw [hLast,Fin.snoc_init_self]

theorem graphFibreSource_carryLastMap (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) :
    graphFibreSource (carryLastMap f k l hLabels) u v=
      {a : Fin (n+1) → VF M | Fin.init a ∈ graphFibreSource f u v ∧ rv M (a (Fin.last n))=u k} := by
  ext a
  constructor
  · rintro ⟨b,hb⟩
    obtain ⟨h,_,hRV⟩ := (graphFibre_carryLastMap_iff f k l hLabels u v a b).mp hb
    exact ⟨⟨Fin.init b,h⟩,hRV⟩
  · rintro ⟨⟨b,hb⟩,hRV⟩
    refine ⟨Fin.snoc b (a (Fin.last n)),(graphFibre_carryLastMap_iff f k l hLabels u v _ _).mpr ?_⟩
    simpa only [Fin.init_snoc,Fin.snoc_last] using (show graphFibre f u v (Fin.init a) b ∧
      a (Fin.last n)=a (Fin.last n) ∧ rv M (a (Fin.last n))=u k from ⟨hb,rfl,hRV⟩)

theorem graphFibreRange_carryLastMap (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) :
    graphFibreRange (carryLastMap f k l hLabels) u v=
      {b : Fin (n+1) → VF M | Fin.init b ∈ graphFibreRange f u v ∧ rv M (b (Fin.last n))=v l} := by
  ext b
  constructor
  · rintro ⟨a,ha⟩
    obtain ⟨h,hLast,hRV⟩ := (graphFibre_carryLastMap_iff f k l hLabels u v a b).mp ha
    exact ⟨⟨Fin.init a,h⟩,(congrArg (rv M) hLast).symm.trans
      (hRV.trans (graphFibre_retained_disc_label f k l hLabels u v _ _ h))⟩
  · rintro ⟨⟨a,ha⟩,hRV⟩
    have hOld : rv M (b (Fin.last n))=u k := hRV.trans (graphFibre_retained_disc_label f k l hLabels u v _ _ ha).symm
    refine ⟨Fin.snoc a (b (Fin.last n)),(graphFibre_carryLastMap_iff f k l hLabels u v _ _).mpr ?_⟩
    simpa only [Fin.init_snoc,Fin.snoc_last] using (show graphFibre f u v a (Fin.init b) ∧
      b (Fin.last n)=b (Fin.last n) ∧ rv M (b (Fin.last n))=u k from ⟨ha,rfl,hOld⟩)

theorem graphFibreSource_carryLastMap_inter (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) :
    graphFibreSource (carryLastMap f k l hLabels) u v=
      {a : Fin (n+1) → VF M | Fin.init a ∈ graphFibreSource f u v} ∩ vfFibre (rvCoordinateBundle A k).carrier u := by
  rw [graphFibreSource_carryLastMap]
  ext a
  constructor
  · rintro ⟨ha,hRV⟩
    exact ⟨ha,graphFibreSource_subset f u v ha,hRV⟩
  · rintro ⟨ha,hA,hRV⟩
    exact ⟨ha,hRV⟩

theorem graphFibreRange_carryLastMap_inter (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) :
    graphFibreRange (carryLastMap f k l hLabels) u v=
      {b : Fin (n+1) → VF M | Fin.init b ∈ graphFibreRange f u v} ∩ vfFibre (rvCoordinateBundle B l).carrier v := by
  rw [graphFibreRange_carryLastMap]
  ext b
  constructor
  · rintro ⟨hb,hRV⟩
    exact ⟨hb,graphFibreRange_subset f u v hb,hRV⟩
  · rintro ⟨hb,hB,hRV⟩
    exact ⟨hb,hRV⟩

end DiamondIntegral.Section6
