import «section 6».UniformCovariance

/-! Actual graph fibers of a definable mixed-sort map, with every old
source and target RV name retained. The full graph specializes over this
exact base; no definability of an arbitrary extension is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8
open SpecialTransformations.Section9 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m r s : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) n r) S}
variable {B : DefSet (rawMixedSpace (M := M) m s) S}

def graphFibre (f : Map A B) (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M)
    (a : Fin n → VF M) (b : Fin m → VF M) : Prop := f.graph (a,u) (b,v)

def graphFibreSource (f : Map A B) (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) :
    Set (Fin n → VF M) := {a | ∃ b, graphFibre f u v a b}

def graphFibreRange (f : Map A B) (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) :
    Set (Fin m → VF M) := {b | ∃ a, graphFibre f u v a b}

def graphFibreBase (S : Set M) (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) :
    Set M := (S ∪ Set.range (rvValues u)) ∪ Set.range (rvValues v)

theorem graphFibre_functional (f : Map A B) (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M)
    {a : Fin n → VF M} {b c : Fin m → VF M}
    (hb : graphFibre f u v a b) (hc : graphFibre f u v a c) : b = c := by
  obtain ⟨p,hp,hfp⟩ := hb
  obtain ⟨q,hq,hfq⟩ := hc
  have he : p = q := Subtype.ext (hp.trans hq.symm)
  exact congrArg Prod.fst (hfp.symm.trans (he ▸ hfq))

def graphFibreMap (f : Map A B) (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M)
    (a : Fin n → VF M) : Fin m → VF M := by
  classical
  exact if ha : a ∈ graphFibreSource f u v then Classical.choose ha else 0

theorem graphFibreMap_graph (f : Map A B) (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M)
    {a : Fin n → VF M} (ha : a ∈ graphFibreSource f u v) :
    graphFibre f u v a (graphFibreMap f u v a) := by
  simpa only [graphFibreMap,dite_eq_left ha] using Classical.choose_spec ha

theorem graphFibreRange_eq_image (f : Map A B) (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) :
    graphFibreRange f u v = graphFibreMap f u v '' graphFibreSource f u v := by
  ext b
  constructor
  · rintro ⟨a,hab⟩
    have ha : a ∈ graphFibreSource f u v := ⟨b,hab⟩
    exact ⟨a,ha,graphFibre_functional f u v (graphFibreMap_graph f u v ha) hab⟩
  · rintro ⟨a,ha,rfl⟩
    exact ⟨a,graphFibreMap_graph f u v ha⟩

def rawMixedMapGraph (f : Map A B) :
    Set ((Fin n ⊕ Fin r) ⊕ (Fin m ⊕ Fin s) → M) :=
  (rawMixedSpace n r).relation (rawMixedSpace m s) f.graph

theorem rawMixedMapGraph_at (f : Map A B) (x : Mixed M n r) (y : Mixed M m s) :
    Sum.elim (mixedValues x) (mixedValues y) ∈ rawMixedMapGraph f ↔ f.graph x y := by
  let xc : (rawMixedSpace (M := M) n r).domain := ⟨mixedValues x,mixedValues_mem_domain x⟩
  let yc : (rawMixedSpace (M := M) m s).domain := ⟨mixedValues y,mixedValues_mem_domain y⟩
  have hx : (rawMixedSpace n r).decode xc = x := decode_mixedValues x
  have hy : (rawMixedSpace m s).decode yc = y := decode_mixedValues y
  have h := (rawMixedSpace n r).relation_decode (rawMixedSpace m s) f.graph xc yc
  rw [hx,hy] at h
  exact h

theorem rawMixedMapGraph_iff (f : Map A B)
    (z : (Fin n ⊕ Fin r) ⊕ (Fin m ⊕ Fin s) → M) :
    z ∈ rawMixedMapGraph f ↔ ∃ p : A,
      Sum.elim (mixedValues p.val) (mixedValues (f p).val) = z := by
  constructor
  · rintro ⟨hx,hy,p,hp,hfp⟩
    have he₁ : mixedValues p.val = z ∘ Sum.inl := by rw [hp]; exact mixedValues_decode _
    have he₂ : mixedValues (f p).val = z ∘ Sum.inr := by rw [hfp]; exact mixedValues_decode _
    exact ⟨p,by funext i; cases i with
      | inl i => exact congrFun he₁ i
      | inr i => exact congrFun he₂ i⟩
  · rintro ⟨p,rfl⟩
    exact (rawMixedMapGraph_at f p.val (f p).val).mpr ⟨p,rfl,rfl⟩

theorem graphFibreMap_definable (f : Map A B)
    (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) :
    (graphFibreBase S u v).Definable LRV
      (vfCorrespondenceGraph (graphFibreSource f u v) (fun x => {graphFibreMap f u v x})) := by
  let T := graphFibreBase S u v
  let φ (z : Fin n ⊕ Fin m → M) : (Fin n ⊕ Fin r) ⊕ (Fin m ⊕ Fin s) → M :=
    Sum.elim (Sum.elim (z ∘ Sum.inl) (rvValues u)) (Sum.elim (z ∘ Sum.inr) (rvValues v))
  have hφ : T.DefinableMap LRV φ := by
    rintro ((i | i) | (i | i))
    · exact Set.DefinableFun.proj LRV
    · exact LRV.definableFun_const _ (Or.inl (Or.inr (Set.mem_range_self i)))
    · exact Set.DefinableFun.proj LRV
    · exact LRV.definableFun_const _ (Or.inr (Set.mem_range_self i))
  have hraw : S.Definable LRV (rawMixedMapGraph f) := f.graph_definable
  convert (hraw.mono (fun _ h => Or.inl (Or.inl h))).preimage_map hφ using 1
  ext z
  constructor
  · rintro ⟨a,ha,b,hb,rfl⟩
    have hG : graphFibre f u v a b := by
      rw [Set.mem_singleton_iff] at hb
      rw [hb]
      exact graphFibreMap_graph f u v ha
    apply (rawMixedMapGraph_at f (a,u) (b,v)).mpr hG
  · intro hz
    obtain ⟨p,he⟩ := (rawMixedMapGraph_iff f (φ z)).mp hz
    have hu : p.val.2 = u := funext (fun i => Subtype.ext (congrFun he (.inl (.inr i))))
    have hv : (f p).val.2 = v := funext (fun i => Subtype.ext (congrFun he (.inr (.inr i))))
    have hG : graphFibre f u v p.val.1 (f p).val.1 :=
      ⟨p,Prod.ext rfl hu,Prod.ext rfl hv⟩
    have ha : p.val.1 ∈ graphFibreSource f u v := ⟨(f p).val.1,hG⟩
    refine ⟨p.val.1,ha,(f p).val.1,?_,?_⟩
    · exact graphFibre_functional f u v hG (graphFibreMap_graph f u v ha)
    · funext i
      cases i with
      | inl i => exact congrFun he (.inl (.inl i))
      | inr i => exact congrFun he (.inr (.inl i))

theorem graphFibreSource_definable (f : Map A B)
    (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) :
    (graphFibreBase S u v).Definable LRV (vfValues '' graphFibreSource f u v) := by
  have h := (graphFibreMap_definable f u v).image_comp (Sum.inl : Fin n → Fin n ⊕ Fin m)
  convert h using 1
  ext z
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ⟨Sum.elim (vfValues a) (vfValues (graphFibreMap f u v a)),
      ⟨a,ha,graphFibreMap f u v a,Set.mem_singleton _,rfl⟩,rfl⟩
  · rintro ⟨w,⟨a,ha,b,_,he⟩,hw⟩
    exact ⟨a,ha,funext (fun i => (congrFun he (.inl i)).trans (congrFun hw i))⟩

theorem graphFibreRange_definable (f : Map A B)
    (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) :
    (graphFibreBase S u v).Definable LRV (vfValues '' graphFibreRange f u v) := by
  have h := (graphFibreMap_definable f u v).image_comp (Sum.inr : Fin m → Fin n ⊕ Fin m)
  convert h using 1
  ext z
  constructor
  · rintro ⟨b,⟨a,hab⟩,rfl⟩
    have ha : a ∈ graphFibreSource f u v := ⟨b,hab⟩
    exact ⟨Sum.elim (vfValues a) (vfValues b),
      ⟨a,ha,b,graphFibre_functional f u v hab (graphFibreMap_graph f u v ha),rfl⟩,rfl⟩
  · rintro ⟨w,⟨a,ha,b,hb,he⟩,hw⟩
    have hab : graphFibre f u v a b := by
      rw [Set.mem_singleton_iff] at hb
      rw [hb]
      exact graphFibreMap_graph f u v ha
    exact ⟨b,⟨a,hab⟩,funext (fun i => (congrFun he (.inr i)).trans (congrFun hw i))⟩

theorem graphFibreSource_subset (f : Map A B)
    (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) :
    graphFibreSource f u v ⊆ vfFibre A.carrier u := by
  rintro a ⟨b,p,hp,_⟩
  change (a,u) ∈ A.carrier
  exact hp ▸ p.property

theorem graphFibreRange_subset (f : Map A B)
    (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) :
    graphFibreRange f u v ⊆ vfFibre B.carrier v := by
  rintro b ⟨a,p,_,hfp⟩
  change (b,v) ∈ B.carrier
  exact hfp ▸ (f p).property

theorem graphFibreSource_cover (f : Map A B) (u : Fin r → RVInfinity M)
    {a : Fin n → VF M} (ha : a ∈ vfFibre A.carrier u) :
    ∃ v : Fin s → RVInfinity M, a ∈ graphFibreSource f u v := by
  let p : A := ⟨(a,u),ha⟩
  exact ⟨(f p).val.2,(f p).val.1,p,rfl,rfl⟩

theorem graphFibreSource_disjoint (f : Map A B) (u : Fin r → RVInfinity M)
    (v w : Fin s → RVInfinity M) (hvw : v ≠ w) :
    Disjoint (graphFibreSource f u v) (graphFibreSource f u w) := by
  apply Set.disjoint_left.mpr
  rintro a ⟨b,p,hp,hfp⟩ ⟨c,q,hq,hfq⟩
  have he : p = q := Subtype.ext (hp.trans hq.symm)
  exact hvw (congrArg Prod.snd (hfp.symm.trans (he ▸ hfq)))

theorem graphFibreRange_cover (f : Map A B) (hf : Function.Surjective f)
    (v : Fin s → RVInfinity M) {b : Fin m → VF M} (hb : b ∈ vfFibre B.carrier v) :
    ∃ u : Fin r → RVInfinity M, b ∈ graphFibreRange f u v := by
  obtain ⟨p,hp⟩ := hf ⟨(b,v),hb⟩
  refine ⟨p.val.2,p.val.1,p,rfl,?_⟩
  rw [hp]

theorem graphFibreRange_disjoint (f : Map A B) (hf : Function.Injective f)
    (v : Fin s → RVInfinity M) (u w : Fin r → RVInfinity M) (huw : u ≠ w) :
    Disjoint (graphFibreRange f u v) (graphFibreRange f w v) := by
  apply Set.disjoint_left.mpr
  rintro b ⟨a,p,hp,hfp⟩ ⟨c,q,hq,hfq⟩
  have he : p = q := hf (Subtype.ext (hfp.trans hfq.symm))
  exact huw (congrArg Prod.snd (hp.symm.trans (he ▸ hq)))

end DiamondIntegral.Section6
