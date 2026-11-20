import «section 7».KernelBaseChange
import «section 6».MixedVFProjectionMaps
import «section 6».TupleCoordinateMaps
import «section 6».DefinableSurjectiveDescent
import «section 6».RVParameterTransport

/-! RV fibres of a mixed set over a VF point, as measured RV objects.

For a definable mixed set `A ⊆ VFᵐ × RVʳ` with a Γ-form `ω`, a VF tuple `a`
and head-start labels `π : Fin k → Fin r`, the fibre `A_a = {u | (a, u) ∈ A}`
with volume map `u ↦ u ∘ π` and form `u ↦ ω(a, u)` is a measured RV object of
degree `k` over `S ∪ a` (`fibreMeasured`), and over the substructure
`adjoin T a = S⟨a⟩` (`fibreObject`). This is the object `(A_a, ω)` of
`μRV^db[≤ k]` in Lemma 7.14, with the degree-`k` reading by selected labels of
Section 6's head starts (`headStartMeasuredObject`). It needs the volume map to
have finite fibres and nonzero values (`hFin`, `hNZ`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.FibreObjects
open DiamondIntegral.Section6 DiamondIntegral.Section2

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {m r k : ℕ}

/-- The VF slice `{p ∈ A | p.1 = a}`, over `S ∪ a`. -/
def slice (A : DefSet (rawMixedSpace (M := M) m r) S) (a : Fin m → VF M) :
    DefSet (rawMixedSpace (M := M) m r) (S ∪ Set.range (vfValues a)) :=
  (mixedVFHeadMap A).fibre ⟨a, Set.mem_univ _⟩ ⟨vfValues a, ⟨a, rfl⟩⟩ (decode_vfValues a)

omit [M ⊨ Axioms.ACVF] in
theorem mem_slice (A : DefSet (rawMixedSpace (M := M) m r) S) (a : Fin m → VF M) (p : Mixed M m r) :
    p ∈ (slice A a).carrier ↔ p ∈ A.carrier ∧ p.1 = a := by
  constructor
  · rintro ⟨q, rfl, hq⟩
    exact ⟨q.property, congrArg Subtype.val hq⟩
  · rintro ⟨hp, he⟩
    exact ⟨⟨p, hp⟩, rfl, Subtype.ext he⟩

theorem slice_subset (A : DefSet (rawMixedSpace (M := M) m r) S) (a : Fin m → VF M) :
    (slice A a).carrier ⊆
      (extendDefSetBase (Set.subset_union_left (t := Set.range (vfValues a))) A).carrier :=
  fun _ hp => ((mem_slice A a _).mp hp).1

/-- The fibre `A_a`, over `S ∪ a`. -/
def fibreDomain (A : DefSet (rawMixedSpace (M := M) m r) S) (a : Fin m → VF M) :
    DefSet (rawRVSpace (M := M) r) (S ∪ Set.range (vfValues a)) :=
  (rvTailMap (slice A a)).image

theorem mem_fibreDomain (A : DefSet (rawMixedSpace (M := M) m r) S) (a : Fin m → VF M)
    (u : Fin r → RVInfinity M) : u ∈ (fibreDomain A a).carrier ↔ (a, u) ∈ A.carrier := by
  constructor
  · rintro ⟨p, rfl⟩
    obtain ⟨hp, he⟩ := (mem_slice A a p.val).mp p.property
    have hpe : p.val = (a, p.val.2) := Prod.ext he rfl
    change (a, p.val.2) ∈ A.carrier
    rw [← hpe]
    exact hp
  · intro h
    exact ⟨⟨(a, u), (mem_slice A a _).mpr ⟨h, rfl⟩⟩, rfl⟩

/-- The volume map `u ↦ u ∘ π`. -/
def fibreVolume (A : DefSet (rawMixedSpace (M := M) m r) S) (a : Fin m → VF M) (π : Fin k → Fin r) :
    Map (fibreDomain A a) (DefSet.univ (rawRVSpace (M := M) k) (S ∪ Set.range (vfValues a))) :=
  (rvTupleSelectMap _ π).comp (Map.inclusion (fun _ _ => Set.mem_univ _))

/-- The fibre with its volume map, as an RV object of degree `k`. -/
def fibreRVObject (A : DefSet (rawMixedSpace (M := M) m r) S) (a : Fin m → VF M) (π : Fin k → Fin r) :
    RVObject (M := M) (S ∪ Set.range (vfValues a)) k where
  arity := r
  domain := fibreDomain A a
  volume := fibreVolume A a π

theorem fibreRVObject_value (A : DefSet (rawMixedSpace (M := M) m r) S) (a : Fin m → VF M) (π : Fin k → Fin r)
    (u : (fibreDomain A a)) : (fibreRVObject A a π).value u = u.val ∘ π := rfl

theorem tail_injective (A : DefSet (rawMixedSpace (M := M) m r) S) (a : Fin m → VF M)
    (p q : slice A a) (he : (rvTailMap (slice A a)).toImage p = (rvTailMap (slice A a)).toImage q) : p = q := by
  have h2 : p.val.2 = q.val.2 := congrArg Subtype.val he
  have h1 : p.val.1 = q.val.1 :=
    ((mem_slice A a p.val).mp p.property).2.trans ((mem_slice A a q.val).mp q.property).2.symm
  exact Subtype.ext (Prod.ext h1 h2)

omit [M ⊨ Axioms.ACVF] in
theorem tail_surjective (A : DefSet (rawMixedSpace (M := M) m r) S) (a : Fin m → VF M) :
    Function.Surjective ((rvTailMap (slice A a)).toImage) := by
  rintro ⟨_, p, rfl⟩
  exact ⟨p, rfl⟩

/-- The form `u ↦ ω(a, u)` on the fibre. -/
def fibreForm (A : DefSet (rawMixedSpace (M := M) m r) S)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) (a : Fin m → VF M) :
    Map (fibreDomain A a) (DefSet.univ (rawGammaPresentation (M := M)) (S ∪ Set.range (vfValues a))) :=
  definableSurjectiveDescent (rvTailMap (slice A a)).toImage (tail_surjective A a)
    ((extendMapBase Set.subset_union_left ω).comp (Map.inclusion (slice_subset A a)))
    (fun p q he => by rw [tail_injective A a p q he])

theorem fibreForm_apply (A : DefSet (rawMixedSpace (M := M) m r) S)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) (a : Fin m → VF M)
    (u : Fin r → RVInfinity M) (hu : (a, u) ∈ A.carrier) :
    (fibreForm A ω a ⟨u, (mem_fibreDomain A a u).mpr hu⟩).val = (ω ⟨(a, u), hu⟩).val := by
  have h := definableSurjectiveDescent_apply (rvTailMap (slice A a)).toImage (tail_surjective A a)
    ((extendMapBase Set.subset_union_left ω).comp (Map.inclusion (slice_subset A a)))
    (fun p q he => by rw [tail_injective A a p q he]) ⟨(a, u), (mem_slice A a _).mpr ⟨hu, rfl⟩⟩
  exact congrArg Subtype.val h

/-- The fibre `(A_a, ω(a, ·))` as a measured RV object of degree `k` over
`S ∪ a`. -/
def fibreMeasured (A : DefSet (rawMixedSpace (M := M) m r) S)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) (a : Fin m → VF M) (π : Fin k → Fin r)
    (hFin : ∀ t : Fin k → RVInfinity M, {u : Fin r → RVInfinity M | (a, u) ∈ A.carrier ∧ u ∘ π = t}.Finite)
    (hNZ : ∀ p ∈ A.carrier, ∀ i, (p.2 (π i)).val ≠ iRVZero) :
    MeasuredRVObject (M := M) (S ∪ Set.range (vfValues a)) k where
  object := fibreRVObject A a π
  finiteVolume := by
    intro t
    have hf := (hFin t.val).preimage (f := fun u : fibreDomain A a => u.val)
      (fun x _ y _ he => Subtype.ext he)
    refine hf.subset ?_
    intro u hu
    exact ⟨(mem_fibreDomain A a u.val).mp u.property, congrArg Subtype.val hu⟩
  nonzero := fun u i => hNZ (a, u.val) ((mem_fibreDomain A a u.val).mp u.property) i
  form := fibreForm A ω a

/-- The fibre object over the substructure `adjoin T a = S⟨a⟩`. -/
def fibreObject (T : LRV.Substructure M) (A : DefSet (rawMixedSpace (M := M) m r) (T : Set M))
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M))) (a : Fin m → VF M) (π : Fin k → Fin r)
    (hFin : ∀ t : Fin k → RVInfinity M, {u : Fin r → RVInfinity M | (a, u) ∈ A.carrier ∧ u ∘ π = t}.Finite)
    (hNZ : ∀ p ∈ A.carrier, ∀ i, (p.2 (π i)).val ≠ iRVZero) :
    MeasuredRVObject (M := M) (KernelBaseChange.adjoin T a : Set M) k :=
  (fibreMeasured A ω a π hFin hNZ).extend
    (Set.union_subset (KernelBaseChange.subset_adjoin a)
      (by rintro _ ⟨i, rfl⟩; exact KernelBaseChange.coordinate_mem_adjoin a i))

end DiamondIntegral.Section7.FibreObjects
