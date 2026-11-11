import «section 2».NamedDiscCompactness
import «section 2».DiscTupleIntersection

/-! Complete-type compactness over the original fixed DC context.
All finite covers and neighbourhoods retain that context. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def namedDiscTypeLocus (B : ParameterBase M) {k n : ℕ} (closed : Fin k → Bool)
    (a : Fin k → VF M) (δ : Fin k → Gamma M) (u : Fin n → M) : Set (Fin n → M) :=
  {x | x ∈ GammaParameters.sortedUniverse (fun _ => .vf) ∧
    ∀ C, DefinableOverFiniteDiscNames B closed a δ (fun _ => .vf) C → u ∈ C → x ∈ C}

theorem namedDiscTypeLocus_generates (B : ParameterBase M) {k n : ℕ}
    (closed : Fin k → Bool) (a : Fin k → VF M) (δ : Fin k → Gamma M)
    (u : Fin n → M) (hu : u ∈ GammaParameters.sortedUniverse (fun _ => .vf)) :
    GeneratesTypeOverFiniteDiscNames B closed a δ (fun _ => .vf)
      (namedDiscTypeLocus B closed a δ u) := by
  refine ⟨⟨u,hu,fun _ _ h => h⟩,fun _ h => h.1,?_⟩
  intro C hC
  by_cases h : u ∈ C
  · exact Or.inl (fun _ hx => hx.2 C hC h)
  · right
    exact Set.disjoint_left.mpr (fun x hx hxC => (hx.2 _ hC.compl ⟨hu,h⟩).2 hxC)

def badDiscFibreCodes {n m : ℕ} (D : Set (Fin m → M))
    (R : (Fin m → M) → Set (Fin n → M)) (C : Set (Fin n → M)) : Set (Fin m → M) :=
  {d | d ∈ D ∧ ∃ x ∈ R d, x ∉ C}

theorem badDiscFibreCodes_definable {B : ParameterBase M} {k n m : ℕ}
    {closed : Fin k → Bool} {a : Fin k → VF M} {δ : Fin k → Gamma M}
    (D : Set (Fin m → M)) (R : (Fin m → M) → Set (Fin n → M))
    (hR : DefinableOverFiniteDiscNames B closed a δ (fun _ : Fin (m+n) => .vf)
      {z | z ∘ Fin.castAdd n ∈ D ∧ z ∘ Fin.natAdd m ∈ R (z ∘ Fin.castAdd n)})
    (C : Set (Fin n → M)) (hC : DefinableOverFiniteDiscNames B closed a δ (fun _ => .vf) C) :
    DefinableOverFiniteDiscNames B closed a δ (fun _ => .vf) (badDiscFibreCodes D R C) := by
  have hcut := hR.inter (hC.compl.preimage_real (fun _ : Fin (m+n) => .vf) (Fin.natAdd m))
  have hp := hcut.image_real (Fin.castAdd n)
  change DefinableOverFiniteDiscNames B closed a δ (fun _ => .vf) (badDiscFibreCodes D R C)
  convert hp using 1
  all_goals try rfl
  ext d
  constructor
  · rintro ⟨hd,x,hx,hno⟩
    let z := Fin.append d x
    have hzR : z ∈ {z | z ∘ Fin.castAdd n ∈ D ∧ z ∘ Fin.natAdd m ∈ R (z ∘ Fin.castAdd n)} := by
      simpa only [Set.mem_ofPred_eq,z,Function.comp_def,Fin.append_left,Fin.append_right] using And.intro hd hx
    refine ⟨z,⟨hzR,⟨?_,?_⟩,hR.proper hzR⟩,?_⟩
    · intro j
      simpa only [Function.comp_apply] using hR.proper hzR (Fin.natAdd m j)
    · simpa only [z,Function.comp_def,Fin.append_right] using hno
    · funext j
      exact Fin.append_left d x j
  · rintro ⟨z,⟨⟨hzD,hzR⟩,⟨_,hno⟩,_⟩,he⟩
    refine ⟨he ▸ hzD,z ∘ Fin.natAdd m,?_,hno⟩
    change z ∘ Fin.castAdd n = d at he
    rwa [he] at hzR

theorem named_type_local_good_neighbourhood
    {κ : Cardinal} (hs : Saturated M κ) (hκ : Cardinal.aleph0 ≤ κ)
    (S : Set M) (hsmall : Cardinal.mk S < κ)
    {k n m : ℕ} (closed : Fin k → Bool) (a : Fin k → VF M) (δ : Fin k → Gamma M)
    (A : Set (Fin n → M))
    (hA : DefinableOverFiniteDiscNames ⟨S,∅⟩ closed a δ (fun _ => .vf) A)
    (u : Fin n → M) (hu : u ∈ A)
    (D P : Set (Fin m → M))
    (hD : DefinableOverFiniteDiscNames ⟨S,∅⟩ closed a δ (fun _ => .vf) D)
    (hP : DefinableOverFiniteDiscNames ⟨S,∅⟩ closed a δ (fun _ => .vf) P)
    (R : (Fin m → M) → Set (Fin n → M))
    (hR : DefinableOverFiniteDiscNames ⟨S,∅⟩ closed a δ (fun _ : Fin (m+n) => .vf)
      {z | z ∘ Fin.castAdd n ∈ D ∧ z ∘ Fin.natAdd m ∈ R (z ∘ Fin.castAdd n)})
    (htype : ∀ d ∈ D, R d ⊆ namedDiscTypeLocus ⟨S,∅⟩ closed a δ u → d ∈ P) :
    ∃ C ⊆ A, DefinableOverFiniteDiscNames ⟨S,∅⟩ closed a δ (fun _ => .vf) C ∧
      u ∈ C ∧ ∀ d ∈ D, R d ⊆ C → d ∈ P := by
  classical
  let Q := {C : Set (Fin n → M) // DefinableOverFiniteDiscNames ⟨S,∅⟩ closed a δ (fun _ => .vf) C ∧ u ∈ C}
  let cover (C : Q) := badDiscFibreCodes D R C.val
  let K := Set.range cover
  have hK : ∀ C ∈ K, DefinableOverFiniteDiscNames ⟨S,∅⟩ closed a δ (fun _ => .vf) C := by
    rintro _ ⟨C,rfl⟩
    exact badDiscFibreCodes_definable D R hR C.val C.property.1
  have hcover : ∀ d ∈ D \ P, ∃ C ∈ K, d ∈ C := by
    rintro d ⟨hd,hnP⟩
    by_contra hn
    apply hnP
    apply htype d hd
    intro x hx
    have hsrt : x ∈ GammaParameters.sortedUniverse (fun _ => .vf) := by
      have hz : Fin.append d x ∈ {z | z ∘ Fin.castAdd n ∈ D ∧ z ∘ Fin.natAdd m ∈ R (z ∘ Fin.castAdd n)} := by
        simpa only [Set.mem_ofPred_eq,Function.comp_def,Fin.append_left,Fin.append_right] using And.intro hd hx
      intro j
      simpa only [Fin.append_right] using hR.proper hz (Fin.natAdd m j)
    refine ⟨hsrt,?_⟩
    intro C hC huC
    by_contra hxC
    exact hn ⟨cover ⟨C,hC,huC⟩,Set.mem_range_self _,hd,x,hx,hxC⟩
  have hdiff : DefinableOverFiniteDiscNames ⟨S,∅⟩ closed a δ (fun _ => .vf) (D \ P) := by
    convert hD.inter hP.compl using 1
    ext d
    exact ⟨fun h => ⟨h.1,hD.proper h.1,h.2⟩,fun h => ⟨h.1,h.2.2⟩⟩
  obtain ⟨K₀,hKsub,hKf,hKcov⟩ := finite_subcover_disc_names hs hκ S hsmall closed a δ
    (D \ P) hdiff K hK hcover
  haveI : Finite K₀ := hKf.to_subtype
  let chooseC (W : K₀) : Q := Classical.choose (hKsub W.property)
  have hchoose (W : K₀) : cover (chooseC W) = W.val := Classical.choose_spec (hKsub W.property)
  let C := A ∩ {x | x ∈ GammaParameters.sortedUniverse (fun _ => .vf) ∧ ∀ W : K₀, x ∈ (chooseC W).val}
  have hC := hA.inter (DefinableOverFiniteDiscNames.sorted_finite_iInter
    (fun W : K₀ => (chooseC W).val) (fun W => (chooseC W).property.1))
  refine ⟨C,Set.inter_subset_left,hC,⟨hu,hA.proper hu,fun W => (chooseC W).property.2⟩,?_⟩
  intro d hd hsub
  by_contra hnP
  obtain ⟨W,hWK,hdW⟩ := hKcov d ⟨hd,hnP⟩
  let w : K₀ := ⟨W,hWK⟩
  have hbad : d ∈ cover (chooseC w) := by rw [hchoose]; exact hdW
  obtain ⟨_,x,hx,hno⟩ := hbad
  exact hno ((hsub hx).2.2 w)

end DiamondIntegral.Section2
