import «section 6».UnaryApertureInclusion
import «section 6».UnaryRelativeRVFamilyMeasuredMatching
import «section 6».PureRVDiscQuotients
import «section 6».MeasuredRVIsomorphisms

/-! Complete Section 6 matching in the precise bounded variable class.
The original proper objects, actual forms and original VF-generated base
are retained. The result includes both genuine finite variable chains,
the literal conjugate, full RV bijection and every-label volume identity.
It does not assert the original scalar-aperture statement or a Section 7
kernel theorem. No downstream definition is changed here.

The final clauses of Lemma 6.38 are also proved here. For a tagged mixed set
`A` (VF leading terms constant on RV-label fibres) the label domain `rv(A)`
carries the VF leading-term volume map. When `A` is an RV-pullback with finite
RV fibres this map is finite-to-one, so `rv(A)` is an object of `RV[n]`
(Definition `defn:c:RV:cat`, Notation `0coor`). In the unary prepared case the
leading term is the label coordinate fixed by the matching, so the volume map
is the degree-one coordinate projection `(rv(A♭))_1`. The transported forms
`ω' = ω ∘ T_A⁻¹`, `σ' = σ ∘ T_B⁻¹` are `rv`-contractible (fields of
`UnaryRelativeMeasuredMatching`) and descend to `rv(A♭)`, `rv(B♭)`; the
contracted objects are doubly bounded, and the induced map `f♭_↓` on label
domains is a measured RV isomorphism, i.e. a morphism of `μRV^db[1]`, whose
balance is the every-label volume identity of the matching. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {r s : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

section RVContraction
open CategoryTheory
variable {S : Set M} {n m : ℕ}

/-- The leading-term volume map of an RV-pullback with finite RV fibres is
finite-to-one: its fibre over `t` lies in the RV fibre over any `a` with
`rv(a) = t`. -/
theorem preparedRVVolume_finiteFibres (A : DefSet (rawMixedSpace (M := M) n r) S)
    (hTag : ∀ p ∈ A.carrier,∀ q ∈ A.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1)
    (hRV : IsRVPullback A.carrier)
    (hFinite : ∀ a : Fin n → VF M,{u : Fin r → RVInfinity M | (a,u) ∈ A.carrier}.Finite) :
    (preparedRVVolume A hTag).FiniteFibres := by
  intro b
  by_cases hb : ∃ p : A,tupleRV M p.val.1=b.val
  · obtain ⟨p₀,hp₀⟩ := hb
    apply ((hFinite p₀.val.1).preimage Subtype.val_injective.injOn).subset
    intro u hu
    obtain ⟨p,rfl⟩ := pureRVTagQuotient_surjective A u
    have hv : tupleRV M p.val.1=b.val :=
      (preparedRVVolume_at A hTag p).symm.trans (congrArg Subtype.val hu)
    have hmem : (p₀.val.1,p.val.2) ∈ rvHull A.carrier :=
      ⟨p.val,p.property,Prod.ext (hv.trans hp₀.symm) rfl⟩
    rw [hRV] at hmem
    exact hmem
  · apply Set.finite_empty.subset
    intro u hu
    obtain ⟨p,rfl⟩ := pureRVTagQuotient_surjective A u
    exact hb ⟨p,(preparedRVVolume_at A hTag p).symm.trans (congrArg Subtype.val hu)⟩

theorem preparedRVObject_value (A : DefSet (rawMixedSpace (M := M) n r) S)
    (hTag : ∀ p ∈ A.carrier,∀ q ∈ A.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1) (p : A) :
    (preparedRVObject A hTag).value (pureRVTagQuotient A p)=tupleRV M p.val.1 :=
  preparedRVVolume_at A hTag p

/-- On a VF-doubly-bounded set the leading-term volume never takes the value
`rv(0)`. -/
theorem preparedRVObject_nonzero_bv (A : DefSet (rawMixedSpace (M := M) n r) S)
    (hTag : ∀ p ∈ A.carrier,∀ q ∈ A.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1)
    (hD : VFDoublyBounded A.carrier) :
    ∀ u : (preparedRVObject A hTag).domain,∀ i,((preparedRVObject A hTag).value u i).val ≠ iRVZero := by
  intro u i
  obtain ⟨p,rfl⟩ := pureRVTagQuotient_surjective A u
  rw [preparedRVObject_value A hTag p]
  intro he
  exact hD.nonzero p.property i ((rv_eq_zero_iff _).mp (Subtype.ext he))

/-- The descent of a Gamma form constant on RV-label fibres to the label domain. -/
def contractedForm (A : DefSet (rawMixedSpace (M := M) n r) S)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hω : ∀ p q : A,p.val.2=q.val.2 → ω p=ω q) :
    Map (pureRVTagDomain A) (DefSet.univ (rawGammaPresentation (M := M)) S) :=
  definableSurjectiveDescent (pureRVTagQuotient A) (pureRVTagQuotient_surjective A) ω
    (fun p q he => hω p q ((pureRVTagQuotient_eq_iff A p q).mp he))

theorem contractedForm_at (A : DefSet (rawMixedSpace (M := M) n r) S)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hω : ∀ p q : A,p.val.2=q.val.2 → ω p=ω q) (p : A) :
    contractedForm A ω hω (pureRVTagQuotient A p)=ω p :=
  definableSurjectiveDescent_apply _ _ _ _ p

/-- The measured RV contraction `(rv(A), ω_↓)` of a tagged RV-pullback with
finite RV fibres and a form constant on RV-label fibres. -/
def contractedMeasuredRVObject (A : DefSet (rawMixedSpace (M := M) n r) S)
    (hTag : ∀ p ∈ A.carrier,∀ q ∈ A.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1)
    (hRV : IsRVPullback A.carrier)
    (hFinite : ∀ a : Fin n → VF M,{u : Fin r → RVInfinity M | (a,u) ∈ A.carrier}.Finite)
    (hD : VFDoublyBounded A.carrier)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hω : ∀ p q : A,p.val.2=q.val.2 → ω p=ω q) : MeasuredRVObject (M := M) S n where
  object := preparedRVObject A hTag
  finiteVolume := preparedRVVolume_finiteFibres A hTag hRV hFinite
  nonzero := preparedRVObject_nonzero_bv A hTag hD
  form := contractedForm A ω hω

theorem contractedMeasuredRVObject_doublyBounded (A : DefSet (rawMixedSpace (M := M) n r) S)
    (hTag : ∀ p ∈ A.carrier,∀ q ∈ A.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1)
    (hRV : IsRVPullback A.carrier)
    (hFinite : ∀ a : Fin n → VF M,{u : Fin r → RVInfinity M | (a,u) ∈ A.carrier}.Finite)
    (hD : VFDoublyBounded A.carrier) (hB : RVSupportDoublyBounded A.carrier)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hω : ∀ p q : A,p.val.2=q.val.2 → ω p=ω q) :
    (contractedMeasuredRVObject A hTag hRV hFinite hD ω hω).doublyBounded := by
  constructor
  · obtain ⟨γ,hγ⟩ := hB
    refine ⟨γ,?_⟩
    rintro _ ⟨p,rfl⟩ i
    exact hγ p.val p.property i
  · obtain ⟨γ,hγ⟩ := hD
    refine ⟨γ,?_⟩
    rintro _ ⟨u,rfl⟩ i
    obtain ⟨p,rfl⟩ := pureRVTagQuotient_surjective A u
    change (γ⁻¹).val ≤ Values.vrv ((preparedRVObject A hTag).value (pureRVTagQuotient A p) i) ∧
      Values.vrv ((preparedRVObject A hTag).value (pureRVTagQuotient A p) i) ≤ γ.val
    rw [preparedRVObject_value A hTag p]
    exact hγ p.val p.property i

/-- In the unary case with the leading term recorded in label `j`, the volume
map is the coordinate projection `pr_j`, so the object is `(rv(A), ω_↓)_1`. -/
theorem contractedMeasuredRVObject_value_unary (A : DefSet (rawMixedSpace (M := M) 1 r) S)
    (hTag : ∀ p ∈ A.carrier,∀ q ∈ A.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1)
    (hRV : IsRVPullback A.carrier)
    (hFinite : ∀ a : Fin 1 → VF M,{u : Fin r → RVInfinity M | (a,u) ∈ A.carrier}.Finite)
    (hD : VFDoublyBounded A.carrier)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hω : ∀ p q : A,p.val.2=q.val.2 → ω p=ω q) (j : Fin r)
    (hLead : ∀ p ∈ A.carrier,rv M (p.1 0)=p.2 j)
    (u : (contractedMeasuredRVObject A hTag hRV hFinite hD ω hω).object.domain) :
    (contractedMeasuredRVObject A hTag hRV hFinite hD ω hω).object.value u=fun _ => u.val j := by
  obtain ⟨p,rfl⟩ := pureRVTagQuotient_surjective A u
  change (preparedRVObject A hTag).value (pureRVTagQuotient A p)=_
  rw [preparedRVObject_value A hTag p]
  funext i
  fin_cases i
  exact hLead p.val p.property

theorem contractedMeasuredRVObject_form (A : DefSet (rawMixedSpace (M := M) n r) S)
    (hTag : ∀ p ∈ A.carrier,∀ q ∈ A.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1)
    (hRV : IsRVPullback A.carrier)
    (hFinite : ∀ a : Fin n → VF M,{u : Fin r → RVInfinity M | (a,u) ∈ A.carrier}.Finite)
    (hD : VFDoublyBounded A.carrier)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hω : ∀ p q : A,p.val.2=q.val.2 → ω p=ω q) (p : A) :
    gammaMapValue (contractedMeasuredRVObject A hTag hRV hFinite hD ω hω).form (pureRVTagQuotient A p)=
      gammaMapValue ω p :=
  congrArg Subtype.val (contractedForm_at A ω hω p)

theorem contractedMeasuredRVObject_volumeGamma_unary (A : DefSet (rawMixedSpace (M := M) 1 r) S)
    (hTag : ∀ p ∈ A.carrier,∀ q ∈ A.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1)
    (hRV : IsRVPullback A.carrier)
    (hFinite : ∀ a : Fin 1 → VF M,{u : Fin r → RVInfinity M | (a,u) ∈ A.carrier}.Finite)
    (hD : VFDoublyBounded A.carrier)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hω : ∀ p q : A,p.val.2=q.val.2 → ω p=ω q) (j : Fin r)
    (hLead : ∀ p ∈ A.carrier,rv M (p.1 0)=p.2 j) (p : A) :
    (contractedMeasuredRVObject A hTag hRV hFinite hD ω hω).volumeGamma (pureRVTagQuotient A p)=
      GammaParameters.codeValue (p.val.2 j).val := by
  have hne : p.val.2 j ≠ rvZero M := by
    rw [← hLead p.val p.property]
    intro he
    exact hD.nonzero p.property 0 ((rv_eq_zero_iff _).mp he)
  apply Subtype.ext
  rw [nonzero_rv_codeValue_val _ hne]
  simp only [MeasuredRVObject.volumeGamma,rvVolumeGamma,Fin.prod_univ_one]
  change Values.vrv ((preparedRVObject A hTag).value (pureRVTagQuotient A p) 0)=_
  rw [preparedRVObject_value A hTag p]
  exact congrArg Values.vrv (hLead p.val p.property)

/-- A bijection of label domains between finite-to-one, nowhere-zero RV
objects is an isomorphism of `RV[n]`: both weight conditions are equalities
and the volume-fibre images are images of finite volume fibres. -/
def rvIsoOfFiniteFibres {k : ℕ} {U V : RVObject (M := M) S k}
    (F : Map U.domain V.domain) (hF : Function.Bijective F)
    (hUF : U.volume.FiniteFibres) (hVF : V.volume.FiniteFibres)
    (hU : ∀ u i,(U.value u i).val ≠ iRVZero)
    (hV : ∀ v i,(V.value v i).val ≠ iRVZero) : U ≅ V where
  hom := {
    map := F
    volumetric u := by simp [rvWeight,hU u,hV (F u)]
    finite_volume_images t := by
      apply ((hUF ⟨t,Set.mem_univ _⟩).image (fun u => V.value (F u))).subset
      rintro _ ⟨u,hu,rfl⟩
      exact ⟨u,Subtype.ext hu,rfl⟩ }
  inv := {
    map := F.inverse hF
    volumetric v := by simp [rvWeight,hV v,hU (F.inverse hF v)]
    finite_volume_images t := by
      apply ((hVF ⟨t,Set.mem_univ _⟩).image (fun v => U.value (F.inverse hF v))).subset
      rintro _ ⟨v,hv,rfl⟩
      exact ⟨v,Subtype.ext hv,rfl⟩ }
  hom_inv_id := by apply RVHom.ext; apply Map.ext; intro u; exact Map.inverse_apply F hF u
  inv_hom_id := by apply RVHom.ext; apply Map.ext; intro v; exact Map.apply_inverse F hF v

omit [M ⊨ Axioms.ACVF] in
theorem rvIsoOfFiniteFibres_map {k : ℕ} {U V : RVObject (M := M) S k}
    (F : Map U.domain V.domain) (hF : Function.Bijective F)
    (hUF : U.volume.FiniteFibres) (hVF : V.volume.FiniteFibres)
    (hU : ∀ u i,(U.value u i).val ≠ iRVZero)
    (hV : ∀ v i,(V.value v i).val ≠ iRVZero) :
    (rvIsoOfFiniteFibres F hF hUF hVF hU hV).hom.map=F :=
  rfl

section Matching

variable {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) m s) S}

/-- The map of label domains induced by a bijection taking whole label fibres
to whole label fibres. -/
def pureRVTagMatchingMap (f : Map A B) (h : MapsWholeTagFibres f) :
    Map (pureRVTagDomain A) (pureRVTagDomain B) :=
  definableSurjectiveDescent (pureRVTagQuotient A) (pureRVTagQuotient_surjective A)
    ((pureRVTagQuotient B).comp f) (fun p q hpq =>
      (pureRVTagQuotient_eq_iff B (f p) (f q)).mpr
        (h.labels f p q ((pureRVTagQuotient_eq_iff A p q).mp hpq)))

theorem pureRVTagMatchingMap_commutes (f : Map A B) (h : MapsWholeTagFibres f) (p : A) :
    pureRVTagMatchingMap f h (pureRVTagQuotient A p)=pureRVTagQuotient B (f p) :=
  definableSurjectiveDescent_apply _ _ _ _ p

theorem pureRVTagMatchingMap_bijective (f : Map A B) (hf : Function.Bijective f)
    (h : MapsWholeTagFibres f) : Function.Bijective (pureRVTagMatchingMap f h) := by
  constructor
  · apply definableSurjectiveDescent_injective
    intro p q he
    have hLabel : (f q).val.2=(f p).val.2 :=
      ((pureRVTagQuotient_eq_iff B (f p) (f q)).mp he).symm
    obtain ⟨a,ha,hfa⟩ := (h p (f q)).mp hLabel
    have haq : a=q := hf.injective hfa
    apply (pureRVTagQuotient_eq_iff A p q).mpr
    exact ha.symm.trans (congrArg (fun z : A => z.val.2) haq)
  · exact definableSurjectiveDescent_surjective _ _ _ _
      ((pureRVTagQuotient_surjective B).comp hf.surjective)

end Matching

namespace UnaryRelativeMeasuredMatching

variable {A : DefSet (rawMixedSpace (M := M) 1 r) S} {B : DefSet (rawMixedSpace (M := M) 1 s) S}
variable {f : Map A B} {h00 : M ⊨ Axioms.ACVF00}
variable {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)}
variable {σ : Map B (DefSet.univ (rawGammaPresentation (M := M)) S)}
variable (H : UnaryRelativeMeasuredMatching (G := G) A B f h00 ω σ)

theorem sourceForm_constant (p q : H.geometry.source) (hTags : p.val.2=q.val.2) :
    H.geometry.sourceForm h00 ω p=H.geometry.sourceForm h00 ω q := by
  apply Subtype.ext
  have h := H.sourceContractible p.val p.property q.val q.property hTags
  simpa only [gammaFormExtension_at] using h

theorem targetForm_constant (p q : H.geometry.target) (hTags : p.val.2=q.val.2) :
    H.geometry.targetForm h00 σ p=H.geometry.targetForm h00 σ q := by
  apply Subtype.ext
  have h := H.targetContractible p.val p.property q.val q.property hTags
  simpa only [gammaFormExtension_at] using h

/-- `rv`-contractibility in the form used by the volume identity: the
contracted value of `ω'` at the label of `p` is `ω'(p)`. -/
theorem sourceContracted_at (p : Mixed M 1 H.geometry.sourceArity) (hp : p ∈ H.geometry.source.carrier) :
    rvContractedGamma H.geometry.source.carrier (gammaFormExtension (H.geometry.sourceForm h00 ω))
      (rvInputValues p.2)=gammaFormExtension (H.geometry.sourceForm h00 ω) p :=
  rvContractedGamma_at _ _ H.sourceContractible p hp

theorem targetContracted_at (p : Mixed M 1 H.geometry.targetArity) (hp : p ∈ H.geometry.target.carrier) :
    rvContractedGamma H.geometry.target.carrier (gammaFormExtension (H.geometry.targetForm h00 σ))
      (rvInputValues p.2)=gammaFormExtension (H.geometry.targetForm h00 σ) p :=
  rvContractedGamma_at _ _ H.targetContractible p hp

/-- The source object `(rv(A♭), ω')_1` of `μRV^db[1]`. -/
def sourceRV (hFin : ∀ a : Fin 1 → VF M,{u : Fin H.geometry.sourceArity → RVInfinity M |
      (a,u) ∈ H.geometry.source.carrier}.Finite) : MeasuredRVObject (M := M) S 1 :=
  contractedMeasuredRVObject H.geometry.source H.geometry.sourceTagged H.geometry.sourcePullback hFin
    H.geometry.sourceBounded (H.geometry.sourceForm h00 ω) H.sourceForm_constant

/-- The target object `(rv(B♭), σ')_1` of `μRV^db[1]`. -/
def targetRV (hFin : ∀ b : Fin 1 → VF M,{v : Fin H.geometry.targetArity → RVInfinity M |
      (b,v) ∈ H.geometry.target.carrier}.Finite) : MeasuredRVObject (M := M) S 1 :=
  contractedMeasuredRVObject H.geometry.target H.geometry.targetTagged H.geometry.targetPullback hFin
    H.geometry.targetBounded (H.geometry.targetForm h00 σ) H.targetForm_constant

variable (hA : ∀ a : Fin 1 → VF M,{u : Fin H.geometry.sourceArity → RVInfinity M |
  (a,u) ∈ H.geometry.source.carrier}.Finite)
variable (hB : ∀ b : Fin 1 → VF M,{v : Fin H.geometry.targetArity → RVInfinity M |
  (b,v) ∈ H.geometry.target.carrier}.Finite)

theorem sourceRV_doublyBounded : (H.sourceRV hA).doublyBounded :=
  contractedMeasuredRVObject_doublyBounded _ _ _ _ _ H.geometry.sourceProper.rvBounded _ _

theorem targetRV_doublyBounded : (H.targetRV hB).doublyBounded :=
  contractedMeasuredRVObject_doublyBounded _ _ _ _ _ H.geometry.targetProper.rvBounded _ _

/-- The volume map of `(rv(A♭), ω')_1` is the projection to the leading label. -/
theorem sourceRV_value (u : (H.sourceRV hA).object.domain) :
    (H.sourceRV hA).object.value u=fun _ => u.val H.sourceIndex :=
  contractedMeasuredRVObject_value_unary _ _ _ _ _ _ _ H.sourceIndex H.sourceLeading u

/-- The volume map of `(rv(B♭), σ')_1` is the projection to the leading label. -/
theorem targetRV_value (v : (H.targetRV hB).object.domain) :
    (H.targetRV hB).object.value v=fun _ => v.val H.targetIndex :=
  contractedMeasuredRVObject_value_unary _ _ _ _ _ _ _ H.targetIndex H.targetLeading v

theorem sourceRV_form (p : H.geometry.source) :
    gammaMapValue (H.sourceRV hA).form (pureRVTagQuotient H.geometry.source p)=
      rvContractedGamma H.geometry.source.carrier (gammaFormExtension (H.geometry.sourceForm h00 ω))
        (rvInputValues p.val.2) := by
  rw [H.sourceContracted_at p.val p.property,gammaFormExtension_at]
  exact contractedMeasuredRVObject_form _ _ _ _ _ _ _ p

theorem targetRV_form (q : H.geometry.target) :
    gammaMapValue (H.targetRV hB).form (pureRVTagQuotient H.geometry.target q)=
      rvContractedGamma H.geometry.target.carrier (gammaFormExtension (H.geometry.targetForm h00 σ))
        (rvInputValues q.val.2) := by
  rw [H.targetContracted_at q.val q.property,gammaFormExtension_at]
  exact contractedMeasuredRVObject_form _ _ _ _ _ _ _ q

theorem sourceRV_volumeGamma (p : H.geometry.source) :
    (H.sourceRV hA).volumeGamma (pureRVTagQuotient H.geometry.source p)=
      GammaParameters.codeValue (p.val.2 H.sourceIndex).val :=
  contractedMeasuredRVObject_volumeGamma_unary _ _ _ _ _ _ _ H.sourceIndex H.sourceLeading p

theorem targetRV_volumeGamma (q : H.geometry.target) :
    (H.targetRV hB).volumeGamma (pureRVTagQuotient H.geometry.target q)=
      GammaParameters.codeValue (q.val.2 H.targetIndex).val :=
  contractedMeasuredRVObject_volumeGamma_unary _ _ _ _ _ _ _ H.targetIndex H.targetLeading q

/-- The induced map `f♭_↓ : rv(A♭) → rv(B♭)`. -/
def contractedMap : Map (pureRVTagDomain H.geometry.source) (pureRVTagDomain H.geometry.target) :=
  pureRVTagMatchingMap H.geometry.map H.geometry.wholeFibres

theorem contractedMap_commutes (p : H.geometry.source) :
    H.contractedMap (pureRVTagQuotient H.geometry.source p)=
      pureRVTagQuotient H.geometry.target (H.geometry.map p) :=
  pureRVTagMatchingMap_commutes _ _ p

theorem contractedMap_bijective : Function.Bijective H.contractedMap :=
  pureRVTagMatchingMap_bijective _ H.geometry.bijective _

/-- `f♭_↓` is the RV map of the matching, read on label domains. -/
theorem contractedMap_eq_rv (p : H.geometry.source) :
    (H.contractedMap (pureRVTagQuotient H.geometry.source p)).val=
      (H.rv.map (rvTagQuotientMap H.geometry.source p)).val.2 := by
  rw [H.contractedMap_commutes p,H.rv.commutes p]
  rfl

/-- Lemma 6.38, last clause: `f♭_↓` is a morphism of `μRV^db[1]`
`(rv(A♭), ω')_1 → (rv(B♭), σ')_1`. -/
def measuredRVIso : MeasuredRVIso (H.sourceRV hA) (H.targetRV hB) where
  iso := rvIsoOfFiniteFibres (U := (H.sourceRV hA).object) (V := (H.targetRV hB).object)
    H.contractedMap H.contractedMap_bijective (H.sourceRV hA).finiteVolume (H.targetRV hB).finiteVolume
    (H.sourceRV hA).nonzero (H.targetRV hB).nonzero
  balance u := by
    obtain ⟨p,rfl⟩ := pureRVTagQuotient_surjective H.geometry.source u
    change gammaMapValue (H.sourceRV hA).form (pureRVTagQuotient H.geometry.source p) *
        (H.sourceRV hA).volumeGamma (pureRVTagQuotient H.geometry.source p)=
      gammaMapValue (H.targetRV hB).form (H.contractedMap (pureRVTagQuotient H.geometry.source p)) *
        (H.targetRV hB).volumeGamma (H.contractedMap (pureRVTagQuotient H.geometry.source p))
    rw [H.contractedMap_commutes p,H.sourceRV_form hA p,H.targetRV_form hB (H.geometry.map p),
      H.sourceRV_volumeGamma hA p,H.targetRV_volumeGamma hB (H.geometry.map p)]
    have h := H.rv.volume (rvTagQuotientMap H.geometry.source p)
    rw [H.rv.commutes p] at h
    exact h

theorem measuredRVIso_map (p : H.geometry.source) :
    (H.measuredRVIso hA hB).iso.hom.map (pureRVTagQuotient H.geometry.source p)=
      pureRVTagQuotient H.geometry.target (H.geometry.map p) :=
  H.contractedMap_commutes p

end UnaryRelativeMeasuredMatching

end RVContraction

theorem lemma_6_38_bounded_variable_apertures
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B₀ : VFGeneratedFieldBase S)
    (hsmall : Cardinal.mk (S : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(S : Set M),∅⟩ : ParameterBase M))
    (hnt : ∃ x : B₀.field,x≠0 ∧ Valued.v x.val≠1)
    (A : DefSet (rawMixedSpace (M := M) 1 r) (S : Set M))
    (B : DefSet (rawMixedSpace (M := M) 1 s) (S : Set M))
    (f : Map A B) (hf : ProperCovariantHomeomorphism f)
    (hA : ProperInvariant (S : Set M) A.carrier) (hB : ProperInvariant (S : Set M) B.carrier)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) (S : Set M)))
    (σ : Map B (DefSet.univ (rawGammaPresentation (M := M)) (S : Set M)))
    (hωLevels : ∀ u γ,IsOpen {a : Fin 1 → VF M | (a,u) ∈ A.carrier ∧ gammaFormExtension ω (a,u)=γ})
    (hσLevels : ∀ u γ,IsOpen {a : Fin 1 → VF M | (a,u) ∈ B.carrier ∧ gammaFormExtension σ (a,u)=γ})
    (hGeneric : ∀ a : A,AlgebraicIndependent (vfParameterField (S : Set M)) a.val.1 →
      ∃ J : VF M,HasMixedVFJacobianAt f a J ∧ vfValue J=(gammaMapValue ω a/gammaMapValue σ (f a)).val) :
    ∃ H : UnaryRelativeMeasuredMatching (G := G) A B f h00 ω σ,
      RelativeApertureChain (G := G) A H.geometry.source H.geometry.sourceMap ∧
      RelativeApertureChain (G := G) B H.geometry.target H.geometry.targetMap := by
  obtain ⟨H⟩ := unary_relative_measured_rv_family_matching_exists h00 hc linear hκ hs hv S B₀ hsmall hΓ hnt
    A B f hf hA hB ω σ hωLevels hσLevels hGeneric
  exact ⟨H,H.geometry.sourceChain.toRelativeChain hc h00 linear hκ.le hs hsmall hΓ,
    H.geometry.targetChain.toRelativeChain hc h00 linear hκ.le hs hsmall hΓ⟩

/-- Lemma 6.38 (`simul:special:dim:1`) with its final clauses. Besides the
bounded variable-aperture chains `T_A`, `T_B` and the measured RV matching,
the transported forms `ω' = ω ∘ T_A⁻¹` and `σ' = σ ∘ T_B⁻¹` are
`rv`-contractible, and the induced map `f♭_↓` is a morphism of `μRV^db[1]`
from `(rv(A♭), ω')_1` to `(rv(B♭), σ')_1`: both contracted objects are doubly
bounded measured RV objects whose finite-to-one volume map is the projection to
the leading label (Notation `0coor`), and `f♭_↓` is a measured RV isomorphism
commuting with the label quotients. The finite RV fibres of `A` (an object of
`VF[1]`, Definition `defn:VF:cat`) give the finite RV fibres of `A♭`, `B♭` by
Lemma `RV:fiber:dim:same`. -/
theorem lemma_6_38_bounded_variable_apertures_contractible
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B₀ : VFGeneratedFieldBase S)
    (hsmall : Cardinal.mk (S : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(S : Set M),∅⟩ : ParameterBase M))
    (hnt : ∃ x : B₀.field,x≠0 ∧ Valued.v x.val≠1)
    (A : DefSet (rawMixedSpace (M := M) 1 r) (S : Set M))
    (B : DefSet (rawMixedSpace (M := M) 1 s) (S : Set M))
    (f : Map A B) (hf : ProperCovariantHomeomorphism f)
    (hA : ProperInvariant (S : Set M) A.carrier) (hB : ProperInvariant (S : Set M) B.carrier)
    (hFinite : ∀ a : Fin 1 → VF M,{u : Fin r → RVInfinity M | (a,u) ∈ A.carrier}.Finite)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) (S : Set M)))
    (σ : Map B (DefSet.univ (rawGammaPresentation (M := M)) (S : Set M)))
    (hωLevels : ∀ u γ,IsOpen {a : Fin 1 → VF M | (a,u) ∈ A.carrier ∧ gammaFormExtension ω (a,u)=γ})
    (hσLevels : ∀ u γ,IsOpen {a : Fin 1 → VF M | (a,u) ∈ B.carrier ∧ gammaFormExtension σ (a,u)=γ})
    (hGeneric : ∀ a : A,AlgebraicIndependent (vfParameterField (S : Set M)) a.val.1 →
      ∃ J : VF M,HasMixedVFJacobianAt f a J ∧ vfValue J=(gammaMapValue ω a/gammaMapValue σ (f a)).val) :
    ∃ H : UnaryRelativeMeasuredMatching (G := G) A B f h00 ω σ,
      RelativeApertureChain (G := G) A H.geometry.source H.geometry.sourceMap ∧
      RelativeApertureChain (G := G) B H.geometry.target H.geometry.targetMap ∧
      (∀ p ∈ H.geometry.source.carrier,∀ q ∈ H.geometry.source.carrier,p.2=q.2 →
        gammaFormExtension (H.geometry.sourceForm h00 ω) p=gammaFormExtension (H.geometry.sourceForm h00 ω) q) ∧
      (∀ p ∈ H.geometry.target.carrier,∀ q ∈ H.geometry.target.carrier,p.2=q.2 →
        gammaFormExtension (H.geometry.targetForm h00 σ) p=gammaFormExtension (H.geometry.targetForm h00 σ) q) ∧
      ∃ (hA' : ∀ a : Fin 1 → VF M,{u : Fin H.geometry.sourceArity → RVInfinity M |
            (a,u) ∈ H.geometry.source.carrier}.Finite)
        (hB' : ∀ b : Fin 1 → VF M,{v : Fin H.geometry.targetArity → RVInfinity M |
            (b,v) ∈ H.geometry.target.carrier}.Finite),
        (H.sourceRV hA').doublyBounded ∧ (H.targetRV hB').doublyBounded ∧
        (∀ u,(H.sourceRV hA').object.value u=fun _ => u.val H.sourceIndex) ∧
        (∀ v,(H.targetRV hB').object.value v=fun _ => v.val H.targetIndex) ∧
        ∃ e : MeasuredRVIso (H.sourceRV hA') (H.targetRV hB'),
          ∀ p : H.geometry.source,
            e.iso.hom.map (pureRVTagQuotient H.geometry.source p)=
              pureRVTagQuotient H.geometry.target (H.geometry.map p) := by
  obtain ⟨H,hSource,hTarget⟩ := lemma_6_38_bounded_variable_apertures (G := G) h00 hc linear hκ hs hv S B₀
    hsmall hΓ hnt A B f hf hA hB ω σ hωLevels hσLevels hGeneric
  have hA' := finite_rv_fibers_of_bijective hc h00 hκ.le hs hsmall H.geometry.sourceMap
    (H.geometry.sourceChain.bijective h00) hFinite
  have hB' := finite_rv_fibers_of_bijective hc h00 hκ.le hs hsmall H.geometry.targetMap
    (H.geometry.targetChain.bijective h00)
    (finite_rv_fibers_of_bijective hc h00 hκ.le hs hsmall f hf.bijective hFinite)
  exact ⟨H,hSource,hTarget,H.sourceContractible,H.targetContractible,hA',hB',
    H.sourceRV_doublyBounded hA',H.targetRV_doublyBounded hB',H.sourceRV_value hA',H.targetRV_value hB',
    H.measuredRVIso hA' hB',H.measuredRVIso_map hA' hB'⟩

end DiamondIntegral.Section6
