import «section 3».GammaRVFormCodeRows
import «section 3».GammaMeasuredTypedRowValidity

/-! A family of finite RV objects inherits any complete Gamma density
on its retained labels. This construction uses all RV representatives
of the density, without a section of the value map. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open IntegrationInACVF.Section6
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {p a k : ℕ} {sp : Fin p → SortTag}

def gammaLabelDensityIndices (p a : ℕ) : Fin (a+1) → Fin ((p+a)+1) :=
  Fin.addCases (fun i => Fin.castAdd 1 (Fin.natAdd p i)) (Fin.natAdd (p+a))

theorem gammaLabelDensityIndices_append (z : Fin p → M) (x : Fin a → M) (c : Fin 1 → M) :
    Fin.append (Fin.append z x) c ∘ gammaLabelDensityIndices p a = Fin.append x c := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp only [Function.comp_apply,gammaLabelDensityIndices,Fin.addCases_left,Fin.addCases_right,
      Fin.append_left,Fin.append_right]

def gammaMeasuredLabelSchema (F : GammaFiniteRVSchema B p a k sp)
    {A : GammaGroundDefSet hc B (rawRVSpace (M := M) a)} (ω : GammaGroundVolumeForm hc B A) :
    GammaMeasuredRVSchema hc B p a k sp where
  object := F
  density := {w | w ∘ Fin.castAdd 1 ∈ F.domain ∧ w ∘ gammaLabelDensityIndices p a ∈ gammaRVFormCodeRows ω ∧
    w ∈ sortedUniverse (Fin.append (Fin.append sp (fun _ : Fin a => .rv)) (fun _ : Fin 1 => .rv))}
  density_definable := by
    let st := Fin.append (Fin.append sp (fun _ : Fin a => SortTag.rv)) (fun _ : Fin 1 => SortTag.rv)
    have h := (F.domain_definable.preimage_real st (Fin.castAdd 1)).inter
      ((gammaRVFormCodeRows_definable ω).preimage_real st (gammaLabelDensityIndices p a))
    convert h using 1
    ext w
    change (_ ∧ _ ∧ _) ↔ ((_ ∧ _) ∧ (_ ∧ _))
    constructor
    · exact fun h => ⟨⟨h.1,h.2.2⟩,h.2⟩
    · exact fun h => ⟨h.1.1,h.2⟩
  density_code w hw := by
    have h := gammaRVFormCodeRows_code ω _ hw.2.1
    have he : (w ∘ gammaLabelDensityIndices p a) ∘ Fin.natAdd a = w ∘ Fin.natAdd (p+a) := by
      funext j
      simp only [Function.comp_apply,gammaLabelDensityIndices,Fin.addCases_right]
    exact he ▸ h

theorem gammaMeasuredLabelSchema_density
    (F : GammaFiniteRVSchema B p a k sp)
    {A : GammaGroundDefSet hc B (rawRVSpace (M := M) a)} (ω : GammaGroundVolumeForm hc B A)
    (z : Fin p → M) (hz : ∀ j, sortEval (sp j) (z j))
    (x : Fin a → CanonicalRV.RVSort M) (c : (volumeGammaSpace hc).domain) :
    (gammaMeasuredLabelSchema F ω).rowDensity z x c ↔
      x ∈ F.rowDomain z ∧ ∃ u : A, u.val = x ∧ (ω u).val = (volumeGammaSpace hc).decode c := by
  have hFirst : Fin.append (Fin.append z (rvValues x)) c.val ∘ Fin.castAdd 1 = Fin.append z (rvValues x) :=
    funext (Fin.append_left _ _)
  have hSort : Fin.append (Fin.append z (rvValues x)) c.val ∈
      sortedUniverse (Fin.append (Fin.append sp (fun _ : Fin a => .rv)) (fun _ : Fin 1 => .rv)) := by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa only [Fin.append_left] using hz j
      · simpa only [Fin.append_left,Fin.append_right,sortEval,iRV,rvValues] using (x j).property
    · intro j
      change Fin 1 at j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simpa only [Fin.append_right,sortEval,iRV] using c.property.1
  change (_ ∧ _ ∧ _) ↔ _
  rw [hFirst,gammaLabelDensityIndices_append,and_iff_left hSort,gammaRVFormCodeRows_mem]
  rfl

theorem gammaMeasuredLabelSchema_valid
    (F : GammaFiniteRVSchema B p a k sp)
    {A : GammaGroundDefSet hc B (rawRVSpace (M := M) a)} (ω : GammaGroundVolumeForm hc B A)
    (z : Fin p → M) (hF : F.valid z) (hA : F.rowDomain z ⊆ A.carrier) :
    (gammaMeasuredLabelSchema F ω).valid z := by
  let E := gammaMeasuredLabelSchema F ω
  have hD := gammaMeasuredLabelSchema_density F ω z hF.1
  apply E.valid_of_typed z hF
  · intro x hx
    let u : A := ⟨x,hA hx⟩
    obtain ⟨c,hc⟩ := (volumeGammaSpace hc).onto (ω u).val
    exact ⟨c,(hD x c).mpr ⟨hx,u,rfl,hc.symm⟩⟩
  · intro x c hx
    exact ((hD x c).mp hx).1
  · intro x c hc d
    obtain ⟨hx,u,hu,hω⟩ := (hD x c).mp hc
    rw [hD x d]
    constructor
    · rintro ⟨_,v,hv,hvω⟩
      have he : v = u := Subtype.ext (hv.trans hu.symm)
      exact hω.symm.trans ((congrArg (fun t => (ω t).val) he).symm.trans hvω)
    · intro h
      exact ⟨hx,u,hu,hω.trans h⟩

end DiamondIntegral.Section3
