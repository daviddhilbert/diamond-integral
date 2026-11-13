import «section 3».GammaProducts
import «section 3».GammaCodeRestrictions
import «section 3».RVFamilyProducts

/-! Full Gamma code preimages commute with coordinate products. -/
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M} {k l : ℕ}

def gammaCodeLeft (c : (codeSpace ((volumeGammaSpace hc).power (Fin (k + l)))).Carrier) :
    (codeSpace ((volumeGammaSpace hc).power (Fin k))).Carrier :=
  ⟨fun p => c.val (Fin.castAdd l p.1, p.2), fun i => c.property (Fin.castAdd l i)⟩

def gammaCodeRight (c : (codeSpace ((volumeGammaSpace hc).power (Fin (k + l)))).Carrier) :
    (codeSpace ((volumeGammaSpace hc).power (Fin l))).Carrier :=
  ⟨fun p => c.val (Fin.natAdd k p.1, p.2), fun i => c.property (Fin.natAdd k i)⟩

def gammaCodeAppend
    (a : (codeSpace ((volumeGammaSpace hc).power (Fin k))).Carrier)
    (b : (codeSpace ((volumeGammaSpace hc).power (Fin l))).Carrier) :
    (codeSpace ((volumeGammaSpace hc).power (Fin (k + l)))).Carrier :=
  ⟨fun p => Fin.append (fun i => a.val (i, p.2)) (fun j => b.val (j, p.2)) p.1, by
    intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left, Function.comp_def] using a.property i
    · simpa only [Fin.append_right, Function.comp_def] using b.property j⟩

theorem gammaCodeAppend_decode
    (a : (codeSpace ((volumeGammaSpace hc).power (Fin k))).Carrier)
    (b : (codeSpace ((volumeGammaSpace hc).power (Fin l))).Carrier) :
    ((volumeGammaSpace hc).power (Fin (k + l))).decode (gammaCodeAppend a b) =
      Fin.append (((volumeGammaSpace hc).power (Fin k)).decode a)
        (((volumeGammaSpace hc).power (Fin l)).decode b) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · simp only [Fin.append_left]
    apply Subtype.ext
    change Values.vrv _ = Values.vrv _
    congr 1
    apply Subtype.ext
    change Fin.append (fun i => a.val (i, (0 : Fin 1))) (fun j => b.val (j, (0 : Fin 1))) (Fin.castAdd l i) = a.val (i, (0 : Fin 1))
    exact Fin.append_left _ _ _
  · simp only [Fin.append_right]
    apply Subtype.ext
    change Values.vrv _ = Values.vrv _
    congr 1
    apply Subtype.ext
    change Fin.append (fun i => a.val (i, (0 : Fin 1))) (fun j => b.val (j, (0 : Fin 1))) (Fin.natAdd k j) = b.val (j, (0 : Fin 1))
    exact Fin.append_right _ _ _

theorem gammaRVCodeLift_product (A : GammaPiece hc S k) (B : GammaPiece hc S l) :
    (gammaRVCodeLift (gammaAppendMap A B).image).domain.carrier =
      (rvProductDomain (gammaRVCodeLift A).domain (gammaRVCodeLift B).domain).carrier := by
  ext t
  constructor
  · rintro ⟨c, rfl⟩
    obtain ⟨p, hp⟩ := c.property
    have ha : ((volumeGammaSpace hc).power (Fin k)).decode (gammaCodeLeft c.val) ∈ A.carrier := by
      have he : ((volumeGammaSpace hc).power (Fin k)).decode (gammaCodeLeft c.val) = p.val.1 := by
        funext i
        have h := congrFun hp (Fin.castAdd l i)
        change Fin.append p.val.1 p.val.2 (Fin.castAdd l i) = _ at h
        exact (Fin.append_left _ _ _).symm.trans h |>.symm
      exact he.symm ▸ p.property.1
    have hb : ((volumeGammaSpace hc).power (Fin l)).decode (gammaCodeRight c.val) ∈ B.carrier := by
      have he : ((volumeGammaSpace hc).power (Fin l)).decode (gammaCodeRight c.val) = p.val.2 := by
        funext i
        have h := congrFun hp (Fin.natAdd k i)
        change Fin.append p.val.1 p.val.2 (Fin.natAdd k i) = _ at h
        exact (Fin.append_right _ _ _).symm.trans h |>.symm
      exact he.symm ▸ p.property.2
    refine ⟨⟨(gammaCodeTuple (gammaCodeLeft c.val), gammaCodeTuple (gammaCodeRight c.val)),
      ⟨⟨gammaCodeLeft c.val, ha⟩, rfl⟩, ⟨⟨gammaCodeRight c.val, hb⟩, rfl⟩⟩, ?_⟩
    funext i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · exact Fin.append_left _ _ _
    · exact Fin.append_right _ _ _
  · rintro ⟨p, rfl⟩
    obtain ⟨a, ha⟩ := p.property.1
    obtain ⟨b, hb⟩ := p.property.2
    let c := gammaCodeAppend a.val b.val
    have hc' : ((volumeGammaSpace hc).power (Fin (k + l))).decode c ∈ (gammaAppendMap A B).image.carrier := by
      refine ⟨⟨((((volumeGammaSpace hc).power (Fin k)).decode a.val),
        (((volumeGammaSpace hc).power (Fin l)).decode b.val)), a.property, b.property⟩, ?_⟩
      exact (gammaCodeAppend_decode a.val b.val).symm
    refine ⟨⟨c, hc'⟩, ?_⟩
    change gammaCodeTuple c = rvAppend p.val.1 p.val.2
    rw [← ha, ← hb]
    funext i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · change gammaCodeTuple c (Fin.castAdd l i) = rvAppend (gammaCodeTuple a.val) (gammaCodeTuple b.val) (Fin.castAdd l i)
      simp only [rvAppend, Fin.append_left]
      apply Subtype.ext
      change Fin.append (fun i => a.val.val (i, (0 : Fin 1))) (fun j => b.val.val (j, (0 : Fin 1))) (Fin.castAdd l i) = _
      exact Fin.append_left _ _ _
    · change gammaCodeTuple c (Fin.natAdd k j) = rvAppend (gammaCodeTuple a.val) (gammaCodeTuple b.val) (Fin.natAdd k j)
      simp only [rvAppend, Fin.append_right]
      apply Subtype.ext
      change Fin.append (fun i => a.val.val (i, (0 : Fin 1))) (fun j => b.val.val (j, (0 : Fin 1))) (Fin.natAdd k j) = _
      exact Fin.append_right _ _ _

end DiamondIntegral.Section3
