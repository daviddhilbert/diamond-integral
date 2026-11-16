import «section 6».UnaryRootControl
import «section 6».CentripetalCoreSaturation

/-! Every protected subset image is RV-saturated on retained core
labels. The proof uses its actual permitted centripetal restriction,
then retains the regularization and all old tags exactly. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.UnaryRootFamily

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A C : DefSet (rawMixedSpace (M := M) 1 r) S}

theorem core_subset_image_rv_saturated
    (h00 : M ⊨ Axioms.ACVF00) (D : CentripetalData (G := G) A) (E : CentripetalData (G := G) C)
    (hCA : C.carrier ⊆ A.carrier) (hpoint : ∀ p ∈ C.carrier, E.point p = D.point p)
    {q q' : Mixed M 1 (1+(1+r))}
    (hq : q ∈ ((stepMap D).restrict hCA).image.carrier)
    (hflag : q.2 (Fin.natAdd 1 (Fin.castAdd r (0 : Fin 1))) = branchTag true)
    (hVF : tupleRV M q.1 = tupleRV M q'.1) (hRV : q.2 = q'.2) :
    q' ∈ ((stepMap D).restrict hCA).image.carrier := by
  obtain ⟨p,hp⟩ := hq
  have heD : stepPoint D p.val = q := hp
  have heE : stepPoint E p.val = q := (congrArg regularize (hpoint p.val p.property)).trans heD
  have hcore : E.core p.val = true := by
    apply branchTag_injective h00
    have hh := congrArg (fun z : Mixed M 1 (1+(1+r)) => z.2 (Fin.natAdd 1 (Fin.castAdd r 0))) heE
    simpa only [stepPoint,regularize,CentripetalData.point,Fin.append_right,Fin.append_left] using hh.trans hflag
  have hcoord : E.coordinate = 0 := Subsingleton.elim _ _
  have hscalar : (E.point p.val).1 0 = q.1 0 := congrArg (fun z : Mixed M 1 (1+(1+r)) => z.1 0) heE
  have hy : rv M (q'.1 0) = rv M ((E.point p.val).1 E.coordinate) := by
    rw [hcoord,hscalar]
    exact (congrFun hVF 0).symm
  have hz := E.core_image_saturated p.property hcore (q'.1 0) hy
  rw [E.image_carrier] at hz
  obtain ⟨b,hb,hbpoint⟩ := hz
  have hstep : stepPoint D b = regularize (Function.update (E.point p.val).1 E.coordinate (q'.1 0),(E.point p.val).2) := by
    change regularize (D.point b) = _
    rw [← hpoint b hb,hbpoint]
  have hfield : Function.update (E.point p.val).1 E.coordinate (q'.1 0) = q'.1 := by
    funext i
    fin_cases i
    change Function.update (E.point p.val).1 E.coordinate (q'.1 0) 0 = q'.1 0
    rw [hcoord,Function.update_self]
  have hOld := congrArg Prod.snd heE
  have hEfield : (E.point p.val).1 = q.1 := congrArg Prod.fst heE
  have htarget : regularize (Function.update (E.point p.val).1 E.coordinate (q'.1 0),(E.point p.val).2) = q' := by
    apply Prod.ext
    · exact hfield
    · change Fin.append (tupleRV M (Function.update (E.point p.val).1 E.coordinate (q'.1 0))) (E.point p.val).2 = q'.2
      rw [hfield,← hRV]
      change Fin.append (tupleRV M q'.1) (E.point p.val).2 = q.2
      change Fin.append (tupleRV M (E.point p.val).1) (E.point p.val).2 = q.2 at hOld
      rw [← hOld,hEfield,hVF]
  exact ⟨⟨b,hb⟩,hstep.trans htarget⟩

end DiamondIntegral.Section6.UnaryRootFamily
