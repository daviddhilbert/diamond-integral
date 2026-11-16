import «section 6».UnaryRootFoci
import «section 6».ApertureRootDecrease

/-! The actual finite-aperture unary root step: center, retain the core
flag, and regularize. Only noncore roots are carried to the next family.
Its full graph is over the original base and its fiber bound decreases. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}

def rvTagSlice (B : DefSet (rawMixedSpace (M := M) n r) S) (j : Fin r) (b : Bool) :
    DefSet (rawMixedSpace (M := M) n r) S := by
  refine ⟨{p | p ∈ B.carrier ∧ p.2 j = branchTag b},?_⟩
  apply (mixed_definable_iff_values_image S _).mpr
  have hflag : S.Definable LRV {z : Fin n ⊕ Fin r → M | (branchTag (M := M) b).val = z (.inr j)} :=
    (branchTag_definable S b).ofPred_eq (Set.DefinableFun.proj LRV)
  convert ((mixed_definable_iff_values_image S _).mp B.definable).inter hflag using 1
  ext z
  exact ⟨fun ⟨p,⟨hp,hb⟩,he⟩ => ⟨⟨p,hp,he⟩,
    (congrArg Subtype.val hb).symm.trans (congrFun he (.inr j))⟩,
    fun ⟨⟨p,hp,he⟩,hb⟩ => ⟨p,⟨hp,Subtype.ext ((congrFun he (.inr j)).trans hb.symm)⟩,he⟩⟩

namespace UnaryRootFamily

variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def stepMap (D : CentripetalData (G := G) A) := (regularization D.map.image).comp D.bijection

def stepPoint (D : CentripetalData (G := G) A) (p : Mixed M 1 r) := regularize (D.point p)

theorem stepMap_apply (D : CentripetalData (G := G) A) (p : A) :
    (stepMap D p).val = stepPoint D p.val := rfl

def remainingRoots (R : UnaryRootFamily A) (D : CentripetalData (G := G) A) :=
  rvTagSlice ((stepMap D).restrict R.subset).image (Fin.natAdd 1 (Fin.castAdd r (0 : Fin 1))) false

theorem remainingRoots_iff (R : UnaryRootFamily A) (D : CentripetalData (G := G) A)
    (h00 : M ⊨ Axioms.ACVF00) (p : Mixed M 1 (1+(1+r))) :
    p ∈ (R.remainingRoots D).carrier ↔
      ∃ a : A, a.val ∈ R.roots.carrier ∧ D.core a.val = false ∧ stepPoint D a.val = p := by
  constructor
  · rintro ⟨⟨a,ha⟩,hflag⟩
    let a' : A := ⟨a.val,R.subset a.property⟩
    have he : stepPoint D a'.val = p := ha
    have hb : branchTag (M := M) (D.core a'.val) = branchTag false := by
      have hh := congrArg (fun z : Mixed M 1 (1+(1+r)) => z.2 (Fin.natAdd 1 (Fin.castAdd r 0))) he
      simpa only [stepPoint,regularize,CentripetalData.point,Fin.append_left,Fin.append_right] using hh.trans hflag
    exact ⟨a',a.property,branchTag_injective h00 hb,he⟩
  · rintro ⟨a,ha,hcore,rfl⟩
    refine ⟨⟨⟨a.val,ha⟩,rfl⟩,?_⟩
    simp only [stepPoint,regularize,CentripetalData.point,Fin.append_right,Fin.append_left,hcore]

theorem root_active (R : UnaryRootFamily A) {p : Mixed M 1 r} (hp : p ∈ R.roots.carrier) :
    p.2 ∈ R.activeTags.carrier := ⟨p,⟨R.subset hp,hp⟩,rfl⟩

def oldTags (t : Fin (1+(1+r)) → RVInfinity M) : Fin r → RVInfinity M :=
  fun i => t (Fin.natAdd 1 (Fin.natAdd 1 i))

def cutoff (R : UnaryRootFamily A) (D : CentripetalData (G := G) A) (u : Fin r → RVInfinity M) : Gamma M :=
  if h : D.coefficient * Barycentre.mean (R.fibre u) ≠ 0 then finiteValue _ h else 1

theorem remainingRoots_child_subset (R : UnaryRootFamily A) (D : CentripetalData (G := G) A)
    (h00 : M ⊨ Axioms.ACVF00) (hcoord : D.coordinate = 0) (hact : D.activeTags = R.activeTags)
    (hfocus : ∀ x u, D.focus x u = Barycentre.mean (R.fibre u))
    (t : Fin (1+(1+r)) → RVInfinity M) (x : VF M)
    (hx : ((fun _ : Fin 1 => x),t) ∈ (R.remainingRoots D).carrier) :
    x ∈ noncoreRootChild (R.fibre (oldTags t)) (R.cutoff D (oldTags t)) (t 0) := by
  obtain ⟨a,ha,hcore,he⟩ := (R.remainingRoots_iff D h00 _).mp hx
  have hu : a.val.2 = oldTags t := by
    funext i
    have hh := congrArg (fun z : Mixed M 1 (1+(1+r)) => z.2 (Fin.natAdd 1 (Fin.natAdd 1 i))) he
    simpa only [stepPoint,regularize,CentripetalData.point,Fin.append_right,oldTags] using hh
  have hactive : a.val.2 ∈ D.activeTags.carrier := hact.symm ▸ R.root_active ha
  have hFocus : D.extendedFocus a.val = Barycentre.mean (R.fibre a.val.2) := by
    rw [D.extendedFocus_active a.property hactive,hfocus]
  have hxval : a.val.1 0 - Barycentre.mean (R.fibre (oldTags t)) = x := by
    have hh := congrArg (fun z : Mixed M 1 (1+(1+r)) => z.1 0) he
    simpa only [stepPoint,regularize,CentripetalData.point,hcoord,Function.update_self,
      hcore,Bool.false_eq_true,ite_false,add_zero,hFocus,hu] using hh
  have hrv : rv M (a.val.1 0-Barycentre.mean (R.fibre (oldTags t))) = t 0 := by
    have hh := congrArg (fun z : Mixed M 1 (1+(1+r)) => z.2 (Fin.castAdd (1+r) 0)) he
    change rv M ((D.point a.val).1 0) = t 0 at hh
    simpa only [CentripetalData.point,hcoord,Function.update_self,
      hcore,Bool.false_eq_true,ite_false,add_zero,hFocus,hu] using hh
  have hprod : D.coefficient * Barycentre.mean (R.fibre (oldTags t)) ≠ 0 := by
    rw [← hu,← hFocus]
    exact mul_ne_zero D.coefficient_nonzero (D.focus_nonzero a.property hactive)
  have hcutoff : (R.cutoff D (oldTags t)).val =
      vfValue (D.coefficient * Barycentre.mean (R.fibre (oldTags t))) := by
    rw [cutoff,dite_eq_left hprod]
    rfl
  have hcut : vfValue (a.val.1 0-Barycentre.mean (R.fibre (oldTags t))) ≤ (R.cutoff D (oldTags t)).val := by
    have hh : vfValue (a.val.1 D.coordinate-D.extendedFocus a.val) ≤
        vfValue (D.coefficient*D.extendedFocus a.val) :=
      le_of_not_gt (of_decide_eq_false hcore)
    simpa only [hcoord,hFocus,hu,hcutoff] using hh
  refine Finset.mem_image.mpr ⟨a.val.1 0,Finset.mem_filter.mpr ⟨?_,hcut,hrv⟩,hxval⟩
  rw [R.mem_fibre,← hu]
  have hEta : (fun _ : Fin 1 => a.val.1 0) = a.val.1 := by funext i; fin_cases i; rfl
  rw [hEta]
  change a.val ∈ R.roots.carrier
  exact ha

def stepFamily (R : UnaryRootFamily A) (D : CentripetalData (G := G) A)
    (h00 : M ⊨ Axioms.ACVF00) (hcoord : D.coordinate = 0) (hact : D.activeTags = R.activeTags)
    (hfocus : ∀ x u, D.focus x u = Barycentre.mean (R.fibre u)) :
    UnaryRootFamily (regularizeMap D.map.image).image where
  roots := R.remainingRoots D
  subset := by
    rintro p ⟨⟨a,ha⟩,_⟩
    exact ha ▸ ((stepMap D) ⟨a.val,R.subset a.property⟩).property
  finite := fun t => ((noncoreRootChild (R.fibre (oldTags t)) (R.cutoff D (oldTags t)) (t 0)).finite_toSet).subset
    (fun x hx => R.remainingRoots_child_subset D h00 hcoord hact hfocus t x hx)

theorem stepFamily_bound (R : UnaryRootFamily A) (D : CentripetalData (G := G) A)
    (h00 : M ⊨ Axioms.ACVF00) (hcoord : D.coordinate = 0) (hact : D.activeTags = R.activeTags)
    (hfocus : ∀ x u, D.focus x u = Barycentre.mean (R.fibre u)) (d : ℕ)
    (hbound : ∀ u, (R.fibre u).card ≤ d+1) :
    ∀ t, ((R.stepFamily D h00 hcoord hact hfocus).fibre t).card ≤ d := by
  intro t
  apply noncoreRootChild_bound h00 _ _ _ d (hbound (oldTags t))
  intro x hx
  exact R.remainingRoots_child_subset D h00 hcoord hact hfocus t x
    (((R.stepFamily D h00 hcoord hact hfocus).mem_fibre t x).mp hx)

theorem stepMap_chain (D : CentripetalData (G := G) A)
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) :
    SpecialCovariantChain (G := G) A (regularizeMap D.map.image).image (stepMap D) :=
  .comp (.centripetal A D) (.regularize D.map.image (D.image_properInvariant h00 hc hκ hs hv) D.image_vfDoublyBounded)

end UnaryRootFamily
end DiamondIntegral.Section6
