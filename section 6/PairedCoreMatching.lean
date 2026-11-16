import «section 6».PairedCoreDomains

/-! The literal restriction of the original bijection to actual paired
core domains is a definable bijection of whole old-label fibres. The
label condition is derived from the actual paired center map. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r s : ℕ}
variable {A C : DefSet (rawMixedSpace (M := M) 1 r) S} {B T : DefSet (rawMixedSpace (M := M) 1 s) S}
variable {f : Map A B} {E : DefSet (rawMixedSpace (M := M) 1 r) S} {hEA : E.carrier ⊆ A.carrier} {α β : Gamma M}

theorem exists_paired_core_matching (hf : Function.Bijective f)
    (D : UniformFinitePairedCores f E hEA α β)
    (hC : C.carrier=D.sourceCoreSet) (hT : T.carrier=D.targetCoreSet)
    (hSourceUnique : ∀ p q : E,p.val.2=q.val.2 → p=q)
    (hTargetUnique : ∀ p q : E,(f ⟨p.val,hEA p.property⟩).val.2=(f ⟨q.val,hEA q.property⟩).val.2 → p=q) :
    ∃ g : Map C T,Function.Bijective g ∧ MapsWholeTagFibres g ∧
      ∀ p : C,∃ hp : p.val ∈ A.carrier,(g p).val=(f ⟨p.val,hp⟩).val := by
  have hCA : C.carrier ⊆ A.carrier := fun x hx => (show x ∈ D.sourceCoreSet from hC ▸ hx).1
  have hTB : T.carrier ⊆ B.carrier := fun y hy => (show y ∈ D.targetCoreSet from hT ▸ hy).1
  let g : Map C T := {
    toFun := fun p => ⟨(f ⟨p.val,hCA p.property⟩).val,
      hT.symm ▸ (D.source_core_iff_target hf.injective ⟨p.val,hCA p.property⟩).mp (hC ▸ p.property)⟩
    graph_definable := (f.restrict hCA).graph_definable }
  have hBij : Function.Bijective g := by
    constructor
    · intro p q he
      have hVal := congrArg (fun z : T => z.val) he
      have hEq : (⟨p.val,hCA p.property⟩ : A)=⟨q.val,hCA q.property⟩ :=
        hf.injective (Subtype.ext hVal)
      have hEqVal := congrArg (fun z : A => z.val) hEq
      exact Subtype.ext hEqVal
    · intro q
      obtain ⟨a,ha⟩ := hf.surjective ⟨q.val,hTB q.property⟩
      have hTarget : (f a).val ∈ D.targetCoreSet :=
        (congrArg Subtype.val ha).symm ▸ (hT ▸ q.property)
      have hSource : a.val ∈ C.carrier := hC.symm ▸ (D.source_core_iff_target hf.injective a).mpr hTarget
      have haVal := congrArg (fun z : B => z.val) ha
      exact ⟨⟨a.val,hSource⟩,Subtype.ext haVal⟩
  have hLabel (x : C) (p : E) (hpx : p.val.2=x.val.2)
      (hClose : vfValue ((D.sourceOffset p).val 0) < vfValue (x.val.1 0-p.val.1 0)) :
      (g x).val.2=(f ⟨p.val,hEA p.property⟩).val.2 := by
    let a : A := ⟨x.val,hCA x.property⟩
    have hDisc : a.val.1 0 ∈ centeredGammaDisc (p.val.1 0)
        (finiteValue ((D.sourceOffset p).val 0) (D.sourceNonzero p)) := (mem_centeredGammaDisc _ _ _).mpr hClose
    exact ((D.mixed_image_iff f E hEA α β p (f a)).mpr ⟨a,hDisc,hpx.symm,rfl⟩).2
  have hTags (x y : C) : (g x).val.2=(g y).val.2 ↔ x.val.2=y.val.2 := by
    obtain ⟨hx,p,hpu,hpClose⟩ := (show x.val ∈ D.sourceCoreSet from hC ▸ x.property)
    obtain ⟨hy,q,hqu,hqClose⟩ := (show y.val ∈ D.sourceCoreSet from hC ▸ y.property)
    have hpx := hLabel x p hpu hpClose
    have hqy := hLabel y q hqu hqClose
    constructor
    · intro he
      have hpq : p=q := hTargetUnique p q (hpx.symm.trans (he.trans hqy))
      exact hpu.symm.trans ((congrArg (fun z : E => z.val.2) hpq).trans hqu)
    · intro he
      have hpq : p=q := hSourceUnique p q (hpu.trans (he.trans hqu.symm))
      exact hpx.trans ((congrArg (fun z : E => (f ⟨z.val,hEA z.property⟩).val.2) hpq).trans hqy.symm)
  exact ⟨g,hBij,mapsWholeTagFibres_of_tag_equivalence g hBij.surjective hTags,
    fun p => ⟨hCA p.property,rfl⟩⟩

end DiamondIntegral.Section6
