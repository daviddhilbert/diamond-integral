import «section 3».GammaGroundFamilySelectedMaps
import «section 3».GammaGroundMapFiniteGluing
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}
variable {P Q : Space LRV M}

/-- Bijections between corresponding pieces of two finite family
partitions glue to an actual same-ground family bijection. -/
theorem gammaGroundFamilyBijection_of_partitions
    (A : GammaGroundFiniteFamily hc B P) (D : GammaGroundFiniteFamily hc B Q)
    (R : Fin A.tags → Fin D.tags → GammaGroundDefSet hc B P)
    (S : Fin A.tags → Fin D.tags → GammaGroundDefSet hc B Q)
    (hR : ∀ i j, (R i j).carrier ⊆ (A.piece i).carrier)
    (hS : ∀ i j, (S i j).carrier ⊆ (D.piece j).carrier)
    (hRc : ∀ i (a : A.piece i), ∃! j, a.val ∈ (R i j).carrier)
    (hSc : ∀ j (b : D.piece j), ∃! i, b.val ∈ (S i j).carrier)
    (L : ∀ i j, GammaGroundBijection (R i j) (S i j)) :
    ∃ F : GammaGroundFamilyBijection A D,
      ∀ i j (a : A.piece i) (ha : a.val ∈ (R i j).carrier),
        (F.equiv ⟨i,a⟩).1 = j ∧ (F.equiv ⟨i,a⟩).2.val = ((L i j).map ⟨a.val,ha⟩).val := by
  have hex (i : Fin A.tags) := gammaGroundMap_of_finite_partition (A.piece i)
    (GammaGroundDefSet.univ hc B Q) (R i) (hR i) (hRc i) (fun j => (L i j).map.toUniv)
  choose f hf using hex
  have hrange : ∀ i j (a : A.piece i), a.val ∈ (R i j).carrier → (f i a).val ∈ (D.piece j).carrier := by
    intro i j a ha
    rw [hf i j a ha]
    exact hS i j ((L i j).map ⟨a.val,ha⟩).property
  obtain ⟨F,hTag,hValue⟩ := gammaGroundFamilyMap_of_selected_values A D R hRc f hrange
  have hpoint (i : Fin A.tags) (j : Fin D.tags) (a : A.piece i) (ha : a.val ∈ (R i j).carrier) :
      (F.toFun ⟨i,a⟩).1 = j ∧ (F.toFun ⟨i,a⟩).2.val = ((L i j).map ⟨a.val,ha⟩).val := by
    refine ⟨(hTag i a j).mpr ha,?_⟩
    exact (hValue i a).trans (congrArg Subtype.val (hf i j a ha))
  have hin : Function.Injective F.toFun := by
    rintro ⟨i,a⟩ ⟨k,b⟩ he
    let j := (F.toFun ⟨i,a⟩).1
    have ha : a.val ∈ (R i j).carrier := (hTag i a j).mp rfl
    have hb : b.val ∈ (R k j).carrier := (hTag k b j).mp (congrArg Sigma.fst he.symm)
    have has : (F.toFun ⟨i,a⟩).2.val ∈ (S i j).carrier := by
      rw [(hpoint i j a ha).2]
      exact ((L i j).map ⟨a.val,ha⟩).property
    have hbs : (F.toFun ⟨i,a⟩).2.val ∈ (S k j).carrier := by
      rw [congrArg (fun t : D.Carrier => t.2.val) he,(hpoint k j b hb).2]
      exact ((L k j).map ⟨b.val,hb⟩).property
    have hik : i = k := (hSc j (F.toFun ⟨i,a⟩).2).unique has hbs
    subst k
    have hv : ((L i j).map ⟨a.val,ha⟩).val = ((L i j).map ⟨b.val,hb⟩).val :=
      (hpoint i j a ha).2.symm.trans
        ((congrArg (fun t : D.Carrier => t.2.val) he).trans (hpoint i j b hb).2)
    have hab := (L i j).bijective.1 (Subtype.ext hv)
    have hvab : a.val = b.val := congrArg (fun t : R i j => t.val) hab
    exact congrArg (Sigma.mk i) (Subtype.ext hvab)
  have hsur : Function.Surjective F.toFun := by
    rintro ⟨j,b⟩
    obtain ⟨i,hi,_⟩ := hSc j b
    obtain ⟨u,hu⟩ := (L i j).bijective.2 ⟨b.val,hi⟩
    let a : A.piece i := ⟨u.val,hR i j u.property⟩
    refine ⟨⟨i,a⟩,?_⟩
    apply gammaGroundFamilyCarrier_ext D (hpoint i j a u.property).1
    exact (hpoint i j a u.property).2.trans (congrArg Subtype.val hu)
  let E : A.Carrier ≃ D.Carrier := Equiv.ofBijective F.toFun ⟨hin,hsur⟩
  exact ⟨⟨E,F.definable⟩,hpoint⟩

end DiamondIntegral.Section3
