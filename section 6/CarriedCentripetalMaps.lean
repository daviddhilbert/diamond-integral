import «section 6».CarriedCentripetalData

/-! The carried permitted component is the actual lower-dimensional
map with the released coordinate unchanged. Its whole image is exactly
the bundle over the lower-dimensional image, with the old tag retained. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.CentripetalData

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

theorem carryCoordinate_extendedFocus (D : CentripetalData (G := G) A) (k : Fin r)
    (hW : ProperInvariant S (rvCoordinateBundle A k).carrier)
    (p : Mixed M (n+1) r) (hp : p ∈ (rvCoordinateBundle A k).carrier) :
    (D.carryCoordinate k hW).extendedFocus p = D.extendedFocus (Fin.init p.1,p.2) := by
  by_cases hu : p.2 ∈ D.activeTags.carrier
  · rw [(D.carryCoordinate k hW).extendedFocus_active hp hu,D.extendedFocus_active hp.1 hu]
    change D.focus (Fin.init (Function.update p.1 D.coordinate.castSucc 0)) p.2 =
      D.focus (Function.update (Fin.init p.1) D.coordinate 0) p.2
    rw [init_update_castSucc]
  · rw [(D.carryCoordinate k hW).extendedFocus_inactive hu,D.extendedFocus_inactive hu]

theorem carryCoordinate_core (D : CentripetalData (G := G) A) (k : Fin r)
    (hW : ProperInvariant S (rvCoordinateBundle A k).carrier)
    (p : Mixed M (n+1) r) (hp : p ∈ (rvCoordinateBundle A k).carrier) :
    (D.carryCoordinate k hW).core p = D.core (Fin.init p.1,p.2) := by
  change decide (vfValue (D.coefficient * (D.carryCoordinate k hW).extendedFocus p) <
      vfValue (p.1 D.coordinate.castSucc - (D.carryCoordinate k hW).extendedFocus p)) = _
  rw [D.carryCoordinate_extendedFocus k hW p hp]
  rfl

theorem carryCoordinate_point (D : CentripetalData (G := G) A) (k : Fin r)
    (hW : ProperInvariant S (rvCoordinateBundle A k).carrier)
    (p : Mixed M (n+1) r) (hp : p ∈ (rvCoordinateBundle A k).carrier) :
    (D.carryCoordinate k hW).point p =
      (Fin.snoc (D.point (Fin.init p.1,p.2)).1 (p.1 (Fin.last n)),(D.point (Fin.init p.1,p.2)).2) := by
  let E := D.carryCoordinate k hW
  have hFocus := D.carryCoordinate_extendedFocus k hW p hp
  have hCore := D.carryCoordinate_core k hW p hp
  have hInit : Fin.init (E.point p).1 = (D.point (Fin.init p.1,p.2)).1 := by
    change Fin.init (Function.update p.1 D.coordinate.castSucc
      (p.1 D.coordinate.castSucc - E.extendedFocus p +
        if E.core p then D.coefficient * E.extendedFocus p else 0)) = _
    rw [init_update_castSucc,hFocus,hCore]
    rfl
  have hLast : (E.point p).1 (Fin.last n) = p.1 (Fin.last n) := by
    change Function.update p.1 D.coordinate.castSucc _ (Fin.last n) = p.1 (Fin.last n)
    exact Function.update_of_ne (Ne.symm (Fin.castSucc_ne_last D.coordinate)) _ _
  apply Prod.ext
  · calc
      (E.point p).1 = Fin.snoc (Fin.init (E.point p).1) ((E.point p).1 (Fin.last n)) :=
        (Fin.snoc_init_self _).symm
      _ = _ := by rw [hInit,hLast]
  · change Fin.append (fun _ : Fin 1 => branchTag (M := M) (E.core p)) p.2 =
      Fin.append (fun _ : Fin 1 => branchTag (M := M) (D.core (Fin.init p.1,p.2))) p.2
    rw [hCore]

theorem carryCoordinate_image (D : CentripetalData (G := G) A) (k : Fin r)
    (hW : ProperInvariant S (rvCoordinateBundle A k).carrier) :
    (D.carryCoordinate k hW).map.image.carrier =
      (rvCoordinateBundle D.map.image (Fin.natAdd 1 k)).carrier := by
  rw [(D.carryCoordinate k hW).image_carrier]
  ext q
  constructor
  · rintro ⟨p,hp,rfl⟩
    rw [D.carryCoordinate_point k hW p hp]
    refine ⟨?_,?_⟩
    · change ((Fin.init (Fin.snoc (D.point (Fin.init p.1,p.2)).1 (p.1 (Fin.last n)) :
          Fin (n+1) → VF M), (D.point (Fin.init p.1,p.2)).2) : Mixed M n (1+r)) ∈ D.map.image.carrier
      rw [Fin.init_snoc]
      rw [D.image_carrier]
      exact ⟨(Fin.init p.1,p.2),hp.1,rfl⟩
    · simpa only [Fin.snoc_last,point,Fin.append_right] using hp.2
  · intro hq
    obtain ⟨a,ha,hDa⟩ := (show (Fin.init q.1,q.2) ∈ D.point '' A.carrier by
      rw [← D.image_carrier]
      exact hq.1)
    let p : Mixed M (n+1) r := (Fin.snoc a.1 (q.1 (Fin.last n)),a.2)
    have hbase : ((Fin.init p.1,p.2) : Mixed M n r) = a := by
      apply Prod.ext
      · simp only [p,Fin.init_snoc]
      · rfl
    have hOld : q.2 (Fin.natAdd 1 k) = a.2 k := by
      have h := congrArg (fun z : Mixed M n (1+r) => z.2 (Fin.natAdd 1 k)) hDa
      simpa only [point,Fin.append_right] using h.symm
    have hp : p ∈ (rvCoordinateBundle A k).carrier := by
      refine ⟨hbase.symm ▸ ha,?_⟩
      simpa only [p,Fin.snoc_last] using hq.2.trans hOld
    refine ⟨p,hp,?_⟩
    rw [D.carryCoordinate_point k hW p hp,hbase,hDa]
    have hLast : p.1 (Fin.last n) = q.1 (Fin.last n) := by simp only [p,Fin.snoc_last]
    rw [hLast]
    change (Fin.snoc (Fin.init q.1) (q.1 (Fin.last n)),q.2) = q
    rw [Fin.snoc_init_self]

end DiamondIntegral.Section6.CentripetalData
