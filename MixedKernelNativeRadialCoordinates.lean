import MixedKernelNativeNormalDomain
import MixedKernelNativeEnergyOutside
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError ConformalDepth ActualScalarPrincipalAdjoint
open scoped ContDiff Topology InnerProductSpace

/-- The actual coherent velocity map and its already proved unique inverse form one partial chart. -/
def nativeVelocityPartialHomeomorph
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0 < R) (hRoom : R < C.radiusCeiling) :
    OpenPartialHomeomorph (R3 × R3) (R3 × R3) where
  toFun := nativeVelocityPair S L C lam R
  invFun := nativeVelocityInverse S L C lam R
  source := nativeNormalVelocityRoom S L C R
  target := nativeNormalImage S L C lam R
  map_source' := fun a ha => ⟨a,ha,rfl⟩
  map_target' := fun q hq => (nativeVelocityInverse_mem_right S L C lam R q hq).1
  left_inv' := fun a ha => nativeVelocityInverse_left S L C lam hlam R hR hRoom a ha
  right_inv' := fun q hq => (nativeVelocityInverse_mem_right S L C lam R q hq).2
  open_source := isOpen_nativeNormalVelocityRoom S L C R
  open_target := isOpen_nativeNormalImage S L C lam hlam R hR hRoom
  continuousOn_toFun := (contDiffOn_nativeVelocityPair S L C lam hlam R hR hRoom).continuousOn
  continuousOn_invFun := (contDiffOn_nativeVelocityInverse S L C lam hlam R hR hRoom).continuousOn

/-- Actual polar coordinates, with the radius a REAL coordinate on the open positive half-line. -/
def unitSphereRadialPartialHomeomorph :
    OpenPartialHomeomorph R3 (sphere (0 : R3) 1 × ℝ) := by
  let N : TopologicalSpace.Opens R3 := ⟨{0}ᶜ,isOpen_compl_singleton⟩
  have hN : Nonempty N := by
    refine ⟨⟨EuclideanSpace.single (2 : Fin 3) (1 : ℝ),?_⟩⟩
    change EuclideanSpace.single (2 : Fin 3) (1 : ℝ)≠0
    intro h
    have hh := congrArg (fun v : R3 => v 2) h
    norm_num at hh
  let P : TopologicalSpace.Opens ℝ := ⟨Ioi 0,isOpen_Ioi⟩
  have hP : Nonempty P := ⟨⟨1,by change (0 : ℝ)<1;norm_num⟩⟩
  exact ((N.openPartialHomeomorphSubtypeCoe hN).symm.transHomeomorph
    (homeomorphUnitSphereProd R3)).trans
      ((OpenPartialHomeomorph.refl (sphere (0 : R3) 1)).prod
        (P.openPartialHomeomorphSubtypeCoe hP))

/-- The polar source contains precisely the original nonzero velocities. -/
theorem unitSphereRadialPartialHomeomorph_source :
    unitSphereRadialPartialHomeomorph.source = ({0}ᶜ : Set R3) := by
  simp [unitSphereRadialPartialHomeomorph,OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.prod_source,OpenPartialHomeomorph.prod_target,OpenPartialHomeomorph.transHomeomorph]

/-- Its radius coordinate is the literal original velocity norm. -/
theorem unitSphereRadialPartialHomeomorph_radius (v : R3) (hv : v ≠ 0) :
    (unitSphereRadialPartialHomeomorph v).2 = ‖v‖ := by
  let N : TopologicalSpace.Opens R3 := ⟨{0}ᶜ,isOpen_compl_singleton⟩
  have hN : Nonempty N := ⟨⟨v,by change v≠0;exact hv⟩⟩
  have hInv : (((N.openPartialHomeomorphSubtypeCoe hN).symm v : N) : R3) = v := by
    exact (N.openPartialHomeomorphSubtypeCoe hN).right_inv (by rw [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target];change v≠0;exact hv)
  change ((homeomorphUnitSphereProd R3) ((N.openPartialHomeomorphSubtypeCoe hN).symm v)).2.1 = ‖v‖
  rw [homeomorphUnitSphereProd_apply_snd_coe,hInv]

/-- The actual polar target consists of every unit direction and a strictly positive real radius. -/
theorem unitSphereRadialPartialHomeomorph_target :
    unitSphereRadialPartialHomeomorph.target =
      (univ : Set (sphere (0 : R3) 1)) ×ˢ Ioi (0 : ℝ) := by
  simp [unitSphereRadialPartialHomeomorph,OpenPartialHomeomorph.trans_target,
    OpenPartialHomeomorph.prod_source,OpenPartialHomeomorph.prod_target,OpenPartialHomeomorph.transHomeomorph]

/-- The actual inverse polar map is scalar multiplication, on its genuine positive target. -/
theorem unitSphereRadialPartialHomeomorph_inverse
    (a : sphere (0 : R3) 1 × ℝ) (ha : 0 < a.2) :
    unitSphereRadialPartialHomeomorph.symm a = a.2 • (a.1 : R3) := by
  let P : TopologicalSpace.Opens ℝ := ⟨Ioi 0,isOpen_Ioi⟩
  have hP : Nonempty P := ⟨⟨1,by change (0 : ℝ)<1;norm_num⟩⟩
  have hInv : (((P.openPartialHomeomorphSubtypeCoe hP).symm a.2 : P) : ℝ) = a.2 :=
    (P.openPartialHomeomorphSubtypeCoe hP).right_inv (by rw [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target];change 0<a.2;exact ha)
  change (((homeomorphUnitSphereProd R3).symm
    (a.1,(P.openPartialHomeomorphSubtypeCoe hP).symm a.2) : ({0}ᶜ : Set R3)) : R3) = _
  rw [homeomorphUnitSphereProd_symm_apply_coe,hInv]

/-- Translating the radial height by the SAME original radius is a genuine homeomorphism. -/
def nativeRadiusHeightShift (L delta Rstar : ℝ) (p : ℕ) (hd : 0 < delta) (hRs : 0 < Rstar) :
    ((R3 × sphere (0 : R3) 1) × ℝ) ≃ₜ ((R3 × sphere (0 : R3) 1) × ℝ) where
  toFun a := (a.1,a.2-referenceRadius delta Rstar p L a.1.1)
  invFun a := (a.1,a.2+referenceRadius delta Rstar p L a.1.1)
  left_inv a := by ext <;> simp
  right_inv a := by ext <;> simp
  continuous_toFun := continuous_fst.prodMk (continuous_snd.sub
    ((contDiff_referenceRadius_actual delta Rstar p L hd hRs).continuous.comp continuous_fst.fst))
  continuous_invFun := continuous_fst.prodMk (continuous_snd.add
    ((contDiff_referenceRadius_actual delta Rstar p L hd hRs).continuous.comp continuous_fst.fst))

/-- One actual physical chart has base(center,unit direction) and height |velocity|-ORIGINAL radius. -/
def nativeEnergyRadialChart
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0 < R) (hRoom : R < C.radiusCeiling)
    (delta Rstar : ℝ) (p : ℕ) (hd : 0 < delta) (hRs : 0 < Rstar) :
    OpenPartialHomeomorph (R3 × R3) ((R3 × sphere (0 : R3) 1) × ℝ) :=
  ((nativeVelocityPartialHomeomorph S L C lam hlam R hR hRoom).symm.trans
    ((OpenPartialHomeomorph.refl R3).prod unitSphereRadialPartialHomeomorph)).transHomeomorph
      ((Homeomorph.prodAssoc R3 (sphere (0 : R3) 1) ℝ).symm.trans
        (nativeRadiusHeightShift L delta Rstar p hd hRs))

/-- The physical chart source retains the genuine normal image and excludes exactly zero velocity. -/
theorem nativeEnergyRadialChart_source
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0 < R) (hRoom : R < C.radiusCeiling)
    (delta Rstar : ℝ) (p : ℕ) (hd : 0 < delta) (hRs : 0 < Rstar) :
    (nativeEnergyRadialChart S L C lam hlam R hR hRoom delta Rstar p hd hRs).source =
      nativeNormalImage S L C lam R ∩ {q | (nativeVelocityInverse S L C lam R q).2 ≠ 0} := by
  ext q
  simp [nativeEnergyRadialChart,nativeVelocityPartialHomeomorph,
    unitSphereRadialPartialHomeomorph_source,OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.prod_source,OpenPartialHomeomorph.transHomeomorph]
  change q ∈ nativeNormalImage S L C lam R →
    ((nativeVelocityInverse S L C lam R q).2≠0 ↔ (nativeVelocityInverse S L C lam R q).2≠0)
  intro _
  rfl

/-- The radial height is computed with the actual physical inverse, not a proxy endpoint. -/
theorem nativeEnergyRadialChart_height
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0 < R) (hRoom : R < C.radiusCeiling)
    (delta Rstar : ℝ) (p : ℕ) (hd : 0 < delta) (hRs : 0 < Rstar)
    (q : R3 × R3) (hq : q ∈ nativeNormalImage S L C lam R)
    (hv : (nativeVelocityInverse S L C lam R q).2 ≠ 0) :
    (nativeEnergyRadialChart S L C lam hlam R hR hRoom delta Rstar p hd hRs q).2 =
      ‖(nativeVelocityInverse S L C lam R q).2‖-referenceRadius delta Rstar p L q.2 := by
  change (unitSphereRadialPartialHomeomorph (nativeVelocityInverse S L C lam R q).2).2-
    referenceRadius delta Rstar p L (nativeVelocityInverse S L C lam R q).1 = _
  rw [unitSphereRadialPartialHomeomorph_radius _ hv,nativeVelocityInverse_fst S L C lam R q hq]

/-- The actual radial chart's base center is exactly the physical second coordinate. -/
theorem nativeEnergyRadialChart_center
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0 < R) (hRoom : R < C.radiusCeiling)
    (delta Rstar : ℝ) (p : ℕ) (hd : 0 < delta) (hRs : 0 < Rstar)
    (q : R3 × R3) (hq : q ∈ nativeNormalImage S L C lam R) :
    (nativeEnergyRadialChart S L C lam hlam R hR hRoom delta Rstar p hd hRs q).1.1 = q.2 := by
  change (nativeVelocityInverse S L C lam R q).1 = q.2
  exact nativeVelocityInverse_fst S L C lam R q hq

/-- The physical inverse chart uses the SAME coherent map at its literal translated radial velocity. -/
theorem nativeEnergyRadialChart_inverse
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0 < R) (hRoom : R < C.radiusCeiling)
    (delta Rstar : ℝ) (p : ℕ) (hd : 0 < delta) (hRs : 0 < Rstar)
    (a : (R3 × sphere (0 : R3) 1) × ℝ)
    (ha : 0 < a.2+referenceRadius delta Rstar p L a.1.1) :
    (nativeEnergyRadialChart S L C lam hlam R hR hRoom delta Rstar p hd hRs).symm a =
      nativeVelocityPair S L C lam R
        (a.1.1,(a.2+referenceRadius delta Rstar p L a.1.1) • (a.1.2 : R3)) := by
  change nativeVelocityPair S L C lam R
    (a.1.1,unitSphereRadialPartialHomeomorph.symm
      (a.1.2,a.2+referenceRadius delta Rstar p L a.1.1)) = _
  rw [unitSphereRadialPartialHomeomorph_inverse _ ha]

/-- The target retains the actual center room and BOTH original velocity bounds. -/
theorem nativeEnergyRadialChart_target
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0 < R) (hRoom : R < C.radiusCeiling)
    (delta Rstar : ℝ) (p : ℕ) (hd : 0 < delta) (hRs : 0 < Rstar) :
    (nativeEnergyRadialChart S L C lam hlam R hR hRoom delta Rstar p hd hRs).target =
      {a | a.1.1 ∈ nativeCoverCenterRoom S L C ∧
        0 < a.2+referenceRadius delta Rstar p L a.1.1 ∧
        a.2+referenceRadius delta Rstar p L a.1.1 < R} := by
  ext a
  let t := a.2+referenceRadius delta Rstar p L a.1.1
  have hOmega : ‖(a.1.2 : R3)‖ = 1 := by
    simpa only [mem_sphere,dist_zero_right] using a.1.2.property
  change ((a.1.1 ∈ (univ : Set R3) ∧ (a.1.2,t) ∈ unitSphereRadialPartialHomeomorph.target) ∧
    (a.1.1,unitSphereRadialPartialHomeomorph.symm (a.1.2,t)) ∈ nativeNormalVelocityRoom S L C R) ↔ _
  constructor
  · intro ha
    have ht : 0 < t := by
      have hh := ha.1.2
      rw [unitSphereRadialPartialHomeomorph_target] at hh
      exact hh.2
    have hh := ha.2
    rw [unitSphereRadialPartialHomeomorph_inverse _ ht] at hh
    have hNorm : ‖t • (a.1.2 : R3)‖ = t := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht,hOmega,mul_one]
    exact ⟨hh.1,ht,by simpa only [mem_ball,dist_zero_right,hNorm] using hh.2⟩
  · rintro ⟨hy,ht,htr⟩
    refine ⟨⟨mem_univ _,?_⟩,?_⟩
    · rw [unitSphereRadialPartialHomeomorph_target]
      exact ⟨mem_univ _,ht⟩
    · rw [unitSphereRadialPartialHomeomorph_inverse _ ht]
      refine ⟨hy,?_⟩
      have hNorm : ‖t • (a.1.2 : R3)‖ = t := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht,hOmega,mul_one]
      simpa only [mem_ball,dist_zero_right,hNorm] using htr

/-- On the ACTUAL target, the original physical inverse recovers the literal radial velocity and center. -/
theorem nativeEnergyRadialChart_inverse_data
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0 < R) (hRoom : R < C.radiusCeiling)
    (delta Rstar : ℝ) (p : ℕ) (hd : 0 < delta) (hRs : 0 < Rstar)
    (a : (R3 × sphere (0 : R3) 1) × ℝ)
    (ha : a ∈ (nativeEnergyRadialChart S L C lam hlam R hR hRoom delta Rstar p hd hRs).target) :
    let q := (nativeEnergyRadialChart S L C lam hlam R hR hRoom delta Rstar p hd hRs).symm a
    q.2 = a.1.1 ∧
      ‖(nativeVelocityInverse S L C lam R q).2‖ = a.2+referenceRadius delta Rstar p L a.1.1 := by
  intro q
  rw [nativeEnergyRadialChart_target] at ha
  let t := a.2+referenceRadius delta Rstar p L a.1.1
  have hOmega : ‖(a.1.2 : R3)‖ = 1 := by
    simpa only [mem_sphere,dist_zero_right] using a.1.2.property
  have hNorm : ‖t • (a.1.2 : R3)‖ = t := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos ha.2.1,hOmega,mul_one]
  have hVel : (a.1.1,t • (a.1.2 : R3)) ∈ nativeNormalVelocityRoom S L C R := by
    refine ⟨ha.1,?_⟩
    simpa only [mem_ball,dist_zero_right,hNorm] using ha.2.2
  have hq : q = nativeVelocityPair S L C lam R (a.1.1,t • (a.1.2 : R3)) :=
    nativeEnergyRadialChart_inverse S L C lam hlam R hR hRoom delta Rstar p hd hRs a ha.2.1
  constructor
  · rw [hq]
    rfl
  · rw [hq,nativeVelocityInverse_left S L C lam hlam R hR hRoom _ hVel]
    exact hNorm

/-- The literal global phase and actual chart have EXACTLY the same positive side. -/
theorem nativeGlobalEnergy_pos_iff_nativeEnergyRadialChart_height_pos
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0 < R) (hRoom : R < C.radiusCeiling)
    (delta Rstar : ℝ) (p : ℕ) (hd : 0 < delta) (hRs : 0 < Rstar)
    (q : R3 × R3) (hq : q ∈ nativeNormalImage S L C lam R)
    (hv : (nativeVelocityInverse S L C lam R q).2 ≠ 0) :
    0 < nativeGlobalEnergy S L C lam R delta Rstar p q ↔
      0 < (nativeEnergyRadialChart S L C lam hlam R hR hRoom delta Rstar p hd hRs q).2 := by
  rw [nativeEnergyRadialChart_height S L C lam hlam R hR hRoom delta Rstar p hd hRs q hq hv]
  have hr := referenceRadius_pos delta Rstar p L q.2 hd hRs
  have hn := norm_nonneg (nativeVelocityInverse S L C lam R q).2
  unfold nativeGlobalEnergy
  rw [real_inner_self_eq_norm_sq]
  constructor
  · intro h
    have hs : (referenceRadius delta Rstar p L q.2)^2 < ‖(nativeVelocityInverse S L C lam R q).2‖^2 := by linarith
    have hh := (sq_lt_sq₀ hr.le hn).mp hs
    linarith
  · intro h
    have hh : referenceRadius delta Rstar p L q.2 < ‖(nativeVelocityInverse S L C lam R q).2‖ := by linarith
    have hs := (sq_lt_sq₀ hr.le hn).mpr hh
    linarith

/-- The literal original zero phase is EXACTLY height zero in the same actual chart. -/
theorem nativeGlobalEnergy_eq_zero_iff_nativeEnergyRadialChart_height_eq_zero
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0 < R) (hRoom : R < C.radiusCeiling)
    (delta Rstar : ℝ) (p : ℕ) (hd : 0 < delta) (hRs : 0 < Rstar)
    (q : R3 × R3) (hq : q ∈ nativeNormalImage S L C lam R)
    (hv : (nativeVelocityInverse S L C lam R q).2 ≠ 0) :
    nativeGlobalEnergy S L C lam R delta Rstar p q = 0 ↔
      (nativeEnergyRadialChart S L C lam hlam R hR hRoom delta Rstar p hd hRs q).2 = 0 := by
  rw [nativeEnergyRadialChart_height S L C lam hlam R hR hRoom delta Rstar p hd hRs q hq hv]
  have hr := referenceRadius_pos delta Rstar p L q.2 hd hRs
  have hn := norm_nonneg (nativeVelocityInverse S L C lam R q).2
  unfold nativeGlobalEnergy
  rw [real_inner_self_eq_norm_sq]
  constructor
  · intro h
    have hs : (referenceRadius delta Rstar p L q.2)^2 = ‖(nativeVelocityInverse S L C lam R q).2‖^2 := by linarith
    have hh := (sq_eq_sq₀ hr.le hn).mp hs
    linarith
  · intro h
    have hh : ‖(nativeVelocityInverse S L C lam R q).2‖ = referenceRadius delta Rstar p L q.2 := by linarith
    rw [hh]
    ring

/-- Increasing ACTUAL chart height keeps the center fixed and increases the SAME inverse-velocity norm. -/
theorem nativeEnergyRadialChart_upward_data
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0 < R) (hRoom : R < C.radiusCeiling)
    (delta Rstar : ℝ) (p : ℕ) (hd : 0 < delta) (hRs : 0 < Rstar) :
    let e := nativeEnergyRadialChart S L C lam hlam R hR hRoom delta Rstar p hd hRs
    ∀ q ∈ e.source, ∀ t : ℝ, (e q).2 ≤ t → ((e q).1,t) ∈ e.target →
      let q' := e.symm ((e q).1,t)
      q'.2 = q.2 ∧
        ‖(nativeVelocityInverse S L C lam R q).2‖ ≤ ‖(nativeVelocityInverse S L C lam R q').2‖ ∧
        q' ∈ e.source := by
  intro e q hq t hle ht q'
  have hSource := hq
  rw [nativeEnergyRadialChart_source] at hSource
  have hBase := nativeEnergyRadialChart_center S L C lam hlam R hR hRoom delta Rstar p hd hRs q hSource.1
  have hHeight := nativeEnergyRadialChart_height S L C lam hlam R hR hRoom delta Rstar p hd hRs q hSource.1 hSource.2
  have hData := nativeEnergyRadialChart_inverse_data S L C lam hlam R hR hRoom delta Rstar p hd hRs ((e q).1,t) ht
  change q'.2 = (e q).1.1 ∧
    ‖(nativeVelocityInverse S L C lam R q').2‖ = t+referenceRadius delta Rstar p L (e q).1.1 at hData
  have hNewNorm : ‖(nativeVelocityInverse S L C lam R q').2‖ =
      t+referenceRadius delta Rstar p L q.2 := by rw [hData.2,hBase]
  refine ⟨hData.1.trans hBase,?_,e.map_target ht⟩
  linarith only [hHeight,hNewNorm,hle]

/-- The literal original outside domain is upward in the SAME actual native chart; no monotonicity premise. -/
theorem nativeRadialOutsideRoom_upward_in_nativeEnergyRadialChart
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0 < R) (hRoom : R < C.radiusCeiling)
    (delta oldDelta Rstar : ℝ) (p : ℕ) (hd : 0 < delta) (hold : 0 < oldDelta) (hRs : 0 < Rstar) :
    let e := nativeEnergyRadialChart S L C lam hlam R hR hRoom delta Rstar p hd hRs
    ∀ q ∈ nativeRadialOutsideRoom S L C lam R oldDelta Rstar p ∩ e.source,
      ∀ t : ℝ, (e q).2 ≤ t → ((e q).1,t) ∈ e.target →
        e.symm ((e q).1,t) ∈ nativeRadialOutsideRoom S L C lam R oldDelta Rstar p := by
  intro e q hq t hle ht
  let q' := e.symm ((e q).1,t)
  obtain ⟨hy,hNorm,hSource⟩ := nativeEnergyRadialChart_upward_data S L C lam hlam R hR hRoom delta Rstar p hd hRs q hq.2 t hle ht
  rw [nativeEnergyRadialChart_source] at hSource
  have hOld := hq.1
  rw [nativeRadialOutsideRoom_eq_positive_nativeGlobalEnergy S L C lam hlam R hR hRoom oldDelta Rstar hold hRs p] at hOld ⊢
  have hr := referenceRadius_pos oldDelta Rstar p L q.2 hold hRs
  have hOldEnergy := hOld.2.2
  unfold nativeGlobalEnergy at hOldEnergy
  rw [real_inner_self_eq_norm_sq] at hOldEnergy
  have hSq : (referenceRadius oldDelta Rstar p L q.2)^2 < ‖(nativeVelocityInverse S L C lam R q).2‖^2 := by linarith
  have hLow := (sq_lt_sq₀ hr.le (norm_nonneg _)).mp hSq
  have hNewLow : referenceRadius oldDelta Rstar p L q'.2 < ‖(nativeVelocityInverse S L C lam R q').2‖ := by
    rw [hy]
    exact hLow.trans_le hNorm
  refine ⟨hSource.1,by rw [hy];exact hOld.2.1,?_⟩
  have hs := (sq_lt_sq₀ (referenceRadius_pos oldDelta Rstar p L q'.2 hold hRs).le (norm_nonneg _)).mpr hNewLow
  unfold nativeGlobalEnergy
  rw [real_inner_self_eq_norm_sq]
  linarith

/-- A delta-independent genuine radial seed: fixed ORIGINAL known center side or fixed velocity tail. -/
def nativeRadialSeedRoom (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam R tail : ℝ) : Set (R3 × R3) :=
  {q | q ∈ nativeNormalImage S L C lam R ∧ (nativeVelocityInverse S L C lam R q).2 ≠ 0 ∧
    (lam • q.2 ∈ S.W ∨ tail < ‖(nativeVelocityInverse S L C lam R q).2‖)}

/-- The retained actual radial seed is open, via the exact original open velocity image. -/
theorem isOpen_nativeRadialSeedRoom
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0 < R) (hRoom : R < C.radiusCeiling) (tail : ℝ) :
    IsOpen (nativeRadialSeedRoom S L C lam R tail) := by
  let A : Set (R3 × R3) := {a | a ∈ nativeNormalVelocityRoom S L C R ∧ a.2 ≠ 0 ∧
    (lam • a.1 ∈ S.W ∨ tail < ‖a.2‖)}
  have hA : IsOpen A := (isOpen_nativeNormalVelocityRoom S L C R).inter
    ((isOpen_ne_fun continuous_snd continuous_const).inter
      ((S.W_open.preimage ((continuous_const_smul lam).comp continuous_fst)).union
        (isOpen_lt continuous_const continuous_snd.norm)))
  have hImage : nativeRadialSeedRoom S L C lam R tail = nativeVelocityPair S L C lam R '' A := by
    ext q
    constructor
    · intro hq
      let a := nativeVelocityInverse S L C lam R q
      obtain ⟨ha,hRight⟩ := nativeVelocityInverse_mem_right S L C lam R q hq.1
      refine ⟨a,⟨ha,hq.2.1,?_⟩,hRight⟩
      rcases hq.2.2 with hW | hTail
      · left
        have hy := nativeVelocityInverse_fst S L C lam R q hq.1
        change lam • (nativeVelocityInverse S L C lam R q).1 ∈ S.W
        rw [hy]
        exact hW
      · exact Or.inr hTail
    · rintro ⟨a,ha,rfl⟩
      have hInv := nativeVelocityInverse_left S L C lam hlam R hR hRoom a ha.1
      refine ⟨⟨a,ha.1,rfl⟩,?_,?_⟩
      · simpa only [hInv] using ha.2.1
      · rcases ha.2.2 with hW | hTail
        · exact Or.inl hW
        · exact Or.inr (by simpa only [hInv] using hTail)
  rw [hImage]
  exact isOpen_nativeVelocityPair_image S L C lam hlam R hR hRoom A hA (fun a ha => ha.1)

/-- The actual retained seed has the upward property needed by common-chart gluing. -/
theorem nativeRadialSeedRoom_upward_in_nativeEnergyRadialChart
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0 < R) (hRoom : R < C.radiusCeiling)
    (delta Rstar tail : ℝ) (p : ℕ) (hd : 0 < delta) (hRs : 0 < Rstar) :
    let e := nativeEnergyRadialChart S L C lam hlam R hR hRoom delta Rstar p hd hRs
    ∀ q ∈ nativeRadialSeedRoom S L C lam R tail ∩ e.source,
      ∀ t : ℝ, (e q).2 ≤ t → ((e q).1,t) ∈ e.target →
        e.symm ((e q).1,t) ∈ nativeRadialSeedRoom S L C lam R tail := by
  intro e q hq t hle ht
  obtain ⟨hy,hNorm,hSource⟩ := nativeEnergyRadialChart_upward_data S L C lam hlam R hR hRoom delta Rstar p hd hRs q hq.2 t hle ht
  rw [nativeEnergyRadialChart_source] at hSource
  refine ⟨hSource.1,hSource.2,?_⟩
  rcases hq.1.2.2 with hW | hTail
  · left
    rw [hy]
    exact hW
  · exact Or.inr (hTail.trans_le hNorm)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
