import Calderon.ActualMixedKernelConstruction
import Mathlib.Geometry.Manifold.PartitionOfUnity

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter Function
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
open SphereHarmonic ReferenceWeightedApproximation ActualScalarPrincipalAdjoint
  ConnectionError ConformalDepth

private theorem exists_open_native_surface_homotopy_room
    (X : (R3 × ℝ) × R3 → R3) (hX : Continuous X)
    (R : R3 → ℝ) (hR : Continuous R) (U : Set (R3 × R3))
    (hU : IsOpen U) (y : R3)
    (hCover : ∀ z ∈ sphere (0 : R3) 1, (X ((y,R y),z),y) ∈ U) :
    ∃ Y : Set R3, IsOpen Y ∧ y ∈ Y ∧
      ∀ y' ∈ Y, ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ sphere (0 : R3) 1,
        (X (((1-t) • y+t • y',(1-t)*R y+t*R y'),z),y') ∈ U := by
  let c : R3 × (ℝ × R3) → R3 := fun p => (1-p.2.1) • y+p.2.1 • p.1
  let r : R3 × (ℝ × R3) → ℝ := fun p => (1-p.2.1)*R y+p.2.1*R p.1
  let Q : R3 × (ℝ × R3) → R3 × R3 := fun p => (X ((c p,r p),p.2.2),p.1)
  have hc : Continuous c :=
    ((continuous_const.sub continuous_snd.fst).smul continuous_const).add
      (continuous_snd.fst.smul continuous_fst)
  have hr : Continuous r :=
    ((continuous_const.sub continuous_snd.fst).mul continuous_const).add
      (continuous_snd.fst.mul (hR.comp continuous_fst))
  have hQ : Continuous Q :=
    (hX.comp ((hc.prodMk hr).prodMk continuous_snd.snd)).prodMk continuous_fst
  have hCompact : IsCompact ((Icc (0 : ℝ) 1) ×ˢ sphere (0 : R3) 1) :=
    isCompact_Icc.prod (isCompact_sphere (0 : R3) 1)
  have hNear : ∀ᶠ y' in 𝓝 y, ∀ tz ∈ ((Icc (0 : ℝ) 1) ×ˢ sphere (0 : R3) 1),
      Q (y',tz) ∈ U := by
    apply hCompact.eventually_forall_of_forall_eventually
    intro tz htz
    apply hQ.continuousAt.eventually (hU.mem_nhds ?_)
    have hc0 : c (y,tz) = y := by
      dsimp [c]
      rw [← add_smul]
      simp
    have hr0 : r (y,tz) = R y := by
      dsimp [r]
      rw [← add_mul]
      simp
    simpa only [Q,hc0,hr0] using hCover tz.2 htz.2
  obtain ⟨Y,hYsub,hYopen,hyY⟩ := _root_.mem_nhds_iff.mp hNear
  refine ⟨Y,hYopen,hyY,?_⟩
  intro y' hy' t ht z hz
  exact hYsub hy' (t,z) ⟨ht,hz⟩

theorem exists_open_mixed_kernel_native_surface_homotopy_room
    (S : KnownSideSourceData) (L lam delta Rstar bound separation : ℝ) (p : ℕ)
    (cover : NativeNormalCover S L)
    (K : ConstructedMixedKernel S L lam delta Rstar bound separation p cover)
    (hdelta : 0 < delta) (hRstar : 0 < Rstar)
    (i : Fin cover.count) (y : R3) (hy : y ∈ cylinder ∩ (cover.packet i).centers) :
    ∃ Y : Set R3, IsOpen Y ∧ y ∈ Y ∧
      ∀ y' ∈ Y, ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ sphere (0 : R3) 1,
        (packetEndpoint S L (cover.packet i) lam
          ((1-t) • y+t • y')
          ((1-t)*referenceRadius delta Rstar p L y+t*referenceRadius delta Rstar p L y') z,
          y') ∈ K.domain := by
  let P := cover.packet i
  let X : (R3 × ℝ) × R3 → R3 := fun pz =>
    referenceFramedPhysicalEndpoint S.g1 L P.Phi (lam,pz)
  have hTheta : ContDiff ℝ ∞
      (fun v : ℝ × (R3 × R3) => (P.Phi v.1 v.2 1).1) :=
    P.native_data.1.1.1.2.2.2.2.2.2.2.1
  have hX : Continuous X :=
    ((contDiff_referenceFramedPhysicalEndpoint S.g1 S.g1_admissible L P.Phi hTheta).comp
      (contDiff_const.prodMk contDiff_id)).continuous
  exact exists_open_native_surface_homotopy_room X hX
    (referenceRadius delta Rstar p L)
    (contDiff_referenceRadius_actual delta Rstar p L hdelta hRstar).continuous
    K.domain K.domain_open y (K.sphere_cover i y hy)


private theorem exists_smooth_product_extension_eq_near_compact
    (K U : Set (R3 × R3)) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (u : R3 × R3 → ℝ) (hu : ContDiffOn ℝ ∞ u U) :
    ∃ v : R3 × R3 → ℝ, ContDiff ℝ ∞ v ∧ HasCompactSupport v ∧
      ∀ x ∈ K, v =ᶠ[𝓝 x] u := by
  obtain ⟨W,hW,hKW,hWcompact⟩ := exists_isOpen_superset_and_isCompact_closure hK
  have hKUW : K ⊆ U ∩ W := fun x hx => ⟨hKU hx,hKW hx⟩
  obtain ⟨A,hA,hKA,hAclosure⟩ :=
    hK.exists_isOpen_closure_subset ((hU.inter hW).mem_nhdsSet.mpr hKUW)
  have hAcompact : IsCompact (closure A) :=
    hWcompact.of_isClosed_subset isClosed_closure
      (fun x hx => subset_closure (hAclosure hx).2)
  obtain ⟨B,hB,hKB,hBclosure⟩ :=
    hK.exists_isOpen_closure_subset (hA.mem_nhdsSet.mpr hKA)
  obtain ⟨χ,hχ,_,hSupport,hOne⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hA isClosed_closure hBclosure
  have hSmooth : ContDiff ℝ ∞ (fun x => χ x*u x) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ U
    · exact hχ.contDiffAt.mul (hu.contDiffAt (hU.mem_nhds hx))
    · have hxOutside : x ∈ (closure A)ᶜ := fun hxA => hx (hAclosure hxA).1
      have hZero : (fun y => χ y*u y) =ᶠ[𝓝 x] (fun _ : R3 × R3 => (0 : ℝ)) := by
        filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hxOutside] with y hy
        have hχZero : χ y = 0 := by
          apply notMem_support.mp
          rw [hSupport]
          exact fun hyA => hy (subset_closure hyA)
        simp only [hχZero,zero_mul]
      exact (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : R3 × R3 => (0 : ℝ)) x).congr_of_eventuallyEq hZero
  have hχCompact : HasCompactSupport χ := by
    change IsCompact (closure (Function.support χ))
    rw [hSupport]
    exact hAcompact
  refine ⟨fun x => χ x*u x,hSmooth,hχCompact.mul_right,?_⟩
  intro x hx
  filter_upwards [hB.mem_nhds (hKB hx)] with y hy
  have hχOne : χ y = 1 := (hOne y).mp (subset_closure hy)
  simp only [hχOne,one_mul]

theorem exists_smooth_mixed_kernel_eq_near_native_surface_homotopy
    (S : KnownSideSourceData) (L lam delta Rstar bound separation : ℝ) (p : ℕ)
    (cover : NativeNormalCover S L)
    (K : ConstructedMixedKernel S L lam delta Rstar bound separation p cover)
    (hdelta : 0 < delta) (hRstar : 0 < Rstar)
    (i : Fin cover.count) (y : R3) (hy : y ∈ cylinder ∩ (cover.packet i).centers) :
    ∃ (Gext : R3 × R3 → ℝ) (Y : Set R3),
      ContDiff ℝ ∞ Gext ∧ HasCompactSupport Gext ∧ IsOpen Y ∧ y ∈ Y ∧
      ∀ y' ∈ Y, ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ sphere (0 : R3) 1,
        (packetEndpoint S L (cover.packet i) lam
          ((1-t) • y+t • y')
          ((1-t)*referenceRadius delta Rstar p L y+t*referenceRadius delta Rstar p L y') z,
          y') ∈ K.domain ∧
        Gext =ᶠ[𝓝 (packetEndpoint S L (cover.packet i) lam
          ((1-t) • y+t • y')
          ((1-t)*referenceRadius delta Rstar p L y+t*referenceRadius delta Rstar p L y') z,
          y')] K.kernel := by
  let P := cover.packet i
  let X : (R3 × ℝ) × R3 → R3 := fun pz =>
    referenceFramedPhysicalEndpoint S.g1 L P.Phi (lam,pz)
  have hTheta : ContDiff ℝ ∞
      (fun v : ℝ × (R3 × R3) => (P.Phi v.1 v.2 1).1) :=
    P.native_data.1.1.1.2.2.2.2.2.2.2.1
  have hX : Continuous X :=
    ((contDiff_referenceFramedPhysicalEndpoint S.g1 S.g1_admissible L P.Phi hTheta).comp
      (contDiff_const.prodMk contDiff_id)).continuous
  let R := referenceRadius delta Rstar p L
  let K0 : Set (R3 × R3) := (fun z => (X ((y,R y),z),y)) '' sphere (0 : R3) 1
  have hK0 : IsCompact K0 :=
    (isCompact_sphere (0 : R3) 1).image
      ((hX.comp (continuous_const.prodMk continuous_id)).prodMk continuous_const)
  have hK0domain : K0 ⊆ K.domain := by
    rintro a ⟨z,hz,rfl⟩
    exact K.sphere_cover i y hy z hz
  obtain ⟨Gext,hGext,hCompact,hEq⟩ := exists_smooth_product_extension_eq_near_compact
    K0 K.domain hK0 K.domain_open hK0domain K.kernel K.product_solution.1
  let A : Set (R3 × R3) := K.domain ∩ interior {v | Gext v = K.kernel v}
  have hA : IsOpen A := K.domain_open.inter isOpen_interior
  have hBase : ∀ z ∈ sphere (0 : R3) 1, (X ((y,R y),z),y) ∈ A := by
    intro z hz
    have hk : (X ((y,R y),z),y) ∈ K0 := ⟨z,hz,rfl⟩
    exact ⟨hK0domain hk,mem_interior_iff_mem_nhds.mpr (hEq _ hk)⟩
  obtain ⟨Y,hY,hyY,hRoom⟩ := exists_open_native_surface_homotopy_room X hX R
    (contDiff_referenceRadius_actual delta Rstar p L hdelta hRstar).continuous A hA y hBase
  refine ⟨Gext,Y,hGext,hCompact,hY,hyY,?_⟩
  intro y' hy' t ht z hz
  have ha := hRoom y' hy' t ht z hz
  exact ⟨ha.1,mem_interior_iff_mem_nhds.mp ha.2⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
