import Calderon.ActualMixedKernelSurfaceHomotopyRoom
import Calderon.ReferenceRadiusScaling

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter Function
open scoped ContDiff Topology

namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
open SphereHarmonic ReferenceWeightedApproximation ActualScalarPrincipalAdjoint
  ConnectionError ConformalDepth

theorem isCompact_native_center_cylinder : IsCompact cylinder := by
  have hc (i : Fin 3) : Continuous (fun y : R3 => y i) :=
    PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i
  have hclosed : IsClosed cylinder :=
    (isClosed_le (((hc 0).pow 2).add ((hc 1).pow 2)) continuous_const).inter
      ((isClosed_le continuous_const (hc 2)).inter
        (isClosed_le (hc 2) continuous_const))
  apply (isCompact_closedBall (0 : R3) 2).of_isClosed_subset hclosed
  intro y hy
  rw [mem_closedBall_zero_iff]
  have hsq2 : (y 2)^2 ≤ (1 : ℝ) := by
    have hp : 0 ≤ (1-y 2)*(1+y 2) :=
      mul_nonneg (sub_nonneg.mpr hy.2.2) (by linarith [hy.2.1])
    nlinarith
  have hn := EuclideanSpace.real_norm_sq_eq y
  simp only [Fin.sum_univ_three] at hn
  nlinarith [hy.1, norm_nonneg y]

/-- The entire native unit-sphere family over the exact compact cylinder.
Its description includes every packet, but its compactness uses coherence
rather than incorrectly treating open packet patches as compact. -/
def nativeMixedKernelSurface
    (S : KnownSideSourceData) (L lam delta Rstar : ℝ) (p : ℕ)
    (cover : NativeNormalCover S L) : Set (R3 × R3) :=
  {v | ∃ i : Fin cover.count, ∃ y : R3,
    y ∈ cylinder ∩ (cover.packet i).centers ∧
      ∃ z ∈ sphere (0 : R3) 1,
        v = (packetEndpoint S L (cover.packet i) lam y
          (referenceRadius delta Rstar p L y) z,y)}

theorem isCompact_nativeMixedKernelSurface
    (S : KnownSideSourceData) (L lam delta Rstar : ℝ) (p : ℕ)
    (cover : NativeNormalCover S L)
    (hdelta : 0 < delta) (hRstar : 0 < Rstar)
    (hLam : lam ∈ Icc (0 : ℝ) cover.dilationCeiling)
    (hRadius : ∀ y ∈ cylinder,
      referenceRadius delta Rstar p L y < cover.radiusCeiling) :
    IsCompact (nativeMixedKernelSurface S L lam delta Rstar p cover) := by
  classical
  let choosePacket : ↥cylinder → Fin cover.count := fun y =>
    Classical.choose (cover.covers_cylinder y y.property)
  have hChoose (y : ↥cylinder) :
      (y : R3) ∈ (cover.packet (choosePacket y)).centers :=
    Classical.choose_spec (cover.covers_cylinder y y.property)
  let R := referenceRadius delta Rstar p L
  have hR : Continuous R :=
    (contDiff_referenceRadius_actual delta Rstar p L hdelta hRstar).continuous
  have hRpos (y : R3) : 0 < R y :=
    referenceRadius_pos delta Rstar p L y hdelta hRstar
  have hSphere (z : ↥(sphere (0 : R3) 1)) :
      (z : R3) ∈ closedBall (0 : R3) 2 := by
    have hz : ‖(z : R3)‖ = 1 := by
      simpa only [mem_sphere_zero_iff_norm] using z.property
    rw [mem_closedBall_zero_iff, hz]
    norm_num
  let F : ↥cylinder × ↥(sphere (0 : R3) 1) → R3 × R3 := fun yz =>
    (packetEndpoint S L (cover.packet (choosePacket yz.1)) lam
      yz.1 (R yz.1) yz.2,yz.1)
  have hPacket (i : Fin cover.count) : Continuous
      (fun yz : ↥cylinder × ↥(sphere (0 : R3) 1) =>
        (packetEndpoint S L (cover.packet i) lam yz.1 (R yz.1) yz.2,
          (yz.1 : R3))) := by
    let P := cover.packet i
    have hTheta : ContDiff ℝ ∞
        (fun v : ℝ × (R3 × R3) => (P.Phi v.1 v.2 1).1) :=
      P.native_data.1.1.1.2.2.2.2.2.2.2.1
    have hX :=
      (contDiff_referenceFramedPhysicalEndpoint S.g1 S.g1_admissible L P.Phi
        hTheta).continuous
    have hy : Continuous (fun yz : ↥cylinder × ↥(sphere (0 : R3) 1) =>
        (yz.1 : R3)) := continuous_subtype_val.comp continuous_fst
    have hz : Continuous (fun yz : ↥cylinder × ↥(sphere (0 : R3) 1) =>
        (yz.2 : R3)) := continuous_subtype_val.comp continuous_snd
    exact (hX.comp (continuous_const.prodMk
      ((hy.prodMk (hR.comp hy)).prodMk hz))).prodMk hy
  have hF : Continuous F := by
    rw [continuous_iff_continuousAt]
    intro yz
    let i := choosePacket yz.1
    have hNear : ∀ᶠ yz' : ↥cylinder × ↥(sphere (0 : R3) 1) in 𝓝 yz,
        (yz'.1 : R3) ∈ (cover.packet i).centers :=
      ((cover.packet i).centers_open.preimage
        (continuous_subtype_val.comp continuous_fst)).mem_nhds (hChoose yz.1)
    apply (hPacket i).continuousAt.congr_of_eventuallyEq
    filter_upwards [hNear] with yz' hy'
    change (packetEndpoint S L (cover.packet (choosePacket yz'.1)) lam
      yz'.1 (R yz'.1) yz'.2,(yz'.1 : R3)) = _
    exact Prod.ext
      (cover.endpoint_coherence (choosePacket yz'.1) i lam hLam yz'.1
        ⟨hChoose yz'.1,hy'⟩ (R yz'.1) (hRpos yz'.1)
        (hRadius yz'.1 yz'.1.property) yz'.2 (hSphere yz'.2)) rfl
  letI : CompactSpace ↥cylinder := isCompact_iff_compactSpace.mp
    isCompact_native_center_cylinder
  letI : CompactSpace ↥(sphere (0 : R3) 1) := isCompact_iff_compactSpace.mp
    (isCompact_sphere (0 : R3) 1)
  have hCompact : IsCompact (Set.range F) := isCompact_range hF
  have hRange : Set.range F = nativeMixedKernelSurface S L lam delta Rstar p cover := by
    ext v
    constructor
    · rintro ⟨yz,rfl⟩
      exact ⟨choosePacket yz.1,yz.1,⟨yz.1.property,hChoose yz.1⟩,
        yz.2,yz.2.property,rfl⟩
    · rintro ⟨i,y,hy,z,hz,rfl⟩
      refine ⟨(⟨y,hy.1⟩,⟨z,hz⟩),?_⟩
      change (packetEndpoint S L (cover.packet (choosePacket ⟨y,hy.1⟩)) lam
        y (R y) z,y) = _
      exact Prod.ext
        (cover.endpoint_coherence (choosePacket ⟨y,hy.1⟩) i lam hLam y
          ⟨hChoose ⟨y,hy.1⟩,hy.2⟩ (R y) (hRpos y) (hRadius y hy.1) z
          (hSphere ⟨z,hz⟩)) rfl
  rwa [hRange] at hCompact

/-- A public cutoff wrapper: one compact family inside an open smoothness
room has one globally smooth compactly supported extension with full germs. -/
theorem exists_smooth_compact_extension_eq_near_compact_product
    (A U : Set (R3 × R3)) (hA : IsCompact A) (hU : IsOpen U) (hAU : A ⊆ U)
    (u : R3 × R3 → ℝ) (hu : ContDiffOn ℝ ∞ u U) :
    ∃ v : R3 × R3 → ℝ, ContDiff ℝ ∞ v ∧ HasCompactSupport v ∧
      ∀ x ∈ A, v =ᶠ[𝓝 x] u := by
  obtain ⟨W,hW,hAW,hWcompact⟩ := exists_isOpen_superset_and_isCompact_closure hA
  have hAUW : A ⊆ U ∩ W := fun x hx => ⟨hAU hx,hAW hx⟩
  obtain ⟨B,hB,hAB,hBclosure⟩ :=
    hA.exists_isOpen_closure_subset ((hU.inter hW).mem_nhdsSet.mpr hAUW)
  have hBcompact : IsCompact (closure B) :=
    hWcompact.of_isClosed_subset isClosed_closure
      (fun x hx => subset_closure (hBclosure hx).2)
  obtain ⟨C,hC,hAC,hCclosure⟩ :=
    hA.exists_isOpen_closure_subset (hB.mem_nhdsSet.mpr hAB)
  obtain ⟨χ,hχ,_,hSupport,hOne⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hB isClosed_closure hCclosure
  have hSmooth : ContDiff ℝ ∞ (fun x => χ x*u x) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ U
    · exact hχ.contDiffAt.mul (hu.contDiffAt (hU.mem_nhds hx))
    · have hxOutside : x ∈ (closure B)ᶜ := fun hxB => hx (hBclosure hxB).1
      have hZero : (fun y => χ y*u y) =ᶠ[𝓝 x] (fun _ : R3 × R3 => (0 : ℝ)) := by
        filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hxOutside] with y hy
        have hχZero : χ y = 0 := by
          apply notMem_support.mp
          rw [hSupport]
          exact fun hyB => hy (subset_closure hyB)
        simp only [hχZero,zero_mul]
      exact (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : R3 × R3 => (0 : ℝ)) x).congr_of_eventuallyEq hZero
  have hχCompact : HasCompactSupport χ := by
    change IsCompact (closure (Function.support χ))
    rw [hSupport]
    exact hBcompact
  refine ⟨fun x => χ x*u x,hSmooth,hχCompact.mul_right,?_⟩
  intro x hx
  filter_upwards [hC.mem_nhds (hAC hx)] with y hy
  have hχOne : χ y = 1 := (hOne y).mp (subset_closure hy)
  simp only [hχOne,one_mul]

theorem exists_smooth_mixed_kernel_eq_near_all_native_surfaces
    (S : KnownSideSourceData) (L lam delta Rstar bound separation : ℝ) (p : ℕ)
    (cover : NativeNormalCover S L)
    (K : ConstructedMixedKernel S L lam delta Rstar bound separation p cover)
    (hdelta : 0 < delta) (hRstar : 0 < Rstar)
    (hLam : lam ∈ Icc (0 : ℝ) cover.dilationCeiling)
    (hRadius : ∀ y ∈ cylinder,
      referenceRadius delta Rstar p L y < cover.radiusCeiling) :
    ∃ Gext : R3 × R3 → ℝ, ContDiff ℝ ∞ Gext ∧ HasCompactSupport Gext ∧
      ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
      ∀ z ∈ sphere (0 : R3) 1,
        Gext =ᶠ[𝓝 (packetEndpoint S L (cover.packet i) lam y
          (referenceRadius delta Rstar p L y) z,y)] K.kernel := by
  have hCompact := isCompact_nativeMixedKernelSurface S L lam delta Rstar p cover
    hdelta hRstar hLam hRadius
  have hRoom : nativeMixedKernelSurface S L lam delta Rstar p cover ⊆ K.domain := by
    rintro v ⟨i,y,hy,z,hz,rfl⟩
    exact K.sphere_cover i y hy z hz
  obtain ⟨Gext,hSmooth,hSupport,hGerm⟩ :=
    exists_smooth_compact_extension_eq_near_compact_product
      (nativeMixedKernelSurface S L lam delta Rstar p cover) K.domain
      hCompact K.domain_open hRoom K.kernel K.product_solution.1
  refine ⟨Gext,hSmooth,hSupport,?_⟩
  intro i y hy z hz
  exact hGerm _ ⟨i,y,hy,z,hz,rfl⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
