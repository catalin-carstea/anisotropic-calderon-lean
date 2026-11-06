import Calderon.ActualMixedKernelSurfaceHomotopyRoom
import Calderon.ActualMetricWronskianDivergence
import Calderon.CurvedSphereFluxHomotopy
import Calderon.ActualNearBallHarmonicLift

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology Gradient InnerProductSpace
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  ConnectionError ConformalDepth ReferenceWeightedApproximation ActualScalarPrincipalAdjoint MetricOperator

def nativeMixedKernelWronskianFlux (S : KnownSideSourceData) (L : ℝ)
    (P : NativeNormalPacket S L) (lam : ℝ) (G : R3 × R3 → ℝ) (u : R3 → ℝ)
    (center : R3) (radius : ℝ) (pole : R3) : ℝ :=
  ∫ theta : UnitSphere, ⟪theta.val,
    signedPiolaFlux (packetEndpoint S L P lam center radius)
      (metricWronskianFlux (fun x => S.g1 (lam • x)) u (fun x => G (x,pole)))
      theta.val⟫_ℝ ∂surfaceMeasure

private theorem metricWronskianFlux_eq_of_kernel_germ
    (g : MatrixField) (u v w : R3 → ℝ) (x : R3) (h : v =ᶠ[𝓝 x] w) :
    metricWronskianFlux g u v x = metricWronskianFlux g u w x := by
  have hGrad : gradient v x = gradient w x := by
    apply ext_inner_right ℝ
    intro W
    rw [inner_gradient_left,inner_gradient_left,h.fderiv_eq]
  unfold metricWronskianFlux metricDivergenceFlux
  rw [h.eq_of_nhds,hGrad]

private theorem exists_open_native_surface_homotopy_test_room
    (X : (R3 × ℝ) × R3 → R3) (hX : Continuous X)
    (R : R3 → ℝ) (hR : Continuous R) (U : Set R3) (hU : IsOpen U) (y : R3)
    (hCover : ∀ z ∈ sphere (0 : R3) 1, X ((y,R y),z) ∈ U) :
    ∃ Y : Set R3, IsOpen Y ∧ y ∈ Y ∧ ∀ y' ∈ Y,
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ sphere (0 : R3) 1,
        X (((1-t) • y+t • y',(1-t)*R y+t*R y'),z) ∈ U := by
  let c : R3 × (ℝ × R3) → R3 := fun p => (1-p.2.1) • y+p.2.1 • p.1
  let r : R3 × (ℝ × R3) → ℝ := fun p => (1-p.2.1)*R y+p.2.1*R p.1
  let Q : R3 × (ℝ × R3) → R3 := fun p => X ((c p,r p),p.2.2)
  have hc : Continuous c :=
    ((continuous_const.sub continuous_snd.fst).smul continuous_const).add
      (continuous_snd.fst.smul continuous_fst)
  have hr : Continuous r :=
    ((continuous_const.sub continuous_snd.fst).mul continuous_const).add
      (continuous_snd.fst.mul (hR.comp continuous_fst))
  have hQ : Continuous Q := hX.comp ((hc.prodMk hr).prodMk continuous_snd.snd)
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
  exact ⟨Y,hYopen,hyY,fun y' hy' t ht z hz => hYsub hy' (t,z) ⟨ht,hz⟩⟩

theorem exists_open_native_mixed_kernel_moving_fixed_flux_eq
    (S : KnownSideSourceData) (L lam delta Rstar bound separation : ℝ) (p : ℕ)
    (cover : NativeNormalCover S L)
    (K : ConstructedMixedKernel S L lam delta Rstar bound separation p cover)
    (hdelta : 0 < delta) (hRstar : 0 < Rstar)
    (i : Fin cover.count) (y : R3) (hy : y ∈ cylinder ∩ (cover.packet i).centers)
    (U : Set R3) (hU : IsOpen U) (u : SmoothData)
    (hCover : (fun z => packetEndpoint S L (cover.packet i) lam y
      (referenceRadius delta Rstar p L y) z) '' closedBall (0 : R3) 1 ⊆ U)
    (hphysical : ∀ x ∈ U,
      coordinateFluxDivergence (metricDivergenceFlux (fun z => S.g1 (lam • z)) u.1) x = 0) :
    ∃ Y : Set R3, IsOpen Y ∧ y ∈ Y ∧ ∀ y' ∈ Y,
      nativeMixedKernelWronskianFlux S L (cover.packet i) lam K.kernel u.1
        y' (referenceRadius delta Rstar p L y') y' =
      nativeMixedKernelWronskianFlux S L (cover.packet i) lam K.kernel u.1
        y (referenceRadius delta Rstar p L y) y' := by
  let P := cover.packet i
  let R := referenceRadius delta Rstar p L
  let X : (R3 × ℝ) × R3 → R3 := fun pz =>
    referenceFramedPhysicalEndpoint S.g1 L P.Phi (lam,pz)
  have hTheta : ContDiff ℝ ∞
      (fun v : ℝ × (R3 × R3) => (P.Phi v.1 v.2 1).1) :=
    P.native_data.1.1.1.2.2.2.2.2.2.2.1
  have hX : ContDiff ℝ ∞ X :=
    (contDiff_referenceFramedPhysicalEndpoint S.g1 S.g1_admissible L P.Phi hTheta).comp
      (contDiff_const.prodMk contDiff_id)
  obtain ⟨Gext,Y0,hG,hGCompact,hY0,hyY0,hKernelRoom⟩ :=
    exists_smooth_mixed_kernel_eq_near_native_surface_homotopy
      S L lam delta Rstar bound separation p cover K hdelta hRstar i y hy
  have hTestCover : ∀ z ∈ sphere (0 : R3) 1, X ((y,R y),z) ∈ U := by
    intro z hz
    exact hCover ⟨z,sphere_subset_closedBall hz,rfl⟩
  obtain ⟨Y1,hY1,hyY1,hTestRoom⟩ := exists_open_native_surface_homotopy_test_room
    X hX.continuous R
    (contDiff_referenceRadius_actual delta Rstar p L hdelta hRstar).continuous U hU y hTestCover
  refine ⟨Y0 ∩ Y1,hY0.inter hY1,⟨hyY0,hyY1⟩,?_⟩
  intro y' hy'
  let H : ℝ × R3 → R3 := fun tz =>
    packetEndpoint S L P lam ((1-tz.1) • y+tz.1 • y') ((1-tz.1)*R y+tz.1*R y') tz.2
  have hs : ContDiff ℝ ∞ (fun tz : ℝ × R3 => 1-tz.1) :=
    contDiff_const.sub contDiff_fst
  have ht1 : ContDiff ℝ ∞ (fun tz : ℝ × R3 => tz.1) := contDiff_fst
  have hc : ContDiff ℝ ∞ (fun tz : ℝ × R3 => (1-tz.1) • y+tz.1 • y') :=
    (hs.smul (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ × R3 => y))).add
      (ht1.smul (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ × R3 => y')))
  have hr : ContDiff ℝ ∞ (fun tz : ℝ × R3 => (1-tz.1)*R y+tz.1*R y') :=
    (hs.mul (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ × R3 => R y))).add
      (ht1.mul (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ × R3 => R y')))
  have hH : ContDiff ℝ ∞ H := hX.comp ((hc.prodMk hr).prodMk contDiff_snd)
  let v : R3 → ℝ := fun x => Gext (x,y')
  let vk : R3 → ℝ := fun x => K.kernel (x,y')
  let Z : R3 → R3 := metricWronskianFlux (fun x => S.g1 (lam • x)) u.1 v
  let Zk : R3 → R3 := metricWronskianFlux (fun x => S.g1 (lam • x)) u.1 vk
  have hv : ContDiff ℝ ∞ v := hG.comp (contDiff_id.prodMk contDiff_const)
  have hZ : ContDiff ℝ ∞ Z :=
    contDiff_dilatedMetricWronskianFlux S.g1 S.g1_admissible lam u.1 v u.2 hv
  have hGerm (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (z : R3) (hz : z ∈ sphere (0 : R3) 1) :
      v =ᶠ[𝓝 (H (t,z))] vk := by
    have hEq : Gext =ᶠ[𝓝 (H (t,z),y')] K.kernel := (hKernelRoom y' hy'.1 t ht z hz).2
    have hT : Tendsto (fun x : R3 => (x,y')) (𝓝 (H (t,z))) (𝓝 (H (t,z),y')) :=
      (continuous_id.prodMk continuous_const).tendsto (H (t,z))
    exact hEq.comp_tendsto hT
  have hDiv : ∀ t ∈ Icc (0 : ℝ) 1, ∀ theta : UnitSphere,
      coordinateFluxDivergence Z (H (t,theta.val)) = 0 := by
    intro t ht theta
    have hRoom := hKernelRoom y' hy'.1 t ht theta.val theta.property
    have hDom : (H (t,theta.val),y') ∈ K.domain := hRoom.1
    have hUpt : H (t,theta.val) ∈ U := hTestRoom y' hy'.2 t ht theta.val theta.property
    have hKPDE : coordinateFluxDivergence
        (metricDivergenceFlux (fun z => S.g1 (lam • z)) vk) (H (t,theta.val)) = 0 :=
      K.product_solution.2.1 (H (t,theta.val),y') hDom
    have hV : coordinateFluxDivergence (metricDivergenceFlux (fun z => S.g1 (lam • z)) v)
        (H (t,theta.val)) = 0 :=
      (coordinateFluxDivergence_metricDivergenceFlux_congr_of_eventuallyEq
        (fun z => S.g1 (lam • z)) v vk (H (t,theta.val))
        (hGerm t ht theta.val theta.property)).trans hKPDE
    exact coordinateFluxDivergence_dilatedMetricWronskianFlux_eq_zero S.g1 S.g1_admissible
      lam u.1 v u.2 hv (H (t,theta.val)) (hphysical (H (t,theta.val)) hUpt) hV
  have hFlux : CurvedSurfaceTransfer.piolaSphereFlux H Z 1 =
      CurvedSurfaceTransfer.piolaSphereFlux H Z 0 :=
    CurvedSurfaceTransfer.piolaSphereFlux_eq_of_boundary_divergence_eq_zero H Z hH hZ hDiv
  have hCongr (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      CurvedSurfaceTransfer.piolaSphereFlux H Z t =
        CurvedSurfaceTransfer.piolaSphereFlux H Zk t := by
    unfold CurvedSurfaceTransfer.piolaSphereFlux
    refine integral_congr_ae (Filter.Eventually.of_forall fun theta => ?_)
    have hW : Z (H (t,theta.val)) = Zk (H (t,theta.val)) :=
      metricWronskianFlux_eq_of_kernel_germ (fun x => S.g1 (lam • x))
        u.1 v vk (H (t,theta.val)) (hGerm t ht theta.val theta.property)
    simp only [signedPiolaFlux,hW]
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one,le_rfl⟩
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl,zero_le_one⟩
  have hFinal : CurvedSurfaceTransfer.piolaSphereFlux H Zk 1 =
      CurvedSurfaceTransfer.piolaSphereFlux H Zk 0 :=
    (hCongr 1 h1).symm.trans (hFlux.trans (hCongr 0 h0))
  have hEnd1 : (fun x => H (1,x)) = packetEndpoint S L P lam y' (R y') := by
    funext x
    show packetEndpoint S L P lam (((1 : ℝ)-1) • y+(1 : ℝ) • y') (((1 : ℝ)-1)*R y+1*R y') x =
      packetEndpoint S L P lam y' (R y') x
    simp only [sub_self,zero_smul,one_smul,zero_add,zero_mul,one_mul]
  have hEnd0 : (fun x => H (0,x)) = packetEndpoint S L P lam y (R y) := by
    funext x
    show packetEndpoint S L P lam (((1 : ℝ)-0) • y+(0 : ℝ) • y') (((1 : ℝ)-0)*R y+0*R y') x =
      packetEndpoint S L P lam y (R y) x
    simp only [sub_zero,one_smul,zero_smul,add_zero,one_mul,zero_mul]
  unfold CurvedSurfaceTransfer.piolaSphereFlux at hFinal
  rw [hEnd1,hEnd0] at hFinal
  unfold nativeMixedKernelWronskianFlux
  exact hFinal

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
