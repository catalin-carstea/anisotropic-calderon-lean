import Calderon.MixedKernelConstruction.TaskInterface
import Calderon.ActualMixedKernelFixedFluxHelpers
import Calderon.ActualMixedKernelMovingFixedFlux
import Calderon.ActualMixedKernelGlobalSurfaceExtension
import Calderon.FixedSurfaceFluxIntegration
import Calderon.FixedSurfaceTransferIntegration
import Calderon.ActualNormalizedSecondMetricDrift

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology Gradient InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  ConnectionError ConformalDepth ReferenceWeightedApproximation ActualScalarPrincipalAdjoint
  MetricOperator MetricVolume ReferenceDensityBounds ActualNormalizedSecondMetricDrift

theorem contDiff_and_secondOrder_integral_of_global_smooth
    (mu : Measure R3) [IsFiniteMeasure mu] (Q : Set R3) (hQ : IsCompact Q)
    (hMass : mu Qᶜ = 0) (V : Set R3) (hV : IsOpen V)
    (H : R3 → R3 → ℝ) (hH : ContDiff ℝ ∞ (Function.uncurry H))
    (a : FixedSurfaceFlux.Coefficients) (b : R3 → Fin 3 → ℝ) (c : R3 → ℝ)
    (hSolve : ∀ x ∈ Q, ∀ y ∈ V, FixedSurfaceFlux.secondOrderOperator a b c (H x) y = 0) :
    ContDiff ℝ ∞ (fun y => ∫ x, H x y ∂mu) ∧
      ∀ y ∈ V, FixedSurfaceFlux.secondOrderOperator a b c (fun z => ∫ x, H x z ∂mu) y = 0 := by
  have hSmooth : ContDiff ℝ ∞ (fun y => ∫ x, H x y ∂mu) := by
    have hFiniteOrder : ∀ n : ℕ, ContDiffOn ℝ n (fun y => ∫ x, H x y ∂mu) univ := fun n =>
      FixedSurfaceTransfer.contDiffOn_parametric_integral hQ (subset_univ _) isOpen_univ isOpen_univ
        hMass n H (hH.of_le (FixedSurfaceTransfer.natCast_le_infty (n+1))).contDiffOn
    exact contDiffOn_univ.1 (contDiffOn_infty.2 hFiniteOrder)
  have hData : FixedSurfaceFlux.FixedSurfaceData mu Q univ V H :=
    ⟨inferInstance,hQ,subset_univ _,isOpen_univ,hV,hMass,
      (hH.of_le (FixedSurfaceTransfer.natCast_le_infty 2)).contDiffOn⟩
  exact ⟨hSmooth,FixedSurfaceFlux.integral_secondOrder_harmonic mu Q univ V H hData a b c hSolve⟩

theorem continuous_fixed_right_slice (H : R3 → R3 → ℝ)
    (hH : Continuous (Function.uncurry H)) (q : R3) : Continuous (fun x : R3 => H x q) := by
  have hPair : Continuous (fun x : R3 => (x,q)) :=
    continuous_id.prodMk (continuous_const : Continuous (fun _ : R3 => q))
  exact hH.comp hPair

theorem integral_unitSphere_eq_integral_image_surfaceMeasure
    (f : R3 → ℝ) (hf : Continuous f) :
    (∫ theta : UnitSphere, f theta.val ∂surfaceMeasure) =
      ∫ z, f z ∂(surfaceMeasure.map (fun theta : UnitSphere => theta.val)) := by
  exact (integral_map (f := f) measurable_subtype_coe.aemeasurable hf.aestronglyMeasurable).symm

theorem inner_signedPiola_metricWronskianFlux_eq_coordinate_expansion
    (g : MatrixField) (X : R3 → R3) (u v : R3 → ℝ) (z : R3) :
    ⟪z,signedPiolaFlux X (metricWronskianFlux g u v) z⟫_ℝ =
      v (X z) * ⟪z,signedPiolaFlux X (metricDivergenceFlux g u) z⟫_ℝ -
      u (X z) * ∑ j : Fin 3, fderiv ℝ v (X z) (FixedSurfaceFlux.coordinateVector j) *
        ⟪z,signedPiolaFlux X (fun x => matrixOperatorMap (principalCoefficient g x)
          (FixedSurfaceFlux.coordinateVector j)) z⟫_ℝ := by
  unfold signedPiolaFlux metricWronskianFlux
  rw [fixedFlux_metricDivergenceFlux_eq_sum g v (X z)]
  simp only [map_sub,map_smul,map_sum,inner_sub_right,real_inner_smul_right,inner_sum]

theorem exists_open_native_mixed_kernel_fixed_flux_secondPDE
    (S : KnownSideSourceData) (L lam delta Rstar bound separation : ℝ) (p : ℕ)
    (cover : NativeNormalCover S L)
    (K : ConstructedMixedKernel S L lam delta Rstar bound separation p cover)
    (hdelta : 0 < delta) (hRstar : 0 < Rstar)
    (i : Fin cover.count) (y : R3) (hy : y ∈ cylinder ∩ (cover.packet i).centers)
    (u : SmoothData) :
    ∃ Y : Set R3, IsOpen Y ∧ y ∈ Y ∧
      ContDiffOn ℝ ∞ (fun pole => nativeMixedKernelWronskianFlux S L (cover.packet i)
        lam K.kernel u.1 y (referenceRadius delta Rstar p L y) pole) Y ∧
      ∀ pole ∈ Y, normalizedSecondLaplacian S.g1 S.g2 L lam
        (fun pole' => nativeMixedKernelWronskianFlux S L (cover.packet i)
          lam K.kernel u.1 y (referenceRadius delta Rstar p L y) pole') pole = 0
 := by
  classical
  let P := cover.packet i
  let r : ℝ := referenceRadius delta Rstar p L y
  -- fixed native endpoint, globally smooth from the packet data
  let X : R3 → R3 := packetEndpoint S L P lam y r
  have hTheta : ContDiff ℝ ∞ (fun v : ℝ × (R3 × R3) => (P.Phi v.1 v.2 1).1) :=
    P.native_data.1.1.1.2.2.2.2.2.2.2.1
  have hX : ContDiff ℝ ∞ X :=
    (contDiff_referenceFramedPhysicalEndpoint S.g1 S.g1_admissible L P.Phi hTheta).comp
      (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))
  -- physical metric g1(lam .): globally smooth and positive for every lam
  have hg : ∀ k l, ContDiff ℝ ∞ (fun x : R3 => S.g1 (lam • x) k l) := fun k l =>
    (S.g1_admissible.smooth k l).comp
      (ContDiff.const_smul lam (contDiff_id : ContDiff ℝ ∞ (fun x : R3 => x)))
  have hgp : ∀ x : R3, (S.g1 (lam • x)).PosDef := fun x => S.g1_admissible.posDef (lam • x)
  /- Step 1: compact graph, smooth product extension, physical product collar. -/
  have hXS : IsCompact (X '' sphere (0 : R3) 1) :=
    (isCompact_sphere (0 : R3) 1).image hX.continuous
  have hA : IsCompact ((X '' sphere (0 : R3) 1) ×ˢ ({y} : Set R3)) :=
    hXS.prod isCompact_singleton
  have hAU : (X '' sphere (0 : R3) 1) ×ˢ ({y} : Set R3) ⊆ K.domain := by
    rintro ⟨x, q⟩ ⟨⟨z, hz, rfl⟩, hq⟩
    simp only [mem_singleton_iff] at hq
    subst q
    exact K.sphere_cover i y hy z hz
  obtain ⟨Gext, hG, -, hGeq⟩ := exists_smooth_compact_extension_eq_near_compact_product
    _ K.domain hA K.domain_open hAU K.kernel K.product_solution.1
  let E : Set (R3 × R3) := {q | Gext =ᶠ[𝓝 q] K.kernel} ∩ K.domain
  have hE : IsOpen E :=
    (isOpen_setOfPred_eventually_nhds (p := fun q => Gext q = K.kernel q)).inter K.domain_open
  have hAE : (X '' sphere (0 : R3) 1) ×ˢ ({y} : Set R3) ⊆ E :=
    fun q hq => ⟨hGeq q hq, hAU hq⟩
  obtain ⟨U0, Y, hU0, hY, hXU0, hyY, hUY⟩ :=
    generalized_tube_lemma hXS isCompact_singleton hE hAE
  have hyY' : y ∈ Y := hyY (mem_singleton y)
  have hCollar : ∀ x ∈ U0, ∀ q ∈ Y, Gext =ᶠ[𝓝 (x,q)] K.kernel ∧ (x,q) ∈ K.domain :=
    fun x hx q hq => hUY ⟨hx, hq⟩
  have hXU : ∀ z ∈ sphere (0 : R3) 1, X z ∈ U0 := fun z hz => hXU0 ⟨z, hz, rfl⟩
  /- Step 2: pole PDE of Gext on the physical collar, from K's second product equation. -/
  let G' : R3 → R3 → ℝ := fun x q => Gext (x,q)
  have hGslice : ∀ x, ContDiff ℝ ∞ (G' x) := fun x =>
    hG.comp (contDiff_const.prodMk contDiff_id)
  have hGpde : ∀ x ∈ U0, ∀ q ∈ Y,
      FixedSurfaceFlux.secondOrderOperator (fixedFluxSecondA S L lam)
        (fixedFluxSecondB S L lam) (fun _ => 0) (G' x) q = 0 := by
    intro x hx q hq
    obtain ⟨hgerm, hdom⟩ := hCollar x hx q hq
    have hT : Tendsto (fun q' : R3 => (x,q')) (𝓝 q) (𝓝 (x,q)) :=
      (continuous_const.prodMk continuous_id).tendsto q
    have hloc : G' x =ᶠ[𝓝 q] (fun q' => K.kernel (x,q')) := hgerm.comp_tendsto hT
    rw [← fixedFlux_normalized_eq_secondOrder S L lam (G' x) (hGslice x) q,
      fixedFlux_normalized_congr S L lam _ _ q hloc]
    exact K.product_solution.2.2 (x,q) hdom
  /- Step 3: physical first-variable partials solve the pole PDE (before composing X). -/
  have hGu : ContDiff ℝ ∞ (Function.uncurry G') := hG
  have hG3 : ContDiffOn ℝ 3 (Function.uncurry G') (U0 ×ˢ Y) :=
    (hGu.of_le (FixedSurfaceTransfer.natCast_le_infty 3)).contDiffOn
  have hPdPde : ∀ x ∈ U0, ∀ j : Fin 3, ∀ q ∈ Y,
      FixedSurfaceFlux.secondOrderOperator (fixedFluxSecondA S L lam)
        (fixedFluxSecondB S L lam) (fun _ => 0)
        (FixedSurfaceTransfer.spatialPartial G' j x) q = 0 :=
    fun x hx j q hq => FixedSurfaceTransfer.secondOrder_spatialPartial_harmonic U0 Y G'
      hU0 hY hG3 (fixedFluxSecondA S L lam) (fixedFluxSecondB S L lam) (fun _ => 0)
      hGpde x hx j q hq
  /- Step 4: the explicit finite fixed-coefficient integrand. -/
  let M : R3 → R3 := metricDivergenceFlux (fun x => S.g1 (lam • x)) u.1
  let D : Fin 3 → R3 → R3 := fun j x =>
    matrixOperatorMap (principalCoefficient (fun x => S.g1 (lam • x)) x)
      (FixedSurfaceFlux.coordinateVector j)
  let c0 : R3 → ℝ := fun z => ⟪z, signedPiolaFlux X M z⟫_ℝ
  let cj : Fin 3 → R3 → ℝ := fun j z => ⟪z, signedPiolaFlux X (D j) z⟫_ℝ
  let pdj : Fin 3 → R3 × R3 → ℝ := fun j v =>
    fderiv ℝ Gext v (FixedSurfaceFlux.coordinateVector j, 0)
  let H : R3 → R3 → ℝ := fun z q =>
    Gext (X z, q) * c0 z - u.1 (X z) * ∑ j : Fin 3, pdj j (X z, q) * cj j z
  have hM : ContDiff ℝ ∞ M :=
    contDiff_metricDivergenceFlux (fun x => S.g1 (lam • x)) hg hgp u.1 u.2
  have hD : ∀ j, ContDiff ℝ ∞ (D j) := fun j =>
    (matrixOperatorMap.contDiff.comp
      (contDiff_principalCoefficient_of_smooth_posDef (fun x => S.g1 (lam • x)) hg hgp)).clm_apply
      contDiff_const
  have hc0 : ContDiff ℝ ∞ c0 := fixedFlux_contDiff_inner_signedPiola X M hX hM
  have hcj : ∀ j, ContDiff ℝ ∞ (cj j) := fun j =>
    fixedFlux_contDiff_inner_signedPiola X (D j) hX (hD j)
  have hpdj : ∀ j, ContDiff ℝ ∞ (pdj j) := fun j =>
    (hG.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hXv : ContDiff ℝ ∞ (fun v : R3 × R3 => (X v.1, v.2)) :=
    (hX.comp contDiff_fst).prodMk contDiff_snd
  have hHu : ContDiff ℝ ∞ (Function.uncurry H) :=
    ((hG.comp hXv).mul (hc0.comp contDiff_fst)).sub
      ((u.2.comp (hX.comp contDiff_fst)).mul
        (ContDiff.sum fun j _ => ((hpdj j).comp hXv).mul ((hcj j).comp contDiff_fst)))
  have hpd_eq : ∀ j (x q : R3),
      FixedSurfaceTransfer.spatialPartial G' j x q = pdj j (x,q) := fun j x q =>
    FixedSurfaceTransfer.fderiv_slice_left (h := Gext) (X := fun w => G' w q)
      (hG.differentiable (by simp) (x,q)) EventuallyEq.rfl
      (FixedSurfaceFlux.coordinateVector j)
  /- Step 5: the pole PDE of each fixed integrand slice on Y. -/
  have hHsol : ∀ z ∈ sphere (0 : R3) 1,
      FixedSurfaceTransfer.SolvesOn (fixedFluxSecondA S L lam) (fixedFluxSecondB S L lam)
        (fun _ => 0) Y (H z) := by
    intro z hz
    have hXz : X z ∈ U0 := hXU z hz
    have hS0 : FixedSurfaceTransfer.SolvesOn (fixedFluxSecondA S L lam)
        (fixedFluxSecondB S L lam) (fun _ => 0) Y (fun q => Gext (X z, q)) :=
      ⟨((hGslice (X z)).of_le (FixedSurfaceTransfer.natCast_le_infty 2)).contDiffOn,
        fun q hq => hGpde (X z) hXz q hq⟩
    have hSj : ∀ j, FixedSurfaceTransfer.SolvesOn (fixedFluxSecondA S L lam)
        (fixedFluxSecondB S L lam) (fun _ => 0) Y (fun q => pdj j (X z, q)) := by
      intro j
      have heq : (fun q => pdj j (X z, q)) = FixedSurfaceTransfer.spatialPartial G' j (X z) :=
        funext fun q => (hpd_eq j (X z) q).symm
      refine ⟨(((hpdj j).comp (contDiff_const.prodMk contDiff_id)).of_le
        (FixedSurfaceTransfer.natCast_le_infty 2)).contDiffOn, fun q hq => ?_⟩
      rw [heq]
      exact hPdPde (X z) hXz j q hq
    show FixedSurfaceTransfer.SolvesOn (fixedFluxSecondA S L lam) (fixedFluxSecondB S L lam)
      (fun _ => 0) Y (fun q => Gext (X z, q) * c0 z -
        u.1 (X z) * ∑ j : Fin 3, pdj j (X z, q) * cj j z)
    refine FixedSurfaceTransfer.solvesOn_sub hY (f := fun q => Gext (X z, q) * c0 z)
      (g := fun q => u.1 (X z) * ∑ j : Fin 3, pdj j (X z, q) * cj j z) ?_ ?_
    · exact FixedSurfaceTransfer.solvesOn_mul_const hY (c0 z) hS0
    · refine FixedSurfaceTransfer.solvesOn_const_mul hY (u.1 (X z))
        (f := fun q => ∑ j : Fin 3, pdj j (X z, q) * cj j z) ?_
      exact FixedSurfaceTransfer.solvesOn_sum hY Finset.univ
        (fun j q => pdj j (X z, q) * cj j z)
        fun j _ => FixedSurfaceTransfer.solvesOn_mul_const hY (cj j z) (hSj j)
  /- Step 6: fixed reference sphere measure and the extended integral. -/
  haveI hsfin : IsFiniteMeasure (surfaceMeasure : Measure UnitSphere) := by
    unfold surfaceMeasure
    infer_instance
  let μ : Measure R3 := surfaceMeasure.map (fun θ : UnitSphere => θ.val)
  haveI hμfin : IsFiniteMeasure μ :=
    MeasureTheory.Measure.isFiniteMeasure_map surfaceMeasure _
  have hμ : μ (sphere (0 : R3) 1)ᶜ = 0 := by
    show (surfaceMeasure.map (fun θ : UnitSphere => θ.val)) (sphere (0 : R3) 1)ᶜ = 0
    rw [Measure.map_apply measurable_subtype_coe isClosed_sphere.measurableSet.compl]
    have hempty : (fun θ : UnitSphere => θ.val) ⁻¹' (sphere (0 : R3) 1)ᶜ = ∅ := by
      ext θ
      simp only [mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false, not_not]
      exact θ.property
    rw [hempty, measure_empty]
  let F : R3 → ℝ := fun q => ∫ x, H x q ∂μ
  have hIntegral : ContDiff ℝ ∞ F ∧
      ∀ q ∈ Y, FixedSurfaceFlux.secondOrderOperator (fixedFluxSecondA S L lam)
        (fixedFluxSecondB S L lam) (fun _ => 0) F q = 0 :=
    contDiff_and_secondOrder_integral_of_global_smooth μ (sphere (0 : R3) 1)
      (isCompact_sphere (0 : R3) 1) hμ Y hY H hHu (fixedFluxSecondA S L lam)
      (fixedFluxSecondB S L lam) (fun _ => 0) (fun z hz q hq => (hHsol z hz).2 q hq)
  obtain ⟨hF,hFpde⟩ := hIntegral
  /- Step 7: the actual SAME-K flux equals the extended integral on Y. -/
  have hEq : ∀ q ∈ Y, nativeMixedKernelWronskianFlux S L (cover.packet i) lam K.kernel u.1
      y (referenceRadius delta Rstar p L y) q = F q := by
    intro q hq
    have hpt : ∀ θ : UnitSphere, ⟪θ.val, signedPiolaFlux
        (packetEndpoint S L (cover.packet i) lam y (referenceRadius delta Rstar p L y))
        (metricWronskianFlux (fun x => S.g1 (lam • x)) u.1 (fun x => K.kernel (x,q)))
        θ.val⟫_ℝ = H θ.val q := by
      intro θ
      have hXθ : X θ.val ∈ U0 := hXU θ.val θ.property
      have hT : Tendsto (fun x : R3 => (x,q)) (𝓝 (X θ.val)) (𝓝 (X θ.val,q)) :=
        (continuous_id.prodMk continuous_const).tendsto (X θ.val)
      have hgerm : (fun x => Gext (x,q)) =ᶠ[𝓝 (X θ.val)] (fun x => K.kernel (x,q)) :=
        (hCollar _ hXθ q hq).1.comp_tendsto hT
      have hKval : K.kernel (X θ.val,q) = Gext (X θ.val,q) := hgerm.eq_of_nhds.symm
      have hKder (j : Fin 3) :
          fderiv ℝ (fun x => K.kernel (x,q)) (X θ.val) (FixedSurfaceFlux.coordinateVector j) =
            pdj j (X θ.val,q) := by
        calc
          _ = fderiv ℝ (fun x => Gext (x,q)) (X θ.val) (FixedSurfaceFlux.coordinateVector j) :=
            congrArg (fun T : R3 →L[ℝ] ℝ => T (FixedSurfaceFlux.coordinateVector j)) hgerm.symm.fderiv_eq
          _ = pdj j (X θ.val,q) := hpd_eq j (X θ.val) q
      change ⟪θ.val,signedPiolaFlux X (metricWronskianFlux (fun x => S.g1 (lam • x))
        u.1 (fun x => K.kernel (x,q))) θ.val⟫_ℝ = H θ.val q
      rw [inner_signedPiola_metricWronskianFlux_eq_coordinate_expansion,hKval]
      simp_rw [hKder]
      rfl
    have hHq : Continuous (fun x => H x q) :=
      continuous_fixed_right_slice H hHu.continuous q
    unfold nativeMixedKernelWronskianFlux
    calc _ = ∫ θ : UnitSphere, H θ.val q ∂surfaceMeasure :=
          integral_congr_ae (Filter.Eventually.of_forall hpt)
      _ = ∫ x, H x q ∂μ :=
          integral_unitSphere_eq_integral_image_surfaceMeasure (fun x => H x q) hHq
  /- Step 8: transfer smoothness and the literal normalized PDE back to K. -/
  refine ⟨Y, hY, hyY', ?_, ?_⟩
  · exact hF.contDiffOn.congr fun q hq => hEq q hq
  · intro q hq
    have hloc : (fun q' => nativeMixedKernelWronskianFlux S L (cover.packet i) lam K.kernel
        u.1 y (referenceRadius delta Rstar p L y) q') =ᶠ[𝓝 q] F := by
      filter_upwards [hY.mem_nhds hq] with q' hq' using hEq q' hq'
    rw [fixedFlux_normalized_congr S L lam _ _ q hloc,
      fixedFlux_normalized_eq_secondOrder S L lam F hF q]
    exact hFpde q hq

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
