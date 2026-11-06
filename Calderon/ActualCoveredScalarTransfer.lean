import Calderon.ActualGlobalNativeDensityOperatorPackage

set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  ConnectionError MetricOperator MetricVolume ConformalDepth ReferenceWeightedApproximation
  ActualNormalizedSecondMetricDrift

theorem nativeMixedKernelDensityFunctional_eq_on_packet_overlap
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (S : KnownSideSourceData) (L lam delta Rstar : ℝ) (p : ℕ)
    (cover : NativeNormalCover S L) (i j : Fin cover.count) (y : R3)
    (hy : y ∈ (cover.packet i).centers ∩ (cover.packet j).centers)
    (hdelta : 0 < delta) (hRstar : 0 < Rstar)
    (hLam : lam ∈ Icc (0 : ℝ) cover.dilationCeiling)
    (hrceil : referenceRadius delta Rstar p L y < cover.radiusCeiling)
    (Psi : R3 → SphereSobolev (3/2 : ℝ)) (u : SmoothData) :
    nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i)
      lam delta Rstar p Psi u y =
    nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet j)
      lam delta Rstar p Psi u y := by
  have hValue : smoothSphereValue
      (referencePhysicalPullbackData S.g1 S.g1_admissible L (cover.packet i).y0
        (cover.packet i).Phi (cover.packet i).B (cover.packet i).native_data.1.1.1
        lam y (referenceRadius delta Rstar p L y) u) =
      smoothSphereValue
      (referencePhysicalPullbackData S.g1 S.g1_admissible L (cover.packet j).y0
        (cover.packet j).Phi (cover.packet j).B (cover.packet j).native_data.1.1.1
        lam y (referenceRadius delta Rstar p L y) u) := by
    ext z
    change u.1 (packetEndpoint S L (cover.packet i) lam y
        (referenceRadius delta Rstar p L y) z.val) =
      u.1 (packetEndpoint S L (cover.packet j) lam y
        (referenceRadius delta Rstar p L y) z.val)
    rw [cover.endpoint_coherence i j lam hLam y hy
      (referenceRadius delta Rstar p L y)
      (referenceRadius_pos delta Rstar p L y hdelta hRstar) hrceil z.val
      (closedBall_subset_closedBall (by norm_num) (sphere_subset_closedBall z.property))]
  unfold nativeMixedKernelDensityFunctional
  rw [τ0.valueTrace_smooth,τ0.valueTrace_smooth,hValue]

attribute [local irreducible] nativeMixedKernelDensityFunctional

theorem exists_native_covered_scalar_function_of_local_secondPDE
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (S : KnownSideSourceData) (L lam delta Rstar : ℝ) (p : ℕ)
    (cover : NativeNormalCover S L) (hdelta : 0 < delta) (hRstar : 0 < Rstar)
    (hLam : lam ∈ Icc (0 : ℝ) cover.dilationCeiling)
    (hRadius : ∀ y ∈ cylinder, referenceRadius delta Rstar p L y < cover.radiusCeiling)
    (Psi : R3 → SphereSobolev (3/2 : ℝ)) (u : SmoothData)
    (hLocal : ∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
      ∃ Y : Set R3, IsOpen Y ∧ y ∈ Y ∧
        ContDiffOn ℝ ∞ (nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i)
          lam delta Rstar p Psi u) Y ∧
        ∀ z ∈ Y, normalizedSecondLaplacian S.g1 S.g2 L lam
          (nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i)
            lam delta Rstar p Psi u) z = 0) :
    ∃ F : R3 → ℝ,
      (∀ i : Fin cover.count, ∀ y ∈ cylinder ∩ (cover.packet i).centers,
        F y = nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i)
          lam delta Rstar p Psi u y) ∧
      ContinuousOn F cylinder ∧
      ContDiffOn ℝ ∞ F (interior cylinder) ∧
      ∀ y ∈ interior cylinder, normalizedSecondLaplacian S.g1 S.g2 L lam F y = 0 := by
  classical
  let sel (y : R3) (hy : y ∈ cylinder) : Fin cover.count :=
    Classical.choose (cover.covers_cylinder y hy)
  have hsel (y : R3) (hy : y ∈ cylinder) : y ∈ (cover.packet (sel y hy)).centers :=
    Classical.choose_spec (cover.covers_cylinder y hy)
  let F : R3 → ℝ := fun y => if hy : y ∈ cylinder then
    nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet (sel y hy))
      lam delta Rstar p Psi u y else 0
  have hEq (i : Fin cover.count) (y : R3) (hy : y ∈ cylinder ∩ (cover.packet i).centers) :
      F y = nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i)
        lam delta Rstar p Psi u y := by
    dsimp only [F]
    rw [dite_eq_left hy.1]
    exact nativeMixedKernelDensityFunctional_eq_on_packet_overlap hO hD τ0 S L lam delta
      Rstar p cover (sel y hy.1) i y ⟨hsel y hy.1,hy.2⟩
      hdelta hRstar hLam (hRadius y hy.1) Psi u
  have hCont : ContinuousOn F cylinder := by
    intro y hy
    obtain ⟨i,hyi⟩ := cover.covers_cylinder y hy
    obtain ⟨Y,hY,hyY,hSmooth,hPDE⟩ := hLocal i y ⟨hy,hyi⟩
    have hNear : F =ᶠ[𝓝[cylinder] y] nativeMixedKernelDensityFunctional hO hD τ0 S L
        (cover.packet i) lam delta Rstar p Psi u := by
      filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds
        ((cover.packet i).centers_open.mem_nhds hyi), self_mem_nhdsWithin] with z hzi hzc
      exact hEq i z ⟨hzc,hzi⟩
    change Tendsto F (𝓝[cylinder] y) (𝓝 (F y))
    rw [hEq i y ⟨hy,hyi⟩]
    exact ((hSmooth.contDiffAt (hY.mem_nhds hyY)).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds).congr' hNear.symm
  have hReg (y : R3) (hy : y ∈ interior cylinder) :
      ContDiffAt ℝ ∞ F y ∧ normalizedSecondLaplacian S.g1 S.g2 L lam F y = 0 := by
    obtain ⟨i,hyi⟩ := cover.covers_cylinder y (interior_subset hy)
    obtain ⟨Y,hY,hyY,hSmooth,hPDE⟩ := hLocal i y ⟨interior_subset hy,hyi⟩
    have hN : IsOpen (Y ∩ (cover.packet i).centers ∩ interior cylinder) :=
      (hY.inter (cover.packet i).centers_open).inter isOpen_interior
    have hyN : y ∈ Y ∩ (cover.packet i).centers ∩ interior cylinder := ⟨⟨hyY,hyi⟩,hy⟩
    have hNear : F =ᶠ[𝓝 y] nativeMixedKernelDensityFunctional hO hD τ0 S L
        (cover.packet i) lam delta Rstar p Psi u := by
      filter_upwards [hN.mem_nhds hyN] with z hz
      exact hEq i z ⟨interior_subset hz.2,hz.1.2⟩
    exact ⟨(hSmooth.contDiffAt (hY.mem_nhds hyY)).congr_of_eventuallyEq hNear,
      (normalizedSecondLaplacian_congr_of_eventuallyEq S.g1 S.g2 L lam F
        (nativeMixedKernelDensityFunctional hO hD τ0 S L (cover.packet i)
          lam delta Rstar p Psi u) y hNear).trans (hPDE y hyY)⟩
  refine ⟨F,hEq,hCont,isOpen_interior.contDiffOn_iff.mpr ?_,?_⟩
  · intro y hy
    exact (hReg y hy).1
  · intro y hy
    exact (hReg y hy).2

end OAI.AnisotropicCalderon.MixedKernelConstructionTask

