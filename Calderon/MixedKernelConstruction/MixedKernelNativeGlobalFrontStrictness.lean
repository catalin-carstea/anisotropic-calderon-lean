import Calderon.MixedKernelConstruction.MixedKernelNativePacketStrictness
import Calderon.MixedKernelConstruction.MixedKernelNativeGlobalStrictnessGerm
import Calderon.MixedKernelConstruction.MixedKernelNativeNormalDomain
import Calderon.MixedKernelConstruction.MixedKernelProfileLargeLTail
import Calderon.MixedKernelConstruction.MixedKernelNativeNormalizedMetricDictionary
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError ConformalDepth MetricOperator NormalCoordinatesFrame
open ReferenceWeightedApproximation ActualScalarPrincipalAdjoint AngularPolynomial NormalizedPrincipalMetric
open scoped ContDiff Topology InnerProductSpace

/-- One actual smooth source collar and its literal native test cover the WHOLE original front, with the original parameter order. -/
theorem exists_native_global_front_strictness_parameters (S : KnownSideSourceData) :
    ∃ L0 : ℝ, 0<L0 ∧ ∀ L : ℝ, L0 ≤ L → ∀ C : NativeNormalCover S L,
      ∀ R : ℝ, 0<R → R<C.radiusCeiling →
      ∃ p0 : ℕ, 2 ≤ p0 ∧ ∀ p : ℕ, p0 ≤ p → ∃ eps0 : ℝ,
        0<eps0 ∧ eps0 ≤ 1 ∧ ∀ eps : ℝ, 0 ≤ eps → eps ≤ eps0 →
        ∃ R0 : ℝ, 0<R0 ∧ ∀ Rstar : ℝ, 0<Rstar → Rstar ≤ R0 →
        ∀ lam ∈ Icc (0 : ℝ) C.dilationCeiling,
        ∀ delta : ℝ, 0<delta → delta ≤ 1 → CurrentRadiusBootstrap S L lam delta Rstar eps p →
        (∀ delta' ∈ Icc delta (1 : ℝ), ∀ y ∈ cylinder,
          referenceRadius delta' Rstar p L y<C.radiusCeiling) ∧
        (∀ delta' ∈ Icc delta (1 : ℝ), ∀ y ∈ cylinder,
          referenceRadius delta' Rstar p L y<R) ∧
        ∃ W : Set (R3 × R3), IsOpen W ∧
          nativeSphereFront S L C lam delta Rstar p ⊆ W ∧ W ⊆ dilatedOffDiagonal S lam ∧
          ContDiffOn ℝ ∞ (nativeGlobalEnergy S L C lam R delta Rstar p) W ∧
          (∀ q ∈ nativeSphereFront S L C lam delta Rstar p,
            nativeGlobalEnergy S L C lam R delta Rstar p q=0) ∧
          ∀ (i : Fin C.count) (y : R3), y ∈ cylinder ∩ (C.packet i).centers →
          ∀ z : R3, ‖z‖=1 →
            ProductHessianStrictAt (fun X => S.g1 (lam • X)) (fun Y => S.g2 (lam • Y))
              (packetEndpoint S L (C.packet i) lam y (referenceRadius delta Rstar p L y) z) y
              (nativeGlobalEnergy S L C lam R delta Rstar p) := by
  classical
  obtain ⟨L0,hL0,HT⟩ := exists_dilated_referenceRadius_uniform_metric_tail S.g1 S.g1_admissible cylinder isCompact_cylinder
  refine ⟨L0,hL0,?_⟩
  intro L hL C R hR hRRoom
  obtain ⟨c0,c,CP,T,hc0,hc,hCP,Htail⟩ := HT L hL
  choose pN hpN HN using fun i : Fin C.count =>
    exists_packet_actual_energy_strictness_parameters S L (C.packet i) c0 c hc0 hc
  let p0 := max 2 (Finset.univ.sup pN)
  refine ⟨p0,Nat.le_max_left _ _,?_⟩
  intro p hp
  have hpAll (i : Fin C.count) : pN i ≤ p := by
    exact (Finset.le_sup (f := pN) (Finset.mem_univ i)).trans ((Nat.le_max_right _ _).trans hp)
  choose epsN rN hepsN hepsN1 hrN Hnative using fun i : Fin C.count => HN i p (hpAll i)
  let i0 : Fin C.count := ⟨0,C.count_positive⟩
  let Eps : Finset ℝ := Finset.univ.image epsN
  let Radii : Finset ℝ := Finset.univ.image rN
  have hEps : Eps.Nonempty := ⟨epsN i0,Finset.mem_image.mpr ⟨i0,Finset.mem_univ i0,rfl⟩⟩
  have hRadii : Radii.Nonempty := ⟨rN i0,Finset.mem_image.mpr ⟨i0,Finset.mem_univ i0,rfl⟩⟩
  let eps0 := Eps.min' hEps
  let rMin := Radii.min' hRadii
  have heps0 : 0<eps0 := by
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp (Finset.min'_mem Eps hEps)
    change 0<Eps.min' hEps
    rw [←hi]
    exact hepsN i
  have hrMin : 0<rMin := by
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp (Finset.min'_mem Radii hRadii)
    change 0<Radii.min' hRadii
    rw [←hi]
    exact hrN i
  have hepsAll (i : Fin C.count) : eps0 ≤ epsN i :=
    Finset.min'_le Eps (epsN i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩)
  have hrAll (i : Fin C.count) : rMin ≤ rN i :=
    Finset.min'_le Radii (rN i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩)
  refine ⟨eps0,heps0,(hepsAll i0).trans (hepsN1 i0),?_⟩
  intro eps heps hepsCap
  let rCap := min (min 1 (R/2)) rMin
  have hrCap : 0<rCap := lt_min (lt_min (by norm_num) (div_pos hR (by norm_num))) hrMin
  have hCap1 : rCap ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hCapR : rCap<R := by
    have hh : rCap ≤ R/2 := (min_le_left _ _).trans (min_le_right _ _)
    linarith
  have hCapAll (i : Fin C.count) : rCap ≤ rN i := (min_le_right _ _).trans (hrAll i)
  let B := Real.log (1+Real.exp T)
  have hB : 0<B := RadiusProfile.log_exp_add_one_pos T
  have hDen : 0<B^p+1 := by positivity
  let R0 := rCap/(B^p+1)
  refine ⟨R0,div_pos hrCap hDen,?_⟩
  intro Rstar hRs hRstar lam hlam delta hd hd1 hBoot
  have hlam1 : lam ∈ Icc (0 : ℝ) 1 := ⟨hlam.1,hlam.2.trans C.dilation_le_one⟩
  have hScale : Rstar*(B^p+1) ≤ rCap := (le_div_iff₀ hDen).mp hRstar
  have hRadiusCap (delta' : ℝ) (hd' : 0<delta') (hd'1 : delta' ≤ 1) (y : R3) (hy : y ∈ cylinder) :
      referenceRadius delta' Rstar p L y<rCap := by
    have hh := (Htail lam hlam1 delta' hd' hd'1 Rstar hRs p 0 (Nat.zero_le p) y hy).2.2
    have hUpper : referenceRadius delta' Rstar p L y ≤ Rstar*B^p := by
      simpa only [pow_zero,mul_one,Nat.sub_zero] using hh
    have hStrict : Rstar*B^p<rCap := by nlinarith only [hScale,hRs]
    exact hUpper.trans_lt hStrict
  have hRadius (y : R3) (hy : y ∈ cylinder) : referenceRadius delta Rstar p L y<R :=
    (hRadiusCap delta hd hd1 y hy).trans hCapR
  have hIntermediate : ∀ delta' ∈ Icc delta (1 : ℝ), ∀ y ∈ cylinder,
      referenceRadius delta' Rstar p L y<C.radiusCeiling := by
    intro delta' hd' y hy
    exact ((hRadiusCap delta' (hd.trans_le hd'.1) hd'.2 y hy).trans hCapR).trans hRRoom
  have hIntermediateR : ∀ delta' ∈ Icc delta (1 : ℝ), ∀ y ∈ cylinder,
      referenceRadius delta' Rstar p L y<R := by
    intro delta' hd' y hy
    exact (hRadiusCap delta' (hd.trans_le hd'.1) hd'.2 y hy).trans hCapR
  obtain ⟨W,hW,hFrontW,hWRoom,hSmooth,hZero⟩ := exists_nativeGlobalEnergy_full_front_open_room
    S L C lam hlam R hR hRRoom delta Rstar hd hRs p hRadius
  refine ⟨hIntermediate,hIntermediateR,W,hW,hFrontW,hWRoom,hSmooth,hZero,?_⟩
  intro i y hy z hz
  let P := C.packet i
  let r := referenceRadius delta Rstar p L y
  let x := packetEndpoint S L P lam y r z
  let E := nativeGlobalEnergy S L C lam R delta Rstar p
  have hr : 0<r := referenceRadius_pos delta Rstar p L y hd hRs
  have hrR : r<R := hRadius y hy.1
  have hr1 : r ≤ 1 := (hRadiusCap delta hd hd1 y hy.1).le.trans hCap1
  have hrRoom : r ≤ 4*P.rho := (hrR.trans hRRoom).le.trans (C.radius_room i).le
  obtain ⟨CF,hCF,HF⟩ := exists_packet_common_native_phase_hessian_bounds S L P
  obtain ⟨V,tau,hV,hxy,hTau,_hZero,hFamily,_hCov1,_hCov2,_hX,_hM,_hY⟩ :=
    HF lam hlam1 y hy.2 r hr (le_min hr1 hrRoom) z hz
  have hTauAt : ContDiffAt ℝ ∞ tau (x,y) := hTau.contDiffAt (hV.mem_nhds hxy)
  have hProf := Htail lam hlam1 delta hd hd1 Rstar hRs p 0 (Nat.zero_le p) y hy.1
  have hBeta : c0*(p : ℝ) ≤ actualReferenceBeta S.g1 L lam delta Rstar p y := hProf.1
  have hLog : ∀ X : R3, RadiusProfile.coordinateHessian
      (fun Y => Real.log (referenceRadius delta Rstar p L Y))
      (fun U V => coordinateConnectionField
        (inverseMetricField (metricOperatorField (conformalReferenceMatrix S.g1 L lam)))
        (metricOperatorField (conformalReferenceMatrix S.g1 L lam)) y U V) y X X ≤
      -c*(actualReferenceBeta S.g1 L lam delta Rstar p y)*
        ⟪metricOperatorField (conformalReferenceMatrix S.g1 L lam) y X,X⟫_ℝ := by
    intro X
    have hh : RadiusProfile.coordinateHessian
        (fun Y => Real.log (referenceRadius delta Rstar p L Y))
        (fun U V => coordinateConnectionField
          (inverseMetricField (metricOperatorField (referenceMetric (dilatedMetric S.g1 lam) L)))
          (metricOperatorField (referenceMetric (dilatedMetric S.g1 lam) L)) y U V) y X X ≤
        -c*(actualReferenceBeta S.g1 L lam delta Rstar p y)*
          ⟪metricOperatorField (referenceMetric (dilatedMetric S.g1 lam) L) y X,X⟫_ℝ := hProf.2.1 X
    rw [referenceMetric_eq_conformalReferenceMatrix S.g1 L lam] at hh
    exact hh
  have hNative := Hnative i eps heps (hepsCap.trans (hepsAll i)) lam hlam1 delta Rstar hd hd1 hRs hBoot y hy
    ((hRadiusCap delta hd hd1 y hy.1).le.trans (hCapAll i)) hBeta hLog z hz tau hTauAt hFamily
  have hGlobal : ProductHessianStrictAt (conformalReferenceMatrix S.g1 L lam)
      (fun Y => (referenceNormalizedPrincipalMatrix S.g1 S.g2 L lam Y)⁻¹) x y E :=
    (productHessianStrictAt_nativeGlobalEnergy_iff S L C lam hlam R hR hRRoom delta Rstar hd hRs p i y hy.2 hrR z hz tau hFamily _ _).mpr hNative
  have hReference : ProductHessianStrictAt (referenceMetric (dilatedMetric S.g1 lam) L)
      (fun Y => (referenceNormalizedPrincipalMatrix S.g1 S.g2 L lam Y)⁻¹) x y E := by
    rw [referenceMetric_eq_conformalReferenceMatrix S.g1 L lam]
    exact hGlobal
  exact (productHessianStrictAt_reference_normalized_iff S L lam x y E).mp hReference

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
